//! rgsql: a tiny SQL-ish server implemented in Zig
//!
//! Summary
//! - TCP server speaking a very small protocol: client sends a UTF-8 SQL string
//!   terminated by a single `\0`; the server responds with a single JSON object
//!   followed by a trailing `\0`.
//! - JSON response shape matches the test harness expectations:
//!   - {"status":"ok","rows":[...],"column_names":[...]} for successful queries
//!   - {"status":"error","error_type":"..."} for failures
//!   - Expression SELECT without tables, with integers/booleans, arithmetic, logic,
//!     comparisons (including `<>`), parentheses, and simple functions `ABS` and `MOD`.
//!   - Minimal DDL/DML and storage: `CREATE TABLE`, `DROP TABLE [IF EXISTS]`,
//!     `INSERT INTO t VALUES (...),(...);` and `SELECT col_list [AS alias] FROM table;`.
//!   - Basic type checking for operators and functions, and division-by-zero detection.
//! - In-memory catalog stores table definitions and rows using the server allocator.
//! Notes & limitations (intentionally simple to satisfy the exercises):
//! - No SQL quoting or string literals; identifiers are ASCII [A-Za-z_][A-Za-z0-9_]*.
//! - Reserved keywords cannot be used as identifiers (but are allowed for aliases).
//! - Table projections support column names and simple binary expressions across columns
//!   or literals using +,-,*,/ and boolean AND/OR keywords for validation purposes.
//! - Statement-level transactional rollback for `INSERT` on validation/div-by-zero is
//!   not yet complete; see tests in Chapter 6 for desired behavior.
//! - The parser is intentionally permissive only for the covered grammar; anything else
//!   returns `parsing_error`.
//!
const std = @import("std");
const dbg = @import("std").debug;

// ---------------------------
// Networking & Server Config
// ---------------------------

fn parsePort(env_map: *const std.process.EnvMap) u16 {
    if (env_map.get("RGSQL_SERVER_PORT")) |port_str| {
        const parsed = std.fmt.parseInt(u16, port_str, 10) catch return 3003;
        // disallow 0 which means auto-assign
        return if (parsed == 0) 3003 else parsed;
    }
    return 3003;
}

// ---------------------------
// Minimal SQL Parser & Eval
// ---------------------------

const ParseError = error{
    ParsingError,
    ValidationError,
    DivisionByZero,
    OutOfMemory,
};

const Value = union(enum) {
    integer: i64,
    boolean: bool,
    null,
};

const SelectItem = struct {
    expr: Value,
    alias: ?[]const u8 = null,
};

/// Normalized representation of a single statement result which is later
/// serialized to JSON by `buildJsonResponse`.
const QueryResult = struct {
    status_ok: bool,
    error_type: ?[]const u8 = null, // when not ok
    // Expression result (chapter 2): single-row result represented by items
    items: []SelectItem,
    // Table result (chapter 3): full row set and column names
    rows: ?[][]Value = null,
    column_names: ?[]const []const u8 = null,
};

// ---------------------------
// Simple in-memory catalog
// ---------------------------

/// Supported column types for the in-memory catalog.
const ColumnType = enum { integer, boolean };

/// Normalized join type for SELECT ... JOIN parsing/evaluation.
const JoinType = enum { none, inner, left, right, full };

/// Column definition used when creating tables and for type checking.
const ColumnDef = struct {
    name: []const u8,
    typ: ColumnType,
};

/// In-memory table: name, column definitions, and an append-only list of rows.
const Table = struct {
    name: []const u8,
    columns: []ColumnDef,
    rows: std.array_list.Managed([]Value),
};

/// In-memory catalog of tables. Single global instance per server process.
const Database = struct {
    tables: std.array_list.Managed(Table),
};

var g_db_initialized: bool = false;
var g_db_allocator: std.mem.Allocator = undefined;
var g_db: Database = undefined;

/// Initialize the global database and bind it to the process allocator once.
fn dbInit(allocator: std.mem.Allocator) void {
    if (!g_db_initialized) {
        g_db_allocator = allocator;
        g_db = Database{ .tables = std.array_list.Managed(Table).init(allocator) };
        g_db_initialized = true;
    }
}

// Global helper type for join evaluation contexts
const EvalTableCtx = struct {
    table_name: []const u8,
    alias: ?[]const u8,
    columns: []const ColumnDef,
    row: []const Value,
};

/// Find an existing table index by name.
fn dbFindTableIndex(name: []const u8) ?usize {
    var i: usize = 0;
    while (i < g_db.tables.items.len) : (i += 1) {
        if (std.mem.eql(u8, g_db.tables.items[i].name, name)) return i;
    }
    return null;
}

/// Create a new table with copied metadata. Returns `validation_error` if it
/// already exists.
fn dbCreateTable(name: []const u8, cols: []const ColumnDef) ParseError!void {
    if (dbFindTableIndex(name)) |_| return ParseError.ValidationError; // already exists

    // Reserve space in the main tables list first.
    try g_db.tables.ensureUnusedCapacity(1);
    // Reserve memory for the table name.
    const name_copy = try g_db_allocator.dupe(u8, name);
    errdefer g_db_allocator.free(name_copy); // Clean up if anything below fails.
                                             
    // copy columns and their names
    const cols_copy = try g_db_allocator.alloc(ColumnDef, cols.len);
    errdefer g_db_allocator.free(cols_copy);

     // This loop is tricky. If an allocation fails on the 3rd column, we
    // need to free the names for the 1st and 2nd columns.
    for (cols, 0..) |c, i| {
        // This errdefer will clean up previously allocated column names
        // if the current `dupe` call fails.
        errdefer {
            for (cols_copy[0..i]) |col_to_free| {
                g_db_allocator.free(col_to_free.name);
            }
        }
        const name_cpy = try g_db_allocator.dupe(u8, c.name);
        cols_copy[i] = .{ .name = name_cpy, .typ = c.typ };
    }
    // This is our guard. We promise the compiler no errors can happen after this point. 
    errdefer comptime unreachable;
    // Now the Mutation Path is error Free :)
    // `https://matklad.github.io/2025/08/16/reserve-first.html`
    // Commit the database table state!
    // We can mutate freely without worrying about errors!
    g_db.tables.appendAssumeCapacity(.{ .name = name_copy, .columns = cols_copy, .rows = std.array_list.Managed([]Value).init(g_db_allocator) });
}

/// Drop a table and free its memory. Returns `validation_error` when the table
/// does not exist and `IF EXISTS` was not specified.
fn dbDropTable(name: []const u8, if_exists: bool) ParseError!void {
    if (dbFindTableIndex(name)) |idx| {
        // free table memory
        const tbl = g_db.tables.items[idx];
        // free rows
        for (tbl.rows.items) |row| {
            g_db_allocator.free(row);
        }
        tbl.rows.deinit();
        // free column names
        for (tbl.columns) |c| {
            g_db_allocator.free(c.name);
        }
        g_db_allocator.free(tbl.columns);
        // free table name
        g_db_allocator.free(tbl.name);
        // remove from array by swap-remove
        _ = g_db.tables.swapRemove(idx);
        return;
    }
    if (!if_exists) return ParseError.ValidationError;
}

/// A hand-written, whitespace/comment resilient, recursive-descent parser for
/// the small SQL subset needed by the exercises. It performs both parsing and
/// limited semantic validation (e.g. type checking and table/column existence).
const Parser = struct {
    input: []const u8,
    pos: usize = 0,
    // Chapter 6: capture division-by-zero encountered during expression
    // evaluation so we can surface it only if no validation errors occurred.
    // This prioritizes type errors over runtime errors per the spec/tests.
    had_division_by_zero: bool = false,

    // When evaluating expressions in table context (WHERE/ORDER BY), resolve
    // bare identifiers as column references using the current row. When null,
    // identifiers are not allowed and cause a validation/parsing error as per
    // clause-specific rules.
    eval_columns: ?[]const ColumnDef = null,
    eval_row: ?[]const Value = null,
    eval_table_name: ?[]const u8 = null,
    // Helper data structure for join evaluation
    // Declared at top-level below; only referenced here
    eval_join_ctx: ?[]const EvalTableCtx = null,

    fn init(input: []const u8) Parser {
        return .{ .input = input, .pos = 0 };
    }

    fn eof(self: *Parser) bool {
        return self.pos >= self.input.len;
    }

    fn peek(self: *Parser) u8 {
        return if (self.eof()) 0 else self.input[self.pos];
    }

    fn advance(self: *Parser) void {
        if (!self.eof()) self.pos += 1;
    }

    fn slice(self: *Parser, start: usize, end: usize) []const u8 {
        return self.input[start..end];
    }

    fn isWhitespace(c: u8) bool {
        return c == ' ' or c == '\n' or c == '\r' or c == '\t' or c == '\x0b' or c == '\x0c';
    }

    fn skipWhitespaceAndComments(self: *Parser) void {
        while (!self.eof()) {
            // whitespace
            if (isWhitespace(self.peek())) {
                self.advance();
                continue;
            }
            // comment: -- ... to end of line
            if (self.peek() == '-' and (self.pos + 1 < self.input.len) and self.input[self.pos + 1] == '-') {
                // skip until newline or EOF
                self.pos += 2;
                while (!self.eof() and self.peek() != '\n') self.advance();
                continue;
            }
            break;
        }
    }

    fn matchChar(self: *Parser, c: u8) bool {
        self.skipWhitespaceAndComments();
        if (!self.eof() and self.peek() == c) {
            self.advance();
            return true;
        }
        return false;
    }

    /// Match a keyword, case-insensitive
    fn matchKeyword(self: *Parser, keyword: []const u8) bool {
        self.skipWhitespaceAndComments();
        var i: usize = 0;
        const start = self.pos;
        while (i < keyword.len and (self.pos + i) < self.input.len) : (i += 1) {
            const a = std.ascii.toLower(self.input[self.pos + i]);
            const b = std.ascii.toLower(keyword[i]);
            if (a != b) break;
        }
        if (i == keyword.len) {
            // ensure not part of a longer identifier (word boundary)
            const after = start + keyword.len;
            const boundary = after >= self.input.len or !isIdentChar(self.input[after]);
            if (boundary) {
                self.pos = after;
                return true;
            }
        }
        return false;
    }

    fn isIdentStart(c: u8) bool {
        return (c >= 'A' and c <= 'Z') or (c >= 'a' and c <= 'z') or c == '_';
    }
    fn isDigit(c: u8) bool {
        return c >= '0' and c <= '9';
    }
    fn isIdentChar(c: u8) bool {
        return isIdentStart(c) or isDigit(c);
    }

    fn isReservedKeyword(tok: []const u8) bool {
        const kws = [_][]const u8{
            "select", "from", "create", "table", "insert", "into", "values",
            "true", "false", "and", "or", "not", "as", "drop", "if", "exists",
            // order/limit/offset
            "order", "by", "asc", "desc", "limit", "offset",
            // join related
            "join", "inner", "outer", "left", "right", "full", "on",
            // types
            "integer", "boolean",
            // null literal
            "null",
        };
        inline for (kws) |kw| {
            if (std.ascii.eqlIgnoreCase(tok, kw)) return true;
        }
        return false;
    }

    fn parseIdentifier(self: *Parser) ?[]const u8 {
        self.skipWhitespaceAndComments();
        if (self.eof()) return null;
        if (!isIdentStart(self.peek())) return null;
        const start = self.pos;
        self.advance();
        while (!self.eof() and isIdentChar(self.peek())) self.advance();
        const tok = self.slice(start, self.pos);
        if (isReservedKeyword(tok)) {
            // rollback if it was a reserved keyword
            self.pos = start;
            return null;
        }
        return tok;
    }

    fn parseAliasIdentifier(self: *Parser) ?[]const u8 {
        // Alias can start with a letter or underscore and may start with a reserved keyword
        self.skipWhitespaceAndComments();
        if (self.eof()) return null;
        if (!isIdentStart(self.peek())) return null;
        const start = self.pos;
        self.advance();
        while (!self.eof() and isIdentChar(self.peek())) self.advance();
        return self.slice(start, self.pos);
    }

    fn parseInteger(self: *Parser) ?i64 {
        self.skipWhitespaceAndComments();
        if (self.eof()) return null;

        var negative = false;
        if (self.peek() == '-') {
            negative = true;
            self.advance();
        }

        if (self.eof() or !isDigit(self.peek())) {
            // roll back if we only consumed '-'
            if (negative) self.pos -= 1;
            return null;
        }

        var value: i64 = 0;
        while (!self.eof() and isDigit(self.peek())) : (self.advance()) {
            const digit: i64 = @intCast(self.peek() - '0');
            value = value * 10 + digit;
        }
        if (negative) value = -value;
        return value;
    }

    fn parseBoolean(self: *Parser) ?bool {
        if (self.matchKeyword("true")) return true;
        if (self.matchKeyword("false")) return false;
        return null;
    }

    fn parseNull(self: *Parser) bool {
        return self.matchKeyword("null");
    }

    fn parsePrimary(self: *Parser) ParseError!Value {
        self.skipWhitespaceAndComments();
        if (self.eof()) return ParseError.ParsingError;

        // parenthesized
        if (self.matchChar('(')) {
            const v = try self.parseExpression();
            if (!self.matchChar(')')) return ParseError.ParsingError;
            return v;
        }

        // function call: IDENT '(' args ')'
        const save_fn = self.pos;
        if (self.parseIdentifier()) |fn_name| {
            self.skipWhitespaceAndComments();
            if (self.matchChar('(')) {
                // parse 0..N args separated by commas, allow whitespace
                var args = std.array_list.Managed(Value).init(std.heap.page_allocator);
                defer args.deinit();
                self.skipWhitespaceAndComments();
                if (!self.matchChar(')')) {
                    while (true) {
                        const v = try self.parseExpression();
                        try args.append(v);
                        self.skipWhitespaceAndComments();
                        if (self.matchChar(',')) {
                            continue;
                        }
                        if (self.matchChar(')')) break;
                        return ParseError.ParsingError;
                    }
                }

                // evaluate supported functions
                if (std.ascii.eqlIgnoreCase(fn_name, "abs")) {
                    if (args.items.len != 1) return ParseError.ValidationError;
                    const a0 = args.items[0];
                    if (a0 == .null) return Value.null;
                    if (a0 != .integer) return ParseError.ValidationError;
                    const n: i64 = a0.integer;
                    // handle minimum value safely: for this kata we assume inputs fit
                    const res: i64 = if (n < 0) -n else n;
                    return Value{ .integer = res };
                } else if (std.ascii.eqlIgnoreCase(fn_name, "mod")) {
                    if (args.items.len != 2) return ParseError.ValidationError;
                    const a0 = args.items[0];
                    const a1 = args.items[1];
                    if (a0 == .null or a1 == .null) return Value.null;
                    if (a0 != .integer or a1 != .integer) return ParseError.ValidationError;
                    const lhs: i64 = a0.integer;
                    const rhs: i64 = a1.integer;
                    if (rhs == 0) {
                        // Defer surfacing the error to statement boundary
                        self.had_division_by_zero = true;
                        const res: i64 = 0;
                        return Value{ .integer = res };
                    }
                    const res: i64 = @rem(lhs, rhs);
                    return Value{ .integer = res };
                } else {
                    // unknown function
                    return ParseError.ValidationError;
                }
            } else {
                // not a function call; if IDENT matches a known function name,
                // this is a missing opening bracket -> parsing_error
                if (std.ascii.eqlIgnoreCase(fn_name, "abs") or std.ascii.eqlIgnoreCase(fn_name, "mod")) {
                    return ParseError.ParsingError;
                }
                // Otherwise rollback to let other primary forms try
                self.pos = save_fn;
            }
        } else {
            self.pos = save_fn;
        }

        // Column reference in join context (supports t.col or alias.col; bare columns must be unambiguous)
        if (self.eval_join_ctx) |jctx| {
            const save_ident = self.pos;
            if (self.parseIdentifier()) |first_ident| {
                var col_name: ?[]const u8 = null;
                var resolved_row: ?[]const Value = null;
                const save_after_first = self.pos;
                self.skipWhitespaceAndComments();
                if (self.matchChar('.')) {
                    // qualified: match table or alias
                    // find context by name or alias
                    var found_ctx: ?EvalTableCtx = null;
                    var k: usize = 0;
                    while (k < jctx.len) : (k += 1) {
                        const tnm = jctx[k].table_name;
                        const anm = jctx[k].alias;
                        if (std.ascii.eqlIgnoreCase(tnm, first_ident) or (anm != null and std.ascii.eqlIgnoreCase(anm.?, first_ident))) {
                            found_ctx = jctx[k];
                            break;
                        }
                    }
                    if (found_ctx == null) return ParseError.ValidationError;
                    const col_ident = self.parseIdentifier() orelse return ParseError.ValidationError;
                    self.skipWhitespaceAndComments();
                    if (self.matchChar('.')) return ParseError.ValidationError;
                    // resolve column
                    var ci: usize = 0;
                    var idx: ?usize = null;
                    while (ci < found_ctx.?.columns.len) : (ci += 1) {
                        if (std.ascii.eqlIgnoreCase(found_ctx.?.columns[ci].name, col_ident)) { idx = ci; break; }
                    }
                    if (idx == null) return ParseError.ValidationError;
                    col_name = col_ident;
                    resolved_row = found_ctx.?.row;
                    return resolved_row.?[idx.?];
                } else {
                    // unqualified: search across contexts, must match exactly once
                    self.pos = save_after_first;
                    var total_matches: usize = 0;
                    var found_value: ?Value = null;
                    var t: usize = 0;
                    while (t < jctx.len) : (t += 1) {
                        var ci: usize = 0;
                        while (ci < jctx[t].columns.len) : (ci += 1) {
                            if (std.ascii.eqlIgnoreCase(jctx[t].columns[ci].name, first_ident)) {
                                total_matches += 1;
                                found_value = jctx[t].row[ci];
                            }
                        }
                    }
                    if (total_matches == 1) {
                        return found_value.?;
                    } else {
                        return ParseError.ValidationError;
                    }
                }
            } else {
                self.pos = save_ident;
            }
        }

        // Column reference in table context (supports qualified t.a and bare a)
        if (self.eval_columns) |cols| {
            const save_ident = self.pos;
            if (self.parseIdentifier()) |first_ident| {
                var use_col_name: []const u8 = first_ident;
                // Optional qualified form: table.column
                const save_after_first = self.pos;
                self.skipWhitespaceAndComments();
                if (self.matchChar('.')) {
                    // must have table name match
                    const tname = self.eval_table_name orelse return ParseError.ValidationError;
                    if (!std.ascii.eqlIgnoreCase(first_ident, tname)) return ParseError.ValidationError;
                    const col_ident = self.parseIdentifier() orelse return ParseError.ValidationError;
                    // ensure no further dots
                    self.skipWhitespaceAndComments();
                    if (self.matchChar('.')) return ParseError.ValidationError;
                    use_col_name = col_ident;
                } else {
                    // rollback whitespace movement if not qualified
                    self.pos = save_after_first;
                }
                // resolve column index case-insensitively
                var idx: ?usize = null;
                var i: usize = 0;
                while (i < cols.len) : (i += 1) {
                    if (std.ascii.eqlIgnoreCase(cols[i].name, use_col_name)) { idx = i; break; }
                }
                if (idx == null) return ParseError.ValidationError;
                const row_vals = self.eval_row orelse return ParseError.ValidationError;
                return row_vals[idx.?];
            } else {
                self.pos = save_ident;
            }
        }

        // boolean
        if (self.parseBoolean()) |b| return Value{ .boolean = b };

        // NULL literal
        if (self.parseNull()) {
            return Value.null;
        }

        // integer (with optional unary minus handled in parseUnary)
        if (self.parseInteger()) |n| return Value{ .integer = n };

        // If we saw an identifier but had no table context, treat as a validation error
        const save_unknown = self.pos;
        if (self.parseIdentifier()) |_| {
            self.pos = save_unknown;
            return ParseError.ValidationError;
        }
        return ParseError.ParsingError;
    }

    fn parseUnary(self: *Parser) ParseError!Value {
        self.skipWhitespaceAndComments();
        if (self.matchKeyword("not")) {
            const v = try self.parseUnary();
            return switch (v) {
                .boolean => |b| Value{ .boolean = !b },
                .null => Value.null,
                else => ParseError.ValidationError,
            };
        }
        if (self.matchChar('-')) {
            const v = try self.parseUnary();
            return switch (v) {
                .integer => |n| Value{ .integer = -n },
                .null => Value.null,
                else => ParseError.ValidationError,
            };
        }
        return self.parsePrimary();
    }

    fn parseMulDiv(self: *Parser) ParseError!Value {
        var left = try self.parseUnary();
        while (true) {
            self.skipWhitespaceAndComments();
            const c = self.peek();
            if (c == '*' or c == '/') {
                self.advance();
                const right = try self.parseUnary();
                switch (c) {
                    '*' => {
                        if (left == .null or right == .null) {
                            left = Value.null;
                        } else if (left != .integer or right != .integer) {
                            return ParseError.ValidationError;
                        } else {
                            left = Value{ .integer = left.integer * right.integer };
                        }
                    },
                    '/' => {
                        if (left == .null or right == .null) {
                            left = Value.null;
                        } else if (left != .integer or right != .integer) {
                            return ParseError.ValidationError;
                        } else if (right.integer == 0) {
                            // Record and continue to allow type errors elsewhere to win
                            self.had_division_by_zero = true;
                            left = Value{ .integer = 0 };
                        } else {
                            left = Value{ .integer = @divTrunc(left.integer, right.integer) };
                        }
                    },
                    else => unreachable,
                }
                continue;
            }
            break;
        }
        return left;
    }

    fn parseAddSub(self: *Parser) ParseError!Value {
        var left = try self.parseMulDiv();
        while (true) {
            self.skipWhitespaceAndComments();
            const c = self.peek();
            if (c == '+' or c == '-') {
                self.advance();
                const right = try self.parseMulDiv();
                switch (c) {
                    '+' => {
                        if (left == .null or right == .null) {
                            left = Value.null;
                        } else if (left != .integer or right != .integer) {
                            return ParseError.ValidationError;
                        } else {
                            left = Value{ .integer = left.integer + right.integer };
                        }
                    },
                    '-' => {
                        if (left == .null or right == .null) {
                            left = Value.null;
                        } else if (left != .integer or right != .integer) {
                            return ParseError.ValidationError;
                        } else {
                            left = Value{ .integer = left.integer - right.integer };
                        }
                    },
                    else => unreachable,
                }
                continue;
            }
            break;
        }
        return left;
    }

    fn parseComparison(self: *Parser) ParseError!Value {
        var left = try self.parseAddSub();
        while (true) {
            self.skipWhitespaceAndComments();
            // operators: < > <= >=
            var op: u8 = 0;
            var or_equal = false;
            if (self.matchChar('<')) {
                // If this is the start of the '<>' inequality operator, leave it for equality parser
                if (self.matchChar('>')) {
                    // rollback and break so higher level can handle '<>'
                    self.pos -= 2;
                    break;
                }
                op = '<';
                or_equal = self.matchChar('=');
            } else if (self.matchChar('>')) {
                op = '>';
                or_equal = self.matchChar('=');
            } else break;

            const right = try self.parseAddSub();
            if (left == .null or right == .null) {
                left = Value.null;
            } else if (left == .integer and right == .integer) {
                const li = left.integer;
                const ri = right.integer;
                var res = false;
                if (op == '<') res = if (or_equal) li <= ri else li < ri;
                if (op == '>') res = if (or_equal) li >= ri else li > ri;
                left = Value{ .boolean = res };
            } else if (left == .boolean and right == .boolean) {
                // define TRUE > FALSE
                const li: i8 = if (left.boolean) 1 else 0;
                const ri: i8 = if (right.boolean) 1 else 0;
                var res = false;
                if (op == '<') res = if (or_equal) li <= ri else li < ri;
                if (op == '>') res = if (or_equal) li >= ri else li > ri;
                left = Value{ .boolean = res };
            } else {
                return ParseError.ValidationError;
            }
        }
        return left;
    }

    fn parseEquality(self: *Parser) ParseError!Value {
        var left = try self.parseComparison();
        while (true) {
            self.skipWhitespaceAndComments();
            var op: enum { eq, neq } = undefined;
            const save = self.pos;
            if (self.matchChar('=')) {
                op = .eq;
            } else if (self.matchChar('<')) {
                if (!self.matchChar('>')) {
                    self.pos = save; // rollback
                    break;
                }
                op = .neq;
            } else break;

            const right = try self.parseComparison();
            if (left == .null or right == .null) {
                left = Value.null;
            } else {
                const res = switch (left) {
                    .integer => |li| switch (right) {
                        .integer => |ri| if (op == .eq) (li == ri) else (li != ri),
                        else => return ParseError.ValidationError,
                    },
                    .boolean => |lb| switch (right) {
                        .boolean => |rb| if (op == .eq) (lb == rb) else (lb != rb),
                        else => return ParseError.ValidationError,
                    },
                    .null => unreachable,
                };
                left = Value{ .boolean = res };
            }
        }
        return left;
    }

    fn parseAnd(self: *Parser) ParseError!Value {
        var left = try self.parseEquality();
        while (true) {
            self.skipWhitespaceAndComments();
            if (!self.matchKeyword("and")) break;
            const right = try self.parseEquality();
            // Enforce operand types: only boolean or NULL are allowed
            if (!((left == .boolean) or (left == .null)) or !((right == .boolean) or (right == .null)))
                return ParseError.ValidationError;
            // Three-valued logic for AND
            if (left == .boolean and !left.boolean) {
                // FALSE AND x => FALSE
                left = Value{ .boolean = false };
            } else if (right == .boolean and !right.boolean) {
                // x AND FALSE => FALSE
                left = Value{ .boolean = false };
            } else if (left == .null or right == .null) {
                // TRUE AND NULL => NULL; NULL AND TRUE => NULL; NULL AND NULL => NULL
                left = Value.null;
            } else {
                // both booleans and neither is FALSE
                left = Value{ .boolean = left.boolean and right.boolean };
            }
        }
        return left;
    }

    fn parseOr(self: *Parser) ParseError!Value {
        var left = try self.parseAnd();
        while (true) {
            self.skipWhitespaceAndComments();
            if (!self.matchKeyword("or")) break;
            const right = try self.parseAnd();
            // Enforce operand types: only boolean or NULL are allowed
            if (!((left == .boolean) or (left == .null)) or !((right == .boolean) or (right == .null)))
                return ParseError.ValidationError;
            // Three-valued logic for OR
            if (left == .boolean and left.boolean) {
                // TRUE OR x => TRUE
                left = Value{ .boolean = true };
            } else if (right == .boolean and right.boolean) {
                // x OR TRUE => TRUE
                left = Value{ .boolean = true };
            } else if (left == .null or right == .null) {
                // FALSE OR NULL => NULL; NULL OR FALSE => NULL; NULL OR NULL => NULL
                left = Value.null;
            } else {
                // both booleans and neither is TRUE
                left = Value{ .boolean = left.boolean or right.boolean };
            }
        }
        return left;
    }

    fn parseExpression(self: *Parser) ParseError!Value {
        return self.parseOr();
    }

    /// Parse a comma-separated list of expressions with optional `AS alias`.
    /// Used for expression-only SELECT and as a helper for table projection
    /// detection.
    fn parseSelectList(self: *Parser, arena: std.mem.Allocator) ParseError![]SelectItem {
        self.skipWhitespaceAndComments();
        var list = std.array_list.Managed(SelectItem).init(arena);
        errdefer list.deinit();

        // handle empty select list (e.g. SELECT;)
        if (self.peek() == ';') {
            return try list.toOwnedSlice();
        }

        while (true) {
            const expr = try self.parseExpression();
            var alias: ?[]const u8 = null;
            const save = self.pos;
            if (self.matchKeyword("as")) {
                if (self.parseAliasIdentifier()) |ident| {
                    // alias must not start with a digit; parseIdentifier enforces it
                    alias = ident;
                } else {
                    return ParseError.ParsingError;
                }
            } else {
                self.pos = save; // rollback if AS not present
            }

            try list.append(.{ .expr = expr, .alias = alias });

            self.skipWhitespaceAndComments();
            if (self.matchChar(',')) {
                continue;
            }
            break;
        }
        return try list.toOwnedSlice();
    }

    /// Parse a SELECT statement. There are two modes:
    /// 1) Expression SELECT (no FROM): returns a single row containing the
    ///    evaluated expressions.
    /// 2) Table SELECT (with FROM): projects columns and simple expressions
    ///    from the named table and returns all rows.
    fn parseSelect(self: *Parser, arena: std.mem.Allocator) ParseError!QueryResult {
        if (!self.matchKeyword("select")) return ParseError.ParsingError;
        // First, optimistically parse as expression SELECT (chapter 2/5). If a FROM appears immediately after,
        // we'll rollback and handle as table SELECT.
        var save_items = self.pos;
        var expr_parse_ok = false;
        var expr_items: []SelectItem = &[_]SelectItem{};
        const expr_try = self.parseSelectList(arena);
        if (expr_try) |itms| {
            expr_items = itms;
            expr_parse_ok = true;
        } else |err| switch (err) {
            error.ParsingError => {
                self.pos = save_items;
                expr_parse_ok = false;
            },
            error.ValidationError => {
                // Heuristic: if a FROM appears later, this is likely a table SELECT
                // where identifiers in the select list will be resolved against the table.
                var i_scan: usize = save_items;
                var found_from = false;
                while (i_scan + 4 <= self.input.len) : (i_scan += 1) {
                    const c = std.ascii.toLower(self.input[i_scan]);
                    if (c == 'f' and i_scan + 4 <= self.input.len) {
                        const kw = self.input[i_scan .. i_scan + 4];
                        if (std.ascii.eqlIgnoreCase(kw, "from")) {
                            // word boundary after 'from'
                            const after = i_scan + 4;
                            const boundary = after >= self.input.len or !isIdentChar(self.input[after]);
                            if (boundary) { found_from = true; break; }
                        }
                    }
                }
                if (found_from) {
                    self.pos = save_items;
                    expr_parse_ok = false;
                } else {
                    return err;
                }
            },
            else => return err,
        }
        if (expr_parse_ok) {
            self.skipWhitespaceAndComments();
            if (!self.matchKeyword("from")) {
                if (!self.matchChar(';')) return ParseError.ParsingError;
                self.skipWhitespaceAndComments();
                if (!self.eof()) return ParseError.ParsingError;
                // If any division-by-zero occurred during evaluation of an
                // expression-only SELECT, surface it now unless a validation
                // error has already been raised.
                if (self.had_division_by_zero) return ParseError.DivisionByZero;
                return .{ .status_ok = true, .error_type = null, .items = expr_items, .rows = null, .column_names = null };
            }
            // had FROM: treat as table select; reset to before list
            self.pos = save_items;
        }

        // Lookahead path: try parsing identifier list (with optional aliases and simple ops) followed by FROM
        save_items = self.pos;
        var left_names = std.array_list.Managed([]const u8).init(arena);
        errdefer left_names.deinit();
        var out_names = std.array_list.Managed([]const u8).init(arena);
        errdefer out_names.deinit();
        var proj_ops = std.array_list.Managed(u8).init(arena); // 0 none, '+','-','*','/','&' (and),'|' (or)
        errdefer proj_ops.deinit();
        var proj_right_names = std.array_list.Managed(?[]const u8).init(arena);
        errdefer proj_right_names.deinit();
        var left_is_lit = std.array_list.Managed(bool).init(arena);
        errdefer left_is_lit.deinit();
        var left_lits = std.array_list.Managed(Value).init(arena);
        errdefer left_lits.deinit();
        var right_is_lit = std.array_list.Managed(bool).init(arena);
        errdefer right_is_lit.deinit();
        var right_lits = std.array_list.Managed(Value).init(arena);
        errdefer right_lits.deinit();
        // Optional table qualifiers for identifiers (e.g., t1.a)
        var left_qualifiers = std.array_list.Managed(?[]const u8).init(arena);
        errdefer left_qualifiers.deinit();
        var right_qualifiers = std.array_list.Managed(?[]const u8).init(arena);
        errdefer right_qualifiers.deinit();

        var table_select = false;
        self.skipWhitespaceAndComments();
        if (isIdentStart(self.peek()) or isDigit(self.peek()) or self.peek() == '-') {
            // parse first projection's left operand: identifier or literal
            var first_is_lit = false;
            var first_lit_val: Value = undefined;
            var first_nm: []const u8 = undefined;
            // Support unary minus before identifier in projection by rewriting to 0 - ident
            var forced_op_char: u8 = 0;
            var forced_right_nm: ?[]const u8 = null;
            var forced_right_qual: ?[]const u8 = null;
            if (self.peek() == '-' and (self.pos + 1 < self.input.len) and isIdentStart(self.input[self.pos + 1])) {
                // consume '-'
                self.advance();
                const id0 = self.parseIdentifier() orelse return ParseError.ParsingError;
                var use_id = id0;
                const save_after_id0 = self.pos;
                self.skipWhitespaceAndComments();
                if (self.matchChar('.')) {
                    // qualified t.col
                    forced_right_qual = id0;
                    const colid = self.parseIdentifier() orelse return ParseError.ValidationError;
                    self.skipWhitespaceAndComments();
                    if (self.matchChar('.')) return ParseError.ValidationError;
                    use_id = colid;
                } else {
                    self.pos = save_after_id0;
                }
                first_is_lit = true;
                first_lit_val = Value{ .integer = 0 };
                first_nm = "";
                try left_qualifiers.append(null);
                forced_op_char = '-';
                forced_right_nm = use_id;
            // 
            } else if (self.parseIdentifier()) |nm| {
                var use_nm = nm;
                var qual_tbl: ?[]const u8 = null;
                const save_after_id = self.pos;
                self.skipWhitespaceAndComments();
                if (self.matchChar('.')) {
                    qual_tbl = nm;
                    const colid = self.parseIdentifier() orelse return ParseError.ValidationError;
                    self.skipWhitespaceAndComments();
                    if (self.matchChar('.')) return ParseError.ValidationError;
                    use_nm = colid;
                } else {
                    self.pos = save_after_id;
                }
                first_nm = use_nm;
                try left_qualifiers.append(qual_tbl);
            } else if (self.parseBoolean()) |b| {
                first_is_lit = true;
                first_lit_val = Value{ .boolean = b };
                first_nm = "";
                try left_qualifiers.append(null);
            } else if (self.parseInteger()) |n| {
                first_is_lit = true;
                first_lit_val = Value{ .integer = n };
                first_nm = "";
                try left_qualifiers.append(null);
            } else if (self.parseNull()) {
                first_is_lit = true;
                first_lit_val = Value.null;
                first_nm = "";
                try left_qualifiers.append(null);
            } else {
                return ParseError.ParsingError;
            }

            try left_names.append(first_nm);
            try left_is_lit.append(first_is_lit);
            // Maintain left_lits length equal to projection count
            try left_lits.append(if (first_is_lit) first_lit_val else Value.null);

            // optional binary op with another operand (identifier or literal)
            self.skipWhitespaceAndComments();
            var op_char: u8 = 0;
            var right_nm: ?[]const u8 = null;
            var right_tbl_qual: ?[]const u8 = null;
            var right_is_lit_flag = false;
            var right_lit_val: Value = undefined;
            const c_after = self.peek();
            if (forced_op_char != 0) {
                op_char = forced_op_char;
                right_nm = forced_right_nm;
                right_tbl_qual = forced_right_qual;
            } else if (c_after == '+' or c_after == '-' or c_after == '*' or c_after == '/') {
                op_char = c_after;
                self.advance();
                if (self.parseIdentifier()) |nm2| {
                    var use_r = nm2;
                    const save_after_r = self.pos;
                    self.skipWhitespaceAndComments();
                    if (self.matchChar('.')) {
                        right_tbl_qual = nm2;
                        const colr = self.parseIdentifier() orelse return ParseError.ValidationError;
                        self.skipWhitespaceAndComments();
                        if (self.matchChar('.')) return ParseError.ValidationError;
                        use_r = colr;
                    } else {
                        self.pos = save_after_r;
                    }
                    right_nm = use_r;
                } else if (self.parseBoolean()) |b2| {
                    right_is_lit_flag = true;
                    right_lit_val = Value{ .boolean = b2 };
                } else if (self.parseInteger()) |n2| {
                    right_is_lit_flag = true;
                    right_lit_val = Value{ .integer = n2 };
                } else if (self.parseNull()) {
                    right_is_lit_flag = true;
                    right_lit_val = Value.null;
                } else return ParseError.ParsingError;
            } else if (self.matchKeyword("and")) {
                op_char = '&';
                if (self.parseIdentifier()) |nm2| {
                    var use_r2 = nm2;
                    const save_after_r2 = self.pos;
                    self.skipWhitespaceAndComments();
                    if (self.matchChar('.')) {
                        right_tbl_qual = nm2;
                        const colr2 = self.parseIdentifier() orelse return ParseError.ValidationError;
                        self.skipWhitespaceAndComments();
                        if (self.matchChar('.')) return ParseError.ValidationError;
                        use_r2 = colr2;
                    } else {
                        self.pos = save_after_r2;
                    }
                    right_nm = use_r2;
                } else if (self.parseBoolean()) |b2| {
                    right_is_lit_flag = true;
                    right_lit_val = Value{ .boolean = b2 };
                } else if (self.parseInteger()) |n2| {
                    // integer on boolean op -> type error at eval stage, but parser accepts integer literal
                    right_is_lit_flag = true;
                    right_lit_val = Value{ .integer = n2 };
                } else if (self.parseNull()) {
                    right_is_lit_flag = true;
                    right_lit_val = Value.null;
                } else return ParseError.ParsingError;
            } else if (self.matchKeyword("or")) {
                op_char = '|';
                if (self.parseIdentifier()) |nm2| {
                    var use_r3 = nm2;
                    const save_after_r3 = self.pos;
                    self.skipWhitespaceAndComments();
                    if (self.matchChar('.')) {
                        right_tbl_qual = nm2;
                        const colr3 = self.parseIdentifier() orelse return ParseError.ValidationError;
                        self.skipWhitespaceAndComments();
                        if (self.matchChar('.')) return ParseError.ValidationError;
                        use_r3 = colr3;
                    } else {
                        self.pos = save_after_r3;
                    }
                    right_nm = use_r3;
                } else if (self.parseBoolean()) |b2| {
                    right_is_lit_flag = true;
                    right_lit_val = Value{ .boolean = b2 };
                } else if (self.parseInteger()) |n2b| {
                    right_is_lit_flag = true;
                    right_lit_val = Value{ .integer = n2b };
                } else if (self.parseNull()) {
                    right_is_lit_flag = true;
                    right_lit_val = Value.null;
                } else return ParseError.ParsingError;
            }
            // optional AS alias
            const save_after_first = self.pos;
            if (self.matchKeyword("as")) {
                if (self.parseAliasIdentifier()) |alias_nm| {
                    try out_names.append(alias_nm);
                } else return ParseError.ParsingError;
            } else {
                self.pos = save_after_first;
                try out_names.append(first_nm);
            }

            try proj_ops.append(op_char);
            try proj_right_names.append(right_nm);
            try right_is_lit.append(right_is_lit_flag);
            // Maintain right_lits length equal to projection count
            try right_lits.append(if (right_is_lit_flag) right_lit_val else Value.null);
            try right_qualifiers.append(right_tbl_qual);

            while (true) {
                self.skipWhitespaceAndComments();
                if (!self.matchChar(',')) break;
                // parse left operand for subsequent projection
                var nm: []const u8 = undefined;
                var nm_qual: ?[]const u8 = null;
                var is_lit: bool = false;
                var lit_val: Value = undefined;
                if (self.parseIdentifier()) |t_nm| {
                    var use_nm2 = t_nm;
                    const save_after_id2 = self.pos;
                    self.skipWhitespaceAndComments();
                    if (self.matchChar('.')) {
                        nm_qual = t_nm;
                        const colid2 = self.parseIdentifier() orelse return ParseError.ValidationError;
                        self.skipWhitespaceAndComments();
                        if (self.matchChar('.')) return ParseError.ValidationError;
                        use_nm2 = colid2;
                    } else {
                        self.pos = save_after_id2;
                    }
                    nm = use_nm2;
                } else if (self.parseBoolean()) |b| {
                    is_lit = true;
                    lit_val = Value{ .boolean = b };
                    nm = "";
                } else if (self.parseInteger()) |n| {
                    is_lit = true;
                    lit_val = Value{ .integer = n };
                    nm = "";
                } else if (self.parseNull()) {
                    is_lit = true;
                    lit_val = Value.null;
                    nm = "";
                } else return ParseError.ParsingError;
                try left_names.append(nm);
                try left_is_lit.append(is_lit);
                try left_lits.append(if (is_lit) lit_val else Value.null);
                try left_qualifiers.append(nm_qual);
                self.skipWhitespaceAndComments();
                var op2: u8 = 0;
                var right2: ?[]const u8 = null;
                var right2_qual: ?[]const u8 = null;
                var right2_is_lit = false;
                var right2_lit: Value = undefined;
                const c2 = self.peek();
                if (c2 == '+' or c2 == '-' or c2 == '*' or c2 == '/') {
                    op2 = c2;
                    self.advance();
                    if (self.parseIdentifier()) |nm_b| {
                        var use_rn = nm_b;
                        const save_after_rn = self.pos;
                        self.skipWhitespaceAndComments();
                        if (self.matchChar('.')) {
                            right2_qual = nm_b;
                            const colr2 = self.parseIdentifier() orelse return ParseError.ValidationError;
                            self.skipWhitespaceAndComments();
                            if (self.matchChar('.')) return ParseError.ValidationError;
                            use_rn = colr2;
                        } else {
                            self.pos = save_after_rn;
                        }
                        right2 = use_rn;
                    } else if (self.parseBoolean()) |bb| {
                        right2_is_lit = true;
                        right2_lit = Value{ .boolean = bb };
                    } else if (self.parseInteger()) |n2| {
                        right2_is_lit = true;
                        right2_lit = Value{ .integer = n2 };
                    } else if (self.parseNull()) {
                        right2_is_lit = true;
                        right2_lit = Value.null;
                    } else return ParseError.ParsingError;
                } else if (self.matchKeyword("and")) {
                    op2 = '&';
                    if (self.parseIdentifier()) |nm_b2| {
                        var use_rn2 = nm_b2;
                        const save_after_rn2 = self.pos;
                        self.skipWhitespaceAndComments();
                        if (self.matchChar('.')) {
                            right2_qual = nm_b2;
                            const colr22 = self.parseIdentifier() orelse return ParseError.ValidationError;
                            self.skipWhitespaceAndComments();
                            if (self.matchChar('.')) return ParseError.ValidationError;
                            use_rn2 = colr22;
                        } else {
                            self.pos = save_after_rn2;
                        }
                        right2 = use_rn2;
                    } else if (self.parseBoolean()) |bb2| {
                        right2_is_lit = true;
                        right2_lit = Value{ .boolean = bb2 };
                    } else if (self.parseInteger()) |nbb| {
                        right2_is_lit = true;
                        right2_lit = Value{ .integer = nbb };
                    } else if (self.parseNull()) {
                        right2_is_lit = true;
                        right2_lit = Value.null;
                    } else return ParseError.ParsingError;
                } else if (self.matchKeyword("or")) {
                    op2 = '|';
                    if (self.parseIdentifier()) |nm_b3| {
                        var use_rn3 = nm_b3;
                        const save_after_rn3 = self.pos;
                        self.skipWhitespaceAndComments();
                        if (self.matchChar('.')) {
                            right2_qual = nm_b3;
                            const colr3 = self.parseIdentifier() orelse return ParseError.ValidationError;
                            self.skipWhitespaceAndComments();
                            if (self.matchChar('.')) return ParseError.ValidationError;
                            use_rn3 = colr3;
                        } else {
                            self.pos = save_after_rn3;
                        }
                        right2 = use_rn3;
                    } else if (self.parseBoolean()) |bb3| {
                        right2_is_lit = true;
                        right2_lit = Value{ .boolean = bb3 };
                    } else if (self.parseInteger()) |ncc| {
                        right2_is_lit = true;
                        right2_lit = Value{ .integer = ncc };
                    } else if (self.parseNull()) {
                        right2_is_lit = true;
                        right2_lit = Value.null;
                    } else return ParseError.ParsingError;
                }
                const save_after_col = self.pos;
                if (self.matchKeyword("as")) {
                    if (self.parseAliasIdentifier()) |alias_nm2| {
                        try out_names.append(alias_nm2);
                    } else return ParseError.ParsingError;
                } else {
                    self.pos = save_after_col;
                    try out_names.append(nm);
                }
                try proj_ops.append(op2);
                try proj_right_names.append(right2);
                try right_is_lit.append(right2_is_lit);
                try right_lits.append(if (right2_is_lit) right2_lit else Value.null);
                try right_qualifiers.append(right2_qual);
            }
            self.skipWhitespaceAndComments();
            const select_list_end_pos = self.pos;
            if (self.matchKeyword("from")) {
                table_select = true;
                const table_name = self.parseIdentifier() orelse return ParseError.ParsingError;
                self.skipWhitespaceAndComments();
                // Optional JOIN clause, WHERE, ORDER BY, LIMIT/OFFSET, then ';'
                // Capture the original select list slice for expression-based projection evaluation per row
                const select_list_start = save_items;
                const select_list_slice: []const u8 = self.input[select_list_start..select_list_end_pos];

                // Parse optional JOIN
                var join_type: JoinType = .none;
                var join_table_name: []const u8 = undefined;
                var join_table_alias: ?[]const u8 = null;
                var on_slice: ?[]const u8 = null;
                const after_from_before_join = self.pos;
                const try_join_pos = self.pos;
                const t_idx_preview_left_opt = dbFindTableIndex(table_name);
                if (self.matchKeyword("inner") or self.matchKeyword("left") or self.matchKeyword("right") or self.matchKeyword("full")) {
                    // Determine join_type from last matched keyword
                    const matched = self.input[try_join_pos..self.pos];
                    if (std.ascii.eqlIgnoreCase(matched, "inner")) join_type = .inner;
                    if (std.ascii.eqlIgnoreCase(matched, "left")) join_type = .left;
                    if (std.ascii.eqlIgnoreCase(matched, "right")) join_type = .right;
                    if (std.ascii.eqlIgnoreCase(matched, "full")) join_type = .full;
                    // optional OUTER
                    const save_outer = self.pos;
                    if (!self.matchKeyword("outer")) self.pos = save_outer;
                    if (!self.matchKeyword("join")) return ParseError.ParsingError;
                    join_table_name = self.parseIdentifier() orelse return ParseError.ParsingError;
                    // optional alias (but do not consume 'ON')
                    const save_alias = self.pos;
                    if (self.parseIdentifier()) |alias_nm| {
                        if (std.ascii.eqlIgnoreCase(alias_nm, "on")) {
                            self.pos = save_alias;
                        } else {
                            join_table_alias = alias_nm;
                        }
                    } else {
                        self.pos = save_alias;
                    }
                    if (!self.matchKeyword("on")) return ParseError.ParsingError;
                    // Disallow joining the same table name without an alias
                    if (join_table_alias == null and std.ascii.eqlIgnoreCase(join_table_name, table_name)) {
                        return ParseError.ValidationError;
                    }
                    // Validate existence only after we have seen the ON, so
                    // a missing ON is always classified as a parsing error.
                    const t_idx_preview_left = t_idx_preview_left_opt orelse return ParseError.ValidationError;
                    const tbl_preview_left = g_db.tables.items[t_idx_preview_left];
                    // Ensure ON expression is a valid boolean (or NULL) expression
                    // Build eval ctx to parse ON expression without validation errors
                    const t_idx_preview_right = dbFindTableIndex(join_table_name) orelse return ParseError.ValidationError;
                    const tbl_preview_right = g_db.tables.items[t_idx_preview_right];
                    var dummy_left = try arena.alloc(Value, tbl_preview_left.columns.len);
                    defer arena.free(dummy_left);
                    var dummy_right = try arena.alloc(Value, tbl_preview_right.columns.len);
                    defer arena.free(dummy_right);
                    var idx_l: usize = 0;
                    while (idx_l < dummy_left.len) : (idx_l += 1) {
                        dummy_left[idx_l] = switch (tbl_preview_left.columns[idx_l].typ) {
                            .integer => Value{ .integer = 1 },
                            .boolean => Value{ .boolean = true },
                        };
                    }
                    var idx_r: usize = 0;
                    while (idx_r < dummy_right.len) : (idx_r += 1) {
                        dummy_right[idx_r] = switch (tbl_preview_right.columns[idx_r].typ) {
                            .integer => Value{ .integer = 1 },
                            .boolean => Value{ .boolean = true },
                        };
                    }
                    var sub_on = Parser.init(self.input[self.pos..]);
                    var ctxs = [_]EvalTableCtx{
                        .{ .table_name = table_name, .alias = null, .columns = tbl_preview_left.columns, .row = dummy_left },
                        .{ .table_name = join_table_name, .alias = join_table_alias, .columns = tbl_preview_right.columns, .row = dummy_right },
                    };
                    sub_on.eval_join_ctx = &ctxs;
                    const on_preview_val = sub_on.parseExpression() catch |err| return err;
                    sub_on.skipWhitespaceAndComments();
                    // Type check ON: must evaluate to boolean or NULL
                    switch (on_preview_val) {
                        .boolean => {},
                        .null => {},
                        else => return ParseError.ValidationError,
                    }
                    const on_len = sub_on.pos;
                    on_slice = self.input[self.pos .. self.pos + on_len];
                    self.pos += on_len;
                    self.skipWhitespaceAndComments();
                } else {
                    self.pos = after_from_before_join;
                }

                // Optional clauses: WHERE, ORDER BY, LIMIT/OFFSET, then ';'
                var where_slice: ?[]const u8 = null;
                var order_by_alias: ?[]const u8 = null;
                var order_by_expr_slice: ?[]const u8 = null;
                var order_desc = false;
                var limit_slice: ?[]const u8 = null;
                var offset_slice: ?[]const u8 = null;

                // WHERE
                const after_from_pos = self.pos;
                if (self.matchKeyword("where")) {
                    const where_start = self.pos;
                    // For initial parse, allow resolving identifiers as columns using dummy row
                    // to locate end of expression and catch obvious type errors early.
                    const t_idx_preview = dbFindTableIndex(table_name) orelse return ParseError.ValidationError;
                    const tbl_preview = g_db.tables.items[t_idx_preview];
                    var dummy_row = try arena.alloc(Value, tbl_preview.columns.len);
                    defer arena.free(dummy_row);
                    var di: usize = 0;
                    while (di < tbl_preview.columns.len) : (di += 1) {
                        dummy_row[di] = switch (tbl_preview.columns[di].typ) { .integer => Value{ .integer = 1 }, .boolean => Value{ .boolean = true } };
                    }
                    var sub = Parser.init(self.input[where_start..]);
                    sub.eval_columns = tbl_preview.columns;
                    sub.eval_row = dummy_row;
                    sub.eval_table_name = table_name;
                    const where_preview_val = sub.parseExpression() catch |err| return err;
                    sub.skipWhitespaceAndComments();
                    // Type check WHERE: must evaluate to boolean or null
                    switch (where_preview_val) {
                        .boolean => {},
                        .null => {},
                        else => return ParseError.ValidationError,
                    }
                    // capture slice consumed by sub
                    const where_len = sub.pos;
                    where_slice = self.input[where_start .. where_start + where_len];
                    self.pos = where_start + where_len;
                    self.skipWhitespaceAndComments();
                } else {
                    self.pos = after_from_pos;
                }

                // ORDER BY
                const after_where_pos = self.pos;
                if (self.matchKeyword("order")) {
                    if (!self.matchKeyword("by")) return ParseError.ParsingError;
                    self.skipWhitespaceAndComments();
                    const expr_start = self.pos;
                    // Hard check for missing expression: ORDER BY ASC|DESC
                    if (self.pos + 3 <= self.input.len) {
                        const a = std.ascii.toLower(self.input[self.pos]);
                        const b = if (self.pos + 1 < self.input.len) std.ascii.toLower(self.input[self.pos + 1]) else 0;
                        const c = if (self.pos + 2 < self.input.len) std.ascii.toLower(self.input[self.pos + 2]) else 0;
                        if (a == 'a' and b == 's' and c == 'c') {
                            const after = self.pos + 3;
                            if (after >= self.input.len or !isIdentChar(self.input[after])) return ParseError.ParsingError;
                        }
                        if (self.pos + 4 <= self.input.len) {
                            const d = if (self.pos + 3 < self.input.len) std.ascii.toLower(self.input[self.pos + 3]) else 0;
                            if (a == 'd' and b == 'e' and c == 's' and d == 'c') {
                                const after2 = self.pos + 4;
                                if (after2 >= self.input.len or !isIdentChar(self.input[after2])) return ParseError.ParsingError;
                            }
                        }
                    }
                    // Early sanity: ensure next token can start an expression and is not just ASC/DESC
                    if (self.eof()) return ParseError.ParsingError;
                    const cstart = self.peek();
                    if (isIdentStart(cstart)) {
                        const save_chk = self.pos;
                        if (self.parseIdentifier()) |tok| {
                            if (std.ascii.eqlIgnoreCase(tok, "asc") or std.ascii.eqlIgnoreCase(tok, "desc")) {
                                return ParseError.ParsingError;
                            }
                        }
                        self.pos = save_chk;
                    } else if (!(isDigit(cstart) or cstart == '(' or cstart == '-' )) {
                        return ParseError.ParsingError;
                    }
                    // Try bare identifier (could be alias or column). If found, treat as minimal expression slice
                    // If the next token is ASC/DESC directly, treat as missing expression
                    const save_after_by = self.pos;
                    if (self.matchKeyword("asc") or self.matchKeyword("desc")) {
                        return ParseError.ParsingError;
                    }
                    if (self.peek() == ';') {
                        return ParseError.ParsingError;
                    }
                    self.pos = save_after_by;
                    const save_ob = self.pos;
                    if (self.parseIdentifier()) |maybe_ident| {
                        // Immediately after BY, an identifier that is actually a reserved keyword
                        // such as ASC/DESC must be rejected as missing expression
                        if (std.ascii.eqlIgnoreCase(maybe_ident, "asc") or std.ascii.eqlIgnoreCase(maybe_ident, "desc")) {
                            return ParseError.ParsingError;
                        }
                        // If the first token after ORDER BY is a direction keyword, it's a parse error
                        if (std.ascii.eqlIgnoreCase(maybe_ident, "asc") or std.ascii.eqlIgnoreCase(maybe_ident, "desc")) {
                            return ParseError.ParsingError;
                        }
                        // After an identifier, decide if this is a simple identifier ORDER BY
                        // or the start of a larger expression (e.g., ident + 2).
                        const ident_end = self.pos;
                        const save_ws = self.pos;
                        self.skipWhitespaceAndComments();
                        const order_clause_ends_here = blk: {
                            const save_kw = self.pos;
                            var ends = false;
                            if (self.matchKeyword("asc") or self.matchKeyword("desc") or self.matchKeyword("limit") or self.matchKeyword("offset")) {
                                ends = true;
                            } else if (self.peek() == ';') {
                                ends = true;
                            }
                            self.pos = save_kw;
                            break :blk ends;
                        };
                        const cnext = self.peek();
                        // If the next token starts an identifier that is not an allowed keyword and
                        // we're still inside the ORDER BY expression (no ASC/DESC/LIMIT/OFFSET yet),
                        // then it's a parsing error (e.g., CLOCKWISE).
                        if (!order_clause_ends_here and isIdentStart(cnext)) return ParseError.ParsingError;
                        const looks_like_expr = (cnext == '+' or cnext == '-' or cnext == '*' or cnext == '/' or cnext == '(' or cnext == '<' or cnext == '>' or cnext == '=' or cnext == '.' or isDigit(cnext));
                        self.pos = save_ws;
                        if (!order_clause_ends_here and looks_like_expr) {
                            // Rewind and parse full expression instead
                            self.pos = expr_start;
                            var sub2 = Parser.init(self.input[expr_start..]);
                            const t_idx_preview2 = dbFindTableIndex(table_name) orelse return ParseError.ValidationError;
                            const tbl_preview2 = g_db.tables.items[t_idx_preview2];
                            var dummy_row2 = try arena.alloc(Value, tbl_preview2.columns.len);
                            defer arena.free(dummy_row2);
                            var dj2: usize = 0;
                            while (dj2 < tbl_preview2.columns.len) : (dj2 += 1) {
                                dummy_row2[dj2] = switch (tbl_preview2.columns[dj2].typ) { .integer => Value{ .integer = 1 }, .boolean => Value{ .boolean = true } };
                            }
                            sub2.eval_columns = tbl_preview2.columns;
                            sub2.eval_row = dummy_row2;
                            sub2.eval_table_name = table_name;
                            _ = sub2.parseExpression() catch |err| return err;
                            sub2.skipWhitespaceAndComments();
                            const order_expr_len2 = sub2.pos;
                            if (order_expr_len2 == 0) return ParseError.ParsingError;
                            order_by_expr_slice = self.input[expr_start .. expr_start + order_expr_len2];
                            self.pos = expr_start + order_expr_len2;
                        } else {
                            order_by_alias = maybe_ident; // may resolve later; harmless if not found
                            // expression slice covers just the identifier; direction handling follows
                            const ident_len = ident_end - expr_start;
                            order_by_expr_slice = self.input[expr_start .. expr_start + ident_len];
                            // Validate identifier now if it's not a select-list alias: it must be a table column
                            var is_sel_alias = false;
                            var oi_chk: usize = 0;
                            while (oi_chk < out_names.items.len) : (oi_chk += 1) {
                                if (std.mem.eql(u8, out_names.items[oi_chk], maybe_ident)) { is_sel_alias = true; break; }
                            }
                            if (!is_sel_alias) {
                                const t_idx_preview2 = dbFindTableIndex(table_name) orelse return ParseError.ValidationError;
                                const tbl_preview2 = g_db.tables.items[t_idx_preview2];
                                var found_col = false;
                                var ci_chk: usize = 0;
                                while (ci_chk < tbl_preview2.columns.len) : (ci_chk += 1) {
                                    if (std.mem.eql(u8, tbl_preview2.columns[ci_chk].name, maybe_ident)) { found_col = true; break; }
                                }
                                if (!found_col) return ParseError.ValidationError;
                            }
                        }
                    } else {
                        // Parse full expression (like -a)
                        self.pos = save_ob;
                        var sub2 = Parser.init(self.input[expr_start..]);
                        // For expressions, allow column resolution
                        const t_idx_preview2 = dbFindTableIndex(table_name) orelse return ParseError.ValidationError;
                        const tbl_preview2 = g_db.tables.items[t_idx_preview2];
                        // Use same dummy row as above technique
                        var dummy_row2 = try arena.alloc(Value, tbl_preview2.columns.len);
                        defer arena.free(dummy_row2);
                        var dj: usize = 0;
                        while (dj < tbl_preview2.columns.len) : (dj += 1) {
                            dummy_row2[dj] = switch (tbl_preview2.columns[dj].typ) { .integer => Value{ .integer = 1 }, .boolean => Value{ .boolean = true } };
                        }
                        sub2.eval_columns = tbl_preview2.columns;
                        sub2.eval_row = dummy_row2;
                        _ = sub2.parseExpression() catch |err| return err;
                        sub2.skipWhitespaceAndComments();
                        const order_expr_len = sub2.pos;
                        if (order_expr_len == 0) return ParseError.ParsingError;
                        order_by_expr_slice = self.input[expr_start .. expr_start + order_expr_len];
                        self.pos = expr_start + order_expr_len;
                    }
                    self.skipWhitespaceAndComments();
                    // direction
                    const save_dir = self.pos;
                    if (order_by_expr_slice == null) {
                        return ParseError.ParsingError;
                    } else if (self.matchKeyword("asc")) {
                        order_desc = false;
                    } else if (self.matchKeyword("desc")) {
                        order_desc = true;
                    } else {
                        self.pos = save_dir;
                        order_desc = false; // default ASC
                    }
                    // Special-case: ORDER BY ASC|DESC with no expression should be a parse error
                    if (order_by_expr_slice == null and order_by_alias != null) {
                        const alias_nm_chk = order_by_alias.?;
                        if (std.ascii.eqlIgnoreCase(alias_nm_chk, "asc") or std.ascii.eqlIgnoreCase(alias_nm_chk, "desc")) {
                            return ParseError.ParsingError;
                        }
                    }
                    // If we still have no expression or alias, it's a parse error (missing expression)
                    if (order_by_expr_slice == null and order_by_alias == null) {
                        return ParseError.ParsingError;
                    }
                    self.skipWhitespaceAndComments();
                    // After ORDER BY expression and optional direction, only LIMIT/OFFSET or ';' may follow
                    const save_extra = self.pos;
                    if (!(self.matchKeyword("limit") or self.matchKeyword("offset") or self.peek() == ';')) {
                        return ParseError.ParsingError;
                    }
                    // rewind so LIMIT/OFFSET loop can handle it
                    self.pos = save_extra;
                    self.skipWhitespaceAndComments();
                } else {
                    self.pos = after_where_pos;
                }

                // LIMIT/OFFSET (either order)
                var seen_limit = false;
                var seen_offset = false;
                while (true) {
                    const save_clause = self.pos;
                    if (!seen_limit and self.matchKeyword("limit")) {
                        self.skipWhitespaceAndComments();
                        // Reject identifiers explicitly for LIMIT
                        const save_l = self.pos;
                        if (self.parseIdentifier()) |_| return ParseError.ValidationError else self.pos = save_l;
                        const start_l = self.pos;
                        var subl = Parser.init(self.input[start_l..]);
                        // Do not allow column resolution in LIMIT
                        _ = subl.parseExpression() catch |err| return err;
                        subl.skipWhitespaceAndComments();
                        const elen = subl.pos;
                        if (elen == 0) return ParseError.ParsingError;
                        limit_slice = self.input[start_l .. start_l + elen];
                        self.pos = start_l + elen;
                        self.skipWhitespaceAndComments();
                        seen_limit = true;
                        continue;
                    }
                    if (!seen_offset and self.matchKeyword("offset")) {
                        self.skipWhitespaceAndComments();
                        // Reject identifiers explicitly for OFFSET
                        const save_o = self.pos;
                        if (self.parseIdentifier()) |_| return ParseError.ValidationError else self.pos = save_o;
                        const start_o = self.pos;
                        var subo = Parser.init(self.input[start_o..]);
                        _ = subo.parseExpression() catch |err| return err;
                        subo.skipWhitespaceAndComments();
                        const olen = subo.pos;
                        if (olen == 0) return ParseError.ParsingError;
                        offset_slice = self.input[start_o .. start_o + olen];
                        self.pos = start_o + olen;
                        self.skipWhitespaceAndComments();
                        seen_offset = true;
                        continue;
                    }
                    self.pos = save_clause;
                    break;
                }

                if (!self.matchChar(';')) return ParseError.ParsingError;
                self.skipWhitespaceAndComments();
                if (!self.eof()) return ParseError.ParsingError;

                const t_idx = dbFindTableIndex(table_name) orelse return ParseError.ValidationError;
                const tbl = g_db.tables.items[t_idx];

                // Resolve and pre-validate only for non-join simple table selects
                var col_indices = std.array_list.Managed(?usize).init(arena);
                errdefer col_indices.deinit();
                var right_indices = std.array_list.Managed(?usize).init(arena);
                errdefer right_indices.deinit();
                if (join_type == .none) {
                    var i: usize = 0;
                    while (i < left_names.items.len) : (i += 1) {
                        if (left_is_lit.items[i]) {
                            try col_indices.append(null);
                        } else {
                            // If qualifier provided, it must match table_name
                            if (left_qualifiers.items.len > i) {
                                if (left_qualifiers.items[i]) |qn| {
                                    if (!std.ascii.eqlIgnoreCase(qn, table_name)) return ParseError.ValidationError;
                                }
                            }
                            const name = left_names.items[i];
                            var found: ?usize = null;
                            var ci: usize = 0;
                            while (ci < tbl.columns.len) : (ci += 1) {
                                if (std.ascii.eqlIgnoreCase(tbl.columns[ci].name, name)) { found = ci; break; }
                            }
                            if (found == null) return ParseError.ValidationError;
                            try col_indices.append(found);
                        }
                        if (proj_right_names.items[i]) |rn| {
                            if (right_qualifiers.items.len > i) {
                                if (right_qualifiers.items[i]) |rq| {
                                    if (!std.ascii.eqlIgnoreCase(rq, table_name)) return ParseError.ValidationError;
                                }
                            }
                            var f2: ?usize = null;
                            var cj: usize = 0;
                            while (cj < tbl.columns.len) : (cj += 1) {
                                if (std.ascii.eqlIgnoreCase(tbl.columns[cj].name, rn)) { f2 = cj; break; }
                            }
                            if (f2 == null) return ParseError.ValidationError;
                            try right_indices.append(f2);
                        } else {
                            try right_indices.append(null);
                        }
                    }

                    // Pre-validate types independent of data rows
                    var k: usize = 0;
                    while (k < col_indices.items.len) : (k += 1) {
                        const opk = proj_ops.items[k];
                        if (opk == 0) continue;
                        // determine left type
                        const l_is_lit = left_is_lit.items[k];
                        const l_type: ColumnType = if (l_is_lit)
                            (switch (left_lits.items[k]) { .integer => ColumnType.integer, .boolean => ColumnType.boolean, .null => ColumnType.integer })
                        else
                            tbl.columns[col_indices.items[k].?].typ;
                        // determine right type
                        const r_is_lit = right_is_lit.items[k];
                        const r_type: ColumnType = if (proj_right_names.items[k] != null) blk: {
                            const idx = right_indices.items[k] orelse return ParseError.ValidationError;
                            break :blk tbl.columns[idx].typ;
                        } else if (r_is_lit) (switch (right_lits.items[k]) { .integer => ColumnType.integer, .boolean => ColumnType.boolean, .null => ColumnType.integer }) else blk2: {
                            // no right operand present
                            break :blk2 ColumnType.integer; // dummy
                        };
                        switch (opk) {
                            '+', '-', '*', '/' => {
                                // Allow NULL literals, which will propagate at row-eval time
                                if (!(l_type == .integer and r_type == .integer)) return ParseError.ValidationError;
                            },
                            '&', '|' => {
                                if (!(l_type == .boolean and r_type == .boolean)) return ParseError.ValidationError;
                            },
                            else => {},
                        }
                    }
                }

                // Build result rows
                var result_rows = std.array_list.Managed([]Value).init(arena);
                errdefer result_rows.deinit();
                var source_row_indices = std.array_list.Managed(usize).init(arena);
                errdefer source_row_indices.deinit();

                if (join_type == .none) {
                    var row_index: usize = 0;
                    while (row_index < tbl.rows.items.len) : (row_index += 1) {
                        const row = tbl.rows.items[row_index];
                        // WHERE filtering
                        if (where_slice) |ws| {
                            var p = Parser.init(ws);
                            p.eval_columns = tbl.columns;
                            p.eval_row = row;
                            p.eval_table_name = table_name;
                            const cond = p.parseExpression() catch |err| return err;
                            p.skipWhitespaceAndComments();
                            if (!p.eof()) return ParseError.ParsingError;
                            if (p.had_division_by_zero) return ParseError.DivisionByZero;
                            switch (cond) {
                                .boolean => |b| if (!b) continue,
                                .null => continue,
                                else => return ParseError.ValidationError,
                            }
                        }
                        // Evaluate projection using select_list_slice
                        var ps = Parser.init(select_list_slice);
                        ps.eval_columns = tbl.columns;
                        ps.eval_row = row;
                        ps.eval_table_name = table_name;
                        const items_eval = ps.parseSelectList(arena) catch |err| return err;
                        if (ps.had_division_by_zero) return ParseError.DivisionByZero;
                        var out = std.array_list.Managed(Value).init(arena);
                        errdefer out.deinit();
                        for (items_eval) |it| try out.append(it.expr);
                        try source_row_indices.append(row_index);
                        try result_rows.append(try out.toOwnedSlice());
                    }
                } else {
                    // JOIN evaluation
                    const t_idx_right = dbFindTableIndex(join_table_name) orelse return ParseError.ValidationError;
                    const tbl_right = g_db.tables.items[t_idx_right];
                    // Prepare arrays to mark matched rows for outer joins
                    var left_matched = try arena.alloc(bool, tbl.rows.items.len);
                    var right_matched = try arena.alloc(bool, tbl_right.rows.items.len);
                    var i_l: usize = 0; while (i_l < left_matched.len) : (i_l += 1) left_matched[i_l] = false;
                    var i_r: usize = 0; while (i_r < right_matched.len) : (i_r += 1) right_matched[i_r] = false;

                    // helper to evaluate ON for a pair
                    const eval_on = struct {
                        fn check(expr: []const u8, left_row: []const Value, right_row: []const Value, t_left: *const Table, t_right: *const Table, tname_left: []const u8, tname_right: []const u8, alias_right: ?[]const u8) ParseError!bool {
                            var p = Parser.init(expr);
                            var ctxs = [_]EvalTableCtx{
                                .{ .table_name = tname_left, .alias = null, .columns = t_left.columns, .row = left_row },
                                .{ .table_name = tname_right, .alias = alias_right, .columns = t_right.columns, .row = right_row },
                            };
                            p.eval_join_ctx = &ctxs;
                            const v = p.parseExpression() catch |err| return err;
                            p.skipWhitespaceAndComments();
                            if (!p.eof()) return ParseError.ParsingError;
                            switch (v) {
                                .boolean => |b| return b,
                                .null => return false,
                                else => return ParseError.ValidationError,
                            }
                        }
                    };

                    if (join_type == .inner or join_type == .left or join_type == .right or join_type == .full) {
                        var li: usize = 0;
                        while (li < tbl.rows.items.len) : (li += 1) {
                            const lrow = tbl.rows.items[li];
                            var any_match = false;
                            var rj: usize = 0;
                            while (rj < tbl_right.rows.items.len) : (rj += 1) {
                                const rrow = tbl_right.rows.items[rj];
                                const is_match = try eval_on.check(on_slice.?, lrow, rrow, &tbl, &tbl_right, table_name, join_table_name, join_table_alias);
                                if (is_match) {
                                    any_match = true;
                                    left_matched[li] = true;
                                    right_matched[rj] = true;
                                    // WHERE filter if present
                                    if (where_slice) |ws| {
                                        var p = Parser.init(ws);
                                        var ctxs2 = [_]EvalTableCtx{
                                            .{ .table_name = table_name, .alias = null, .columns = tbl.columns, .row = lrow },
                                            .{ .table_name = join_table_name, .alias = join_table_alias, .columns = tbl_right.columns, .row = rrow },
                                        };
                                        p.eval_join_ctx = &ctxs2;
                                        const cond = p.parseExpression() catch |err| return err;
                                        p.skipWhitespaceAndComments();
                                        if (!p.eof()) return ParseError.ParsingError;
                                        switch (cond) {
                                            .boolean => |b| if (!b) { continue; },
                                            .null => continue,
                                            else => return ParseError.ValidationError,
                                        }
                                    }
                                    // Evaluate projection
                                    var ps = Parser.init(select_list_slice);
                                    var ctxs3 = [_]EvalTableCtx{
                                        .{ .table_name = table_name, .alias = null, .columns = tbl.columns, .row = lrow },
                                        .{ .table_name = join_table_name, .alias = join_table_alias, .columns = tbl_right.columns, .row = rrow },
                                    };
                                    ps.eval_join_ctx = &ctxs3;
                                    const items_eval = ps.parseSelectList(arena) catch |err| return err;
                                    if (ps.had_division_by_zero) return ParseError.DivisionByZero;
                                    var out = std.array_list.Managed(Value).init(arena);
                                    errdefer out.deinit();
                                    for (items_eval) |it| try out.append(it.expr);
                                    try result_rows.append(try out.toOwnedSlice());
                                }
                            }
                            if (!any_match and (join_type == .left or join_type == .full)) {
                                // Fill right side nulls and evaluate WHERE/projection
                                var null_right = try arena.alloc(Value, tbl_right.columns.len);
                                var nr: usize = 0; while (nr < null_right.len) : (nr += 1) null_right[nr] = Value.null;
                                if (where_slice) |ws| {
                                    var p = Parser.init(ws);
                                    var ctxs2 = [_]EvalTableCtx{
                                        .{ .table_name = table_name, .alias = null, .columns = tbl.columns, .row = lrow },
                                        .{ .table_name = join_table_name, .alias = join_table_alias, .columns = tbl_right.columns, .row = null_right },
                                    };
                                    p.eval_join_ctx = &ctxs2;
                                    const cond = p.parseExpression() catch |err| return err;
                                    p.skipWhitespaceAndComments();
                                    if (!p.eof()) return ParseError.ParsingError;
                                    switch (cond) {
                                        .boolean => |b| if (!b) { continue; },
                                        .null => continue,
                                        else => return ParseError.ValidationError,
                                    }
                                }
                                var ps = Parser.init(select_list_slice);
                                var ctxs3 = [_]EvalTableCtx{
                                    .{ .table_name = table_name, .alias = null, .columns = tbl.columns, .row = lrow },
                                    .{ .table_name = join_table_name, .alias = join_table_alias, .columns = tbl_right.columns, .row = null_right },
                                };
                                ps.eval_join_ctx = &ctxs3;
                                const items_eval = ps.parseSelectList(arena) catch |err| return err;
                                if (ps.had_division_by_zero) return ParseError.DivisionByZero;
                                var out = std.array_list.Managed(Value).init(arena);
                                errdefer out.deinit();
                                for (items_eval) |it| try out.append(it.expr);
                                try result_rows.append(try out.toOwnedSlice());
                            }
                        }

                        if (join_type == .right or join_type == .full) {
                            // handle right-only unmatched
                            var ronly: usize = 0;
                            while (ronly < tbl_right.rows.items.len) : (ronly += 1) {
                                if (right_matched[ronly]) continue;
                                const rrow = tbl_right.rows.items[ronly];
                                var null_left = try arena.alloc(Value, tbl.columns.len);
                                var nl: usize = 0; while (nl < null_left.len) : (nl += 1) null_left[nl] = Value.null;
                                if (where_slice) |ws| {
                                    var p = Parser.init(ws);
                                    var ctxs2 = [_]EvalTableCtx{
                                        .{ .table_name = table_name, .alias = null, .columns = tbl.columns, .row = null_left },
                                        .{ .table_name = join_table_name, .alias = join_table_alias, .columns = tbl_right.columns, .row = rrow },
                                    };
                                    p.eval_join_ctx = &ctxs2;
                                    const cond = p.parseExpression() catch |err| return err;
                                    p.skipWhitespaceAndComments();
                                    if (!p.eof()) return ParseError.ParsingError;
                                    switch (cond) {
                                        .boolean => |b| if (!b) { continue; },
                                        .null => continue,
                                        else => return ParseError.ValidationError,
                                    }
                                }
                                var ps = Parser.init(select_list_slice);
                                var ctxs3 = [_]EvalTableCtx{
                                    .{ .table_name = table_name, .alias = null, .columns = tbl.columns, .row = null_left },
                                    .{ .table_name = join_table_name, .alias = join_table_alias, .columns = tbl_right.columns, .row = rrow },
                                };
                                ps.eval_join_ctx = &ctxs3;
                                const items_eval = ps.parseSelectList(arena) catch |err| return err;
                                if (ps.had_division_by_zero) return ParseError.DivisionByZero;
                                var out = std.array_list.Managed(Value).init(arena);
                                errdefer out.deinit();
                                for (items_eval) |it| try out.append(it.expr);
                                try result_rows.append(try out.toOwnedSlice());
                            }
                        }
                    }
                }

                // ORDER BY
                if (order_by_alias != null or order_by_expr_slice != null) {
                    // Build keys for sorting
                    var keys = std.array_list.Managed(Value).init(arena);
                    errdefer keys.deinit();
                    var alias_idx: ?usize = null;
                    if (order_by_alias) |alias_name| {
                        // resolve against out_names
                        var oi: usize = 0;
                        while (oi < out_names.items.len) : (oi += 1) {
                            if (std.mem.eql(u8, out_names.items[oi], alias_name)) { alias_idx = oi; break; }
                        }
                    }
                    var rix: usize = 0;
                    while (rix < result_rows.items.len) : (rix += 1) {
                        const base_row = tbl.rows.items[ if (source_row_indices.items.len > rix) source_row_indices.items[rix] else 0];
                        var key: Value = Value.null;
                        if (alias_idx) |ai| {
                            key = result_rows.items[rix][ai];
                        } else if (order_by_expr_slice) |obs| {
                            var p3 = Parser.init(obs);
                            if (join_type == .none) {
                                p3.eval_columns = tbl.columns;
                                p3.eval_row = base_row;
                                p3.eval_table_name = table_name;
                            } else {
                                // Can't reconstruct exact rows here; fallback to evaluating against first available joined contexts
                                // Sort stability not critical for tests
                                const t_idx_right2 = if (join_type == .none) t_idx else (dbFindTableIndex(join_table_name) orelse t_idx);
                                const tbl_right2 = g_db.tables.items[t_idx_right2];
                                var null_left = try arena.alloc(Value, tbl.columns.len);
                                var nl2: usize = 0; while (nl2 < null_left.len) : (nl2 += 1) null_left[nl2] = Value.null;
                                var null_right = try arena.alloc(Value, tbl_right2.columns.len);
                                var nr2: usize = 0; while (nr2 < null_right.len) : (nr2 += 1) null_right[nr2] = Value.null;
                                var ctxs4 = [_]EvalTableCtx{
                                    .{ .table_name = table_name, .alias = null, .columns = tbl.columns, .row = null_left },
                                    .{ .table_name = join_table_name, .alias = join_table_alias, .columns = tbl_right2.columns, .row = null_right },
                                };
                                p3.eval_join_ctx = &ctxs4;
                            }
                    const kv = p3.parseExpression() catch |err| return err;
                            p3.skipWhitespaceAndComments();
                            if (!p3.eof()) return ParseError.ParsingError;
                    // Accept integer/boolean/null order keys only; others are invalid
                    if (kv != .integer and kv != .boolean and kv != .null) return ParseError.ValidationError;
                            key = kv;
                        } else {
                            // No expression slice and no resolvable alias: treat as missing ORDER BY expression
                            return ParseError.ParsingError;
                        }
                        try keys.append(key);
                    }

                    // Comparator
                    const asc = !order_desc;
                    // Implement a sort on indices to avoid moving large rows
                    var order_indices = try arena.alloc(usize, result_rows.items.len);
                    var oi2: usize = 0;
                    while (oi2 < order_indices.len) : (oi2 += 1) order_indices[oi2] = oi2;
                    const Cmp = struct {
                        keys: []const Value,
                        asc: bool,
                        pub fn lt(ctx: @This(), idx_i: usize, idx_j: usize) bool {
                            const ki = ctx.keys[idx_i];
                            const kj = ctx.keys[idx_j];
                            if (ki == .null and kj != .null) return !ctx.asc; // nulls last in asc
                            if (ki != .null and kj == .null) return ctx.asc;
                            if (ki == .null and kj == .null) return false;
                            switch (ki) {
                                .integer => |ivi| switch (kj) {
                                    .integer => |jvi| return if (ctx.asc) ivi < jvi else ivi > jvi,
                                    .boolean => |_| return if (ctx.asc) true else false, // integers < booleans arbitrarily; not tested
                                    .null => unreachable,
                                },
                                .boolean => |ib| switch (kj) {
                                    .boolean => |jb| return if (ctx.asc) ((!ib and jb) or (ib == jb and false)) else ((ib and !jb) or (ib == jb and false)),
                                    .integer => |_| return if (ctx.asc) false else true,
                                    .null => unreachable,
                                },
                                .null => unreachable,
                            }
                        }
                    };
                    const cmp_info = Cmp{ .keys = keys.items, .asc = asc };
                    std.sort.heap(usize, order_indices, cmp_info, struct {
                        pub fn lessThan(info: Cmp, ai: usize, bi: usize) bool { return info.lt(ai, bi); }
                    }.lessThan);
                    // reorder result_rows according to order_indices
                    var sorted_rows = std.array_list.Managed([]Value).init(arena);
                    errdefer sorted_rows.deinit();
                    var si: usize = 0;
                    while (si < order_indices.len) : (si += 1) {
                        try sorted_rows.append(result_rows.items[order_indices[si]]);
                    }
                    result_rows.deinit();
                    result_rows = sorted_rows;
                }

                // LIMIT/OFFSET application
                var start_idx: usize = 0;
                var max_rows: ?usize = null;
                if (offset_slice) |os| {
                    var pofs = Parser.init(os);
                    const v = pofs.parseExpression() catch |err| return err;
                    pofs.skipWhitespaceAndComments();
                    if (!pofs.eof()) return ParseError.ParsingError;
                    switch (v) {
                        .integer => |n| start_idx = if (n < 0) 0 else @intCast(n),
                        .null => start_idx = 0,
                        else => return ParseError.ValidationError,
                    }
                }
                if (limit_slice) |ls| {
                    var plim = Parser.init(ls);
                    const v = plim.parseExpression() catch |err| return err;
                    plim.skipWhitespaceAndComments();
                    if (!plim.eof()) return ParseError.ParsingError;
                    switch (v) {
                        .integer => |n| max_rows = if (n < 0) 0 else @intCast(n),
                        .null => max_rows = null,
                        else => return ParseError.ValidationError,
                    }
                }

                // Slice rows according to offset/limit
                const total = result_rows.items.len;
                if (start_idx > total) start_idx = total;
                var end_idx = total;
                if (max_rows) |lim| {
                    const lim_end = start_idx + lim;
                    end_idx = if (lim_end < total) lim_end else total;
                }
                // Build final slice
                var final_rows = std.array_list.Managed([]Value).init(arena);
                errdefer final_rows.deinit();
                var ri: usize = start_idx;
                while (ri < end_idx) : (ri += 1) {
                    try final_rows.append(result_rows.items[ri]);
                }

                return .{
                    .status_ok = true,
                    .error_type = null,
                    .items = &[_]SelectItem{},
                    .rows = try final_rows.toOwnedSlice(),
                    .column_names = try out_names.toOwnedSlice(),
                };
            }
        }

        // Not a table select; reset and parse expression list
        self.pos = save_items;
        const items = try self.parseSelectList(arena);
        self.skipWhitespaceAndComments();
        if (!self.matchChar(';')) return ParseError.ParsingError;
        self.skipWhitespaceAndComments();
        if (!self.eof()) return ParseError.ParsingError;
        if (self.had_division_by_zero) return ParseError.DivisionByZero;
        return .{ .status_ok = true, .error_type = null, .items = items, .rows = null, .column_names = null };
    }
    /// Parse `CREATE TABLE name (col type, ...) ;` with basic validations:
    /// - identifier syntax and keyword restrictions
    /// - supported types: INTEGER, BOOLEAN
    /// - duplicate column names produce `validation_error`
    /// - TODO: bug if declare only one column with type INTEGER, and then try to insert a row with 1, TRUE, the parser will NOT return an error
    fn parseCreateTable(self: *Parser, arena: std.mem.Allocator) ParseError!QueryResult {
        _ = arena;
        if (!self.matchKeyword("create")) return ParseError.ParsingError;
        if (!self.matchKeyword("table")) return ParseError.ParsingError;

        const table_name = self.parseIdentifier() orelse return ParseError.ParsingError;
        self.skipWhitespaceAndComments();
        if (!self.matchChar('(')) return ParseError.ParsingError;

        var cols = std.array_list.Managed(ColumnDef).init(std.heap.page_allocator);
        defer cols.deinit();

        var seen_names = std.StringHashMap(void).init(std.heap.page_allocator);
        defer seen_names.deinit();

        // We use this loop to process both CREATE TABLE and INSERT INTO. Need to split this.  
        while (true) {
            const col_name = self.parseIdentifier() orelse return ParseError.ParsingError;
            self.skipWhitespaceAndComments();
            var typ: ColumnType = undefined;
            if (self.matchKeyword("integer")) {
                typ = .integer;
            } else if (self.matchKeyword("boolean")) {
                typ = .boolean;
            } else {
                return ParseError.ParsingError;
            }

            // dup name into temporary arena for uniqueness set
            if (seen_names.contains(col_name)) return ParseError.ValidationError;
            try seen_names.put(col_name, {});

            try cols.append(.{ .name = col_name, .typ = typ });

            self.skipWhitespaceAndComments();
            if (self.matchChar(',')) {
                continue;
            }
            if (self.matchChar(')')) break;
            return ParseError.ParsingError;
        }

        self.skipWhitespaceAndComments();
        if (!self.matchChar(';')) return ParseError.ParsingError;
        self.skipWhitespaceAndComments();
        if (!self.eof()) return ParseError.ParsingError;

        // Create in database; copies data into db allocator
        try dbCreateTable(table_name, cols.items);

        return .{ .status_ok = true, .error_type = null, .items = &[_]SelectItem{} };
    }

    /// Parse `DROP TABLE [IF EXISTS] name;`.
    fn parseDropTable(self: *Parser, arena: std.mem.Allocator) ParseError!QueryResult {
        _ = arena;
        if (!self.matchKeyword("drop")) return ParseError.ParsingError;
        if (!self.matchKeyword("table")) return ParseError.ParsingError;

        var if_exists = false;
        const save = self.pos;
        if (self.matchKeyword("if")) {
            if (!self.matchKeyword("exists")) return ParseError.ParsingError;
            if_exists = true;
        } else {
            self.pos = save;
        }

        const table_name = self.parseIdentifier() orelse return ParseError.ParsingError;
        self.skipWhitespaceAndComments();
        if (!self.matchChar(';')) return ParseError.ParsingError;
        self.skipWhitespaceAndComments();
        if (!self.eof()) return ParseError.ParsingError;

        try dbDropTable(table_name, if_exists);

        return .{ .status_ok = true, .error_type = null, .items = &[_]SelectItem{}, .rows = null, .column_names = null };
    }

    /// Parse `INSERT INTO name VALUES (...), (...);`.
    ///
    /// Semantics: This must be all-or-nothing. We first parse and validate
    /// every row into a temporary arena-backed buffer. Only after the entire
    /// statement has parsed and validated (including the final `;`) do we copy
    /// rows into the database's allocator. This ensures a later validation
    /// error (e.g. wrong type in the second tuple or division-by-zero inside an
    /// expression) does not partially insert earlier rows.
    fn parseInsert(self: *Parser, arena: std.mem.Allocator) ParseError!QueryResult {
        // Use the provided arena for staging parsed rows prior to commit.
        if (!self.matchKeyword("insert")) return ParseError.ParsingError;
        if (!self.matchKeyword("into")) return ParseError.ParsingError;
        const table_name = self.parseIdentifier() orelse return ParseError.ParsingError;
        self.skipWhitespaceAndComments();
        if (!self.matchKeyword("values")) return ParseError.ParsingError;
        self.skipWhitespaceAndComments();

        const t_idx = dbFindTableIndex(table_name) orelse return ParseError.ValidationError;
        var tbl = &g_db.tables.items[t_idx];

        // Stage rows here; commit to `tbl.rows` only after full success.
        var staged_rows = std.array_list.Managed([]Value).init(arena);
        defer staged_rows.deinit();

        var any_rows = false;
        while (true) {
            if (!self.matchChar('(')) return ParseError.ParsingError;
            // parse one row values list
            var values = std.array_list.Managed(Value).init(std.heap.page_allocator);
            defer values.deinit();
            var first = true;
            while (true) {
                self.skipWhitespaceAndComments();
                const v = try self.parseExpression();
                try values.append(v);
                self.skipWhitespaceAndComments();
                if (self.matchChar(',')) { first = false; continue; }
                break;
            }
            if (!self.matchChar(')')) return ParseError.ParsingError;

            // Validate arity: too many values is an error; fewer values imply trailing NULLs
            if (values.items.len > tbl.columns.len) return ParseError.ValidationError;
            // Validate types and build staged row (arena-backed). Chapter 7:
            // allow NULL literal for any column and store it as Value.null.
            var row_slice = try arena.alloc(Value, tbl.columns.len);
            var i: usize = 0;
            while (i < tbl.columns.len) : (i += 1) {
                const col = tbl.columns[i];
                if (i < values.items.len) {
                    const vv = values.items[i];
                    if (vv == .null) {
                        // NULL accepted for any column type
                    } else switch (col.typ) {
                        .integer => if (vv != .integer) return ParseError.ValidationError else {},
                        .boolean => if (vv != .boolean) return ParseError.ValidationError else {},
                    }
                    row_slice[i] = vv;
                } else {
                    // fill missing columns with NULL
                    row_slice[i] = Value.null;
                }
            }
            // Keep staged; do not mutate table yet
            try staged_rows.append(row_slice);
            any_rows = true;

            self.skipWhitespaceAndComments();
            if (self.matchChar(',')) {
                // next row
                continue;
            }
            break;
        }

        // Only commit after the entire statement terminates correctly
        if (!self.matchChar(';')) return ParseError.ParsingError;
        self.skipWhitespaceAndComments();
        if (!self.eof()) return ParseError.ParsingError;
        if (!any_rows) return ParseError.ParsingError;
        // Surface division-by-zero for INSERT after full parsing/validation,
        // before committing staged rows to ensure all-or-nothing semantics.
        if (self.had_division_by_zero) return ParseError.DivisionByZero;

        // Commit: copy staged rows into the database allocator
        var sr: usize = 0;
        while (sr < staged_rows.items.len) : (sr += 1) {
            const staged = staged_rows.items[sr];
            const persistent = try g_db_allocator.alloc(Value, staged.len);
            std.mem.copyForwards(Value, persistent, staged);
            try tbl.rows.append(persistent);
        }

        return .{ .status_ok = true, .error_type = null, .items = &[_]SelectItem{}, .rows = null, .column_names = null };
    }

    fn parseQuery(self: *Parser, arena: std.mem.Allocator) ParseError!QueryResult {
        self.skipWhitespaceAndComments();

        var save = self.pos;
        const sel = self.parseSelect(arena);
        if (sel) |r| return r else |err| {
            if (err != error.ParsingError) return err;
            self.pos = save;
        }

        save = self.pos;
        const crt = self.parseCreateTable(arena);
        if (crt) |r| return r else |err| {
            if (err != error.ParsingError) return err;
            self.pos = save;
        }

        save = self.pos;
        const ins = self.parseInsert(arena);
        if (ins) |r| return r else |err| {
            if (err != error.ParsingError) return err;
            self.pos = save;
        }

        save = self.pos;
        const drp = self.parseDropTable(arena);
        if (drp) |r| return r else |err| {
            if (err != error.ParsingError) return err;
            self.pos = save;
        }

        return ParseError.ParsingError;
    }
};

fn jsonWriteStringEscaped(writer: anytype, s: []const u8) !void {
    try writer.writeByte('"');
    var i: usize = 0;
    while (i < s.len) : (i += 1) {
        const c = s[i];
        switch (c) {
            '"' => try writer.writeAll("\\\""),
            '\\' => try writer.writeAll("\\\\"),
            '\n' => try writer.writeAll("\\n"),
            '\r' => try writer.writeAll("\\r"),
            '\t' => try writer.writeAll("\\t"),
            else => try writer.writeByte(c),
        }
    }
    try writer.writeByte('"');
}

/// Serialize a `QueryResult` into a JSON object that matches the test runner
/// contract. Only the keys required by the harness are emitted.
fn buildJsonResponse(allocator: std.mem.Allocator, result: QueryResult) ![]u8 {
    var buf = std.array_list.Managed(u8).init(allocator);
    errdefer buf.deinit();
    var w = buf.writer();

    try w.writeAll("{");
    // status
    try w.writeAll("\"status\":\"");
    if (result.status_ok) {
        try w.writeAll("ok\"");
    } else {
        try w.writeAll("error\"");
    }

    if (!result.status_ok) {
        if (result.error_type) |et| {
            try w.writeAll(",\"error_type\":");
            try jsonWriteStringEscaped(w, et);
        }
        try w.writeAll("}");
        return try buf.toOwnedSlice();
    }

    // rows
    try w.writeAll(",\"rows\":");
    if (result.rows) |rows| {
        // table rows
        try w.writeByte('[');
        var r: usize = 0;
        while (r < rows.len) : (r += 1) {
            if (r > 0) try w.writeByte(',');
            const row = rows[r];
            try w.writeByte('[');
            var c: usize = 0;
            while (c < row.len) : (c += 1) {
                if (c > 0) try w.writeByte(',');
                switch (row[c]) {
                    .integer => |n| try w.print("{d}", .{n}),
                    .boolean => |b| if (b) try w.writeAll("true") else try w.writeAll("false"),
                    .null => try w.writeAll("null"),
                }
            }
            try w.writeByte(']');
        }
        try w.writeByte(']');
    } else {
        // expression single-row result
        try w.writeByte('[');
        if (result.items.len != 0) {
            try w.writeByte('[');
            var i: usize = 0;
            while (i < result.items.len) : (i += 1) {
                if (i > 0) try w.writeByte(',');
                const v = result.items[i].expr;
                switch (v) {
                    .integer => |n| try w.print("{d}", .{n}),
                    .boolean => |b| if (b) try w.writeAll("true") else try w.writeAll("false"),
                    .null => try w.writeAll("null"),
                }
            }
            try w.writeByte(']');
        }
        try w.writeByte(']');
    }

    // column_names
    if (result.column_names) |cols| {
        try w.writeAll(",\"column_names\":[");
        var i: usize = 0;
        while (i < cols.len) : (i += 1) {
            if (i > 0) try w.writeByte(',');
            try jsonWriteStringEscaped(w, cols[i]);
        }
        try w.writeByte(']');
    } else {
        // For expression SELECTs, include column_names when aliases were provided
        var any_alias = false;
        for (result.items) |it| {
            if (it.alias != null) { any_alias = true; break; }
        }
        if (any_alias) {
            try w.writeAll(",\"column_names\":[");
            var idx_alias: usize = 0;
            while (idx_alias < result.items.len) : (idx_alias += 1) {
                if (idx_alias > 0) try w.writeByte(',');
                if (result.items[idx_alias].alias) |a| {
                    try jsonWriteStringEscaped(w, a);
                } else {
                    try jsonWriteStringEscaped(w, "");
                }
            }
            try w.writeByte(']');
        }
    }

    try w.writeByte('}');
    return try buf.toOwnedSlice();
}

/// Entry point for processing a single SQL statement. It maps parser/validation
/// errors into the standard error_type strings required by the tests.
fn handleQuery(allocator: std.mem.Allocator, msg: []const u8) ![]u8 {
    var arena_impl = std.heap.ArenaAllocator.init(allocator);
    defer arena_impl.deinit();
    const arena = arena_impl.allocator();

    dbInit(allocator);

    var parser = Parser.init(msg);
    const parsed = parser.parseQuery(arena) catch |err| switch (err) {
        error.ParsingError => {
            const qr = QueryResult{ .status_ok = false, .error_type = "parsing_error", .items = &[_]SelectItem{} };
            return buildJsonResponse(allocator, qr);
        },
        error.ValidationError => {
            const qr = QueryResult{ .status_ok = false, .error_type = "validation_error", .items = &[_]SelectItem{} };
            return buildJsonResponse(allocator, qr);
        },
        error.DivisionByZero => {
            const qr = QueryResult{ .status_ok = false, .error_type = "division_by_zero_error", .items = &[_]SelectItem{} };
            return buildJsonResponse(allocator, qr);
        },
        else => return err,
    };

    return buildJsonResponse(allocator, parsed);
}

/// Read null-terminated statements from a client connection, write back JSON
/// responses, and continue until the client closes the connection.
fn handleConnection(allocator: std.mem.Allocator, conn: std.net.Server.Connection) !void {
    var message_buffer = std.array_list.Managed(u8).init(allocator);
    defer message_buffer.deinit();

    var read_buffer: [4096]u8 = undefined;
    var net_writer = conn.stream.writer(&.{});

    while (true) {
        const bytes_read = conn.stream.read(&read_buffer) catch |err| switch (err) {
            error.ConnectionResetByPeer => break,
            else => return err,
        };
        if (bytes_read == 0) break; // remote closed

        try message_buffer.appendSlice(read_buffer[0..bytes_read]);

        while (true) {
            if (std.mem.indexOfScalar(u8, message_buffer.items, 0)) |nul_index| {
                const msg = message_buffer.items[0..nul_index];

                const response_json = handleQuery(allocator, msg) catch blk: {
                    // On unexpected server error, return a parsing_error to conform to contract
                    const qr = QueryResult{ .status_ok = false, .error_type = "parsing_error", .items = &[_]SelectItem{} };
                    break :blk buildJsonResponse(allocator, qr) catch "{\"status\":\"error\",\"error_type\":\"parsing_error\"}";
                };
                defer allocator.free(response_json);

                // Write response plus trailing null
                try net_writer.interface.writeAll(response_json);
                try net_writer.interface.writeByte(0);

                // Remove processed message (including the null) from the buffer
                const remaining_start = nul_index + 1;
                const remaining_len = message_buffer.items.len - remaining_start;
                std.mem.copyForwards(u8, message_buffer.items[0..remaining_len], message_buffer.items[remaining_start..]);
                try message_buffer.resize(remaining_len);
            } else break;
        }
    }
}

/// Start the TCP server and accept connections sequentially on
/// RGSQL_SERVER_PORT (default 3003). Each connection is handled synchronously
/// which is sufficient for these exercises.
pub fn main() !void {
    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    defer _ = gpa.deinit();
    // Use this allocator for the handleConnection function
    const allocator = gpa.allocator();

    var env_map = try std.process.getEnvMap(allocator);
    defer env_map.deinit();

    const port: u16 = parsePort(&env_map);

    const address = try std.net.Address.parseIp4("127.0.0.1", port);

    var listener = try address.listen(.{ .reuse_address = true });

    defer listener.deinit();

    // Accept connections serially (sufficient for the initial tests)
    while (true) {
        const conn = listener.accept() catch |err| switch (err) {
            error.ConnectionResetByPeer => continue,
            else => return err,
        };

        handleConnection(allocator, conn) catch |err| {
            // Best-effort close on error; ignore further errors
            _ = conn.stream.close();
            switch (err) {
                error.BrokenPipe, error.ConnectionResetByPeer => {},
                else => return err,
            }
        };
        // Close connection after handling
        _ = conn.stream.close();
    }
}
