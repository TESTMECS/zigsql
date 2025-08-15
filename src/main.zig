const std = @import("std");

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
};

const SelectItem = struct {
    expr: Value,
    alias: ?[]const u8 = null,
};

const QueryResult = struct {
    status_ok: bool,
    error_type: ?[]const u8 = null, // when not ok
    // rows: optional single result set for this basic subset
    // each row is a list of values; for now we only ever return 0 or 1 rows
    items: []SelectItem,
};

const Parser = struct {
    input: []const u8,
    pos: usize = 0,

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

    fn parseIdentifier(self: *Parser) ?[]const u8 {
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

    fn parsePrimary(self: *Parser) ParseError!Value {
        self.skipWhitespaceAndComments();
        if (self.eof()) return ParseError.ParsingError;

        // parenthesized
        if (self.matchChar('(')) {
            const v = try self.parseExpression();
            if (!self.matchChar(')')) return ParseError.ParsingError;
            return v;
        }

        // boolean
        if (self.parseBoolean()) |b| return Value{ .boolean = b };

        // integer (with optional unary minus handled in parseUnary)
        if (self.parseInteger()) |n| return Value{ .integer = n };

        return ParseError.ParsingError;
    }

    fn parseUnary(self: *Parser) ParseError!Value {
        self.skipWhitespaceAndComments();
        if (self.matchKeyword("not")) {
            const v = try self.parseUnary();
            return switch (v) {
                .boolean => |b| Value{ .boolean = !b },
                else => ParseError.ValidationError,
            };
        }
        if (self.matchChar('-')) {
            const v = try self.parseUnary();
            return switch (v) {
                .integer => |n| Value{ .integer = -n },
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
                        if (left != .integer or right != .integer) return ParseError.ValidationError;
                        left = Value{ .integer = left.integer * right.integer };
                    },
                    '/' => {
                        if (left != .integer or right != .integer) return ParseError.ValidationError;
                        if (right.integer == 0) return ParseError.DivisionByZero;
                        left = Value{ .integer = @divTrunc(left.integer, right.integer) };
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
                        if (left != .integer or right != .integer) return ParseError.ValidationError;
                        left = Value{ .integer = left.integer + right.integer };
                    },
                    '-' => {
                        if (left != .integer or right != .integer) return ParseError.ValidationError;
                        left = Value{ .integer = left.integer - right.integer };
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
                op = '<';
                or_equal = self.matchChar('=');
            } else if (self.matchChar('>')) {
                op = '>';
                or_equal = self.matchChar('=');
            } else break;

            const right = try self.parseAddSub();
            if (left == .integer and right == .integer) {
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
            const res = switch (left) {
                .integer => |li| switch (right) {
                    .integer => |ri| if (op == .eq) (li == ri) else (li != ri),
                    else => return ParseError.ValidationError,
                },
                .boolean => |lb| switch (right) {
                    .boolean => |rb| if (op == .eq) (lb == rb) else (lb != rb),
                    else => return ParseError.ValidationError,
                },
            };
            left = Value{ .boolean = res };
        }
        return left;
    }

    fn parseAnd(self: *Parser) ParseError!Value {
        var left = try self.parseEquality();
        while (true) {
            self.skipWhitespaceAndComments();
            if (!self.matchKeyword("and")) break;
            const right = try self.parseEquality();
            if (left != .boolean or right != .boolean) return ParseError.ValidationError;
            left = Value{ .boolean = left.boolean and right.boolean };
        }
        return left;
    }

    fn parseOr(self: *Parser) ParseError!Value {
        var left = try self.parseAnd();
        while (true) {
            self.skipWhitespaceAndComments();
            if (!self.matchKeyword("or")) break;
            const right = try self.parseAnd();
            if (left != .boolean or right != .boolean) return ParseError.ValidationError;
            left = Value{ .boolean = left.boolean or right.boolean };
        }
        return left;
    }

    fn parseExpression(self: *Parser) ParseError!Value {
        return self.parseOr();
    }

    fn parseSelectList(self: *Parser, arena: std.mem.Allocator) ParseError![]SelectItem {
        self.skipWhitespaceAndComments();
        var list = std.ArrayList(SelectItem).init(arena);
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
                if (self.parseIdentifier()) |ident| {
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

    fn parseSelect(self: *Parser, arena: std.mem.Allocator) ParseError!QueryResult {
        if (!self.matchKeyword("select")) return ParseError.ParsingError;
        const items = try self.parseSelectList(arena);
        self.skipWhitespaceAndComments();
        if (!self.matchChar(';')) return ParseError.ParsingError;

        // ensure nothing but whitespace/comments remain
        self.skipWhitespaceAndComments();
        if (!self.eof()) return ParseError.ParsingError;

        return .{ .status_ok = true, .error_type = null, .items = items };
    }

    fn parseQuery(self: *Parser, arena: std.mem.Allocator) ParseError!QueryResult {
        // For now, only SELECT statements are supported
        return self.parseSelect(arena);
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

fn buildJsonResponse(allocator: std.mem.Allocator, result: QueryResult) ![]u8 {
    var buf = std.ArrayList(u8).init(allocator);
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
    try w.writeAll(",\"rows\":[");
    if (result.items.len == 0) {
        // return no rows: []
    } else {
        // single row
        try w.writeByte('[');
        var i: usize = 0;
        while (i < result.items.len) : (i += 1) {
            if (i > 0) try w.writeByte(',');
            const v = result.items[i].expr;
            switch (v) {
                .integer => |n| try w.print("{d}", .{n}),
                .boolean => |b| if (b) try w.writeAll("true") else try w.writeAll("false"),
            }
        }
        try w.writeByte(']');
    }
    try w.writeByte(']');

    // column_names when aliases provided
    var any_alias = false;
    for (result.items) |it| {
        if (it.alias != null) { any_alias = true; break; }
    }
    if (any_alias) {
        try w.writeAll(",\"column_names\":[");
        var i: usize = 0;
        while (i < result.items.len) : (i += 1) {
            if (i > 0) try w.writeByte(',');
            if (result.items[i].alias) |a| {
                try jsonWriteStringEscaped(w, a);
            } else {
                // default empty alias name
                try jsonWriteStringEscaped(w, "");
            }
        }
        try w.writeByte(']');
    }

    try w.writeByte('}');
    return try buf.toOwnedSlice();
}

fn handleQuery(allocator: std.mem.Allocator, msg: []const u8) ![]u8 {
    var arena_impl = std.heap.ArenaAllocator.init(allocator);
    defer arena_impl.deinit();
    const arena = arena_impl.allocator();

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

fn handleConnection(allocator: std.mem.Allocator, conn: std.net.Server.Connection) !void {
    var message_buffer = std.ArrayList(u8).init(allocator);
    defer message_buffer.deinit();

    var read_buffer: [4096]u8 = undefined;
    const reader = conn.stream.reader();
    const writer = conn.stream.writer();

    while (true) {
        const bytes_read = reader.read(&read_buffer) catch |err| switch (err) {
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
                try writer.writeAll(response_json);
                try writer.writeByte(0);

                // Remove processed message (including the null) from the buffer
                const remaining_start = nul_index + 1;
                const remaining_len = message_buffer.items.len - remaining_start;
                std.mem.copyForwards(u8, message_buffer.items[0..remaining_len], message_buffer.items[remaining_start..]);
                try message_buffer.resize(remaining_len);
            } else break;
        }
    }
}

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
