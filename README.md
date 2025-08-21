# rgSQL

> Made with ❤️ 

<img alt="rgSQL logo" align=right width=159 height=187 src="https://technicaldeft.com/rgsql_logo_small.png"/> rgSQL is a SQL database server that **YOU** get to build from scratch.

[More about rgSQL and why it was created](https://technicaldeft.com/posts/rgsql-a-test-suite-for-database-engines).

This project contains a test runner and 200+ test cases to guide you through creating a database server. The tests check your implementation can parse, type check and evaluate SQL statements. 

The test suite starts with simpler statements such as `SELECT 1;` and builds up to more complex queries that can evaluate expressions, join tables and run aggregate functions on grouped data.



### Using
### Zig version - v0.15.0-dev.1593+399bace2f

To start, fork this repository. Then clone it and run:
```bash
./run-tests
```
If you want more guidance and suggestions for building your implementation, see the **[Build a Database Server](https://technicaldeft.com/build-a-database-server)** book.

### Tests cases
The `tests/` directory contains 13 files that check different parts of your implementation. Here's an example test that checks that you can insert multiple rows at once: 
```sql
--- can insert multiple rows
CREATE TABLE t1(a INTEGER, b INTEGER);
INSERT INTO t1 VALUES (1, 2), (3, 4);
SELECT a, b FROM t1;
--- returns:
1, 2
3, 4
```
### Companion book

<a href="https://technicaldeft.com/build-a-database-server"><img alt="Cover of the Build a Database Server book" align=right width=232 height=306 src="https://technicaldeft.com/build_a_database_server_cover.png"/></a>

Get the **[Build a Database Server](https://technicaldeft.com/build-a-database-server)** book to get:

+ A 13 chapter guide on how to build your rgSQL implementation.
+ In depth explanations of how to write a parser, build a type checker, and create a query plan with iterators.
+ Details about important SQL and relational database concepts such as atomicity and 3-valued logic.
+ Comparisons between rgSQL and databases such as PostgreSQL, MySQL, SQLite and DuckDB.
+ 30+ extension projects that add to your implementation.
+ Ideas on how to structure and refactor your code, including a sample solution.
+ Access to a Discord server to share solutions and ask for help.
+ Instructions on how to work with and extend the rgSQL test suite.
