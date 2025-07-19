const std = @import("std");

const Token = struct {
    type: Type,
    meta: ?[]const u8 = null,

    fn init(s: []const u8) Token {
        return if (std.mem.startsWith(u8, s, "__"))
            .{ .type = .__a, .meta = s[2..] }
        else if (std.mem.eql(u8, s, "::"))
            .{ .type = .@"::" }
        else if (std.mem.eql(u8, s, ".."))
            .{ .type = .@".." }
        else if (s[s.len - 1] == '=')
            .{ .type = .@"a=", .meta = s[0 .. s.len - 1] }
        else if (s[0] == '=')
            .{ .type = .@"=a", .meta = s[1..] }
        else if (s.len >= 2 and s[0] == '`' and s[s.len - 1] == '`')
            .{ .type = .assembly, .meta = s[1 .. s.len - 1] }
        else
            .{ .type = .atom, .meta = s };
    }

    const Type = enum {
        __a,
        @"::",
        @"..",
        @"a=",
        @"=a",
        assembly,
        atom,
    };
};

const RawTokenizer = struct {
    buf: []const u8,

    fn init(s: []const u8) RawTokenizer {
        return .{ .buf = s };
    }

    fn next(self: *RawTokenizer) ?[]const u8 {
        return while (self.buf.len > 0) {
            var i: usize = 0;
            defer self.buf = self.buf[@min(i + 1, self.buf.len)..];
            if (self.buf[0] == '`') {
                if (std.mem.indexOfScalarPos(u8, self.buf, 1, '`')) |r| {
                    i = r;
                    break self.buf[0 .. r + 1];
                }
            }
            while (i < self.buf.len) : (i += 1) {
                if (std.ascii.isWhitespace(self.buf[i]))
                    break;
            }
            if (i != 0) break self.buf[0..i];
        } else null;
    }
};

/// Lifetime of `s` must be not less than lifetime of function result.
pub fn tokenizeFromSlice(alloc: std.mem.Allocator, s: []const u8) ![]Token {
    var list = std.ArrayList(Token).init(alloc);
    var iter = RawTokenizer.init(s);
    while (iter.next()) |raw| {
        try list.append(Token.init(raw));
    }
    return list.toOwnedSlice();
}

test "tokenizer" {
    const prog =
        \\__foo a b ::
        \\a=    a
        \\      b
        \\`add a0, =a, a0`
        \\  =a
        \\..
    ;
    const alloc = std.testing.allocator;
    const tokens = try tokenizeFromSlice(alloc, prog);
    defer alloc.free(tokens);

    try std.testing.expectEqualDeep(&[_]Token{
        .{ .type = .__a, .meta = "foo" },
        .{ .type = .atom, .meta = "a" },
        .{ .type = .atom, .meta = "b" },
        .{ .type = .@"::" },
        .{ .type = .@"a=", .meta = "a" },
        .{ .type = .atom, .meta = "a" },
        .{ .type = .atom, .meta = "b" },
        .{ .type = .assembly, .meta = "add a0, =a, a0" },
        .{ .type = .@"=a", .meta = "a" },
        .{ .type = .@".." },
    }, tokens);
}

const NodeRoot = struct {
    suncs: []*const NodeSuncDecl,
};

const NodeSuncDecl = struct {
    name: []const u8,
    args: []*const NodeArgDecl,
    body: []INodeStmt,
};

const NodeArgDecl = struct {
    name: []const u8,
};

const NodeArgPlace = struct {
    name: []const u8,
};

const NodeTagPlace = struct {
    name: []const u8,
};

const NodeSuncPlace = struct {
    name: []const u8,
    args: []INodeExpr,
};

const NodeTagDecl = struct {
    name: []const u8,
};

const NodeTaggedExpr = struct {
    tag: *const NodeTagDecl,
    expr: INodeExpr,
};

const INodeStmt = union(enum) {
    expr: INodeExpr,
    tagged_expr: NodeTaggedExpr,
    assembly: *const NodeAssembly,
};

const INodeExpr = union(enum) {
    arg_place: *const NodeArgPlace,
    tag_place: *const NodeTagPlace,
    sunc_place: *const NodeSuncPlace,
};

const NodeAssembly = struct {
    // TODO
};
