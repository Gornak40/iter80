const std = @import("std");

const iter = @import("iter");

pub fn main() !void {
    var gpa: std.heap.GeneralPurposeAllocator(.{}) = .{};
    const alloc = gpa.allocator();

    const args = try std.process.argsAlloc(alloc);
    defer std.process.argsFree(alloc, args);
    if (args.len != 2) {
        return error.UsageError; // TODO: more verbose
    }

    var file = try std.fs.cwd().openFile(args[1], .{});
    defer file.close();

    const prog = try file.readToEndAlloc(alloc, std.math.maxInt(u32));
    defer alloc.free(prog);

    const source = try iter.compile(alloc, prog);
    defer alloc.free(source);

    const ouf = std.io.getStdOut();
    try std.fmt.format(ouf.writer(), "{s}", .{source});
}
