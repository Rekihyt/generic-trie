const std = @import("std");
const Allocator = std.mem.Allocator;
const mem = std.mem;
const math = std.math;
const assert = std.debug.assert;
const Order = math.Order;
const Wyhash = std.hash.Wyhash;
const array_hash_map = std.array_hash_map;
const AutoContext = std.array_hash_map.AutoContext;
const StringContext = std.array_hash_map.StringContext;
const ArrayListUnmanaged = std.ArrayListUnmanaged;
const DoublyLinkedList = std.DoublyLinkedList;
const meta = std.meta;
const ArenaAllocator = std.heap.ArenaAllocator;
const hash_map = std.hash_map;
const testing = std.testing;

pub fn StringTrie(comptime Value: type) type {
    return OptionTrie(u8, Value);
}

pub fn ByteTrie(comptime Value: type) type {
    return OptionTrie(u8, Value);
}

/// A trie where keys are arrays of strings.
pub fn TokenTrie(comptime Value: type) type {
    return OptionTrie([]const u8, Value);
}

/// A generic trie with default value null.
pub fn OptionTrie(comptime Key: type, comptime Value: type) type {
    return AutoTrie(Key, ?Value, null);
}

pub fn AutoTrie(
    comptime Key: type,
    comptime Value: type,
    comptime default: Value,
) type {
    return Trie(
        Key,
        Value,
        default,
        if (Key == []const u8)
            hash_map.StringContext
        else
            hash_map.AutoContext(Key),
        hash_map.default_max_load_percentage,
    );
}

/// A trie that maps slices of Key to a Value using std's hashmaps. Intermediate
/// and empty nodes that don't have a Value will be set to `default`. For
/// example, mapping strings to ints: `Trie(u8, ?i64, null)`.
/// The Value type isn't nullable by default because there are usecases / types
/// where there is already an identity element (such as "" for strings).
/// Keys and values are copied by value, for types that require freeing use an
/// arena or call `iterator` for a way to free all values.
pub fn Trie(
    comptime Term: type, // a single component of a key (i.e. u8 for strings)
    comptime Value: type,
    comptime default: Value,
    comptime Context: type,
    comptime max_load_percentage: u64,
) type {
    return struct {
        pub const Self = @This();
        pub const Key = []const Term;
        pub const HashMap = std.HashMapUnmanaged(
            Term,
            Self,
            Context,
            max_load_percentage,
        );

        pub const GetOrPutResult = HashMap.GetOrPutResult;
        pub const Entry = HashMap.Entry;

        map: HashMap = .{},
        value: Value = default,

        /// The intermediate results of matching a trie, which may or may not be
        /// a full match.
        pub const Prefix = struct {
            len: usize,
            leaf: Self,
        };

        /// Deep copy a trie, but copy keys and values by value.
        /// Use deinit to free.
        // TODO: optimize by allocating top level maps of same size and then
        // use putAssumeCapacity
        pub fn copy(self: Self, allocator: Allocator) Allocator.Error!Self {
            var result = Self{};
            var map_iter = self.map.iterator();
            while (map_iter.next()) |entry|
                try result.map.putNoClobber(
                    allocator,
                    entry.key_ptr.*,
                    try entry.value_ptr.*.copy(allocator),
                );
        }

        /// Deep copy a trie pointer, returning a pointer to new memory. Use
        /// destroy to free. Same as copy besides the root allocation.
        pub fn clone(self: *Self, allocator: Allocator) !*Self {
            const clone_ptr = try allocator.create(Self);
            clone_ptr.* = try self.copy(allocator);
            return clone_ptr;
        }

        /// Frees all memory recursively, leaving the Trie in an undefined
        /// state. The `self` pointer must have been allocated with `allocator`.
        /// The opposite of `clone`.
        pub fn destroy(self: *Self, allocator: Allocator) void {
            self.deinit(allocator);
            allocator.destroy(self);
        }

        /// The opposite of `copy`.
        pub fn deinit(self: *Self, allocator: Allocator) void {
            defer self.map.deinit(allocator);
            var iter = self.map.iterator();
            while (iter.next()) |entry| {
                entry.value_ptr.*.deinit(allocator);
            }
        }

        /// Tries are equal if they have the same keys and values. Values are
        // compared without following pointers using meta.eql if no eql function
        // is provided.
        pub fn eql(self: Self, other: Self) bool {
            if (self.map.count() != other.map.count())
                return false;

            var map_iter = self.map.iterator();
            var other_map_iter = other.map.iterator();
            while (map_iter.next()) |entry| {
                const other_entry = other_map_iter.next() orelse
                    return false;
                if (!(Context.eql(
                    undefined,
                    entry.key_ptr.*,
                    other_entry.key_ptr.*,
                )) or
                    entry.value_ptr.*.eql(other_entry.value_ptr.*))
                    return false;
            }
            return true;
        }

        pub fn create(allocator: Allocator) !*Self {
            const result = try allocator.create(Self);
            result.* = Self{};
            return result;
        }

        /// Return a pointer to the last trie in `trie` after the longest path
        /// following `keys`
        pub fn getPrefix(
            trie: Self,
            key: Key,
        ) Prefix {
            var current = trie;
            // Follow the longest branch that exists
            const prefix_len = for (key, 0..) |term, i| {
                current = current.map.get(term) orelse
                    break i;
            } else key.len;

            return .{ .len = prefix_len, .leaf = current };
        }

        pub fn get(
            trie: Self,
            keys: Key,
        ) Value {
            const prefix = trie.getPrefix(keys);
            return if (prefix.len == keys.len)
                prefix.leaf.value
            else
                null;
        }

        pub fn put(
            trie: *Self,
            allocator: Allocator,
            key: Key,
            value: Value,
        ) !*Self {
            const leaf_ptr = try trie.getOrPut(allocator, key);
            leaf_ptr.value = value;
            return leaf_ptr;
        }

        /// Creates the necessary branches and key entries in the trie for
        /// keys, and returns a pointer to the branch at the end of the path.
        /// Returns a pointer to the updated trie node. If the given keys is
        /// empty (0 len), the returned pointer is `trie`.
        fn getOrPut(
            trie: *Self,
            allocator: Allocator,
            key: Key,
        ) !*Self {
            var current = trie;
            for (key) |term| {
                const entry = try current.map
                    .getOrPutValue(allocator, term, Self{});
                current = entry.value_ptr;
            }
            return current;
        }

        pub fn count(self: Self) usize {
            var iter = self.map.valueIterator();
            var total = 0;
            while (iter.next()) |next|
                total += next.count();
            return total;
        }
    };
}

const TokenStrTrie = TokenTrie([]const u8);
const StrTrie = ByteTrie([]const u8);
const NumTrie = ByteTrie(usize);

test "Trie: eql" {
    var arena = ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();

    var expected = TokenStrTrie{};
    var child1 = TokenStrTrie{};
    var child2 = TokenStrTrie{};

    try expected.map.put(allocator, "Aa", child1);
    child1.value = "Val1";
    try child1.map.put(allocator, "Bb", child2);
    child2.value = "Val2";

    var actual = TokenStrTrie{};
    _ = try actual.put(allocator, &.{"Aa"}, "Val1");
    _ = try actual.put(allocator, &.{ "Aa", "Bb" }, "Val2");
    try testing.expect(actual.eql(expected));
}

test "put single lit" {}

test "put multiple keys" {
    var trie = NumTrie{};
    defer trie.deinit(testing.allocator);

    _ = try trie.put(
        testing.allocator,
        &.{ 1, 2, 3 },
        456,
    );
    try testing.expectEqual(
        trie.map.get(1).?
            .map.get(2).?
            .map.get(3).?
            .value,
        456,
    );
}

test "Compile: simple" {
    _ = TokenStrTrie{};
    _ = StrTrie{};
    _ = NumTrie{};
}

test "Memory: idempotency" {
    var token_trie = TokenStrTrie{};
    defer token_trie.deinit(testing.allocator);
    var str_trie = StrTrie{};
    defer str_trie.deinit(testing.allocator);
    var num_trie = NumTrie{};
    defer num_trie.deinit(testing.allocator);
}

test "Memory: multiple keys with value" {
    var trie = TokenStrTrie{};
    defer trie.deinit(testing.allocator);

    const keys = &.{ "cherry", "blossom", "tree" };
    const child_ptr = try trie
        .put(testing.allocator, keys, "beautiful");
    try testing.expect(null != trie.get(keys));
    try testing.expectEqualSlices(u8, child_ptr.value.?, trie.get(keys).?);
}

test "Memory: multiple keys" {
    var trie = try TokenStrTrie.create(testing.allocator);
    defer trie.destroy(testing.allocator);

    const keys = &.{ "cherry", "blossom", "tree" };
    const child_ptr = try trie.put(testing.allocator, keys, null);
    try testing.expectEqual(null, child_ptr.value);
    try testing.expectEqual(null, trie.get(keys));
}

test "Behavior: duplicates" {
    var trie = StrTrie{};
    defer trie.deinit(testing.allocator);
    _ = try trie.put(testing.allocator, "xyz", "1");
    _ = try trie.put(testing.allocator, "xyz", "2");

    try testing.expect(null != trie.get("xyz"));
    try testing.expectEqualSlices(u8, trie.get("xyz").?, "2");
}
