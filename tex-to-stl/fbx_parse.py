#!/usr/bin/env python3
"""Minimal binary-FBX parser: extract mesh Vertices / PolygonVertexIndex."""
import struct
import zlib


def parse_fbx(path):
    data = open(path, "rb").read()
    assert data[:18] == b"Kaydara FBX Binary"
    version = struct.unpack("<I", data[23:27])[0]
    big = version >= 7500
    W = 8 if big else 4
    fmt = "<QQQ" if big else "<III"

    def read_node(off):
        end, nprops, plen = struct.unpack(fmt, data[off:off + 3 * W])
        off += 3 * W
        nlen = data[off]
        off += 1
        name = data[off:off + nlen].decode("ascii")
        off += nlen
        props = []
        for _ in range(nprops):
            t = chr(data[off]); off += 1
            if t in "YCIFDL":
                sz = {"Y": 2, "C": 1, "I": 4, "F": 4, "D": 8, "L": 8}[t]
                fm = {"Y": "<h", "C": "<b", "I": "<i", "F": "<f",
                      "D": "<d", "L": "<q"}[t]
                props.append(struct.unpack(fm, data[off:off + sz])[0])
                off += sz
            elif t in "fdlib":
                n, enc, clen = struct.unpack("<III", data[off:off + 12])
                off += 12
                raw = data[off:off + clen]
                off += clen
                if enc == 1:
                    raw = zlib.decompress(raw)
                fm = {"f": "f", "d": "d", "l": "q", "i": "i", "b": "b"}[t]
                props.append(list(struct.unpack(f"<{n}{fm}", raw)))
            elif t in "SR":
                n = struct.unpack("<I", data[off:off + 4])[0]
                off += 4
                props.append(data[off:off + n])
                off += n
            else:
                raise ValueError(f"unknown prop type {t!r}")
        children = []
        while off < end:
            if end - off <= 3 * W + 1 and all(
                    b == 0 for b in data[off:end]):
                off = end
                break
            child, off = read_node(off)
            if child is None:
                break
            children.append(child)
        return (name, props, children), end

    root = []
    off = 27
    while off < len(data):
        if all(b == 0 for b in data[off:off + 3 * W + 1]):
            break
        node, off = read_node(off)
        root.append(node)
    return version, root


def find_meshes(nodes):
    out = []

    def walk(n, path):
        name, props, children = n
        if name == "Vertices":
            out.append(("V", path, props[0]))
        if name == "PolygonVertexIndex":
            out.append(("P", path, props[0]))
        for c in children:
            walk(c, path + "/" + name)

    for n in nodes:
        walk(n, "")
    return out


if __name__ == "__main__":
    import sys
    version, root = parse_fbx(sys.argv[1] if len(sys.argv) > 1
                              else "associahedron.fbx")
    print("FBX version", version)
    for kind, path, arr in find_meshes(root):
        print(kind, path, "len", len(arr))
