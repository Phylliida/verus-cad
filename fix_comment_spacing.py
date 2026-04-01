#!/usr/bin/env python3
import os

for root, dirs, files in os.walk("."):
    dirs[:] = [d for d in dirs if d not in (".git", "target", "node_modules")]
    for f in files:
        path = os.path.join(root, f)
        try:
            data = open(path, "rb").read()
            new = data.replace(b"//  ", b"//   ")
            if new != data:
                open(path, "wb").write(new)
                print(path)
        except Exception:
            pass
