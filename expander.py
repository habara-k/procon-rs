# コマンドライン引数を解析.
import argparse

parser = argparse.ArgumentParser(description="Expand the local crates")
parser.add_argument("--deps", nargs="+", help="Path to the local crates")
parser.add_argument("--root", default=".", help="Root directory of the workspace")
parser.add_argument(
    "--tgt", default="src/bin/a.rs", help="Solution file to be submitted"
)

args = parser.parse_args()

if args.deps is not None and args.root != ".":
    raise Exception("Only one of `deps` or `root` needs to be given.")


# 1. 展開するローカルクレートのパスを取得する.
def using_deps():
    if args.deps is not None:
        return args.deps
    else:
        # Cargo.toml を解析してローカルのクレートを列挙.
        import toml
        from pathlib import Path

        dep_path = {}

        with open(Path(args.root) / "Cargo.toml") as file:
            obj = toml.load(file)
            if "dependencies" in obj:
                for k, v in obj["dependencies"].items():
                    if "path" not in v:
                        continue
                    dep_path[k.replace("-", "_")] = v["path"]

        # tgt ファイル内で use <local_crate_name>::*; を使用している箇所を探索し,
        # 依存しているローカルクレートを列挙.
        import re

        using_deps = set()

        with open(args.tgt) as file:
            for line in file:
                m = re.match("^use (.*)::\*;$", line)
                if m is None:
                    continue
                dep = m.groups()[0]
                if dep in dep_path:
                    using_deps.add(dep_path[dep])

        return list(map(lambda path: Path(args.root) / path, using_deps))


deps = using_deps()


# 2. stdout に出力する.

## 2.1. tgt を出力.
with open(args.tgt) as file:
    for line in file:
        line = line.rstrip()
        print(line)

## 2.2. 依存しているローカルクレートを出力.
import subprocess

for dep in deps:
    res = subprocess.run(
        [
            "procon-bundler",
            "bundle",
            dep,
        ],
        stdout=subprocess.PIPE,
    )

    for line in res.stdout.splitlines():
        print(line.decode("UTF-8"))
