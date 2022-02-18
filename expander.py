import argparse

parser = argparse.ArgumentParser(description='Expand the local crates')

parser.add_argument('--crates', nargs='+', help='Path to the local crates')
parser.add_argument('--tgt', default='src/bin/a.rs', help='Solution file to be submitted')

args = parser.parse_args()


lines = []

with open(args.tgt) as file:
    for line in file:
        lines.append(line.rstrip())

import subprocess

for path in args.crates:
    res = subprocess.run([
        'procon-bundler', 'bundle', path,
        ], stdout=subprocess.PIPE)

    for line in res.stdout.splitlines():
        lines.append(line.decode('UTF-8'))


for line in lines:
    print(line)
