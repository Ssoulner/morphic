from argparse import ArgumentParser
import subprocess
import os
import json
from collections import defaultdict
import math

script_dir = os.path.dirname(os.path.realpath(__file__))
os.chdir(script_dir)

parser = ArgumentParser()
parser.add_argument("--include-type-mono", action="store_true", help="Include results for configurations with type monomorphization but without LSS")
parser.add_argument("--measure", choices=["time", "size"], default="time", help="Select whether to report run time or binary size")
args = parser.parse_args()

benchmarks = defaultdict(lambda: defaultdict(lambda: defaultdict(lambda: math.nan)))

# langs = ["morphic", "ocaml", "sml"]
langs = ["mor"]
human_langs = {
    "mor": "Morphic",
    "ocaml": "OCaml",
    "sml": "MLton",
}

# modes = ["baseline", "typemono", "lss"]
# human_modes = {
#     "baseline": "Baseline",
#     "typemono": "Type-Mono",
#     "lss": "LSS",
# }
modes = ["single", "specialize"]
human_modes = {
    "single": "Baseline",
    "specialize": "LSS",
}

if args.measure == "time":
    results_dir = os.path.join(script_dir, 'benchmark_out', 'results')
    filenames = os.listdir(results_dir)
    for filename in filenames:
        for lang in langs:
            for mode in modes:
                suffix = f".{lang}_{mode}.txt"
                if filename.endswith(suffix):
                    with open(os.path.join(results_dir, filename)) as f:
                        data = json.load(f)
                        mean = sum(data) / len(data)
                        benchmarks[filename[:-len(suffix)]][lang][mode] = mean
else:
    bin_dir = os.path.join(script_dir, 'benchmark_out', 'bin')
    filenames = os.listdir(bin_dir)
    for filename in filenames:
        for lang in langs:
            for mode in modes:
                suffix = f"_{lang}_{mode}"
                if filename.endswith(suffix):
                    size = os.path.getsize(os.path.join(bin_dir, filename))
                    benchmarks[filename[:-len(suffix)]][lang][mode] = size


if args.measure == "size" and args.include_type_mono:
    col_size = 18
else:
    col_size = 15

if args.include_type_mono:
    col_modes = modes
else:
    col_modes = ["single", "specialize"]

col_names = ["Compiler"]

if args.measure == "time":
    unit = 1e6
    get_ratio = lambda x, y: x / y
    for mode in col_modes:
        col_names.append(f"{human_modes[mode]} (ms)")
        if mode != "baseline":
            col_names.append(f"{human_modes[mode]} Speedup")
else:
    unit = 1 << 10
    get_ratio = lambda x, y: y / x
    for mode in col_modes:
        col_names.append(f"{human_modes[mode]} (kiB)")
        if mode != "baseline":
            col_names.append(f"{human_modes[mode]} Ratio")

def show(n):
    if math.isnan(n):
        return "-"
    else:
        return f"{n:.2f}"

print(benchmarks)
for name in sorted(benchmarks.keys()):
    print(f"---- {name} ".ljust(col_size * len(col_names), "-"))
    print()
    print("".join(name.rjust(col_size) for name in col_names))
    print()
    for lang in langs:
        print(human_langs[lang].rjust(col_size), end="")
        for mode in col_modes:
            value = benchmarks[name][lang][mode]
            print(show(value / unit).rjust(col_size), end="")
            if mode != "baseline":
                baseline = benchmarks[name][lang]["baseline"]
                print(show(get_ratio(baseline, value)).rjust(col_size), end="")
        print()
    print()


