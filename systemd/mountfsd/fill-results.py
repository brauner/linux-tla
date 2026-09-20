#!/usr/bin/env python3
"""Print the results table for README.md from logs/summary.txt, or replace
the RESULTS_TABLE marker in README.md with it."""
import importlib.util, pathlib, sys
here = pathlib.Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("gen_cfgs", here / "gen-cfgs.py")
# gen-cfgs.py writes the configurations on import; that is idempotent
gen = importlib.util.module_from_spec(spec)
sys.stdout = open("/dev/null", "w"); spec.loader.exec_module(gen); sys.stdout = sys.__stdout__
desc = {name: entry[-1] for name, entry in gen.CONFIGS.items()}
rows = {}
for line in (here / "logs" / "summary.txt").read_text().splitlines()[1:]:
    parts = line.split()
    if len(parts) < 6 or parts[0] == "ALL-DONE":
        continue
    rows[parts[0]] = parts
out = ["| Configuration | What it checks | Expected | Result | Distinct states | TLC time |",
       "|---|---|---|---|---|---|"]
for cfg in gen.CONFIGS:
    if cfg not in rows:
        continue
    _, expect, result, states, took, _ = rows[cfg]
    out.append(f"| `{cfg}` | {desc[cfg]} | {expect} | {result} | {states} | {took} |")
table = "\n".join(out)
if len(sys.argv) > 1 and sys.argv[1] == "--readme":
    readme = here / "README.md"
    s = readme.read_text()
    if "RESULTS_TABLE" in s:
        s = s.replace("RESULTS_TABLE", table)
    else:
        # replace the table that is there
        start = s.index("| Configuration | What it checks |")
        end = start
        while end < len(s) and s[end] == "|":
            end = s.find("\n", end) + 1
        s = s[:start] + table + "\n" + s[end:]
    readme.write_text(s)
print(table)
