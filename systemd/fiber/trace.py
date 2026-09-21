#!/usr/bin/env python3
"""Pretty-print a TLC counterexample of Fiber.tla read from stdin: one block per
state with the action that led to it, the loop state, the live fibers and the
live futures.  Used by extract-trace.sh."""
import re
import sys


def split_top(s):
    """Split on commas at bracket depth 0."""
    out, depth, cur, i = [], 0, [], 0
    while i < len(s):
        if s.startswith("<<", i):
            depth += 1; cur.append("<<"); i += 2; continue
        if s.startswith(">>", i):
            depth -= 1; cur.append(">>"); i += 2; continue
        c = s[i]
        if c in "[{(":
            depth += 1
        elif c in "]})":
            depth -= 1
        if c == "," and depth == 0:
            out.append("".join(cur).strip()); cur = []
        else:
            cur.append(c)
        i += 1
    if "".join(cur).strip():
        out.append("".join(cur).strip())
    return out


def parse(s):
    """TLC value -> python: records and functions as dicts, sets and sequences as lists."""
    s = s.strip()
    if s.startswith("[") and s.endswith("]"):
        d = {}
        for part in split_top(s[1:-1]):
            k, v = part.split("|->", 1)
            d[k.strip()] = parse(v)
        return d
    if s.startswith("(") and s.endswith(")") and ":>" in s:
        d = {}
        for part in re.split(r"\s@@\s", s[1:-1]):
            k, v = part.split(":>", 1)
            d[k.strip().strip('"')] = parse(v)
        return d
    if s.startswith("<<") and s.endswith(">>"):
        return [parse(p) for p in split_top(s[2:-2])]
    if s.startswith("{") and s.endswith("}"):
        return [parse(p) for p in split_top(s[1:-1])]
    if s.startswith('"') and s.endswith('"'):
        return s[1:-1]
    if s in ("TRUE", "FALSE"):
        return s == "TRUE"
    try:
        return int(s)
    except ValueError:
        return s


def main():
    text = sys.stdin.read()
    for b in re.split(r"\n(?=State \d+: |Back to state|Stuttering)", text):
        head, _, body = b.partition("\n")
        m = re.match(r"State (\d+): <(\w+)", head)
        if m:
            print(f"--- state {m.group(1)}: {m.group(2)}")
        elif head.startswith("Back to state") or head.startswith("Stuttering"):
            print("--- " + head.strip()); continue
        elif "Initial predicate" in head:
            print("--- state 1: Init")
        else:
            continue
        m = re.search(r"st = (\[.*\])\s*$", body, re.S)
        if not m:
            continue
        st = parse(m.group(1))
        print("    loop: phase=%s exiting=%s exitReq=%s finished=%s iter=%s crash=%r spurious=%s badYield=%s lostCancel=%s" % (
            st["phase"], st["exiting"], st["exitReq"], st["finished"], st["iter"], st["crash"],
            st["spurious"], st["badYield"], st["lostCancel"]))
        for g, f in sorted(st["fib"].items()):
            if f["state"] == "none":
                continue
            print("    %s: %-9s defer=%s/%s exit=%s float=%s by=%s prio=%s bud=%s stack=%s mode=%s->%s/%s rv=%s cont=%s:%s fut=%s tgt=%s w=%s wake=%s/%s pend=%s sw=%s" % (
                g, f["state"], f["deferOn"], f["deferIter"], f["exitOn"], f["floating"], f["creator"],
                f["prio"], f["budget"], f["cstack"], f["mode"], f["unwindTo"], f["after"], f["retval"],
                f["cont"], f["opkind"], f["opfut"], f["optarget"], f["cwuWait"], f["wakeVal"],
                f["wakeSrc"], f["pendingVal"], f["swallowedVal"]))
        for x, u in sorted(st["fut"].items()):
            if u["kind"] == "free":
                continue
            if u["kind"] in ("ext", "deadline"):
                extra = " src=%s fired=%s obs=%s prio=%s dropped=%s" % (u["srcOn"], u["fired"], u["obsIter"], u["prio"], u["dropped"])
            elif u["kind"] == "wait":
                extra = " tgt=%s" % u["target"]
            else:
                extra = ""
            print("    fut %s: %s %s res=%s cb=%s waiters=%s held=%s%s" % (
                x, u["kind"], u["state"], u["result"], u["cb"], u["waiters"], u["held"], extra))


main()
