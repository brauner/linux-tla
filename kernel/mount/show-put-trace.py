#!/usr/bin/env python3
"""Print a TLC counterexample of the MntPut model compactly, one line per
state: the action, every task's label, the visible seq/counters/lock,
the store buffers, the mount's flags, RCU and the ledger.
    ./show-put-trace.py logs/<cfg>.log
"""
import re
import sys

log = open(sys.argv[1]).read()
marks = ['Error: The behavior up to this point is:', 'Error: The following behavior constitutes a counter-example:']
mark = next((mk for mk in marks if mk in log), None)
if mark is None:
    print(log[log.find('Error'):][:1500] if 'Error' in log else 'no error in log')
    sys.exit(0)
print(log[log.index('Error:'):log.index(mark)].strip())
trace = log[log.index(mark):]
states = re.split(r'\nState (\d+): ', trace)


def var(body, name):
    m = re.search(r'/\\ ' + name + r' = (.*?)(?=\n/\\ |\Z)', body, re.S)
    return re.sub(r'\s+', ' ', m.group(1)).strip() if m else '?'


def short(rec):
    return re.sub(r'\[f \|-> "(\w+)"(?:, c \|-> (\d+))?, (?:d|v) \|-> ([^\]]+)\]',
                  lambda mm: f'{mm.group(1)}{"[" + mm.group(2) + "]" if mm.group(2) else ""}={mm.group(3)}', rec)


for i in range(1, len(states), 2):
    num, body = states[i], states[i + 1]
    head = body.split('\n', 1)[0].strip()
    act = re.sub(r' line \d+, col \d+ to line \d+, col \d+ of module \w+', '', head)
    mrec = var(body, 'm')
    flags = ''.join(k[0].upper() for k in ('hashed', 'ns', 'umount', 'sync', 'doomed', 'freed')
                    if re.search(k + r' \|-> TRUE', mrec))
    print(f"{num:>3} {act:<22} pc={var(body, 'pc')} seq={var(body, 'seqv')} cnt={var(body, 'cntv')} "
          f"lock={var(body, 'lockv')} m=[{flags}] rcu={var(body, 'rcu')} refs={var(body, 'refs')} "
          f"nsref={var(body, 'nsref')} acc={var(body, 'acc')} ci={var(body, 'ci')} gp={var(body, 'gp')} "
          f"gpfree={var(body, 'gpfree')} res={var(body, 'uresult')} cleaner={var(body, 'cleaner')}")
    b = short(var(body, 'buf'))
    if b and b != '?' and '<<>>' != b.replace(' ', '').strip('[]').split('|->')[-1]:
        print(f"      buf={b}")
tail = trace[trace.rfind('State '):]
m = re.search(r'Back to state (\d+)', trace)
if m:
    print(f"... back to state {m.group(1)} (stuttering/lasso)")
