from collections import namedtuple, defaultdict
import json
import sys

def read_report_data(f):
    buf = f.read()
    start = buf.index(b'(')
    end = buf.rindex(b')')
    return json.loads(buf[start + 1 : end])

assert len(sys.argv) > 1, 'expected at least one input file'
js = [read_report_data(open(fn, 'rb')) for fn in sys.argv[1:]]

# Collect all events
evts = []
for j in js:
    for x in j:
        if x['type'] != 'callgraph':
            continue
        evts.extend(x['events'])

# Build tables of branches and visited blocks
branches = set()
visited = set()
for evt in evts:
    if evt['type'] == 'BRANCH':
        branches.add((evt['function'], evt['callsite'], tuple(evt['blocks'])))
    elif evt['type'] == 'BLOCK':
        func = evt['function']
        for b in evt['blocks']:
            visited.add((func, b))

BranchInfo = namedtuple('BranchInfo', ('function', 'callsite', 'blocks', 'taken'))

branch_info = []
for (function, callsite, blocks) in branches:
    taken = [(function, b) in visited for b in blocks]
    branch_info.append(BranchInfo(function, callsite, blocks, taken))

# Merge branches by callsite.  We want to treat instances of the same source
# branch in different monomorphizations as a single branch for coverage
# purposes.
by_callsite = defaultdict(list)
for bi in branch_info:
    by_callsite[bi.callsite].append(bi)

for callsite in sorted(by_callsite.keys()):
    bis = by_callsite[callsite]
    if len(set(bi.function for bi in bis)) != len(bis):
        # Multiple distinct branches within a single function.  We can't
        # distinguish them, so the results may overestimate coverage.
        print('warning: found multiple branches at %s' % callsite)
    taken = [False] * max(len(bi.taken) for bi in bis)
    for bi in bis:
        for i, t in enumerate(bi.taken):
            if t:
                taken[i] = True
    missing = [i for i,t in enumerate(taken) if not t]
    if len(missing) == 0:
        continue
    print('exit %s not taken at %s' % (missing, callsite))
