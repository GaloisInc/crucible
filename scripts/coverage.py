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

# Build a table of branches, combining the parts of compound branches

Branch = namedtuple('Branch', ('values', 'dests'))

# Maps (function, span) to a `Branch`.
branches = {}

def parse_callsite(s):
    parts = s.split()
    out_parts = []
    index = None
    value = None
    for p in parts:
        if p.startswith('#'):
            index = int(p[1:])
        elif p.startswith('='):
            value = int(p[1:])
        else:
            out_parts.append(p)
    return (' '.join(out_parts), index, value)

for evt in evts:
    if evt['type'] == 'BRANCH':
        loc, idx, val = parse_callsite(evt['callsite'])
        if len(evt['blocks']) != 2:
            print('warning: unsupported multi-destination branch at %s' % loc)
            continue

        dest_t, dest_f = evt['blocks']

        key = (evt['function'], loc)
        if key not in branches:
            branches[key] = Branch({}, {})
        b = branches[key]

        if idx is None:
            if 0 in b.dests and b.dests[0] != dest_f:
                print('warning: multiple instances of boolean branch at %s' % loc)
                continue
            b.dests[0] = dest_f
            b.values[0] = 0
            b.dests[1] = dest_t
            b.values[1] = 1
        else:
            if idx in b.dests and b.dests[idx] != dest_t:
                print('warning: multiple instances of part %d at %s' % (idx, loc))
                continue

            b.dests[idx] = dest_t
            b.values[idx] = val
            if idx == 1 and 0 not in b.dests:
                b.dests[0] = dest_f
                b.values[0] = None

# Gather all visited blocks
visited = set()
for evt in evts:
    if evt['type'] == 'BLOCK':
        func = evt['function']
        for b in evt['blocks']:
            visited.add((func, b))

for k in sorted(branches.keys()):
    func, loc = k
    b = branches[k]

    visited_vals = sorted(b.values[i] for i, dest in b.dests.items()
            if (func, dest) in visited and b.values[i] is not None)

    for idx in sorted(b.dests.keys(), reverse=True):
        if (func, b.dests[idx]) in visited:
            continue
        val = b.values[idx]
        if val is None:
            print('%s: %s: switch condition never takes on a value other than %s' %
                    (loc, func, visited_vals))
        else:
            print('%s: %s: switch condition never takes on value %d' % (loc, func, val))
