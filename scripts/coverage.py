import json
import sys

def read_report_data(f):
    buf = f.read()
    start = buf.index(b'(')
    end = buf.rindex(b')')
    return json.loads(buf[start + 1 : end])

branches = {}
visited = set()

for fn in sys.argv[1:]:
    with open(fn, 'rb') as f:
        j = read_report_data(f)

    for x in j:
        if x['type'] != 'callgraph':
            continue
        for evt in x['events']:
            if evt['type'] == 'BRANCH':
                k = (evt['function'], evt['callsite'], tuple(evt['blocks']))
                branches[k] = evt
            elif evt['type'] == 'BLOCK':
                func = evt['function']
                for b in evt['blocks']:
                    visited.add((func, b))

for evt in branches.values():
    func = evt['function']
    missing = [i for i,b in enumerate(evt['blocks']) if (func, b) not in visited]
    if len(missing) == 0:
        continue
    print('exit %s not taken at %s' % (missing, evt['callsite']))



