# Generate random permutations and binary numbers for use in ./example.saw.
import random

def random_perm(n):
    inputs = ["x%i" % i for i in xrange(n)]
    outputs = random.sample(inputs, len(inputs))
    def show(vars): return "[%s]" % ",".join(vars)
    print "p%i %s = %s" % (n, show(inputs), show(outputs))

def random_bits(n):
    bits = [random.randint(0, 1) for _ in xrange(n)]
    print "r%i = 0b%s" % (n, "".join(str(b) for b in bits))

if __name__ == '__main__':
    random_perm(4)
    random_bits(4)
    random_perm(16)
    random_bits(16)
    random_perm(128)
    random_bits(128)
    random_perm(256)
    random_bits(256)
