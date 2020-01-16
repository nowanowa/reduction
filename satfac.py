import numpy
import subprocess
from . import satmodules

def int2bitarray(x): return [int(b) for b in bin(x)[2:]]
def bitarray2int(x): return int(''.join(list(map(str,x))),2)

# factorize integer
class satFactorize:
  #
  # init
  #
  def __init__(self, target):
    self.target = target
    self.tbits = numpy.array(int2bitarray(target),dtype='uint8')
    self.tbitlen = int(numpy.log2(target)) + 1 # = len(self.tbits)

    l = self.tbitlen
    self.t = l-1
    self.u = l-1
    self.varsize = 0
    self.clauses = []
    self.satisfiability = 'UNSAT'
    self.fbits = numpy.zeros(l*2,dtype='uint8')
    self.facts = [1,1]
    self.out = ''
    self.err = ''

    self.setbitlen(self.t, self.u)
    self.setcnf()

  # setup bit length of each factors
  def setbitlen(self,t,u):
    self.t = t
    self.u = u

  # setup of CNF formula
  def setcnf(self):
    # p = [1,2,3,4]
    # q = [5,6,7,8]
    # N = [9,10,11,12,13,14,15,16]
    h = 0
    p = [h + 1 + i for i in range(self.t)]
    h += self.t
    q = [h + 1 + j for j in range(self.u)]
    h += self.u
    v = self.t + self.u
    N = [h + 1 + k for k in range(v)]
    h += v
    # N == targetnumber
    self.varsize = len(p) + len(q) + len(N)
    self.clauses = []
    target_pm = numpy.flip(self.tbits.astype('int') * 2 - 1)
    minuses = -1 * numpy.ones(len(N)-len(self.tbits),dtype='int')
    target = numpy.append(target_pm, minuses)
    for i in range(len(N)):
      self.clauses.append([N[i] * target[i]])
    # p*q == N
    mul_var, mul_cla = satmodules.multiplier(p,q,N,h)
    self.varsize += mul_var
    self.clauses += mul_cla

  #
  # run SAT solver
  #
  def run_sat(self,dimacsfile='temp.dimacs',output='temp.output',stdout=subprocess.PIPE,stderr=subprocess.PIPE):
    self.output_dimacs(dimacsfile)
    run = satmodules.run_sat(dimacsfile,output,stdout,stderr)
    proc, satisfiability, assignments = run
    self.out = proc.stdout.decode('utf8')
    self.err = proc.stderr.decode('utf8')
    if satisfiability == 'SAT':
      ans = numpy.array([int(x) > 0 for x in assignments], dtype='uint8')
    else:
      ans = numpy.zeros(self.t+self.u, dtype='uint8')
    self.satisfiability = satisfiability
    self.fbits = ans[0:self.t+self.u]
    p = numpy.flip(ans[0:self.t])
    q = numpy.flip(ans[self.t:self.t+self.u])
    self.facts = [bitarray2int(p), bitarray2int(q)]

  # output dimacs file of CNF
  def output_dimacs(self,dimacsfile='temp.dimacs'):
    comments = []
    t = str(1) + '-' + str(self.t)
    u = str(self.t+1) + '-' + str(self.t+self.u)
    comments.append('Factors encoded in variables ' + t + ' and ' + u)
    tg = str(self.target)
    comments.append('Target number: ' + tg)
    comments.append('Minowa Taro')
    satmodules.output_dimacs(self.varsize, self.clauses, comments, dimacsfile)

def testsat(n):
  a = satFactorize(n)
  a.run_sat()
  return a.tbitlen, n, a.facts, a.satisfiability, a

def testsat2(n,stdout=subprocess.PIPE):
  a = satFactorize(n)
  t = int(numpy.log2(n)/2.) + 1
  u = int(numpy.log2(n/3.)) + 1
  a.setbitlen(t,u)
  a.setcnf()
  a.run_sat(stdout=stdout)
  return a.tbitlen, n, a.facts, a.satisfiability, a
