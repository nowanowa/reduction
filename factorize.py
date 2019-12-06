import math
import numpy
import subprocess
import wildqat
from numpy import exp2 as E2


# factorize 8bit integer using minisat (SAT solver)
class sat:
  # init
  def __init__(self, target):
    #if target <= 2 or target >= 256:# or target % 2 == 0:
    #  raise ValueError('target N must be odd, 3 <= N <= 255')
    self.target = target
    self.tbits = numpy.unpackbits(numpy.array([target],dtype='uint8'))
    self.facts = numpy.array([1,1],dtype='uint8')
    self.fbits = numpy.array([0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,1],dtype='uint8')
    self.satisfiability = 'UNSAT'
    self.t = 4
    self.u = 4
    self.varsize = 8
    self.clauses = []
    self.out = ''
    self.err = ''
    # p = ____0000, q = ____0000

  # setup bit length of each factors
  def setbitlen(self,t,u):
    #if t <= 0 or u <= 0 or t >= 8 or u >= 8:
    #  raise ValueError('len = t or u must be 1 <= len <= 8')
    self.t = t
    self.u = u
    self.varsize = t + u

  # from 2 * 8bit boolean to 2 integer
  def decodepq(self,fbits):
    facts = numpy.packbits(numpy.split(fbits.astype('uint8'),2))
    return facts
  # from answer to factors bits (max 8bit)
  def slicepq(self,ans):
    p = numpy.flip(ans[0:self.t])
    q = numpy.flip(ans[self.t:self.t+self.u])
    _p = numpy.zeros(8-self.t,dtype='uint8')
    _q = numpy.zeros(8-self.u,dtype='uint8')
    fbits = numpy.concatenate((_p,p,_q,q)).astype('uint8')
    return fbits

  # sat encode of Half Adder
  #   sum <-> x XOR y
  # carry <-> x AND y
  def HA(self,x,y,sum,carry,h=0):
    newvarcnt = 0
    clauses = []
    # XOR
    clauses.append([sum,x,-y])
    clauses.append([sum,-x,y])
    clauses.append([-sum,x,y])
    clauses.append([-sum,-x,-y])
    # AND
    clauses.append([carry,-x,-y])
    clauses.append([-carry,x])
    clauses.append([-carry,y])
    return (newvarcnt,clauses)

  # sat encode of Full Adder
  #   sum <-> x XOR y XOR z
  # carry <-> (x AND y) OR (y AND z) OR (z AND x)
  def FA(self,x,y,z,sum,carry,h=0):
    newvarcnt = 0
    clauses = []
    # XOR
    clauses.append([sum,-x,y,z])
    clauses.append([sum,x,-y,z])
    clauses.append([sum,x,y,-z])
    clauses.append([sum,-x,-y,-z])
    clauses.append([-sum,x,-y,-z])
    clauses.append([-sum,-x,y,-z])
    clauses.append([-sum,-x,-y,z])
    clauses.append([-sum,x,y,z])
    # AND
    a = h + newvarcnt + 1
    b = h + newvarcnt + 2
    c = h + newvarcnt + 3
    newvarcnt += 3
    clauses.append([-carry,a,b,c])
    clauses.append([carry,-a])
    clauses.append([carry,-b])
    clauses.append([carry,-c])
    clauses.append([a,-x,-y])
    clauses.append([-a,x])
    clauses.append([-a,y])
    clauses.append([b,-y,-z])
    clauses.append([-b,y])
    clauses.append([-b,z])
    clauses.append([c,-z,-x])
    clauses.append([-c,z])
    clauses.append([-c,x])
    return (newvarcnt,clauses)

  # sat encode of <->
  def IFF(self,x,y):
    clauses = []
    clauses.append([x,-y])
    clauses.append([-x,y])
    return clauses
  
  # sat encode of adder
  #      m2 m1 m0 (r=3)
  # +)      n1 n0 (s=2)
  # --------------
  #   z3 z2 z1 z0 (must be r+1)
  def adder(self,x=[1,2,3],y=[4,5,6],z=[7,8,9,10],h=10):
    t = len(x)
    u = len(y)
    m = x if t >= u else y
    n = y if t >= u else x
    r = max(t,u)
    s = min(t,u)
    newvarcnt = 0
    clauses = []
    sum = z[0:-1]
    carry = [h+1 + i for i in range(r-1)]
    newvarcnt += r-1
    carry.append(z[-1])
    for i in range(r):
      if i == 0:
        ha = self.HA(m[i],n[i],sum[i],carry[i],h+newvarcnt)
        newvarcnt += ha[0]
        clauses += ha[1]
      elif i < s:
        fa = self.FA(m[i],n[i],carry[i-1],sum[i],carry[i],h+newvarcnt)
        newvarcnt += fa[0]
        clauses += fa[1]
      else:
        ha = self.HA(m[i],carry[i-1],sum[i],carry[i],h+newvarcnt)
        newvarcnt += ha[0]
        clauses += ha[1]
    return (newvarcnt,clauses)

  # sat encode of multiplier (CSA)
  #                   p3  p2  p1  p0
  # *)                q3  q2  q1  q0
  # ---------------------------------   i= 3  2  1  0  j
  #                  I30 I20 I10 I00                   0
  #              I31 I21 I11 I01             HA HA HA  1
  #          I32 I22 I12 I02                 FA FA FA  2
  # +)   I33 I23 I13 I03                     FA FA FA  3
  # ---------------------------------        FA FA HA  4
  #   P7  P6  P5  P4  P3  P2  P1  P0 
  def multiplier(self,p=[1,2,3,4],q=[5,6,7,8],P=[9,10,11,12,13,14,15,16],h=16):
    t = len(p)
    u = len(q)
    newvarcnt = 0
    clauses = []
    I = [[h+newvarcnt + 1+i*u+j for j in range(u)] for i in range(t)]
    newvarcnt += t*u
    for i in range(t):
      for j in range(u):
        # I[i][j] <-> p[i] AND q[j]
        clauses.append([I[i][j],-p[i],-q[j]])
        clauses.append([-I[i][j],p[i]])
        clauses.append([-I[i][j],q[j]])
    S = [[h+newvarcnt + i*u+j if j != 0 else 0 for j in range(u+1)] for i in range(t-1)]
    newvarcnt += (t-1)*u
    C = [[h+newvarcnt + i*u+j if j != 0 else 0 for j in range(u+1)] for i in range(t-1)]
    newvarcnt += (t-1)*u
    for i in range(t-1):
      for j in range(1,u+1):
        # HA
        if j == 1 or (j == u and i == 0):
          x = I[i][j]     if j == 1 else S[i+1][j-1]
          y = I[i+1][j-1] if j == 1 else C[i][j-1]
          ha = self.HA(x,y,S[i][j],C[i][j],h+newvarcnt)
          newvarcnt += ha[0]
          clauses += ha[1]
        # FA
        else:
          x = I[i][j] if j < u else C[i-1][j]
          y = S[i+1][j-1] if i < t-2 else I[i+1][j-1]
          z = C[i][j-1]
          fa = self.FA(x,y,z,S[i][j],C[i][j],h+newvarcnt)
          newvarcnt += fa[0]
          clauses += fa[1]
    for k in range(len(P)):
      if k == 0:
        clauses += self.IFF(P[k],I[0][0])
      elif 0 < k <= u:
        clauses += self.IFF(P[k],S[0][k])
      elif u < k < t + u - 1:
        clauses += self.IFF(P[k],S[k-u][u])
      elif k == t + u - 1:
        clauses += self.IFF(P[k],C[t-2][u])
      else:
        clauses += [[-P[k]]]
    return (newvarcnt,clauses)
  
  # setup of cnf formula
  def setcnfsat(self):
    #p = [1,2,3,4]
    #q = [5,6,7,8]
    #N = [9,10,11,12,13,14,15,16]
    h = 0
    p = [h + 1 + i for i in range(self.t)]
    h += self.t
    q = [h + 1 + j for j in range(self.u)]
    h += self.u
    v = self.t + self.u # 8
    N = [h + 1 + k for k in range(v)]
    h += v
    mul = self.multiplier(p,q,N,h)
    #mul = self.adder(p,q,N,13)
    self.varsize = len(p) + len(q) + len(N) + mul[0]
    self.clauses = mul[1]
    target_pm = numpy.flip(self.tbits.astype('int') * 2 - 1)
    minuses = -1 * numpy.ones(len(N)-len(self.tbits),dtype='int')
    target = numpy.append(target_pm, minuses)
    for i in range(len(N)):
      self.clauses.append([N[i] * target[i]])

  # output dimacs file of cnfsat
  def output_dimacs(self,dimacsfile='temp.dimacs'):
    vr = str(self.varsize)
    cl = str(len(self.clauses))
    t = str(1) + '-' + str(self.t)
    u = str(self.t+1) + '-' + str(self.t+self.u)
    tg = str(self.target)
    open(dimacsfile,'w').close()
    with open(dimacsfile,'a',encoding='utf8') as f:
      f.write('p cnf ' + vr + ' ' + cl + '\n')
      f.write('c Factors encoded in variables ' + t + ' and ' + u + '\n')
      f.write('c Target number: ' + tg + '\n')
      f.write('c Minowa Taro\n')
      for clause in self.clauses:
        f.write(' '.join([str(x) for x in clause]) + ' 0\n')

  # run minsat
  def run_sat(self,dimacsfile='temp.dimacs',output='temp.output',stdout=subprocess.PIPE,stderr=subprocess.PIPE):
    self.output_dimacs(dimacsfile)
    proc = subprocess.run(['minisat',dimacsfile,output], stdout = stdout, stderr = stderr)
    with open(output,'r',encoding='utf8') as f:
      sat = f.readline().replace('\n','')
      lits = f.readline().split()[:-1]
    self.satisfiability = sat
    if sat == 'SAT':
      ans = numpy.array([int(x) > 0 for x in lits], dtype='uint8')
    else:
      ans = numpy.zeros(16,dtype='uint8')
    self.fbits = self.slicepq(ans)
    self.facts = self.decodepq(self.fbits)
    self.out = proc.stdout.decode('utf8')
    self.err = proc.stderr.decode('utf8')


# factorize 8bit odd integer using wildqat (simulated quantum annealer)
class annealer(wildqat.opt):
  # init
  def __init__(self, target):
    wildqat.opt.__init__(self)
    #if target <= 2 or target >= 256 or target % 2 == 0:
    #  raise ValueError('target N must be odd, 3 <= N <= 255')
    self.target = target
    self.tbits = numpy.unpackbits(numpy.array([target],dtype='uint8'))
    self.factss = numpy.zeros((8,2),dtype='uint8')
    self.fbitss = numpy.zeros((8,16),dtype='uint8')
    self.Es = numpy.zeros(8)
    self.t = 3
    self.u = 6
    self.Hs = numpy.zeros(8)
    # p = ____0001, q = _0000001
  # setup bit length (2^0 is 1)
  def setbitlen(self,t,u):
    #if t <= 0 or u <= 0 or t >= 8 or u >= 8:
    #  raise ValueError('len = t or u must be 1 <= len <= 8')
    self.t = t - 1
    self.u = u - 1
    return

  # from 8bit boolean to integer
  def decodepq(self,fbits):
    facts = numpy.packbits(numpy.split(fbits.astype('uint8'),2))
    return facts
  # from answer to factors bits (max 8bit)
  def slicepq(self,ans):
    p = numpy.flip(ans[0:self.t])
    q = numpy.flip(ans[self.t:self.t+self.u])
    _p = numpy.zeros(7-self.t,dtype='uint8')
    _q = numpy.zeros(7-self.u,dtype='uint8')
    fbits = numpy.concatenate((_p,p,[1],_q,q,[1])).astype('uint8')
    return fbits
  # calculate hammiltonean
  def hamm(self,ans):
    H = 0
    qubo = self.qubo
    for i in range(len(qubo)):
      row = qubo[i]
      for j in range(len(row)):
        H += row[j] * ans[i] * ans[j]
    return H

  # run simulated annealing
  def run_sa(self):
    for i in range(8):
      ans = self.sa()
      self.fbitss[i] = self.slicepq(ans)
      self.factss[i] = self.decodepq(self.fbitss[i])
      self.Es[i] = self.E[-1]
      self.Hs[i] = self.hamm(ans)
    return ans
  # run simulated quantum annealing
  def run_sqa(self):
    anss = (self.sqa() + 1) // 2
    for i in range(8):
      ans = anss[i]
      self.fbitss[i] = self.slicepq(ans)
      self.factss[i] = self.decodepq(self.fbitss[i])
      self.Es[i] = self.E[-1]
      self.Hs[i] = self.hamm(ans)
    return anss

  # setup QUBO matrix
  def setqubo(self,D=0):
    N = self.target
    t = self.t
    u = self.u
    v = t * (t-1) // 2
    w = u * (u-1) // 2
    if D == 0:
      D = E2((t+u)*2) * 128
    # p = 0000???1, q = 0??????1
    # 3 + 6 + 3[3C2] + 15[6C2] = 27
    pp = numpy.zeros((t,t))
    pq = numpy.zeros((t,u))
    pr = numpy.zeros((t,v))
    ps = numpy.zeros((t,w))
    qq = numpy.zeros((u,u))
    qr = numpy.zeros((u,v))
    qs = numpy.zeros((u,w))
    rr = numpy.zeros((v,v))
    rs = numpy.zeros((v,w))
    ss = numpy.zeros((w,w))
    a = numpy.zeros(v)
    b = numpy.zeros(w)
    # pp, pr, rr
    m = 0
    for i in range(t):
      pp[i][i] = E2(i+2) * (1 + E2(i) - N)
      for j in range(i+1, t):
        a[m] = E2(i+j+3)
        rr[m][m] = a[m] + 3 * D
        pp[i][j] = D
        pr[i][m] = -2 * D
        pr[j][m] = -2 * D
        m += 1
    # qq, qs, ss
    n = 0
    for k in range(u):
      qq[k][k] = E2(k+2) * (1 + E2(k) - N)
      for l in range(k+1, u):
        b[n] = E2(k+l+3)
        ss[n][n] = b[n] + 3 * D
        qq[k][l] = D
        qs[k][n] = -2 * D
        qs[l][n] = -2 * D
        n += 1
    # pq
    for i in range(t):
      for k in range(u):
        pq[i][k] = E2(i+k+3) * (2 + E2(i+1) + E2(k+1) + E2(i+k+1) - N)
    # ps
    for i in range(t):
      n = 0
      for n in range(w):
        ps[i][n] = 4 * (E2(i) + E2(2*i)) * b[n]
    # qr
    for k in range(u):
      m = 0
      for m in range(v):
        qr[k][m] = 4 * (E2(k) + E2(2*k)) * a[m]
    # rs
    m = 0
    n = 0
    for m in range(v):
      for n in range(w):
        rs[m][n] = a[m] * b[n]
    # wildqat qubo
    self.qubo = numpy.block([
      [pp,                 pq,                 pr,                 ps],
      [numpy.zeros((u,t)), qq,                 qr,                 qs],
      [numpy.zeros((v,t)), numpy.zeros((v,u)), rr,                 rs],
      [numpy.zeros((w,t)), numpy.zeros((w,u)), numpy.zeros((w,v)), ss]
    ])



def testsat(n):
  a = sat(n)
  t = int(numpy.log2(n)/2.) + 1
  u = int(numpy.log2(n/3.)) + 1
  #print(t,u)
  a.setbitlen(t,u)
  a.setcnfsat()
  a.run_sat()
  return (a.satisfiability, a.facts, a)

def testanneal(n):
  a = annealer(n)
  t = int(numpy.log2(n)/2.) + 1
  u = int(numpy.log2(n/3.)) + 1
  #print(t,u)
  a.setbitlen(t,u)
  a.setqubo()
  a.run_sqa()
  return (a.factss, a.Hs, a)
