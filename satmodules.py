import subprocess

# SAT encode of Half Adder
#   sum <-> x XOR y
# carry <-> x AND y
def HA(x,y,sum,carry,h=0):
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
  return newvarcnt, clauses

# SAT encode of Full Adder
#   sum <-> x XOR y XOR z
# carry <-> (x AND y) OR (y AND z) OR (z AND x)
def FAprev(x,y,z,sum,carry,h=0):
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
  return newvarcnt, clauses

# SAT encode of Full Adder
# x-|H|-c0--------|AND)-carry
# y-|A|-s0-|H|-c1-'
# z--------|A|----------sum
def FA(x,y,z,sum,carry,h=0):
  newvarcnt = 0
  clauses = []
  c0 = h + newvarcnt + 1
  s0 = h + newvarcnt + 2
  c1 = h + newvarcnt + 3
  newvarcnt += 3
  # HA0
  ha0 = HA(x,y,s0,c0,h+newvarcnt)
  newvarcnt += ha0[0]
  clauses += ha0[1]
  # HA1
  ha1 = HA(s0,z,sum,c1,h+newvarcnt)
  newvarcnt += ha1[0]
  clauses += ha1[1]
  # AND
  clauses.append([carry,-c0,-c1])
  clauses.append([-carry,c0])
  clauses.append([-carry,c1])
  return newvarcnt, clauses

# SAT encode of <->
def IFF(x,y):
  clauses = []
  clauses.append([x,-y])
  clauses.append([-x,y])
  return 0, clauses

# SAT encode of 
def NOT(x,y):
  clauses = []
  clauses.append([x,y])
  clauses.append([-x,-y])
  return 0, clauses

# SAT encode of x,y =|)- z
def AND(x,y,z):
  clauses = []
  clauses.append([z,-x,-y])
  clauses.append([-z,x])
  clauses.append([-z,y])
  return 0, clauses

# SAT encode of x,y =)>- z
def OR(x,y,z):
  clauses = []
  clauses.append([-z,x,y])
  clauses.append([z,-x])
  clauses.append([z,-y])
  return 0, clauses

# SAT encode of adder
#      m2 m1 m0 (r=3)
# +)      n1 n0 (s=2)
# --------------
#   z3 z2 z1 z0 (must be r+1)
def adder(x=[1,2,3],y=[4,5,6],z=[7,8,9,10],h=10):
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
      ha = HA(m[i],n[i],sum[i],carry[i],h+newvarcnt)
      newvarcnt += ha[0]
      clauses += ha[1]
    elif i < s:
      fa = FA(m[i],n[i],carry[i-1],sum[i],carry[i],h+newvarcnt)
      newvarcnt += fa[0]
      clauses += fa[1]
    else:
      ha = HA(m[i],carry[i-1],sum[i],carry[i],h+newvarcnt)
      newvarcnt += ha[0]
      clauses += ha[1]
  return newvarcnt, clauses

# SAT encode of multiplier (CSA)
#                   p3  p2  p1  p0
# *)                q3  q2  q1  q0
# ---------------------------------   i= 3  2  1  0  j
#                  I30 I20 I10 I00                   0
#              I31 I21 I11 I01             HA HA HA  1
#          I32 I22 I12 I02                 FA FA FA  2
# +)   I33 I23 I13 I03                     FA FA FA  3
# ---------------------------------        FA FA HA  4
#   P7  P6  P5  P4  P3  P2  P1  P0 
def multiplier(p=[1,2,3,4],q=[5,6,7,8],P=[9,10,11,12,13,14,15,16],h=16):
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
        ha = HA(x,y,S[i][j],C[i][j],h+newvarcnt)
        newvarcnt += ha[0]
        clauses += ha[1]
      # FA
      else:
        x = I[i][j] if j < u else C[i-1][j]
        y = S[i+1][j-1] if i < t-2 else I[i+1][j-1]
        z = C[i][j-1]
        fa = FA(x,y,z,S[i][j],C[i][j],h+newvarcnt)
        newvarcnt += fa[0]
        clauses += fa[1]
  for k in range(len(P)):
    if k == 0:
      clauses += IFF(P[k],I[0][0])[1]
    elif 0 < k <= u:
      clauses += IFF(P[k],S[0][k])[1]
    elif u < k < t + u - 1:
      clauses += IFF(P[k],S[k-u][u])[1]
    elif k == t + u - 1:
      clauses += IFF(P[k],C[t-2][u])[1]
    else:
      clauses += [[-P[k]]]
  return newvarcnt, clauses

# SAT encode of (z = b ? x : 0)
def selector0(b=9,x=[1,2,3,4],z=[5,6,7,8],h=9):
  clauses = []
  for i in range(len(x)):
    clauses += AND(x[i],b,z[i])[1]
  return 0, clauses

# SAT encode of (z = b ? x : 1)
def selector1(b=9,x=[1,2,3,4],z=[5,6,7,8],h=9):
  clauses = []
  for i in range(len(x)):
    clauses += AND(x[i],b,z[i])[1] if i != 0 else OR(x[i],-b,z[i])
  return 0, clauses

# SAT encode of MOD/DIV

# SAT encode of Montgomery Reduction
#def MontRed():
# SAT encode of Montgomery Multiplier
#def MontMul():

# output dimacs file of CNF
def output_dimacs(varsize, clauses, comments, dimacsfile='temp.dimacs'):
  vr = str(varsize)
  cl = str(len(clauses))
  open(dimacsfile,'w').close()
  with open(dimacsfile,'a',encoding='utf8') as f:
    f.write('p cnf ' + vr + ' ' + cl + '\n')
    for c in comments:
      f.write('c ' + c + '\n')
    for clause in clauses:
      f.write(' '.join([str(x) for x in clause]) + ' 0\n')

# run minisat
def run_sat(dimacsfile='temp.dimacs',output='temp.output',stdout=subprocess.PIPE,stderr=subprocess.PIPE):
  proc = subprocess.run(['minisat',dimacsfile,output], stdout = stdout, stderr = stderr)
  with open(output,'r',encoding='utf8') as f:
    satisfiability = f.readline().replace('\n','')
    assignments = f.readline().split()[:-1]
  return proc, satisfiability, assignments
