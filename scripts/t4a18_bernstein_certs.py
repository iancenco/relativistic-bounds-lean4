"""Generator for the exact rational Bernstein certificates used in
lean4/NaturalMechanics/T4A18_KerrInertia.lean (section "Exact rational Bernstein certificates").

Polynomials (from branches/track-4a-continuum-bounds/audit/sprint2-opus/t4a18_kerr_chain.py):
  P1c = -Fcore(B1)/u, P1k = -Fconst(B1)/u^2 on [0, 49/200]
  P2c = -Fcore(B2),   P2k = -Fconst(B2)     on [49/200, 51/125]
  P0  = B1/u - 3                            on [0, 1/200]
  e5, s4 (alpha = 69/100, I0 = 4 Kerr-barrier factors) on t = s^2 in [23/125, 1]
Each certificate is P(x) = mu + sum_k gamma_k (x-a)^k (b-x)^(n-k), mu > 0, gamma_k >= 0,
found by exact-rational Bernstein subdivision (no floating point). Requires sympy.
Usage: python3 t4a18_bernstein_certs.py > certs.lean
"""
from fractions import Fraction as Fr
import math
def poly_shift(coeffs, a, b):
    # coeffs: list of Fr, p(u)=sum c_k u^k. return q(x)=p(a+(b-a)x) coeffs
    n = len(coeffs)-1
    res = [Fr(0)]*(n+1)
    # Horner
    for c in reversed(coeffs):
        # res = res*(a+(b-a)x) + c
        new = [Fr(0)]*(n+1)
        for k in range(n+1):
            if res[k]:
                new[k] += res[k]*a
                if k+1<=n: new[k+1] += res[k]*(b-a)
        new[0] += c
        res = new
    return res
def bern_coeffs(coeffs, a, b):
    q = poly_shift(coeffs, a, b); n = len(q)-1
    return [sum(q[k]*Fr(math.comb(i,k), math.comb(n,k)) for k in range(i+1)) for i in range(n+1)]
def cert(coeffs, a, b, maxdepth=30):
    """prove p>0 on [a,b]: returns list of (a_i,b_i,bern list)"""
    out=[]
    def rec(a,b,d):
        bc = bern_coeffs(coeffs,a,b)
        if min(bc)>0: out.append((a,b,bc)); return True
        if d==0: return False
        m=(a+b)/2
        return rec(a,m,d-1) and rec(m,b,d-1)
    ok = rec(Fr(a),Fr(b),maxdepth)
    return out if ok else None
import sympy as sp, math
from fractions import Fraction as Fr
u,t = sp.symbols('u t')
R=sp.Rational
uj = R(49,200); b1=[R(61,20),-R(103,20),R(4,5),-R(103,4)]; b2=[-R(23,20),-R(133,20),R(13,10)]
B1 = sp.expand(u*(b1[0]+b1[1]*u+b1[2]*u**2+b1[3]*u**3))
d=u-uj
B2 = sp.expand(B1.subs(u,uj) + d*(b2[0]+b2[1]*d+b2[2]*d**2))
def Fcore(B): Bp=sp.diff(B,u); return sp.expand((1-2*u)*(2*B+(u-B)*Bp)-2*B*(u+B))
def Fconst(B): Bp=sp.diff(B,u); return sp.expand((1-2*u)*(2*B-2*u*Bp)-(3*u+B)*(u+B))
q=R(51,125)
def L(fr):
    fr=Fr(fr)
    if fr.denominator==1: return "(%d : ℝ)"%fr.numerator
    return "(%d / %d : ℝ)"%(fr.numerator,fr.denominator)
def tofr(e,v):
    P=sp.Poly(e,v); n=P.degree()
    return [Fr(int(sp.numer(P.coeff_monomial(v**k))),int(sp.denom(P.coeff_monomial(v**k)))) for k in range(n+1)]
def polydef(name, cs, v):
    terms=[]
    for k,c in enumerate(cs):
        if c==0: continue
        m = "" if k==0 else (" * %s"%v if k==1 else " * %s ^ %d"%(v,k))
        terms.append(L(c)+m)
    return "/-- Exact rational polynomial (generated, see docstring of section). -/\nnoncomputable def %s (%s : ℝ) : ℝ :=\n  %s\n"%(name,v," +\n    ".join(terms))
out=[]
def certify(name, e, v, a, b):
    cs=tofr(sp.expand(e),v); n=len(cs)-1
    pieces=cert(cs,Fr(a),Fr(b))
    assert pieces is not None
    out.append(polydef(name,cs,v))
    lemnames=[]
    for i,(pa,pb,bc) in enumerate(pieces):
        mu=min(bc)
        gam=[(bc[k]-mu)*math.comb(n,k)/(pb-pa)**n for k in range(n+1)]
        assert all(g>=0 for g in gam) and mu>0
        terms=[]
        for k,g in enumerate(gam):
            if g==0: continue
            terms.append("%s * (%s - %s) ^ %d * (%s - %s) ^ %d"%(L(g),v,L(pa),k,L(pb),v,n-k))
        ln="%s_pos_%d"%(name,i)
        lemnames.append((ln,pa,pb))
        out.append("""lemma %s (%s : ℝ) (h₁ : %s ≤ %s) (h₂ : %s ≤ %s) : 0 < %s %s := by
  have hX : 0 ≤ %s - %s := by linarith
  have hY : 0 ≤ %s - %s := by linarith
  have e : %s %s = %s +
      (%s) := by
    unfold %s; ring
  rw [e]; positivity
"""%(ln,v,L(pa),v,v,L(pb),name,v,v,L(pa),L(pb),v,name,v,L(mu)," +\n       ".join(terms),name))
    # combine
    body=[]
    if len(lemnames)==1:
        ln,pa,pb=lemnames[0]
        body="  exact %s %s h₁ h₂"%(ln,v)
    else:
        lines=[]
        for i,(ln,pa,pb) in enumerate(lemnames[:-1]):
            lines.append("  rcases le_or_gt %s %s with h%d | h%d"%(v,L(pb),i,i))
            lines.append("  · exact %s %s (by linarith) h%d"%(ln,v,i))
        ln,pa,pb=lemnames[-1]
        lines.append("  exact %s %s h%d.le h₂"%(ln,v,len(lemnames)-2))
        # fix: for >2 pieces, need lower bound from previous; handle via nested
        body="\n".join(lines)
        if len(lemnames)>2:
            lines=[]
            for i,(ln,pa,pb) in enumerate(lemnames):
                lo = "h₁" if i==0 else "(le_of_lt h%d)"%(i-1)
                if i<len(lemnames)-1:
                    lines.append("  rcases le_or_gt %s %s with h%d | h%d"%(v,L(pb),i,i))
                    lines.append("  · exact %s %s %s h%d"%(ln,v,"(by linarith)" if i>0 else "h₁",i))
                else:
                    lines.append("  exact %s %s (le_of_lt h%d) h₂"%(ln,v,i-1))
            body="\n".join(lines)
    out.append("""/-- Exact Bernstein certificate: `%s > 0` on `[%s, %s]`. -/
lemma %s_pos (%s : ℝ) (h₁ : %s ≤ %s) (h₂ : %s ≤ %s) : 0 < %s %s := by
%s
"""%(name,a,b,name,v,L(Fr(a)),v,v,L(Fr(b)),name,v,body))
    return cs
def frR(x): return Fr(x.p,x.q)
certify("P1c", -sp.cancel(Fcore(B1)/u), u, Fr(0), frR(uj))
certify("P1k", -sp.cancel(Fconst(B1)/u**2), u, Fr(0), frR(uj))
certify("P2c", -Fcore(B2), u, frR(uj), frR(q))
certify("P2k", -Fconst(B2), u, frR(uj), frR(q))
certify("P0", sp.cancel(B1/u)-3, u, Fr(0), Fr(1,200))
certify("e5", 31*t**5 - 117*t**4 + 51*t**3 - 1023*t**2 + 1737*t - 279, t, Fr(23,125), Fr(1))
certify("s4", 31*t**4 - 48*t**3 - 363*t**2 + 498*t - 63, t, Fr(23,125), Fr(1))
print("\n".join(out))
import sys; print("-- B2(51/125) =", B2.subs(u,q), file=sys.stderr)
