"""Opus independent audit of T4A-18 (N40, N41, N33).

Part A: exact re-derivation of the Hartle-TOV Riccati residual along the vacuum curve,
        from first principles (not copied from neon-1 code).
Part B: exact verification of the N40 two-piece barrier polynomials (own Sturm + own
        exact-rational Bernstein subdivision, two independent methods).
Part C: N41 alpha = 69/100 positivity on t = s^2 in [23/125, 1]; exact thresholds.
Part D: N33 Part I w_Kerr, Part II and Part III constants.
Part E: numerical stress tests:
   E1 exact-equality identity I = 4 M^3 for P_r = w_Kerr(s) eps (tapered profile)
   E2 relaxed bang-bang compactness maxima
   E3 counterexample hunt: monotone isotropic DEC stars minimising I/M^3
Part F: rounding / application numbers.
ASCII output only.
"""
from fractions import Fraction as Fr
import math
import sympy as sp
import numpy as np
from scipy.integrate import solve_ivp
from scipy.optimize import minimize, brentq

print("=" * 78)
print("T4A-18 independent audit (Opus)")
print("=" * 78)

# ---------------------------------------------------------------------------
# Part A: residual along vacuum curve, derived from scratch
# ---------------------------------------------------------------------------
s, pe, pr, pt, al, I0 = sp.symbols('s pi_e pi_r pi_t alpha I0', real=True)
Wv = sp.symbols('W', real=True)
u_s = (1 - s**2) / 2
# Vacuum curve: y = r wbar'/wbar at radius with compactness C=(1-s^2)/2, Ibar = I0
# I = R^3 y/(6+2y)  =>  y = 3 I0 (1-s^2)^3 / (4 - I0 (1-s^2)^3), Z = s*y
Zc = 3 * I0 * s * (1 - s**2)**3 / (4 - I0 * (1 - s**2)**3)
# Riccati for y (derived): r y' = -y^2 - 3y + (pe+pr) y / s^2 + 4 (pe+pt)/s^2
# Z = s y ; r s' = (u - pe)/s
Z = Wv + 2 * al * pr / s
y = Z / s
rs_p = (u_s - pe) / s
ry_p = -y**2 - 3 * y + (pe + pr) * y / s**2 + 4 * (pe + pt) / s**2
rZ_p = rs_p * y + s * ry_p
# anisotropic TOV: pi_t = r pi_r'/2 + (pe+pr)(u+pr)/(2 s^2)  => r pi_r' = 2 pt - (pe+pr)(u+pr)/s^2
rpr_p = 2 * pt - (pe + pr) * (u_s + pr) / s**2
rW_p = rZ_p - 2 * al * (rpr_p / s - pr * rs_p / s**2)
res = sp.together(rW_p.subs(Wv, Zc) - sp.diff(Zc, s) * rs_p)
res = sp.expand(sp.simplify(res))
P = sp.Poly(sp.numer(sp.together(res)), pe, pr, pt)
den = sp.denom(sp.together(res))
coef = {}
for mon, c in zip(P.monoms(), P.coeffs()):
    coef[mon] = sp.simplify(c / den)
const = sp.simplify(coef.get((0, 0, 0), 0))
cross = sp.simplify(coef.get((1, 1, 0), 0))
c_pr2 = sp.simplify(coef.get((0, 2, 0), 0))
c_pt = sp.simplify(coef.get((0, 0, 1), 0))
c_e = sp.simplify(coef.get((1, 0, 0), 0))
c_r = sp.simplify(coef.get((0, 1, 0), 0))
others = [m for m in coef if m not in [(0, 0, 0), (1, 1, 0), (0, 2, 0), (0, 0, 1), (1, 0, 0), (0, 1, 0)]]
print("[A] constant term along vacuum curve      :", const)
print("[A] pi_e*pi_r cross term                  :", cross)
print("[A] coeff(pi_r^2)                         :", sp.factor(c_pr2))
print("[A] coeff(pi_t)                           :", sp.factor(c_pt))
print("[A] other monomials present               :", others)
assert const == 0 and cross == 0
assert sp.simplify(c_pr2 - 4 * al * (1 - al) / s**3) == 0
assert sp.simplify(c_pt - 4 * (1 - al) / s) == 0

# isotropic: pi_t = pi_p = pi_r ; coefficients
c_eps_iso = c_e
c_p_iso = sp.simplify(c_r + c_pt)
# ---------------------------------------------------------------------------
# Part D (first): N33 Part I w_Kerr  (alpha=1, I0=4)
# ---------------------------------------------------------------------------
ce1 = sp.factor(sp.simplify(c_e.subs({al: 1, I0: 4})))
cr1 = sp.factor(sp.simplify(c_r.subs({al: 1, I0: 4})))
wK = sp.factor(sp.simplify(-ce1 / cr1))
wK_claim = (9 - 6 * s**4 + s**6) / (3 * (3 - s**2) * (3 - 3 * s**2 + s**4))
print("[D1] alpha=1 coeff(pi_e)                  :", ce1)
print("[D1] alpha=1 coeff(pi_r)                  :", cr1)
print("[D1] w_Kerr derived                       :", wK)
assert sp.simplify(wK - wK_claim) == 0
print("[D1] w_Kerr(1) =", wK_claim.subs(s, 1), " w_Kerr(0) =", wK_claim.subs(s, 0))
d13 = sp.factor(sp.simplify(wK_claim - sp.Rational(1, 3)))
print("[D1] w_Kerr - 1/3 =", d13)
# check positivity of w_Kerr - 1/3 on (0,1]
num13 = sp.Poly(sp.numer(sp.together(wK_claim - sp.Rational(1, 3))), s)
print("[D1] real roots of numerator(w_Kerr-1/3) in (0,1]:",
      [r for r in sp.real_roots(num13) if 0 < r <= 1])

# Part II: alpha = 0, find sup I0 with coeff(pi_e) >= 0 for all s in (0,1)
ce0 = sp.simplify(c_e.subs({al: 0}))
uu = sp.symbols('uu', positive=True)  # uu = 1 - s^2
num0 = sp.factor(sp.numer(sp.together(ce0)))
print("[D2] alpha=0 numerator coeff(pi_e)        :", num0)
I2 = (1021 + sp.sqrt(6073353)) / 1024
def min_ce_alpha(alpha_val, I0_val, smin=1e-6, smax=1.0, n=20001, iso=False):
    f = sp.lambdify(s, (c_eps_iso if not iso else c_eps_iso).subs({al: alpha_val, I0: I0_val}), 'numpy')
    ss = np.linspace(smin, smax, n)
    return float(np.min(f(ss)))
for I0v in [float(I2) - 1e-6, float(I2) + 1e-4]:
    print("[D2] min_s coeff(pi_e) at alpha=0, I0=%.8f : %.3e" % (I0v, min_ce_alpha(0, I0v)))
# exact: coefficient numerator as polynomial in uu after s^2 = 1-uu
ce0_u = sp.simplify(ce0.subs(s, sp.sqrt(1 - uu)) * sp.sqrt(1 - uu))
print("[D2] s*coeff(pi_e), alpha=0, in uu=1-s^2  :", sp.factor(sp.simplify(ce0_u)))
# Part III: alpha = 2/5, isotropic
ce25 = sp.simplify(c_eps_iso.subs({al: sp.Rational(2, 5)}))
cp25 = sp.simplify(c_p_iso.subs({al: sp.Rational(2, 5)}))
cp25_4 = sp.factor(sp.simplify(cp25.subs(I0, 4)))
ce25_4 = sp.factor(sp.simplify(ce25.subs(I0, 4)))
print("[D3] alpha=2/5 I0=4 coeff(pi_p) iso       :", cp25_4)
print("[D3] alpha=2/5 I0=4 coeff(pi_e)           :", ce25_4)
num_ce25 = sp.Poly(sp.numer(sp.together(ce25_4)), s)
rts = [sp.N(r, 15) for r in sp.real_roots(num_ce25) if 0 < r < 1]
print("[D3] roots of coeff(pi_e) numerator in (0,1):", rts)
sK = max([r for r in rts])
print("[D3] => C_Kerr,iso = (1-s^2)/2 =", sp.N((1 - sK**2) / 2, 12), " (ledger 0.3673541659)")
# Ibar_iso* : largest I0 with coeff(pi_e)>=0 and coeff(pi_p)>=0 for all s in (0,1]
def ok_iso(I0v, alpha_val=0.4):
    fe = sp.lambdify(s, c_eps_iso.subs({al: alpha_val, I0: I0v}), 'numpy')
    fp = sp.lambdify(s, c_p_iso.subs({al: alpha_val, I0: I0v}), 'numpy')
    ss = np.linspace(1e-3, 1.0 - 1e-9, 40001)
    # c_p vanishes exactly at s=1 (factor (1-s^2)); allow round-off there
    return min(np.min(fe(ss)), np.min(fp(ss)) + 1e-12)
lo, hi = 3.0, 4.0
for _ in range(50):
    mid = 0.5 * (lo + hi)
    if ok_iso(mid) >= 0:
        lo = mid
    else:
        hi = mid
print("[D3] grid sup I0 with both coeffs >= 0 (alpha=2/5): %.10f  (ledger 3.7685208416)" % lo)
Nce = sp.numer(sp.together(c_eps_iso.subs({al: sp.Rational(2, 5)})))
fN = sp.lambdify((s, I0), Nce, 'mpmath'); fdN = sp.lambdify((s, I0), sp.diff(Nce, s), 'mpmath')
import mpmath as _mp
_mp.mp.dps = 30
dr = _mp.findroot(lambda a, b: [fN(a, b), fdN(a, b)], (0.36, 3.7685))
print("[D3] exact double-root of coeff(pi_e) numerator: s = %s, I0 = %s (ledger 3.7685208416)" % (_mp.nstr(dr[0], 12), _mp.nstr(dr[1], 13)))

# ---------------------------------------------------------------------------
# Part C: N41 alpha = 69/100
# ---------------------------------------------------------------------------
t = sp.symbols('t', positive=True)
a69 = sp.Rational(69, 100)
ce69 = sp.simplify(c_eps_iso.subs({al: a69, I0: 4}))
cp69 = sp.simplify(c_p_iso.subs({al: a69, I0: 4}))
def num_in_t(expr):
    # expr in s ; multiply by suitable power of s to make polynomial in s^2
    e = sp.together(expr)
    n, d = sp.numer(e), sp.denom(e)
    n = sp.expand(n); d = sp.expand(d)
    return n, d
for name, ex in [("c_eps", ce69), ("c_eps + c_p", sp.simplify(ce69 + cp69))]:
    n, d = num_in_t(ex)
    # substitute s = sqrt(t): n and d should be s^k * poly(t)
    nP = sp.Poly(n, s); dP = sp.Poly(d, s)
    print("[C] %s : numerator degree %d, denominator %s" % (name, nP.degree(), sp.factor(d)))
    # sign on t in [23/125, 1] via s in [sqrt(23/125), 1]
    rr = [r for r in sp.real_roots(nP) if sp.sqrt(sp.Rational(23, 125)) <= r <= 1]
    print("    real roots of numerator for s in [sqrt(23/125),1]:", [sp.N(r, 12) for r in rr])
    val = sp.N(ex.subs(s, sp.sqrt(sp.Rational(23, 125))), 10)
    print("    value at t=23/125:", val)
    assert len(rr) == 0
    # denominator sign
    dsgn = [sp.N(d.subs(s, v)) for v in [sp.sqrt(sp.Rational(23, 125)), sp.Rational(1, 2), 1]]
    print("    denominator samples:", dsgn)
# exact threshold for alpha=69/100: largest m/r such that both >= 0 for all s above
def thr(alpha_val):
    fe = sp.Poly(sp.numer(sp.together(c_eps_iso.subs({al: alpha_val, I0: 4}))), s)
    fs = sp.Poly(sp.numer(sp.together((c_eps_iso + c_p_iso).subs({al: alpha_val, I0: 4}))), s)
    roots = [r for r in sp.real_roots(fe) + sp.real_roots(fs) if 0 < r < 1]
    smax = max(roots) if roots else 0
    return sp.N((1 - smax**2) / 2, 12), sp.N(smax, 12)
print("[C] alpha=69/100 Kerr threshold max m/r, s :", thr(a69), " (ledger 0.4102534466)")
# center factor
cf = 1 + (1 - sp.Rational(5, 2) * a69) * 1
print("[C] center factor at p_c = eps_c          :", cf, "=", sp.N(cf))
assert cf == sp.Rational(11, 40)

# ---------------------------------------------------------------------------
# Part B: N40 barrier polynomials
# ---------------------------------------------------------------------------
u = sp.symbols('u', real=True)
def barrier(w, uj, b1, b2):
    B1 = u * (b1[0] + b1[1] * u + b1[2] * u**2 + b1[3] * u**3)
    B1j = B1.subs(u, uj)
    d = u - uj
    B2 = B1j + d * (b2[0] + b2[1] * d + b2[2] * d**2)
    return sp.expand(B1), sp.expand(B2)
def Fcore(B, w):
    Bp = sp.diff(B, u)
    return sp.expand((1 - 2 * u) * (2 * B + (u - B / w) * Bp) - (1 + 1 / w) * B * (u + B))
def Fconst(B):
    Bp = sp.diff(B, u)
    return sp.expand((1 - 2 * u) * (2 * B - 2 * u * Bp) - (3 * u + B) * (u + B))

def bern_min_sign(poly_expr, a, b, depth=40):
    """exact-rational Bernstein subdivision: returns (sign, leaves) with sign=-1 if
    poly < 0 on [a,b] proved, +1 if > 0 proved, 0 if failed."""
    Pp = sp.Poly(poly_expr, u)
    n = Pp.degree()
    # map u = a + (b-a) x, x in [0,1]
    x = sp.symbols('x')
    q = sp.Poly(sp.expand(Pp.as_expr().subs(u, a + (b - a) * x)), x)
    coeffs = [Fr(int(sp.numer(q.coeff_monomial(x**k))), int(sp.denom(q.coeff_monomial(x**k)))) for k in range(n + 1)]
    # power -> Bernstein
    bern = []
    for i in range(n + 1):
        sacc = Fr(0)
        for k in range(i + 1):
            sacc += coeffs[k] * Fr(math.comb(i, k), math.comb(n, k))
        bern.append(sacc)
    def split(bc):
        # de Casteljau at 1/2
        m = len(bc) - 1
        left, right = [bc[0]], [bc[-1]]
        cur = bc[:]
        for lev in range(1, m + 1):
            cur = [(cur[i] + cur[i + 1]) / 2 for i in range(len(cur) - 1)]
            left.append(cur[0]); right.append(cur[-1])
        return left, right[::-1]
    def rec(bc, dep, target):
        if target < 0 and max(bc) < 0:
            return 1
        if target > 0 and min(bc) > 0:
            return 1
        if dep == 0:
            return None
        L, R = split(bc)
        l1 = rec(L, dep - 1, target)
        if l1 is None:
            return None
        l2 = rec(R, dep - 1, target)
        if l2 is None:
            return None
        return l1 + l2
    for target in (-1, 1):
        leaves = rec(bern, depth, target)
        if leaves is not None:
            return target, leaves
    return 0, None

cases = {
    '1/3': (sp.Rational(1, 3), sp.Rational(47, 200),
            [sp.Rational(21, 20), -sp.Rational(9, 5), sp.Rational(29, 20), -17],
            [-sp.Rational(3, 5), -sp.Rational(43, 10), -sp.Rational(13, 20)], sp.Rational(343, 1000), 0.34205790),
    '1/2': (sp.Rational(1, 2), sp.Rational(49, 200),
            [sp.Rational(38, 25), -sp.Rational(62, 25), sp.Rational(59, 50), -sp.Rational(458, 25)],
            [-sp.Rational(39, 50), -sp.Rational(127, 25), -sp.Rational(6, 25)], sp.Rational(369, 1000), 0.368804),
    '1': (sp.Integer(1), sp.Rational(49, 200),
          [sp.Rational(61, 20), -sp.Rational(103, 20), sp.Rational(4, 5), -sp.Rational(103, 4)],
          [-sp.Rational(23, 20), -sp.Rational(133, 20), sp.Rational(13, 10)], sp.Rational(51, 125), 0.407566),
}
uzero = {}
for key, (w, uj, b1, b2, cap, ledger_val) in cases.items():
    B1, B2 = barrier(w, uj, b1, b2)
    print("[B] w = %s : B1'(0) = %s > 3w = %s ? %s" % (key, b1[0], 3 * w, b1[0] > 3 * w))
    d1 = sp.diff(B1, u).subs(u, uj); d2 = sp.diff(B2, u).subs(u, uj)
    print("    corner slopes B1'(uj) = %.6f , B2'(uj) = %.6f , convex corner: %s" % (float(d1), float(d2), d1 > d2))
    # zero of B2 beyond uj
    rts = [r for r in sp.real_roots(sp.Poly(B2, u)) if r > uj]
    uz = min(rts)
    uzero[key] = uz
    uzf = sp.N(uz, 15)
    print("    u_zero (first zero of B2 right of uj) = %s ; ledger states < %s ; cap %s" % (uzf, ledger_val, cap))
    # rounding direction: ledger quoted bound must be >= u_zero
    print("    ledger decimal >= u_zero ? %s  (difference %.3e)" % (ledger_val >= float(uzf), ledger_val - float(uzf)))
    # checks on [0, uj]
    q1c = sp.cancel(Fcore(B1, w) / u)
    q1k = sp.cancel(Fconst(B1) / u**2)
    pos1 = sp.cancel(B1 / u)
    for nm, ex, target in [("Fcore(B1)/u", q1c, -1), ("Fconst(B1)/u^2", q1k, -1), ("B1/u", pos1, 1)]:
        sg, lv = bern_min_sign(ex, sp.Integer(0), uj)
        nroots = sp.Poly(ex, u).count_roots(0, uj)
        print("    on [0,uj]  %-16s Bernstein sign %+d (leaves %s), Sturm roots %d" % (nm, sg, lv, nroots))
        assert sg == target and nroots == 0
    # checks on [uj, uz] (closed); uz algebraic -> use rational upper bracket slightly above uz
    uz_hi = sp.Rational(int(float(uz) * 10**9) + 1, 10**9)
    for nm, ex, target in [("Fcore(B2)", Fcore(B2, w), -1), ("Fconst(B2)", Fconst(B2), -1)]:
        sg, lv = bern_min_sign(ex, uj, uz_hi)
        nroots = sp.Poly(ex, u).count_roots(uj, uz_hi)
        print("    on [uj,uz+]%-16s Bernstein sign %+d (leaves %s), Sturm roots %d" % (nm, sg, lv, nroots))
        assert sg == target and nroots == 0
    sg, lv = bern_min_sign(B2, uj, sp.Rational(int(float(uz) * 10**9), 10**9))
    print("    B2 > 0 on [uj, uz-] : Bernstein sign %+d" % sg)
    # also: admissible-control interval nonempty? (B/w <= 3u) informational
    f_adm = sp.lambdify(u, B1 / w - 3 * u, 'numpy'); f_adm2 = sp.lambdify(u, B2 / w - 3 * u, 'numpy')
    uu1 = np.linspace(1e-6, float(uj), 2000); uu2 = np.linspace(float(uj), float(uz), 2000)
    print("    max(B/w - 3u) on barrier (>0 means no admissible control there): %.4f, %.4f"
          % (np.max(f_adm(uu1)), np.max(f_adm2(uu2))))

# ---------------------------------------------------------------------------
# Part E2: relaxed bang-bang maxima (diagnostic)
# ---------------------------------------------------------------------------
def relaxed_bangbang(w, switch_mode='Q', usw_target=None):
    # core e = v/w from origin with v/u -> 3w (series), switch, then e = 3u to v=0
    def rhs_core(lr, Y):
        uu_, vv = Y
        e = vv / w
        return [e - uu_, 2 * vv - (e + vv) * (uu_ + vv) / (1 - 2 * uu_)]
    def rhs_env(lr, Y):
        uu_, vv = Y
        e = 3 * uu_
        return [e - uu_, 2 * vv - (e + vv) * (uu_ + vv) / (1 - 2 * uu_)]
    # start: small u with v = 3w u (leading order)
    u0 = 1e-7
    Y0 = [u0, 3 * w * u0]
    if switch_mode == 'Q':
        ev = lambda lr, Y: Y[0]**2 + 6 * Y[0] * Y[1] + Y[1]**2 - 2 * Y[1]
    else:
        ev = lambda lr, Y: Y[0] - usw_target
    ev.terminal = True
    sol = solve_ivp(rhs_core, [0, 60], Y0, events=ev, rtol=1e-12, atol=1e-15, max_step=0.05)
    Ysw = sol.y[:, -1]
    ev2 = lambda lr, Y: Y[1]
    ev2.terminal = True; ev2.direction = -1
    sol2 = solve_ivp(rhs_env, [0, 60], Ysw, events=ev2, rtol=1e-12, atol=1e-15, max_step=0.01)
    return float(np.max(sol2.y[0])), Ysw
for w, led in [(1 / 3, 0.330993), (0.5, 0.365429), (1.0, 0.405573)]:
    umax, Ysw = relaxed_bangbang(w)
    # scan alternative single-switch points
    best = umax
    for usw in np.linspace(0.02, 0.38, 73):
        try:
            um, _ = relaxed_bangbang(w, 'u', usw)
            best = max(best, um)
        except Exception:
            pass
    print("[E2] w=%.4f relaxed Q-switch max u = %.8f (ledger diag %s); best single-switch scan %.8f"
          % (w, umax, led, best))

# ---------------------------------------------------------------------------
# Part E1: exact equality identity for P_r = w_Kerr(s) eps
# ---------------------------------------------------------------------------
wKf = sp.lambdify(s, wK_claim, 'numpy')
dwKf = sp.lambdify(s, sp.diff(wK_claim, s), 'numpy')
def star_Pr_wkerr(eps0, R=1.0, prof=lambda r: (1 - r**2)**2, dprof=lambda r: -4 * r * (1 - r**2)):
    # integrate m, y with P_r = wK(s) eps, P_t from TOV
    def rhs(r, Y):
        m, yv = Y
        e = eps0 * prof(r); de = eps0 * dprof(r)
        s2 = 1 - 2 * m / r; sv = math.sqrt(s2)
        w_ = wKf(sv)
        Pr = w_ * e
        mp = 4 * math.pi * r**2 * e
        dsdr = (m / r**2 - mp / r) / sv  # s' = -(m/r)'/s
        dPr = dwKf(sv) * dsdr * e + w_ * de
        Pt = Pr + 0.5 * r * (dPr + (e + Pr) * (m + 4 * math.pi * r**3 * Pr) / (r**2 * s2))
        pe_ = 4 * math.pi * r**2 * e; pr_ = 4 * math.pi * r**2 * Pr; pt_ = 4 * math.pi * r**2 * Pt
        ryp = -yv**2 - 3 * yv + (pe_ + pr_) * yv / s2 + 4 * (pe_ + pt_) / s2
        return [mp, ryp / r]
    r0 = 1e-5
    e0 = eps0
    m0 = 4 * math.pi / 3 * e0 * r0**3
    Pc = (2 / 3) * e0
    y0 = 0.8 * 4 * math.pi * r0**2 * (e0 + Pc)
    sol = solve_ivp(rhs, [r0, R], [m0, y0], rtol=1e-12, atol=1e-16, method='DOP853')
    m, yv = sol.y[:, -1]
    C = m / R
    Ib = yv / (6 + 2 * yv) / C**3
    return C, Ib
for eps0 in [0.05, 0.15, 0.30]:
    C, Ib = star_Pr_wkerr(eps0)
    print("[E1] P_r = w_Kerr(s) eps, eps(r)=eps0(1-r^2)^2: C = %.6f, I/M^3 = %.10f (claim: exactly 4)" % (C, Ib))

# ---------------------------------------------------------------------------
# Part E3: counterexample hunt over monotone isotropic DEC stars
# ---------------------------------------------------------------------------
def iso_star(zones, pc_frac, return_profile=False):
    """zones: list of (r_outer, eps) with eps non-increasing; outermost zone extends
    until p=0.  pc_frac = p_c/eps_c in (0,1].  Returns (C, Ibar, ok) where ok checks p<=eps."""
    eps_list = [z[1] for z in zones]
    radii = [z[0] for z in zones[:-1]]
    pc = pc_frac * eps_list[0]
    def eps_of(r):
        for rb, e in zip(radii, eps_list):
            if r < rb:
                return e
        return eps_list[-1]
    def rhs(r, Y):
        m, p, yv = Y
        e = eps_of(r)
        s2 = 1 - 2 * m / r
        dp = -(e + p) * (m + 4 * math.pi * r**3 * p) / (r**2 * s2)
        pe_ = 4 * math.pi * r**2 * e; pp_ = 4 * math.pi * r**2 * p
        ryp = -yv**2 - 3 * yv + (pe_ + pp_) * yv / s2 + 4 * (pe_ + pp_) / s2
        return [4 * math.pi * r**2 * e, dp, ryp / r]
    r0 = 1e-6
    e0 = eps_list[0]
    Y = [4 * math.pi / 3 * e0 * r0**3, pc, 0.8 * 4 * math.pi * r0**2 * (e0 + pc)]
    ev = lambda r, Y: Y[1]
    ev.terminal = True; ev.direction = -1
    edges = radii + [50.0]
    rcur = r0
    okflag = True
    for k, rb in enumerate(edges):
        sol = solve_ivp(rhs, [rcur, rb], Y, events=ev, rtol=1e-11, atol=1e-14, method='DOP853', max_step=(rb - rcur) / 50)
        # DEC check p <= eps in this zone
        e = eps_list[min(k, len(eps_list) - 1)]
        if np.any(sol.y[1] > e * (1 + 1e-12)):
            okflag = False
        if sol.status == 1:
            m, p, yv = sol.y_events[0][0]
            Rs = sol.t_events[0][0]
            C = m / Rs
            if 1 - 2 * C <= 0:
                return None
            Ib = yv / (6 + 2 * yv) / C**3
            return C, Ib, okflag
        Y = list(sol.y[:, -1]); rcur = rb
        if 1 - 2 * Y[0] / rcur <= 0:
            return None
    return None

# (i) neon-like 2-zone: p = eps core (EOS p = eps, i.e. eps = eps_c - (p_c - p)??) -- we use the
# relaxed-extremal family: core with p=w*eps is not a fixed-eps zone; implement directly.
def two_zone_stiff(r_sw, eps_c=1.0):
    """core EOS p = eps (DEC-saturating) from center to r_sw, then constant density envelope."""
    def rhs_core(r, Y):
        m, p, yv = Y
        e = p  # p = eps
        s2 = 1 - 2 * m / r
        dp = -(e + p) * (m + 4 * math.pi * r**3 * p) / (r**2 * s2)
        pe_ = 4 * math.pi * r**2 * e; pp_ = 4 * math.pi * r**2 * p
        ryp = -yv**2 - 3 * yv + (pe_ + pp_) * yv / s2 + 4 * (pe_ + pp_) / s2
        return [4 * math.pi * r**2 * e, dp, ryp / r]
    r0 = 1e-6
    Y = [4 * math.pi / 3 * eps_c * r0**3, eps_c, 0.8 * 4 * math.pi * r0**2 * 2 * eps_c]
    sol = solve_ivp(rhs_core, [r0, r_sw], Y, rtol=1e-11, atol=1e-14, method='DOP853')
    m, p, yv = sol.y[:, -1]
    e_env = p
    def rhs_env(r, Y):
        m, p, yv = Y
        e = e_env
        s2 = 1 - 2 * m / r
        dp = -(e + p) * (m + 4 * math.pi * r**3 * p) / (r**2 * s2)
        pe_ = 4 * math.pi * r**2 * e; pp_ = 4 * math.pi * r**2 * p
        ryp = -yv**2 - 3 * yv + (pe_ + pp_) * yv / s2 + 4 * (pe_ + pp_) / s2
        return [4 * math.pi * r**2 * e, dp, ryp / r]
    ev = lambda r, Y: Y[1]
    ev.terminal = True; ev.direction = -1
    sol2 = solve_ivp(rhs_env, [r_sw, 100], [m, p, yv], events=ev, rtol=1e-11, atol=1e-14, method='DOP853')
    m, p, yv = sol2.y_events[0][0]
    Rs = sol2.t_events[0][0]
    C = m / Rs
    return C, yv / (6 + 2 * yv) / C**3

best2 = (None, 1e9)
for r_sw in np.linspace(0.05, 1.2, 47):
    C, Ib = two_zone_stiff(r_sw)
    if Ib < best2[1]:
        best2 = (r_sw, Ib, C)
print("[E3] stiff-core + uniform-envelope family: min I/M^3 = %.6f at r_sw = %.3f (C = %.6f)"
      % (best2[1], best2[0], best2[2]))
# uniform density star with p_c = eps (C = 3/8)
r = iso_star([(1.0, 1.0)], 1.0)
print("[E3] uniform density, p_c = eps: C = %.6f , I/M^3 = %.6f" % (r[0], r[1]))
# random / optimised multi-zone piecewise-constant monotone isotropic DEC stars
rng = np.random.default_rng(12345)
def obj(params, nz):
    # params: log density ratios (<=0 cumulative), zone widths, pc_frac
    ratios = np.cumsum(-np.abs(params[:nz - 1]))
    widths = np.abs(params[nz - 1:2 * nz - 2]) + 1e-3
    pcf = 1 / (1 + math.exp(-params[-1]))
    eps = [1.0] + list(np.exp(ratios))
    radii = list(np.cumsum(widths))
    zones = [(radii[i], eps[i]) for i in range(nz - 1)] + [(1e9, eps[-1])]
    out = iso_star(zones, pcf)
    if out is None:
        return 1e3
    C, Ib, ok = out
    if not ok:
        return 1e3
    return Ib
results = []
for nz in [2, 3, 4]:
    bestv = 1e9; bestp = None
    for trial in range(12):
        x0 = np.concatenate([rng.uniform(0, 1.5, nz - 1), rng.uniform(0.05, 0.4, nz - 1), [rng.uniform(-1, 4)]])
        try:
            rres = minimize(obj, x0, args=(nz,), method='Nelder-Mead', options={'maxiter': 400, 'xatol': 1e-6, 'fatol': 1e-8})
            if rres.fun < bestv:
                bestv, bestp = rres.fun, rres.x
        except Exception:
            pass
    results.append((nz, bestv))
    print("[E3] %d-zone piecewise-constant monotone isotropic DEC: min I/M^3 found = %.6f" % (nz, bestv))
assert all(v > 4 for _, v in results) and best2[1] > 4

# ---------------------------------------------------------------------------
# Part F: application numbers
# ---------------------------------------------------------------------------
GM = 1.476625038
for Mv, led in [(2.08, 8.979), (2.35, 10.145)]:
    Rmin = GM * Mv / 0.342058
    Rmin_exact = GM * Mv / float(uzero['1/3'])
    print("[F] M=%.2f: R <= GM/(0.342058 c^2) = %.5f km ; with exact u_zero %.5f km ; ledger %.3f"
          % (Mv, Rmin, Rmin_exact, led))
print("[F] Florides C=0.499 I/M^3 check deferred to t4a12 script")
print("DONE t4a18_kerr_chain.py")
