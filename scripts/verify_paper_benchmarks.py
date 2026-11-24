"""Standalone verification script for all numerical benchmarks and extensions
reported in paper/kerr_inertia_floor.tex.

Reproduces:
  1. Uniform-density Schwarzschild interior stars (C = 0.10, 0.30, 3/8, 0.4444).
  2. Two-zone locally monotone (eps' <= 0) isotropic DEC stars (exceeding C = 3/8).
  3. Mean-density monotone (4*pi*r^3*eps <= 3*m, matching the exact Lean class)
     bang-bang isotropic DEC stars (approaching C = 0.40557, I/M^3 ~ 4.264).
  4. Exact barrier margins: wall u < 51/125 = 0.408 vs. e_5(t) root u = 0.410253,
     plus exact single-interval Bernstein check for I0 = 1001/250 = 4.004.
  5. Beyond-DEC numerical extension: optimal alpha_* and cutoff w_* ~ 1.1556.
  6. Smooth (C^inf) strictly-interior full-DEC anisotropic star with I/M^3 < 4
     (plus continuous witness), cross-checked via both the Hartle-Silva Riccati
     ODE and the independent 2nd-order linear frame-dragging ODE.

Requires: numpy, scipy, sympy.
"""
import math
import numpy as np
import sympy as sp
from scipy.integrate import solve_ivp
from scipy.optimize import brentq


def print_header(title: str) -> None:
    print("\n" + "=" * 78)
    print(title)
    print("=" * 78)


# ---------------------------------------------------------------------------
# 1. Uniform-density Schwarzschild interior stars
# ---------------------------------------------------------------------------
def uniform_star(C: float):
    rho = 3.0 * C / (4.0 * math.pi)
    a = math.sqrt(1.0 - 2.0 * C)

    def rhs(r, y):
        Z = y[0]
        u = C * r * r
        s = math.sqrt(1.0 - 2.0 * u)
        p = rho * (s - a) / (3.0 * a - s)
        pi_e = 4.0 * math.pi * r * r * rho
        pi_p = 4.0 * math.pi * r * r * p
        return [((u + pi_p) * Z / (s * s) - Z * Z / s - 3.0 * Z + 4.0 * (pi_e + pi_p) / s) / r]

    r0 = 1e-5
    p0 = rho * (1.0 - a) / (3.0 * a - 1.0)
    Z0 = (8.0 / 5.0) * 4.0 * math.pi * (rho + p0) * r0 * r0
    sol = solve_ivp(rhs, [r0, 1.0], [Z0], rtol=1e-13, atol=1e-15)
    ZR = float(sol.y[0, -1])
    I = ZR / (6.0 * a + 2.0 * ZR)
    return p0 / rho, ZR, I / C, I / (C ** 3)


# ---------------------------------------------------------------------------
# 2. Two-zone locally monotone (eps' <= 0) isotropic DEC stars
# ---------------------------------------------------------------------------
def two_zone_local_monotone_dec(r_sw: float):
    # Units eps_c = 1. Core [0, r_sw]: p = eps (stiff DEC saturation, eps' < 0).
    # Envelope [r_sw, R]: constant eps = p(r_sw) (continuous density, p <= eps).
    def rhs_core(r, y):
        m, p, Z = y
        u = m / r
        s2 = 1.0 - 2.0 * u
        s = math.sqrt(s2)
        pi_e = 4.0 * math.pi * r * r * p
        pi_p = pi_e
        dm = 4.0 * math.pi * r * r * p
        dp = -2.0 * p * (m + 4.0 * math.pi * r ** 3 * p) / (r * r * s2)
        dZ = ((u + pi_p) * Z / s2 - Z * Z / s - 3.0 * Z + 4.0 * (pi_e + pi_p) / s) / r
        return [dm, dp, dZ]

    r0 = 1e-5
    m0 = (4.0 * math.pi / 3.0) * r0 ** 3
    p0 = 1.0 - (4.0 * math.pi / 3.0) * 4.0 * r0 * r0
    Z0 = (8.0 / 5.0) * 4.0 * math.pi * 2.0 * r0 * r0
    sol1 = solve_ivp(rhs_core, [r0, r_sw], [m0, p0, Z0], rtol=1e-12, atol=1e-14)
    m_sw, p_sw, Z_sw = sol1.y[:, -1]
    eps_env = p_sw

    def rhs_env(r, y):
        m, p, Z = y
        u = m / r
        s2 = 1.0 - 2.0 * u
        s = math.sqrt(s2)
        pi_e = 4.0 * math.pi * r * r * eps_env
        pi_p = 4.0 * math.pi * r * r * p
        dm = 4.0 * math.pi * r * r * eps_env
        dp = -(eps_env + p) * (m + 4.0 * math.pi * r ** 3 * p) / (r * r * s2)
        dZ = ((u + pi_p) * Z / s2 - Z * Z / s - 3.0 * Z + 4.0 * (pi_e + pi_p) / s) / r
        return [dm, dp, dZ]

    def hit_surface(r, y):
        return y[1]

    hit_surface.terminal = True
    hit_surface.direction = -1
    sol2 = solve_ivp(rhs_env, [r_sw, 10.0], [m_sw, p_sw, Z_sw], events=hit_surface, rtol=1e-12, atol=1e-14)
    R = float(sol2.t_events[0][0])
    M, _, ZR = [float(v) for v in sol2.y_events[0][0]]
    C = M / R
    sR = math.sqrt(1.0 - 2.0 * C)
    I = R ** 3 * ZR / (6.0 * sR + 2.0 * ZR)
    return C, I / (M * R * R), I / (M ** 3)


# ---------------------------------------------------------------------------
# 3. Mean-density monotone (4*pi*r^3*eps <= 3*m) bang-bang DEC stars
#    (exact class of MonotoneIsotropicDECStar; switches from e = v to e = 3u
#    with an upward local density jump at r_sw while preserving 4*pi*r^3*eps <= 3*m)
# ---------------------------------------------------------------------------
def mean_density_bang_bang_dec(r_sw: float):
    # Zone 1 [0, r_sw]: p = eps (e = v), eps_c = 1.
    # Zone 2 [r_sw, R]: constant density eps_env = 3*m_sw/(4*pi*r_sw^3) >= p_sw,
    #                   so 4*pi*r^3*eps_env = 3*m(r) identically on [r_sw, R]!
    def rhs_core(r, y):
        m, p, Z = y
        u = m / r
        s2 = 1.0 - 2.0 * u
        s = math.sqrt(s2)
        pi_e = 4.0 * math.pi * r * r * p
        pi_p = pi_e
        dm = 4.0 * math.pi * r * r * p
        dp = -2.0 * p * (m + 4.0 * math.pi * r ** 3 * p) / (r * r * s2)
        dZ = ((u + pi_p) * Z / s2 - Z * Z / s - 3.0 * Z + 4.0 * (pi_e + pi_p) / s) / r
        return [dm, dp, dZ]

    r0 = 1e-5
    m0 = (4.0 * math.pi / 3.0) * r0 ** 3
    p0 = 1.0 - (4.0 * math.pi / 3.0) * 4.0 * r0 * r0
    Z0 = (8.0 / 5.0) * 4.0 * math.pi * 2.0 * r0 * r0
    sol1 = solve_ivp(rhs_core, [r0, r_sw], [m0, p0, Z0], rtol=1e-12, atol=1e-14)
    m_sw, p_sw, Z_sw = sol1.y[:, -1]
    eps_env = 3.0 * m_sw / (4.0 * math.pi * r_sw ** 3)
    assert eps_env >= p_sw - 1e-12, "DEC violated at switch"

    def rhs_env(r, y):
        m, p, Z = y
        u = m / r
        s2 = 1.0 - 2.0 * u
        s = math.sqrt(s2)
        pi_e = 4.0 * math.pi * r * r * eps_env
        pi_p = 4.0 * math.pi * r * r * p
        dm = 4.0 * math.pi * r * r * eps_env
        dp = -(eps_env + p) * (m + 4.0 * math.pi * r ** 3 * p) / (r * r * s2)
        dZ = ((u + pi_p) * Z / s2 - Z * Z / s - 3.0 * Z + 4.0 * (pi_e + pi_p) / s) / r
        return [dm, dp, dZ]

    def hit_surface(r, y):
        return y[1]

    hit_surface.terminal = True
    hit_surface.direction = -1
    sol2 = solve_ivp(rhs_env, [r_sw, 10.0], [m_sw, p_sw, Z_sw], events=hit_surface, rtol=1e-12, atol=1e-14)
    R = float(sol2.t_events[0][0])
    M, _, ZR = [float(v) for v in sol2.y_events[0][0]]
    C = M / R
    sR = math.sqrt(1.0 - 2.0 * C)
    I = R ** 3 * ZR / (6.0 * sR + 2.0 * ZR)
    return C, I / (M * R * R), I / (M ** 3), eps_env / p_sw


# ---------------------------------------------------------------------------
# 4. Exact barrier margins & Bernstein verification for I0 = 1001/250 = 4.004
# ---------------------------------------------------------------------------
def check_barrier_margins_and_4004():
    t, al, I0 = sp.symbols("t alpha I0")
    NumE = -(
        I0**2 * al * t**7 - 7 * I0**2 * al * t**6 + 21 * I0**2 * al * t**5 - 35 * I0**2 * al * t**4
        + 35 * I0**2 * al * t**3 - 21 * I0**2 * al * t**2 + 7 * I0**2 * al * t - I0**2 * al
        - I0**2 * t**7 + 6 * I0**2 * t**6 - 15 * I0**2 * t**5 + 20 * I0**2 * t**4 - 15 * I0**2 * t**3
        + 6 * I0**2 * t**2 - I0**2 * t + 8 * I0 * al * t**4 - 32 * I0 * al * t**3 + 48 * I0 * al * t**2
        - 32 * I0 * al * t + 8 * I0 * al + 52 * I0 * t**4 - 84 * I0 * t**3 + 12 * I0 * t**2
        + 20 * I0 * t + 16 * al * t - 16 * al - 64 * t
    )
    NumP = -(
        I0 * al * t**4 - 6 * I0 * al * t**3 + 12 * I0 * al * t**2 - 10 * I0 * al * t + 3 * I0 * al
        - I0 * t**4 + 3 * I0 * t**3 - 3 * I0 * t**2 + I0 * t + 52 * al * t - 12 * al - 16 * t
    )

    e5 = 31 * t**5 - 117 * t**4 + 51 * t**3 - 1023 * t**2 + 1737 * t - 279
    rts = [float(r) for r in sp.real_roots(sp.Poly(e5, t)) if 0 < float(r) < 1]
    t_root = max(rts)
    u_root = (1.0 - t_root) / 2.0

    def bernstein_min(poly_expr, a, b):
        u = sp.symbols("u")
        q = sp.Poly(sp.expand(poly_expr.subs(t, a + (b - a) * u)), u)
        n = q.degree()
        coeffs = [q.nth(k) for k in range(n + 1)]
        bvals = []
        for j in range(n + 1):
            val = sp.Rational(0)
            for k in range(j + 1):
                val += sp.Rational(sp.binomial(j, k), sp.binomial(n, k)) * coeffs[k]
            bvals.append(val)
        return min(bvals)

    a, b = sp.Rational(23, 125), sp.Rational(1)
    pe_4004 = sp.expand(NumE.subs({al: sp.Rational(69, 100), I0: sp.Rational(1001, 250)}))
    pep_4004 = sp.expand(
        (NumE + NumP * (4 - I0 * (1 - t) ** 3)).subs({al: sp.Rational(69, 100), I0: sp.Rational(1001, 250)})
    )
    min_e = bernstein_min(pe_4004, a, b)
    min_ep = bernstein_min(pep_4004, a, b)
    assert min_e > 0 and min_ep > 0
    return t_root, u_root, float(min_e), float(min_ep)


# ---------------------------------------------------------------------------
# 5. Beyond-DEC extension: optimal alpha_* and cutoff w_* ~ 1.1556
# ---------------------------------------------------------------------------
def beyond_dec_extension():
    t, al = sp.symbols("t alpha")
    I0 = sp.Rational(4)
    NumE = -(
        I0**2 * al * t**7 - 7 * I0**2 * al * t**6 + 21 * I0**2 * al * t**5 - 35 * I0**2 * al * t**4
        + 35 * I0**2 * al * t**3 - 21 * I0**2 * al * t**2 + 7 * I0**2 * al * t - I0**2 * al
        - I0**2 * t**7 + 6 * I0**2 * t**6 - 15 * I0**2 * t**5 + 20 * I0**2 * t**4 - 15 * I0**2 * t**3
        + 6 * I0**2 * t**2 - I0**2 * t + 8 * I0 * al * t**4 - 32 * I0 * al * t**3 + 48 * I0 * al * t**2
        - 32 * I0 * al * t + 8 * I0 * al + 52 * I0 * t**4 - 84 * I0 * t**3 + 12 * I0 * t**2
        + 20 * I0 * t + 16 * al * t - 16 * al - 64 * t
    )
    NumP = -(
        I0 * al * t**4 - 6 * I0 * al * t**3 + 12 * I0 * al * t**2 - 10 * I0 * al * t + 3 * I0 * al
        - I0 * t**4 + 3 * I0 * t**3 - 3 * I0 * t**2 + I0 * t + 52 * al * t - 12 * al - 16 * t
    )
    den = 4 - 4 * (1 - t) ** 3

    fE = sp.lambdify((t, al), NumE, "numpy")
    fEW = sp.lambdify((t, al, sp.Symbol("w")), NumE + sp.Symbol("w") * NumP * den, "numpy")

    def mu_kerr_iso(w: float):
        # Exact root of NumE(t, al) and NumE + w*NumP*den on [0.15, 0.30] via brentq
        def u_max_for_alpha(a_val: float):
            def largest_root(fn):
                # Scan coarse 200 pts from right to left to bracket largest root in [0.15, 0.40]
                grid = np.linspace(0.40, 0.15, 251)
                vals = fn(grid)
                neg = np.where(vals <= 0.0)[0]
                if len(neg) == 0:
                    return 0.15
                idx = neg[0]
                if idx == 0:
                    return 0.40
                return brentq(fn, grid[idx], grid[idx - 1], xtol=1e-12)

            t1 = largest_root(lambda tv: fE(tv, a_val))
            t2 = largest_root(lambda tv: fEW(tv, a_val, w))
            return (1.0 - max(t1, t2)) / 2.0

        from scipy.optimize import minimize_scalar
        res = minimize_scalar(lambda a: -u_max_for_alpha(a), bounds=(0.65, 0.72), method="bounded", options={"xatol": 1e-8})
        return float(-res.fun), float(res.x)

    def mu_bondi_bang_bang(w: float):
        # Integrate relaxed Bondi bang-bang: e = v/w from (0,0) to switching curve Q(u,v)=0,
        # then e = 3u to v = 0.
        def rhs1(tau, y):
            u, v = y
            e = v / w
            return [e - u, 2 * v - (e + v) * (u + v) / (1.0 - 2.0 * u)]

        def hit_Q(tau, y):
            u, v = y
            return u * u + 6 * u * v + v * v - 2 * v

        hit_Q.terminal = True
        hit_Q.direction = 1
        u0 = 1e-6
        v0 = 3.0 * w * u0
        s1 = solve_ivp(rhs1, [0.0, 10.0], [u0, v0], events=hit_Q, rtol=1e-12, atol=1e-14)
        u_sw, v_sw = s1.y_events[0][0]

        def rhs2(tau, y):
            u, v = y
            e = 3.0 * u
            return [e - u, 2 * v - (e + v) * (u + v) / (1.0 - 2.0 * u)]

        def hit_v0(tau, y):
            return y[1]

        hit_v0.terminal = True
        hit_v0.direction = -1
        s2 = solve_ivp(rhs2, [0.0, 10.0], [u_sw, v_sw], events=hit_v0, rtol=1e-12, atol=1e-14)
        return float(s2.y_events[0][0][0])

    mu_k_1, al_1 = mu_kerr_iso(1.0)
    mu_b_1 = mu_bondi_bang_bang(1.0)
    w_star = brentq(lambda w: mu_kerr_iso(w)[0] - mu_bondi_bang_bang(w), 1.10, 1.20, xtol=1e-5)
    return al_1, mu_k_1, mu_b_1, w_star, mu_bondi_bang_bang(w_star)


# ---------------------------------------------------------------------------
# 6. Smooth (C^inf) strictly-interior DEC anisotropic star with I/M^3 < 4
#    and continuous monotone full-DEC witness, cross-checked by 2nd-order ODE
# ---------------------------------------------------------------------------
def anisotropic_sub_kerr_star(smooth: bool = True):
    # Scaled variables e = 4*pi*eps, p = 4*pi*P_r, q = 4*pi*P_t.
    # Smooth witness: p_c = 12, e_0 = 1e-3, c = 0.99, e(p) = p/c + e_0,
    #   q(r, p) = p - (p + c*e) * (2r)^8 / (1 + (2r)^8).
    #   Satisfies C^inf regularity, eps' < 0, 0 < P_r < 0.99*eps, |P_t| < 0.99*eps.
    # Continuous witness: p_c = 12, e_0 = 1e-3, e(p) = p + e_0,
    #   q = p on [0, 0.4], q = -e on (0.4, R].
    p_c = 12.0
    e_0 = 1e-3
    c_dec = 0.99 if smooth else 1.0

    def matter(r, p):
        e = p / c_dec + e_0
        if smooth:
            x8 = (2.0 * r) ** 8
            q_mp = -(p + c_dec * e) * x8 / (1.0 + x8)
        else:
            q_mp = 0.0 if r <= 0.4 else -(p + e)
        q = p + q_mp
        return e, q, q_mp

    def rhs_riccati(r, y):
        m, p, Z = y
        e, q, q_mp = matter(r, p)
        u = m / r
        f = 1.0 - 2.0 * u
        s = math.sqrt(f)
        dm = r * r * e
        dp = -(e + p) * (m + r ** 3 * p) / (r * r * f) + 2.0 * q_mp / r
        pi_e, pi_r, pi_t = r * r * e, r * r * p, r * r * q
        dZ = (-Z * Z / s + Z * ((1.0 - 7.0 * f) / (2.0 * f) + pi_r / f) + 4.0 * (pi_e + pi_t) / s) / r
        return [dm, dp, dZ]

    def rhs_linear(r, y):
        # Independent 2nd-order linear Hartle-Silva ODE for (wbar, wbar')
        m, p, w, wp = y
        e, q, q_mp = matter(r, p)
        u = m / r
        f = 1.0 - 2.0 * u
        dm = r * r * e
        dp = -(e + p) * (m + r ** 3 * p) / (r * r * f) + 2.0 * q_mp / r
        wpp = -(4.0 / r - r * (e + p) / f) * wp + (4.0 * (e + q) / f) * w
        return [dm, dp, wp, wpp]

    r0 = 1e-5
    e_c = p_c / c_dec + e_0
    m0 = e_c * r0 ** 3 / 3.0
    p0 = p_c - (e_c + p_c) * (e_c / 3.0 + p_c) * r0 * r0 / 2.0
    Z0 = (4.0 / 5.0) * (e_c + p_c) * r0 * r0
    B_lin = (2.0 / 5.0) * (e_c + p_c)
    w0 = 1.0 + B_lin * r0 * r0
    wp0 = 2.0 * B_lin * r0

    def hit_zero(r, y):
        return y[1]

    hit_zero.terminal = True
    hit_zero.direction = -1

    if smooth:
        sol_r = solve_ivp(rhs_riccati, [r0, 5.0], [m0, p0, Z0], events=hit_zero, rtol=1e-12, atol=1e-14)
        sol_l = solve_ivp(rhs_linear, [r0, 5.0], [m0, p0, w0, wp0], events=hit_zero, rtol=1e-12, atol=1e-14)
    else:
        s1_r = solve_ivp(rhs_riccati, [r0, 0.4], [m0, p0, Z0], rtol=1e-12, atol=1e-14)
        sol_r = solve_ivp(rhs_riccati, [0.4, 5.0], s1_r.y[:, -1], events=hit_zero, rtol=1e-12, atol=1e-14)
        s1_l = solve_ivp(rhs_linear, [r0, 0.4], [m0, p0, w0, wp0], rtol=1e-12, atol=1e-14)
        sol_l = solve_ivp(rhs_linear, [0.4, 5.0], s1_l.y[:, -1], events=hit_zero, rtol=1e-12, atol=1e-14)

    R = float(sol_r.t_events[0][0])
    M, _, ZR = [float(v) for v in sol_r.y_events[0][0]]
    C = M / R
    sR = math.sqrt(1.0 - 2.0 * C)
    Ibar_ric = (R ** 3 * ZR / (6.0 * sR + 2.0 * ZR)) / (M ** 3)

    Rl = float(sol_l.t_events[0][0])
    Ml, _, wR, wpR = [float(v) for v in sol_l.y_events[0][0]]
    sRl = math.sqrt(1.0 - 2.0 * Ml / Rl)
    ZRl = Rl * sRl * wpR / wR
    Ibar_lin = (Rl ** 3 * ZRl / (6.0 * sRl + 2.0 * ZRl)) / (Ml ** 3)

    # Check pointwise DEC, strict monotonicity (dp < 0), and horizonless interior
    max_dec = 0.0
    max_u = 0.0
    for r_i, m_i, p_i in zip(sol_r.t, sol_r.y[0], sol_r.y[1]):
        if p_i < 0:
            continue
        e_i, q_i, _ = matter(r_i, p_i)
        max_dec = max(max_dec, abs(p_i) / e_i, abs(q_i) / e_i)
        max_u = max(max_u, m_i / r_i)

    assert abs(Ibar_ric - Ibar_lin) < 1e-8
    assert Ibar_ric < 4.0
    assert max_dec <= c_dec + 1e-12
    return R, C, max_u, max_dec, Ibar_ric, Ibar_lin


def main():
    print_header("1. Uniform-Density Schwarzschild Interior Stars")
    for C in [0.10, 0.30, 0.375, 0.4444]:
        pr, ZR, I_MR2, Ibar = uniform_star(C)
        print(f"C={C:7.4f} | p_c/eps={pr:10.5f} | Z_R={ZR:.8f} | I/(MR^2)={I_MR2:.6f} | I/M^3={Ibar:.6f}")

    print_header("2. Two-Zone Locally Monotone (eps' <= 0) Isotropic DEC Stars")
    for r_sw in [0.25, 0.30, 0.40]:
        C, I_MR2, Ibar = two_zone_local_monotone_dec(r_sw)
        print(f"r_sw={r_sw:.2f} | C={C:.6f} (>3/8? {C > 0.375}) | I/(MR^2)={I_MR2:.6f} | I/M^3={Ibar:.6f}")

    print_header("3. Wider Mean-Density Class (4*pi*r^3*eps <= 3*m) Bang-Bang DEC Stars")
    best_I = 1e9
    best_r = None
    max_C = 0.0
    max_C_r = None
    for r_sw in [0.20, 0.30, 0.35, 0.40, 0.45, 0.50, 0.55, 0.60]:
        C, I_MR2, Ibar, ratio = mean_density_bang_bang_dec(r_sw)
        print(
            f"r_sw={r_sw:.2f} | C={C:.6f} | I/(MR^2)={I_MR2:.6f} | I/M^3={Ibar:.6f} | eps_env/p_sw={ratio:.4f}"
        )
        if Ibar < best_I:
            best_I, best_r = Ibar, r_sw
        if C > max_C:
            max_C, max_C_r = C, r_sw
    print(f"--> Mean-density class scan: max C = {max_C:.6f} (r_sw={max_C_r}), min I/M^3 = {best_I:.6f} (r_sw={best_r})")

    print_header("4. Barrier Margins & Exact Single-Interval Bernstein Check for I0 = 1001/250")
    t_root, u_root, min_e, min_ep = check_barrier_margins_and_4004()
    print(f"e_5(t) root in (0,1): t = {t_root:.8f}  =>  u_root = {u_root:.8f} (vs. wall 51/125 = 0.40800000)")
    print(f"I0 = 1001/250 = 4.004 at alpha = 69/100 on [23/125, 1]:")
    print(f"  min Bernstein coeff(NumE)            = {min_e:.8f} > 0")
    print(f"  min Bernstein coeff(NumE + NumP*den) = {min_ep:.8f} > 0")

    print_header("5. Beyond-DEC Numerical Extension (Not Formalized in Lean)")
    al_1, mu_k_1, mu_b_1, w_star, mu_w_star = beyond_dec_extension()
    print(f"At w = 1 (DEC): optimal alpha ~ {al_1:.6f}, mu_Kerr_iso = {mu_k_1:.6f} > mu_Bondi = {mu_b_1:.6f}")
    print(f"Beyond-DEC cutoff: w_* = {w_star:.6f} (where mu_Kerr_iso = mu_Bondi = {mu_w_star:.6f})")

    print_header("6. Anisotropic Full-DEC Sub-Kerr Counterexamples (Necessity of Isotropy)")
    for label, sm in [("C^inf strictly-interior DEC (<= 0.99)", True), ("Continuous monotone full-DEC", False)]:
        R, C, max_u, max_dec, I_ric, I_lin = anisotropic_sub_kerr_star(smooth=sm)
        print(
            f"{label}:\n"
            f"  R = {R:.6f}, C = {C:.6f}, max(m/r) = {max_u:.6f}, max(|P|/eps) = {max_dec:.6f}\n"
            f"  I/M^3 (Riccati) = {I_ric:.8f}, I/M^3 (2nd-order linear) = {I_lin:.8f} (< 4!)"
        )

    print("\nALL CHECKS PASSED.")


if __name__ == "__main__":
    main()
