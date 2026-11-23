# T4A-18 statement and physics audit

**DEFECT FOUND — the Lean theorem omits interior density jumps explicitly included in the source theorem statement.** The strict inertia floor is proved for the encoded class. Its equations and surface observable agree with first-order, rigidly rotating perfect-fluid GR, and the class has an analytic physical witness.

## Scope defect and repair

At an ordinary interface of radius $b>0$ with $\varepsilon_->\varepsilon_+$, the continuous enclosed mass has one-sided derivatives $4\pi b^2\varepsilon_-$ and $4\pi b^2\varepsilon_+$. No choice of $\varepsilon(b)$ makes `hasDerivAt_m` true. Even the literal `AntitoneOn` theorem inherits that field. The source theorem expressly includes ordinary matched jumps. [Lean fields (initial pass, commit `44df754`)](NaturalMechanics/T4A18_KerrInertia.lean)

Such an interface is compatible with DEC. For example, set $R=1$, take density $2\rho$ inside $b=1/2$ and $\rho=3/(800\pi)$ outside the core up to the surface. Then $m\le r^3/100$. Integrate TOV inwards with continuous pressure and $p(1)=0$. While $0\le p\le\rho$, the equation gives $0\le-p'\le(15/196)\rho r$ on each layer. Hence $p\le(15/392)\rho$ and the solution continues to the centre within DEC. The mass derivative fails precisely at the interior interface even when the surface is treated as interior data.

**Required fix.** Qualify the formalization claim as requiring pointwise derivatives of the interior mass, pressure and Hartle variable. To recover the jump-inclusive claim, prove a version with piecewise or almost-everywhere equations, matching $m,p,\bar\omega,r^4j\bar\omega'$ across interfaces, and justify barrier propagation there. A one-sided derivative at the outer surface alone leaves the interior defect in place.

## Equations and theorem statement

In $G=c=1$, write the static metric as $-N^2dt^2+s^{-2}dr^2+r^2d\Omega^2$, with $s^2=1-2m/r$. The mixed Einstein components give $8\pi\varepsilon=[r(1-s^2)]'/r^2$ and $8\pi p=2s^2N'/(rN)-(1-s^2)/r^2$. Radial stress conservation gives $p'=-(\varepsilon+p)N'/N$. Substitution yields exactly

$$
m'=4\pi r^2\varepsilon,\qquad
N'/N=(m+4\pi r^3p)/(r^2s^2),\qquad
p'=-(\varepsilon+p)(m+4\pi r^3p)/(r^2s^2).
$$

Set $u=m/r$, $e=4\pi r^2\varepsilon$, $v=4\pi r^2p$, $w=\bar\omega$, $j=s/N$. Then $rs'=(u-e)/s$, $rv'=2v-(e+v)(u+v)/s^2$ and $rj'/j=-(e+v)/s^2$. Expanding $(r^4jw')'+4r^3j'w=0$ for $y=rw'/w$ gives $ry'=-y^2-3y-(y+4)rj'/j$. Thus $Z=sy$ obeys

$$
rZ'=(u+v)Z/s^2-Z^2/s-3Z+4(e+v)/s.
$$

This checks every term in `rhsS`, `rhsP`, `rhsZ` and the outer division by $r$ in `hasDerivAt_Z`. The structure takes this reduced equation as input. [Hartle (1967), §IV, equations 46–48](https://doi.org/10.1086/149400)

In vacuum $j=1$ and $w=\Omega-2J/r^3$, with $J=I\Omega$. Matching $w,w'$ gives $Z_R=6s_R I/(R^3-2I)$ and $I=R^3Z_R/(6s_R+2Z_R)$, as defined. Substitution of $I=4M^3$, $u_R=M/R$, gives $Z_c=24s_Ru_R^3/(1-8u_R^3)$. The proof uses $p(R)=0$ to obtain $Z_R>Z_c\ge0$ and proves the denominator positive before multiplying. The strict wall $u<51/125$ on $(0,R]$ is a conclusion. Neither the wall nor the inertia floor is a field. The Kerr comparator is the zero-spin limit of $J/\Omega_H$.

## Non-vacuity, field by field

Choose $R=1$, $M=C=1/10$, $\rho=3C/(4\pi)$, $a=\sqrt{1-2C}$ and $s=\sqrt{1-2Cr^2}$. The exact Schwarzschild interior has $N=(3a-s)/2$. [Homogeneous slow-rotation solution, Petroff (2007)](https://arxiv.org/pdf/gr-qc/0701081)

| Lean fields or hypotheses | Check on the same star |
|---|---|
| `R, m, ε, R_pos, m_zero, M_pos, hasDerivAt_m` | $m=Cr^3$, $\varepsilon=\rho$. Differentiation gives $3Cr^2=4\pi r^2\rho$. Both endpoint masses and $R>0$ follow. |
| `s_pos, center_u` | $s\ge a>0$ on $[0,1]$ and $m/r=Cr^2\to0$ from the right. |
| `p, hasDerivAt_p, p_surface` | $p=\rho(s-a)/(3a-s)$ vanishes at $1$. Direct differentiation gives $p'=-4\rho aCr/[s(3a-s)^2]$, exactly the TOV value. |
| `p_nonneg, p_le_ε, center_p` | $0\le p/\rho\le(1-a)/(3a-1)<1$ since $a>1/2$. Pressure is positive for $r<1$ and finite at zero, so $4\pi r^2p\to0$. |
| `mean_density`, literal `AntitoneOn` | $4\pi r^3\rho=3m$ identically and $\varepsilon$ is constant. In general the field says $(m/r^3)'\le0$ for positive radii. The literal theorem derives the field from non-increasing $\varepsilon$ on $(0,R]$. |
| `Z, hasDerivAt_Z, Z_zero, center_Z` | Take the regular Hartle solution below and set $Z=rsw'/w$, $Z(0)=0$. It is pole-free, satisfies the derived Riccati equation and tends to zero as $O(r^2)$. |

For existence, $j=2s/(3a-s)$ is positive, even and analytic near zero. The expanded Hartle equation has indicial roots $0,-3$. The regular Frobenius solution is $w=1+Br^2+O(r^4)$ with $B=8\pi(\rho+p(0))/5$. Ordinary linear ODE continuation reaches $R$ since $j>0$ there and throughout the interior. Also $j'<0$ for $r>0$. Integrating from the regular centre gives $r^4jw'=\int_0^r -4t^3 j'(t)w(t)\,dt$. While $w>0$, this is strictly positive, so $w$ increases from one and cannot have a first zero. Thus $Z>0$ throughout $(0,R]$ and $6s_R+2Z_R>0$ independently of the audited theorem. As a numerical cross-check, RK4 on the linear Hartle equation, started at $r=h$ from the displayed series with $h=1/1000,1/2000,1/4000$, gave $Z_R=0.25824624$ and $I/M^3=43.896617$ from $J=R^4w'_R/6$, $\Omega=w_R+Rw'_R/3$. This gives a mathematical witness outside Lean. The file contains no formal inhabitance proof.

**Endpoint convention.** All three derivative fields use ordinary two-sided `HasDerivAt` on `Ioc 0 R`. At $R$ use a smooth continuation of the interior formulas a little past $R$ and assign arbitrary values farther away to obtain Lean's total real functions. The physical vacuum matching uses the surface values and $w'_R$. The physically glued mass and pressure have different exterior slopes when $\varepsilon(R^-)>0$. At zero only the listed values and right limits are required. The weighted limits do not themselves impose finite continuous central density and pressure. The closed intervals in the comparison arguments impose no centre ODE.

## Build and trust

Clean branch `lean4/t4a18-kerr-inertia` at `44df754`, parent `7447ebb`. Lean 4.36.0. With Elan on `PATH`, `lake build` in `lean4/` exited 0 with module-system warnings. A separate `lake env lean NaturalMechanics/T4A18_KerrInertia.lean` re-elaborated the source and exited 0. The scan for `sorry|admit|axiom |unsafe|implemented_by|native_decide|extern` across `NaturalMechanics/` returned no executable occurrences. The independent run's `#print axioms` reported exactly `[propext, Classical.choice, Quot.sound]` for each of `t4a18_unconditional_kerr_inertia_floor`, `t4a18_kerr_inertia_floor_of_antitone` and `compactness_wall`.

## Resolution of the scope defect (post-audit implementation)

*Added by the implementation pass. The audit text above is unchanged.*

The fix follows the audit's "Required fix": the equations hold pointwise off finitely many interfaces, the junction quantities are matched, and the barrier argument is shown to propagate across the interfaces.

- **New base class** [`PiecewiseRegularIsotropicDECStar`](NaturalMechanics/T4A18_KerrInertia.lean#L694) has a field `jumps : Finset ℝ`. It requires `ContinuousOn` of `m`, `p` and `Z` on `(0, R]`, which encodes matching of $m$, $p$, $\bar\omega$ and $r^4 j\bar\omega'$, so $Z = rs\bar\omega'/\bar\omega$ is continuous. The TOV and Hartle `HasDerivAt` fields hold only on `(0, R] \ jumps`. The surface $R$ may itself be listed as a jump, so no smooth continuation past $R$ is needed. `MonotoneIsotropicDECStar` now extends this class. The old smooth `RegularIsotropicDECStar` is unchanged and is the case `jumps = ∅` via [`toPiecewise`](NaturalMechanics/T4A18_KerrInertia.lean#L788).
- **Monotonicity across jumps.** [`monotoneOn_Icc_of_deriv_nonneg_off`](NaturalMechanics/T4A18_KerrInertia.lean#L169) inducts on the finite exceptional set: split at an interior exceptional point, then glue at that point using continuity. It is used for `m/r³` antitone (`m_pos`) and for [`mean_density_of_antitone`](NaturalMechanics/T4A18_KerrInertia.lean#L845) (`AntitoneOn ε → 4π r³ ε ≤ 3m`).
- **Barrier crossing at a jump.** [`pos_left_of_eventually_deriv_neg`](NaturalMechanics/T4A18_KerrInertia.lean#L146) needs a negative derivative only on a punctured left neighbourhood of the touching point. The Part B Bondi barrier ([`piece_left`](NaturalMechanics/T4A18_KerrInertia.lean#L1018)) and the Part C exponential barrier ([`D_surface_pos`](NaturalMechanics/T4A18_KerrInertia.lean#L1428)) both check that inequality on the left of the touching point. There the strict inequalities persist by continuity of $(u, v)$, $D$ and $L/r$. `kernelB` is linear in the density control, which may jump, and is now stated for an arbitrary state $(u,v)$. The centre analysis (C1–C3') runs on an initial segment `(0, a]` that contains no interfaces.
- **Theorems now covering the jump-inclusive class:** `MonotoneIsotropicDECStar.compactness_wall`, `MonotoneIsotropicDECStar.t4a18_unconditional_kerr_inertia_floor`, [`t4a18_kerr_inertia_floor_of_antitone_piecewise`](NaturalMechanics/T4A18_KerrInertia.lean#L1548), `compactness_wall_of_antitone_piecewise`. The smooth `t4a18_kerr_inertia_floor_of_antitone` keeps its statement and is a corollary.
- **Build and trust:** `lake build` exits 0. The scan finds no `sorry`, `admit`, `axiom `, `unsafe` or `native_decide`. `#print axioms` reports only `[propext, Classical.choice, Quot.sound]` for all of the above and for `mean_density_of_antitone`.
- **Not formalized:** there is still no formal inhabitance proof in Lean. The two-layer DEC star described above remains a witness outside Lean for the jump case.

## Final Re-Audit Sign-Off (commit `9f1203a`)

**PASS (CLEAN).** The upgrade closes the reported scope defect for finitely many ordinary matched jumps, including a surface density jump. The two-layer star above satisfies every field of `PiecewiseRegularIsotropicDECStar` and the literal antitonicity hypothesis.

- Take `jumps = {1/2, 1}`, with density $2\rho$ below $1/2$, $\rho$ from $1/2$ to the surface, and zero at and beyond $R=1$. This choice is antitone on $(0,1]$. Integrating the density gives continuous mass with $m(0)=0$, $m(1)>0$ and $m/r\le r^2/100$, so $s>0$ and $m/r\to0$ at the centre. The matched TOV pressure is continuous, vanishes at the surface and satisfies $0\le p\le15\rho/392$ by the bound above. Thus DEC holds even at the assigned jump values, and $4\pi r^2p\to0$.
- Normalize the regular core Hartle solution by $w(0)=1$ and match $w$ and $F=r^4jw'$ at $1/2$. On either open layer $j'<0$, so $F'=-4r^3j'w>0$ while $w>0$. Since $F(0)=0$, $w$ increases and stays positive through the surface. With $j=s/N>0$ continuous, $Z=sF/(r^3jw)$ is continuous at the interface and has a finite left limit equal to its surface value. Core regularity gives $Z=O(r^2)$ and $Z(0)=0$. The three derivative fields hold on the open layers. This witness is mathematical, outside Lean.
- The monotonicity proof joins continuous values at each exceptional radius. At a first barrier contact, the derivative has the required strict negative sign immediately to its left, where finiteness excludes other jumps. This covers contact at $R$ using only interior data. The same finiteness supplies the initial jump-free interval at the centre.
- At review, `git log -2` showed `9f1203a` over `251ffc3`. With Elan on `PATH`, `lake build` exited 0. A separate import and `#print axioms` returned exactly `[propext, Classical.choice, Quot.sound]` for `t4a18_unconditional_kerr_inertia_floor`, `t4a18_kerr_inertia_floor_of_antitone_piecewise` and `compactness_wall_of_antitone_piecewise`. The requested token scan found zero matches in the theorem file.
