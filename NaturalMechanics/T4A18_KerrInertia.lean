import Mathlib

/-!
# T4A-18: the unconditional Kerr inertia floor `I > 4 M³` (N40 ⟹ N41)

Formalisation of the Sprint-2 (5-for-5 blind-audited) flagship theorem `T4A-18` of
`branches/track-4a-continuum-bounds/LEDGER.md`, following the exact proof chain of
`branches/track-4a-continuum-bounds/audit/sprint2-opus/t4a18_kerr_chain.py`.

Units `G = c = 1`. Notation along the star: `u = m/r`, `π_e = 4π r² ε`, `π_p = 4π r² p`,
`s = √(1 − 2u)`, `Z = r s ω̄'/ω̄`, `W_α = Z − 2α π_p / s`, and the Schwarzschild vacuum curve
`Z_c(s) = 3 Ī₀ s (1 − s²)³ / (4 − Ī₀ (1 − s²)³)` (the value of `Z` at the surface of a star of
compactness `(1 − s²)/2` with `I/M³ = Ī₀`).

* **General comparison lemmas** — `first_crossing` (strict barrier / first-crossing argument via
  `sInf` of a closed set) and `no_rise_to_left` (monotonicity on the last excursion via `sSup`).
* **Part A** — `partA`: the exact shifted Hartle–TOV Riccati identity
  `r (W_α − Z_c)' = L · (W_α − Z_c) + c_e π_e + c_p π_p + c_pp π_p²` for *arbitrary* `α, Ī₀`;
  in particular the constant term and the `π_e π_p` cross term vanish identically
  (`partA_const_vanishes`, `partA_cross_vanishes`).
* **Part B** — `MonotoneIsotropicDECStar.compactness_wall`: `m(r)/r < 51/125` on `(0, R]`, from the
  exact two-piece Bondi barrier `(B₁, B₂)` (`u_j = 49/200`), with all polynomial sign conditions
  discharged by exact rational Bernstein certificates (no floating point).
* **Part C** — at `α = 69/100`, `Ī₀ = 4`: `c_e > 0` and `c_e + c_p > 0` on `s² ∈ [23/125, 1]`
  (exact Bernstein certificates for `e₅`, `s₄`), a centre analysis giving `W − Z_c > 0` at some
  interior point, an exponential strict barrier up to the surface, and finally (`p(R) = 0`)
  `Z(R) > Z_c(s_R)`, i.e. `I > 4 M³`:
  `MonotoneIsotropicDECStar.t4a18_unconditional_kerr_inertia_floor`, and the literal
  non-increasing-density versions `t4a18_kerr_inertia_floor_of_antitone_piecewise` and
  `t4a18_kerr_inertia_floor_of_antitone`.
  The barrier argument is proved once for a general level `Ī₀` satisfying the sign conditions
  `KerrBarrierLevel` (`kerr_inertia_gt_of_level`) and specialised to `Ī₀ = 4`.
* **Uniform gap** — the same barrier closes at `Ī₀ = 1001/250`: the polynomials `e7`, `s7`
  (degree 7) have strictly positive exact Bernstein coefficients on `[23/125, 1]` without
  subdivision, and `4 − (1001/250)(1 − t)³ ≥ 4 − (1001/250)(102/125)³ > 0` there. Hence
  `I > (1001/250) M³`: `I/M³ > 4.004` for every star, so `inf I/M³ ≥ 4.004 > 4` over the class:
  `MonotoneIsotropicDECStar.t4a18_uniform_kerr_inertia_gap`,
  `t4a18_uniform_kerr_inertia_gap_of_antitone_piecewise` and
  `t4a18_uniform_kerr_inertia_gap_of_antitone`.

**Scope: piecewise-smooth stars (ordinary interior density jumps).** As in `LEDGER.md` (N40/N41),
the star class `PiecewiseRegularIsotropicDECStar` allows a finite set `jumps : Finset ℝ` of
interface radii (first-order phase transitions, and optionally the surface): `m, p, Z` are only
required to be continuous on `(0, R]`, and the TOV/Hartle equations hold pointwise on
`(0, R] \ jumps` (at a density jump `m` has unequal one-sided derivatives, so `HasDerivAt m`
fails there). The barrier arguments propagate across every interface: monotonicity statements
use finite-subinterval induction (`monotoneOn_Icc_of_deriv_nonneg_off`), and every
first-crossing step uses the flow only on a punctured left neighbourhood of the touching point
(`pos_left_of_eventually_deriv_neg`), where the strict barrier inequalities persist by
continuity. The smooth class `RegularIsotropicDECStar` is the special case `jumps = ∅`
(`RegularIsotropicDECStar.toPiecewise`).

Zero proof gaps and zero custom axioms; the `#print` audit at the end of the file lists only
the three standard Lean axioms.
-/

open Set Filter Topology Real

namespace NaturalMechanics.T4A18

/-! ## General one-dimensional comparison lemmas -/

lemma pos_left_of_deriv_neg {f : ℝ → ℝ} {x d : ℝ} (hf : HasDerivAt f d x) (hd : d < 0)
    (h0 : f x = 0) : ∀ᶠ y in 𝓝[<] x, 0 < f y := by
  have h1 : Tendsto (slope f x) (𝓝[<] x) (𝓝 d) :=
    (hasDerivWithinAt_iff_tendsto_slope' (lt_irrefl x)).1 hf.hasDerivWithinAt
  have h2 : ∀ᶠ y in 𝓝[<] x, slope f x y < 0 := h1.eventually (gt_mem_nhds hd)
  filter_upwards [h2, self_mem_nhdsWithin] with y hy hyx
  rw [slope_def_field, h0, sub_zero] at hy
  have hyx' : y - x < 0 := sub_neg.2 hyx
  rcases div_neg_iff.1 hy with h | h
  · exact h.1
  · exact absurd h.2 (not_lt.2 hyx'.le)

lemma first_crossing {f : ℝ → ℝ} {a b : ℝ} (hc : ContinuousOn f (Icc a b)) (ha : f a < 0)
    (hz : ∀ x ∈ Ioc a b, f x = 0 → ∀ᶠ y in 𝓝[<] x, 0 < f y) : ∀ x ∈ Icc a b, f x < 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨x₀, hx₀, hfx₀⟩ := hcon
  set S := Icc a b ∩ f ⁻¹' (Ici 0) with hS
  have hSc : IsClosed S := hc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have hSne : S.Nonempty := ⟨x₀, hx₀, hfx₀⟩
  have hSbdd : BddBelow S := ⟨a, fun y hy => hy.1.1⟩
  have hcS : sInf S ∈ S := hSc.csInf_mem hSne hSbdd
  set c := sInf S with hc_def
  have hcmem : c ∈ Icc a b := hcS.1
  have hfc_nonneg : 0 ≤ f c := hcS.2
  have hac : a < c := by
    rcases eq_or_lt_of_le hcmem.1 with h | h
    · exfalso; rw [← h] at hfc_nonneg; linarith
    · exact h
  have hneg : ∀ y ∈ Ico a c, f y < 0 := by
    intro y hy
    by_contra h; push Not at h
    have : c ≤ y := csInf_le hSbdd ⟨⟨hy.1, hy.2.le.trans hcmem.2⟩, h⟩
    linarith [hy.2]
  have hfc0 : f c ≤ 0 := by
    have hcw : Tendsto f (𝓝[<] c) (𝓝 (f c)) := by
      have := (hc c hcmem).mono (show Ioo a c ⊆ Icc a b from
        fun y hy => ⟨hy.1.le, hy.2.le.trans hcmem.2⟩)
      rwa [ContinuousWithinAt, nhdsWithin_Ioo_eq_nhdsLT hac] at this
    exact le_of_tendsto hcw (by
      filter_upwards [Ioo_mem_nhdsLT hac] with y hy using (hneg y ⟨hy.1.le, hy.2⟩).le)
  have hfc : f c = 0 := le_antisymm hfc0 hfc_nonneg
  have hev := hz c ⟨hac, hcmem.2⟩ hfc
  obtain ⟨y, hy1, hy2⟩ := (hev.and (Ioo_mem_nhdsLT hac)).exists
  linarith [hneg y ⟨hy2.1.le, hy2.2⟩]

lemma no_rise_to_left {f f' : ℝ → ℝ} {b x : ℝ} (hbx : b ≤ x) (hc : ContinuousOn f (Icc b x))
    (hlt : f x < f b) (hx : f x < 0)
    (hderiv : ∀ r ∈ Ioo b x, HasDerivAt f (f' r) r)
    (hd : ∀ r ∈ Ioo b x, f r < 0 → 0 ≤ f' r) : False := by
  set l := (f x + min (f b) 0) / 2 with hl
  have hl1 : f x < l := by
    have : f x < min (f b) 0 := lt_min hlt hx
    linarith
  have hl2 : l < 0 := by
    have : min (f b) 0 ≤ 0 := min_le_right _ _
    linarith
  have hl3 : l ≤ f b := by
    have : min (f b) 0 ≤ f b := min_le_left _ _
    have : f x < f b := hlt
    linarith
  set S := Icc b x ∩ f ⁻¹' (Ici l) with hS
  have hSc : IsClosed S := hc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have hSne : S.Nonempty := ⟨b, ⟨le_rfl, hbx⟩, hl3⟩
  have hSbdd : BddAbove S := ⟨x, fun y hy => hy.1.2⟩
  have hcS : sSup S ∈ S := hSc.csSup_mem hSne hSbdd
  set c := sSup S with hc_def
  have hcmem : c ∈ Icc b x := hcS.1
  have hlc : l ≤ f c := hcS.2
  have hright : ∀ r ∈ Ioc c x, f r < l := by
    intro r hr
    by_contra h; push Not at h
    have : r ≤ c := le_csSup hSbdd ⟨⟨hcmem.1.trans hr.1.le, hr.2⟩, h⟩
    linarith [hr.1]
  have hmono : MonotoneOn f (Icc c x) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc c x)
      (hc.mono (Icc_subset_Icc_left hcmem.1)) (f' := f') ?_ ?_
    · intro r hr
      rw [interior_Icc] at hr ⊢
      exact (hderiv r ⟨hcmem.1.trans_lt hr.1, hr.2⟩).hasDerivWithinAt
    · intro r hr
      rw [interior_Icc] at hr
      exact hd r ⟨hcmem.1.trans_lt hr.1, hr.2⟩ (by linarith [hright r ⟨hr.1, hr.2.le⟩])
  have := hmono ⟨le_rfl, hcmem.2⟩ ⟨hcmem.2, le_rfl⟩ hcmem.2
  linarith

/-! ### Piecewise-smooth tools (finitely many interface radii) -/

/-- Left-neighbourhood version of `pos_left_of_deriv_neg`: if `f` is continuous on `[l, x]`,
`f x = 0`, and `f` has a negative derivative at every point of some punctured left
neighbourhood of `x` (but possibly *not* at `x` itself, e.g. at a density jump), then `f > 0`
just to the left of `x`. -/
lemma pos_left_of_eventually_deriv_neg {f f' : ℝ → ℝ} {l x : ℝ} (hl : l < x)
    (hc : ContinuousOn f (Icc l x))
    (hd : ∀ᶠ y in 𝓝[<] x, HasDerivAt f (f' y) y ∧ f' y < 0) (h0 : f x = 0) :
    ∀ᶠ y in 𝓝[<] x, 0 < f y := by
  obtain ⟨l', hl', hsub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.1 hd
  filter_upwards [Ioo_mem_nhdsLT (max_lt hl hl')] with y hy
  have hly : l ≤ y := (le_max_left _ _).trans hy.1.le
  have hl'y : l' ≤ y := (le_max_right _ _).trans hy.1.le
  have hanti : StrictAntiOn f (Icc y x) := by
    refine strictAntiOn_of_hasDerivWithinAt_neg (convex_Icc y x)
      (hc.mono (Icc_subset_Icc_left hly)) (f' := f') ?_ ?_
    · intro z hz
      rw [interior_Icc] at hz
      exact (hsub ⟨hl'y.trans_lt hz.1, hz.2⟩).1.hasDerivWithinAt
    · intro z hz
      rw [interior_Icc] at hz
      exact (hsub ⟨hl'y.trans_lt hz.1, hz.2⟩).2
  have := hanti ⟨le_rfl, hy.2.le⟩ ⟨hy.2.le, le_rfl⟩ hy.2
  linarith

/-- Monotonicity from a nonnegative derivative *off a finite set* of points: finite-subinterval
induction over the exceptional points (split `[a, b]` at an exceptional point `c ∈ (a, b)` and
glue the two monotone pieces at `c`, using continuity of `f` on the closed interval). -/
lemma monotoneOn_Icc_of_deriv_nonneg_off (F : Finset ℝ) {f f' : ℝ → ℝ} {a b : ℝ}
    (hc : ContinuousOn f (Icc a b)) (hd : ∀ x ∈ Ioo a b, x ∉ F → HasDerivAt f (f' x) x)
    (hnn : ∀ x ∈ Ioo a b, x ∉ F → 0 ≤ f' x) : MonotoneOn f (Icc a b) := by
  induction F using Finset.induction_on generalizing a b with
  | empty =>
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a b) hc (f' := f') ?_ ?_
    · intro x hx; rw [interior_Icc] at hx
      exact (hd x hx (by simp)).hasDerivWithinAt
    · intro x hx; rw [interior_Icc] at hx
      exact hnn x hx (by simp)
  | @insert c F _ ih =>
    by_cases hcab : c ∈ Ioo a b
    · have h1 : MonotoneOn f (Icc a c) :=
        ih (hc.mono (Icc_subset_Icc_right hcab.2.le))
          (fun x hx hxF => hd x ⟨hx.1, hx.2.trans hcab.2⟩ (by simp [hxF, hx.2.ne]))
          (fun x hx hxF => hnn x ⟨hx.1, hx.2.trans hcab.2⟩ (by simp [hxF, hx.2.ne]))
      have h2 : MonotoneOn f (Icc c b) :=
        ih (hc.mono (Icc_subset_Icc_left hcab.1.le))
          (fun x hx hxF => hd x ⟨hcab.1.trans hx.1, hx.2⟩ (by simp [hxF, hx.1.ne']))
          (fun x hx hxF => hnn x ⟨hcab.1.trans hx.1, hx.2⟩ (by simp [hxF, hx.1.ne']))
      have := h1.union_right h2 (isGreatest_Icc hcab.1.le) (isLeast_Icc hcab.2.le)
      rwa [Icc_union_Icc_eq_Icc hcab.1.le hcab.2.le] at this
    · have hne : ∀ x ∈ Ioo a b, x ≠ c := fun x hx h => hcab (h ▸ hx)
      exact ih hc (fun x hx hxF => hd x hx (by simp [hxF, hne x hx]))
        (fun x hx hxF => hnn x hx (by simp [hxF, hne x hx]))

/-- Antitone version of `monotoneOn_Icc_of_deriv_nonneg_off`. -/
lemma antitoneOn_Icc_of_deriv_nonpos_off (F : Finset ℝ) {f f' : ℝ → ℝ} {a b : ℝ}
    (hc : ContinuousOn f (Icc a b)) (hd : ∀ x ∈ Ioo a b, x ∉ F → HasDerivAt f (f' x) x)
    (hnp : ∀ x ∈ Ioo a b, x ∉ F → f' x ≤ 0) : AntitoneOn f (Icc a b) := by
  have hm := monotoneOn_Icc_of_deriv_nonneg_off F (f := fun x => -f x) (f' := fun x => -f' x)
    hc.neg (fun x hx hxF => (hd x hx hxF).neg) (fun x hx hxF => neg_nonneg.2 (hnp x hx hxF))
  intro x hx y hy hxy
  have := hm hx hy hxy
  simp only at this
  linarith

/-- Points of a finite set are isolated: near `x` (punctured) we avoid `F`. -/
lemma eventually_notMem_finset (F : Finset ℝ) (x : ℝ) : ∀ᶠ y in 𝓝[≠] x, y ∉ F := by
  have h : (↑(F.erase x) : Set ℝ)ᶜ ∈ 𝓝 x :=
    (F.erase x).finite_toSet.isClosed.isOpen_compl.mem_nhds (by simp)
  filter_upwards [nhdsWithin_le_nhds h, self_mem_nhdsWithin] with y hy hyx hyF
  exact hy (Finset.mem_coe.2 (Finset.mem_erase.2 ⟨hyx, hyF⟩))

lemma eventually_notMem_left (F : Finset ℝ) (x : ℝ) : ∀ᶠ y in 𝓝[<] x, y ∉ F :=
  nhdsWithin_mono x (fun _ hy => ne_of_lt hy) (eventually_notMem_finset F x)

lemma eventually_notMem_right (F : Finset ℝ) (x : ℝ) : ∀ᶠ y in 𝓝[>] x, y ∉ F :=
  nhdsWithin_mono x (fun _ hy => ne_of_gt hy) (eventually_notMem_finset F x)

/-- Continuity on `(0, R]` gives continuity within any `s ⊆ (-∞, R]` at a point of `(0, R]`. -/
lemma continuousWithinAt_of_Ioc {f : ℝ → ℝ} {R x : ℝ} {s : Set ℝ}
    (hf : ContinuousOn f (Ioc 0 R)) (hx : x ∈ Ioc 0 R) (hs : s ⊆ Iic R) :
    ContinuousWithinAt f s x :=
  (hf x hx).mono_of_mem_nhdsWithin
    (mem_nhdsWithin.2 ⟨Ioi 0, isOpen_Ioi, hx.1, fun _ hz => ⟨hz.1, hs hz.2⟩⟩)

/-- Left limit from continuity on `(0, R]`. -/
lemma tendsto_left_of_Ioc {f : ℝ → ℝ} {R x : ℝ} (hf : ContinuousOn f (Ioc 0 R))
    (hx : x ∈ Ioc 0 R) : Tendsto f (𝓝[<] x) (𝓝 (f x)) :=
  (continuousWithinAt_of_Ioc hf hx (fun _ hy => (le_of_lt hy).trans hx.2)).tendsto

/-- A function continuous on `[l, x]` and negative at `x` is negative just left of `x`. -/
lemma eventually_lt_left_of_continuousOn {G : ℝ → ℝ} {l x : ℝ} (hl : l < x)
    (hG : ContinuousOn G (Icc l x)) (hneg : G x < 0) : ∀ᶠ y in 𝓝[<] x, G y < 0 :=
  nhdsWithin_le_of_mem (mem_of_superset (Ioo_mem_nhdsLT hl) Ioo_subset_Icc_self)
    ((hG x ⟨hl.le, le_rfl⟩).tendsto.eventually (gt_mem_nhds hneg))

/-! ## Part A — exact shifted Hartle–TOV Riccati identity along the vacuum curve -/

noncomputable def Zc (I₀ s : ℝ) : ℝ := 3 * I₀ * s * (1 - s ^ 2) ^ 3 / (4 - I₀ * (1 - s ^ 2) ^ 3)

noncomputable def ZcD (I₀ s : ℝ) : ℝ :=
  ((3 * I₀ * (1 - s ^ 2) ^ 3 - 18 * I₀ * s ^ 2 * (1 - s ^ 2) ^ 2) * (4 - I₀ * (1 - s ^ 2) ^ 3)
    - 3 * I₀ * s * (1 - s ^ 2) ^ 3 * (6 * I₀ * s * (1 - s ^ 2) ^ 2)) / (4 - I₀ * (1 - s ^ 2) ^ 3) ^ 2

lemma hasDerivAt_Zc (I₀ s : ℝ) (h : 4 - I₀ * (1 - s ^ 2) ^ 3 ≠ 0) :
    HasDerivAt (Zc I₀) (ZcD I₀ s) s := by
  have h1 : HasDerivAt (fun y : ℝ => 1 - y ^ 2) (-(2 * s)) s := by
    simpa using (hasDerivAt_pow 2 s).const_sub 1
  have hN : HasDerivAt (fun y : ℝ => 3 * I₀ * y * (1 - y ^ 2) ^ 3)
      (3 * I₀ * (1 - s ^ 2) ^ 3 + 3 * I₀ * s * (3 * (1 - s ^ 2) ^ 2 * (-(2 * s)))) s := by
    have := ((hasDerivAt_id s).const_mul (3 * I₀)).mul (h1.pow 3)
    convert this using 1
    · funext y; simp [id]
    · simp [id]
  have hD : HasDerivAt (fun y : ℝ => 4 - I₀ * (1 - y ^ 2) ^ 3)
      (-(I₀ * (3 * (1 - s ^ 2) ^ 2 * (-(2 * s))))) s := by
    have := ((h1.pow 3).const_mul I₀).const_sub 4
    convert this using 1
  have := hN.div hD h
  convert this using 1
  · funext y; simp [Zc]
  · unfold ZcD; ring

/-- Right-hand side of `r Z'` (Hartle, isotropic). -/
noncomputable def rhsZ (u s πe πp Z : ℝ) : ℝ :=
  (u + πp) * Z / s ^ 2 - Z ^ 2 / s - 3 * Z + 4 * (πe + πp) / s
noncomputable def rhsP (u s πe πp : ℝ) : ℝ := 2 * πp - (πe + πp) * (u + πp) / s ^ 2
noncomputable def rhsS (u s πe : ℝ) : ℝ := (u - πe) / s

noncomputable def rhsD (α I₀ u s πe πp W : ℝ) : ℝ :=
  rhsZ u s πe πp (W + 2 * α * πp / s) - 2 * α * (rhsP u s πe πp / s - πp * rhsS u s πe / s ^ 2)
    - ZcD I₀ s * rhsS u s πe

noncomputable def Lco (α I₀ u s πp W : ℝ) : ℝ :=
  -(W + Zc I₀ s) / s + (u + (1 - 4 * α) * πp) / s ^ 2 - 3

noncomputable def NumE (α I₀ t : ℝ) : ℝ :=
  -(I₀^2*α*t^7 - 7*I₀^2*α*t^6 + 21*I₀^2*α*t^5 - 35*I₀^2*α*t^4 + 35*I₀^2*α*t^3
    - 21*I₀^2*α*t^2 + 7*I₀^2*α*t - I₀^2*α - I₀^2*t^7 + 6*I₀^2*t^6 - 15*I₀^2*t^5
    + 20*I₀^2*t^4 - 15*I₀^2*t^3 + 6*I₀^2*t^2 - I₀^2*t + 8*I₀*α*t^4 - 32*I₀*α*t^3
    + 48*I₀*α*t^2 - 32*I₀*α*t + 8*I₀*α + 52*I₀*t^4 - 84*I₀*t^3 + 12*I₀*t^2 + 20*I₀*t
    + 16*α*t - 16*α - 64*t)
noncomputable def NumP (α I₀ t : ℝ) : ℝ :=
  -(I₀*α*t^4 - 6*I₀*α*t^3 + 12*I₀*α*t^2 - 10*I₀*α*t + 3*I₀*α - I₀*t^4 + 3*I₀*t^3
    - 3*I₀*t^2 + I₀*t + 52*α*t - 12*α - 16*t)

noncomputable def cE (α I₀ s : ℝ) : ℝ := NumE α I₀ (s ^ 2) / (s ^ 3 * (4 - I₀ * (1 - s ^ 2) ^ 3) ^ 2)
noncomputable def cP (α I₀ s : ℝ) : ℝ := NumP α I₀ (s ^ 2) / (s ^ 3 * (4 - I₀ * (1 - s ^ 2) ^ 3))
noncomputable def cPP (α s : ℝ) : ℝ := 4 * α * (1 - α) / s ^ 3

theorem partA (α I₀ u s πe πp W : ℝ) (hs : s ≠ 0) (hden : 4 - I₀ * (1 - s ^ 2) ^ 3 ≠ 0)
    (hu : s ^ 2 = 1 - 2 * u) :
    rhsD α I₀ u s πe πp W = Lco α I₀ u s πp W * (W - Zc I₀ s)
      + cE α I₀ s * πe + cP α I₀ s * πp + cPP α s * πp ^ 2 := by
  have hu' : u = (1 - s ^ 2) / 2 := by linarith
  subst hu'
  set K := 4 - I₀ * (1 - s ^ 2) ^ 3 with hK
  unfold rhsD rhsZ rhsP rhsS ZcD Lco Zc cE cP cPP NumE NumP
  rw [← hK]
  field_simp
  rw [hK]
  ring

/-- The Riccati residual `r (W_α − Z_c)'` evaluated *on* the vacuum curve `W_α = Z_c(s)`
(with `u = (1 − s²)/2`), as a function of the matter variables `π_e, π_p`. -/
noncomputable def resVac (α I₀ s πe πp : ℝ) : ℝ :=
  rhsD α I₀ ((1 - s ^ 2) / 2) s πe πp (Zc I₀ s)

/-- **Part A (exact residual form).** On the vacuum curve the residual is exactly
`c_e π_e + c_p π_p + c_pp π_p²`. -/
theorem partA_residual_form (α I₀ s πe πp : ℝ) (hs : s ≠ 0)
    (hden : 4 - I₀ * (1 - s ^ 2) ^ 3 ≠ 0) :
    resVac α I₀ s πe πp = cE α I₀ s * πe + cP α I₀ s * πp + cPP α s * πp ^ 2 := by
  unfold resVac
  rw [partA α I₀ _ s πe πp _ hs hden (by ring), sub_self, mul_zero, zero_add]

/-- **Part A (constant term cancels).** -/
theorem partA_const_vanishes (α I₀ s : ℝ) (hs : s ≠ 0) (hden : 4 - I₀ * (1 - s ^ 2) ^ 3 ≠ 0) :
    resVac α I₀ s 0 0 = 0 := by
  rw [partA_residual_form α I₀ s 0 0 hs hden]; ring

/-- **Part A (the `π_e π_p` cross term cancels).** -/
theorem partA_cross_vanishes (α I₀ s πe πp : ℝ) (hs : s ≠ 0)
    (hden : 4 - I₀ * (1 - s ^ 2) ^ 3 ≠ 0) :
    resVac α I₀ s πe πp - resVac α I₀ s πe 0 - resVac α I₀ s 0 πp + resVac α I₀ s 0 0 = 0 := by
  simp only [partA_residual_form α I₀ s _ _ hs hden]; ring

/-! ## Exact rational Bernstein certificates

Each `P > 0 on [a, b]` lemma below is proved by an explicit identity
`P(x) = μ + Σₖ γₖ (x − a)ᵏ (b − x)ⁿ⁻ᵏ` with rational `μ > 0`, `γₖ ≥ 0` (checked by `ring`),
on a subdivision of `[a, b]` (generated by exact-rational Bernstein subdivision, mirroring
`bern_min_sign` in `t4a18_kerr_chain.py`). The polynomials are
* `P1c = −Fcore(B₁)/u`, `P1k = −Fconst(B₁)/u²` on `[0, 49/200]`,
* `P2c = −Fcore(B₂)`, `P2k = −Fconst(B₂)` on `[49/200, 51/125]`,
* `P0 = B₁/u − 3` on `[0, 1/200]`,
* `e5`, `s4`: the `α = 69/100`, `Ī₀ = 4` Kerr-barrier factors on `t = s² ∈ [23/125, 1]`.
* `e7 = N_e(69/100, 1001/250, ·)`, `s7 = N_e + N_p (4 − (1001/250)(1 − t)³)`: the
  `α = 69/100`, `Ī₀ = 1001/250` barrier numerators on `t = s² ∈ [23/125, 1]`.
-/

/-- Exact rational polynomial (see the certificate section docstring). -/
noncomputable def P1c (u : ℝ) : ℝ :=
  (61 / 400 : ℝ) +
    (-849 / 400 : ℝ) * u +
    (968 / 25 : ℝ) * u ^ 2 +
    (-124797 / 400 : ℝ) * u ^ 3 +
    (23326 / 25 : ℝ) * u ^ 4 +
    (-60383 / 50 : ℝ) * u ^ 5 +
    (11433 / 4 : ℝ) * u ^ 6 +
    (-31827 / 8 : ℝ) * u ^ 7

lemma P1c_pos_0 (u : ℝ) (h₁ : (0 : ℝ) ≤ u) (h₂ : u ≤ (49 / 400 : ℝ)) : 0 < P1c u := by
  have hX : 0 ≤ u - (0 : ℝ) := by linarith
  have hY : 0 ≤ (49 / 400 : ℝ) - u := by linarith
  have e : P1c u = (1111720738214746077 / 13107200000000000000 : ℝ) +
      ((18104637995617427 / 110730297608 : ℝ) * (u - (0 : ℝ)) ^ 0 * ((49 / 400 : ℝ) - u) ^ 7 +
       (57182385969321989 / 110730297608 : ℝ) * (u - (0 : ℝ)) ^ 1 * ((49 / 400 : ℝ) - u) ^ 6 +
       (118322095507965967 / 110730297608 : ℝ) * (u - (0 : ℝ)) ^ 2 * ((49 / 400 : ℝ) - u) ^ 5 +
       (214122568182609945 / 110730297608 : ℝ) * (u - (0 : ℝ)) ^ 3 * ((49 / 400 : ℝ) - u) ^ 4 +
       (239457573346129945 / 110730297608 : ℝ) * (u - (0 : ℝ)) ^ 4 * ((49 / 400 : ℝ) - u) ^ 3 +
       (130408617333681167 / 110730297608 : ℝ) * (u - (0 : ℝ)) ^ 5 * ((49 / 400 : ℝ) - u) ^ 2 +
       (26269791283645989 / 110730297608 : ℝ) * (u - (0 : ℝ)) ^ 6 * ((49 / 400 : ℝ) - u) ^ 1) := by
    unfold P1c; ring
  rw [e]; positivity

lemma P1c_pos_1 (u : ℝ) (h₁ : (49 / 400 : ℝ) ≤ u) (h₂ : u ≤ (49 / 200 : ℝ)) : 0 < P1c u := by
  have hX : 0 ≤ u - (49 / 400 : ℝ) := by linarith
  have hY : 0 ≤ (49 / 200 : ℝ) - u := by linarith
  have e : P1c u = (1737077478588077 / 409600000000000000 : ℝ) +
      ((150876322699989659 / 775112083256 : ℝ) * (u - (49 / 400 : ℝ)) ^ 0 * ((49 / 200 : ℝ) - u) ^ 7 +
       (62303265708171835 / 55365148804 : ℝ) * (u - (49 / 400 : ℝ)) ^ 1 * ((49 / 200 : ℝ) - u) ^ 6 +
       (66950022507474569 / 27682574402 : ℝ) * (u - (49 / 400 : ℝ)) ^ 2 * ((49 / 200 : ℝ) - u) ^ 5 +
       (30352842058983835 / 13841287201 : ℝ) * (u - (49 / 400 : ℝ)) ^ 3 * ((49 / 200 : ℝ) - u) ^ 4 +
       (8252710359675890 / 13841287201 : ℝ) * (u - (49 / 400 : ℝ)) ^ 4 * ((49 / 200 : ℝ) - u) ^ 3 +
       (3811032248384044 / 13841287201 : ℝ) * (u - (49 / 400 : ℝ)) ^ 6 * ((49 / 200 : ℝ) - u) ^ 1 +
       (15744747151113732 / 96889010407 : ℝ) * (u - (49 / 400 : ℝ)) ^ 7 * ((49 / 200 : ℝ) - u) ^ 0) := by
    unfold P1c; ring
  rw [e]; positivity

/-- Exact Bernstein certificate: `P1c > 0` on `[0, 49/200]`. -/
lemma P1c_pos (u : ℝ) (h₁ : (0 : ℝ) ≤ u) (h₂ : u ≤ (49 / 200 : ℝ)) : 0 < P1c u := by
  rcases le_or_gt u (49 / 400 : ℝ) with h0 | h0
  · exact P1c_pos_0 u (by linarith) h0
  exact P1c_pos_1 u h0.le h₂

/-- Exact rational polynomial (see the certificate section docstring). -/
noncomputable def P1k (u : ℝ) : ℝ :=
  (5681 / 400 : ℝ) +
    (-5643 / 200 : ℝ) * u +
    (-50519 / 400 : ℝ) * u ^ 2 +
    (8137 / 200 : ℝ) * u ^ 3 +
    (53173 / 200 : ℝ) * u ^ 4 +
    (-206 / 5 : ℝ) * u ^ 5 +
    (10609 / 16 : ℝ) * u ^ 6

lemma P1k_pos_0 (u : ℝ) (h₁ : (0 : ℝ) ≤ u) (h₂ : u ≤ (49 / 200 : ℝ)) : 0 < P1k u := by
  have hX : 0 ≤ u - (0 : ℝ) := by linarith
  have hY : 0 ≤ (49 / 200 : ℝ) - u := by linarith
  have e : P1k u = (1405009850840849 / 1024000000000000 : ℝ) +
      ((268129594880799 / 4519603984 : ℝ) * (u - (0 : ℝ)) ^ 0 * ((49 / 200 : ℝ) - u) ^ 6 +
       (732158384642397 / 2259801992 : ℝ) * (u - (0 : ℝ)) ^ 1 * ((49 / 200 : ℝ) - u) ^ 5 +
       (3141212339211985 / 4519603984 : ℝ) * (u - (0 : ℝ)) ^ 2 * ((49 / 200 : ℝ) - u) ^ 4 +
       (824194300323995 / 1129900996 : ℝ) * (u - (0 : ℝ)) ^ 3 * ((49 / 200 : ℝ) - u) ^ 3 +
       (1684299739138385 / 4519603984 : ℝ) * (u - (0 : ℝ)) ^ 4 * ((49 / 200 : ℝ) - u) ^ 2 +
       (164775461366877 / 2259801992 : ℝ) * (u - (0 : ℝ)) ^ 5 * ((49 / 200 : ℝ) - u) ^ 1) := by
    unfold P1k; ring
  rw [e]; positivity

/-- Exact Bernstein certificate: `P1k > 0` on `[0, 49/200]`. -/
lemma P1k_pos (u : ℝ) (h₁ : (0 : ℝ) ≤ u) (h₂ : u ≤ (49 / 200 : ℝ)) : 0 < P1k u := by
  exact P1k_pos_0 u h₁ h₂

/-- Exact rational polynomial (see the certificate section docstring). -/
noncomputable def P2c (u : ℝ) : ℝ :=
  (3540473903494206609 / 20480000000000000000 : ℝ) +
    (-3249033476758417 / 1280000000000000 : ℝ) * u +
    (-219318696977 / 64000000000 : ℝ) * u ^ 2 +
    (2571952765659 / 32000000000 : ℝ) * u ^ 3 +
    (-64681807 / 400000 : ℝ) * u ^ 4 +
    (643929 / 10000 : ℝ) * u ^ 5 +
    (-169 / 25 : ℝ) * u ^ 6

lemma P2c_pos_0 (u : ℝ) (h₁ : (49 / 200 : ℝ) ≤ u) (h₂ : u ≤ (51 / 125 : ℝ)) : 0 < P2c u := by
  have hX : 0 ≤ u - (49 / 200 : ℝ) := by linarith
  have hY : 0 ≤ (51 / 125 : ℝ) - u := by linarith
  have e : P2c u = (695112667278449 / 20480000000000000000 : ℝ) +
      ((7471373243668125 / 460254468172 : ℝ) * (u - (49 / 200 : ℝ)) ^ 1 * ((51 / 125 : ℝ) - u) ^ 5 +
       (332832786064311995 / 3682035745376 : ℝ) * (u - (49 / 200 : ℝ)) ^ 2 * ((51 / 125 : ℝ) - u) ^ 4 +
       (698394333497080751 / 3682035745376 : ℝ) * (u - (49 / 200 : ℝ)) ^ 3 * ((51 / 125 : ℝ) - u) ^ 3 +
       (683574683340156283 / 3682035745376 : ℝ) * (u - (49 / 200 : ℝ)) ^ 4 * ((51 / 125 : ℝ) - u) ^ 2 +
       (1528363450551324497 / 18410178726880 : ℝ) * (u - (49 / 200 : ℝ)) ^ 5 * ((51 / 125 : ℝ) - u) ^ 1 +
       (592570619882295383 / 46025446817200 : ℝ) * (u - (49 / 200 : ℝ)) ^ 6 * ((51 / 125 : ℝ) - u) ^ 0) := by
    unfold P2c; ring
  rw [e]; positivity

/-- Exact Bernstein certificate: `P2c > 0` on `[49/200, 51/125]`. -/
lemma P2c_pos (u : ℝ) (h₁ : (49 / 200 : ℝ) ≤ u) (h₂ : u ≤ (51 / 125 : ℝ)) : 0 < P2c u := by
  exact P2c_pos_0 u h₁ h₂

/-- Exact rational polynomial (see the certificate section docstring). -/
noncomputable def P2k (u : ℝ) : ℝ :=
  (-16076642596721657391 / 40960000000000000000 : ℝ) +
    (3581481880126983 / 1280000000000000 : ℝ) * u +
    (-4531252990427 / 6400000000000 : ℝ) * u ^ 2 +
    (-955512205659 / 32000000000 : ℝ) * u ^ 3 +
    (46987507 / 800000 : ℝ) * u ^ 4 +
    (-197743 / 10000 : ℝ) * u ^ 5 +
    (169 / 100 : ℝ) * u ^ 6

lemma P2k_pos_0 (u : ℝ) (h₁ : (49 / 200 : ℝ) ≤ u) (h₂ : u ≤ (653 / 2000 : ℝ)) : 0 < P2k u := by
  have hX : 0 ≤ u - (49 / 200 : ℝ) := by linarith
  have hY : 0 ≤ (653 / 2000 : ℝ) - u := by linarith
  have e : P2k u = (62359446663848921409 / 25600000000000000000000 : ℝ) +
      ((34321312620475502 / 2876590426075 : ℝ) * (u - (49 / 200 : ℝ)) ^ 0 * ((653 / 2000 : ℝ) - u) ^ 6 +
       (351408386335353012 / 2876590426075 : ℝ) * (u - (49 / 200 : ℝ)) ^ 1 * ((653 / 2000 : ℝ) - u) ^ 5 +
       (192132014920297756 / 575318085215 : ℝ) * (u - (49 / 200 : ℝ)) ^ 2 * ((653 / 2000 : ℝ) - u) ^ 4 +
       (881394933719134177 / 2301272340860 : ℝ) * (u - (49 / 200 : ℝ)) ^ 3 * ((653 / 2000 : ℝ) - u) ^ 3 +
       (444911593609574459 / 2301272340860 : ℝ) * (u - (49 / 200 : ℝ)) ^ 4 * ((653 / 2000 : ℝ) - u) ^ 2 +
       (391855857247366223 / 11506361704300 : ℝ) * (u - (49 / 200 : ℝ)) ^ 5 * ((653 / 2000 : ℝ) - u) ^ 1) := by
    unfold P2k; ring
  rw [e]; positivity

lemma P2k_pos_1 (u : ℝ) (h₁ : (653 / 2000 : ℝ) ≤ u) (h₂ : u ≤ (1469 / 4000 : ℝ)) : 0 < P2k u := by
  have hX : 0 ≤ u - (653 / 2000 : ℝ) := by linarith
  have hY : 0 ≤ (1469 / 4000 : ℝ) - u := by linarith
  have e : P2k u = (47573657388408249433 / 307200000000000000000000 : ℝ) +
      ((171960663209270873 / 345190851129 : ℝ) * (u - (653 / 2000 : ℝ)) ^ 0 * ((1469 / 4000 : ℝ) - u) ^ 6 +
       (5463186302484613866 / 2876590426075 : ℝ) * (u - (653 / 2000 : ℝ)) ^ 1 * ((1469 / 4000 : ℝ) - u) ^ 5 +
       (275278533540334997 / 115063617043 : ℝ) * (u - (653 / 2000 : ℝ)) ^ 2 * ((1469 / 4000 : ℝ) - u) ^ 4 +
       (1620898875786091202 / 1725954255645 : ℝ) * (u - (653 / 2000 : ℝ)) ^ 3 * ((1469 / 4000 : ℝ) - u) ^ 3 +
       (704298438962589811 / 2876590426075 : ℝ) * (u - (653 / 2000 : ℝ)) ^ 5 * ((1469 / 4000 : ℝ) - u) ^ 1 +
       (1329645273462904513 / 6903817022580 : ℝ) * (u - (653 / 2000 : ℝ)) ^ 6 * ((1469 / 4000 : ℝ) - u) ^ 0) := by
    unfold P2k; ring
  rw [e]; positivity

lemma P2k_pos_2 (u : ℝ) (h₁ : (1469 / 4000 : ℝ) ≤ u) (h₂ : u ≤ (51 / 125 : ℝ)) : 0 < P2k u := by
  have hX : 0 ≤ u - (1469 / 4000 : ℝ) := by linarith
  have hY : 0 ≤ (51 / 125 : ℝ) - u := by linarith
  have e : P2k u = (424651842475300058609 / 409600000000000000000000 : ℝ) +
      ((5239629489389342943 / 5753180852150 : ℝ) * (u - (1469 / 4000 : ℝ)) ^ 1 * ((51 / 125 : ℝ) - u) ^ 5 +
       (14310291590242849207 / 2301272340860 : ℝ) * (u - (1469 / 4000 : ℝ)) ^ 2 * ((51 / 125 : ℝ) - u) ^ 4 +
       (9337841053437803763 / 575318085215 : ℝ) * (u - (1469 / 4000 : ℝ)) ^ 3 * ((51 / 125 : ℝ) - u) ^ 3 +
       (9437335016126012179 / 460254468172 : ℝ) * (u - (1469 / 4000 : ℝ)) ^ 4 * ((51 / 125 : ℝ) - u) ^ 2 +
       (72700646224389953343 / 5753180852150 : ℝ) * (u - (1469 / 4000 : ℝ)) ^ 5 * ((51 / 125 : ℝ) - u) ^ 1 +
       (35152558587701397589 / 11506361704300 : ℝ) * (u - (1469 / 4000 : ℝ)) ^ 6 * ((51 / 125 : ℝ) - u) ^ 0) := by
    unfold P2k; ring
  rw [e]; positivity

/-- Exact Bernstein certificate: `P2k > 0` on `[49/200, 51/125]`. -/
lemma P2k_pos (u : ℝ) (h₁ : (49 / 200 : ℝ) ≤ u) (h₂ : u ≤ (51 / 125 : ℝ)) : 0 < P2k u := by
  rcases le_or_gt u (653 / 2000 : ℝ) with h0 | h0
  · exact P2k_pos_0 u h₁ h0
  rcases le_or_gt u (1469 / 4000 : ℝ) with h1 | h1
  · exact P2k_pos_1 u (by linarith) h1
  exact P2k_pos_2 u (le_of_lt h1) h₂

/-- Exact rational polynomial (see the certificate section docstring). -/
noncomputable def P0 (u : ℝ) : ℝ :=
  (1 / 20 : ℝ) +
    (-103 / 20 : ℝ) * u +
    (4 / 5 : ℝ) * u ^ 2 +
    (-103 / 4 : ℝ) * u ^ 3

lemma P0_pos_0 (u : ℝ) (h₁ : (0 : ℝ) ≤ u) (h₂ : u ≤ (1 / 200 : ℝ)) : 0 < P0 u := by
  have hX : 0 ≤ u - (0 : ℝ) := by linarith
  have hY : 0 ≤ (1 / 200 : ℝ) - u := by linarith
  have e : P0 u = (776537 / 32000000 : ℝ) +
      ((823463 / 4 : ℝ) * (u - (0 : ℝ)) ^ 0 * ((1 / 200 : ℝ) - u) ^ 3 +
       (1646389 / 4 : ℝ) * (u - (0 : ℝ)) ^ 1 * ((1 / 200 : ℝ) - u) ^ 2 +
       (823029 / 4 : ℝ) * (u - (0 : ℝ)) ^ 2 * ((1 / 200 : ℝ) - u) ^ 1) := by
    unfold P0; ring
  rw [e]; positivity

/-- Exact Bernstein certificate: `P0 > 0` on `[0, 1/200]`. -/
lemma P0_pos (u : ℝ) (h₁ : (0 : ℝ) ≤ u) (h₂ : u ≤ (1 / 200 : ℝ)) : 0 < P0 u := by
  exact P0_pos_0 u h₁ h₂

/-- Exact rational polynomial (see the certificate section docstring). -/
noncomputable def e5 (t : ℝ) : ℝ :=
  (-279 : ℝ) +
    (1737 : ℝ) * t +
    (-1023 : ℝ) * t ^ 2 +
    (51 : ℝ) * t ^ 3 +
    (-117 : ℝ) * t ^ 4 +
    (31 : ℝ) * t ^ 5

lemma e5_pos_0 (t : ℝ) (h₁ : (23 / 125 : ℝ) ≤ t) (h₂ : t ≤ (1 : ℝ)) : 0 < e5 t := by
  have hX : 0 ≤ t - (23 / 125 : ℝ) := by linarith
  have hY : 0 ≤ (1 : ℝ) - t := by linarith
  have e : e5 t = (188093445758 / 30517578125 : ℝ) +
      ((332758355855 / 108243216 : ℝ) * (t - (23 / 125 : ℝ)) ^ 1 * ((1 : ℝ) - t) ^ 4 +
       (282122738615 / 27060804 : ℝ) * (t - (23 / 125 : ℝ)) ^ 2 * ((1 : ℝ) - t) ^ 3 +
       (230820164285 / 18040536 : ℝ) * (t - (23 / 125 : ℝ)) ^ 3 * ((1 : ℝ) - t) ^ 2 +
       (175916392745 / 27060804 : ℝ) * (t - (23 / 125 : ℝ)) ^ 4 * ((1 : ℝ) - t) ^ 1 +
       (117832723571 / 108243216 : ℝ) * (t - (23 / 125 : ℝ)) ^ 5 * ((1 : ℝ) - t) ^ 0) := by
    unfold e5; ring
  rw [e]; positivity

/-- Exact Bernstein certificate: `e5 > 0` on `[23/125, 1]`. -/
lemma e5_pos (t : ℝ) (h₁ : (23 / 125 : ℝ) ≤ t) (h₂ : t ≤ (1 : ℝ)) : 0 < e5 t := by
  exact e5_pos_0 t h₁ h₂

/-- Exact rational polynomial (see the certificate section docstring). -/
noncomputable def s4 (t : ℝ) : ℝ :=
  (-63 : ℝ) +
    (498 : ℝ) * t +
    (-363 : ℝ) * t ^ 2 +
    (-48 : ℝ) * t ^ 3 +
    (31 : ℝ) * t ^ 4

lemma s4_pos_0 (t : ℝ) (h₁ : (23 / 125 : ℝ) ≤ t) (h₂ : t ≤ (1 : ℝ)) : 0 < s4 t := by
  have hX : 0 ≤ t - (23 / 125 : ℝ) := by linarith
  have hY : 0 ≤ (1 : ℝ) - t := by linarith
  have e : s4 t = (3925485571 / 244140625 : ℝ) +
      ((175934177 / 265302 : ℝ) * (t - (23 / 125 : ℝ)) ^ 1 * ((1 : ℝ) - t) ^ 3 +
       (250081177 / 176868 : ℝ) * (t - (23 / 125 : ℝ)) ^ 2 * ((1 : ℝ) - t) ^ 2 +
       (35708842 / 44217 : ℝ) * (t - (23 / 125 : ℝ)) ^ 3 * ((1 : ℝ) - t) ^ 1 +
       (46579651 / 530604 : ℝ) * (t - (23 / 125 : ℝ)) ^ 4 * ((1 : ℝ) - t) ^ 0) := by
    unfold s4; ring
  rw [e]; positivity

/-- Exact Bernstein certificate: `s4 > 0` on `[23/125, 1]`. -/
lemma s4_pos (t : ℝ) (h₁ : (23 / 125 : ℝ) ≤ t) (h₂ : t ≤ (1 : ℝ)) : 0 < s4 t := by
  exact s4_pos_0 t h₁ h₂

/-- Exact rational polynomial `N_e(69/100, 1001/250, t)` (see the certificate section docstring). -/
noncomputable def e7 (t : ℝ) : ℝ :=
  (69 / 6250000 : ℝ) +
    (-714383 / 6250000 : ℝ) * t +
    (-278429151 / 6250000 : ℝ) * t ^ 2 +
    (347564217 / 1250000 : ℝ) * t ^ 3 +
    (-204721517 / 1250000 : ℝ) * t ^ 4 +
    (51102051 / 6250000 : ℝ) * t ^ 5 +
    (-117234117 / 6250000 : ℝ) * t ^ 6 +
    (31062031 / 6250000 : ℝ) * t ^ 7

lemma e7_pos_0 (t : ℝ) (h₁ : (23 / 125 : ℝ) ≤ t) (h₂ : t ≤ (1 : ℝ)) : 0 < e7 t := by
  have hX : 0 ≤ t - (23 / 125 : ℝ) := by linarith
  have hY : 0 ≤ (1 : ℝ) - t := by linarith
  have e : e7 t = (3011531300957971952 / 186264514923095703125 : ℝ) +
      ((1429837643634501221 / 54988399378125000 : ℝ) * (t - (23 / 125 : ℝ)) ^ 1 * ((1 : ℝ) - t) ^ 6 +
       (13407655109022511817 / 36658932918750000 : ℝ) * (t - (23 / 125 : ℝ)) ^ 2 * ((1 : ℝ) - t) ^ 5 +
       (822695448872661379 / 458236661484375 : ℝ) * (t - (23 / 125 : ℝ)) ^ 3 * ((1 : ℝ) - t) ^ 4 +
       (82283046683241261817 / 21995359751250000 : ℝ) * (t - (23 / 125 : ℝ)) ^ 4 * ((1 : ℝ) - t) ^ 3 +
       (67902091044867701221 / 18329466459375000 : ℝ) * (t - (23 / 125 : ℝ)) ^ 5 * ((1 : ℝ) - t) ^ 2 +
       (61581645342167660189 / 36658932918750000 : ℝ) * (t - (23 / 125 : ℝ)) ^ 6 * ((1 : ℝ) - t) ^ 1 +
       (14605290960511234103 / 54988399378125000 : ℝ) * (t - (23 / 125 : ℝ)) ^ 7 * ((1 : ℝ) - t) ^ 0) := by
    unfold e7; ring
  rw [e]; positivity

/-- Exact Bernstein certificate: `e7 > 0` on `[23/125, 1]`. -/
lemma e7_pos (t : ℝ) (h₁ : (23 / 125 : ℝ) ≤ t) (h₂ : t ≤ (1 : ℝ)) : 0 < e7 t := by
  exact e7_pos_0 t h₁ h₂

/-- Exact rational polynomial `N_e + N_p (4 − (1001/250)(1 − t)³)` at `α = 69/100`,
`Ī₀ = 1001/250` (see the certificate section docstring). -/
noncomputable def s7 (t : ℝ) : ℝ :=
  (69 / 1562500 : ℝ) +
    (-714797 / 3125000 : ℝ) * t +
    (471471 / 781250 : ℝ) * t ^ 2 +
    (-13072059 / 625000 : ℝ) * t ^ 3 +
    (9998989 / 62500 : ℝ) * t ^ 4 +
    (-363726363 / 3125000 : ℝ) * t ^ 5 +
    (-6012006 / 390625 : ℝ) * t ^ 6 +
    (31062031 / 3125000 : ℝ) * t ^ 7

lemma s7_pos_0 (t : ℝ) (h₁ : (23 / 125 : ℝ) ≤ t) (h₂ : t ≤ (1 : ℝ)) : 0 < s7 t := by
  have hX : 0 ≤ t - (23 / 125 : ℝ) := by linarith
  have hY : 0 ≤ (1 : ℝ) - t := by linarith
  have e : s7 t = (1192169795765337904 / 186264514923095703125 : ℝ) +
      ((218239404567789067 / 54988399378125000 : ℝ) * (t - (23 / 125 : ℝ)) ^ 1 * ((1 : ℝ) - t) ^ 6 +
       (2300206359255213259 / 36658932918750000 : ℝ) * (t - (23 / 125 : ℝ)) ^ 2 * ((1 : ℝ) - t) ^ 5 +
       (2788265568091581503 / 7331786583750000 : ℝ) * (t - (23 / 125 : ℝ)) ^ 3 * ((1 : ℝ) - t) ^ 4 +
       (23316792822634119509 / 21995359751250000 : ℝ) * (t - (23 / 125 : ℝ)) ^ 4 * ((1 : ℝ) - t) ^ 3 +
       (46801250671755213259 / 36658932918750000 : ℝ) * (t - (23 / 125 : ℝ)) ^ 5 * ((1 : ℝ) - t) ^ 2 +
       (22039498718384550253 / 36658932918750000 : ℝ) * (t - (23 / 125 : ℝ)) ^ 6 * ((1 : ℝ) - t) ^ 1 +
       (8032017874634115287 / 109976798756250000 : ℝ) * (t - (23 / 125 : ℝ)) ^ 7 * ((1 : ℝ) - t) ^ 0) := by
    unfold s7; ring
  rw [e]; positivity

/-- Exact Bernstein certificate: `s7 > 0` on `[23/125, 1]`. -/
lemma s7_pos (t : ℝ) (h₁ : (23 / 125 : ℝ) ≤ t) (h₂ : t ≤ (1 : ℝ)) : 0 < s7 t := by
  exact s7_pos_0 t h₁ h₂
/-! ## Part B — Bondi–Pontryagin compactness wall `m/r < 51/125`

The two-piece barrier from `t4a18_kerr_chain.py` (case `w = 1`, isotropic DEC):
`B₁(u) = u (61/20 − 103/20 u + 4/5 u² − 103/4 u³)` on `[0, u_j]`, `u_j = 49/200`, and
`B₂(u) = B₁(u_j) + d (−23/20 − 133/20 d + 13/10 d²)`, `d = u − u_j`, on `[u_j, 51/125]`. -/

/-- First barrier piece `B₁`. -/
noncomputable def B1 (u : ℝ) : ℝ := u * (61 / 20 + (-103 / 20) * u + 4 / 5 * u ^ 2 + (-103 / 4) * u ^ 3)

/-- `B₁'`. -/
noncomputable def B1d (u : ℝ) : ℝ :=
  61 / 20 + 2 * (-103 / 20) * u + 3 * (4 / 5) * u ^ 2 + 4 * (-103 / 4) * u ^ 3

/-- Second barrier piece `B₂`. -/
noncomputable def B2 (u : ℝ) : ℝ :=
  B1 (49 / 200) + (u - 49 / 200) * (-23 / 20 + (-133 / 20) * (u - 49 / 200)
    + 13 / 10 * (u - 49 / 200) ^ 2)

/-- `B₂'`. -/
noncomputable def B2d (u : ℝ) : ℝ :=
  -23 / 20 + 2 * (-133 / 20) * (u - 49 / 200) + 3 * (13 / 10) * (u - 49 / 200) ^ 2

lemma hasDerivAt_B1 (z : ℝ) : HasDerivAt B1 (B1d z) z := by
  have h := ((((hasDerivAt_id z).const_mul (61 / 20 : ℝ)).add
    ((hasDerivAt_pow 2 z).const_mul (-103 / 20 : ℝ))).add
    ((hasDerivAt_pow 3 z).const_mul (4 / 5 : ℝ))).add
    ((hasDerivAt_pow 4 z).const_mul (-103 / 4 : ℝ))
  convert h using 1
  · funext y; simp only [B1, Pi.add_apply, id]; ring
  · norm_num [B1d]; ring

lemma hasDerivAt_B2 (z : ℝ) : HasDerivAt B2 (B2d z) z := by
  have h1 : HasDerivAt (fun y : ℝ => y - 49 / 200) 1 z := (hasDerivAt_id z).sub_const _
  have h := ((h1.const_mul (-23 / 20 : ℝ)).add ((h1.pow 2).const_mul (-133 / 20 : ℝ))).add
    ((h1.pow 3).const_mul (13 / 10 : ℝ))
  have h' := h.const_add (B1 (49 / 200))
  convert h' using 1
  · funext y; simp only [B2, Pi.add_apply, Pi.pow_apply]; ring
  · norm_num [B2d]; ring

/-- Barrier residual along the DEC-saturating core control `π_e = v` (`w = 1`). -/
noncomputable def Fcore (B Bd : ℝ → ℝ) (u : ℝ) : ℝ :=
  (1 - 2 * u) * (2 * B u + (u - B u) * Bd u) - 2 * B u * (u + B u)

/-- Barrier residual along the constant-density control `π_e = 3u`. -/
noncomputable def Fconst (B Bd : ℝ → ℝ) (u : ℝ) : ℝ :=
  (1 - 2 * u) * (2 * B u - 2 * u * Bd u) - (3 * u + B u) * (u + B u)

lemma continuous_B1d : Continuous B1d := by unfold B1d; fun_prop
lemma continuous_B2d : Continuous B2d := by unfold B2d; fun_prop

lemma B1_core {u : ℝ} (h0 : 0 < u) (h1 : u ≤ 49 / 200) : Fcore B1 B1d u < 0 := by
  have e : Fcore B1 B1d u = -(u * P1c u) := by unfold Fcore B1 B1d P1c; ring
  rw [e]; have := P1c_pos u h0.le h1; have := mul_pos h0 this; linarith

lemma B1_const {u : ℝ} (h0 : 0 < u) (h1 : u ≤ 49 / 200) : Fconst B1 B1d u < 0 := by
  have e : Fconst B1 B1d u = -(u ^ 2 * P1k u) := by unfold Fconst B1 B1d P1k; ring
  rw [e]; have := P1k_pos u h0.le h1; have := mul_pos (pow_pos h0 2) this; linarith

lemma B2_core {u : ℝ} (h0 : 49 / 200 ≤ u) (h1 : u ≤ 51 / 125) : Fcore B2 B2d u < 0 := by
  have e : Fcore B2 B2d u = -P2c u := by unfold Fcore B2 B2d B1 P2c; ring
  rw [e]; have := P2c_pos u h0 h1; linarith

lemma B2_const {u : ℝ} (h0 : 49 / 200 ≤ u) (h1 : u ≤ 51 / 125) : Fconst B2 B2d u < 0 := by
  have e : Fconst B2 B2d u = -P2k u := by unfold Fconst B2 B2d B1 P2k; ring
  rw [e]; have := P2k_pos u h0 h1; linarith

/-- Near the centre the barrier lies strictly above the DEC + mean-density cone `v ≤ 3u`. -/
lemma B1_gt_three_mul {u : ℝ} (h0 : 0 < u) (h1 : u ≤ 1 / 200) : 3 * u < B1 u := by
  have e : B1 u - 3 * u = u * P0 u := by unfold B1 P0; ring
  have := mul_pos h0 (P0_pos u h0.le h1); linarith

/-- The barrier is strictly negative at the wall `u = 51/125`. -/
lemma B2_wall_neg : B2 (51 / 125) < 0 := by unfold B2 B1; norm_num

lemma B1_eq_B2 : B1 (49 / 200) = B2 (49 / 200) := by unfold B2; ring

/-- The glued (continuous) barrier, frozen beyond the wall. -/
noncomputable def Bpw (u : ℝ) : ℝ := if u ≤ 49 / 200 then B1 u else B2 (min u (51 / 125))

lemma continuous_Bpw : Continuous Bpw := by
  have h1 : Continuous B1 := by unfold B1; fun_prop
  have h2 : Continuous (fun u : ℝ => B2 (min u (51 / 125))) := by unfold B2; fun_prop
  refine Continuous.if_le h1 h2 continuous_id continuous_const ?_
  intro x hx
  rw [show x = 49 / 200 from hx, min_eq_left (by norm_num), B1_eq_B2]

/-- Pure-algebra kernel of the barrier crossing: an affine function of the density control
`e ∈ [v, 3u]` that is negative at both endpoints is negative throughout. (Stated for an
arbitrary state `(u, v)`, not only on the barrier, so that it can be applied on a left
neighbourhood of a touching point that is itself a density jump.) -/
lemma kernelB {u v e Bd : ℝ} (hu2 : 0 < 1 - 2 * u) (h1 : v ≤ e)
    (h2 : e ≤ 3 * u)
    (hcore : (1 - 2 * u) * (2 * v + (u - v) * Bd) - 2 * v * (u + v) < 0)
    (hconst : (1 - 2 * u) * (2 * v - 2 * u * Bd) - (3 * u + v) * (u + v) < 0) :
    (2 * v - (e + v) * (u + v) / (1 - 2 * u)) - Bd * (e - u) < 0 := by
  have key : (2 * v - (e + v) * (u + v) / (1 - 2 * u)) - Bd * (e - u)
      = ((1 - 2 * u) * 2 * v - (e + v) * (u + v) - (1 - 2 * u) * Bd * (e - u)) / (1 - 2 * u) := by
    field_simp
  rw [key]
  apply div_neg_of_neg_of_pos _ hu2
  set k := -(u + v) - (1 - 2 * u) * Bd
  rcases le_or_gt 0 k with hk | hk
  · have : (1 - 2 * u) * 2 * v - (e + v) * (u + v) - (1 - 2 * u) * Bd * (e - u)
        = ((1 - 2 * u) * (2 * v - 2 * u * Bd) - (3 * u + v) * (u + v)) - (3 * u - e) * k := by
      simp only [k]; ring
    rw [this]; nlinarith
  · have : (1 - 2 * u) * 2 * v - (e + v) * (u + v) - (1 - 2 * u) * Bd * (e - u)
        = ((1 - 2 * u) * (2 * v + (u - v) * Bd) - 2 * v * (u + v)) + (e - v) * k := by
      simp only [k]; ring
    rw [this]; nlinarith

/-! ## The star -/

/-- `s(r) = √(1 − 2 m(r)/r)` (so `s² = e^{-λ}`; `s(0) = 1` by Lean's `x/0 = 0`). -/
noncomputable def sFun (m : ℝ → ℝ) (r : ℝ) : ℝ := Real.sqrt (1 - 2 * m r / r)

/-- A static, spherically symmetric, horizonless, regular perfect-fluid star on `[0, R]` with
isotropic pressure obeying the dominant energy condition, together with the first-order
(Hartle) frame-dragging variable `Z = r s ω̄'/ω̄` — **piecewise-smooth version**.

The star may have finitely many interface radii `jumps` (ordinary first-order phase
transitions / interior density discontinuities, and optionally the surface `R` itself). Across
an interface the mass `m`, the pressure `p` and the Hartle variable `Z` are continuous (the
Israel/Darmois junction conditions for a perfect fluid: continuity of `m`, `p`, `ω̄` and
`r⁴ j ω̄'`), while `ε` may jump, so `m` has unequal one-sided derivatives there and
`HasDerivAt m` genuinely fails at the interface. Accordingly the field equations are imposed
pointwise only on `(0, R] \ jumps`, and continuity of `m, p, Z` on all of `(0, R]`.
At a jump radius `ε` may take any value; the pointwise conditions `p ≤ ε` (and, for monotone
stars, `4π r³ ε ≤ 3m`) are then required of that value, e.g. one of the one-sided limits. -/
structure PiecewiseRegularIsotropicDECStar where
  /-- stellar radius -/
  R : ℝ
  /-- mass function -/
  m : ℝ → ℝ
  /-- energy density -/
  ε : ℝ → ℝ
  /-- isotropic pressure -/
  p : ℝ → ℝ
  /-- Hartle variable `Z = r s ω̄'/ω̄` -/
  Z : ℝ → ℝ
  /-- finite set of interface radii (density jumps); the field equations hold off this set -/
  jumps : Finset ℝ
  R_pos : 0 < R
  /-- horizonless: `s(r) > 0` on `(0, R]` -/
  s_pos : ∀ r ∈ Ioc 0 R, 0 < sFun m r
  /-- junction condition: `m` is continuous across interfaces -/
  continuousOn_m : ContinuousOn m (Ioc 0 R)
  /-- junction condition: `p` is continuous across interfaces -/
  continuousOn_p : ContinuousOn p (Ioc 0 R)
  /-- junction condition: `Z` is continuous across interfaces (`ω̄`, `r⁴ j ω̄'`, `s`, `N`
  continuous) -/
  continuousOn_Z : ContinuousOn Z (Ioc 0 R)
  /-- TOV mass equation (off the interfaces) -/
  hasDerivAt_m : ∀ r ∈ Ioc 0 R, r ∉ jumps → HasDerivAt m (4 * π * r ^ 2 * ε r) r
  /-- TOV hydrostatic equilibrium (off the interfaces) -/
  hasDerivAt_p : ∀ r ∈ Ioc 0 R, r ∉ jumps →
    HasDerivAt p (-(ε r + p r) * (m r + 4 * π * r ^ 3 * p r) / (r ^ 2 * sFun m r ^ 2)) r
  /-- Hartle slow-rotation Riccati equation for `Z = r s ω̄'/ω̄` (off the interfaces):
  `r Z' = (u + π_p) Z / s² − Z²/s − 3Z + 4(π_e + π_p)/s`. -/
  hasDerivAt_Z : ∀ r ∈ Ioc 0 R, r ∉ jumps → HasDerivAt Z
    (((m r / r + 4 * π * r ^ 2 * p r) * Z r / sFun m r ^ 2 - Z r ^ 2 / sFun m r - 3 * Z r
      + 4 * (4 * π * r ^ 2 * ε r + 4 * π * r ^ 2 * p r) / sFun m r) / r) r
  m_zero : m 0 = 0
  p_surface : p R = 0
  Z_zero : Z 0 = 0
  /-- regular centre: `u = m/r → 0` -/
  center_u : Tendsto (fun r => m r / r) (𝓝[>] 0) (𝓝 0)
  /-- regular centre: `π_p = 4π r² p → 0` -/
  center_p : Tendsto (fun r => 4 * π * r ^ 2 * p r) (𝓝[>] 0) (𝓝 0)
  /-- regular centre: `Z → 0` -/
  center_Z : Tendsto Z (𝓝[>] 0) (𝓝 0)
  p_nonneg : ∀ r ∈ Ioc 0 R, 0 ≤ p r
  /-- isotropic dominant energy condition -/
  p_le_ε : ∀ r ∈ Ioc 0 R, p r ≤ ε r
  /-- non-trivial star -/
  M_pos : 0 < m R

/-- A static, spherically symmetric, horizonless, regular perfect-fluid star on `[0, R]` with
isotropic pressure obeying the dominant energy condition, together with the first-order
(Hartle) frame-dragging variable `Z = r s ω̄'/ω̄` — **smooth version** (field equations at
every point of `(0, R]`). It is the special case `jumps = ∅` of
`PiecewiseRegularIsotropicDECStar`, see `RegularIsotropicDECStar.toPiecewise`. -/
structure RegularIsotropicDECStar where
  /-- stellar radius -/
  R : ℝ
  /-- mass function -/
  m : ℝ → ℝ
  /-- energy density -/
  ε : ℝ → ℝ
  /-- isotropic pressure -/
  p : ℝ → ℝ
  /-- Hartle variable `Z = r s ω̄'/ω̄` -/
  Z : ℝ → ℝ
  R_pos : 0 < R
  /-- horizonless: `s(r) > 0` on `(0, R]` -/
  s_pos : ∀ r ∈ Ioc 0 R, 0 < sFun m r
  /-- TOV mass equation -/
  hasDerivAt_m : ∀ r ∈ Ioc 0 R, HasDerivAt m (4 * π * r ^ 2 * ε r) r
  /-- TOV hydrostatic equilibrium -/
  hasDerivAt_p : ∀ r ∈ Ioc 0 R,
    HasDerivAt p (-(ε r + p r) * (m r + 4 * π * r ^ 3 * p r) / (r ^ 2 * sFun m r ^ 2)) r
  /-- Hartle slow-rotation Riccati equation for `Z = r s ω̄'/ω̄`:
  `r Z' = (u + π_p) Z / s² − Z²/s − 3Z + 4(π_e + π_p)/s`. -/
  hasDerivAt_Z : ∀ r ∈ Ioc 0 R, HasDerivAt Z
    (((m r / r + 4 * π * r ^ 2 * p r) * Z r / sFun m r ^ 2 - Z r ^ 2 / sFun m r - 3 * Z r
      + 4 * (4 * π * r ^ 2 * ε r + 4 * π * r ^ 2 * p r) / sFun m r) / r) r
  m_zero : m 0 = 0
  p_surface : p R = 0
  Z_zero : Z 0 = 0
  /-- regular centre: `u = m/r → 0` -/
  center_u : Tendsto (fun r => m r / r) (𝓝[>] 0) (𝓝 0)
  /-- regular centre: `π_p = 4π r² p → 0` -/
  center_p : Tendsto (fun r => 4 * π * r ^ 2 * p r) (𝓝[>] 0) (𝓝 0)
  /-- regular centre: `Z → 0` -/
  center_Z : Tendsto Z (𝓝[>] 0) (𝓝 0)
  p_nonneg : ∀ r ∈ Ioc 0 R, 0 ≤ p r
  /-- isotropic dominant energy condition -/
  p_le_ε : ∀ r ∈ Ioc 0 R, p r ≤ ε r
  /-- non-trivial star -/
  M_pos : 0 < m R

/-- A smooth star is a piecewise-smooth star with no interfaces (`jumps = ∅`); continuity of
`m, p, Z` follows from differentiability. -/
def RegularIsotropicDECStar.toPiecewise (S : RegularIsotropicDECStar) :
    PiecewiseRegularIsotropicDECStar where
  R := S.R
  m := S.m
  ε := S.ε
  p := S.p
  Z := S.Z
  jumps := ∅
  R_pos := S.R_pos
  s_pos := S.s_pos
  continuousOn_m := fun r hr => (S.hasDerivAt_m r hr).continuousAt.continuousWithinAt
  continuousOn_p := fun r hr => (S.hasDerivAt_p r hr).continuousAt.continuousWithinAt
  continuousOn_Z := fun r hr => (S.hasDerivAt_Z r hr).continuousAt.continuousWithinAt
  hasDerivAt_m := fun r hr _ => S.hasDerivAt_m r hr
  hasDerivAt_p := fun r hr _ => S.hasDerivAt_p r hr
  hasDerivAt_Z := fun r hr _ => S.hasDerivAt_Z r hr
  m_zero := S.m_zero
  p_surface := S.p_surface
  Z_zero := S.Z_zero
  center_u := S.center_u
  center_p := S.center_p
  center_Z := S.center_Z
  p_nonneg := S.p_nonneg
  p_le_ε := S.p_le_ε
  M_pos := S.M_pos

/-- A (piecewise-smooth) regular isotropic DEC star with non-increasing mean density,
`4π r³ ε ≤ 3 m` (`π_e ≤ 3u`); this is implied by a non-increasing `ε` (density jumps allowed),
see `PiecewiseRegularIsotropicDECStar.toMonotone`. -/
structure MonotoneIsotropicDECStar extends PiecewiseRegularIsotropicDECStar where
  /-- non-increasing mean density, `π_e ≤ 3u` -/
  mean_density : ∀ r ∈ Ioc 0 R, 4 * π * r ^ 3 * ε r ≤ 3 * m r

/-- From a regular centre, `m(r) → 0` as `r → 0⁺`. -/
lemma tendsto_m_of_center {m : ℝ → ℝ} (hu : Tendsto (fun r => m r / r) (𝓝[>] 0) (𝓝 0)) :
    Tendsto m (𝓝[>] 0) (𝓝 0) := by
  have h := hu.mul (tendsto_id.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ))))
  simp only [mul_zero] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  simp only [id]
  field_simp [ne_of_gt (mem_Ioi.1 hy)]

/-- `m` is continuous on `[0, a]` (regular centre plus continuity on `(0, R]`). -/
lemma continuousOn_m_of_center {R a : ℝ} {m : ℝ → ℝ} (haR : a ≤ R)
    (hm : ContinuousOn m (Ioc 0 R)) (m0 : m 0 = 0)
    (hu : Tendsto (fun r => m r / r) (𝓝[>] 0) (𝓝 0)) : ContinuousOn m (Icc 0 a) := by
  intro y hy
  rcases eq_or_lt_of_le hy.1 with h | h
  · subst h
    have : ContinuousWithinAt m (Ioi 0) 0 := by
      rw [ContinuousWithinAt, m0]; exact tendsto_m_of_center hu
    exact (continuousWithinAt_Ioi_iff_Ici.1 this).mono Icc_subset_Ici_self
  · exact continuousWithinAt_of_Ioc hm ⟨h, hy.2.trans haR⟩ (fun _ hz => hz.2.trans haR)

/-- A non-increasing energy density implies non-increasing mean density, `4π r³ ε(r) ≤ 3 m(r)`,
also across finitely many density jumps `F` (where only continuity of `m` is used). -/
lemma mean_density_of_antitone {R : ℝ} {m ε : ℝ → ℝ} (F : Finset ℝ)
    (hmc : ContinuousOn m (Ioc 0 R))
    (hm : ∀ r ∈ Ioc 0 R, r ∉ F → HasDerivAt m (4 * π * r ^ 2 * ε r) r) (m0 : m 0 = 0)
    (hu : Tendsto (fun r => m r / r) (𝓝[>] 0) (𝓝 0)) (hε : AntitoneOn ε (Ioc 0 R)) :
    ∀ r ∈ Ioc 0 R, 4 * π * r ^ 3 * ε r ≤ 3 * m r := by
  intro r hr
  have hcont : ContinuousOn m (Icc 0 r) := continuousOn_m_of_center hr.2 hmc m0 hu
  have hmono : MonotoneOn (fun ρ => m ρ - 4 * π / 3 * ρ ^ 3 * ε r) (Icc 0 r) := by
    refine monotoneOn_Icc_of_deriv_nonneg_off F (hcont.sub (by fun_prop))
      (f' := fun ρ => 4 * π * ρ ^ 2 * ε ρ - 4 * π * ρ ^ 2 * ε r) ?_ ?_
    · intro y hy hyF
      have hy' : y ∈ Ioc 0 R := ⟨hy.1, hy.2.le.trans hr.2⟩
      have := (hm y hy' hyF).sub (((hasDerivAt_pow 3 y).const_mul (4 * π / 3)).mul_const (ε r))
      exact this.congr_deriv (by push_cast; ring)
    · intro y hy _
      have h1 : ε r ≤ ε y := hε ⟨hy.1, hy.2.le.trans hr.2⟩ hr hy.2.le
      have h2 : 0 ≤ 4 * π * y ^ 2 := by positivity
      nlinarith
  have := hmono ⟨le_rfl, hr.1.le⟩ ⟨hr.1.le, le_rfl⟩ hr.1.le
  simp only [m0] at this
  nlinarith

/-- A piecewise-smooth regular isotropic DEC star with non-increasing energy density (ordinary
downward density jumps allowed) is a `MonotoneIsotropicDECStar`. -/
def PiecewiseRegularIsotropicDECStar.toMonotone (S : PiecewiseRegularIsotropicDECStar)
    (hε : AntitoneOn S.ε (Ioc 0 S.R)) : MonotoneIsotropicDECStar :=
  { S with
    mean_density :=
      mean_density_of_antitone S.jumps S.continuousOn_m S.hasDerivAt_m S.m_zero S.center_u hε }

/-- A smooth regular isotropic DEC star with non-increasing energy density is a
`MonotoneIsotropicDECStar` (via `toPiecewise`, `jumps = ∅`). -/
def RegularIsotropicDECStar.toMonotone (S : RegularIsotropicDECStar)
    (hε : AntitoneOn S.ε (Ioc 0 S.R)) : MonotoneIsotropicDECStar :=
  S.toPiecewise.toMonotone hε

namespace MonotoneIsotropicDECStar

variable (S : MonotoneIsotropicDECStar)

/-- `s(r)` -/
noncomputable def s (r : ℝ) : ℝ := sFun S.m r
/-- compactness function `u = m/r` -/
noncomputable def u (r : ℝ) : ℝ := S.m r / r
/-- `π_e = 4π r² ε` -/
noncomputable def piE (r : ℝ) : ℝ := 4 * π * r ^ 2 * S.ε r
/-- `π_p = 4π r² p` (Bondi's `v`) -/
noncomputable def piP (r : ℝ) : ℝ := 4 * π * r ^ 2 * S.p r
/-- total mass -/
noncomputable def M : ℝ := S.m S.R
/-- Moment of inertia from the exterior matching, `I = R³ Z_R / (6 s_R + 2 Z_R)`
(i.e. `I/(MR²) = (Z_R/(6 C s_R)) / (1 + Z_R/(3 s_R))`). -/
noncomputable def I : ℝ := S.R ^ 3 * S.Z S.R / (6 * S.s S.R + 2 * S.Z S.R)

lemma s_zero : S.s 0 = 1 := by simp [s, sFun]

variable {S}

lemma arg_pos {x : ℝ} (hx : x ∈ Ioc 0 S.R) : 0 < 1 - 2 * S.m x / x :=
  Real.sqrt_pos.1 (S.s_pos x hx)

lemma s_pos' {x : ℝ} (hx : x ∈ Ioc 0 S.R) : 0 < S.s x := S.s_pos x hx

lemma s_sq {x : ℝ} (hx : x ∈ Ioc 0 S.R) : S.s x ^ 2 = 1 - 2 * S.u x := by
  rw [s, sFun, Real.sq_sqrt (arg_pos hx).le, u, mul_div_assoc]

lemma one_sub_two_u_pos {x : ℝ} (hx : x ∈ Ioc 0 S.R) : 0 < 1 - 2 * S.u x := by
  rw [← s_sq hx]; exact pow_pos (s_pos' hx) 2

/-- Mean density is non-increasing, so `m/r³` is antitone (across the finitely many
interfaces, by finite-subinterval induction) and `m > 0` on `(0, R]`. -/
lemma m_pos {r : ℝ} (hr : r ∈ Ioc 0 S.R) : 0 < S.m r := by
  have hsub : Icc r S.R ⊆ Ioc 0 S.R := fun y hy => ⟨hr.1.trans_le hy.1, hy.2⟩
  have hanti : AntitoneOn (fun y => S.m y / y ^ 3) (Icc r S.R) := by
    refine antitoneOn_Icc_of_deriv_nonpos_off S.jumps
      (f' := fun y => (4 * π * y ^ 2 * S.ε y * y ^ 3 - S.m y * (3 * y ^ 2)) / (y ^ 3) ^ 2)
      ?_ ?_ ?_
    · exact (S.continuousOn_m.mono hsub).div (continuousOn_pow 3)
        (fun y hy => pow_ne_zero 3 (hsub hy).1.ne')
    · intro y hy hyF
      have hy' : y ∈ Ioc 0 S.R := hsub ⟨hy.1.le, hy.2.le⟩
      have := (S.hasDerivAt_m y hy' hyF).div (hasDerivAt_pow 3 y) (pow_ne_zero 3 hy'.1.ne')
      convert this using 2
    · intro y hy _
      have hy' : y ∈ Ioc 0 S.R := hsub ⟨hy.1.le, hy.2.le⟩
      apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
      have := S.mean_density y hy'
      have hy2 : 0 < y ^ 2 := pow_pos hy'.1 2
      nlinarith
  have h := hanti ⟨le_rfl, hr.2⟩ ⟨hr.2, le_rfl⟩ hr.2
  have hR : 0 < S.m S.R / S.R ^ 3 := div_pos S.M_pos (pow_pos S.R_pos 3)
  have : 0 < S.m r / r ^ 3 := lt_of_lt_of_le hR h
  exact (div_pos_iff_of_pos_right (pow_pos hr.1 3)).1 this

lemma u_pos {r : ℝ} (hr : r ∈ Ioc 0 S.R) : 0 < S.u r := div_pos (m_pos hr) hr.1

lemma piP_nonneg {r : ℝ} (hr : r ∈ Ioc 0 S.R) : 0 ≤ S.piP r := by
  unfold piP; have := S.p_nonneg r hr; positivity

lemma piP_le_piE {r : ℝ} (hr : r ∈ Ioc 0 S.R) : S.piP r ≤ S.piE r := by
  unfold piP piE
  have := S.p_le_ε r hr
  have h : 0 ≤ 4 * π * r ^ 2 := by positivity
  exact mul_le_mul_of_nonneg_left this h

lemma piE_le_three_u {r : ℝ} (hr : r ∈ Ioc 0 S.R) : S.piE r ≤ 3 * S.u r := by
  unfold piE u
  rw [← mul_div_assoc, le_div_iff₀ hr.1]
  have := S.mean_density r hr
  nlinarith

lemma s_le_one {r : ℝ} (hr : r ∈ Ioc 0 S.R) : S.s r ≤ 1 := by
  have h1 := s_sq hr
  have h2 := u_pos hr
  have h3 := s_pos' hr
  nlinarith

/-! ### Logarithmic-radius TOV flow in Bondi variables -/

lemma hasDerivAt_u {x : ℝ} (hx : x ∈ Ioc 0 S.R) (hj : x ∉ S.jumps) :
    HasDerivAt S.u ((S.piE x - S.u x) / x) x := by
  have h := (S.hasDerivAt_m x hx hj).div (hasDerivAt_id x) hx.1.ne'
  have hx0 : x ≠ 0 := hx.1.ne'
  refine (h.congr_of_eventuallyEq (Eventually.of_forall fun _ => rfl)).congr_deriv ?_
  simp only [piE, u, id]
  field_simp

lemma hasDerivAt_piP {x : ℝ} (hx : x ∈ Ioc 0 S.R) (hj : x ∉ S.jumps) :
    HasDerivAt S.piP (rhsP (S.u x) (S.s x) (S.piE x) (S.piP x) / x) x := by
  have h := ((hasDerivAt_pow 2 x).const_mul (4 * π)).mul (S.hasDerivAt_p x hx hj)
  have hx0 : x ≠ 0 := hx.1.ne'
  have hs0 : S.s x ≠ 0 := (s_pos' hx).ne'
  have hs0' : sFun S.m x ≠ 0 := hs0
  refine (h.congr_of_eventuallyEq (Eventually.of_forall fun _ => rfl)).congr_deriv ?_
  simp only [rhsP, u, piE, piP, s]
  field_simp
  ring

lemma hasDerivAt_s {x : ℝ} (hx : x ∈ Ioc 0 S.R) (hj : x ∉ S.jumps) :
    HasDerivAt S.s (rhsS (S.u x) (S.s x) (S.piE x) / x) x := by
  have hx0 : x ≠ 0 := hx.1.ne'
  have hin := (((S.hasDerivAt_m x hx hj).const_mul 2).div (hasDerivAt_id x) hx0).const_sub 1
  have h := hin.sqrt (arg_pos hx).ne'
  have hs0 : Real.sqrt (1 - 2 * S.m x / x) ≠ 0 := (s_pos' hx).ne'
  refine (h.congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)).congr_deriv ?_
  · simp only [s, sFun, Pi.div_apply, id, mul_div_assoc]
  · simp only [rhsS, u, piE, s, sFun, Pi.div_apply, id]
    field_simp
    ring

lemma hasDerivAt_Z' {x : ℝ} (hx : x ∈ Ioc 0 S.R) (hj : x ∉ S.jumps) :
    HasDerivAt S.Z (rhsZ (S.u x) (S.s x) (S.piE x) (S.piP x) (S.Z x) / x) x :=
  S.hasDerivAt_Z x hx hj

/-! ### Continuity on `(0, R]` (across interfaces) -/

lemma continuousOn_u : ContinuousOn S.u (Ioc 0 S.R) := by
  unfold u
  exact S.continuousOn_m.div continuousOn_id (fun x hx => hx.1.ne')

lemma continuousOn_piP : ContinuousOn S.piP (Ioc 0 S.R) := by
  unfold piP
  exact (continuousOn_const.mul (continuousOn_pow 2)).mul S.continuousOn_p

lemma continuousOn_s : ContinuousOn S.s (Ioc 0 S.R) := by
  unfold s sFun
  exact (continuousOn_const.sub ((continuousOn_const.mul S.continuousOn_m).div continuousOn_id
    (fun x hx => hx.1.ne'))).sqrt

/-- One barrier piece: if the trajectory touches `v = B(u)` at `x`, it was strictly above the
curve just before `x` (the barrier is crossed only downward). The touching point `x` may be a
density jump: we use the TOV flow only on a punctured left neighbourhood of `x`, where the
strict barrier inequalities persist by continuity of `(u, v)`. -/
lemma piece_left {B Bd : ℝ → ℝ} (hB : ∀ z, HasDerivAt B (Bd z) z) (hBd : Continuous Bd)
    {x : ℝ} (hx : x ∈ Ioc 0 S.R) (hv : S.piP x = B (S.u x)) (hcore : Fcore B Bd (S.u x) < 0)
    (hconst : Fconst B Bd (S.u x) < 0) :
    ∀ᶠ y in 𝓝[<] x, 0 < S.piP y - B (S.u y) := by
  have hBc : Continuous B := continuous_iff_continuousAt.2 fun z => (hB z).continuousAt
  have huv := (tendsto_left_of_Ioc (continuousOn_u (S := S)) hx).prodMk_nhds
    (tendsto_left_of_Ioc (continuousOn_piP (S := S)) hx)
  have hΦc : Continuous (fun q : ℝ × ℝ =>
      (1 - 2 * q.1) * (2 * q.2 + (q.1 - q.2) * Bd q.1) - 2 * q.2 * (q.1 + q.2)) := by
    fun_prop
  have hΦk : Continuous (fun q : ℝ × ℝ =>
      (1 - 2 * q.1) * (2 * q.2 - 2 * q.1 * Bd q.1) - (3 * q.1 + q.2) * (q.1 + q.2)) := by
    fun_prop
  have hc0 : (1 - 2 * S.u x) * (2 * S.piP x + (S.u x - S.piP x) * Bd (S.u x))
      - 2 * S.piP x * (S.u x + S.piP x) < 0 := by
    rw [hv]; simpa [Fcore] using hcore
  have hk0 : (1 - 2 * S.u x) * (2 * S.piP x - 2 * S.u x * Bd (S.u x))
      - (3 * S.u x + S.piP x) * (S.u x + S.piP x) < 0 := by
    rw [hv]; simpa [Fconst] using hconst
  have evc := ((hΦc.tendsto _).comp huv).eventually (gt_mem_nhds hc0)
  have evk := ((hΦk.tendsto _).comp huv).eventually (gt_mem_nhds hk0)
  refine pos_left_of_eventually_deriv_neg (half_lt_self hx.1) ?_ ?_ (by simp [hv])
    (f' := fun y => rhsP (S.u y) (S.s y) (S.piE y) (S.piP y) / y
      - Bd (S.u y) * ((S.piE y - S.u y) / y))
  · exact ((continuousOn_piP (S := S)).sub (hBc.comp_continuousOn (continuousOn_u (S := S)))).mono
      (fun y hy => ⟨(half_pos hx.1).trans_le hy.1, hy.2.trans hx.2⟩)
  · filter_upwards [evc, evk, eventually_notMem_left S.jumps x, Ioo_mem_nhdsLT hx.1]
      with y hc hk hj hy0
    have hy : y ∈ Ioc 0 S.R := ⟨hy0.1, hy0.2.le.trans hx.2⟩
    refine ⟨(hasDerivAt_piP hy hj).sub ((hB (S.u y)).comp y (hasDerivAt_u hy hj)), ?_⟩
    have hk' := kernelB (one_sub_two_u_pos hy) (piP_le_piE hy) (piE_le_three_u hy) hc hk
    have e : rhsP (S.u y) (S.s y) (S.piE y) (S.piP y) / y - Bd (S.u y) * ((S.piE y - S.u y) / y)
        = ((2 * S.piP y - (S.piE y + S.piP y) * (S.u y + S.piP y) / (1 - 2 * S.u y))
            - Bd (S.u y) * (S.piE y - S.u y)) / y := by
      rw [rhsP, s_sq hy]; ring
    show rhsP (S.u y) (S.s y) (S.piE y) (S.piP y) / y - Bd (S.u y) * ((S.piE y - S.u y) / y) < 0
    rw [e]
    exact div_neg_of_neg_of_pos hk' hy0.1

/-- At a touching point of the glued barrier the trajectory was strictly above it just before. -/
lemma glued_left {x : ℝ} (hx : x ∈ Ioc 0 S.R) (h0 : S.piP x = Bpw (S.u x)) :
    ∀ᶠ y in 𝓝[<] x, 0 < S.piP y - Bpw (S.u y) := by
  have hu0 := u_pos hx
  have hcu := tendsto_left_of_Ioc (continuousOn_u (S := S)) hx
  rcases lt_trichotomy (S.u x) (49 / 200) with hlt | heq | hgt
  · have h1 : S.piP x = B1 (S.u x) := by rw [h0, Bpw, ite_eq_left hlt.le]
    have hev : ∀ᶠ y in 𝓝[<] x, S.u y < 49 / 200 := hcu.eventually (gt_mem_nhds hlt)
    filter_upwards [piece_left hasDerivAt_B1 continuous_B1d hx h1 (B1_core hu0 hlt.le)
      (B1_const hu0 hlt.le), hev] with y hy1 hy2
    rw [Bpw, ite_eq_left hy2.le]; exact hy1
  · have h1 : S.piP x = B1 (S.u x) := by rw [h0, Bpw, ite_eq_left heq.le]
    have h2 : S.piP x = B2 (S.u x) := by rw [h1, heq, B1_eq_B2]
    have hev : ∀ᶠ y in 𝓝[<] x, S.u y < 51 / 125 :=
      hcu.eventually (gt_mem_nhds (by rw [heq]; norm_num))
    filter_upwards [piece_left hasDerivAt_B1 continuous_B1d hx h1 (B1_core hu0 heq.le)
        (B1_const hu0 heq.le),
      piece_left hasDerivAt_B2 continuous_B2d hx h2 (B2_core heq.ge (by rw [heq]; norm_num))
        (B2_const heq.ge (by rw [heq]; norm_num)),
      hev] with y hy1 hy2 hy3
    unfold Bpw
    split_ifs
    · exact hy1
    · rw [min_eq_left hy3.le]; exact hy2
  · have hlt : S.u x < 51 / 125 := by
      by_contra hc
      push Not at hc
      have : Bpw (S.u x) = B2 (51 / 125) := by
        rw [Bpw, ite_eq_right (not_le.2 hgt), min_eq_right hc]
      have := piP_nonneg hx
      linarith [B2_wall_neg, h0 ▸ this]
    have h2 : S.piP x = B2 (S.u x) := by
      rw [h0, Bpw, ite_eq_right (not_le.2 hgt), min_eq_left hlt.le]
    have hev1 : ∀ᶠ y in 𝓝[<] x, 49 / 200 < S.u y := hcu.eventually (lt_mem_nhds hgt)
    have hev2 : ∀ᶠ y in 𝓝[<] x, S.u y < 51 / 125 := hcu.eventually (gt_mem_nhds hlt)
    filter_upwards [piece_left hasDerivAt_B2 continuous_B2d hx h2 (B2_core hgt.le hlt.le)
        (B2_const hgt.le hlt.le), hev1, hev2]
      with y hy1 hy2 hy3
    rw [Bpw, ite_eq_right (not_le.2 hy2), min_eq_left hy3.le]; exact hy1

/-- **Part B (Bondi–Pontryagin compactness wall, `N40`, `w = 1`).** Every (piecewise-smooth,
density jumps allowed) monotone isotropic DEC star satisfies `m(r)/r < 51/125` on `(0, R]`. -/
theorem compactness_wall (S : MonotoneIsotropicDECStar) :
    ∀ r ∈ Ioc 0 S.R, S.m r / r < 51 / 125 := by
  intro r hr
  have hev : ∀ᶠ y in 𝓝[>] (0 : ℝ), S.m y / y < 1 / 200 :=
    S.center_u.eventually (gt_mem_nhds (by norm_num))
  obtain ⟨a, ha1, ha2⟩ := (hev.and (Ioo_mem_nhdsGT hr.1)).exists
  have ha : a ∈ Ioc 0 S.R := ⟨ha2.1, ha2.2.le.trans hr.2⟩
  set g : ℝ → ℝ := fun y => S.piP y - Bpw (S.u y) with hg
  have hcont : ContinuousOn g (Icc a S.R) :=
    ((continuousOn_piP (S := S)).sub (continuous_Bpw.comp_continuousOn
      (continuousOn_u (S := S)))).mono (fun y hy => ⟨ha.1.trans_le hy.1, hy.2⟩)
  have hga : g a < 0 := by
    have hua : S.u a < 1 / 200 := ha1
    have h1 : S.piP a ≤ 3 * S.u a := (piP_le_piE ha).trans (piE_le_three_u ha)
    have h2 := B1_gt_three_mul (u_pos ha) hua.le
    have h3 : Bpw (S.u a) = B1 (S.u a) := by rw [Bpw, ite_eq_left (by linarith)]
    simp only [hg, h3]; linarith
  have hneg := first_crossing hcont hga (fun x hx hgx =>
    glued_left ⟨ha.1.trans hx.1, hx.2⟩ (by simp only [hg] at hgx; linarith))
  have hgr : g r < 0 := hneg r ⟨ha2.2.le, hr.2⟩
  have hpos : 0 < Bpw (S.u r) := by
    have := piP_nonneg hr; simp only [hg] at hgr; linarith
  by_contra hc
  push Not at hc
  have hc' : (51 / 125 : ℝ) ≤ S.u r := hc
  have : Bpw (S.u r) = B2 (51 / 125) := by
    rw [Bpw, ite_eq_right (by linarith), min_eq_right hc']
  linarith [B2_wall_neg]

/-- Corollary of the wall: `23/125 < s(r)²` on `(0, R]`. -/
theorem s_sq_gt (S : MonotoneIsotropicDECStar) :
    ∀ r ∈ Ioc 0 S.R, 23 / 125 < S.s r ^ 2 := by
  intro r hr
  rw [s_sq hr]
  have : S.u r < 51 / 125 := S.compactness_wall r hr
  linarith

/-! ## Part C — the `α = 69/100` Kerr barrier and the headline theorems

The barrier argument is carried out once for an arbitrary level `Ī₀` satisfying the sign
conditions collected in `KerrBarrierLevel`, namely positivity of the denominator
`4 − Ī₀ (1 − t)³` and of the two Riccati numerators `N_e`, `N_e + N_p (4 − Ī₀ (1 − t)³)` on the
compactness window `t = s² ∈ [23/125, 1]`. The general statement
`kerr_inertia_gt_of_level` gives `I > Ī₀ M³` for every such level. It is instantiated at
`Ī₀ = 4` (the Kerr value, `kerrBarrierLevel_four`) and at `Ī₀ = 1001/250`
(`kerrBarrierLevel_gap`), the latter giving a uniform positive gap above the Kerr value. -/

/-- The exact positivity factorisation: `−N_e(69/100, 4, t) = (4/25) t² e₅(t)`. -/
lemma NumE_eq (t : ℝ) : NumE (69 / 100) 4 t = 4 / 25 * t ^ 2 * e5 t := by
  unfold NumE e5; ring

/-- `−N_e − N_p (4 − 4(1−t)³) = (8/25) t³ s₄(t)` at `α = 69/100`, `Ī₀ = 4`. -/
lemma NumEP_eq (t : ℝ) :
    NumE (69 / 100) 4 t + NumP (69 / 100) 4 t * (4 - 4 * (1 - t) ^ 3) = 8 / 25 * t ^ 3 * s4 t := by
  unfold NumE NumP s4; ring

lemma den_pos {s : ℝ} (h0 : 0 < s) (h1 : s ≤ 1) : 0 < 4 - 4 * (1 - s ^ 2) ^ 3 := by
  have ha : 0 ≤ 1 - s ^ 2 := by nlinarith
  have hb : 1 - s ^ 2 < 1 := by nlinarith
  have : (1 - s ^ 2) ^ 3 < 1 := pow_lt_one₀ ha hb (by norm_num)
  linarith

lemma Zc_nonneg {s : ℝ} (h0 : 0 < s) (h1 : s ≤ 1) : 0 ≤ Zc 4 s := by
  unfold Zc
  have ha : 0 ≤ 1 - s ^ 2 := by nlinarith
  exact div_nonneg (by positivity) (den_pos h0 h1).le

/-- `c_e > 0` on `t = s² ∈ [23/125, 1]`. -/
lemma cE_pos {s : ℝ} (h0 : 0 < s) (h1 : s ≤ 1) (ht : 23 / 125 ≤ s ^ 2) :
    0 < cE (69 / 100) 4 s := by
  unfold cE
  rw [NumE_eq]
  have := e5_pos (s ^ 2) ht (by nlinarith)
  have := den_pos h0 h1
  positivity

/-- `c_e + c_p > 0` on `t = s² ∈ [23/125, 1]`. -/
lemma cE_add_cP_pos {s : ℝ} (h0 : 0 < s) (h1 : s ≤ 1) (ht : 23 / 125 ≤ s ^ 2) :
    0 < cE (69 / 100) 4 s + cP (69 / 100) 4 s := by
  have hd := den_pos h0 h1
  have e : cE (69 / 100) 4 s + cP (69 / 100) 4 s
      = (8 / 25 * (s ^ 2) ^ 3 * s4 (s ^ 2)) / (s ^ 3 * (4 - 4 * (1 - s ^ 2) ^ 3) ^ 2) := by
    rw [← NumEP_eq]
    unfold cE cP
    field_simp
  rw [e]
  have := s4_pos (s ^ 2) ht (by nlinarith)
  positivity

/-- Sign conditions on a level `Ī₀` under which the `α = 69/100` Kerr barrier closes on the
compactness window `t = s² ∈ [23/125, 1]`. -/
structure KerrBarrierLevel (I₀ : ℝ) : Prop where
  nonneg : 0 ≤ I₀
  den : ∀ t : ℝ, 23 / 125 ≤ t → t ≤ 1 → 0 < 4 - I₀ * (1 - t) ^ 3
  numE : ∀ t : ℝ, 23 / 125 ≤ t → t ≤ 1 → 0 < NumE (69 / 100) I₀ t
  numEP : ∀ t : ℝ, 23 / 125 ≤ t → t ≤ 1 →
    0 < NumE (69 / 100) I₀ t + NumP (69 / 100) I₀ t * (4 - I₀ * (1 - t) ^ 3)

/-- The Kerr value `Ī₀ = 4` is an admissible barrier level. -/
lemma kerrBarrierLevel_four : KerrBarrierLevel 4 where
  nonneg := by norm_num
  den t h₁ h₂ := by
    have ha : 0 ≤ 1 - t := by linarith
    have hb : 1 - t < 1 := by linarith
    have : (1 - t) ^ 3 < 1 := pow_lt_one₀ ha hb (by norm_num)
    linarith
  numE t h₁ h₂ := by
    rw [NumE_eq]
    have := e5_pos t h₁ h₂
    have : 0 < t := by linarith
    positivity
  numEP t h₁ h₂ := by
    rw [NumEP_eq]
    have := s4_pos t h₁ h₂
    have : 0 < t := by linarith
    positivity

/-- The level `Ī₀ = 1001/250 = 4.004` is an admissible barrier level: the denominator is
bounded below by `4 − (1001/250)(102/125)³ > 0`, and both numerators coincide with the
certified polynomials `e7`, `s7`. -/
lemma kerrBarrierLevel_gap : KerrBarrierLevel (1001 / 250) where
  nonneg := by norm_num
  den t h₁ h₂ := by
    have ha : 0 ≤ 1 - t := by linarith
    have hb : 1 - t ≤ 102 / 125 := by linarith
    have : (1 - t) ^ 3 ≤ (102 / 125) ^ 3 := pow_le_pow_left₀ ha hb 3
    norm_num at this ⊢
    linarith
  numE t h₁ h₂ := by
    have e : NumE (69 / 100) (1001 / 250) t = e7 t := by unfold NumE e7; ring
    rw [e]; exact e7_pos t h₁ h₂
  numEP t h₁ h₂ := by
    have e : NumE (69 / 100) (1001 / 250) t
        + NumP (69 / 100) (1001 / 250) t * (4 - 1001 / 250 * (1 - t) ^ 3) = s7 t := by
      unfold NumE NumP s7; ring
    rw [e]; exact s7_pos t h₁ h₂

lemma level_den_pos {I₀ : ℝ} (hI : KerrBarrierLevel I₀) {s : ℝ} (h0 : 0 < s) (h1 : s ≤ 1)
    (ht : 23 / 125 ≤ s ^ 2) : 0 < 4 - I₀ * (1 - s ^ 2) ^ 3 :=
  hI.den _ ht (by nlinarith)

lemma level_Zc_nonneg {I₀ : ℝ} (hI : KerrBarrierLevel I₀) {s : ℝ} (h0 : 0 < s) (h1 : s ≤ 1)
    (ht : 23 / 125 ≤ s ^ 2) : 0 ≤ Zc I₀ s := by
  unfold Zc
  have ha : 0 ≤ 1 - s ^ 2 := by nlinarith
  have hI0 := hI.nonneg
  exact div_nonneg (by positivity) (level_den_pos hI h0 h1 ht).le

/-- `c_e > 0` on `t = s² ∈ [23/125, 1]` at an admissible level. -/
lemma level_cE_pos {I₀ : ℝ} (hI : KerrBarrierLevel I₀) {s : ℝ} (h0 : 0 < s) (h1 : s ≤ 1)
    (ht : 23 / 125 ≤ s ^ 2) : 0 < cE (69 / 100) I₀ s := by
  unfold cE
  exact div_pos (hI.numE _ ht (by nlinarith))
    (mul_pos (pow_pos h0 3) (pow_pos (level_den_pos hI h0 h1 ht) 2))

/-- `c_e + c_p > 0` on `t = s² ∈ [23/125, 1]` at an admissible level. -/
lemma level_cE_add_cP_pos {I₀ : ℝ} (hI : KerrBarrierLevel I₀) {s : ℝ} (h0 : 0 < s)
    (h1 : s ≤ 1) (ht : 23 / 125 ≤ s ^ 2) : 0 < cE (69 / 100) I₀ s + cP (69 / 100) I₀ s := by
  have hd := level_den_pos hI h0 h1 ht
  have e : cE (69 / 100) I₀ s + cP (69 / 100) I₀ s
      = (NumE (69 / 100) I₀ (s ^ 2)
          + NumP (69 / 100) I₀ (s ^ 2) * (4 - I₀ * (1 - s ^ 2) ^ 3))
        / (s ^ 3 * (4 - I₀ * (1 - s ^ 2) ^ 3) ^ 2) := by
    unfold cE cP
    field_simp
  rw [e]
  exact div_pos (hI.numEP _ ht (by nlinarith)) (mul_pos (pow_pos h0 3) (pow_pos hd 2))

/-- The Riccati residual is nonnegative under isotropic DEC, positive where `π_e > 0`. -/
lemma res_lower {ce cp cpp e v : ℝ} (hce : 0 < ce) (hs : 0 < ce + cp) (hcpp : 0 ≤ cpp)
    (hv : 0 ≤ v) (hve : v ≤ e) :
    0 ≤ ce * e + cp * v + cpp * v ^ 2 ∧ (0 < e → 0 < ce * e + cp * v + cpp * v ^ 2) := by
  have hq : 0 ≤ cpp * v ^ 2 := mul_nonneg hcpp (sq_nonneg v)
  rcases le_or_gt 0 cp with hcp | hcp
  · have h1 : 0 ≤ cp * v := mul_nonneg hcp hv
    refine ⟨by nlinarith, fun he => by nlinarith⟩
  · have h1 : cp * e ≤ cp * v := mul_le_mul_of_nonpos_left hve hcp.le
    refine ⟨by nlinarith, fun he => by nlinarith⟩

/-- Upper bound on the linear Riccati coefficient near a regular centre. -/
lemma L_bound {u s pp Z W zc : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (hs2 : s ^ 2 = 1 - 2 * u)
    (hu : u ≤ 1 / 8) (hpp : 0 ≤ pp) (hZ : -1 / 8 ≤ Z) (hzc : 0 ≤ zc)
    (hW : W = Z - 2 * (69 / 100) * pp / s) :
    -(W + zc) / s + (u + (1 - 4 * (69 / 100)) * pp) / s ^ 2 - 3 ≤ -2 := by
  have e : -(W + zc) / s + (u + (1 - 4 * (69 / 100)) * pp) / s ^ 2
      = (-(Z * s) - zc * s + u + (1 - 2 * (69 / 100)) * pp) / s ^ 2 := by
    rw [hW]; field_simp; ring
  rw [e]
  have hnum : -(Z * s) - zc * s + u + (1 - 2 * (69 / 100)) * pp ≤ s ^ 2 := by
    have h1 : -(Z * s) ≤ s / 8 := by nlinarith
    have h2 : 0 ≤ zc * s := mul_nonneg hzc hs.le
    nlinarith
  have := (div_le_one (pow_pos hs 2)).2 hnum
  linarith

variable (S) in
/-- Shifted Hartle variable `W_α = Z − 2α π_p / s` at `α = 69/100`. -/
noncomputable def W (r : ℝ) : ℝ := S.Z r - 2 * (69 / 100) * S.piP r / S.s r

variable (S) in
/-- Distance to the Schwarzschild vacuum curve `Z_c(s)` with `Ī₀ = I/M³ = 4` (Kerr). -/
noncomputable def D (r : ℝ) : ℝ := S.W r - Zc 4 (S.s r)

variable (S) in
/-- `D'(r)`. -/
noncomputable def Dd (r : ℝ) : ℝ :=
  rhsD (69 / 100) 4 (S.u r) (S.s r) (S.piE r) (S.piP r) (S.W r) / r

variable (S) in
/-- Linear Riccati coefficient along the trajectory. -/
noncomputable def Lf (r : ℝ) : ℝ := Lco (69 / 100) 4 (S.u r) (S.s r) (S.piP r) (S.W r)

variable (S) in
/-- Riccati residual along the trajectory. -/
noncomputable def Res (r : ℝ) : ℝ :=
  cE (69 / 100) 4 (S.s r) * S.piE r + cP (69 / 100) 4 (S.s r) * S.piP r
    + cPP (69 / 100) (S.s r) * S.piP r ^ 2

variable (S) in
/-- Distance to the Schwarzschild vacuum curve `Z_c(s)` at a general level `Ī₀`. -/
noncomputable def DI (I₀ r : ℝ) : ℝ := S.W r - Zc I₀ (S.s r)

variable (S) in
/-- `∂_r DI(Ī₀, r)`. -/
noncomputable def DdI (I₀ r : ℝ) : ℝ :=
  rhsD (69 / 100) I₀ (S.u r) (S.s r) (S.piE r) (S.piP r) (S.W r) / r

variable (S) in
/-- Linear Riccati coefficient along the trajectory at level `Ī₀`. -/
noncomputable def LfI (I₀ r : ℝ) : ℝ := Lco (69 / 100) I₀ (S.u r) (S.s r) (S.piP r) (S.W r)

variable (S) in
/-- Riccati residual along the trajectory at level `Ī₀`. -/
noncomputable def ResI (I₀ r : ℝ) : ℝ :=
  cE (69 / 100) I₀ (S.s r) * S.piE r + cP (69 / 100) I₀ (S.s r) * S.piP r
    + cPP (69 / 100) (S.s r) * S.piP r ^ 2

lemma hasDerivAt_W {x : ℝ} (hx : x ∈ Ioc 0 S.R) (hj : x ∉ S.jumps) :
    HasDerivAt S.W (rhsZ (S.u x) (S.s x) (S.piE x) (S.piP x) (S.Z x) / x
      - (2 * (69 / 100) * (rhsP (S.u x) (S.s x) (S.piE x) (S.piP x) / x) * S.s x
        - 2 * (69 / 100) * S.piP x * (rhsS (S.u x) (S.s x) (S.piE x) / x)) / S.s x ^ 2) x :=
  (hasDerivAt_Z' hx hj).sub (((hasDerivAt_piP hx hj).const_mul (2 * (69 / 100))).div
    (hasDerivAt_s hx hj) (s_pos' hx).ne')

lemma continuousOn_W : ContinuousOn S.W (Ioc 0 S.R) := by
  unfold W
  exact S.continuousOn_Z.sub ((continuousOn_const.mul (continuousOn_piP (S := S))).div
    (continuousOn_s (S := S)) (fun x hx => (s_pos' hx).ne'))

lemma tendsto_s : Tendsto S.s (𝓝[>] 0) (𝓝 1) := by
  have h : Tendsto (fun y => 1 - 2 * (S.m y / y)) (𝓝[>] 0) (𝓝 (1 - 2 * 0)) :=
    tendsto_const_nhds.sub (S.center_u.const_mul 2)
  have h2 := (Real.continuous_sqrt.tendsto _).comp h
  simp only [mul_zero, sub_zero, Real.sqrt_one] at h2
  refine h2.congr (fun y => ?_)
  simp [s, sFun, mul_div_assoc]

lemma tendsto_W : Tendsto S.W (𝓝[>] 0) (𝓝 0) := by
  have h := S.center_Z.sub ((S.center_p.const_mul (2 * (69 / 100))).div (tendsto_s (S := S)) one_ne_zero)
  simp only [mul_zero, zero_div, sub_zero] at h
  exact h

/-- C3: the density is somewhere positive in any initial segment. -/
lemma exists_eps_pos {a : ℝ} (ha : 0 < a) (haR : a ≤ S.R) (hj : ∀ r ∈ Ioc 0 a, r ∉ S.jumps) :
    ∃ r ∈ Ioo 0 a, 0 < S.ε r := by
  by_contra hcon
  push Not at hcon
  have hcont : ContinuousOn S.m (Icc 0 a) :=
    continuousOn_m_of_center haR S.continuousOn_m S.m_zero S.center_u
  have hanti : AntitoneOn S.m (Icc 0 a) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 a) hcont
      (f' := fun y => 4 * π * y ^ 2 * S.ε y) ?_ ?_
    · intro y hy
      rw [interior_Icc] at hy
      exact (S.hasDerivAt_m y ⟨hy.1, hy.2.le.trans haR⟩ (hj y ⟨hy.1, hy.2.le⟩)).hasDerivWithinAt
    · intro y hy
      rw [interior_Icc] at hy
      have := hcon y hy
      have h4 : 0 ≤ 4 * π * y ^ 2 := by positivity
      exact mul_nonpos_of_nonneg_of_nonpos h4 this
  have := hanti ⟨le_rfl, ha.le⟩ ⟨ha.le, le_rfl⟩ ha.le
  rw [S.m_zero] at this
  linarith [m_pos (S := S) ⟨ha, haR⟩]

/-! ### The barrier argument at a general admissible level `Ī₀` -/

lemma tendsto_DI (I₀ : ℝ) : Tendsto (S.DI I₀) (𝓝[>] 0) (𝓝 0) := by
  have hc : ContinuousAt (Zc I₀) 1 :=
    (hasDerivAt_Zc I₀ 1 (by norm_num)).continuousAt
  have h := (tendsto_W (S := S)).sub ((hc.tendsto).comp (tendsto_s (S := S)))
  have h0 : Zc I₀ 1 = 0 := by norm_num [Zc]
  rw [h0, sub_zero] at h
  exact h

section Level

variable {I₀ : ℝ} (hI : KerrBarrierLevel I₀)
include hI

lemma level_den_ne {x : ℝ} (hx : x ∈ Ioc 0 S.R) : 4 - I₀ * (1 - S.s x ^ 2) ^ 3 ≠ 0 :=
  (level_den_pos hI (s_pos' hx) (s_le_one hx) (S.s_sq_gt x hx).le).ne'

lemma hasDerivAt_DI {x : ℝ} (hx : x ∈ Ioc 0 S.R) (hj : x ∉ S.jumps) :
    HasDerivAt (S.DI I₀) (S.DdI I₀ x) x := by
  have h := (hasDerivAt_W hx hj).sub
    ((hasDerivAt_Zc I₀ (S.s x) (level_den_ne hI hx)).comp x (hasDerivAt_s hx hj))
  refine h.congr_deriv ?_
  have hx0 : x ≠ 0 := hx.1.ne'
  have hs0 : S.s x ≠ 0 := (s_pos' hx).ne'
  have hZW : S.W x + 2 * (69 / 100) * S.piP x / S.s x = S.Z x := by
    unfold W; ring
  unfold DdI rhsD
  rw [hZW]
  field_simp

lemma continuousOn_DI : ContinuousOn (S.DI I₀) (Ioc 0 S.R) := by
  have hZc : ContinuousOn (fun r => Zc I₀ (S.s r)) (Ioc 0 S.R) := fun y hy =>
    (hasDerivAt_Zc I₀ (S.s y) (level_den_ne hI hy)).continuousAt.comp_continuousWithinAt
      (continuousOn_s (S := S) y hy)
  exact (continuousOn_W (S := S)).sub hZc

/-- The exact Part-A identity along the star at level `Ī₀`: `r D' = L D + Res`. -/
lemma r_DdI {x : ℝ} (hx : x ∈ Ioc 0 S.R) :
    x * S.DdI I₀ x = S.LfI I₀ x * S.DI I₀ x + S.ResI I₀ x := by
  have hx0 : x ≠ 0 := hx.1.ne'
  have := partA (69 / 100) I₀ (S.u x) (S.s x) (S.piE x) (S.piP x) (S.W x) (s_pos' hx).ne'
    (level_den_ne hI hx) (s_sq hx)
  unfold DdI LfI DI ResI
  rw [mul_div_cancel₀ _ hx0, this]
  ring

lemma level_res_facts {x : ℝ} (hx : x ∈ Ioc 0 S.R) :
    0 ≤ S.ResI I₀ x ∧ (0 < S.piE x → 0 < S.ResI I₀ x) := by
  have h0 := s_pos' hx
  have h1 := s_le_one hx
  have ht : 23 / 125 ≤ S.s x ^ 2 := (S.s_sq_gt x hx).le
  exact res_lower (level_cE_pos hI h0 h1 ht) (level_cE_add_cP_pos hI h0 h1 ht)
    (show 0 ≤ cPP (69 / 100) (S.s x) by unfold cPP; have := h0; positivity) (piP_nonneg hx) (piP_le_piE hx)

/-- Near the centre the linear Riccati coefficient satisfies `L ≤ −2`, on an initial segment
`(0, a]` free of interfaces. -/
lemma exists_LI_le : ∃ a, 0 < a ∧ a ≤ S.R ∧ (∀ r ∈ Ioc 0 a, r ∉ S.jumps) ∧
    ∀ r ∈ Ioc 0 a, S.LfI I₀ r ≤ -2 := by
  have h1 : ∀ᶠ y in 𝓝[>] (0 : ℝ), S.m y / y < 1 / 8 :=
    S.center_u.eventually (gt_mem_nhds (by norm_num))
  have h2 : ∀ᶠ y in 𝓝[>] (0 : ℝ), -1 / 8 < S.Z y :=
    S.center_Z.eventually (lt_mem_nhds (by norm_num))
  have h3 : ∀ᶠ y in 𝓝[>] (0 : ℝ), y ∈ Ioo 0 S.R := Ioo_mem_nhdsGT S.R_pos
  have h4 : ∀ᶠ y in 𝓝[>] (0 : ℝ), y ∉ S.jumps := eventually_notMem_right S.jumps 0
  obtain ⟨b, hb, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 (h1.and (h2.and (h3.and h4)))
  refine ⟨b / 2, by linarith [mem_Ioi.1 hb], ?_, ?_, ?_⟩
  · have hb0 : 0 < b := hb
    have := (hsub (show b / 2 ∈ Ioo 0 b from ⟨by linarith, by linarith⟩)).2.2.1
    exact this.2.le
  · intro r hr
    exact (hsub (show r ∈ Ioo 0 b from ⟨hr.1, by linarith [hr.2, mem_Ioi.1 hb]⟩)).2.2.2
  · intro r hr
    have hrb : r ∈ Ioo 0 b := ⟨hr.1, by linarith [hr.2, mem_Ioi.1 hb]⟩
    obtain ⟨hu, hZ, hR, -⟩ := hsub hrb
    have hr' : r ∈ Ioc 0 S.R := ⟨hR.1, hR.2.le⟩
    exact L_bound (s_pos' hr') (s_le_one hr') (s_sq hr') hu.le (piP_nonneg hr') hZ.le
      (level_Zc_nonneg hI (s_pos' hr') (s_le_one hr') (S.s_sq_gt r hr').le) rfl

lemma continuousAt_DI {x : ℝ} (hx : x ∈ Ioc 0 S.R) (hj : x ∉ S.jumps) :
    ContinuousAt (S.DI I₀) x :=
  (hasDerivAt_DI hI hx hj).continuousAt

/-- `D ≥ 0` near the centre (comparison with `r² D`, using `L ≤ −2` and `Res ≥ 0`). -/
lemma DI_nonneg_near_center {a : ℝ} (haR : a ≤ S.R) (hj : ∀ r ∈ Ioc 0 a, r ∉ S.jumps)
    (hL : ∀ r ∈ Ioc 0 a, S.LfI I₀ r ≤ -2) : ∀ x ∈ Ioc 0 a, 0 ≤ S.DI I₀ x := by
  intro x hx
  by_contra hneg
  push Not at hneg
  have hxR : x ∈ Ioc 0 S.R := ⟨hx.1, hx.2.trans haR⟩
  set f : ℝ → ℝ := fun y => y ^ 2 * S.DI I₀ y with hf
  have hfx : f x < 0 := by
    simp only [hf]; exact mul_neg_of_pos_of_neg (pow_pos hx.1 2) hneg
  have hlim : Tendsto f (𝓝[>] 0) (𝓝 0) := by
    have hsq : Tendsto (fun y : ℝ => y ^ 2) (𝓝[>] 0) (𝓝 0) := by
      have := ((continuous_pow 2).tendsto (0 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
      simpa using this
    simpa using hsq.mul (tendsto_DI (S := S) I₀)
  have hev : ∀ᶠ y in 𝓝[>] (0 : ℝ), f x < f y := hlim.eventually (lt_mem_nhds hfx)
  obtain ⟨b, hb1, hb2⟩ := (hev.and (Ioo_mem_nhdsGT hx.1)).exists
  have hsub : ∀ y ∈ Icc b x, y ∈ Ioc 0 S.R := fun y hy => ⟨hb2.1.trans_le hy.1, hy.2.trans hxR.2⟩
  have hsj : ∀ y ∈ Icc b x, y ∉ S.jumps := fun y hy => hj y ⟨hb2.1.trans_le hy.1, hy.2.trans hx.2⟩
  refine no_rise_to_left (f' := fun y => 2 * y * S.DI I₀ y + y ^ 2 * S.DdI I₀ y) hb2.2.le ?_
    hb1 hfx ?_ ?_
  · intro y hy
    exact ((continuousAt_id.pow 2).mul
      (continuousAt_DI hI (hsub y hy) (hsj y hy))).continuousWithinAt
  · intro y hy
    have hy' := hsub y ⟨hy.1.le, hy.2.le⟩
    have := (hasDerivAt_pow 2 y).mul (hasDerivAt_DI hI hy' (hsj y ⟨hy.1.le, hy.2.le⟩))
    refine this.congr_deriv ?_
    push_cast; ring
  · intro y hy hfy
    have hy' := hsub y ⟨hy.1.le, hy.2.le⟩
    have hya : y ∈ Ioc 0 a := ⟨hy'.1, hy.2.le.trans hx.2⟩
    have hy0 := hy'.1
    have hDy : S.DI I₀ y < 0 := by
      simp only [hf] at hfy
      exact neg_of_mul_neg_right hfy (sq_nonneg y)
    have hrd := r_DdI hI hy'
    have hres := (level_res_facts hI hy').1
    have hLy := hL y hya
    have e : 2 * y * S.DI I₀ y + y ^ 2 * S.DdI I₀ y
        = y * ((2 + S.LfI I₀ y) * S.DI I₀ y + S.ResI I₀ y) := by
      have : y ^ 2 * S.DdI I₀ y = y * (y * S.DdI I₀ y) := by ring
      rw [this, hrd]; ring
    rw [e]
    apply mul_nonneg hy0.le
    have : 0 ≤ (2 + S.LfI I₀ y) * S.DI I₀ y := mul_nonneg_of_nonpos_of_nonpos (by linarith) hDy.le
    linarith

/-- `D` is strictly positive somewhere near the centre. -/
lemma exists_DI_pos : ∃ x₀ ∈ Ioc 0 S.R, 0 < S.DI I₀ x₀ := by
  obtain ⟨a, ha, haR, hj, hL⟩ := exists_LI_le hI (S := S)
  have hnn := DI_nonneg_near_center hI haR hj hL
  obtain ⟨r₁, hr₁, hε⟩ := exists_eps_pos (S := S) ha haR hj
  have hr₁a : r₁ ∈ Ioc 0 a := ⟨hr₁.1, hr₁.2.le⟩
  have hr₁R : r₁ ∈ Ioc 0 S.R := ⟨hr₁.1, hr₁.2.le.trans haR⟩
  refine ⟨r₁, hr₁R, ?_⟩
  rcases eq_or_lt_of_le (hnn r₁ hr₁a) with h | h
  · exfalso
    have hpe : 0 < S.piE r₁ := by unfold piE; have := hr₁.1; positivity
    have hres := (level_res_facts hI hr₁R).2 hpe
    have hrd := r_DdI hI hr₁R
    rw [← h, mul_zero, zero_add] at hrd
    have hDd : 0 < S.DdI I₀ r₁ := by
      have := hr₁.1
      by_contra hc; push Not at hc
      nlinarith
    have hev := pos_left_of_deriv_neg (hasDerivAt_DI hI hr₁R (hj r₁ hr₁a)).neg (by linarith)
      (by simp [← h])
    obtain ⟨y, hy1, hy2⟩ := (hev.and (Ioo_mem_nhdsLT hr₁.1)).exists
    have := hnn y ⟨hy2.1, hy2.2.le.trans hr₁a.2⟩
    simp only [Pi.neg_apply] at hy1
    linarith
  · exact h

/-- From the interior positive point to the surface, by a strict exponential barrier.
The barrier propagates across every interface radius: at a touching point (jump or not) the
TOV/Hartle flow is used only on a punctured left neighbourhood, where the strict comparison
inequality persists by continuity of `D`, `L/r` and the exponential. -/
lemma DI_surface_pos : 0 < S.DI I₀ S.R := by
  obtain ⟨x₀, hx₀, hD₀⟩ := exists_DI_pos hI (S := S)
  have hsub : ∀ y ∈ Icc x₀ S.R, y ∈ Ioc 0 S.R := fun y hy => ⟨hx₀.1.trans_le hy.1, hy.2⟩
  have hsubset : Icc x₀ S.R ⊆ Ioc 0 S.R := fun y hy => hsub y hy
  -- lower bound for `L/r` on the compact interval
  have hcontL : ContinuousOn (fun r => S.LfI I₀ r / r) (Icc x₀ S.R) := by
    have hs := (continuousOn_s (S := S)).mono hsubset
    have hs0 : ∀ y ∈ Icc x₀ S.R, S.s y ≠ 0 := fun y hy => (s_pos' (hsub y hy)).ne'
    have hW := (continuousOn_W (S := S)).mono hsubset
    have hZc : ContinuousOn (fun r => Zc I₀ (S.s r)) (Icc x₀ S.R) := fun y hy =>
      (hasDerivAt_Zc I₀ (S.s y) (level_den_ne hI (hsub y hy))).continuousAt.comp_continuousWithinAt
        (hs y hy)
    have hu := (continuousOn_u (S := S)).mono hsubset
    have hp := (continuousOn_piP (S := S)).mono hsubset
    unfold LfI Lco
    exact ((((hW.add hZc).neg.div hs hs0).add ((hu.add (continuousOn_const.mul hp)).div
      (hs.pow 2) (fun y hy => pow_ne_zero 2 (hs0 y hy)))).sub continuousOn_const).div
      continuousOn_id (fun y hy => (hsub y hy).1.ne')
  obtain ⟨r₀, -, hr₀⟩ := isCompact_Icc.exists_isMinOn ⟨x₀, le_rfl, hx₀.2⟩ hcontL
  set K : ℝ := -(S.LfI I₀ r₀ / r₀) + 1 with hK
  have hKL : ∀ y ∈ Icc x₀ S.R, 1 ≤ K + S.LfI I₀ y / y := by
    intro y hy
    have : S.LfI I₀ r₀ / r₀ ≤ S.LfI I₀ y / y := hr₀ hy
    linarith
  set η : ℝ := S.DI I₀ x₀ / 2 with hη
  have hη0 : 0 < η := by linarith
  set φ : ℝ → ℝ := fun r => Real.exp (-K * (r - x₀)) with hφ
  have hφc : Continuous φ := by simp only [hφ]; fun_prop
  set f : ℝ → ℝ := fun r => η * φ r - S.DI I₀ r with hf
  have hcont : ContinuousOn f (Icc x₀ S.R) :=
    (continuousOn_const.mul hφc.continuousOn).sub ((continuousOn_DI hI (S := S)).mono hsubset)
  have hf0 : f x₀ < 0 := by
    simp only [hf, hφ, sub_self, mul_zero, Real.exp_zero, mul_one]; linarith
  have hneg := first_crossing hcont hf0 (fun x hx hfx => by
    have hxI : Icc x₀ x ⊆ Icc x₀ S.R := Icc_subset_Icc_right hx.2
    set H : ℝ → ℝ := fun r => -(η * φ r) + S.LfI I₀ r / r * f r with hH
    have hHc : ContinuousOn H (Icc x₀ x) :=
      (((continuousOn_const.mul hφc.continuousOn).neg).add (hcontL.mul hcont)).mono hxI
    have hHx : H x < 0 := by
      have : 0 < η * φ x := mul_pos hη0 (Real.exp_pos _)
      simp only [hH, hfx, mul_zero, add_zero]
      linarith
    refine pos_left_of_eventually_deriv_neg hx.1 (hcont.mono hxI) ?_ hfx
      (f' := fun y => η * (Real.exp (-K * (y - x₀)) * (-K * 1)) - S.DdI I₀ y)
    filter_upwards [eventually_lt_left_of_continuousOn hx.1 hHc hHx,
      eventually_notMem_left S.jumps x, Ioo_mem_nhdsLT hx.1] with y hHy hj hy
    have hyI : y ∈ Icc x₀ S.R := ⟨hy.1.le, hy.2.le.trans hx.2⟩
    have hy' : y ∈ Ioc 0 S.R := hsub y hyI
    have hφd : HasDerivAt φ (Real.exp (-K * (y - x₀)) * (-K * 1)) y :=
      ((((hasDerivAt_id y).sub_const x₀).const_mul (-K))).exp
    refine ⟨(hφd.const_mul η).sub (hasDerivAt_DI hI hy' hj), ?_⟩
    have hP : 0 < η * φ y := mul_pos hη0 (Real.exp_pos _)
    have hrd := r_DdI hI hy'
    have hres := (level_res_facts hI hy').1
    have hy0 := hy'.1
    have hKy := hKL y hyI
    have hDd : S.LfI I₀ y / y * S.DI I₀ y ≤ S.DdI I₀ y := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hy0]
      nlinarith
    have e1 : η * (Real.exp (-K * (y - x₀)) * (-K * 1)) = -K * (η * φ y) := by
      simp only [hφ]; ring
    have hfy : f y = η * φ y - S.DI I₀ y := by simp only [hf]
    have hHy' : -(η * φ y) + S.LfI I₀ y / y * f y < 0 := hHy
    have hKP : 0 ≤ (K + S.LfI I₀ y / y - 1) * (η * φ y) := mul_nonneg (by linarith) hP.le
    show η * (Real.exp (-K * (y - x₀)) * (-K * 1)) - S.DdI I₀ y < 0
    rw [e1, hfy] at *
    nlinarith)
  have hR := hneg S.R ⟨hx₀.2, le_rfl⟩
  have : 0 < η * φ S.R := mul_pos hη0 (Real.exp_pos _)
  simp only [hf] at hR
  linarith

end Level

/-! ### The Kerr level `Ī₀ = 4` -/

lemma den_ne {x : ℝ} (hx : x ∈ Ioc 0 S.R) : 4 - 4 * (1 - S.s x ^ 2) ^ 3 ≠ 0 :=
  (den_pos (s_pos' hx) (s_le_one hx)).ne'

lemma hasDerivAt_D {x : ℝ} (hx : x ∈ Ioc 0 S.R) (hj : x ∉ S.jumps) :
    HasDerivAt S.D (S.Dd x) x :=
  hasDerivAt_DI kerrBarrierLevel_four hx hj

lemma continuousOn_D : ContinuousOn S.D (Ioc 0 S.R) :=
  continuousOn_DI kerrBarrierLevel_four

/-- The exact Part-A identity along the star: `r D' = L D + Res`. -/
lemma r_Dd {x : ℝ} (hx : x ∈ Ioc 0 S.R) : x * S.Dd x = S.Lf x * S.D x + S.Res x :=
  r_DdI kerrBarrierLevel_four hx

lemma res_facts {x : ℝ} (hx : x ∈ Ioc 0 S.R) :
    0 ≤ S.Res x ∧ (0 < S.piE x → 0 < S.Res x) :=
  level_res_facts kerrBarrierLevel_four hx

/-! ### Behaviour at the regular centre -/

lemma tendsto_D : Tendsto S.D (𝓝[>] 0) (𝓝 0) :=
  tendsto_DI 4

/-- C1: near the centre the linear Riccati coefficient satisfies `L ≤ −2`, on an initial
segment `(0, a]` free of interfaces. -/
lemma exists_L_le : ∃ a, 0 < a ∧ a ≤ S.R ∧ (∀ r ∈ Ioc 0 a, r ∉ S.jumps) ∧
    ∀ r ∈ Ioc 0 a, S.Lf r ≤ -2 :=
  exists_LI_le kerrBarrierLevel_four

lemma continuousAt_D {x : ℝ} (hx : x ∈ Ioc 0 S.R) (hj : x ∉ S.jumps) : ContinuousAt S.D x :=
  (hasDerivAt_D hx hj).continuousAt

/-- C2: `D ≥ 0` near the centre (comparison with `r² D`, using `L ≤ −2` and `Res ≥ 0`). -/
lemma D_nonneg_near_center {a : ℝ} (haR : a ≤ S.R) (hj : ∀ r ∈ Ioc 0 a, r ∉ S.jumps)
    (hL : ∀ r ∈ Ioc 0 a, S.Lf r ≤ -2) : ∀ x ∈ Ioc 0 a, 0 ≤ S.D x :=
  DI_nonneg_near_center kerrBarrierLevel_four haR hj hL

/-- C3': `D` is strictly positive somewhere near the centre. -/
lemma exists_D_pos : ∃ x₀ ∈ Ioc 0 S.R, 0 < S.D x₀ :=
  exists_DI_pos kerrBarrierLevel_four

/-- C4: from the interior positive point to the surface, by a strict exponential barrier
(the case `Ī₀ = 4` of `DI_surface_pos`). -/
lemma D_surface_pos : 0 < S.D S.R :=
  DI_surface_pos kerrBarrierLevel_four

/-! ### Headline theorems -/

/-- **Inertia bound at an admissible level.** For every admissible barrier level `Ī₀`
(`KerrBarrierLevel`), every regular, horizonless, static, monotone-density, isotropic DEC star
satisfies `I > Ī₀ M³`. -/
theorem kerr_inertia_gt_of_level {I₀ : ℝ} (hI : KerrBarrierLevel I₀)
    (S : MonotoneIsotropicDECStar) : S.I > I₀ * S.M ^ 3 := by
  have hR : S.R ∈ Ioc 0 S.R := ⟨S.R_pos, le_rfl⟩
  have hD := DI_surface_pos hI (S := S)
  have hpR : S.piP S.R = 0 := by simp [piP, S.p_surface]
  have hDR : S.DI I₀ S.R = S.Z S.R - Zc I₀ (S.s S.R) := by simp only [DI, W, hpR]; ring
  have hM : S.M = S.u S.R * S.R := by
    unfold M MonotoneIsotropicDECStar.u; field_simp [S.R_pos.ne']
  have hs0 : 0 < S.s S.R := s_pos' hR
  have hs1 : S.s S.R ≤ 1 := s_le_one hR
  have hs2 : S.s S.R ^ 2 = 1 - 2 * S.u S.R := s_sq hR
  have ht : 23 / 125 ≤ S.s S.R ^ 2 := (S.s_sq_gt S.R hR).le
  have hden := level_den_pos hI hs0 hs1 ht
  have hZc0 := level_Zc_nonneg hI hs0 hs1 ht
  unfold I
  rw [hM]
  generalize S.s S.R = s at *
  generalize S.u S.R = u at *
  generalize S.Z S.R = Zr at *
  have hZ : Zc I₀ s < Zr := by linarith
  -- on the vacuum curve: `Z_c(s) (4 − 8 Ī₀ u³) = 24 Ī₀ s u³`
  have h1s : 1 - s ^ 2 = 2 * u := by linarith
  have h8 : 0 < 4 - 8 * I₀ * u ^ 3 := by
    have : 4 - I₀ * (1 - s ^ 2) ^ 3 = 4 - 8 * I₀ * u ^ 3 := by rw [h1s]; ring
    linarith
  have hZc_eq : Zc I₀ s * (4 - 8 * I₀ * u ^ 3) = 24 * I₀ * s * u ^ 3 := by
    have hd' : 4 - I₀ * (2 * u) ^ 3 ≠ 0 := by rw [← h1s]; exact hden.ne'
    unfold Zc
    rw [h1s, div_mul_eq_mul_div, div_eq_iff hd']
    ring
  have key : I₀ * u ^ 3 * (6 * s + 2 * Zr) < Zr := by
    have : Zc I₀ s * (4 - 8 * I₀ * u ^ 3) < Zr * (4 - 8 * I₀ * u ^ 3) :=
      mul_lt_mul_of_pos_right hZ h8
    nlinarith
  have hpos : 0 < 6 * s + 2 * Zr := by linarith
  rw [gt_iff_lt, lt_div_iff₀ hpos]
  have hR3 : 0 < S.R ^ 3 := pow_pos S.R_pos 3
  calc I₀ * (u * S.R) ^ 3 * (6 * s + 2 * Zr) = S.R ^ 3 * (I₀ * u ^ 3 * (6 * s + 2 * Zr)) := by
        ring
    _ < S.R ^ 3 * Zr := mul_lt_mul_of_pos_left key hR3

/-- **Headline theorem (T4A-18, `N40 ⟹ N41`).** Every regular, horizonless, static,
monotone-density, isotropic DEC star — piecewise smooth, with finitely many interior density
jumps allowed — has moment of inertia strictly above the Kerr value: `I > 4 M³ = I_Kerr`. -/
theorem t4a18_unconditional_kerr_inertia_floor (S : MonotoneIsotropicDECStar) :
    S.I > 4 * S.M ^ 3 :=
  kerr_inertia_gt_of_level kerrBarrierLevel_four S

/-- **Uniform positive gap above the Kerr value.** Every regular, horizonless, static,
monotone-density, isotropic DEC star — piecewise smooth, with finitely many interior density
jumps allowed — satisfies `I > (1001/250) M³`, i.e. `I/M³ > 4.004`. Consequently the infimum
of `I/M³` over this class is at least `4.004`, strictly above the Kerr value `4`. -/
theorem t4a18_uniform_kerr_inertia_gap (S : MonotoneIsotropicDECStar) :
    S.I > (1001 / 250 : ℝ) * S.M ^ 3 :=
  kerr_inertia_gt_of_level kerrBarrierLevel_gap S

end MonotoneIsotropicDECStar

/-- **Headline theorem, literal monotone-density form, piecewise-smooth stars.** For every
regular, horizonless, static isotropic DEC star with finitely many interior density jumps
(first-order phase transitions; `m, p, Z` continuous across them, field equations off them)
whose energy density is non-increasing on `(0, R]`,
`I = R³ Z_R / (6 s_R + 2 Z_R) > 4 M³ = I_Kerr`. -/
theorem t4a18_kerr_inertia_floor_of_antitone_piecewise (S : PiecewiseRegularIsotropicDECStar)
    (hε : AntitoneOn S.ε (Ioc 0 S.R)) :
    S.R ^ 3 * S.Z S.R / (6 * sFun S.m S.R + 2 * S.Z S.R) > 4 * S.m S.R ^ 3 :=
  MonotoneIsotropicDECStar.t4a18_unconditional_kerr_inertia_floor (S.toMonotone hε)

/-- **Compactness wall, literal monotone-density form, piecewise-smooth stars.** -/
theorem compactness_wall_of_antitone_piecewise (S : PiecewiseRegularIsotropicDECStar)
    (hε : AntitoneOn S.ε (Ioc 0 S.R)) : ∀ r ∈ Ioc 0 S.R, S.m r / r < 51 / 125 :=
  MonotoneIsotropicDECStar.compactness_wall (S.toMonotone hε)

/-- **Headline theorem, literal monotone-density form (smooth stars, `jumps = ∅`).** For every
regular, horizonless, static isotropic DEC star whose energy density is non-increasing on
`(0, R]`, `I = R³ Z_R / (6 s_R + 2 Z_R) > 4 M³ = I_Kerr`. -/
theorem t4a18_kerr_inertia_floor_of_antitone (S : RegularIsotropicDECStar)
    (hε : AntitoneOn S.ε (Ioc 0 S.R)) :
    S.R ^ 3 * S.Z S.R / (6 * sFun S.m S.R + 2 * S.Z S.R) > 4 * S.m S.R ^ 3 :=
  t4a18_kerr_inertia_floor_of_antitone_piecewise S.toPiecewise hε

/-- **Uniform Kerr inertia gap, literal monotone-density form, piecewise-smooth stars.** For
every regular, horizonless, static isotropic DEC star with finitely many interior density
jumps whose energy density is non-increasing on `(0, R]`,
`I = R³ Z_R / (6 s_R + 2 Z_R) > (1001/250) M³`. -/
theorem t4a18_uniform_kerr_inertia_gap_of_antitone_piecewise
    (S : PiecewiseRegularIsotropicDECStar) (hε : AntitoneOn S.ε (Ioc 0 S.R)) :
    S.R ^ 3 * S.Z S.R / (6 * sFun S.m S.R + 2 * S.Z S.R) > (1001 / 250 : ℝ) * S.m S.R ^ 3 :=
  MonotoneIsotropicDECStar.t4a18_uniform_kerr_inertia_gap (S.toMonotone hε)

/-- **Uniform Kerr inertia gap, literal monotone-density form (smooth stars, `jumps = ∅`).**
For every regular, horizonless, static isotropic DEC star whose energy density is
non-increasing on `(0, R]`, `I = R³ Z_R / (6 s_R + 2 Z_R) > (1001/250) M³`. -/
theorem t4a18_uniform_kerr_inertia_gap_of_antitone (S : RegularIsotropicDECStar)
    (hε : AntitoneOn S.ε (Ioc 0 S.R)) :
    S.R ^ 3 * S.Z S.R / (6 * sFun S.m S.R + 2 * S.Z S.R) > (1001 / 250 : ℝ) * S.m S.R ^ 3 :=
  t4a18_uniform_kerr_inertia_gap_of_antitone_piecewise S.toPiecewise hε

end NaturalMechanics.T4A18

/-! ## Axiom audit -/

#print axioms NaturalMechanics.T4A18.MonotoneIsotropicDECStar.t4a18_unconditional_kerr_inertia_floor
#print axioms NaturalMechanics.T4A18.t4a18_kerr_inertia_floor_of_antitone_piecewise
#print axioms NaturalMechanics.T4A18.t4a18_kerr_inertia_floor_of_antitone
#print axioms NaturalMechanics.T4A18.mean_density_of_antitone
#print axioms NaturalMechanics.T4A18.MonotoneIsotropicDECStar.compactness_wall
#print axioms NaturalMechanics.T4A18.compactness_wall_of_antitone_piecewise
#print axioms NaturalMechanics.T4A18.partA
#print axioms NaturalMechanics.T4A18.MonotoneIsotropicDECStar.t4a18_uniform_kerr_inertia_gap
#print axioms NaturalMechanics.T4A18.t4a18_uniform_kerr_inertia_gap_of_antitone_piecewise
#print axioms NaturalMechanics.T4A18.t4a18_uniform_kerr_inertia_gap_of_antitone
