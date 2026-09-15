import UpperTailOptimizers.LZBoundary.Jp

/-!
# The one-variable Lubetzky–Zhao function and the convexity defect (`lem:convexity-defect`)

For `d ≥ 2` and `p ∈ (0,1)`, Section 3 of `paper/paper.tex` studies
`φ_{p,d}(x) = J_p(x^{1/d})` and the convexity-defect function
`h_{p,d}(z) = z J_p''(z) - (d-1) J_p'(z)`, whose sign is the sign of `φ_{p,d}''`.

Clauses (a)–(c) of `lem:convexity-defect` (convexity defect), as enumerated in the docstring
of `convexity_defect` (`LZBoundary/PhiDeriv.lean`), are proved here at the level of `h_{p,d}`:
* `hasDerivAt_hpd` :  `h_{p,d}'(z) = d(z - r_*) / (z(1-z)^2)`,
* `hpd_rStar` :       `h_{p,d}(r_*) = d - (d-1) log((d-1)(1-p)/p)`,
* `hpd_strictAntiOn` / `hpd_strictMonoOn` : monotonicity on `(0,r_*)` and `(r_*,1)`,
where `r_* = (d-1)/d` and `p_* = (d-1)/((d-1)+exp(d/(d-1)))`.

The rest of the lemma is downstream: `LZBoundary/PhiConvex.lean` has the `p_*` threshold
(`hpd_rStar_nonneg_iff`), and `LZBoundary/PhiDeriv.lean` has the unique minimum, the second
derivative of `φ_{p,d}`, the two zeros below the threshold, the three curvature intervals,
and the packaging `convexity_defect`.
-/

namespace UpperTailOptimizers

open Real

/-- The exceptional density `r_* = (d-1)/d` of `paper/paper.tex` (the Lean name is
`rStar`). -/
noncomputable def rStar (d : ℕ) : ℝ := ((d : ℝ) - 1) / (d : ℝ)

/-- The threshold probability `p_* = (d-1)/((d-1) + exp(d/(d-1)))`. -/
noncomputable def pStar (d : ℕ) : ℝ :=
  ((d : ℝ) - 1) / (((d : ℝ) - 1) + Real.exp ((d : ℝ) / ((d : ℝ) - 1)))

/-- The Lubetzky–Zhao one-variable function `φ_{p,d}(x) = J_p(x^{1/d})`. -/
noncomputable def phi (p : ℝ) (d : ℕ) (x : ℝ) : ℝ := Jp p (Real.rpow x (1 / (d : ℝ)))

/-- The convexity-defect function `h_{p,d}(z) = z J_p''(z) - (d-1) J_p'(z)`. -/
noncomputable def hpd (p : ℝ) (d : ℕ) (u : ℝ) : ℝ := u * Jp'' u - ((d : ℝ) - 1) * Jp' p u

section
variable {d : ℕ}

/-- `0 < d` in `ℝ`, from `2 ≤ d`. -/
theorem dpos (hd : 2 ≤ d) : (0 : ℝ) < (d : ℝ) := by
  have : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  linarith

/-- `1 < d` in `ℝ`, from `2 ≤ d`. -/
theorem one_lt_d (hd : 2 ≤ d) : (1 : ℝ) < (d : ℝ) := by
  have : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  linarith

/-- `0 < r_*` for `d ≥ 2`. -/
theorem rStar_pos (hd : 2 ≤ d) : 0 < rStar d := by
  unfold rStar
  have h1 : (0:ℝ) < (d : ℝ) - 1 := by have := one_lt_d hd; linarith
  exact div_pos h1 (dpos hd)

/-- `r_* < 1` for `d ≥ 2`. -/
theorem rStar_lt_one (hd : 2 ≤ d) : rStar d < 1 := by
  unfold rStar
  have h2 := dpos hd
  rw [div_lt_one h2]; linarith

/-- `r_* ∈ (0,1)` for `d ≥ 2`. -/
theorem rStar_mem_Ioo (hd : 2 ≤ d) : rStar d ∈ Set.Ioo (0 : ℝ) 1 :=
  ⟨rStar_pos hd, rStar_lt_one hd⟩

/-- On `(0,1)`, `h_{p,d}(u) = 1/(1-u) - (d-1) J_p'(u)`, eliminating `J_p''`. -/
theorem hpd_eq {p u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    hpd p d u = (1 - u)⁻¹ - ((d : ℝ) - 1) * Jp' p u := by
  unfold hpd Jp''
  have hune : u ≠ 0 := ne_of_gt hu0
  have h1une : (1 - u) ≠ 0 := ne_of_gt (by linarith)
  field_simp

/-- `lem:convexity-defect`: the derivative of `h_{p,d}` is `d(u - r_*)/(u(1-u)^2)`. -/
theorem hasDerivAt_hpd {p : ℝ} (hd : 2 ≤ d) (hp0 : 0 < p) (hp1 : p < 1)
    {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    HasDerivAt (hpd p d) (((d : ℝ) * (u - rStar d)) / (u * (1 - u) ^ 2)) u := by
  have hune : u ≠ 0 := ne_of_gt hu0
  have h1une : (1 - u) ≠ 0 := ne_of_gt (by linarith)
  have hdne : (d : ℝ) ≠ 0 := ne_of_gt (dpos hd)
  -- derivative of `(1-y)⁻¹` is `1/(1-u)^2`
  have hinv : HasDerivAt (fun y : ℝ => (1 - y)⁻¹) (1 / (1 - u) ^ 2) u := by
    have hsub : HasDerivAt (fun y : ℝ => 1 - y) (-1) u := by
      simpa using (hasDerivAt_id u).const_sub 1
    have h := hsub.inv h1une
    have hval : (1 : ℝ) / (1 - u) ^ 2 = -(-1) / (1 - u) ^ 2 := by norm_num
    rw [hval]
    exact h
  have hJp' := hasDerivAt_Jp' hp0 hp1 hu0 hu1
  have hg : HasDerivAt (fun y : ℝ => (1 - y)⁻¹ - ((d : ℝ) - 1) * Jp' p y)
      (1 / (1 - u) ^ 2 - ((d : ℝ) - 1) * Jp'' u) u :=
    hinv.sub (HasDerivAt.const_mul ((d : ℝ) - 1) hJp')
  -- `hpd p d` agrees with the simplified form on `(0,1)`
  have hagree : hpd p d =ᶠ[nhds u] (fun y : ℝ => (1 - y)⁻¹ - ((d : ℝ) - 1) * Jp' p y) := by
    filter_upwards [Ioo_mem_nhds hu0 hu1] with y hy
    exact hpd_eq hy.1 hy.2
  have hres := hg.congr_of_eventuallyEq hagree
  have hval : ((d : ℝ) * (u - rStar d)) / (u * (1 - u) ^ 2)
      = 1 / (1 - u) ^ 2 - ((d : ℝ) - 1) * Jp'' u := by
    unfold rStar Jp''
    field_simp
    ring
  rw [hval]
  exact hres

/-- `lem:convexity-defect`: the value of `h_{p,d}` at `r_*` equals `d - (d-1) log((d-1)(1-p)/p)`. -/
theorem hpd_rStar {p : ℝ} (hd : 2 ≤ d) (hp0 : 0 < p) (hp1 : p < 1) :
    hpd p d (rStar d) = (d : ℝ) - ((d : ℝ) - 1) * Real.log (((d : ℝ) - 1) * (1 - p) / p) := by
  have hus0 := rStar_pos hd
  have hus1 := rStar_lt_one hd
  have hdne : (d : ℝ) ≠ 0 := ne_of_gt (dpos hd)
  have hpne : p ≠ 0 := ne_of_gt hp0
  have hp1' : (0:ℝ) < 1 - p := by linarith
  have h1pne : (1 - p) ≠ 0 := ne_of_gt hp1'
  rw [hpd_eq hus0 hus1]
  have hsub : (1 : ℝ) - rStar d = 1 / (d : ℝ) := by
    unfold rStar; field_simp; ring
  have h1uspos : (0 : ℝ) < 1 - rStar d := by linarith
  -- `(1 - r_*)⁻¹ = d`
  have e1 : (1 - rStar d)⁻¹ = (d : ℝ) := by rw [hsub, one_div, inv_inv]
  -- `J_p'(r_*) = log((d-1)(1-p)/p)`
  have e2 : Jp' p (rStar d) = Real.log (((d : ℝ) - 1) * (1 - p) / p) := by
    rw [Jp'_eq_sub hp0 hp1 hus0 hus1,
      ← Real.log_div (div_ne_zero (ne_of_gt hus0) hpne)
        (div_ne_zero (ne_of_gt h1uspos) h1pne)]
    congr 1
    rw [hsub, show rStar d = ((d : ℝ) - 1) / (d : ℝ) from rfl]
    field_simp
  rw [e1, e2]

/-- The denominator `u(1-u)^2` is positive on `(0,1)`. -/
private theorem den_pos {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) : 0 < u * (1 - u) ^ 2 := by
  have : (0:ℝ) < 1 - u := by linarith
  positivity

/-- `h_{p,d}` is differentiable, hence continuous, on `(0,1)`. -/
theorem hpd_continuousOn {p : ℝ} (hd : 2 ≤ d) (hp0 : 0 < p) (hp1 : p < 1) :
    ContinuousOn (hpd p d) (Set.Ioo 0 1) := by
  intro u hu
  exact (hasDerivAt_hpd hd hp0 hp1 hu.1 hu.2).continuousAt.continuousWithinAt

/-- `lem:convexity-defect`: `h_{p,d}` is strictly decreasing on `(0,r_*)`. -/
theorem hpd_strictAntiOn {p : ℝ} (hd : 2 ≤ d) (hp0 : 0 < p) (hp1 : p < 1) :
    StrictAntiOn (hpd p d) (Set.Ioo 0 (rStar d)) := by
  have hus1 := rStar_lt_one hd
  apply strictAntiOn_of_hasDerivWithinAt_neg (convex_Ioo _ _)
    (fun u hu => ((hasDerivAt_hpd hd hp0 hp1 hu.1 (lt_trans hu.2 hus1)).continuousAt.continuousWithinAt))
    (f' := fun u => ((d : ℝ) * (u - rStar d)) / (u * (1 - u) ^ 2))
  · intro u hu
    rw [interior_Ioo] at hu
    exact (hasDerivAt_hpd hd hp0 hp1 hu.1 (lt_trans hu.2 hus1)).hasDerivWithinAt
  · intro u hu
    rw [interior_Ioo] at hu
    have hd0 := dpos hd
    have hden := den_pos hu.1 (lt_trans hu.2 hus1)
    have hnum : (d : ℝ) * (u - rStar d) < 0 := by
      have : u - rStar d < 0 := by linarith [hu.2]
      have := mul_neg_of_pos_of_neg hd0 this
      linarith
    exact div_neg_of_neg_of_pos hnum hden

/-- `lem:convexity-defect`: `h_{p,d}` is strictly increasing on `(r_*,1)`. -/
theorem hpd_strictMonoOn {p : ℝ} (hd : 2 ≤ d) (hp0 : 0 < p) (hp1 : p < 1) :
    StrictMonoOn (hpd p d) (Set.Ioo (rStar d) 1) := by
  have hus0 := rStar_pos hd
  apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Ioo _ _)
    (fun u hu => ((hasDerivAt_hpd hd hp0 hp1 (lt_trans hus0 hu.1) hu.2).continuousAt.continuousWithinAt))
    (f' := fun u => ((d : ℝ) * (u - rStar d)) / (u * (1 - u) ^ 2))
  · intro u hu
    rw [interior_Ioo] at hu
    exact (hasDerivAt_hpd hd hp0 hp1 (lt_trans hus0 hu.1) hu.2).hasDerivWithinAt
  · intro u hu
    rw [interior_Ioo] at hu
    have hd0 := dpos hd
    have hden := den_pos (lt_trans hus0 hu.1) hu.2
    have hnum : 0 < (d : ℝ) * (u - rStar d) := by
      have : 0 < u - rStar d := by linarith [hu.1]
      exact mul_pos hd0 this
    exact div_pos hnum hden

end

end UpperTailOptimizers
