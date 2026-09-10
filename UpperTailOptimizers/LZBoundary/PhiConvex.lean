import UpperTailOptimizers.LZBoundary.Phi

/-!
# `lem:convexity-defect`, the `p_*` threshold (convexity half)

This file completes the convexity half of `lem:convexity-defect` of
`paper/bipodal_optimizer.tex`.  The sign of
`φ_{p,d}''` is the sign of `h_{p,d}`, whose minimum over `(0,1)` is its value at
`r_*`.  We prove the threshold characterisation
`h_{p,d}(r_*) ≥ 0 ↔ p_* ≤ p`, equivalently `φ_{p,d}` is (everywhere) convex if and
only if `p ≥ p_*`.  We also record the first-derivative formula `φ_{p,d}'`.

The full-interval packaging `ConvexOn ℝ (Icc 0 1) (phi p d)` for `p ≥ p_*` is *not* proved
here: it needs the rpow second derivative `hasDerivAt_phi''`, so it lives one file up as
`convexOn_phi_of_pStar_le` in `LZBoundary/PhiDeriv.lean`, alongside the piecewise
`StrictConvexOn` / `StrictConcaveOn` packagings and the rest of `lem:convexity-defect`.  It is what makes
the exceptional density `r_*` work in `LZBoundary/Curve.lean`: `r_*` has no Lubetzky–Zhao boundary arc, so the
supporting line at `r_*^d` for `p ≥ p_*` must come from the convexity of `φ_{p,d}` on the
whole interval.
-/

namespace UpperTailOptimizers

open Real

section
variable {d : ℕ}

/-- `0 < p_*` for `d ≥ 2`. -/
theorem pStar_pos (hd : 2 ≤ d) : 0 < pStar d := by
  unfold pStar
  have hd1 : (0:ℝ) < (d:ℝ) - 1 := by have := one_lt_d hd; linarith
  have : (0:ℝ) < ((d:ℝ) - 1) + Real.exp ((d:ℝ) / ((d:ℝ) - 1)) := by positivity
  exact div_pos hd1 this

/-- `p_* < 1` for `d ≥ 2`. -/
theorem pStar_lt_one (hd : 2 ≤ d) : pStar d < 1 := by
  unfold pStar
  have hd1 : (0:ℝ) < (d:ℝ) - 1 := by have := one_lt_d hd; linarith
  have hE : (0:ℝ) < Real.exp ((d:ℝ) / ((d:ℝ) - 1)) := Real.exp_pos _
  have hden : (0:ℝ) < ((d:ℝ) - 1) + Real.exp ((d:ℝ) / ((d:ℝ) - 1)) := by positivity
  rw [div_lt_one hden]; linarith

/-- `lem:convexity-defect` threshold (equality form): `h_{p,d}(r_*) = 0 ↔ p = p_*`. -/
theorem hpd_rStar_eq_zero_iff (hd : 2 ≤ d) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    hpd p d (rStar d) = 0 ↔ p = pStar d := by
  have hd1 : (0:ℝ) < (d:ℝ) - 1 := by have := one_lt_d hd; linarith
  have hd1ne : (d:ℝ) - 1 ≠ 0 := ne_of_gt hd1
  have hpne : p ≠ 0 := ne_of_gt hp0
  have hp1' : (0:ℝ) < 1 - p := by linarith
  have hArg : (0:ℝ) < ((d:ℝ) - 1) * (1 - p) / p := by positivity
  have hden : (0:ℝ) < ((d:ℝ) - 1) + Real.exp ((d:ℝ) / ((d:ℝ) - 1)) := by positivity
  rw [hpd_rStar hd hp0 hp1, sub_eq_zero]
  constructor
  · intro h
    -- `d = (d-1) log arg`  ⟹  `arg = exp(d/(d-1))`
    have hlog : Real.log (((d:ℝ) - 1) * (1 - p) / p) = (d:ℝ) / ((d:ℝ) - 1) := by
      rw [eq_div_iff hd1ne, mul_comm]; exact h.symm
    have harg : ((d:ℝ) - 1) * (1 - p) / p = Real.exp ((d:ℝ) / ((d:ℝ) - 1)) := by
      rw [← hlog, Real.exp_log hArg]
    have harg' : ((d:ℝ) - 1) * (1 - p) = Real.exp ((d:ℝ) / ((d:ℝ) - 1)) * p :=
      (div_eq_iff hpne).mp harg
    unfold pStar
    rw [eq_div_iff (ne_of_gt hden)]
    linear_combination -harg'
  · intro h
    have harg : ((d:ℝ) - 1) * (1 - p) / p = Real.exp ((d:ℝ) / ((d:ℝ) - 1)) := by
      rw [h]; unfold pStar; field_simp; ring
    rw [harg, Real.log_exp]
    field_simp

/-- `lem:convexity-defect` threshold (sign form): `h_{p,d}(r_*) ≥ 0 ↔ p_* ≤ p`.  Thus `φ_{p,d}`
is convex on `[0,1]` exactly when `p ≥ p_*`. -/
theorem hpd_rStar_nonneg_iff (hd : 2 ≤ d) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    0 ≤ hpd p d (rStar d) ↔ pStar d ≤ p := by
  have hd1 : (0:ℝ) < (d:ℝ) - 1 := by have := one_lt_d hd; linarith
  have hpne : p ≠ 0 := ne_of_gt hp0
  have hp1' : (0:ℝ) < 1 - p := by linarith
  have hArg : (0:ℝ) < ((d:ℝ) - 1) * (1 - p) / p := by positivity
  have hden : (0:ℝ) < ((d:ℝ) - 1) + Real.exp ((d:ℝ) / ((d:ℝ) - 1)) := by positivity
  rw [hpd_rStar hd hp0 hp1, sub_nonneg, mul_comm, ← le_div_iff₀ hd1,
    Real.log_le_iff_le_exp hArg]
  -- now: `arg ≤ exp(d/(d-1)) ↔ pStar ≤ p`
  rw [div_le_iff₀ hp0]
  unfold pStar
  rw [div_le_iff₀ hden]
  constructor <;> intro h <;> nlinarith [h]

/-- `lem:convexity-defect` threshold (strict form): `h_{p,d}(r_*) < 0 ↔ p < p_*`. -/
theorem hpd_rStar_neg_iff (hd : 2 ≤ d) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    hpd p d (rStar d) < 0 ↔ p < pStar d := by
  rw [← not_le, ← not_le, hpd_rStar_nonneg_iff hd hp0 hp1]

end

/-! ### First derivative of `φ_{p,d}` (rpow chain rule). -/

section
variable {p : ℝ} {d : ℕ}

/-- The first derivative of `φ_{p,d}(x) = J_p(x^{1/d})` at `x > 0`:
`φ_{p,d}'(x) = J_p'(x^{1/d}) · (1/d) x^{1/d - 1}`, matching the paper's
`J_p'(u)/(d u^{d-1})` after substituting `u = x^{1/d}`. -/
theorem hasDerivAt_phi (hd : 2 ≤ d) (hp0 : 0 < p) (hp1 : p < 1)
    {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    HasDerivAt (phi p d)
      (Jp' p (Real.rpow x (1 / (d:ℝ))) * ((1 / (d:ℝ)) * Real.rpow x (1 / (d:ℝ) - 1))) x := by
  have hdpos := dpos hd
  -- inner: `x ↦ x^{1/d}` is positive and below 1 on (0,1)
  have hu0 : 0 < Real.rpow x (1 / (d:ℝ)) := Real.rpow_pos_of_pos hx0 _
  have hu1 : Real.rpow x (1 / (d:ℝ)) < 1 := by
    have : Real.rpow x (1 / (d:ℝ)) < Real.rpow 1 (1 / (d:ℝ)) := by
      apply Real.rpow_lt_rpow (le_of_lt hx0) hx1
      positivity
    simpa using this
  have hinner : HasDerivAt (fun y : ℝ => Real.rpow y (1 / (d:ℝ)))
      ((1 / (d:ℝ)) * Real.rpow x (1 / (d:ℝ) - 1)) x :=
    Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hx0))
  have houter := hasDerivAt_Jp hp0 hp1 hu0 hu1
  exact houter.comp x hinner

end

end UpperTailOptimizers
