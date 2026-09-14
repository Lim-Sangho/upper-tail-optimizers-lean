import UpperTailOptimizers.SingularEndpoint.RankOneStationaryFamily.Defs

/-!
# Bipodality of rank-one KKT points: the scalar core (Section 5)

This file proves the scalar half of `lem:stationary-rank-one-bipodality` of `paper/sections/singular.tex`:
the rank-one KKT function `F_{p,γ}(z) = J_p'(z) - γ z^{d-1}` of `Fkkt` has **at most three
zeros** in `(0,1)`, and consequently a nonconstant rank-one factor cannot take three
distinct values.

The argument of the paper is followed literally.  Since `J_p''(z) = 1/(z(1-z))`,
`F_{p,γ}'(z) = 1/(z(1-z)) - γ(d-1)z^{d-2}`, so a critical point of `F_{p,γ}` in `(0,1)` is
exactly a solution of `γ(d-1) z^{d-1}(1-z) = 1`.  The shape function `z ↦ z^{d-1}(1-z)`
increases strictly on `[0,r_*]` and decreases strictly on `[r_*,1]` with `r_* = (d-1)/d`,
so it takes no value three times: `F_{p,γ}` has at most two critical points, and Rolle's
theorem turns this into the three-zero bound.  Finally, if a factor `f` took three values
`a < b < c` then `a², ab, ac, bc, c²` would be five distinct zeros.

No graphons and no measure theory appear here; the measurable-selection step that produces
the five products lives further up the file hierarchy.

## Contents

* `hasDerivAt_Fkkt` — the derivative `F_{p,γ}'(z) = J_p''(z) - γ(d-1)z^{d-2}`;
* `pow_mul_one_sub_strictMonoOn`, `pow_mul_one_sub_strictAntiOn` — the shape of
  `z ↦ z^{d-1}(1-z)` on `[0,r_*]` and on `[r_*,1]`;
* `three_critical_points_absurd` — `F_{p,γ}'` has at most two zeros in `(0,1)`;
* `four_zeros_absurd` — **at most three zeros**: the Rolle consequence;
* `three_values_absurd` — the five-product contradiction of
  `lem:stationary-rank-one-bipodality`: no admissible factor takes three distinct values.
-/

namespace UpperTailOptimizers

namespace SingularEndpoint

variable {d : ℕ}

/-! ## The derivative of the rank-one KKT function -/

/-- `((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1`, the cast juggling needed to read `hasDerivAt_pow`. -/
private theorem cast_d_sub_one (hd : 2 ≤ d) : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
  rw [Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_one]

/-- `z^{d-1} = z^{d-2} · z`, valid because `d ≥ 2` makes `d - 1 = (d - 2) + 1` in `ℕ`. -/
private theorem pow_d_sub_one (hd : 2 ≤ d) (z : ℝ) : z ^ (d - 1) = z ^ (d - 2) * z := by
  rw [← pow_succ]
  congr 1
  omega

/-- The monomial derivative `(z^{d-1})' = (d-1) z^{d-2}`, with the casts already sorted. -/
private theorem hasDerivAt_pow_d_sub_one (hd : 2 ≤ d) (z : ℝ) :
    HasDerivAt (fun x : ℝ => x ^ (d - 1)) (((d : ℝ) - 1) * z ^ (d - 2)) z := by
  have hidx : d - 1 - 1 = d - 2 := by omega
  have h := hasDerivAt_pow (d - 1) z
  rwa [cast_d_sub_one hd, hidx] at h

/-- **The derivative of the rank-one KKT function.**
`F_{p,γ}'(z) = J_p''(z) - γ(d-1)z^{d-2}`, the displayed formula in the proof of
`lem:stationary-rank-one-bipodality`. -/
theorem hasDerivAt_Fkkt (hd : 2 ≤ d) {p z : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hz0 : 0 < z) (hz1 : z < 1) {γ : ℝ} :
    HasDerivAt (Fkkt d p γ) (Jp'' z - γ * ((d : ℝ) - 1) * z ^ (d - 2)) z := by
  have h := (hasDerivAt_Jp' hp0 hp1 hz0 hz1).sub
    ((hasDerivAt_pow_d_sub_one hd z).const_mul γ)
  have hval : Jp'' z - γ * (((d : ℝ) - 1) * z ^ (d - 2))
      = Jp'' z - γ * ((d : ℝ) - 1) * z ^ (d - 2) := by ring
  rw [hval] at h
  exact h

/-! ## The shape function `z ↦ z^{d-1}(1-z)` -/

/-- The derivative of the shape function: `(z^{d-1}(1-z))' = z^{d-2}((d-1) - d z)`. -/
private theorem hasDerivAt_pow_mul_one_sub (hd : 2 ≤ d) (z : ℝ) :
    HasDerivAt (fun x : ℝ => x ^ (d - 1) * (1 - x))
      (z ^ (d - 2) * (((d : ℝ) - 1) - (d : ℝ) * z)) z := by
  have hlin : HasDerivAt (fun x : ℝ => 1 - x) (-1) z := by
    simpa using (hasDerivAt_const z (1 : ℝ)).fun_sub (hasDerivAt_id z)
  have h := (hasDerivAt_pow_d_sub_one hd z).mul hlin
  have hval : ((d : ℝ) - 1) * z ^ (d - 2) * (1 - z) + z ^ (d - 1) * (-1)
      = z ^ (d - 2) * (((d : ℝ) - 1) - (d : ℝ) * z) := by
    rw [pow_d_sub_one hd]; ring
  rw [hval] at h
  exact h

private theorem continuous_pow_mul_one_sub (d : ℕ) :
    Continuous (fun z : ℝ => z ^ (d - 1) * (1 - z)) :=
  (continuous_pow (d - 1)).mul (continuous_const.sub continuous_id)

/-- `z ↦ z^{d-1}(1-z)` is strictly increasing on `[0, r_*]`, `r_* = (d-1)/d`: its derivative
`z^{d-2}((d-1) - dz)` is positive on `(0, r_*)`. -/
theorem pow_mul_one_sub_strictMonoOn (hd : 2 ≤ d) :
    StrictMonoOn (fun z : ℝ => z ^ (d - 1) * (1 - z)) (Set.Icc 0 (rStar d)) := by
  refine strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc _ _)
    (continuous_pow_mul_one_sub d).continuousOn
    (f' := fun z => z ^ (d - 2) * (((d : ℝ) - 1) - (d : ℝ) * z))
    (fun z _ => (hasDerivAt_pow_mul_one_sub hd z).hasDerivWithinAt) ?_
  intro z hz
  rw [interior_Icc] at hz
  have hd0 : (0 : ℝ) < (d : ℝ) := dpos hd
  have hlt : z < ((d : ℝ) - 1) / (d : ℝ) := hz.2
  rw [lt_div_iff₀ hd0] at hlt
  exact mul_pos (pow_pos hz.1 _) (by linarith)

/-- `z ↦ z^{d-1}(1-z)` is strictly decreasing on `[r_*, 1]`, `r_* = (d-1)/d`: its derivative
`z^{d-2}((d-1) - dz)` is negative on `(r_*, 1)`. -/
theorem pow_mul_one_sub_strictAntiOn (hd : 2 ≤ d) :
    StrictAntiOn (fun z : ℝ => z ^ (d - 1) * (1 - z)) (Set.Icc (rStar d) 1) := by
  refine strictAntiOn_of_hasDerivWithinAt_neg (convex_Icc _ _)
    (continuous_pow_mul_one_sub d).continuousOn
    (f' := fun z => z ^ (d - 2) * (((d : ℝ) - 1) - (d : ℝ) * z))
    (fun z _ => (hasDerivAt_pow_mul_one_sub hd z).hasDerivWithinAt) ?_
  intro z hz
  rw [interior_Icc] at hz
  have hd0 : (0 : ℝ) < (d : ℝ) := dpos hd
  have hgt : ((d : ℝ) - 1) / (d : ℝ) < z := hz.1
  rw [div_lt_iff₀ hd0] at hgt
  have hz0 : 0 < z := lt_trans (rStar_pos hd) hz.1
  exact mul_neg_of_pos_of_neg (pow_pos hz0 _) (by linarith)

/-! ## At most two critical points -/

/-- A critical point of `F_{p,γ}` in `(0,1)` solves `γ(d-1) z^{d-1}(1-z) = 1`: multiply
`J_p''(z) = γ(d-1)z^{d-2}` by `z(1-z) > 0`. -/
private theorem pow_mul_one_sub_eq_of_deriv_eq_zero (hd : 2 ≤ d) {γ z : ℝ}
    (hz0 : 0 < z) (hz1 : z < 1)
    (e : Jp'' z - γ * ((d : ℝ) - 1) * z ^ (d - 2) = 0) :
    γ * ((d : ℝ) - 1) * (z ^ (d - 1) * (1 - z)) = 1 := by
  have hz1' : (0 : ℝ) < 1 - z := by linarith
  have hden : (0 : ℝ) < z * (1 - z) := mul_pos hz0 hz1'
  have hJ : Jp'' z = 1 / (z * (1 - z)) := rfl
  have key : γ * ((d : ℝ) - 1) * z ^ (d - 2) = 1 / (z * (1 - z)) := by
    rw [← hJ]; linarith
  calc γ * ((d : ℝ) - 1) * (z ^ (d - 1) * (1 - z))
      = γ * ((d : ℝ) - 1) * z ^ (d - 2) * (z * (1 - z)) := by
        rw [pow_d_sub_one hd]; ring
    _ = 1 / (z * (1 - z)) * (z * (1 - z)) := by rw [key]
    _ = 1 := by field_simp

/-- **`F_{p,γ}'` has at most two zeros in `(0,1)`.**  Three critical points would give three
points at which the shape function `z ↦ z^{d-1}(1-z)` takes the value `1/(γ(d-1))`, which
`pow_mul_one_sub_strictMonoOn` and `pow_mul_one_sub_strictAntiOn` forbid.  (The multiplier
`p` plays no role: only `γ` enters `F_{p,γ}'`.) -/
theorem three_critical_points_absurd (hd : 2 ≤ d) {γ : ℝ} {z₁ z₂ z₃ : ℝ}
    (h₁ : 0 < z₁) (h₁₂ : z₁ < z₂) (h₂₃ : z₂ < z₃) (h₃ : z₃ < 1)
    (e₁ : Jp'' z₁ - γ * ((d : ℝ) - 1) * z₁ ^ (d - 2) = 0)
    (e₂ : Jp'' z₂ - γ * ((d : ℝ) - 1) * z₂ ^ (d - 2) = 0)
    (e₃ : Jp'' z₃ - γ * ((d : ℝ) - 1) * z₃ ^ (d - 2) = 0) : False := by
  have h2 : 0 < z₂ := h₁.trans h₁₂
  have h3 : 0 < z₃ := h2.trans h₂₃
  have h2' : z₂ < 1 := h₂₃.trans h₃
  have h1' : z₁ < 1 := h₁₂.trans h2'
  have k₁ := pow_mul_one_sub_eq_of_deriv_eq_zero hd h₁ h1' e₁
  have k₂ := pow_mul_one_sub_eq_of_deriv_eq_zero hd h2 h2' e₂
  have k₃ := pow_mul_one_sub_eq_of_deriv_eq_zero hd h3 h₃ e₃
  have hdm : (0 : ℝ) < (d : ℝ) - 1 := by have := one_lt_d hd; linarith
  -- the multiplier must be positive
  have hγ : 0 < γ := by
    by_contra hcon
    push Not at hcon
    have hpos : 0 < z₁ ^ (d - 1) * (1 - z₁) := mul_pos (pow_pos h₁ _) (by linarith)
    have hA : γ * ((d : ℝ) - 1) ≤ 0 := by nlinarith
    linarith [mul_nonneg (neg_nonneg.mpr hA) hpos.le, k₁]
  have hc : γ * ((d : ℝ) - 1) ≠ 0 := ne_of_gt (mul_pos hγ hdm)
  have e12 : z₁ ^ (d - 1) * (1 - z₁) = z₂ ^ (d - 1) * (1 - z₂) :=
    mul_left_cancel₀ hc (k₁.trans k₂.symm)
  have e23 : z₂ ^ (d - 1) * (1 - z₂) = z₃ ^ (d - 1) * (1 - z₃) :=
    mul_left_cancel₀ hc (k₂.trans k₃.symm)
  by_cases hcase : z₂ ≤ rStar d
  · have hmono : z₁ ^ (d - 1) * (1 - z₁) < z₂ ^ (d - 1) * (1 - z₂) :=
      pow_mul_one_sub_strictMonoOn hd (Set.mem_Icc.mpr ⟨h₁.le, h₁₂.le.trans hcase⟩)
        (Set.mem_Icc.mpr ⟨h2.le, hcase⟩) h₁₂
    exact absurd e12 (ne_of_lt hmono)
  · push Not at hcase
    have hanti : z₃ ^ (d - 1) * (1 - z₃) < z₂ ^ (d - 1) * (1 - z₂) :=
      pow_mul_one_sub_strictAntiOn hd (Set.mem_Icc.mpr ⟨hcase.le, h2'.le⟩)
        (Set.mem_Icc.mpr ⟨hcase.le.trans h₂₃.le, h₃.le⟩) h₂₃
    exact absurd e23 (ne_of_gt hanti)

/-! ## At most three zeros -/

/-- **`F_{p,γ}` has at most three zeros in `(0,1)`.**  Rolle's theorem on `[z₁,z₂]`,
`[z₂,z₃]` and `[z₃,z₄]` produces three strictly increasing critical points, contradicting
`three_critical_points_absurd`.  This is the root bound of
`lem:stationary-rank-one-bipodality`. -/
theorem four_zeros_absurd (hd : 2 ≤ d) {p γ : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    {z₁ z₂ z₃ z₄ : ℝ} (h₁ : 0 < z₁) (h₁₂ : z₁ < z₂) (h₂₃ : z₂ < z₃) (h₃₄ : z₃ < z₄)
    (h₄ : z₄ < 1)
    (e₁ : Fkkt d p γ z₁ = 0) (e₂ : Fkkt d p γ z₂ = 0)
    (e₃ : Fkkt d p γ z₃ = 0) (e₄ : Fkkt d p γ z₄ = 0) : False := by
  have rolle : ∀ a b : ℝ, 0 < a → a < b → b < 1 → Fkkt d p γ a = 0 → Fkkt d p γ b = 0 →
      ∃ c, a < c ∧ c < b ∧ Jp'' c - γ * ((d : ℝ) - 1) * c ^ (d - 2) = 0 := by
    intro a b ha hab hb ea eb
    have hcont : ContinuousOn (Fkkt d p γ) (Set.Icc a b) := fun x hx =>
      (hasDerivAt_Fkkt hd hp0 hp1 (lt_of_lt_of_le ha hx.1)
        (lt_of_le_of_lt hx.2 hb)).continuousAt.continuousWithinAt
    obtain ⟨c, hc, hc0⟩ := exists_hasDerivAt_eq_zero
      (f' := fun z : ℝ => Jp'' z - γ * ((d : ℝ) - 1) * z ^ (d - 2)) hab hcont
      (ea.trans eb.symm)
      (fun x hx => hasDerivAt_Fkkt hd hp0 hp1 (ha.trans hx.1) (hx.2.trans hb))
    exact ⟨c, hc.1, hc.2, hc0⟩
  obtain ⟨c₁, hc₁a, hc₁b, k₁⟩ := rolle z₁ z₂ h₁ h₁₂ (by linarith) e₁ e₂
  obtain ⟨c₂, hc₂a, hc₂b, k₂⟩ := rolle z₂ z₃ (by linarith) h₂₃ (by linarith) e₂ e₃
  obtain ⟨c₃, hc₃a, _hc₃b, k₃⟩ := rolle z₃ z₄ (by linarith) h₃₄ h₄ e₃ e₄
  exact three_critical_points_absurd hd (by linarith) (by linarith) (by linarith)
    (by linarith) k₁ k₂ k₃

/-- **The five-product contradiction of `lem:stationary-rank-one-bipodality`.**  If a rank-one
factor took three distinct values `0 < a < b < c < 1`, then the five products
`a², ab, ac, bc, c²` would all be zeros of `F_{p,γ}`; they are distinct and lie in `(0,1)`,
so already the first four contradict `four_zeros_absurd`. Only those four equations are
required below. Hence such a factor takes at most two values. -/
theorem three_values_absurd (hd : 2 ≤ d) {p γ a b c : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (ha0 : 0 < a) (hab : a < b) (hbc : b < c) (hc1 : c < 1)
    (haa : Fkkt d p γ (a * a) = 0) (hab' : Fkkt d p γ (a * b) = 0)
    (hac : Fkkt d p γ (a * c) = 0) (hbc' : Fkkt d p γ (b * c) = 0) : False := by
  have hb0 : 0 < b := ha0.trans hab
  have hc0 : 0 < c := hb0.trans hbc
  have h1 : a * a < a * b := by nlinarith
  have h2 : a * b < a * c := by nlinarith
  have h3 : a * c < b * c := by nlinarith
  have h4 : b * c < 1 := by nlinarith
  exact four_zeros_absurd hd hp0 hp1 (mul_pos ha0 ha0) h1 h2 h3 h4 haa hab' hac hbc'

end SingularEndpoint

end UpperTailOptimizers
