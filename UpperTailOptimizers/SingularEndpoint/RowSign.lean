import UpperTailOptimizers.SingularEndpoint.Bipodality
import UpperTailOptimizers.SingularEndpoint.Family

/-!
# Signs between the three roots, and the block weight (Section 7)

`lem:rank-one-kkt-family` of `paper/singular_endpoint.tex` recovers the block weight
`α_h` from block-weight stationarity `eq:block-proportion-balance`,

  `α·{𝓜(s²) - 𝓜(st)} = (1-α)·{𝓜(t²) - 𝓜(st)}`,

whose solution `eq:block-proportion-formula` is `α = B/(A+B)` with `A = 𝓜(s²) - 𝓜(st)` and
`B = 𝓜(t²) - 𝓜(st)`.  The paper argues that the denominator `A + B` is
`-4d³h⁴/3 + O_d(h⁵)` and hence nonzero.  **That expansion is unnecessary.**  Both `A` and `B` are *strictly
negative*, which gives the nonvanishing denominator and `0 < α < 1` at one stroke.

The reason is a sign analysis of the rank-one KKT function
`F_{p,γ}(z) = J_p'(z) - γz^{d-1}` `eq:rank-one-kkt` of which
`𝓜_{p,γ}` is the antiderivative (`hasDerivAt_Mfun`).  Let `z₁ < z₂ < z₃` be the three
roots of `eq:three-value-kkt` in `(0,1)`.  Rolle on `[z₁,z₂]` and `[z₂,z₃]` produces
`ρ₁ ∈ (z₁,z₂)` and `ρ₂ ∈ (z₂,z₃)` with `F' = 0`.  Since `J_p''(z) = 1/(z(1-z))`,

  `F'(z)·z(1-z) = 1 - γ(d-1)·z^{d-1}(1-z)`,

so the sign of `F'` on `(0,1)` is governed entirely by the unimodal shape function
`S(z) = z^{d-1}(1-z)` of `SingularEndpoint/Bipodality.lean`, which increases strictly on `[0,r_*]`
and decreases strictly on `[r_*,1]`.  From `S(ρ₁) = S(ρ₂) = 1/(γ(d-1))` one gets
`ρ₁ < r_* < ρ₂` and then, with no limits and no `h`-expansion,

  `F' > 0` on `(0,ρ₁)`,  `F' < 0` on `(ρ₁,ρ₂)`,  `F' > 0` on `(ρ₂,1)`.

Hence `F` rises from `F(z₁) = 0` to `ρ₁` and falls back to `F(z₂) = 0`, so `F > 0` on
`(z₁,z₂)`; symmetrically `F < 0` on `(z₂,z₃)`.  Integrating, `𝓜` is strictly increasing on
`[z₁,z₂]` and strictly decreasing on `[z₂,z₃]`, which is exactly `A < 0` and `B < 0`.

## Contents

* `Fkkt_pos_of_mem_Ioo` — `F_{p,γ} > 0` strictly between the first two roots;
* `Fkkt_neg_of_mem_Ioo` — `F_{p,γ} < 0` strictly between the last two roots;
* `Mfun_lt_of_root_left`, `Mfun_lt_of_root_right` — `𝓜(z₁) < 𝓜(z₂)` and `𝓜(z₃) < 𝓜(z₂)`,
  i.e. the two differences of `eq:block-proportion-balance` are strictly negative;
* `rowBalance_denom_ne_zero` — the denominator of `eq:block-proportion-formula` is nonzero;
* `rowBalance_alpha_mem` — the resulting block weight lies in `(0,1)`;
* `rowBalance_solution` — it really solves `eq:block-proportion-balance`.
-/

namespace UpperTailOptimizers

namespace SingularEndpoint

variable {d : ℕ}

/-! ## The derivative of the rank-one KKT function, and its sign -/

/-- `F_{p,γ}'(z) = J_p''(z) - γ(d-1)z^{d-2}`, the derivative supplied by `hasDerivAt_Fkkt`,
named so that it can be quantified over.  It does not depend on `p`. -/
private noncomputable def Fder (d : ℕ) (γ z : ℝ) : ℝ :=
  Jp'' z - γ * ((d : ℝ) - 1) * z ^ (d - 2)

/-- Clearing the denominator of `J_p''(z) = 1/(z(1-z))`:
`F_{p,γ}'(z)·z(1-z) = 1 - γ(d-1)·z^{d-1}(1-z)`.  This is what reduces the sign of the
derivative to the shape function of `SingularEndpoint/Bipodality.lean`. -/
private theorem Fder_mul_eq (hd : 2 ≤ d) {γ z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    Fder d γ z * (z * (1 - z)) = 1 - γ * ((d : ℝ) - 1) * (z ^ (d - 1) * (1 - z)) := by
  have hden : (0 : ℝ) < z * (1 - z) := mul_pos hz0 (by linarith)
  have hne : z * (1 - z) ≠ 0 := ne_of_gt hden
  have hJ : Jp'' z = 1 / (z * (1 - z)) := rfl
  have hp : z ^ (d - 1) = z ^ (d - 2) * z := by
    rw [← pow_succ]; congr 1; omega
  have hcan : 1 / (z * (1 - z)) * (z * (1 - z)) = 1 := one_div_mul_cancel hne
  simp only [Fder, hJ, hp]
  rw [sub_mul, hcan]
  ring

/-- If the shape value `γ(d-1)·z^{d-1}(1-z)` is below `1`, the derivative is positive. -/
private theorem Fder_pos_of (hd : 2 ≤ d) {γ z : ℝ} (hz0 : 0 < z) (hz1 : z < 1)
    (h : γ * ((d : ℝ) - 1) * (z ^ (d - 1) * (1 - z)) < 1) : 0 < Fder d γ z := by
  have hden : (0 : ℝ) < z * (1 - z) := mul_pos hz0 (by linarith)
  have hkey := Fder_mul_eq (γ := γ) hd hz0 hz1
  nlinarith [hkey, hden, h]

/-- If the shape value `γ(d-1)·z^{d-1}(1-z)` is above `1`, the derivative is negative. -/
private theorem Fder_neg_of (hd : 2 ≤ d) {γ z : ℝ} (hz0 : 0 < z) (hz1 : z < 1)
    (h : 1 < γ * ((d : ℝ) - 1) * (z ^ (d - 1) * (1 - z))) : Fder d γ z < 0 := by
  have hden : (0 : ℝ) < z * (1 - z) := mul_pos hz0 (by linarith)
  have hkey := Fder_mul_eq (γ := γ) hd hz0 hz1
  nlinarith [hkey, hden, h]

/-- A critical point of `F_{p,γ}` in `(0,1)` solves `γ(d-1)·z^{d-1}(1-z) = 1`. -/
private theorem Fder_eq_one (hd : 2 ≤ d) {γ z : ℝ} (hz0 : 0 < z) (hz1 : z < 1)
    (h : Fder d γ z = 0) : γ * ((d : ℝ) - 1) * (z ^ (d - 1) * (1 - z)) = 1 := by
  have hkey := Fder_mul_eq (γ := γ) hd hz0 hz1
  rw [h, zero_mul] at hkey
  linarith

/-- **The sign pattern of `F_{p,γ}'`.**  Given two critical points `ρ₁ < ρ₂` in `(0,1)`, the
derivative is positive on `(0,ρ₁)`, negative on `(ρ₁,ρ₂)` and positive again on `(ρ₂,1)`.

The proof is pure unimodality: `S(ρ₁) = S(ρ₂) = 1/(γ(d-1))` with `S(z) = z^{d-1}(1-z)`
forces `ρ₁ < r_* < ρ₂` by `pow_mul_one_sub_strictMonoOn` and
`pow_mul_one_sub_strictAntiOn`, after which the three comparisons are immediate. -/
private theorem Fder_sign (hd : 2 ≤ d) {γ ρ₁ ρ₂ : ℝ}
    (hr1 : 0 < ρ₁) (hr12 : ρ₁ < ρ₂) (hr2 : ρ₂ < 1)
    (k₁ : Fder d γ ρ₁ = 0) (k₂ : Fder d γ ρ₂ = 0) :
    (∀ z : ℝ, 0 < z → z < ρ₁ → 0 < Fder d γ z) ∧
      (∀ z : ℝ, ρ₁ < z → z < ρ₂ → Fder d γ z < 0) ∧
      (∀ z : ℝ, ρ₂ < z → z < 1 → 0 < Fder d γ z) := by
  have hr1' : ρ₁ < 1 := hr12.trans hr2
  have hr2' : (0 : ℝ) < ρ₂ := hr1.trans hr12
  have hc1 : γ * ((d : ℝ) - 1) * (ρ₁ ^ (d - 1) * (1 - ρ₁)) = 1 := Fder_eq_one hd hr1 hr1' k₁
  have hc2 : γ * ((d : ℝ) - 1) * (ρ₂ ^ (d - 1) * (1 - ρ₂)) = 1 := Fder_eq_one hd hr2' hr2 k₂
  have hS1pos : (0 : ℝ) < ρ₁ ^ (d - 1) * (1 - ρ₁) :=
    mul_pos (pow_pos hr1 _) (by linarith)
  have hcpos : (0 : ℝ) < γ * ((d : ℝ) - 1) := by
    by_contra hcon
    push Not at hcon
    nlinarith
  have hSeq : ρ₁ ^ (d - 1) * (1 - ρ₁) = ρ₂ ^ (d - 1) * (1 - ρ₂) :=
    mul_left_cancel₀ (ne_of_gt hcpos) (hc1.trans hc2.symm)
  -- the two critical points straddle `r_*`
  have hlt1 : ρ₁ < rStar d := by
    by_contra hcon
    push Not at hcon
    have hstep : ρ₂ ^ (d - 1) * (1 - ρ₂) < ρ₁ ^ (d - 1) * (1 - ρ₁) :=
      pow_mul_one_sub_strictAntiOn hd (Set.mem_Icc.mpr ⟨hcon, hr1'.le⟩)
        (Set.mem_Icc.mpr ⟨hcon.trans hr12.le, hr2.le⟩) hr12
    linarith
  have hlt2 : rStar d < ρ₂ := by
    by_contra hcon
    push Not at hcon
    have hstep : ρ₁ ^ (d - 1) * (1 - ρ₁) < ρ₂ ^ (d - 1) * (1 - ρ₂) :=
      pow_mul_one_sub_strictMonoOn hd (Set.mem_Icc.mpr ⟨hr1.le, hr12.le.trans hcon⟩)
        (Set.mem_Icc.mpr ⟨hr2'.le, hcon⟩) hr12
    linarith
  refine ⟨?_, ?_, ?_⟩
  · intro z hz0 hzr
    refine Fder_pos_of hd hz0 (hzr.trans hr1') ?_
    have hstep : z ^ (d - 1) * (1 - z) < ρ₁ ^ (d - 1) * (1 - ρ₁) :=
      pow_mul_one_sub_strictMonoOn hd (Set.mem_Icc.mpr ⟨hz0.le, hzr.le.trans hlt1.le⟩)
        (Set.mem_Icc.mpr ⟨hr1.le, hlt1.le⟩) hzr
    have hmul := mul_lt_mul_of_pos_left hstep hcpos
    linarith
  · intro z hz1 hz2
    refine Fder_neg_of hd (hr1.trans hz1) (hz2.trans hr2) ?_
    have hstep : ρ₁ ^ (d - 1) * (1 - ρ₁) < z ^ (d - 1) * (1 - z) := by
      by_cases hcase : z ≤ rStar d
      · exact pow_mul_one_sub_strictMonoOn hd (Set.mem_Icc.mpr ⟨hr1.le, hlt1.le⟩)
          (Set.mem_Icc.mpr ⟨(hr1.trans hz1).le, hcase⟩) hz1
      · push Not at hcase
        have hst : ρ₂ ^ (d - 1) * (1 - ρ₂) < z ^ (d - 1) * (1 - z) :=
          pow_mul_one_sub_strictAntiOn hd (Set.mem_Icc.mpr ⟨hcase.le, (hz2.trans hr2).le⟩)
            (Set.mem_Icc.mpr ⟨hlt2.le, hr2.le⟩) hz2
        linarith
    have hmul := mul_lt_mul_of_pos_left hstep hcpos
    linarith
  · intro z hz2 hz1
    refine Fder_pos_of hd (hr2'.trans hz2) hz1 ?_
    have hstep : z ^ (d - 1) * (1 - z) < ρ₂ ^ (d - 1) * (1 - ρ₂) :=
      pow_mul_one_sub_strictAntiOn hd (Set.mem_Icc.mpr ⟨hlt2.le, hr2.le⟩)
        (Set.mem_Icc.mpr ⟨hlt2.le.trans hz2.le, hz1.le⟩) hz2
    have hmul := mul_lt_mul_of_pos_left hstep hcpos
    linarith

/-! ## Rolle, and monotonicity of `F_{p,γ}` -/

/-- Rolle's theorem between two zeros of `F_{p,γ}` inside `(0,1)`. -/
private theorem exists_rolle (hd : 2 ≤ d) {p γ a b : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (ha : 0 < a) (hab : a < b) (hb : b < 1)
    (ea : Fkkt d p γ a = 0) (eb : Fkkt d p γ b = 0) :
    ∃ c, a < c ∧ c < b ∧ Fder d γ c = 0 := by
  have hcont : ContinuousOn (Fkkt d p γ) (Set.Icc a b) := fun x hx =>
    (hasDerivAt_Fkkt hd hp0 hp1 (lt_of_lt_of_le ha hx.1)
      (lt_of_le_of_lt hx.2 hb)).continuousAt.continuousWithinAt
  obtain ⟨c, hc, hc0⟩ := exists_hasDerivAt_eq_zero (f' := fun z : ℝ => Fder d γ z)
    hab hcont (ea.trans eb.symm)
    (fun x hx => hasDerivAt_Fkkt hd hp0 hp1 (ha.trans hx.1) (hx.2.trans hb))
  exact ⟨c, hc.1, hc.2, hc0⟩

/-- `F_{p,γ}` is strictly increasing on a closed subinterval of `(0,1)` on whose interior
its derivative is positive. -/
private theorem Fkkt_strictMonoOn_of (hd : 2 ≤ d) {p γ a b : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (ha : 0 < a) (hb : b < 1) (hpos : ∀ z : ℝ, a < z → z < b → 0 < Fder d γ z) :
    StrictMonoOn (Fkkt d p γ) (Set.Icc a b) := by
  refine strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc _ _)
    (fun x hx => (hasDerivAt_Fkkt hd hp0 hp1 (lt_of_lt_of_le ha hx.1)
      (lt_of_le_of_lt hx.2 hb)).continuousAt.continuousWithinAt)
    (f' := fun z => Fder d γ z) ?_ ?_
  · intro x hx
    rw [interior_Icc] at hx
    exact (hasDerivAt_Fkkt hd hp0 hp1 (ha.trans hx.1) (hx.2.trans hb)).hasDerivWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    exact hpos x hx.1 hx.2

/-- `F_{p,γ}` is strictly decreasing on a closed subinterval of `(0,1)` on whose interior
its derivative is negative. -/
private theorem Fkkt_strictAntiOn_of (hd : 2 ≤ d) {p γ a b : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (ha : 0 < a) (hb : b < 1) (hneg : ∀ z : ℝ, a < z → z < b → Fder d γ z < 0) :
    StrictAntiOn (Fkkt d p γ) (Set.Icc a b) := by
  refine strictAntiOn_of_hasDerivWithinAt_neg (convex_Icc _ _)
    (fun x hx => (hasDerivAt_Fkkt hd hp0 hp1 (lt_of_lt_of_le ha hx.1)
      (lt_of_le_of_lt hx.2 hb)).continuousAt.continuousWithinAt)
    (f' := fun z => Fder d γ z) ?_ ?_
  · intro x hx
    rw [interior_Icc] at hx
    exact (hasDerivAt_Fkkt hd hp0 hp1 (ha.trans hx.1) (hx.2.trans hb)).hasDerivWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    exact hneg x hx.1 hx.2

/-! ## The sign of `F_{p,γ}` between consecutive roots -/

/-- **`F_{p,γ} > 0` strictly between its first two roots.**  With `z₁ < z₂ < z₃` the three
roots of `eq:three-value-kkt` in `(0,1)`, Rolle gives critical points
`ρ₁ ∈ (z₁,z₂)` and `ρ₂ ∈ (z₂,z₃)`; by `Fder_sign` the derivative is positive on `(z₁,ρ₁)`
and negative on `(ρ₁,z₂)`, so `F_{p,γ}` rises from `0` and falls back to `0`. -/
theorem Fkkt_pos_of_mem_Ioo (hd : 2 ≤ d) {p γ z₁ z₂ z₃ : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (h₁ : 0 < z₁) (h₁₂ : z₁ < z₂) (h₂₃ : z₂ < z₃) (h₃ : z₃ < 1)
    (e₁ : Fkkt d p γ z₁ = 0) (e₂ : Fkkt d p γ z₂ = 0) (e₃ : Fkkt d p γ z₃ = 0)
    {z : ℝ} (hz : z ∈ Set.Ioo z₁ z₂) : 0 < Fkkt d p γ z := by
  obtain ⟨ρ₁, hρ₁a, hρ₁b, k₁⟩ :=
    exists_rolle hd hp0 hp1 h₁ h₁₂ (by linarith) e₁ e₂
  obtain ⟨ρ₂, hρ₂a, hρ₂b, k₂⟩ :=
    exists_rolle hd hp0 hp1 (by linarith) h₂₃ h₃ e₂ e₃
  obtain ⟨sL, sM, _sR⟩ := Fder_sign hd (show (0 : ℝ) < ρ₁ by linarith)
    (show ρ₁ < ρ₂ by linarith) (show ρ₂ < 1 by linarith) k₁ k₂
  by_cases hc : z ≤ ρ₁
  · have hmono := Fkkt_strictMonoOn_of hd hp0 hp1 h₁ (show ρ₁ < 1 by linarith)
      (fun w hw1 hw2 => sL w (by linarith) hw2)
    have hlt := hmono (Set.mem_Icc.mpr ⟨le_rfl, hρ₁a.le⟩)
      (Set.mem_Icc.mpr ⟨hz.1.le, hc⟩) hz.1
    rw [e₁] at hlt
    exact hlt
  · push Not at hc
    have hanti := Fkkt_strictAntiOn_of hd hp0 hp1 (show (0 : ℝ) < ρ₁ by linarith)
      (show z₂ < 1 by linarith) (fun w hw1 hw2 => sM w hw1 (by linarith))
    have hlt := hanti (Set.mem_Icc.mpr ⟨hc.le, hz.2.le⟩)
      (Set.mem_Icc.mpr ⟨hρ₁b.le, le_rfl⟩) hz.2
    rw [e₂] at hlt
    exact hlt

/-- **`F_{p,γ} < 0` strictly between its last two roots.**  The mirror image of
`Fkkt_pos_of_mem_Ioo`: the derivative is negative on `(z₂,ρ₂)` and positive on `(ρ₂,z₃)`,
so `F_{p,γ}` falls from `0` and rises back to `0`. -/
theorem Fkkt_neg_of_mem_Ioo (hd : 2 ≤ d) {p γ z₁ z₂ z₃ : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (h₁ : 0 < z₁) (h₁₂ : z₁ < z₂) (h₂₃ : z₂ < z₃) (h₃ : z₃ < 1)
    (e₁ : Fkkt d p γ z₁ = 0) (e₂ : Fkkt d p γ z₂ = 0) (e₃ : Fkkt d p γ z₃ = 0)
    {z : ℝ} (hz : z ∈ Set.Ioo z₂ z₃) : Fkkt d p γ z < 0 := by
  obtain ⟨ρ₁, hρ₁a, hρ₁b, k₁⟩ :=
    exists_rolle hd hp0 hp1 h₁ h₁₂ (by linarith) e₁ e₂
  obtain ⟨ρ₂, hρ₂a, hρ₂b, k₂⟩ :=
    exists_rolle hd hp0 hp1 (by linarith) h₂₃ h₃ e₂ e₃
  obtain ⟨_sL, sM, sR⟩ := Fder_sign hd (show (0 : ℝ) < ρ₁ by linarith)
    (show ρ₁ < ρ₂ by linarith) (show ρ₂ < 1 by linarith) k₁ k₂
  by_cases hc : z ≤ ρ₂
  · have hanti := Fkkt_strictAntiOn_of hd hp0 hp1 (show (0 : ℝ) < z₂ by linarith)
      (show ρ₂ < 1 by linarith) (fun w hw1 hw2 => sM w (by linarith) hw2)
    have hlt := hanti (Set.mem_Icc.mpr ⟨le_rfl, hρ₂a.le⟩)
      (Set.mem_Icc.mpr ⟨hz.1.le, hc⟩) hz.1
    rw [e₂] at hlt
    exact hlt
  · push Not at hc
    have hmono := Fkkt_strictMonoOn_of hd hp0 hp1 (show (0 : ℝ) < ρ₂ by linarith) h₃
      (fun w hw1 hw2 => sR w hw1 (by linarith))
    have hlt := hmono (Set.mem_Icc.mpr ⟨hc.le, hz.2.le⟩)
      (Set.mem_Icc.mpr ⟨hρ₂b.le, le_rfl⟩) hz.2
    rw [e₃] at hlt
    exact hlt

/-! ## The two differences of `eq:block-proportion-balance` -/

/-- **`𝓜(z₁) < 𝓜(z₂)`.**  `𝓜_{p,γ}` has derivative `F_{p,γ}` (`hasDerivAt_Mfun`), which is
strictly positive on `(z₁,z₂)` by `Fkkt_pos_of_mem_Ioo`.  This is the strict negativity of
the first difference `𝓜(s²) - 𝓜(st)` of `eq:block-proportion-balance`. -/
theorem Mfun_lt_of_root_left (hd : 2 ≤ d) {p γ z₁ z₂ z₃ : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (h₁ : 0 < z₁) (h₁₂ : z₁ < z₂) (h₂₃ : z₂ < z₃) (h₃ : z₃ < 1)
    (e₁ : Fkkt d p γ z₁ = 0) (e₂ : Fkkt d p γ z₂ = 0) (e₃ : Fkkt d p γ z₃ = 0) :
    Mfun d p γ z₁ < Mfun d p γ z₂ := by
  have h₂1 : z₂ < 1 := h₂₃.trans h₃
  have hmono : StrictMonoOn (Mfun d p γ) (Set.Icc z₁ z₂) := by
    refine strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc _ _)
      (fun x hx => (hasDerivAt_Mfun hd hp0 hp1 (lt_of_lt_of_le h₁ hx.1)
        (lt_of_le_of_lt hx.2 h₂1)).continuousAt.continuousWithinAt)
      (f' := fun z => Fkkt d p γ z) ?_ ?_
    · intro x hx
      rw [interior_Icc] at hx
      exact (hasDerivAt_Mfun hd hp0 hp1 (h₁.trans hx.1)
        (hx.2.trans h₂1)).hasDerivWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      exact Fkkt_pos_of_mem_Ioo hd hp0 hp1 h₁ h₁₂ h₂₃ h₃ e₁ e₂ e₃ hx
  exact hmono (Set.mem_Icc.mpr ⟨le_rfl, h₁₂.le⟩) (Set.mem_Icc.mpr ⟨h₁₂.le, le_rfl⟩) h₁₂

/-- **`𝓜(z₃) < 𝓜(z₂)`.**  `F_{p,γ}` is strictly negative on `(z₂,z₃)` by
`Fkkt_neg_of_mem_Ioo`, so `𝓜_{p,γ}` is strictly decreasing there.  This is the strict
negativity of the second difference `𝓜(t²) - 𝓜(st)` of `eq:block-proportion-balance`. -/
theorem Mfun_lt_of_root_right (hd : 2 ≤ d) {p γ z₁ z₂ z₃ : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (h₁ : 0 < z₁) (h₁₂ : z₁ < z₂) (h₂₃ : z₂ < z₃) (h₃ : z₃ < 1)
    (e₁ : Fkkt d p γ z₁ = 0) (e₂ : Fkkt d p γ z₂ = 0) (e₃ : Fkkt d p γ z₃ = 0) :
    Mfun d p γ z₃ < Mfun d p γ z₂ := by
  have h₂0 : (0 : ℝ) < z₂ := h₁.trans h₁₂
  have hanti : StrictAntiOn (Mfun d p γ) (Set.Icc z₂ z₃) := by
    refine strictAntiOn_of_hasDerivWithinAt_neg (convex_Icc _ _)
      (fun x hx => (hasDerivAt_Mfun hd hp0 hp1 (lt_of_lt_of_le h₂0 hx.1)
        (lt_of_le_of_lt hx.2 h₃)).continuousAt.continuousWithinAt)
      (f' := fun z => Fkkt d p γ z) ?_ ?_
    · intro x hx
      rw [interior_Icc] at hx
      exact (hasDerivAt_Mfun hd hp0 hp1 (h₂0.trans hx.1) (hx.2.trans h₃)).hasDerivWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      exact Fkkt_neg_of_mem_Ioo hd hp0 hp1 h₁ h₁₂ h₂₃ h₃ e₁ e₂ e₃ hx
  exact hanti (Set.mem_Icc.mpr ⟨le_rfl, h₂₃.le⟩) (Set.mem_Icc.mpr ⟨h₂₃.le, le_rfl⟩) h₂₃

/-! ## Block-weight stationarity `eq:block-proportion-balance` -/

/-- **The denominator of `eq:block-proportion-formula` is nonzero.**  Both differences
`A = 𝓜(z₁) - 𝓜(z₂)` and `B = 𝓜(z₃) - 𝓜(z₂)` are strictly negative, so `A + B < 0`.  This
replaces the paper's expansion `A + B = -4d³h⁴/3 + O_d(h⁵)` in the proof of
`lem:rank-one-kkt-family`. -/
theorem rowBalance_denom_ne_zero (hd : 2 ≤ d) {p γ z₁ z₂ z₃ : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (h₁ : 0 < z₁) (h₁₂ : z₁ < z₂) (h₂₃ : z₂ < z₃) (h₃ : z₃ < 1)
    (e₁ : Fkkt d p γ z₁ = 0) (e₂ : Fkkt d p γ z₂ = 0) (e₃ : Fkkt d p γ z₃ = 0) :
    (Mfun d p γ z₁ - Mfun d p γ z₂) + (Mfun d p γ z₃ - Mfun d p γ z₂) ≠ 0 := by
  have hA := Mfun_lt_of_root_left hd hp0 hp1 h₁ h₁₂ h₂₃ h₃ e₁ e₂ e₃
  have hB := Mfun_lt_of_root_right hd hp0 hp1 h₁ h₁₂ h₂₃ h₃ e₁ e₂ e₃
  intro hcon
  linarith

/-- **The block weight of `eq:block-proportion-formula` lies in `(0,1)`.**  With `A, B < 0` the
quotient `B/(A+B)` is a genuine convex weight — the admissibility clause `0 < α_h < 1` of
`lem:rank-one-kkt-family`, obtained with no `h`-expansion. -/
theorem rowBalance_alpha_mem (hd : 2 ≤ d) {p γ z₁ z₂ z₃ : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (h₁ : 0 < z₁) (h₁₂ : z₁ < z₂) (h₂₃ : z₂ < z₃) (h₃ : z₃ < 1)
    (e₁ : Fkkt d p γ z₁ = 0) (e₂ : Fkkt d p γ z₂ = 0) (e₃ : Fkkt d p γ z₃ = 0) :
    0 < (Mfun d p γ z₃ - Mfun d p γ z₂) /
        ((Mfun d p γ z₁ - Mfun d p γ z₂) + (Mfun d p γ z₃ - Mfun d p γ z₂)) ∧
      (Mfun d p γ z₃ - Mfun d p γ z₂) /
        ((Mfun d p γ z₁ - Mfun d p γ z₂) + (Mfun d p γ z₃ - Mfun d p γ z₂)) < 1 := by
  have hA := Mfun_lt_of_root_left hd hp0 hp1 h₁ h₁₂ h₂₃ h₃ e₁ e₂ e₃
  have hB := Mfun_lt_of_root_right hd hp0 hp1 h₁ h₁₂ h₂₃ h₃ e₁ e₂ e₃
  have hne := rowBalance_denom_ne_zero hd hp0 hp1 h₁ h₁₂ h₂₃ h₃ e₁ e₂ e₃
  have hmul : (Mfun d p γ z₃ - Mfun d p γ z₂) /
      ((Mfun d p γ z₁ - Mfun d p γ z₂) + (Mfun d p γ z₃ - Mfun d p γ z₂)) *
      ((Mfun d p γ z₁ - Mfun d p γ z₂) + (Mfun d p γ z₃ - Mfun d p γ z₂))
      = Mfun d p γ z₃ - Mfun d p γ z₂ := by
    field_simp
  constructor
  · nlinarith [hmul, hA, hB]
  · nlinarith [hmul, hA, hB]

/-- **The displayed block weight solves `eq:block-proportion-balance`.**  With
`A = 𝓜(z₁) - 𝓜(z₂)`, `B = 𝓜(z₃) - 𝓜(z₂)` and `α = B/(A+B)`, the linear equation
`α·A = (1-α)·B` holds — this is `eq:block-proportion-formula`. -/
theorem rowBalance_solution (hd : 2 ≤ d) {p γ z₁ z₂ z₃ : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (h₁ : 0 < z₁) (h₁₂ : z₁ < z₂) (h₂₃ : z₂ < z₃) (h₃ : z₃ < 1)
    (e₁ : Fkkt d p γ z₁ = 0) (e₂ : Fkkt d p γ z₂ = 0) (e₃ : Fkkt d p γ z₃ = 0) :
    (Mfun d p γ z₃ - Mfun d p γ z₂) /
        ((Mfun d p γ z₁ - Mfun d p γ z₂) + (Mfun d p γ z₃ - Mfun d p γ z₂)) *
        (Mfun d p γ z₁ - Mfun d p γ z₂)
      = (1 - (Mfun d p γ z₃ - Mfun d p γ z₂) /
          ((Mfun d p γ z₁ - Mfun d p γ z₂) + (Mfun d p γ z₃ - Mfun d p γ z₂))) *
        (Mfun d p γ z₃ - Mfun d p γ z₂) := by
  have hne := rowBalance_denom_ne_zero hd hp0 hp1 h₁ h₁₂ h₂₃ h₃ e₁ e₂ e₃
  field_simp
  ring

end SingularEndpoint

end UpperTailOptimizers
