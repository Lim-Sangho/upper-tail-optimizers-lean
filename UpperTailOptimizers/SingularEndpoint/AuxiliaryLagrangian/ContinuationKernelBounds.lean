import UpperTailOptimizers.SingularEndpoint.AuxiliaryLagrangian.KernelInterp
import UpperTailOptimizers.SingularEndpoint.AuxiliaryLagrangian.DistributionLocal
import UpperTailOptimizers.SingularEndpoint.ConstantGraphonComparison.ParityOrder
import UpperTailOptimizers.LZBoundary.ContactMaps

/-!
# `lem:continuation-kernel-bounds`: uniform control of the continued entropy and its kernel

`sec:auxiliary-lagrangian` of `paper/sections/singular_auxiliary_lagrangian.tex` continues the
gap by `Γ̃_d(z) = Γ_d(z)` on `[0,1]` and `Γ̃_d(z) = Γ_d(1) + (z-1)²` on `(1,4]`, and sets

```
J̃_{p_*}(z) := J_{p_*}(r_*) + β_d(z^d - r_*^d) + Γ̃_d(z),
J̃_{p_h}(z) := J̃_{p_*}(z) + Λ_h z + J_{p_h}(0) - J_{p_*}(0),      0 ≤ z ≤ 4,
K_h(x,y)  := J̃_{p_h}(xy),                                          x, y ∈ [0,2],
```

with `Λ_h = ℓ(p_h) - ℓ_*`.  In Lean these are `GamTilde d`, `JpTilde d` and
`KKTFamily.JpTildeH B h` (the same formulas, with `ℓ_* = ell (pStar d)`), and the kernel is
`KKTFamily.contKernel B h x y = B.JpTildeH h (x * y)`, the integrand of `distributionJ`.
`contKernel_zero` identifies `K_0` with `J̃_{p_*}(xy)`, and `contKernel_eq_kernel` identifies
`K_h` with the plain kernel `J_{p_h}(xy)` wherever `xy ∈ [0,1]`.

**`lem:continuation-kernel-bounds`** asserts one `C_d ≥ 1` and one `h₀ > 0` such that, for
`0 ≤ h < h₀`, `z, z' ∈ [0,4]` and `x, x', y ∈ [0,2]`,

```
|J̃_{p_h}(z) - J̃_{p_h}(z')| ≤ C_d |z - z'|^{1/2},   ‖J̃_{p_h} - J̃_{p_*}‖_∞ ≤ C_d h²,   ‖J̃_{p_h}‖_∞ ≤ C_d,
|K_h(x,y) - K_h(x',y)|   ≤ C_d |x - x'|^{1/2},    ‖K_h - K_0‖_∞ ≤ C_d h²,           ‖K_h‖_∞ ≤ C_d.
```

`continuation_kernel_bounds` states exactly this, with `|·|^{1/2}` written `Real.sqrt |·|`, the
sup norms written pointwise on the stated domains (the functions are continuous), and the
constants depending only on `d` and the family `B`.

## The proof

* **Hölder.**  The logarithmic modulus `exists_JpTilde_modulus` gives
  `|J̃_{p_*}(z) - J̃_{p_*}(z')| ≤ C τ(1 + log⁺(1/τ))` with `τ = |z - z'| ≤ 4`, and
  `mul_logMod_le_three_sqrt` is `τ(1 + log⁺(1/τ)) ≤ 3√τ` on `[0,4]` (from `log x ≤ x - 1` at
  `x = 1/√τ`).
* **`O(h²)` shift.**  `h ↦ Λ_h` and `h ↦ J_{p_h}(0) - J_{p_*}(0)` are analytic at `0`, even,
  and vanish at `0`, so `exists_pow_bound_of_reflect` makes both `O(h²)`
  (`exists_shift_sq_bound`).
* **Uniform bound.**  `J̃_{p_*}` is continuous on the compact `[0,4]`.
* **Kernel.**  All three kernel bounds are the continuation bounds at `z = xy`, `z' = x'y`,
  using `|xy - x'y| ≤ 2|x - x'|`.
-/

namespace UpperTailOptimizers

namespace SingularEndpoint

open Filter Topology

variable {d : ℕ}

/-! ## The modulus `τ(1 + log⁺(1/τ))` is at most `3√τ` on `[0,4]` -/

/-- **`τ(1 + log⁺(1/τ)) ≤ 3√τ` for `0 ≤ τ ≤ 4`.**  For `0 < τ ≤ 1`, `log x ≤ x - 1` at
`x = 1/√τ` gives `log(1/τ) ≤ 2/√τ - 2`, so the left side is at most `2√τ - τ`; for `1 < τ ≤ 4`
the positive part vanishes and `τ = √τ·√τ ≤ 2√τ`. -/
theorem mul_logMod_le_three_sqrt {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ4 : τ ≤ 4) :
    τ * (1 + max 0 (Real.log (1 / τ))) ≤ 3 * Real.sqrt τ := by
  have hs0 : 0 ≤ Real.sqrt τ := Real.sqrt_nonneg τ
  have hss : Real.sqrt τ ^ 2 = τ := Real.sq_sqrt hτ0
  have hs2 : Real.sqrt τ ≤ 2 := by
    calc Real.sqrt τ ≤ Real.sqrt 4 := Real.sqrt_le_sqrt hτ4
      _ = 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  rcases eq_or_lt_of_le hτ0 with h0 | hpos
  · rw [← h0]
    simp
  rcases le_or_gt τ 1 with h1 | h1
  · have hspos : 0 < Real.sqrt τ := Real.sqrt_pos.mpr hpos
    have hlogs : Real.log (1 / Real.sqrt τ) ≤ 1 / Real.sqrt τ - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    have hlogτ : Real.log (1 / τ) = 2 * Real.log (1 / Real.sqrt τ) := by
      conv_lhs => rw [← hss]
      rw [one_div, one_div, Real.log_inv, Real.log_inv, Real.log_pow]
      push_cast
      ring
    have hnn : 0 ≤ Real.log (1 / τ) := by
      rw [one_div, Real.log_inv]
      linarith [Real.log_nonpos hτ0 h1]
    rw [max_eq_right hnn, hlogτ]
    have hkey : τ * (1 + 2 * Real.log (1 / Real.sqrt τ))
        ≤ τ * (1 + 2 * (1 / Real.sqrt τ - 1)) :=
      mul_le_mul_of_nonneg_left (by linarith) hτ0
    have hval : τ * (1 + 2 * (1 / Real.sqrt τ - 1)) = 2 * Real.sqrt τ - τ := by
      have hdiv : τ / Real.sqrt τ = Real.sqrt τ := by
        rw [div_eq_iff hspos.ne', ← sq, hss]
      calc τ * (1 + 2 * (1 / Real.sqrt τ - 1)) = 2 * (τ / Real.sqrt τ) - τ := by ring
        _ = 2 * Real.sqrt τ - τ := by rw [hdiv]
    linarith
  · have hneg : Real.log (1 / τ) ≤ 0 := by
      rw [one_div, Real.log_inv]
      linarith [Real.log_pos h1]
    rw [max_eq_left hneg]
    nlinarith

/-! ## The continued kernel -/

namespace KKTFamily

/-- **The continued kernel** `K_h(x,y) := J̃_{p_h}(xy)` of `sec:auxiliary-lagrangian`,
defined on `[0,2]²`.  It is the integrand of `distributionJ`. -/
noncomputable def contKernel (B : KKTFamily d) (h x y : ℝ) : ℝ := B.JpTildeH h (x * y)

/-- `K_0(x,y) = J̃_{p_*}(xy)`, since `p_0 = p_*`. -/
theorem contKernel_zero (B : KKTFamily d) (x y : ℝ) : B.contKernel 0 x y = JpTilde d (x * y) :=
  B.JpTildeH_zero (x * y)

/-- The auxiliary factor functional `𝒥_h(ξ) = ∬ K_h dξ dξ` of `sec:auxiliary-lagrangian` is
`distributionJ`: its integrand is the continued kernel. -/
theorem distributionJ_eq_contKernel (B : KKTFamily d) (h : ℝ) (ν : MeasureTheory.Measure ℝ) :
    B.distributionJ h ν = ∫ x, ∫ y, B.contKernel h x y ∂ν ∂ν := rfl

/-- Where `xy ∈ [0,1]` the continued kernel is the plain kernel `J_{p_h}(xy)`. -/
theorem contKernel_eq_kernel (hd : 2 ≤ d) {B : KKTFamily d} {h : ℝ} (hh : |h| < B.h₀)
    {x y : ℝ} (hxy0 : 0 ≤ x * y) (hxy1 : x * y ≤ 1) : B.contKernel h x y = B.kernel h x y :=
  JpTildeH_eq_Jp hd hh hxy0 hxy1

/-! ## The shift `J̃_{p_h} - J̃_{p_*}` is `O(h²)` -/

/-- **`Λ_h = O(h²)` and `J_{p_h}(0) - J_{p_*}(0) = O(h²)`.**  Both are analytic at `h = 0`
(`p_0 = p_* ∈ (0,1)`), even (`p_{-h} = p_h`) and vanish at `0`, so the two-order gain
`exists_pow_bound_of_reflect` applies at `n = 0`. -/
theorem exists_shift_sq_bound (hd : 2 ≤ d) (B : KKTFamily d) :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∀ h : ℝ, |h| < δ →
      |ell (B.p h) - ell (pStar d)| ≤ C * h ^ 2 ∧
        |Jp (B.p h) 0 - Jp (pStar d) 0| ≤ C * h ^ 2 := by
  have hp0 : 0 < pStar d := pStar_pos hd
  have hp1 : pStar d < 1 := pStar_lt_one hd
  have hpA : AnalyticAt ℝ B.p 0 := B.analyticAt_p 0 (zero_mem_window B)
  have hB0 : B.p 0 = pStar d := B.p_zero
  -- `h ↦ Λ_h`
  have hellA : AnalyticAt ℝ (fun h => ell (B.p h) - ell (pStar d)) 0 := by
    have hdiv : AnalyticAt ℝ (fun h => (1 - B.p h) / B.p h) 0 :=
      (analyticAt_const.sub hpA).div hpA (by rw [hB0]; exact hp0.ne')
    have hlog : AnalyticAt ℝ (fun h => Real.log ((1 - B.p h) / B.p h)) 0 :=
      analyticAt_log_comp hdiv (by rw [hB0]; exact div_pos (by linarith) hp0)
    exact hlog.sub analyticAt_const
  -- `h ↦ J_{p_h}(0) - J_{p_*}(0) = -log(1 - p_h) + log(1 - p_*)`
  have hJA : AnalyticAt ℝ (fun h => Jp (B.p h) 0 - Jp (pStar d) 0) 0 := by
    simp only [Jp_zero]
    have hlog : AnalyticAt ℝ (fun h => Real.log (1 - B.p h)) 0 :=
      analyticAt_log_comp (analyticAt_const.sub hpA) (by rw [hB0]; linarith)
    exact hlog.neg.sub analyticAt_const
  have hlim : ∀ F : ℝ → ℝ, ContinuousAt F 0 → F 0 = 0 →
      Tendsto (fun h : ℝ => F h / h ^ 0) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    intro F hF hF0
    have h1 : Tendsto F (𝓝 (0 : ℝ)) (𝓝 0) := by
      have := hF.tendsto
      rwa [hF0] at this
    simpa using h1.mono_left nhdsWithin_le_nhds
  obtain ⟨C₁, δ₁, hC₁, hδ₁, hb₁⟩ := exists_pow_bound_of_reflect (n := 0) hellA
    (fun h => by simp only [B.p_even, pow_zero, one_mul])
    (hlim _ hellA.continuousAt (by simp only [hB0, sub_self]))
  obtain ⟨C₂, δ₂, hC₂, hδ₂, hb₂⟩ := exists_pow_bound_of_reflect (n := 0) hJA
    (fun h => by simp only [B.p_even, pow_zero, one_mul])
    (hlim _ hJA.continuousAt (by simp only [hB0, sub_self]))
  refine ⟨C₁ + C₂, min δ₁ δ₂, by linarith, lt_min hδ₁ hδ₂, fun h hh => ?_⟩
  have hsq : |h| ^ (0 + 2) = h ^ 2 := by rw [zero_add, sq_abs]
  have h1 := hb₁ h (lt_of_lt_of_le hh (min_le_left _ _))
  have h2 := hb₂ h (lt_of_lt_of_le hh (min_le_right _ _))
  rw [hsq] at h1 h2
  have hh2 : (0 : ℝ) ≤ h ^ 2 := sq_nonneg h
  constructor
  · exact le_trans h1 (mul_le_mul_of_nonneg_right (by linarith) hh2)
  · exact le_trans h2 (mul_le_mul_of_nonneg_right (by linarith) hh2)

end KKTFamily

/-! ## `lem:continuation-kernel-bounds` -/

/-- **`J̃_{p_*}` is `1/2`-Hölder on `[0,4]`**, from the logarithmic modulus. -/
theorem exists_JpTilde_sqrt_holder (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ u ∈ Set.Icc (0 : ℝ) 4, ∀ u' ∈ Set.Icc (0 : ℝ) 4,
      |JpTilde d u - JpTilde d u'| ≤ C * Real.sqrt |u - u'| := by
  obtain ⟨C₀, hC₀, hmod⟩ := exists_JpTilde_modulus (d := d) hd
  refine ⟨3 * C₀, by positivity, fun u hu u' hu' => ?_⟩
  have hτ4 : |u - u'| ≤ 4 := abs_le.mpr ⟨by linarith [hu.1, hu'.2], by linarith [hu.2, hu'.1]⟩
  have h1 := hmod u hu u' hu'
  have h2 := mul_logMod_le_three_sqrt (abs_nonneg (u - u')) hτ4
  calc |JpTilde d u - JpTilde d u'|
      ≤ C₀ * |u - u'| * (1 + max 0 (Real.log (1 / |u - u'|))) := h1
    _ = C₀ * (|u - u'| * (1 + max 0 (Real.log (1 / |u - u'|)))) := by ring
    _ ≤ C₀ * (3 * Real.sqrt |u - u'|) := mul_le_mul_of_nonneg_left h2 hC₀.le
    _ = 3 * C₀ * Real.sqrt |u - u'| := by ring

/-- **`lem:continuation-kernel-bounds`.**  There are `C ≥ 1` and `h₀ > 0` (inside the family
window) such that for every `0 ≤ h < h₀`, `z, z' ∈ [0,4]` and `x, x', y ∈ [0,2]`:

* `|J̃_{p_h}(z) - J̃_{p_h}(z')| ≤ C|z - z'|^{1/2}`;
* `|J̃_{p_h}(z) - J̃_{p_*}(z)| ≤ Ch²`, i.e. `‖J̃_{p_h} - J̃_{p_*}‖_{L^∞([0,4])} ≤ Ch²`;
* `|J̃_{p_h}(z)| ≤ C`;
* `|K_h(x,y) - K_h(x',y)| ≤ C|x - x'|^{1/2}`;
* `|K_h(x,y) - K_0(x,y)| ≤ Ch²`;
* `|K_h(x,y)| ≤ C`.

The constants depend only on `d` and the family `B`. -/
theorem continuation_kernel_bounds (hd : 2 ≤ d) (B : KKTFamily d) :
    ∃ C h₀ : ℝ, 1 ≤ C ∧ 0 < h₀ ∧ h₀ ≤ B.h₀ ∧ ∀ h : ℝ, 0 ≤ h → h < h₀ →
      (∀ z ∈ Set.Icc (0 : ℝ) 4, ∀ z' ∈ Set.Icc (0 : ℝ) 4,
          |B.JpTildeH h z - B.JpTildeH h z'| ≤ C * Real.sqrt |z - z'|) ∧
      (∀ z ∈ Set.Icc (0 : ℝ) 4, |B.JpTildeH h z - JpTilde d z| ≤ C * h ^ 2) ∧
      (∀ z ∈ Set.Icc (0 : ℝ) 4, |B.JpTildeH h z| ≤ C) ∧
      (∀ x ∈ Set.Icc (0 : ℝ) 2, ∀ x' ∈ Set.Icc (0 : ℝ) 2, ∀ y ∈ Set.Icc (0 : ℝ) 2,
          |B.contKernel h x y - B.contKernel h x' y| ≤ C * Real.sqrt |x - x'|) ∧
      (∀ x ∈ Set.Icc (0 : ℝ) 2, ∀ y ∈ Set.Icc (0 : ℝ) 2,
          |B.contKernel h x y - B.contKernel 0 x y| ≤ C * h ^ 2) ∧
      (∀ x ∈ Set.Icc (0 : ℝ) 2, ∀ y ∈ Set.Icc (0 : ℝ) 2, |B.contKernel h x y| ≤ C) := by
  obtain ⟨CH, hCH, hhold⟩ := exists_JpTilde_sqrt_holder (d := d) hd
  obtain ⟨CS, δS, hCS, hδS, hshift⟩ := B.exists_shift_sq_bound hd
  obtain ⟨M₀, hM₀⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 4)).exists_bound_of_continuousOn
    (continuousOn_JpTilde hd)
  have hM₀0 : 0 ≤ M₀ := le_trans (norm_nonneg _) (hM₀ 0 ⟨le_rfl, by norm_num⟩)
  -- the three constants
  obtain ⟨CJ, hCJ⟩ : ∃ C : ℝ, C = CH + 2 * CS := ⟨_, rfl⟩
  obtain ⟨CD, hCD⟩ : ∃ C : ℝ, C = 5 * CS := ⟨_, rfl⟩
  obtain ⟨CB, hCB⟩ : ∃ C : ℝ, C = M₀ + 5 * CS := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = 1 + 2 * CJ + CD + CB := ⟨_, rfl⟩
  have hCJ0 : 0 ≤ CJ := by rw [hCJ]; positivity
  have hCD0 : 0 ≤ CD := by rw [hCD]; positivity
  have hCB0 : 0 ≤ CB := by rw [hCB]; positivity
  have hC1 : 1 ≤ C := by rw [hC]; linarith
  have hCJC : 2 * CJ ≤ C := by rw [hC]; linarith
  have hCDC : CD ≤ C := by rw [hC]; linarith
  have hCBC : CB ≤ C := by rw [hC]; linarith
  refine ⟨C, min (min δS 1) B.h₀, hC1, lt_min (lt_min hδS one_pos) B.h₀_pos, min_le_right _ _, ?_⟩
  intro h hh0 hhlt
  have hhδ : |h| < δS := by
    rw [abs_of_nonneg hh0]
    exact lt_of_lt_of_le hhlt (le_trans (min_le_left _ _) (min_le_left _ _))
  have hh1 : h ≤ 1 := le_trans hhlt.le (le_trans (min_le_left _ _) (min_le_right _ _))
  have hhsq : h ^ 2 ≤ 1 := by nlinarith
  obtain ⟨hΛ, hK⟩ := hshift h hhδ
  have hΛ1 : |ell (B.p h) - ell (pStar d)| ≤ CS := by
    calc |ell (B.p h) - ell (pStar d)| ≤ CS * h ^ 2 := hΛ
      _ ≤ CS * 1 := mul_le_mul_of_nonneg_left hhsq hCS.le
      _ = CS := mul_one _
  -- the displacement formulas
  have hdiff : ∀ u u' : ℝ, B.JpTildeH h u - B.JpTildeH h u'
      = (JpTilde d u - JpTilde d u') + (ell (B.p h) - ell (pStar d)) * (u - u') := by
    intro u u'
    simp only [KKTFamily.JpTildeH]
    ring
  have hshiftEq : ∀ u : ℝ, B.JpTildeH h u - JpTilde d u
      = (ell (B.p h) - ell (pStar d)) * u + (Jp (B.p h) 0 - Jp (pStar d) 0) := by
    intro u
    simp only [KKTFamily.JpTildeH]
    ring
  -- (1) Hölder bound for `J̃_{p_h}`
  have hJhold : ∀ u ∈ Set.Icc (0 : ℝ) 4, ∀ u' ∈ Set.Icc (0 : ℝ) 4,
      |B.JpTildeH h u - B.JpTildeH h u'| ≤ CJ * Real.sqrt |u - u'| := by
    intro u hu u' hu'
    have hτ4 : |u - u'| ≤ 4 :=
      abs_le.mpr ⟨by linarith [hu.1, hu'.2], by linarith [hu.2, hu'.1]⟩
    have hsq0 : 0 ≤ Real.sqrt |u - u'| := Real.sqrt_nonneg _
    have hsqle : Real.sqrt |u - u'| ≤ 2 := by
      calc Real.sqrt |u - u'| ≤ Real.sqrt 4 := Real.sqrt_le_sqrt hτ4
        _ = 2 := by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
    have hlin : |u - u'| ≤ 2 * Real.sqrt |u - u'| := by
      have hss : Real.sqrt |u - u'| ^ 2 = |u - u'| := Real.sq_sqrt (abs_nonneg _)
      nlinarith
    rw [hdiff]
    calc |(JpTilde d u - JpTilde d u') + (ell (B.p h) - ell (pStar d)) * (u - u')|
        ≤ |JpTilde d u - JpTilde d u'| + |(ell (B.p h) - ell (pStar d)) * (u - u')| :=
          abs_add_le _ _
      _ ≤ CH * Real.sqrt |u - u'| + CS * (2 * Real.sqrt |u - u'|) := by
          refine add_le_add (hhold u hu u' hu') ?_
          rw [abs_mul]
          exact mul_le_mul hΛ1 hlin (abs_nonneg _) hCS.le
      _ = CJ * Real.sqrt |u - u'| := by rw [hCJ]; ring
  -- (2) the `O(h²)` shift
  have hJshift : ∀ u ∈ Set.Icc (0 : ℝ) 4, |B.JpTildeH h u - JpTilde d u| ≤ CD * h ^ 2 := by
    intro u hu
    rw [hshiftEq]
    have hu4 : |u| ≤ 4 := by rw [abs_of_nonneg hu.1]; exact hu.2
    calc |(ell (B.p h) - ell (pStar d)) * u + (Jp (B.p h) 0 - Jp (pStar d) 0)|
        ≤ |(ell (B.p h) - ell (pStar d)) * u| + |Jp (B.p h) 0 - Jp (pStar d) 0| :=
          abs_add_le _ _
      _ ≤ CS * h ^ 2 * 4 + CS * h ^ 2 := by
          refine add_le_add ?_ hK
          rw [abs_mul]
          exact mul_le_mul hΛ hu4 (abs_nonneg _) (by positivity)
      _ = CD * h ^ 2 := by rw [hCD]; ring
  -- (3) the uniform bound
  have hJbd : ∀ u ∈ Set.Icc (0 : ℝ) 4, |B.JpTildeH h u| ≤ CB := by
    intro u hu
    have h0 : |JpTilde d u| ≤ M₀ := by
      have := hM₀ u hu
      rwa [Real.norm_eq_abs] at this
    have h1 := hJshift u hu
    have h2 : CD * h ^ 2 ≤ 5 * CS := by
      rw [hCD]
      nlinarith [hCS.le]
    calc |B.JpTildeH h u| = |JpTilde d u + (B.JpTildeH h u - JpTilde d u)| := by ring_nf
      _ ≤ |JpTilde d u| + |B.JpTildeH h u - JpTilde d u| := abs_add_le _ _
      _ ≤ M₀ + 5 * CS := by linarith
      _ = CB := by rw [hCB]
  -- products of points of `[0,2]` lie in `[0,4]`
  have hprod : ∀ x ∈ Set.Icc (0 : ℝ) 2, ∀ y ∈ Set.Icc (0 : ℝ) 2, x * y ∈ Set.Icc (0 : ℝ) 4 := by
    intro x hx y hy
    exact ⟨mul_nonneg hx.1 hy.1, by nlinarith [hx.1, hx.2, hy.1, hy.2]⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u hu u' hu'
    exact le_trans (hJhold u hu u' hu')
      (mul_le_mul_of_nonneg_right (by linarith) (Real.sqrt_nonneg _))
  · intro u hu
    exact le_trans (hJshift u hu) (mul_le_mul_of_nonneg_right hCDC (sq_nonneg h))
  · intro u hu
    exact le_trans (hJbd u hu) hCBC
  · intro x hx x' hx' y hy
    have h1 := hJhold (x * y) (hprod x hx y hy) (x' * y) (hprod x' hx' y hy)
    have hxy : |x * y - x' * y| ≤ 2 * |x - x'| := by
      rw [show x * y - x' * y = (x - x') * y by ring, abs_mul, abs_of_nonneg hy.1, mul_comm]
      exact mul_le_mul_of_nonneg_right hy.2 (abs_nonneg _)
    have hsq : Real.sqrt |x * y - x' * y| ≤ 2 * Real.sqrt |x - x'| := by
      calc Real.sqrt |x * y - x' * y| ≤ Real.sqrt (2 * |x - x'|) := Real.sqrt_le_sqrt hxy
        _ = Real.sqrt 2 * Real.sqrt |x - x'| := Real.sqrt_mul (by norm_num) _
        _ ≤ 2 * Real.sqrt |x - x'| := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
          rw [Real.sqrt_le_left (by norm_num : (0 : ℝ) ≤ 2)]
          norm_num
    calc |B.contKernel h x y - B.contKernel h x' y|
        ≤ CJ * Real.sqrt |x * y - x' * y| := h1
      _ ≤ CJ * (2 * Real.sqrt |x - x'|) := mul_le_mul_of_nonneg_left hsq hCJ0
      _ = 2 * CJ * Real.sqrt |x - x'| := by ring
      _ ≤ C * Real.sqrt |x - x'| := mul_le_mul_of_nonneg_right hCJC (Real.sqrt_nonneg _)
  · intro x hx y hy
    rw [KKTFamily.contKernel_zero]
    exact le_trans (hJshift (x * y) (hprod x hx y hy))
      (mul_le_mul_of_nonneg_right hCDC (sq_nonneg h))
  · intro x hx y hy
    exact le_trans (hJbd (x * y) (hprod x hx y hy)) hCBC

end SingularEndpoint

end UpperTailOptimizers
