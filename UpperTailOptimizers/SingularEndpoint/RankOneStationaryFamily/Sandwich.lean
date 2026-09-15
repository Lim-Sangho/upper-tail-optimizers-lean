import UpperTailOptimizers.SingularEndpoint.RankOneStationaryFamily.Interp3
import UpperTailOptimizers.SingularEndpoint.RankOneStationaryFamily.CubicInt

/-!
# The two-sided cubic sandwich (Section 5, `paper/sections/singular.tex`)

The analytic input to `eq:rank-one-parameter-expansions`, in a form that mentions neither the
family nor Section 5.

Let `f` be three times differentiable on `[a,b]`, vanishing at three interior nodes
`z₁ < z₂ < z₃`, and let `F` be an antiderivative of `f`.  The three-node Lagrange remainder
of `SingularEndpoint/RankOneStationaryFamily/Interp3.lean` writes

    f z = (f''' ξ / 6) · (z - z₁)(z - z₂)(z - z₃)

pointwise, and the node cubic integrates in closed form over each subinterval
(`SingularEndpoint/RankOneStationaryFamily/CubicInt.lean`).  So any two-sided bound `m ≤ f''' ≤ M` on `[a,b]` transfers to a
two-sided bound on the two increments `F z₂ - F z₁` and `F z₃ - F z₂`, with the *same*
explicit cubic factor on both sides.

This is what replaces the paper's analytic Weierstrass division `𝓜_h' = D_h · R`
(`eq:mh-factorization-proof`; `𝓜_h'` is the `𝓛_h` of `app:rank-one-parameter-expansions`).  The
division produces an exact analytic quotient `R`; the sandwich produces only upper and lower
bounds — but the bounds pinch as `m, M → f'''`, which is all the order argument needs, and
unlike the division it costs no analyticity at all.

Note the orientation: on `(z₁, z₂)` the node cubic is positive and on `(z₂, z₃)` it is
negative, so the right-hand statement has `m` and `M` **exchanged**.

## Contents

* `increment_sandwich_left` — bounds on `F z₂ - F z₁` by `m/6·a³(a+2b)/12` and `M/6·…`;
* `increment_sandwich_right` — bounds on `F z₃ - F z₂` by `M/6·(-b³(b+2a)/12)` and `m/6·…`.
-/

namespace UpperTailOptimizers

open MeasureTheory intervalIntegral

/-! ## Sign of the node cubic on the closed subintervals -/

/-- On the closed left subinterval the node cubic is non-negative: it is positive inside
(`Pcube_pos_of_mem_Ioo_left`) and vanishes at the two endpoints. -/
private theorem Pcube_nonneg_left {z1 z2 z3 z : ℝ} (h12 : z1 < z2) (h23 : z2 < z3)
    (hz : z ∈ Set.Icc z1 z2) : 0 ≤ Pcube z1 z2 z3 z := by
  rcases eq_or_lt_of_le hz.1 with rfl | hlo
  · simp [Pcube]
  rcases eq_or_lt_of_le hz.2 with rfl | hhi
  · simp [Pcube]
  exact (Pcube_pos_of_mem_Ioo_left h12 h23 ⟨hlo, hhi⟩).le

/-- On the closed right subinterval the node cubic is non-positive. -/
private theorem Pcube_nonpos_right {z1 z2 z3 z : ℝ} (h12 : z1 < z2) (h23 : z2 < z3)
    (hz : z ∈ Set.Icc z2 z3) : Pcube z1 z2 z3 z ≤ 0 := by
  rcases eq_or_lt_of_le hz.1 with rfl | hlo
  · simp [Pcube]
  rcases eq_or_lt_of_le hz.2 with rfl | hhi
  · simp [Pcube]
  exact (Pcube_neg_of_mem_Ioo_right h12 h23 ⟨hlo, hhi⟩).le

/-! ## Integrability bookkeeping -/

private theorem intervalIntegrable_of_hasDerivAt {F f : ℝ → ℝ} {u v : ℝ} (huv : u ≤ v)
    (hF : ∀ x ∈ Set.Icc u v, HasDerivAt F (f x) x)
    (hf : ContinuousOn f (Set.Icc u v)) : IntervalIntegrable f volume u v := by
  have _ := hF
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le huv]
  exact hf.integrableOn_Icc

private theorem intervalIntegrable_Pcube (z1 z2 z3 u v : ℝ) :
    IntervalIntegrable (fun z => Pcube z1 z2 z3 z) volume u v := by
  apply Continuous.intervalIntegrable
  unfold Pcube
  fun_prop

private theorem intervalIntegrable_const_mul_Pcube (c z1 z2 z3 u v : ℝ) :
    IntervalIntegrable (fun z => c * Pcube z1 z2 z3 z) volume u v :=
  (intervalIntegrable_Pcube z1 z2 z3 u v).const_mul c

/-! ## The sandwich -/

/-- **The left increment.**

`F z₂ - F z₁ = ∫_{z₁}^{z₂} f`, and on that interval `f` equals `f₃(ξ)/6` times the node
cubic, which is non-negative there.  So the increment is pinched between the two multiples
of `∫_{z₁}^{z₂} (z-z₁)(z-z₂)(z-z₃) = a³(a+2b)/12` with `a = z₂ - z₁`, `b = z₃ - z₂`. -/
theorem increment_sandwich_left {f f₁ f₂ f₃ F : ℝ → ℝ} {a b : ℝ}
    (hf : ∀ x ∈ Set.Icc a b, HasDerivAt f (f₁ x) x)
    (hf₁ : ∀ x ∈ Set.Icc a b, HasDerivAt f₁ (f₂ x) x)
    (hf₂ : ∀ x ∈ Set.Icc a b, HasDerivAt f₂ (f₃ x) x)
    (hF : ∀ x ∈ Set.Icc a b, HasDerivAt F (f x) x)
    {z₁ z₂ z₃ : ℝ}
    (hz₁ : z₁ ∈ Set.Icc a b) (hz₂ : z₂ ∈ Set.Icc a b) (hz₃ : z₃ ∈ Set.Icc a b)
    (h₁₂ : z₁ < z₂) (h₂₃ : z₂ < z₃)
    (e₁ : f z₁ = 0) (e₂ : f z₂ = 0) (e₃ : f z₃ = 0)
    {m M : ℝ} (hm : ∀ x ∈ Set.Icc a b, m ≤ f₃ x) (hM : ∀ x ∈ Set.Icc a b, f₃ x ≤ M) :
    m / 6 * ((z₂ - z₁) ^ 3 * ((z₂ - z₁) + 2 * (z₃ - z₂)) / 12) ≤ F z₂ - F z₁ ∧
      F z₂ - F z₁ ≤ M / 6 * ((z₂ - z₁) ^ 3 * ((z₂ - z₁) + 2 * (z₃ - z₂)) / 12) := by
  -- the left subinterval sits inside `[a,b]`
  have hsub : Set.Icc z₁ z₂ ⊆ Set.Icc a b := fun x hx =>
    ⟨hz₁.1.trans hx.1, hx.2.trans hz₂.2⟩
  have hle : z₁ ≤ z₂ := h₁₂.le
  -- `f` is continuous there, hence integrable
  have hfc : ContinuousOn f (Set.Icc z₁ z₂) := fun x hx =>
    ((hf x (hsub hx)).continuousAt).continuousWithinAt
  have hfi : IntervalIntegrable f volume z₁ z₂ :=
    intervalIntegrable_of_hasDerivAt hle (fun x hx => hF x (hsub hx)) hfc
  -- the fundamental theorem of calculus
  have hFTC : ∫ z in z₁..z₂, f z = F z₂ - F z₁ := by
    refine integral_eq_sub_of_hasDerivAt (fun x hx => hF x (hsub ?_)) hfi
    rwa [Set.uIcc_of_le hle] at hx
  -- the pointwise two-sided bound coming from the Lagrange remainder
  have hpt : ∀ x ∈ Set.Icc z₁ z₂,
      m / 6 * Pcube z₁ z₂ z₃ x ≤ f x ∧ f x ≤ M / 6 * Pcube z₁ z₂ z₃ x := by
    intro x hx
    obtain ⟨ξ, hξ, hval⟩ :=
      exists_deriv3_eq_of_three_roots hf hf₁ hf₂ hz₁ hz₂ hz₃ h₁₂ h₂₃ e₁ e₂ e₃ (hsub hx)
    have hP : 0 ≤ Pcube z₁ z₂ z₃ x := Pcube_nonneg_left h₁₂ h₂₃ hx
    have hval' : f x = f₃ ξ / 6 * Pcube z₁ z₂ z₃ x := by rw [hval, Pcube]
    constructor
    · rw [hval']
      exact mul_le_mul_of_nonneg_right (by linarith [hm ξ hξ]) hP
    · rw [hval']
      exact mul_le_mul_of_nonneg_right (by linarith [hM ξ hξ]) hP
  -- integrate the two halves of the bound
  have hlow : ∫ z in z₁..z₂, m / 6 * Pcube z₁ z₂ z₃ z ≤ ∫ z in z₁..z₂, f z :=
    integral_mono_on hle (intervalIntegrable_const_mul_Pcube _ _ _ _ _ _) hfi
      fun x hx => (hpt x hx).1
  have hhigh : ∫ z in z₁..z₂, f z ≤ ∫ z in z₁..z₂, M / 6 * Pcube z₁ z₂ z₃ z :=
    integral_mono_on hle hfi (intervalIntegrable_const_mul_Pcube _ _ _ _ _ _)
      fun x hx => (hpt x hx).2
  -- and evaluate the cubic integrals in closed form
  have hval : ∀ c : ℝ, ∫ z in z₁..z₂, c * Pcube z₁ z₂ z₃ z
      = c * ((z₂ - z₁) ^ 3 * ((z₂ - z₁) + 2 * (z₃ - z₂)) / 12) := by
    intro c
    rw [intervalIntegral.integral_const_mul, integral_Pcube_left]
  rw [hval, hFTC] at hlow
  rw [hval, hFTC] at hhigh
  exact ⟨hlow, hhigh⟩

/-- **The right increment.**

Same argument on `(z₂, z₃)`, where the node cubic is *negative*: multiplying the bound
`m ≤ f₃ ξ ≤ M` by a non-positive number reverses it, so `m` and `M` swap sides.  The cubic
integral there is `-b³(b+2a)/12`. -/
theorem increment_sandwich_right {f f₁ f₂ f₃ F : ℝ → ℝ} {a b : ℝ}
    (hf : ∀ x ∈ Set.Icc a b, HasDerivAt f (f₁ x) x)
    (hf₁ : ∀ x ∈ Set.Icc a b, HasDerivAt f₁ (f₂ x) x)
    (hf₂ : ∀ x ∈ Set.Icc a b, HasDerivAt f₂ (f₃ x) x)
    (hF : ∀ x ∈ Set.Icc a b, HasDerivAt F (f x) x)
    {z₁ z₂ z₃ : ℝ}
    (hz₁ : z₁ ∈ Set.Icc a b) (hz₂ : z₂ ∈ Set.Icc a b) (hz₃ : z₃ ∈ Set.Icc a b)
    (h₁₂ : z₁ < z₂) (h₂₃ : z₂ < z₃)
    (e₁ : f z₁ = 0) (e₂ : f z₂ = 0) (e₃ : f z₃ = 0)
    {m M : ℝ} (hm : ∀ x ∈ Set.Icc a b, m ≤ f₃ x) (hM : ∀ x ∈ Set.Icc a b, f₃ x ≤ M) :
    M / 6 * (-((z₃ - z₂) ^ 3 * ((z₃ - z₂) + 2 * (z₂ - z₁)) / 12)) ≤ F z₃ - F z₂ ∧
      F z₃ - F z₂ ≤ m / 6 * (-((z₃ - z₂) ^ 3 * ((z₃ - z₂) + 2 * (z₂ - z₁)) / 12)) := by
  have hsub : Set.Icc z₂ z₃ ⊆ Set.Icc a b := fun x hx =>
    ⟨hz₂.1.trans hx.1, hx.2.trans hz₃.2⟩
  have hle : z₂ ≤ z₃ := h₂₃.le
  have hfc : ContinuousOn f (Set.Icc z₂ z₃) := fun x hx =>
    ((hf x (hsub hx)).continuousAt).continuousWithinAt
  have hfi : IntervalIntegrable f volume z₂ z₃ :=
    intervalIntegrable_of_hasDerivAt hle (fun x hx => hF x (hsub hx)) hfc
  have hFTC : ∫ z in z₂..z₃, f z = F z₃ - F z₂ := by
    refine integral_eq_sub_of_hasDerivAt (fun x hx => hF x (hsub ?_)) hfi
    rwa [Set.uIcc_of_le hle] at hx
  have hpt : ∀ x ∈ Set.Icc z₂ z₃,
      M / 6 * Pcube z₁ z₂ z₃ x ≤ f x ∧ f x ≤ m / 6 * Pcube z₁ z₂ z₃ x := by
    intro x hx
    obtain ⟨ξ, hξ, hval⟩ :=
      exists_deriv3_eq_of_three_roots hf hf₁ hf₂ hz₁ hz₂ hz₃ h₁₂ h₂₃ e₁ e₂ e₃ (hsub hx)
    have hP : Pcube z₁ z₂ z₃ x ≤ 0 := Pcube_nonpos_right h₁₂ h₂₃ hx
    have hval' : f x = f₃ ξ / 6 * Pcube z₁ z₂ z₃ x := by rw [hval, Pcube]
    constructor
    · rw [hval']
      exact mul_le_mul_of_nonpos_right (by linarith [hM ξ hξ]) hP
    · rw [hval']
      exact mul_le_mul_of_nonpos_right (by linarith [hm ξ hξ]) hP
  have hlow : ∫ z in z₂..z₃, M / 6 * Pcube z₁ z₂ z₃ z ≤ ∫ z in z₂..z₃, f z :=
    integral_mono_on hle (intervalIntegrable_const_mul_Pcube _ _ _ _ _ _) hfi
      fun x hx => (hpt x hx).1
  have hhigh : ∫ z in z₂..z₃, f z ≤ ∫ z in z₂..z₃, m / 6 * Pcube z₁ z₂ z₃ z :=
    integral_mono_on hle hfi (intervalIntegrable_const_mul_Pcube _ _ _ _ _ _)
      fun x hx => (hpt x hx).2
  have hval : ∀ c : ℝ, ∫ z in z₂..z₃, c * Pcube z₁ z₂ z₃ z
      = c * (-((z₃ - z₂) ^ 3 * ((z₃ - z₂) + 2 * (z₂ - z₁)) / 12)) := by
    intro c
    rw [intervalIntegral.integral_const_mul, integral_Pcube_right]
  rw [hval, hFTC] at hlow
  rw [hval, hFTC] at hhigh
  exact ⟨hlow, hhigh⟩

end UpperTailOptimizers
