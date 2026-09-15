import UpperTailOptimizers.SingularEndpoint.LocalizationRankOne.Gap

/-!
# Strong convexity of `J_p`, as a convexity gap

`J_p''(u) = 1/(u(1-u)) ≥ 4` on `(0,1)`, uniformly in `p`, so `J_p` is `4`-strongly convex and
its convexity gap at an interior base point dominates `2(u-v)²`.

This is a generic fact about the binomial relative entropy, with no Section 5 content of its
own.  In the manuscript it is the strong-convexity input of Step 2 of `lem:graphon-lagrangian-bound`,
bound), which reads: "Since `J_{p_h}''(z) = 1/(z(1-z)) ≥ 4`, strong
convexity gives `∬_{Ω_ρ(f)²}{J_{p_h}(W) - J_{p_h}(f⊗f) - (J_{p_h})'(f⊗f)E} ≥ 2‖E‖²_{2,Ω_ρ(f)²}`."
Its one consumer is the central-square bound in `SingularEndpoint/GraphonComparison/GraphonComparisonMain.lean`.

## Contents

* `four_le_Jp''` — `J_p''(u) ≥ 4` on `(0,1)`, the strong-convexity modulus;
* `two_sq_le_Jp_convexGap` — `J_p(u) - J_p(v) - J_p'(v)(u-v) ≥ 2(u-v)²` for `u ∈ [0,1]`,
  `v ∈ (0,1)`.
-/

namespace UpperTailOptimizers

/-- **`J_p'' ≥ 4` on `(0,1)`**, uniformly in `p`: `J_p''(u) = 1/(u(1-u))` and
`u(1-u) ≤ 1/4`. -/
theorem four_le_Jp'' {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) : 4 ≤ Jp'' u := by
  have hpos : 0 < u * (1 - u) := mul_pos hu0 (by linarith)
  rw [Jp'', le_div_iff₀ hpos]
  nlinarith [sq_nonneg (2 * u - 1)]

/-- The derivative of `u ↦ 2u²`, spelled out so that no numeral bookkeeping is needed
downstream. -/
private theorem hasDerivAt_two_sq (x : ℝ) : HasDerivAt (fun u : ℝ => 2 * u ^ 2) (4 * x) x := by
  have hsq : HasDerivAt (fun u : ℝ => u ^ 2) (2 * x) x := by
    simpa using hasDerivAt_pow 2 x
  have h := hsq.const_mul (2 : ℝ)
  have hv : (2 : ℝ) * (2 * x) = 4 * x := by ring
  rw [hv] at h
  exact h

/-- The derivative of `u ↦ 4u`. -/
private theorem hasDerivAt_four_mul (x : ℝ) : HasDerivAt (fun u : ℝ => 4 * u) 4 x := by
  simpa using (hasDerivAt_id x).const_mul (4 : ℝ)

/-- `u ↦ J_p(u) - 2u²` is convex on `[0,1]`: its second derivative is `J_p'' - 4 ≥ 0` by
`four_le_Jp''`.  This is the statement that `J_p` is `4`-strongly convex. -/
private theorem convexOn_Jp_sub_two_sq {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    ConvexOn ℝ (Set.Icc (0 : ℝ) 1) (fun u : ℝ => Jp p u - 2 * u ^ 2) := by
  refine convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc 0 1)
    (f' := fun u : ℝ => Jp' p u - 4 * u) (f'' := fun u : ℝ => Jp'' u - 4)
    ((continuousOn_Jp_Icc hp0 hp1).sub (by fun_prop)) ?_ ?_ ?_
  · intro x hx
    rw [interior_Icc] at hx
    exact ((hasDerivAt_Jp hp0 hp1 hx.1 hx.2).sub (hasDerivAt_two_sq x)).hasDerivWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    exact ((hasDerivAt_Jp' hp0 hp1 hx.1 hx.2).sub (hasDerivAt_four_mul x)).hasDerivWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    linarith [four_le_Jp'' hx.1 hx.2]

/-- **The strong-convexity lemma.**  The convexity gap of `J_p` at an interior base point
dominates `2(u-v)²`:

`J_p(u) ≥ J_p(v) + J_p'(v)(u-v) + 2(u-v)²`   (`u ∈ [0,1]`, `v ∈ (0,1)`),

the modulus `4 = 2·2` coming from `four_le_Jp''`. -/
theorem two_sq_le_Jp_convexGap {p u v : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hu : u ∈ Set.Icc (0 : ℝ) 1) (hv0 : 0 < v) (hv1 : v < 1) :
    2 * (u - v) ^ 2 ≤ Jp p u - Jp p v - Jp' p v * (u - v) := by
  have hderiv : HasDerivAt (fun y : ℝ => Jp p y - 2 * y ^ 2) (Jp' p v - 4 * v) v :=
    (hasDerivAt_Jp hp0 hp1 hv0 hv1).sub (hasDerivAt_two_sq v)
  have h := convexOn_tangent_le (convexOn_Jp_sub_two_sq hp0 hp1)
    (⟨hv0.le, hv1.le⟩ : v ∈ Set.Icc (0 : ℝ) 1) hderiv u hu
  have h' : Jp p v - 2 * v ^ 2 + (Jp' p v - 4 * v) * (u - v) ≤ Jp p u - 2 * u ^ 2 := h
  nlinarith [h']

end UpperTailOptimizers
