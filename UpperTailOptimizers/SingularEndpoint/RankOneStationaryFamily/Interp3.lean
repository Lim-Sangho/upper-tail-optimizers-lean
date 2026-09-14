import UpperTailOptimizers.SingularEndpoint.RankOneStationaryFamily.Defs

/-!
# The three-node Lagrange interpolation remainder

A self-contained piece of elementary real analysis, used nowhere else in
`sec:singular-endpoint` but needed by it: if a thrice differentiable function `f`
vanishes at three points `z₁ < z₂ < z₃`, then at every point `z` of the ambient interval

  `f z = f''' ξ / 6 * (z - z₁) (z - z₂) (z - z₃)`

for some `ξ` in the interval.  This is the classical Lagrange remainder for interpolation at
three nodes, specialised to the case where the interpolant is identically zero.

The point of proving it here is that it replaces an appeal to analyticity.  To analyse the two
differences in `eq:block-proportion-formula` (in the proofs of `lem:rank-one-kkt-family` and
`lem:rank-one-parameter-expansions`) the paper divides `𝓜_h'` by the monic cubic with roots
`s²`, `st`, `t²` (the analytic Weierstrass division behind
`eq:mh-derivative-factorization`) in order to see that they vanish to order four.  The lemma below gives the same factorisation from
Rolle's theorem alone, with no analyticity and no power series: the third derivative is
continuous and has a nonzero limit at the base point, so the cubic factor — which
integrates in closed form — sandwiches the combination between two multiples of `h⁴`.

The proof is the textbook one.  Off the nodes, subtract from `f` the multiple `K · P` of
the monic cubic `P` that matches `f` at `z`; the difference then has **four** distinct
zeros in the interval, and three rounds of Rolle produce a point where its third derivative
vanishes.  Since `P''' = 6` identically, that point is the required `ξ`.

## Contents

* `exists_deriv3_eq_of_three_roots` — the remainder formula above, stated for an explicit
  chain of `HasDerivAt` hypotheses `f → f₁ → f₂ → f₃` on `Set.Icc a b`;
* `exists_deriv_zero_of_two_roots`, `exists_deriv3_zero_of_four_roots` — the packaged Rolle
  steps the remainder is built from.  `SingularEndpoint/AuxiliaryLagrangian/Interp2.lean` and `SingularEndpoint/AuxiliaryLagrangian/Interp4.lean`
  use them too, which is why they are not `private`.

Nothing in this file mentions the singular endpoint family, the graph `H`, or any object of
Section 5; it is stated for a bare triple of derivatives on a compact interval.
-/

namespace UpperTailOptimizers

namespace SingularEndpoint

/-- Rolle's theorem, packaged for a function given together with an explicit derivative on
a closed interval `Set.Icc a b`: between two zeros of `g` inside the interval there is a
zero of `g₁`. -/
theorem exists_deriv_zero_of_two_roots {g g₁ : ℝ → ℝ} {a b : ℝ}
    (hg : ∀ x ∈ Set.Icc a b, HasDerivAt g (g₁ x) x)
    {w₁ w₂ : ℝ} (m₁ : w₁ ∈ Set.Icc a b) (m₂ : w₂ ∈ Set.Icc a b) (hlt : w₁ < w₂)
    (e₁ : g w₁ = 0) (e₂ : g w₂ = 0) :
    ∃ c, w₁ < c ∧ c < w₂ ∧ g₁ c = 0 := by
  have hsub : Set.Icc w₁ w₂ ⊆ Set.Icc a b := Set.Icc_subset_Icc m₁.1 m₂.2
  have hcont : ContinuousOn g (Set.Icc w₁ w₂) := fun x hx =>
    (hg x (hsub hx)).continuousAt.continuousWithinAt
  obtain ⟨c, hc, hc0⟩ := exists_hasDerivAt_eq_zero hlt hcont (by rw [e₁, e₂])
    (fun x hx => hg x (hsub (Set.Ioo_subset_Icc_self hx)))
  exact ⟨c, hc.1, hc.2, hc0⟩

/-- Three rounds of Rolle: if `g` has four zeros `w₁ < w₂ < w₃ < w₄` in `Set.Icc a b` and
`g → g₁ → g₂ → g₃` is a chain of derivatives there, then `g₃` vanishes somewhere in the
interval. -/
theorem exists_deriv3_zero_of_four_roots {g g₁ g₂ g₃ : ℝ → ℝ} {a b : ℝ}
    (hg : ∀ x ∈ Set.Icc a b, HasDerivAt g (g₁ x) x)
    (hg₁ : ∀ x ∈ Set.Icc a b, HasDerivAt g₁ (g₂ x) x)
    (hg₂ : ∀ x ∈ Set.Icc a b, HasDerivAt g₂ (g₃ x) x)
    {w₁ w₂ w₃ w₄ : ℝ}
    (m₁ : w₁ ∈ Set.Icc a b) (m₂ : w₂ ∈ Set.Icc a b) (m₃ : w₃ ∈ Set.Icc a b)
    (m₄ : w₄ ∈ Set.Icc a b)
    (o₁₂ : w₁ < w₂) (o₂₃ : w₂ < w₃) (o₃₄ : w₃ < w₄)
    (e₁ : g w₁ = 0) (e₂ : g w₂ = 0) (e₃ : g w₃ = 0) (e₄ : g w₄ = 0) :
    ∃ ξ ∈ Set.Icc a b, g₃ ξ = 0 := by
  obtain ⟨c₁, hc₁l, hc₁r, hc₁⟩ := exists_deriv_zero_of_two_roots hg m₁ m₂ o₁₂ e₁ e₂
  obtain ⟨c₂, hc₂l, hc₂r, hc₂⟩ := exists_deriv_zero_of_two_roots hg m₂ m₃ o₂₃ e₂ e₃
  obtain ⟨c₃, hc₃l, hc₃r, hc₃⟩ := exists_deriv_zero_of_two_roots hg m₃ m₄ o₃₄ e₃ e₄
  have mc₁ : c₁ ∈ Set.Icc a b := ⟨m₁.1.trans hc₁l.le, hc₁r.le.trans m₂.2⟩
  have mc₂ : c₂ ∈ Set.Icc a b := ⟨m₂.1.trans hc₂l.le, hc₂r.le.trans m₃.2⟩
  have mc₃ : c₃ ∈ Set.Icc a b := ⟨m₃.1.trans hc₃l.le, hc₃r.le.trans m₄.2⟩
  obtain ⟨d₁, hd₁l, hd₁r, hd₁⟩ :=
    exists_deriv_zero_of_two_roots hg₁ mc₁ mc₂ (hc₁r.trans hc₂l) hc₁ hc₂
  obtain ⟨d₂, hd₂l, hd₂r, hd₂⟩ :=
    exists_deriv_zero_of_two_roots hg₁ mc₂ mc₃ (hc₂r.trans hc₃l) hc₂ hc₃
  have md₁ : d₁ ∈ Set.Icc a b := ⟨mc₁.1.trans hd₁l.le, hd₁r.le.trans mc₂.2⟩
  have md₂ : d₂ ∈ Set.Icc a b := ⟨mc₂.1.trans hd₂l.le, hd₂r.le.trans mc₃.2⟩
  obtain ⟨ξ, hξl, hξr, hξ⟩ :=
    exists_deriv_zero_of_two_roots hg₂ md₁ md₂ (hd₁r.trans hd₂l) hd₁ hd₂
  exact ⟨ξ, ⟨md₁.1.trans hξl.le, hξr.le.trans md₂.2⟩, hξ⟩

/-- **The three-node Lagrange interpolation remainder.**

If `f → f₁ → f₂ → f₃` is a chain of derivatives on `Set.Icc a b` and `f` vanishes at three
points `z₁ < z₂ < z₃` of that interval, then for every `z ∈ Set.Icc a b` there is a
`ξ ∈ Set.Icc a b` with

  `f z = f₃ ξ / 6 * ((z - z₁) * (z - z₂) * (z - z₃))`.

No analyticity is used: the proof is Rolle's theorem applied three times to
`f - K · (· - z₁)(· - z₂)(· - z₃)`, where `K` is chosen so that the difference also
vanishes at `z`. -/
theorem exists_deriv3_eq_of_three_roots {f f₁ f₂ f₃ : ℝ → ℝ} {a b : ℝ}
    (hf : ∀ x ∈ Set.Icc a b, HasDerivAt f (f₁ x) x)
    (hf₁ : ∀ x ∈ Set.Icc a b, HasDerivAt f₁ (f₂ x) x)
    (hf₂ : ∀ x ∈ Set.Icc a b, HasDerivAt f₂ (f₃ x) x)
    {z₁ z₂ z₃ : ℝ}
    (hz₁ : z₁ ∈ Set.Icc a b) (hz₂ : z₂ ∈ Set.Icc a b) (hz₃ : z₃ ∈ Set.Icc a b)
    (h₁₂ : z₁ < z₂) (h₂₃ : z₂ < z₃)
    (e₁ : f z₁ = 0) (e₂ : f z₂ = 0) (e₃ : f z₃ = 0)
    {z : ℝ} (hz : z ∈ Set.Icc a b) :
    ∃ ξ ∈ Set.Icc a b, f z = f₃ ξ / 6 * ((z - z₁) * (z - z₂) * (z - z₃)) := by
  -- If `z` is one of the nodes both sides vanish.
  by_cases hd₁ : z = z₁
  · exact ⟨z₁, hz₁, by rw [hd₁, e₁]; ring⟩
  by_cases hd₂ : z = z₂
  · exact ⟨z₁, hz₁, by rw [hd₂, e₂]; ring⟩
  by_cases hd₃ : z = z₃
  · exact ⟨z₁, hz₁, by rw [hd₃, e₃]; ring⟩
  -- Otherwise the monic cubic is nonzero at `z`, so `f z` is a multiple of it.
  have hPne : (z - z₁) * (z - z₂) * (z - z₃) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hd₁) (sub_ne_zero.mpr hd₂))
      (sub_ne_zero.mpr hd₃)
  obtain ⟨K, hK⟩ : ∃ K : ℝ, f z = K * ((z - z₁) * (z - z₂) * (z - z₃)) :=
    ⟨f z / ((z - z₁) * (z - z₂) * (z - z₃)), (div_mul_cancel₀ _ hPne).symm⟩
  -- Derivatives of the monic cubic `P w = (w - z₁)(w - z₂)(w - z₃)`.
  have hlin : ∀ c x : ℝ, HasDerivAt (fun w : ℝ => w - c) 1 x := fun c x =>
    (hasDerivAt_id x).sub_const c
  have hP : ∀ x : ℝ, HasDerivAt (fun w : ℝ => (w - z₁) * (w - z₂) * (w - z₃))
      ((x - z₂) * (x - z₃) + (x - z₁) * (x - z₃) + (x - z₁) * (x - z₂)) x := by
    intro x
    have h := ((hlin z₁ x).mul (hlin z₂ x)).mul (hlin z₃ x)
    exact h.congr_deriv (by simp only [Pi.mul_apply]; ring)
  have hP₁ : ∀ x : ℝ, HasDerivAt
      (fun w : ℝ => (w - z₂) * (w - z₃) + (w - z₁) * (w - z₃) + (w - z₁) * (w - z₂))
      (2 * ((x - z₁) + (x - z₂) + (x - z₃))) x := by
    intro x
    have h := (((hlin z₂ x).mul (hlin z₃ x)).add ((hlin z₁ x).mul (hlin z₃ x))).add
      ((hlin z₁ x).mul (hlin z₂ x))
    exact h.congr_deriv (by ring)
  have hP₂ : ∀ x : ℝ,
      HasDerivAt (fun w : ℝ => 2 * ((w - z₁) + (w - z₂) + (w - z₃))) 6 x := by
    intro x
    have h := (((hlin z₁ x).add (hlin z₂ x)).add (hlin z₃ x)).const_mul (2 : ℝ)
    exact h.congr_deriv (by norm_num)
  -- The chain of derivatives of `g = f - K · P`.
  have hg : ∀ x ∈ Set.Icc a b,
      HasDerivAt (fun w : ℝ => f w - K * ((w - z₁) * (w - z₂) * (w - z₃)))
        (f₁ x - K * ((x - z₂) * (x - z₃) + (x - z₁) * (x - z₃) + (x - z₁) * (x - z₂))) x :=
    fun x hx => (hf x hx).sub ((hP x).const_mul K)
  have hg₁ : ∀ x ∈ Set.Icc a b,
      HasDerivAt (fun w : ℝ =>
          f₁ w - K * ((w - z₂) * (w - z₃) + (w - z₁) * (w - z₃) + (w - z₁) * (w - z₂)))
        (f₂ x - K * (2 * ((x - z₁) + (x - z₂) + (x - z₃)))) x :=
    fun x hx => (hf₁ x hx).sub ((hP₁ x).const_mul K)
  have hg₂ : ∀ x ∈ Set.Icc a b,
      HasDerivAt (fun w : ℝ => f₂ w - K * (2 * ((w - z₁) + (w - z₂) + (w - z₃))))
        (f₃ x - K * 6) x :=
    fun x hx => (hf₂ x hx).sub ((hP₂ x).const_mul K)
  -- The four zeros of `g`.
  have g₁0 : f z₁ - K * ((z₁ - z₁) * (z₁ - z₂) * (z₁ - z₃)) = 0 := by rw [e₁]; ring
  have g₂0 : f z₂ - K * ((z₂ - z₁) * (z₂ - z₂) * (z₂ - z₃)) = 0 := by rw [e₂]; ring
  have g₃0 : f z₃ - K * ((z₃ - z₁) * (z₃ - z₂) * (z₃ - z₃)) = 0 := by rw [e₃]; ring
  have gz0 : f z - K * ((z - z₁) * (z - z₂) * (z - z₃)) = 0 := by rw [hK]; ring
  -- Rolle, in whichever order the four points happen to sit.
  have key : ∀ w₁ w₂ w₃ w₄ : ℝ, w₁ ∈ Set.Icc a b → w₂ ∈ Set.Icc a b → w₃ ∈ Set.Icc a b →
      w₄ ∈ Set.Icc a b → w₁ < w₂ → w₂ < w₃ → w₃ < w₄ →
      f w₁ - K * ((w₁ - z₁) * (w₁ - z₂) * (w₁ - z₃)) = 0 →
      f w₂ - K * ((w₂ - z₁) * (w₂ - z₂) * (w₂ - z₃)) = 0 →
      f w₃ - K * ((w₃ - z₁) * (w₃ - z₂) * (w₃ - z₃)) = 0 →
      f w₄ - K * ((w₄ - z₁) * (w₄ - z₂) * (w₄ - z₃)) = 0 →
      ∃ ξ ∈ Set.Icc a b, f z = f₃ ξ / 6 * ((z - z₁) * (z - z₂) * (z - z₃)) := by
    intro w₁ w₂ w₃ w₄ m₁ m₂ m₃ m₄ o₁₂ o₂₃ o₃₄ r₁ r₂ r₃ r₄
    obtain ⟨ξ, hξ, hξ0⟩ :=
      exists_deriv3_zero_of_four_roots hg hg₁ hg₂ m₁ m₂ m₃ m₄ o₁₂ o₂₃ o₃₄ r₁ r₂ r₃ r₄
    refine ⟨ξ, hξ, ?_⟩
    have : f₃ ξ = 6 * K := by linarith
    rw [hK, this]; ring
  rcases lt_trichotomy z z₁ with hA | hA | hA
  · exact key z z₁ z₂ z₃ hz hz₁ hz₂ hz₃ hA h₁₂ h₂₃ gz0 g₁0 g₂0 g₃0
  · exact absurd hA hd₁
  rcases lt_trichotomy z z₂ with hB | hB | hB
  · exact key z₁ z z₂ z₃ hz₁ hz hz₂ hz₃ hA hB h₂₃ g₁0 gz0 g₂0 g₃0
  · exact absurd hB hd₂
  rcases lt_trichotomy z z₃ with hC | hC | hC
  · exact key z₁ z₂ z z₃ hz₁ hz₂ hz hz₃ h₁₂ hB hC g₁0 g₂0 gz0 g₃0
  · exact absurd hC hd₃
  · exact key z₁ z₂ z₃ z hz₁ hz₂ hz₃ hz h₁₂ h₂₃ hC g₁0 g₂0 g₃0 gz0

end SingularEndpoint

end UpperTailOptimizers
