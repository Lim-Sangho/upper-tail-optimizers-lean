import UpperTailOptimizers.SingularEndpoint.Interp3

/-!
# The two-node Hermite interpolation remainder (Section 7, `paper/singular_endpoint.tex`)

The confluent companion of `SingularEndpoint/Interp3.lean`.  There the three interpolation nodes are
simple; here there are **two** nodes, each a *double* node, so that a four-times
differentiable `f` with

  `f s = f₁ s = f t = f₁ t = 0`

satisfies, at every point `z` of the ambient interval,

  `f z = f⁗(ξ)/24 · (z - s)² (z - t)²`

for some `ξ` in the interval.  This is the classical Hermite remainder for interpolation at
two double nodes, specialised to the case where the interpolant is identically zero.

## Why Section 7 wants it

`lem:first-variation-bound` needs the one-point dual
potential `eq:first-variation` in the factored form `Ψ_h(x) = Q_h(x)² R_h(x)`, with
`Q_h(x) = (x - s_h)(x - t_h)` the node quadratic and a lower bound on `R_h` that is
**uniform** as `h ↓ 0`.  The paper obtains the factorisation from an analytic Weierstrass
division carried out jointly in `(h, x)`.  As in `SingularEndpoint/Order4.lean` we replace that by
the elementary remainder below together with a uniform bound on the fourth derivative over a
shrinking window; this suffices because only a *lower* bound on `Ψ_h / Q_h²` is wanted, and
an unlocated `ξ` is harmless for a lower bound.

The four hypotheses `f s = f₁ s = f t = f₁ t = 0` are exactly the four contact conditions
already proved in `SingularEndpoint/FirstVariation.lean` — `KKTFamily.Psi_sVal`, `.Psi_tVal`,
`.Psi_deriv_sVal`, `.Psi_deriv_tVal`.

## The proof

The textbook one, and structurally that of `exists_deriv3_eq_of_three_roots`.  Off the nodes,
subtract from `f` the multiple `K · P` of the monic quartic `P w = (w - s)²(w - t)²` that
matches `f` at `z`.  The difference `φ` then vanishes at the three points `s`, `t`, `z`, and
— because `P` and `P'` both vanish at each node — its derivative `φ'` vanishes at `s` and at
`t`.  One round of Rolle on the three zeros of `φ` adds two more zeros of `φ'`, strictly
between consecutive members of `{s, t, z}`, hence distinct from `s` and `t` and from each
other: **four** zeros of `φ'`.  Three further rounds of Rolle produce a point where `φ⁗`
vanishes, and `P⁗ ≡ 24` identifies it as the required `ξ`.

## Contents

* `exists_deriv4_eq_of_two_double_roots` — the remainder formula above, stated for an
  explicit chain of `HasDerivAt` hypotheses `f → f₁ → f₂ → f₃ → f₄` on `Set.Icc a b`.

Nothing in this file mentions the singular endpoint family, the graph `H`, or any object of
Section 7; it is stated for a bare quadruple of derivatives on a compact interval.
-/

namespace UpperTailOptimizers

namespace SingularEndpoint

/-- **Zero counting for two double nodes and one extra simple zero.**

If `g → g₁ → g₂ → g₃ → g₄` is a chain of derivatives on `Set.Icc a b`, if `g` and `g₁` both
vanish at two points `s < t` of that interval, and if `g` has a further zero `z` there
distinct from both, then `g₄` vanishes somewhere in the interval.

The count: one round of Rolle on the three zeros `{s, t, z}` of `g` produces two zeros of
`g₁` lying strictly between consecutive members of that set, so together with `s` and `t`
there are four *distinct* ordered zeros of `g₁`; three more rounds finish.  The three
positions of `z` relative to `s < t` give the three cases below, which differ only in how the
four zeros are interleaved. -/
private theorem exists_deriv4_zero_of_two_double_roots {g g₁ g₂ g₃ g₄ : ℝ → ℝ} {a b : ℝ}
    (hg : ∀ x ∈ Set.Icc a b, HasDerivAt g (g₁ x) x)
    (hg₁ : ∀ x ∈ Set.Icc a b, HasDerivAt g₁ (g₂ x) x)
    (hg₂ : ∀ x ∈ Set.Icc a b, HasDerivAt g₂ (g₃ x) x)
    (hg₃ : ∀ x ∈ Set.Icc a b, HasDerivAt g₃ (g₄ x) x)
    {s t z : ℝ} (hs : s ∈ Set.Icc a b) (ht : t ∈ Set.Icc a b) (hzm : z ∈ Set.Icc a b)
    (hst : s < t) (hzs : z ≠ s) (hzt : z ≠ t)
    (e₀s : g s = 0) (e₁s : g₁ s = 0) (e₀t : g t = 0) (e₁t : g₁ t = 0) (e₀z : g z = 0) :
    ∃ ξ ∈ Set.Icc a b, g₄ ξ = 0 := by
  rcases lt_trichotomy z s with hA | hA | hA
  · -- `z < s < t`: the zeros of `g₁` are `c₁ < s < c₂ < t`.
    obtain ⟨c₁, hc₁l, hc₁r, hc₁⟩ := exists_deriv_zero_of_two_roots hg hzm hs hA e₀z e₀s
    obtain ⟨c₂, hc₂l, hc₂r, hc₂⟩ := exists_deriv_zero_of_two_roots hg hs ht hst e₀s e₀t
    have mc₁ : c₁ ∈ Set.Icc a b := ⟨hzm.1.trans hc₁l.le, hc₁r.le.trans hs.2⟩
    have mc₂ : c₂ ∈ Set.Icc a b := ⟨hs.1.trans hc₂l.le, hc₂r.le.trans ht.2⟩
    exact exists_deriv3_zero_of_four_roots hg₁ hg₂ hg₃ mc₁ hs mc₂ ht hc₁r hc₂l hc₂r
      hc₁ e₁s hc₂ e₁t
  · exact absurd hA hzs
  rcases lt_trichotomy z t with hB | hB | hB
  · -- `s < z < t`: the zeros of `g₁` are `s < c₁ < c₂ < t`.
    obtain ⟨c₁, hc₁l, hc₁r, hc₁⟩ := exists_deriv_zero_of_two_roots hg hs hzm hA e₀s e₀z
    obtain ⟨c₂, hc₂l, hc₂r, hc₂⟩ := exists_deriv_zero_of_two_roots hg hzm ht hB e₀z e₀t
    have mc₁ : c₁ ∈ Set.Icc a b := ⟨hs.1.trans hc₁l.le, hc₁r.le.trans hzm.2⟩
    have mc₂ : c₂ ∈ Set.Icc a b := ⟨hzm.1.trans hc₂l.le, hc₂r.le.trans ht.2⟩
    exact exists_deriv3_zero_of_four_roots hg₁ hg₂ hg₃ hs mc₁ mc₂ ht hc₁l
      (hc₁r.trans hc₂l) hc₂r e₁s hc₁ hc₂ e₁t
  · exact absurd hB hzt
  · -- `s < t < z`: the zeros of `g₁` are `s < c₁ < t < c₂`.
    obtain ⟨c₁, hc₁l, hc₁r, hc₁⟩ := exists_deriv_zero_of_two_roots hg hs ht hst e₀s e₀t
    obtain ⟨c₂, hc₂l, hc₂r, hc₂⟩ := exists_deriv_zero_of_two_roots hg ht hzm hB e₀t e₀z
    have mc₁ : c₁ ∈ Set.Icc a b := ⟨hs.1.trans hc₁l.le, hc₁r.le.trans ht.2⟩
    have mc₂ : c₂ ∈ Set.Icc a b := ⟨ht.1.trans hc₂l.le, hc₂r.le.trans hzm.2⟩
    exact exists_deriv3_zero_of_four_roots hg₁ hg₂ hg₃ hs mc₁ ht mc₂ hc₁l hc₁r hc₂l
      e₁s hc₁ e₁t hc₂

/-- **The two-node Hermite interpolation remainder.**

If `f → f₁ → f₂ → f₃ → f₄` is a chain of derivatives on `Set.Icc a b` and both `f` and `f₁`
vanish at two points `s < t` of that interval, then for every `z ∈ Set.Icc a b` there is a
`ξ ∈ Set.Icc a b` with

  `f z = f₄ ξ / 24 * ((z - s) ^ 2 * (z - t) ^ 2)`.

No analyticity is used: the proof is Rolle's theorem applied four times to
`f - K · (· - s)²(· - t)²`, where `K` is chosen so that the difference also vanishes at `z`.
This is the confluent form of `exists_deriv3_eq_of_three_roots`, with the three simple nodes
replaced by two double nodes, and it is what replaces the paper's Weierstrass division in
`lem:first-variation-bound`. -/
theorem exists_deriv4_eq_of_two_double_roots {f f₁ f₂ f₃ f₄ : ℝ → ℝ} {a b : ℝ}
    (hf : ∀ x ∈ Set.Icc a b, HasDerivAt f (f₁ x) x)
    (hf₁ : ∀ x ∈ Set.Icc a b, HasDerivAt f₁ (f₂ x) x)
    (hf₂ : ∀ x ∈ Set.Icc a b, HasDerivAt f₂ (f₃ x) x)
    (hf₃ : ∀ x ∈ Set.Icc a b, HasDerivAt f₃ (f₄ x) x)
    {s t : ℝ} (hs : s ∈ Set.Icc a b) (ht : t ∈ Set.Icc a b) (hst : s < t)
    (e₀s : f s = 0) (e₁s : f₁ s = 0) (e₀t : f t = 0) (e₁t : f₁ t = 0)
    {z : ℝ} (hz : z ∈ Set.Icc a b) :
    ∃ ξ ∈ Set.Icc a b, f z = f₄ ξ / 24 * ((z - s) ^ 2 * (z - t) ^ 2) := by
  -- If `z` is one of the two nodes both sides vanish.
  by_cases hzs : z = s
  · exact ⟨s, hs, by rw [hzs, e₀s]; ring⟩
  by_cases hzt : z = t
  · exact ⟨s, hs, by rw [hzt, e₀t]; ring⟩
  -- Otherwise the monic quartic is nonzero at `z`, so `f z` is a multiple of it.
  have hPne : (z - s) ^ 2 * (z - t) ^ 2 ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 (sub_ne_zero.mpr hzs)) (pow_ne_zero 2 (sub_ne_zero.mpr hzt))
  obtain ⟨K, hK⟩ : ∃ K : ℝ, f z = K * ((z - s) ^ 2 * (z - t) ^ 2) :=
    ⟨f z / ((z - s) ^ 2 * (z - t) ^ 2), (div_mul_cancel₀ _ hPne).symm⟩
  -- Derivatives of the monic quartic `P w = (w - s)²(w - t)²`, down to `P⁗ ≡ 24`.
  have hlin : ∀ c x : ℝ, HasDerivAt (fun w : ℝ => w - c) 1 x := fun c x =>
    (hasDerivAt_id x).sub_const c
  have hP : ∀ x : ℝ, HasDerivAt (fun w : ℝ => (w - s) ^ 2 * (w - t) ^ 2)
      (2 * (x - s) * (x - t) ^ 2 + 2 * (x - s) ^ 2 * (x - t)) x := by
    intro x
    have h := ((hlin s x).pow 2).mul ((hlin t x).pow 2)
    exact h.congr_deriv (by simp only [Pi.pow_apply]; push_cast; ring)
  have hP₁ : ∀ x : ℝ,
      HasDerivAt (fun w : ℝ => 2 * (w - s) * (w - t) ^ 2 + 2 * (w - s) ^ 2 * (w - t))
        (2 * (x - t) ^ 2 + 8 * (x - s) * (x - t) + 2 * (x - s) ^ 2) x := by
    intro x
    have h := (((hlin s x).const_mul (2 : ℝ)).mul ((hlin t x).pow 2)).add
      ((((hlin s x).pow 2).const_mul (2 : ℝ)).mul (hlin t x))
    exact h.congr_deriv (by simp only [Pi.pow_apply]; push_cast; ring)
  have hP₂ : ∀ x : ℝ,
      HasDerivAt (fun w : ℝ => 2 * (w - t) ^ 2 + 8 * (w - s) * (w - t) + 2 * (w - s) ^ 2)
        (12 * (x - s) + 12 * (x - t)) x := by
    intro x
    have h := ((((hlin t x).pow 2).const_mul (2 : ℝ)).add
      (((hlin s x).const_mul (8 : ℝ)).mul (hlin t x))).add
      (((hlin s x).pow 2).const_mul (2 : ℝ))
    exact h.congr_deriv (by push_cast; ring)
  have hP₃ : ∀ x : ℝ,
      HasDerivAt (fun w : ℝ => 12 * (w - s) + 12 * (w - t)) 24 x := by
    intro x
    have h := ((hlin s x).const_mul (12 : ℝ)).add ((hlin t x).const_mul (12 : ℝ))
    exact h.congr_deriv (by norm_num)
  -- The chain of derivatives of `φ = f - K · P`.
  have hg : ∀ x ∈ Set.Icc a b,
      HasDerivAt (fun w : ℝ => f w - K * ((w - s) ^ 2 * (w - t) ^ 2))
        (f₁ x - K * (2 * (x - s) * (x - t) ^ 2 + 2 * (x - s) ^ 2 * (x - t))) x :=
    fun x hx => (hf x hx).sub ((hP x).const_mul K)
  have hg₁ : ∀ x ∈ Set.Icc a b,
      HasDerivAt
        (fun w : ℝ => f₁ w - K * (2 * (w - s) * (w - t) ^ 2 + 2 * (w - s) ^ 2 * (w - t)))
        (f₂ x - K * (2 * (x - t) ^ 2 + 8 * (x - s) * (x - t) + 2 * (x - s) ^ 2)) x :=
    fun x hx => (hf₁ x hx).sub ((hP₁ x).const_mul K)
  have hg₂ : ∀ x ∈ Set.Icc a b,
      HasDerivAt
        (fun w : ℝ => f₂ w - K * (2 * (w - t) ^ 2 + 8 * (w - s) * (w - t) + 2 * (w - s) ^ 2))
        (f₃ x - K * (12 * (x - s) + 12 * (x - t))) x :=
    fun x hx => (hf₂ x hx).sub ((hP₂ x).const_mul K)
  have hg₃ : ∀ x ∈ Set.Icc a b,
      HasDerivAt (fun w : ℝ => f₃ w - K * (12 * (w - s) + 12 * (w - t)))
        (f₄ x - K * 24) x :=
    fun x hx => (hf₃ x hx).sub ((hP₃ x).const_mul K)
  -- `φ` vanishes at `s`, `t`, `z`; `φ'` vanishes at the two double nodes `s`, `t`.
  have gs0 : f s - K * ((s - s) ^ 2 * (s - t) ^ 2) = 0 := by rw [e₀s]; ring
  have gt0 : f t - K * ((t - s) ^ 2 * (t - t) ^ 2) = 0 := by rw [e₀t]; ring
  have gz0 : f z - K * ((z - s) ^ 2 * (z - t) ^ 2) = 0 := by rw [hK]; ring
  have g₁s0 : f₁ s - K * (2 * (s - s) * (s - t) ^ 2 + 2 * (s - s) ^ 2 * (s - t)) = 0 := by
    rw [e₁s]; ring
  have g₁t0 : f₁ t - K * (2 * (t - s) * (t - t) ^ 2 + 2 * (t - s) ^ 2 * (t - t)) = 0 := by
    rw [e₁t]; ring
  -- Four rounds of Rolle, then `P⁗ ≡ 24` identifies the constant.
  obtain ⟨ξ, hξ, hξ0⟩ :=
    exists_deriv4_zero_of_two_double_roots hg hg₁ hg₂ hg₃ hs ht hz hst hzs hzt
      gs0 g₁s0 gt0 g₁t0 gz0
  refine ⟨ξ, hξ, ?_⟩
  have hval : f₄ ξ = 24 * K := by linarith
  rw [hK, hval]; ring

end SingularEndpoint

end UpperTailOptimizers
