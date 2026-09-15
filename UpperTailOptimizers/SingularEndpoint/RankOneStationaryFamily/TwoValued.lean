import UpperTailOptimizers.SingularEndpoint.RankOneStationaryFamily.Bipodality
import UpperTailOptimizers.Preliminaries.Graphons.Basic

/-!
# Two-valuedness of rank-one KKT factors: the measure-theoretic step (Section 5)

This file carries the scalar core of `lem:stationary-rank-one-bipodality` of `paper/sections/singular.tex`
across the measure-theoretic divide.  `three_values_absurd` says that the four
numbers `a², ab, ac, bc` coming from `0 < a < b < c < 1` cannot all be zeros of the
rank-one KKT function `F_{p,γ}`.  What the paper actually uses is the statement about a
*factor* `f : [0,1] → ℝ`: if `F_{p,γ}(f(x)f(y)) = 0` for a.e. `(x,y)`, then `f` cannot take
three distinct values `a < b < c` each on a set of positive measure.

The bridge is a single product-measure observation.  If `A` and `B` both have positive
`unitμ`-measure, then `gμ (A ×ˢ B) = unitμ A * unitμ B > 0` because `gμ = unitμ.prod unitμ`,
so the rectangle `A ×ˢ B` cannot be contained in a `gμ`-null set; consequently any property
holding `gμ`-a.e. holds at *some* point of `A ×ˢ B`. Applying this to the four rectangles
`A ×ˢ A`, `A ×ˢ B`, `A ×ˢ C`, `B ×ˢ C` built from the level sets of `f` produces
the four zeros forbidden by `three_values_absurd`. The paper also lists `c²`; the
three-zero bound already gives a contradiction without that fifth product.

## Contents

* `exists_mem_prod_of_ae` — a `gμ`-a.e. property is realised at some point of a rectangle
  whose two sides have positive `unitμ`-measure (private, but the crux of the file);
* `not_three_values` — the measure-theoretic form of `lem:stationary-rank-one-bipodality`: a
  rank-one KKT factor takes no three distinct values on sets of positive measure;
* `two_of_three_measure_zero` — the same statement in contrapositive form.
-/

namespace UpperTailOptimizers

open MeasureTheory

variable {d : ℕ}

/-! ## The product-measure bridge -/

/-- **A `gμ`-a.e. property is realised on every positive-measure rectangle.**

If `unitμ A > 0` and `unitμ B > 0`, then `gμ (A ×ˢ B) = unitμ A * unitμ B > 0`, so the
rectangle `A ×ˢ B` is not contained in the null set where `P` fails.  This is the
measurable-selection step in the proof of `lem:stationary-rank-one-bipodality` of
`paper/sections/singular.tex`. -/
private theorem exists_mem_prod_of_ae {A B : Set ℝ} (_hA : MeasurableSet A)
    (_hB : MeasurableSet B) (hApos : 0 < unitμ A) (hBpos : 0 < unitμ B)
    {P : ℝ × ℝ → Prop} (hP : ∀ᵐ z ∂gμ, P z) :
    ∃ x ∈ A, ∃ y ∈ B, P (x, y) := by
  by_contra hcon
  push Not at hcon
  have hsub : A ×ˢ B ⊆ {z : ℝ × ℝ | ¬ P z} := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    exact hcon x hx y hy
  have hnull : gμ {z : ℝ × ℝ | ¬ P z} = 0 := ae_iff.mp hP
  have h0 : gμ (A ×ˢ B) = 0 := measure_mono_null hsub hnull
  rw [gμ, Measure.prod_prod] at h0
  exact (ENNReal.mul_pos hApos.ne' hBpos.ne').ne' h0

/-! ## No rank-one KKT factor takes three values -/

/-- **`lem:stationary-rank-one-bipodality`, measure-theoretic form.**

Let `f` be measurable and suppose the rank-one KKT equation
`F_{p,γ}(f(x) f(y)) = 0` holds for `gμ`-almost every `(x, y)`.  Then `f` cannot take three
distinct values `0 < a < b < c < 1` on sets of positive measure: the four products
`a·a`, `a·b`, `a·c`, `b·c` would all be zeros of `F_{p,γ}`, contradicting the
three-zero bound `three_values_absurd`. -/
theorem not_three_values (hd : 2 ≤ d) {p g : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    {f : ℝ → ℝ} (hfm : Measurable f)
    (hkkt : ∀ᵐ z ∂gμ, Fkkt d p g (f z.1 * f z.2) = 0)
    {a b c : ℝ} (ha0 : 0 < a) (hab : a < b) (hbc : b < c) (hc1 : c < 1)
    (hA : 0 < unitμ {x | f x = a}) (hB : 0 < unitμ {x | f x = b})
    (hC : 0 < unitμ {x | f x = c}) : False := by
  have mA : MeasurableSet {x | f x = a} := hfm (measurableSet_singleton a)
  have mB : MeasurableSet {x | f x = b} := hfm (measurableSet_singleton b)
  have mC : MeasurableSet {x | f x = c} := hfm (measurableSet_singleton c)
  obtain ⟨_, hx1, _, hy1, h1⟩ := exists_mem_prod_of_ae mA mA hA hA hkkt
  obtain ⟨_, hx2, _, hy2, h2⟩ := exists_mem_prod_of_ae mA mB hA hB hkkt
  obtain ⟨_, hx3, _, hy3, h3⟩ := exists_mem_prod_of_ae mA mC hA hC hkkt
  obtain ⟨_, hx4, _, hy4, h4⟩ := exists_mem_prod_of_ae mB mC hB hC hkkt
  simp only [Set.mem_ofPred_eq] at hx1 hy1 hx2 hy2 hx3 hy3 hx4 hy4
  rw [hx1, hy1] at h1
  rw [hx2, hy2] at h2
  rw [hx3, hy3] at h3
  rw [hx4, hy4] at h4
  exact three_values_absurd hd hp0 hp1 ha0 hab hbc hc1 h1 h2 h3 h4

/-- **`lem:stationary-rank-one-bipodality`, contrapositive form.**

Under the rank-one KKT equation, at least one of any three candidate values
`0 < a < b < c < 1` is attained only on a null set; that is, `f` is two-valued up to null
sets. -/
theorem two_of_three_measure_zero (hd : 2 ≤ d) {p g : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    {f : ℝ → ℝ} (hfm : Measurable f)
    (hkkt : ∀ᵐ z ∂gμ, Fkkt d p g (f z.1 * f z.2) = 0)
    {a b c : ℝ} (ha0 : 0 < a) (hab : a < b) (hbc : b < c) (hc1 : c < 1) :
    unitμ {x | f x = a} = 0 ∨ unitμ {x | f x = b} = 0 ∨ unitμ {x | f x = c} = 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2, h3⟩ := hcon
  exact not_three_values hd hp0 hp1 hfm hkkt ha0 hab hbc hc1
    (pos_iff_ne_zero.mpr h1) (pos_iff_ne_zero.mpr h2) (pos_iff_ne_zero.mpr h3)

end UpperTailOptimizers
