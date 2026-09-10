import UpperTailOptimizers.SingularEndpoint.Quotient
import UpperTailOptimizers.SingularEndpoint.Interp3

/-!
# The two-node interpolation remainder (Section 7, `paper/singular_endpoint.tex`)

The arity-2 companion of `SingularEndpoint/Interp3.lean`: the same textbook Rolle argument with
**one fewer round**.  A twice differentiable `f` vanishing at two points `z₁ < z₂` of an
interval satisfies, at every point `z` of that interval,

  `f z = f'' ξ / 2 · (z - z₁)(z - z₂)`

for some `ξ` in the interval, and the *second divided difference* of an arbitrary `f` — the
everywhere-defined `dd2 f a b = dslope (dslope f a) b`, built the way `SingularEndpoint/Quotient.lean`
builds `quotient3` — is therefore trapped between `m/2` and `M/2` as soon as `m ≤ f'' ≤ M`.

## Why Section 7 wants it

The proof of `lem:central-kernel-bound`, which absorbs the expansion, expands the law kernel
`K_h` on the central square by linear interpolation in the analytic coordinate `w = x^d` at
the two nodes `s_h^d, t_h^d` `eq:moment-interpolation`, and needs the four coefficient
functions and the double remainder `Θ_h` of its kernel decomposition —
now an unlabelled display in that proof — to stay
*uniformly bounded as the nodes coalesce*.  The paper gets this from the integral formula
for divided differences quoted in that proof; the elementary substitute is the pair
below.  `dd2_factor` is the Newton form

  `f z = f a + (z - a)·f[a,b] + (z - a)(z - b)·f[a,b,z]`,

an identity with **no hypotheses at all** and no division by zero at the nodes, so it survives
the coalescence `h ↓ 0` verbatim; `dd2_mem_of_deriv2_mem` is the mean-value bound
`m/2 ≤ f[a,b,z] ≤ M/2` that makes the remainder uniformly bounded.  Together they replace the
divided-difference integral formula, exactly as `SingularEndpoint/Interp3.lean` and
`SingularEndpoint/Interp4.lean` replace the two Weierstrass divisions.

## The nodes

The bound is wanted at *every* `z` of the ambient interval, including `z = a` and `z = b`,
where the Rolle argument produces the vacuous identity `0 = 0`.  Those two values are computed
directly (route (ii) of the two routes available — no continuity/density argument is used):
`dd2 f a b a` is a plain difference quotient of `dslope f a` because `dslope f a a = f' a`,
and `dd2 f a b b` is the honest derivative of the quotient `(f · - f a)/(· - a)` at `b`.  Both
reduce to `exists_deriv2_eq_slope_sub`, which is Taylor's theorem with Lagrange remainder at a
double node — one round of Rolle to reach a critical point, one more to reach `f''`.

## Contents

* `exists_deriv2_eq_of_two_roots` — the two-node Lagrange remainder above, stated for an
  explicit chain of `HasDerivAt` hypotheses `f → f₁ → f₂` on `Set.Icc a b`;
* `dd2`, `dd2_factor`, `analyticOnNhd_dd2` — the total second divided difference, its Newton
  form, and the preservation of analyticity;
* `exists_dd2_eq_deriv2_half` — `dd2 f a b z = f₂ ξ / 2` for some `ξ` in the interval;
* `dd2_mem_of_deriv2_mem` — the resulting two-sided bound, valid at the nodes too.

Nothing in this file mentions the singular endpoint family, the graph `H`, or any object of Section 7;
it is stated for a bare pair of derivatives on a compact interval.
-/

namespace UpperTailOptimizers

namespace SingularEndpoint

open Filter Topology

/-! ## Rolle's theorem, twice -/

/-- Two rounds of Rolle at three simple zeros: if `g` vanishes at `w₁ < w₂ < w₃` in
`Set.Icc a b` and `g → g₁ → g₂` is a chain of derivatives there, then `g₂` vanishes somewhere
in the interval. -/
private theorem exists_deriv2_zero_of_three_roots {g g₁ g₂ : ℝ → ℝ} {a b : ℝ}
    (hg : ∀ x ∈ Set.Icc a b, HasDerivAt g (g₁ x) x)
    (hg₁ : ∀ x ∈ Set.Icc a b, HasDerivAt g₁ (g₂ x) x)
    {w₁ w₂ w₃ : ℝ}
    (m₁ : w₁ ∈ Set.Icc a b) (m₂ : w₂ ∈ Set.Icc a b) (m₃ : w₃ ∈ Set.Icc a b)
    (o₁₂ : w₁ < w₂) (o₂₃ : w₂ < w₃)
    (e₁ : g w₁ = 0) (e₂ : g w₂ = 0) (e₃ : g w₃ = 0) :
    ∃ ξ ∈ Set.Icc a b, g₂ ξ = 0 := by
  obtain ⟨c₁, hc₁l, hc₁r, hc₁⟩ := exists_deriv_zero_of_two_roots hg m₁ m₂ o₁₂ e₁ e₂
  obtain ⟨c₂, hc₂l, hc₂r, hc₂⟩ := exists_deriv_zero_of_two_roots hg m₂ m₃ o₂₃ e₂ e₃
  have mc₁ : c₁ ∈ Set.Icc a b := ⟨m₁.1.trans hc₁l.le, hc₁r.le.trans m₂.2⟩
  have mc₂ : c₂ ∈ Set.Icc a b := ⟨m₂.1.trans hc₂l.le, hc₂r.le.trans m₃.2⟩
  obtain ⟨ξ, hξl, hξr, hξ⟩ :=
    exists_deriv_zero_of_two_roots hg₁ mc₁ mc₂ (hc₁r.trans hc₂l) hc₁ hc₂
  exact ⟨ξ, ⟨mc₁.1.trans hξl.le, hξr.le.trans mc₂.2⟩, hξ⟩

/-- Two rounds of Rolle at one double zero and one simple zero: if `g` vanishes at `p` and at
`z ≠ p`, if `g₁` vanishes at `p` as well, and if `g → g₁ → g₂` is a chain of derivatives on
`Set.Icc A B`, then `g₂` vanishes somewhere in the interval.

The first round produces a zero `c` of `g₁` strictly between `p` and `z`; the second applies
to the two zeros `p ≠ c` of `g₁`. -/
private theorem exists_deriv2_zero_of_double_root {g g₁ g₂ : ℝ → ℝ} {A B : ℝ}
    (hg : ∀ x ∈ Set.Icc A B, HasDerivAt g (g₁ x) x)
    (hg₁ : ∀ x ∈ Set.Icc A B, HasDerivAt g₁ (g₂ x) x)
    {p z : ℝ} (hp : p ∈ Set.Icc A B) (hz : z ∈ Set.Icc A B) (hne : z ≠ p)
    (e₀p : g p = 0) (e₁p : g₁ p = 0) (e₀z : g z = 0) :
    ∃ ξ ∈ Set.Icc A B, g₂ ξ = 0 := by
  rcases lt_or_gt_of_ne hne with h | h
  · obtain ⟨c, hcl, hcr, hc⟩ := exists_deriv_zero_of_two_roots hg hz hp h e₀z e₀p
    have mc : c ∈ Set.Icc A B := ⟨hz.1.trans hcl.le, hcr.le.trans hp.2⟩
    obtain ⟨ξ, hξl, hξr, hξ⟩ := exists_deriv_zero_of_two_roots hg₁ mc hp hcr hc e₁p
    exact ⟨ξ, ⟨mc.1.trans hξl.le, hξr.le.trans hp.2⟩, hξ⟩
  · obtain ⟨c, hcl, hcr, hc⟩ := exists_deriv_zero_of_two_roots hg hp hz h e₀p e₀z
    have mc : c ∈ Set.Icc A B := ⟨hp.1.trans hcl.le, hcr.le.trans hz.2⟩
    obtain ⟨ξ, hξl, hξr, hξ⟩ := exists_deriv_zero_of_two_roots hg₁ hp mc hcl e₁p hc
    exact ⟨ξ, ⟨hp.1.trans hξl.le, hξr.le.trans mc.2⟩, hξ⟩

/-! ## The two-node Lagrange remainder -/

/-- **The two-node Lagrange interpolation remainder.**

If `f → f₁ → f₂` is a chain of derivatives on `Set.Icc a b` and `f` vanishes at two points
`z₁ < z₂` of that interval, then for every `z ∈ Set.Icc a b` there is a `ξ ∈ Set.Icc a b` with

  `f z = f₂ ξ / 2 * ((z - z₁) * (z - z₂))`.

No analyticity is used: the proof is Rolle's theorem applied twice to
`f - K · (· - z₁)(· - z₂)`, where `K` is chosen so that the difference also vanishes at `z`.
This is `exists_deriv3_eq_of_three_roots` of `SingularEndpoint/Interp3.lean` with one node — and one
round of Rolle — removed. -/
theorem exists_deriv2_eq_of_two_roots {f f₁ f₂ : ℝ → ℝ} {a b : ℝ}
    (hf : ∀ x ∈ Set.Icc a b, HasDerivAt f (f₁ x) x)
    (hf₁ : ∀ x ∈ Set.Icc a b, HasDerivAt f₁ (f₂ x) x)
    {z₁ z₂ : ℝ} (hz₁ : z₁ ∈ Set.Icc a b) (hz₂ : z₂ ∈ Set.Icc a b) (h₁₂ : z₁ < z₂)
    (e₁ : f z₁ = 0) (e₂ : f z₂ = 0)
    {z : ℝ} (hz : z ∈ Set.Icc a b) :
    ∃ ξ ∈ Set.Icc a b, f z = f₂ ξ / 2 * ((z - z₁) * (z - z₂)) := by
  -- If `z` is one of the nodes both sides vanish.
  by_cases hd₁ : z = z₁
  · exact ⟨z₁, hz₁, by rw [hd₁, e₁]; ring⟩
  by_cases hd₂ : z = z₂
  · exact ⟨z₁, hz₁, by rw [hd₂, e₂]; ring⟩
  -- Otherwise the monic quadratic is nonzero at `z`, so `f z` is a multiple of it.
  have hPne : (z - z₁) * (z - z₂) ≠ 0 :=
    mul_ne_zero (sub_ne_zero.mpr hd₁) (sub_ne_zero.mpr hd₂)
  obtain ⟨K, hK⟩ : ∃ K : ℝ, f z = K * ((z - z₁) * (z - z₂)) :=
    ⟨f z / ((z - z₁) * (z - z₂)), (div_mul_cancel₀ _ hPne).symm⟩
  -- Derivatives of the monic quadratic `P w = (w - z₁)(w - z₂)`, down to `P'' ≡ 2`.
  have hlin : ∀ c x : ℝ, HasDerivAt (fun w : ℝ => w - c) 1 x := fun c x =>
    (hasDerivAt_id x).sub_const c
  have hP : ∀ x : ℝ,
      HasDerivAt (fun w : ℝ => (w - z₁) * (w - z₂)) ((x - z₂) + (x - z₁)) x := fun x =>
    ((hlin z₁ x).mul (hlin z₂ x)).congr_deriv (by ring)
  have hP₁ : ∀ x : ℝ, HasDerivAt (fun w : ℝ => (w - z₂) + (w - z₁)) 2 x := fun x =>
    ((hlin z₂ x).add (hlin z₁ x)).congr_deriv (by norm_num)
  -- The chain of derivatives of `g = f - K · P`.
  have hg : ∀ x ∈ Set.Icc a b,
      HasDerivAt (fun w : ℝ => f w - K * ((w - z₁) * (w - z₂)))
        (f₁ x - K * ((x - z₂) + (x - z₁))) x :=
    fun x hx => (hf x hx).sub ((hP x).const_mul K)
  have hg₁ : ∀ x ∈ Set.Icc a b,
      HasDerivAt (fun w : ℝ => f₁ w - K * ((w - z₂) + (w - z₁))) (f₂ x - K * 2) x :=
    fun x hx => (hf₁ x hx).sub ((hP₁ x).const_mul K)
  -- The three zeros of `g`.
  have g₁0 : f z₁ - K * ((z₁ - z₁) * (z₁ - z₂)) = 0 := by rw [e₁]; ring
  have g₂0 : f z₂ - K * ((z₂ - z₁) * (z₂ - z₂)) = 0 := by rw [e₂]; ring
  have gz0 : f z - K * ((z - z₁) * (z - z₂)) = 0 := by rw [hK]; ring
  -- Rolle, in whichever order the three points happen to sit.
  have key : ∀ w₁ w₂ w₃ : ℝ, w₁ ∈ Set.Icc a b → w₂ ∈ Set.Icc a b → w₃ ∈ Set.Icc a b →
      w₁ < w₂ → w₂ < w₃ →
      f w₁ - K * ((w₁ - z₁) * (w₁ - z₂)) = 0 →
      f w₂ - K * ((w₂ - z₁) * (w₂ - z₂)) = 0 →
      f w₃ - K * ((w₃ - z₁) * (w₃ - z₂)) = 0 →
      ∃ ξ ∈ Set.Icc a b, f z = f₂ ξ / 2 * ((z - z₁) * (z - z₂)) := by
    intro w₁ w₂ w₃ m₁ m₂ m₃ o₁₂ o₂₃ r₁ r₂ r₃
    obtain ⟨ξ, hξ, hξ0⟩ :=
      exists_deriv2_zero_of_three_roots hg hg₁ m₁ m₂ m₃ o₁₂ o₂₃ r₁ r₂ r₃
    refine ⟨ξ, hξ, ?_⟩
    have hval : f₂ ξ = 2 * K := by linarith
    rw [hK, hval]; ring
  rcases lt_trichotomy z z₁ with hA | hA | hA
  · exact key z z₁ z₂ hz hz₁ hz₂ hA h₁₂ gz0 g₁0 g₂0
  · exact absurd hA hd₁
  rcases lt_trichotomy z z₂ with hB | hB | hB
  · exact key z₁ z z₂ hz₁ hz hz₂ hA hB g₁0 gz0 g₂0
  · exact absurd hB hd₂
  · exact key z₁ z₂ z hz₁ hz₂ hz h₁₂ hB g₁0 g₂0 gz0

/-- **Taylor's theorem with Lagrange remainder at a double node.**  If `f → f₁ → f₂` is a
chain of derivatives on `Set.Icc A B` and both `f` and `f₁` vanish at `p`, then for every
`z ∈ Set.Icc A B` there is a `ξ ∈ Set.Icc A B` with

  `f z = f₂ ξ / 2 * ((z - p) * (z - p))`.

The confluent face of `exists_deriv2_eq_of_two_roots`, proved the same way from
`exists_deriv2_zero_of_double_root`; it is what supplies the values of `dd2` at the nodes. -/
private theorem exists_deriv2_eq_of_double_root {f f₁ f₂ : ℝ → ℝ} {A B : ℝ}
    (hf : ∀ x ∈ Set.Icc A B, HasDerivAt f (f₁ x) x)
    (hf₁ : ∀ x ∈ Set.Icc A B, HasDerivAt f₁ (f₂ x) x)
    {p : ℝ} (hp : p ∈ Set.Icc A B) (e₀ : f p = 0) (e₁ : f₁ p = 0)
    {z : ℝ} (hz : z ∈ Set.Icc A B) :
    ∃ ξ ∈ Set.Icc A B, f z = f₂ ξ / 2 * ((z - p) * (z - p)) := by
  by_cases hzp : z = p
  · exact ⟨p, hp, by rw [hzp, e₀]; ring⟩
  have hPne : (z - p) * (z - p) ≠ 0 :=
    mul_ne_zero (sub_ne_zero.mpr hzp) (sub_ne_zero.mpr hzp)
  obtain ⟨K, hK⟩ : ∃ K : ℝ, f z = K * ((z - p) * (z - p)) :=
    ⟨f z / ((z - p) * (z - p)), (div_mul_cancel₀ _ hPne).symm⟩
  have hlin : ∀ x : ℝ, HasDerivAt (fun w : ℝ => w - p) 1 x := fun x =>
    (hasDerivAt_id x).sub_const p
  have hP : ∀ x : ℝ,
      HasDerivAt (fun w : ℝ => (w - p) * (w - p)) ((x - p) + (x - p)) x := fun x =>
    ((hlin x).mul (hlin x)).congr_deriv (by ring)
  have hP₁ : ∀ x : ℝ, HasDerivAt (fun w : ℝ => (w - p) + (w - p)) 2 x := fun x =>
    ((hlin x).add (hlin x)).congr_deriv (by norm_num)
  have hg : ∀ x ∈ Set.Icc A B,
      HasDerivAt (fun w : ℝ => f w - K * ((w - p) * (w - p)))
        (f₁ x - K * ((x - p) + (x - p))) x :=
    fun x hx => (hf x hx).sub ((hP x).const_mul K)
  have hg₁ : ∀ x ∈ Set.Icc A B,
      HasDerivAt (fun w : ℝ => f₁ w - K * ((w - p) + (w - p))) (f₂ x - K * 2) x :=
    fun x hx => (hf₁ x hx).sub ((hP₁ x).const_mul K)
  have r₀ : f p - K * ((p - p) * (p - p)) = 0 := by rw [e₀]; ring
  have r₁ : f₁ p - K * ((p - p) + (p - p)) = 0 := by rw [e₁]; ring
  have rz : f z - K * ((z - p) * (z - p)) = 0 := by rw [hK]; ring
  obtain ⟨ξ, hξ, hξ0⟩ := exists_deriv2_zero_of_double_root hg hg₁ hp hz hzp r₀ r₁ rz
  refine ⟨ξ, hξ, ?_⟩
  have hval : f₂ ξ = 2 * K := by linarith
  rw [hK, hval]; ring

/-- The mean-value form of the **first** divided difference minus the derivative at its base
point: for `p ≠ q` in `Set.Icc A B` there is a `ξ` in the interval with

  `f[p,q] - f' p = f₂ ξ / 2 · (q - p)`.

This is `exists_deriv2_eq_of_double_root` applied to `w ↦ f w - f p - (w - p) f' p`, and it is
the single computation behind both node values of `dd2`. -/
private theorem exists_deriv2_eq_slope_sub {f f₁ f₂ : ℝ → ℝ} {A B : ℝ}
    (hf : ∀ x ∈ Set.Icc A B, HasDerivAt f (f₁ x) x)
    (hf₁ : ∀ x ∈ Set.Icc A B, HasDerivAt f₁ (f₂ x) x)
    {p q : ℝ} (hp : p ∈ Set.Icc A B) (hq : q ∈ Set.Icc A B) (hpq : p ≠ q) :
    ∃ ξ ∈ Set.Icc A B, dslope f p q - f₁ p = f₂ ξ / 2 * (q - p) := by
  have hG : ∀ x ∈ Set.Icc A B,
      HasDerivAt (fun w : ℝ => f w - f p - (w - p) * f₁ p) (f₁ x - f₁ p) x := by
    intro x hx
    exact (((hf x hx).sub_const (f p)).sub
      (((hasDerivAt_id x).sub_const p).mul_const (f₁ p))).congr_deriv (by ring)
  have hG₁ : ∀ x ∈ Set.Icc A B, HasDerivAt (fun w : ℝ => f₁ w - f₁ p) (f₂ x) x :=
    fun x hx => (hf₁ x hx).sub_const (f₁ p)
  have e₀ : f p - f p - (p - p) * f₁ p = 0 := by ring
  have e₁ : f₁ p - f₁ p = 0 := by ring
  obtain ⟨ξ, hξ, hval⟩ := exists_deriv2_eq_of_double_root hG hG₁ hp e₀ e₁ hq
  refine ⟨ξ, hξ, ?_⟩
  have hval' : f q - f p - (q - p) * f₁ p = f₂ ξ / 2 * ((q - p) * (q - p)) := hval
  have hd : (q - p) * dslope f p q = f q - f p := sub_mul_dslope f p q
  have hqp : q - p ≠ 0 := sub_ne_zero.mpr (Ne.symm hpq)
  refine mul_left_cancel₀ hqp ?_
  linarith [hval', hd]

/-! ## The everywhere-defined second divided difference -/

/-- **The second divided difference `f[a,b,·]`**, built the way `SingularEndpoint/Quotient.lean` builds
`quotient3`: two iterations of Mathlib's `dslope`, based first at `a` and then at `b`.

Being a `dslope` it is *total* — there is no division by zero at the nodes, and no hypothesis
of any kind enters `dd2_factor` below. -/
noncomputable def dd2 (f : ℝ → ℝ) (a b : ℝ) : ℝ → ℝ := dslope (dslope f a) b

/-- **The Newton form.**  For every `f` and all reals `a`, `b`, `z`,

  `f z = f a + (z - a)·f[a,b] + (z - a)(z - b)·f[a,b,z]`,

an identity with no hypotheses: `f` need not be differentiable, and `a`, `b`, `z` need not be
distinct.  Two applications of `sub_mul_dslope`, first at the base point `b` of the outer
quotient and then at the base point `a` of the inner one. -/
theorem dd2_factor (f : ℝ → ℝ) (a b z : ℝ) :
    f z = f a + (z - a) * dslope f a b + (z - a) * (z - b) * dd2 f a b z := by
  have e₂ : (z - b) * dd2 f a b z = dslope f a z - dslope f a b :=
    sub_mul_dslope (dslope f a) b z
  have e₁ : (z - a) * dslope f a z = f z - f a := sub_mul_dslope f a z
  calc f z = f a + (z - a) * dslope f a z := by linarith [e₁]
    _ = f a + (z - a) * (dslope f a b + (z - b) * dd2 f a b z) := by
        rw [show dslope f a b + (z - b) * dd2 f a b z = dslope f a z from by linarith [e₂]]
    _ = f a + (z - a) * dslope f a b + (z - a) * (z - b) * dd2 f a b z := by ring

/-- The second divided difference of a function analytic on a neighbourhood of `s` is again
analytic on a neighbourhood of `s`, as soon as both nodes lie in `s`.  Two applications of
`analyticOnNhd_dslope` (`SingularEndpoint/Quotient.lean`). -/
theorem analyticOnNhd_dd2 {f : ℝ → ℝ} {s : Set ℝ} {a b : ℝ}
    (hf : AnalyticOnNhd ℝ f s) (ha : a ∈ s) (hb : b ∈ s) : AnalyticOnNhd ℝ (dd2 f a b) s :=
  analyticOnNhd_dslope (analyticOnNhd_dslope hf ha) hb

/-- The value of `dd2` at its **first** node.  Since `dslope f a a = f' a`, the outer quotient
is an ordinary difference quotient of `dslope f a` between `a` and `b`:

  `f[a,b,a]·(b - a) = f[a,b] - f' a`.

Stated multiplicatively so that no nonvanishing hypothesis on `b - a` is needed here. -/
private theorem dd2_left {f f₁ : ℝ → ℝ} {a b : ℝ} (hab : a ≠ b)
    (hfa : HasDerivAt f (f₁ a) a) :
    dd2 f a b a * (b - a) = dslope f a b - f₁ a := by
  have h1 : dslope f a a = f₁ a := by rw [dslope_same]; exact hfa.deriv
  have h2 : dd2 f a b a = (f₁ a - dslope f a b) / (a - b) := by
    show dslope (dslope f a) b a = (f₁ a - dslope f a b) / (a - b)
    rw [dslope_of_ne _ hab, slope_def_field, h1]
  rw [h2, div_mul_eq_mul_div, div_eq_iff (sub_ne_zero.mpr hab)]
  ring

/-- The value of `dd2` at its **second** node.  There `dslope (dslope f a) b b` is by
definition `deriv (dslope f a) b`, and near `b ≠ a` the function `dslope f a` is the honest
quotient `(f · - f a)/(· - a)`, whose derivative at `b` is computed by the quotient rule:

  `f[a,b,b]·(b - a) = f' b - f[a,b]`. -/
private theorem dd2_right {f f₁ : ℝ → ℝ} {a b : ℝ} (hab : a ≠ b)
    (hfb : HasDerivAt f (f₁ b) b) :
    dd2 f a b b * (b - a) = f₁ b - dslope f a b := by
  have hba : b ≠ a := Ne.symm hab
  have hba' : b - a ≠ 0 := sub_ne_zero.mpr hba
  have hq : HasDerivAt (fun w : ℝ => (f w - f a) / (w - a))
      ((f₁ b * (b - a) - (f b - f a) * 1) / (b - a) ^ 2) b :=
    (hfb.sub_const (f a)).div ((hasDerivAt_id b).sub_const a) hba'
  have heq : dslope f a =ᶠ[𝓝 b] fun w : ℝ => (f w - f a) / (w - a) := by
    filter_upwards [isOpen_ne.mem_nhds hba] with w hw
    rw [dslope_of_ne _ hw, slope_def_field]
  have hd : HasDerivAt (dslope f a) ((f₁ b * (b - a) - (f b - f a) * 1) / (b - a) ^ 2) b :=
    hq.congr_of_eventuallyEq heq
  have h0 : dd2 f a b b = deriv (dslope f a) b := dslope_same (dslope f a) b
  have hfa : f b - f a = (b - a) * dslope f a b := (sub_mul_dslope f a b).symm
  rw [h0, hd.deriv, hfa, div_mul_eq_mul_div, div_eq_iff (pow_ne_zero 2 hba')]
  ring

/-! ## The mean-value bound -/

/-- **The mean-value theorem for the second divided difference.**  If `f → f₁ → f₂` is a chain
of derivatives on `Set.Icc A B` and `a < b` are two points of that interval, then for every
`z ∈ Set.Icc A B` there is a `ξ ∈ Set.Icc A B` with

  `dd2 f a b z = f₂ ξ / 2`.

Off the nodes this is `exists_deriv2_eq_of_two_roots` applied to the difference `g` between
`f` and its linear interpolant, whose two roots are `a` and `b`: `dd2_factor` identifies
`g z` with `(z - a)(z - b)·dd2 f a b z`, and the common factor cancels.  At `z = a` and at
`z = b` — which the coalescing application does reach — the identity `0 = 0` carries no
information, and the two values are instead computed directly by `dd2_left`, `dd2_right` and
`exists_deriv2_eq_slope_sub`. -/
theorem exists_dd2_eq_deriv2_half {f f₁ f₂ : ℝ → ℝ} {A B : ℝ}
    (hf : ∀ x ∈ Set.Icc A B, HasDerivAt f (f₁ x) x)
    (hf₁ : ∀ x ∈ Set.Icc A B, HasDerivAt f₁ (f₂ x) x)
    {a b : ℝ} (ha : a ∈ Set.Icc A B) (hb : b ∈ Set.Icc A B) (hab : a < b)
    {z : ℝ} (hz : z ∈ Set.Icc A B) :
    ∃ ξ ∈ Set.Icc A B, dd2 f a b z = f₂ ξ / 2 := by
  have hne : a ≠ b := ne_of_lt hab
  have hba' : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  by_cases hza : z = a
  · rw [hza]
    obtain ⟨ξ, hξ, hval⟩ := exists_deriv2_eq_slope_sub hf hf₁ ha hb hne
    refine ⟨ξ, hξ, mul_right_cancel₀ hba' ?_⟩
    rw [dd2_left hne (hf a ha)]
    exact hval
  by_cases hzb : z = b
  · rw [hzb]
    obtain ⟨ξ, hξ, hval⟩ := exists_deriv2_eq_slope_sub hf hf₁ hb ha (Ne.symm hne)
    have hsym : dslope f b a = dslope f a b := by
      rw [dslope_of_ne _ hne, dslope_of_ne _ (Ne.symm hne), slope_comm]
    rw [hsym] at hval
    refine ⟨ξ, hξ, mul_right_cancel₀ hba' ?_⟩
    rw [dd2_right hne (hf b hb)]
    linarith [hval]
  -- The generic case: `g = f - (linear interpolant)` has the two roots `a` and `b`.
  · have hG : ∀ x ∈ Set.Icc A B,
        HasDerivAt (fun w : ℝ => f w - f a - (w - a) * dslope f a b)
          (f₁ x - dslope f a b) x := by
      intro x hx
      exact (((hf x hx).sub_const (f a)).sub
        (((hasDerivAt_id x).sub_const a).mul_const (dslope f a b))).congr_deriv (by ring)
    have hG₁ : ∀ x ∈ Set.Icc A B,
        HasDerivAt (fun w : ℝ => f₁ w - dslope f a b) (f₂ x) x :=
      fun x hx => (hf₁ x hx).sub_const (dslope f a b)
    have eA : f a - f a - (a - a) * dslope f a b = 0 := by ring
    have eB : f b - f a - (b - a) * dslope f a b = 0 := by rw [sub_mul_dslope]; ring
    obtain ⟨ξ, hξ, hval⟩ := exists_deriv2_eq_of_two_roots hG hG₁ ha hb hab eA eB hz
    have hval' : f z - f a - (z - a) * dslope f a b
        = f₂ ξ / 2 * ((z - a) * (z - b)) := hval
    refine ⟨ξ, hξ, mul_left_cancel₀
      (mul_ne_zero (sub_ne_zero.mpr hza) (sub_ne_zero.mpr hzb)) ?_⟩
    linarith [hval', dd2_factor f a b z]

/-- **The mean-value bound for `dd2` — the point of the file.**  If `f → f₁ → f₂` is a chain of
derivatives on `Set.Icc A B` with `m ≤ f₂ ≤ M` there, and `a < b` are two points of the
interval, then the second divided difference is trapped:

  `m/2 ≤ f[a,b,z] ≤ M/2`   for every `z ∈ Set.Icc A B`.

The bound holds at the two nodes as well, and — since `dd2` never divides by zero — it is
uniform as the nodes coalesce.  Together with the hypothesis-free `dd2_factor` this is what
replaces the divided-difference integral formula quoted in the proof of
`lem:central-kernel-bound`. -/
theorem dd2_mem_of_deriv2_mem {f f₁ f₂ : ℝ → ℝ} {A B m M : ℝ}
    (hf : ∀ x ∈ Set.Icc A B, HasDerivAt f (f₁ x) x)
    (hf₁ : ∀ x ∈ Set.Icc A B, HasDerivAt f₁ (f₂ x) x)
    (hm : ∀ x ∈ Set.Icc A B, m ≤ f₂ x) (hM : ∀ x ∈ Set.Icc A B, f₂ x ≤ M)
    {a b : ℝ} (ha : a ∈ Set.Icc A B) (hb : b ∈ Set.Icc A B) (hab : a < b)
    {z : ℝ} (hz : z ∈ Set.Icc A B) :
    m / 2 ≤ dd2 f a b z ∧ dd2 f a b z ≤ M / 2 := by
  obtain ⟨ξ, hξ, hval⟩ := exists_dd2_eq_deriv2_half hf hf₁ ha hb hab hz
  rw [hval]
  exact ⟨by linarith [hm ξ hξ], by linarith [hM ξ hξ]⟩

end SingularEndpoint

end UpperTailOptimizers
