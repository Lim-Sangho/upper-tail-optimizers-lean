import UpperTailOptimizers.SingularEndpoint.DistributionMeasure

/-!
# The product-variance identity and the variance bootstrap (Section 7)

The measure-algebra chain inside the proof of `lem:auxiliary-lagrangian-bound`.  Three paper displays are realised:

* **The product–variance identity** — the paper carries no probabilistic
  second-moment identity (`\EE`, `Var`, `XY` do not occur in it); its role is taken by
  `eq:rank-one-reduction-bounds` together with the Chebyshev step in the same proof.  The exact
  identity `E(XY - r)² = (EX² - r)² + 2r·Var(X)` for independent `X, Y` with a common law;
* **`R_d² ≤ C_dΓ_d`**
  — its consequence
  `2r_*·Var(X) ≤ E(XY - r_*)²`, together with the Cauchy–Schwarz step
  `E(XY - r_*)² ≤ (E(XY - r_*)⁴)^{1/2}` through which `𝒢^{1/2}` enters it;
* the Taylor moment bound `0 ≤ EX^d - (EX)^d ≤ C·Var(X)` of
  `paper/singular_endpoint.tex`.

No family, no kernel and no law functional appears: every statement is about an arbitrary
probability measure `ν` on `ℝ` carried by the law interval `[0,2]`, written as
`ν ([0,2])ᶜ = 0` exactly as in `SingularEndpoint/DistributionMeasure.lean`.  That is why this half of the
capstone is independent of `lem:central-kernel-bound`.

## Independence without a product measure

The paper phrases the identity through independent copies `X, Y`.  Here it is the iterated
integral `∫∫(xy - r)² dν(y) dν(x)`, which is the same number and needs no Fubini theorem: the
inner integral is a quadratic polynomial in `x` whose coefficients are moments of `ν`, and the
outer integral is read off from the very same computation.  `integral_poly` is that one
computation — the moment expansion of a quartic polynomial — and it is used four times.

## Cauchy–Schwarz

`sq_integral_le_integral_sq`, namely `(∫F)² ≤ ∫F²` for a probability measure, is proved here
from `0 ≤ ∫(F - ∫F)²` and is the only form of Cauchy–Schwarz used.  Applying it first in the
inner variable and then in the outer variable gives `integral_sq_le_sqrt_integral_pow_four`
without ever forming `ν ⊗ ν`; the intermediate function `x ↦ ∫(xy - r)⁴ dν(y)` is integrable
because it too is an explicit polynomial in `x`.

## The Taylor bound keeps `d` symbolic

`exists_moment_sub_pow_le_variance` is proved from the exact double-geometric-sum
factorisation `pow_convex_gap_eq` of `Nondegeneracy/PowBounds.lean` — no derivative and no
decision procedure on `d`.  The lower bound `0 ≤ EX^d - (EX)^d` is the companion
`pow_convex_gap_ge` (Jensen for `x ↦ x^d`, read off from the same factorisation), and the
upper bound comes from bounding each summand of the factorisation by `2^{d-2}`, which gives
the explicit constant `C = d²·2^{d-2}`.  Only its existence is used downstream.

## Contents

* `integrable_of_continuousOn` — a function continuous on `[0,2]` is `ν`-integrable;
* `integral_prod_sub_sq` — the product–variance identity, an artefact of the formalisation:
  the paper states no such display;
* `variance_nonneg` — `0 ≤ m₂ - m₁²`;
* `integral_sq_le_sqrt_integral_pow_four` — the quartic-to-quadratic Cauchy–Schwarz step;
* `two_mul_rStar_mul_variance_le` — the rank-one case of `R_d² ≤ C_dΓ_d`;
* `exists_moment_sub_pow_le_variance` — the Taylor moment bound.
-/

namespace UpperTailOptimizers

namespace SingularEndpoint

open MeasureTheory

variable {d : ℕ}

/-! ## Integrability on the law interval -/

/-- **The integrability package, global form.**  A function continuous on the law interval
is integrable against a finite measure carried by `[0,2]`.  This is
`SingularEndpoint/DistributionMeasure.lean`'s `integrableOn_of_continuousOn` at `s = [0,2]`, followed by
`restrict_Icc_self`; every integrand below is a polynomial, so this is the only integrability
lemma the file needs. -/
theorem integrable_of_continuousOn {ν : Measure ℝ} [IsFiniteMeasure ν]
    (hν : ν (Set.Icc (0 : ℝ) 2)ᶜ = 0) {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc 0 2)) :
    Integrable f ν := by
  have h : IntegrableOn f (Set.Icc (0 : ℝ) 2) ν :=
    integrableOn_of_continuousOn hν hf isCompact_Icc
  rwa [IntegrableOn, restrict_Icc_self hν] at h

/-- **The moment expansion of a quartic polynomial.**  Against a probability measure carried by
`[0,2]` the integral of `a y⁴ + b y³ + c y² + e y + f` is the same combination of the first
four moments.  Every integral computed in this file is an instance of this one lemma. -/
private theorem integral_poly {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hν : ν (Set.Icc (0 : ℝ) 2)ᶜ = 0) (a b c e f : ℝ) :
    ∫ y, (a * y ^ 4 + b * y ^ 3 + c * y ^ 2 + e * y + f) ∂ν
      = a * (∫ y, y ^ 4 ∂ν) + b * (∫ y, y ^ 3 ∂ν) + c * (∫ y, y ^ 2 ∂ν)
        + e * (∫ y, y ∂ν) + f := by
  have i4 : Integrable (fun y : ℝ => a * y ^ 4) ν :=
    (integrable_of_continuousOn hν (f := fun y : ℝ => y ^ 4) (by fun_prop)).const_mul a
  have i3 : Integrable (fun y : ℝ => b * y ^ 3) ν :=
    (integrable_of_continuousOn hν (f := fun y : ℝ => y ^ 3) (by fun_prop)).const_mul b
  have i2 : Integrable (fun y : ℝ => c * y ^ 2) ν :=
    (integrable_of_continuousOn hν (f := fun y : ℝ => y ^ 2) (by fun_prop)).const_mul c
  have i1 : Integrable (fun y : ℝ => e * y) ν :=
    (integrable_of_continuousOn hν (f := fun y : ℝ => y) (by fun_prop)).const_mul e
  have s1 : Integrable (fun y : ℝ => a * y ^ 4 + b * y ^ 3) ν := i4.add i3
  have s2 : Integrable (fun y : ℝ => a * y ^ 4 + b * y ^ 3 + c * y ^ 2) ν := s1.add i2
  have s3 : Integrable (fun y : ℝ => a * y ^ 4 + b * y ^ 3 + c * y ^ 2 + e * y) ν := s2.add i1
  rw [integral_add s3 (integrable_const f), integral_add s2 i1, integral_add s1 i2,
    integral_add i4 i3, integral_const_mul, integral_const_mul, integral_const_mul,
    integral_const_mul, integral_const, probReal_univ, smul_eq_mul, one_mul]

/-- The moment expansion of `x^k + b x + c`, the shape in which the Taylor remainder is
integrated.  The exponent `k` stays symbolic, so this cannot be folded into `integral_poly`. -/
private theorem integral_pow_affine {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hν : ν (Set.Icc (0 : ℝ) 2)ᶜ = 0) (k : ℕ) (b c : ℝ) :
    ∫ x, (x ^ k + b * x + c) ∂ν = (∫ x, x ^ k ∂ν) + b * (∫ x, x ∂ν) + c := by
  have ik : Integrable (fun x : ℝ => x ^ k) ν :=
    integrable_of_continuousOn hν (f := fun x : ℝ => x ^ k) (by fun_prop)
  have i1 : Integrable (fun x : ℝ => b * x) ν :=
    (integrable_of_continuousOn hν (f := fun x : ℝ => x) (by fun_prop)).const_mul b
  have is : Integrable (fun x : ℝ => x ^ k + b * x) ν := ik.add i1
  rw [integral_add is (integrable_const c), integral_add ik i1, integral_const_mul,
    integral_const, probReal_univ, smul_eq_mul, one_mul]

/-! ## The product–variance identity (no counterpart in the paper) -/

/-- **The product–variance identity.**  The paper does not use it and reaches the dispersion bound from `eq:rank-one-reduction-bounds` instead.  Kept here because the Lean's route consumes it.
For `X, Y`
independent with common law `ν`,

`E(XY - r)² = (EX² - r)² + 2r·Var(X)`.

Both sides expand to `m₂² - 2r m₁² + r²`, so the proof is the moment expansion `integral_poly`
applied to the inner integral and then to the outer one, followed by `ring`.  The hypothesis
`ν ([0,2])ᶜ = 0` is used only for integrability of the polynomial integrands. -/
theorem integral_prod_sub_sq (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : ν (Set.Icc (0 : ℝ) 2)ᶜ = 0) (r : ℝ) :
    (∫ x, ∫ y, (x * y - r) ^ 2 ∂ν ∂ν)
      = ((∫ x, x ^ 2 ∂ν) - r) ^ 2 + 2 * r * ((∫ x, x ^ 2 ∂ν) - (∫ x, x ∂ν) ^ 2) := by
  have hinner : ∀ x : ℝ, (∫ y, (x * y - r) ^ 2 ∂ν)
      = x ^ 2 * (∫ y, y ^ 2 ∂ν) - 2 * r * (∫ y, y ∂ν) * x + r ^ 2 := by
    intro x
    have h1 : (∫ y, (x * y - r) ^ 2 ∂ν)
        = ∫ y, (0 * y ^ 4 + 0 * y ^ 3 + x ^ 2 * y ^ 2 + (-(2 * r * x)) * y + r ^ 2) ∂ν := by
      congr 1
      funext y
      ring
    rw [h1, integral_poly hν]
    ring
  have houter : (∫ x, (x ^ 2 * (∫ y, y ^ 2 ∂ν) - 2 * r * (∫ y, y ∂ν) * x + r ^ 2) ∂ν)
      = (∫ x, x ^ 2 ∂ν) * (∫ y, y ^ 2 ∂ν) - 2 * r * (∫ y, y ∂ν) * (∫ x, x ∂ν) + r ^ 2 := by
    have h1 : (∫ x, (x ^ 2 * (∫ y, y ^ 2 ∂ν) - 2 * r * (∫ y, y ∂ν) * x + r ^ 2) ∂ν)
        = ∫ x, (0 * x ^ 4 + 0 * x ^ 3 + (∫ y, y ^ 2 ∂ν) * x ^ 2
            + (-(2 * r * (∫ y, y ∂ν))) * x + r ^ 2) ∂ν := by
      congr 1
      funext x
      ring
    rw [h1, integral_poly hν]
    ring
  have hstep : (∫ x, ∫ y, (x * y - r) ^ 2 ∂ν ∂ν)
      = ∫ x, (x ^ 2 * (∫ y, y ^ 2 ∂ν) - 2 * r * (∫ y, y ∂ν) * x + r ^ 2) ∂ν := by
    congr 1
    funext x
    exact hinner x
  rw [hstep, houter]
  ring

/-! ## Cauchy–Schwarz -/

/-- **Cauchy–Schwarz for a probability measure:** `(∫F)² ≤ ∫F²`.  Proved from
`0 ≤ ∫(F - ∫F)²`, expanded by linearity; this is the only form of Cauchy–Schwarz the file
uses. -/
private theorem sq_integral_le_integral_sq {ν : Measure ℝ} [IsProbabilityMeasure ν] {F : ℝ → ℝ}
    (hF : Integrable F ν) (hF2 : Integrable (fun x => F x ^ 2) ν) :
    (∫ x, F x ∂ν) ^ 2 ≤ ∫ x, F x ^ 2 ∂ν := by
  have key : ∀ c : ℝ, ∫ x, (F x - c) ^ 2 ∂ν
      = (∫ x, F x ^ 2 ∂ν) + (-(2 * c)) * (∫ x, F x ∂ν) + c ^ 2 := by
    intro c
    have h1 : ∫ x, (F x - c) ^ 2 ∂ν
        = ∫ x, (F x ^ 2 + (-(2 * c)) * F x + c ^ 2) ∂ν := by
      congr 1
      funext x
      ring
    have i1 : Integrable (fun x => (-(2 * c)) * F x) ν := hF.const_mul _
    have is : Integrable (fun x => F x ^ 2 + (-(2 * c)) * F x) ν := hF2.add i1
    rw [h1, integral_add is (integrable_const _), integral_add hF2 i1, integral_const_mul,
      integral_const, probReal_univ, smul_eq_mul, one_mul]
  have h0 : 0 ≤ ∫ x, (F x - (∫ x, F x ∂ν)) ^ 2 ∂ν :=
    integral_nonneg fun _ => sq_nonneg _
  rw [key] at h0
  nlinarith [h0]

/-- `∫F ≤ (∫F²)^{1/2}` for a probability measure and an `F` of nonnegative integral. -/
private theorem integral_le_sqrt_integral_sq {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {F : ℝ → ℝ} (hF : Integrable F ν) (hF2 : Integrable (fun x => F x ^ 2) ν)
    (hnn : 0 ≤ ∫ x, F x ∂ν) : (∫ x, F x ∂ν) ≤ Real.sqrt (∫ x, F x ^ 2 ∂ν) :=
  (Real.le_sqrt hnn (integral_nonneg fun _ => sq_nonneg _)).mpr
    (sq_integral_le_integral_sq hF hF2)

/-- The outer Cauchy–Schwarz step, isolated so that the law computation only has to supply
the pointwise bound `G ≤ √H` and the three integrability facts. -/
private theorem integral_le_sqrt_of_pointwise {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {G H : ℝ → ℝ} (hG : Integrable G ν) (hH : Integrable H ν)
    (hs : Integrable (fun x => Real.sqrt (H x)) ν) (hHnn : ∀ x, 0 ≤ H x)
    (hpt : ∀ x, G x ≤ Real.sqrt (H x)) :
    (∫ x, G x ∂ν) ≤ Real.sqrt (∫ x, H x ∂ν) := by
  have hsq : (fun x => Real.sqrt (H x) ^ 2) = H := by
    funext x
    exact Real.sq_sqrt (hHnn x)
  have h1 : (∫ x, G x ∂ν) ≤ ∫ x, Real.sqrt (H x) ∂ν := integral_mono hG hs hpt
  have h2 : (∫ x, Real.sqrt (H x) ∂ν) ≤ Real.sqrt (∫ x, Real.sqrt (H x) ^ 2 ∂ν) :=
    integral_le_sqrt_integral_sq hs (by rw [hsq]; exact hH)
      (integral_nonneg fun _ => Real.sqrt_nonneg _)
  have h3 : (∫ x, Real.sqrt (H x) ^ 2 ∂ν) = ∫ x, H x ∂ν := by rw [hsq]
  rw [h3] at h2
  linarith

/-- **From the quartic average to the quadratic one.**  For a probability measure carried by
`[0,2]`,

`∫∫(xy - r)² ≤ (∫∫(xy - r)⁴)^{1/2}`,

which is how `𝒢^{1/2}` reaches the variance bootstrap in the paper's chain
`E(XY - r_*)² ≤ C𝒢^{1/2}`.  Cauchy–Schwarz is applied twice: in the inner variable, where the
square of `(xy - r)²` is `(xy - r)⁴`; and then in the outer variable, where the integrand is
`x ↦ (∫(xy - r)⁴ dν(y))^{1/2}`.  Both intermediate functions of `x` are explicit polynomials in
`x` with moment coefficients (`integral_poly`), which is what makes them integrable. -/
theorem integral_sq_le_sqrt_integral_pow_four (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : ν (Set.Icc (0 : ℝ) 2)ᶜ = 0) (r : ℝ) :
    (∫ x, ∫ y, (x * y - r) ^ 2 ∂ν ∂ν) ≤ Real.sqrt (∫ x, ∫ y, (x * y - r) ^ 4 ∂ν ∂ν) := by
  -- the two inner integrals as polynomials in `x`
  have hGeq : ∀ x : ℝ, (∫ y, (x * y - r) ^ 2 ∂ν)
      = (∫ y, y ^ 2 ∂ν) * x ^ 2 + (-(2 * r * (∫ y, y ∂ν))) * x + r ^ 2 := by
    intro x
    have h1 : (∫ y, (x * y - r) ^ 2 ∂ν)
        = ∫ y, (0 * y ^ 4 + 0 * y ^ 3 + x ^ 2 * y ^ 2 + (-(2 * r * x)) * y + r ^ 2) ∂ν := by
      congr 1
      funext y
      ring
    rw [h1, integral_poly hν]
    ring
  have hHeq : ∀ x : ℝ, (∫ y, (x * y - r) ^ 4 ∂ν)
      = (∫ y, y ^ 4 ∂ν) * x ^ 4 + (-(4 * r * (∫ y, y ^ 3 ∂ν))) * x ^ 3
          + 6 * r ^ 2 * (∫ y, y ^ 2 ∂ν) * x ^ 2 + (-(4 * r ^ 3 * (∫ y, y ∂ν))) * x
          + r ^ 4 := by
    intro x
    have h1 : (∫ y, (x * y - r) ^ 4 ∂ν)
        = ∫ y, (x ^ 4 * y ^ 4 + (-(4 * r * x ^ 3)) * y ^ 3 + (6 * r ^ 2 * x ^ 2) * y ^ 2
            + (-(4 * r ^ 3 * x)) * y + r ^ 4) ∂ν := by
      congr 1
      funext y
      ring
    rw [h1, integral_poly hν]
    ring
  -- integrability of the three outer integrands
  have iG : Integrable (fun x : ℝ => ∫ y, (x * y - r) ^ 2 ∂ν) ν := by
    simp only [hGeq]
    exact integrable_of_continuousOn hν (by fun_prop)
  have iH : Integrable (fun x : ℝ => ∫ y, (x * y - r) ^ 4 ∂ν) ν := by
    simp only [hHeq]
    exact integrable_of_continuousOn hν (by fun_prop)
  have iS : Integrable (fun x : ℝ => Real.sqrt (∫ y, (x * y - r) ^ 4 ∂ν)) ν := by
    simp only [hHeq]
    exact integrable_of_continuousOn hν (by fun_prop)
  -- the inner Cauchy–Schwarz, pointwise in `x`
  have hHnn : ∀ x : ℝ, 0 ≤ ∫ y, (x * y - r) ^ 4 ∂ν := by
    intro x
    exact integral_nonneg fun y => by positivity
  have hpt : ∀ x : ℝ, (∫ y, (x * y - r) ^ 2 ∂ν) ≤ Real.sqrt (∫ y, (x * y - r) ^ 4 ∂ν) := by
    intro x
    have i2 : Integrable (fun y : ℝ => (x * y - r) ^ 2) ν :=
      integrable_of_continuousOn hν (by fun_prop)
    have i4 : Integrable (fun y : ℝ => ((x * y - r) ^ 2) ^ 2) ν :=
      integrable_of_continuousOn hν (by fun_prop)
    have hnn : 0 ≤ ∫ y, (x * y - r) ^ 2 ∂ν := integral_nonneg fun y => sq_nonneg _
    have h := integral_le_sqrt_integral_sq i2 i4 hnn
    have he : (∫ y, ((x * y - r) ^ 2) ^ 2 ∂ν) = ∫ y, (x * y - r) ^ 4 ∂ν := by
      congr 1
      funext y
      ring
    rwa [he] at h
  exact integral_le_sqrt_of_pointwise iG iH iS hHnn hpt

/-! ## The variance -/

/-- **The variance is nonnegative:** `0 ≤ m₂ - m₁²`.  This is `(∫x)² ≤ ∫x²`, an instance of
`sq_integral_le_integral_sq`. -/
theorem variance_nonneg (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : ν (Set.Icc (0 : ℝ) 2)ᶜ = 0) : 0 ≤ (∫ x, x ^ 2 ∂ν) - (∫ x, x ∂ν) ^ 2 := by
  have h : (∫ x, x ∂ν) ^ 2 ≤ ∫ x, x ^ 2 ∂ν :=
    sq_integral_le_integral_sq (ν := ν) (F := fun x : ℝ => x)
      (integrable_of_continuousOn hν (f := fun x : ℝ => x) (by fun_prop))
      (integrable_of_continuousOn hν (f := fun x : ℝ => x ^ 2) (by fun_prop))
  linarith

/-- **The variance bootstrap**, the rank-one case of `R_d² ≤ C_dΓ_d`, which the paper states for an arbitrary
competitor `W` rather than for the factor law:

`2r_*·Var(X) ≤ E(XY - r_*)²`.

Immediate from `integral_prod_sub_sq` at `r = r_*`, the discarded term `(m₂ - r_*)²` being a
square.  Combined with `integral_sq_le_sqrt_integral_pow_four` and the paper's
`E(XY - r_*)² ≤ C𝒢^{1/2}` this is the paper's `Var(X) ≤ C𝒢^{1/2}`.  The degree hypothesis is
carried for documentation only: the inequality holds for every real `r`. -/
theorem two_mul_rStar_mul_variance_le (_hd : 2 ≤ d) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : ν (Set.Icc (0 : ℝ) 2)ᶜ = 0) :
    2 * rStar d * ((∫ x, x ^ 2 ∂ν) - (∫ x, x ∂ν) ^ 2)
      ≤ ∫ x, ∫ y, (x * y - rStar d) ^ 2 ∂ν ∂ν := by
  rw [integral_prod_sub_sq ν hν (rStar d)]
  linarith [sq_nonneg ((∫ x, x ^ 2 ∂ν) - rStar d)]

/-! ## The Taylor moment bound -/

/-- **The second-order Taylor bound for `x ↦ x^k` on `[0,2]`, `k` symbolic:**

`x^k - m^k - k·m^{k-1}(x - m) ≤ k²·2^{k-2}·(x - m)²`.

`pow_convex_gap_eq` (`Nondegeneracy/PowBounds.lean`) writes the left-hand side exactly as
`(x - m)²·∑_{i<k} (∑_{j<i} x^j m^{i-1-j}) m^{k-1-i}`.  On `[0,2]` each summand of the double
sum has total exponent `j + (i-1-j) + (k-1-i) = k-2`, hence is at most `2^{k-2}`, and there are
at most `k²` of them.  No derivative and no computation with `k` is involved; the exponent is
written `k` rather than `d` only to avoid shadowing the section variable. -/
private theorem pow_taylor_upper {x m : ℝ} (hx0 : 0 ≤ x) (hx2 : x ≤ 2) (hm0 : 0 ≤ m)
    (hm2 : m ≤ 2) (k : ℕ) :
    x ^ k - m ^ k - (k : ℝ) * m ^ (k - 1) * (x - m)
      ≤ (k : ℝ) ^ 2 * 2 ^ (k - 2) * (x - m) ^ 2 := by
  have hterm : ∀ i ∈ Finset.range k,
      (∑ j ∈ Finset.range i, x ^ j * m ^ (i - 1 - j)) * m ^ (k - 1 - i)
        ≤ (k : ℝ) * 2 ^ (k - 2) := by
    intro i hi
    have hid : i < k := Finset.mem_range.mp hi
    rw [Finset.sum_mul]
    calc ∑ j ∈ Finset.range i, x ^ j * m ^ (i - 1 - j) * m ^ (k - 1 - i)
        ≤ ∑ _j ∈ Finset.range i, (2 : ℝ) ^ (k - 2) := by
          refine Finset.sum_le_sum fun j hj => ?_
          have hji : j < i := Finset.mem_range.mp hj
          have e1 : x ^ j ≤ 2 ^ j := pow_le_pow_left₀ hx0 hx2 j
          have e2 : m ^ (i - 1 - j) ≤ 2 ^ (i - 1 - j) := pow_le_pow_left₀ hm0 hm2 _
          have e3 : m ^ (k - 1 - i) ≤ 2 ^ (k - 1 - i) := pow_le_pow_left₀ hm0 hm2 _
          have hexp : j + (i - 1 - j) + (k - 1 - i) = k - 2 := by omega
          calc x ^ j * m ^ (i - 1 - j) * m ^ (k - 1 - i)
              ≤ 2 ^ j * 2 ^ (i - 1 - j) * 2 ^ (k - 1 - i) := by
                have h12 : x ^ j * m ^ (i - 1 - j) ≤ 2 ^ j * 2 ^ (i - 1 - j) :=
                  mul_le_mul e1 e2 (pow_nonneg hm0 _) (by positivity)
                exact mul_le_mul h12 e3 (pow_nonneg hm0 _) (by positivity)
            _ = (2 : ℝ) ^ (k - 2) := by rw [← pow_add, ← pow_add, hexp]
      _ = (i : ℝ) * 2 ^ (k - 2) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ (k : ℝ) * 2 ^ (k - 2) := by
          have hle : (i : ℝ) ≤ (k : ℝ) := by exact_mod_cast hid.le
          exact mul_le_mul_of_nonneg_right hle (by positivity)
  have hsum : (∑ i ∈ Finset.range k,
      (∑ j ∈ Finset.range i, x ^ j * m ^ (i - 1 - j)) * m ^ (k - 1 - i))
      ≤ (k : ℝ) ^ 2 * 2 ^ (k - 2) := by
    calc (∑ i ∈ Finset.range k,
        (∑ j ∈ Finset.range i, x ^ j * m ^ (i - 1 - j)) * m ^ (k - 1 - i))
        ≤ ∑ _i ∈ Finset.range k, (k : ℝ) * 2 ^ (k - 2) := Finset.sum_le_sum hterm
      _ = (k : ℝ) * ((k : ℝ) * 2 ^ (k - 2)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ = (k : ℝ) ^ 2 * 2 ^ (k - 2) := by ring
  rw [pow_convex_gap_eq m x k, mul_comm ((x - m) ^ 2) _]
  exact mul_le_mul_of_nonneg_right hsum (sq_nonneg _)

/-- **The Taylor moment bound**.  There is a constant
`C > 0`, depending on `d` only, with

`0 ≤ EX^d - (EX)^d ≤ C·Var(X)`

for every probability measure `ν` on `ℝ` carried by `[0,2]`.

The lower bound is Jensen for the convex map `x ↦ x^d`, in the pointwise form
`pow_convex_gap_ge`: the mean lies in `[0,2]`, so `m^{d-2}(x-m)² ≤ x^d - m^d - d m^{d-1}(x-m)`
and the left-hand side is nonnegative.  The upper bound is `pow_taylor_upper`.  Integrating
either pointwise inequality kills the linear term, because `∫(x - m) dν = 0`, and turns
`∫(x - m)² dν` into `m₂ - m₁²`.  The explicit constant is `C = d²·2^{d-2}`; only its existence
is used downstream. -/
theorem exists_moment_sub_pow_le_variance (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ ν : Measure ℝ, IsProbabilityMeasure ν → ν (Set.Icc (0 : ℝ) 2)ᶜ = 0 →
      0 ≤ (∫ x, x ^ d ∂ν) - (∫ x, x ∂ν) ^ d ∧
        (∫ x, x ^ d ∂ν) - (∫ x, x ∂ν) ^ d
          ≤ C * ((∫ x, x ^ 2 ∂ν) - (∫ x, x ∂ν) ^ 2) := by
  have hdR : (0 : ℝ) < (d : ℝ) := by
    have : 0 < d := lt_of_lt_of_le (by norm_num) hd
    exact_mod_cast this
  refine ⟨(d : ℝ) ^ 2 * 2 ^ (d - 2), mul_pos (pow_pos hdR 2) (pow_pos (by norm_num) _), ?_⟩
  intro ν hν hνc
  have : IsProbabilityMeasure ν := hν
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = ∫ x, x ∂ν := ⟨_, rfl⟩
  rw [← hm]
  -- the mean lies in the law interval
  have hm0 : 0 ≤ m := by
    rw [hm]
    exact integral_nonneg_of_ae (by filter_upwards [ae_mem_Icc_of_distribution hνc] with x hx
      using hx.1)
  have hm2 : m ≤ 2 := by
    have h := integral_mono_ae
      (integrable_of_continuousOn hνc (f := fun x : ℝ => x) (by fun_prop))
      (integrable_const (2 : ℝ))
      (by filter_upwards [ae_mem_Icc_of_distribution hνc] with x hx using hx.2)
    rw [integral_const, probReal_univ, smul_eq_mul, one_mul, ← hm] at h
    exact h
  -- the two integrals of the Taylor sandwich
  have iL : Integrable
      (fun x : ℝ => x ^ d - m ^ d - (d : ℝ) * m ^ (d - 1) * (x - m)) ν :=
    integrable_of_continuousOn hνc (by fun_prop)
  have iR : Integrable
      (fun x : ℝ => (d : ℝ) ^ 2 * 2 ^ (d - 2) * (x - m) ^ 2) ν :=
    integrable_of_continuousOn hνc (by fun_prop)
  have hLint : (∫ x, (x ^ d - m ^ d - (d : ℝ) * m ^ (d - 1) * (x - m)) ∂ν)
      = (∫ x, x ^ d ∂ν) - m ^ d := by
    have h1 : (∫ x, (x ^ d - m ^ d - (d : ℝ) * m ^ (d - 1) * (x - m)) ∂ν)
        = ∫ x, (x ^ d + (-((d : ℝ) * m ^ (d - 1))) * x
            + (-(m ^ d) + (d : ℝ) * m ^ (d - 1) * m)) ∂ν := by
      congr 1
      funext x
      ring
    rw [h1, integral_pow_affine hνc, ← hm]
    ring
  have hRint : (∫ x, ((d : ℝ) ^ 2 * 2 ^ (d - 2) * (x - m) ^ 2) ∂ν)
      = (d : ℝ) ^ 2 * 2 ^ (d - 2) * ((∫ x, x ^ 2 ∂ν) - m ^ 2) := by
    have h1 : (∫ x, ((d : ℝ) ^ 2 * 2 ^ (d - 2) * (x - m) ^ 2) ∂ν)
        = ∫ x, (0 * x ^ 4 + 0 * x ^ 3 + ((d : ℝ) ^ 2 * 2 ^ (d - 2)) * x ^ 2
            + (-(2 * ((d : ℝ) ^ 2 * 2 ^ (d - 2)) * m)) * x
            + (d : ℝ) ^ 2 * 2 ^ (d - 2) * m ^ 2) ∂ν := by
      congr 1
      funext x
      ring
    rw [h1, integral_poly hνc, ← hm]
    ring
  constructor
  · have hae : ∀ᵐ x ∂ν, 0 ≤ x ^ d - m ^ d - (d : ℝ) * m ^ (d - 1) * (x - m) := by
      filter_upwards [ae_mem_Icc_of_distribution hνc] with x hx
      have h := pow_convex_gap_ge hm0 hx.1 hd
      have h0 : 0 ≤ m ^ (d - 2) * (x - m) ^ 2 :=
        mul_nonneg (pow_nonneg hm0 _) (sq_nonneg _)
      linarith
    have h := integral_nonneg_of_ae hae
    rwa [hLint] at h
  · have hae : ∀ᵐ x ∂ν, x ^ d - m ^ d - (d : ℝ) * m ^ (d - 1) * (x - m)
        ≤ (d : ℝ) ^ 2 * 2 ^ (d - 2) * (x - m) ^ 2 := by
      filter_upwards [ae_mem_Icc_of_distribution hνc] with x hx
      exact pow_taylor_upper hx.1 hx.2 hm0 hm2 d
    have h := integral_mono_ae iL iR hae
    rwa [hLint, hRint] at h

end SingularEndpoint

end UpperTailOptimizers
