import UpperTailOptimizers.SingularEndpoint.Factor

/-!
# Local Hölder stability at the singular endpoint (Section 7)

This file formalises chunk **(II)** of `lem:localization-rank-one` of
`paper/singular_endpoint.tex` — the coercivity bound `eq:moment-and-cost-gap-bounds` and, combined with
`eq:rank-one-reduction-bounds`, the stability inequality

`(∫ W^d)^{m/d} - t(H,W) ≥ c‖E‖₂² - C‖W - r_*‖₄⁴ - C‖E‖₂³`,

on top of the algebraic layer of `SingularEndpoint/Factor.lean`.  The paper no longer
labels the combined inequality: `lem:localization-rank-one` states its two ingredients
separately, and the proof of `lem:localization-rank-one` recombines them with an
additional `-C_{d,m}‖E‖₂⁴` term; the form proved here carries no such term.  That layer
supplies the exact
binomial expansion `eq:rank-one-reduction-bounds` (`FactorDecomp.Wmoment_eq`) together with the
vanishing of its linear term (`FactorDecomp.linear_term_zero`); what is added here is the
analytic content of the last two paragraphs of the proof:

* **coercivity** of the quadratic term, `∫∫ A^{d-2}E² ≥ c‖E‖₂² - Cε⁴` (`coercive_quadratic`);
* **Young absorption** of the cubic-and-higher tail of the expansion (`tail_absorption`,
  `abs_tail_le`), giving `eq:moment-and-cost-gap-bounds` as `Wmoment_sub_qsq_ge`;
* the **tangent-line** step at the base point `q²` (Bernoulli's inequality for the exponent
  `m/d = v/2`), which replaces the paper's two-sided Taylor expansion and is *sharper*: it
  produces no `O(ε⁴)` remainder at all.

## What is assumed, and where it comes from

`Nonempty (FactorDecomp d W)` is vacuous (`f = 0` satisfies every field), so every closeness
statement of `lem:localization-rank-one` that the argument needs is carried as an
*explicit hypothesis*, in the repo's integral vocabulary rather than as Mathlib `Lp` norms:

* `hA4 : P.rankOneQuart ≤ C₁ * defectQuart d W` — this is `‖A - r_*‖₄ ≤ Cε` from
  `eq:rank-one-reduction-bounds`, raised to the fourth power (the paper's
  "`‖A - r_*‖₄ + ‖E‖₄ ≤ Cε`");
* `hE4 : P.residQuart ≤ C₂ * defectQuart d W` — likewise `‖E‖₄ ≤ Cε`, from the same clause;
* `hq : q₀ ≤ P.qVal` with `0 < q₀` — the paper's "`q` stays bounded away from zero", a
  consequence of `eq:rank-one-reduction-bounds` and `q → u_*^d`;
* `hT : |T - P.qVal ^ v| ≤ C₃ * P.residNorm ^ 3` — this is exactly chunk **(III)**,
  `eq:rank-one-reduction-bounds`, which is *not* proved here: `T` stands for
  `t(H,W)` and the hypothesis is `t(H,W) = q^v + 𝓡_H` with `|𝓡_H| ≤ C‖E‖₂³`.  It is proved in
  `SingularEndpoint/FactorHDensity.lean`.

The existence of the decomposition — chunk **(I)**, the `L^p` problem — is likewise not here;
it is the contraction construction of `SingularEndpoint/FactorContraction.lean`, `SingularEndpoint/FactorFix.lean` and
`SingularEndpoint/FactorSolution.lean`, delivered as `exists_factorDecomp`
(`SingularEndpoint/FactorMain.lean`), where all three chunks are joined into `localization_rankOne`.
Nothing in this file uses the graph `H` itself; it
enters only through the two integers `v = |V(H)|` and `m = |E(H)|` and the `d`-regular
handshake `2m = vd`, which is taken as the hypothesis `hvm`.

## Contents

* `defectQuart d W` — the quartic defect `ε⁴ = ‖W - r_*‖₄⁴`;
* `coerConst`, `tailConst`, `tailQuartConst`, `quartConst`, `stabCoer`, `stabQuart` — the
  explicit constants of the estimates, with their positivity lemmas;
* `FactorDecomp.residSq`, `residCube`, `residQuart`, `rankOneQuart`, `residNorm` — the norms
  `‖E‖₂²`, `‖E‖₁₁₁ := ∫|E|³`, `‖E‖₄⁴`, `‖A - r_*‖₄⁴` and `‖E‖₂`;
* `FactorDecomp.coercive_quadratic` — the coercivity estimate, unconditional;
* `FactorDecomp.tail_absorption`, `FactorDecomp.abs_tail_le` — the cubic-and-higher tail;
* `FactorDecomp.Wmoment_sub_qsq_ge` — `eq:moment-and-cost-gap-bounds`;
* `FactorDecomp.holder_stability` and `exists_holder_stability` — the combined stability
  inequality above, with explicit constants and in `∃ c, C > 0`
  shape respectively.
-/

namespace UpperTailOptimizers

namespace SingularEndpoint

open MeasureTheory

variable {d : ℕ} {W : Graphon}

/-! ## Elementary tools -/

/-- **The pointwise coercivity inequality.**  With `θ` the threshold `r_*/2`, on the good set
`A ≥ θ` the coefficient `A^e` dominates `θ^e`, while on the bad set `A < θ` the quartic
defect `(A - 2θ)⁴` already exceeds `θ⁴` and pays for the whole of `θ^e E² ≤ 25`.  This is the
pointwise form of the measure-theoretic Chebyshev split in the proof of
`lem:localization-rank-one`. -/
private theorem pointwise_coercive {θ A E : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hA : 0 ≤ A)
    (hE : E ^ 2 ≤ 25) (e : ℕ) :
    θ ^ e * E ^ 2 - 25 / θ ^ 4 * (A - 2 * θ) ^ 4 ≤ A ^ e * E ^ 2 := by
  have hE0 : (0:ℝ) ≤ E ^ 2 := sq_nonneg E
  have hθ4 : (0:ℝ) < θ ^ 4 := by positivity
  by_cases hcase : θ ≤ A
  · have h1 : θ ^ e ≤ A ^ e := pow_le_pow_left₀ hθ0.le hcase e
    have h2 : θ ^ e * E ^ 2 ≤ A ^ e * E ^ 2 := mul_le_mul_of_nonneg_right h1 hE0
    have h3 : (0:ℝ) ≤ 25 / θ ^ 4 * (A - 2 * θ) ^ 4 :=
      mul_nonneg (div_nonneg (by norm_num) hθ4.le) (by positivity)
    linarith
  · push Not at hcase
    have h1 : θ ^ e ≤ 1 := pow_le_one₀ hθ0.le hθ1
    have h2 : θ ^ e * E ^ 2 ≤ 25 := by
      calc θ ^ e * E ^ 2 ≤ 1 * E ^ 2 := mul_le_mul_of_nonneg_right h1 hE0
        _ = E ^ 2 := one_mul _
        _ ≤ 25 := hE
    have h3 : θ ^ 4 ≤ (A - 2 * θ) ^ 4 := by
      have hle : θ ≤ 2 * θ - A := by linarith
      calc θ ^ 4 ≤ (2 * θ - A) ^ 4 := pow_le_pow_left₀ hθ0.le hle 4
        _ = (A - 2 * θ) ^ 4 := by ring
    have h5 : (25:ℝ) ≤ 25 / θ ^ 4 * (A - 2 * θ) ^ 4 := by
      have h6 : 25 / θ ^ 4 * θ ^ 4 ≤ 25 / θ ^ 4 * (A - 2 * θ) ^ 4 :=
        mul_le_mul_of_nonneg_left h3 (div_nonneg (by norm_num) hθ4.le)
      rwa [div_mul_cancel₀ _ (ne_of_gt hθ4)] at h6
    have h7 : (0:ℝ) ≤ A ^ e * E ^ 2 := mul_nonneg (pow_nonneg hA e) hE0
    linarith

/-- **Young's inequality in the cubic form** `K u³ ≤ α u² + (K²/4α) u⁴`, which is the
identity `4α(α u² + (K²/4α) u⁴ - K u³) = (2αu - K u²)²`.  This is the paper's "by Young's
inequality, `C‖E‖₂‖E‖₄² ≤ o(1)‖E‖₂² + Cε⁴`", in a pointwise form that needs neither a square
root nor Cauchy–Schwarz. -/
private theorem cube_absorption {K α u : ℝ} (hα : 0 < α) :
    K * u ^ 3 ≤ α * u ^ 2 + K ^ 2 / (4 * α) * u ^ 4 := by
  have h4 : (0:ℝ) < 4 * α := by linarith
  have hc : K ^ 2 / (4 * α) * (4 * α) = K ^ 2 := div_mul_cancel₀ _ (ne_of_gt h4)
  have hexp : (α * u ^ 2 + K ^ 2 / (4 * α) * u ^ 4 - K * u ^ 3) * (4 * α)
      = (2 * α * u - K * u ^ 2) ^ 2 + (K ^ 2 / (4 * α) * (4 * α) - K ^ 2) * u ^ 4 := by
    ring
  rw [hc] at hexp
  have hnn : 0 ≤ (α * u ^ 2 + K ^ 2 / (4 * α) * u ^ 4 - K * u ^ 3) * (4 * α) := by
    rw [hexp]
    nlinarith [sq_nonneg (2 * α * u - K * u ^ 2)]
  nlinarith [hnn, h4]

/-- **The tangent line below `x ↦ x^{v/2}` at the base point `q²`.**  This is Bernoulli's
inequality for real exponents applied to `1 + s = X/q²`, and it replaces the two-sided Taylor
expansion of the last paragraph of the proof of `lem:localization-rank-one`: because
`x ↦ x^{v/2}` is convex for `v ≥ 2`, the tangent line is a genuine lower bound and there is no
`O(ε⁴)` remainder to control. -/
private theorem pow_half_tangent {X q : ℝ} (hX : 0 ≤ X) (hq : 0 < q) {v : ℕ} (hv : 2 ≤ v) :
    q ^ v + (v : ℝ) / 2 * q ^ (v - 2) * (X - q ^ 2) ≤ X ^ ((v : ℝ) / 2) := by
  have hqne : q ≠ 0 := ne_of_gt hq
  have hvR : (2:ℝ) ≤ (v : ℝ) := by exact_mod_cast hv
  have ha : (1:ℝ) ≤ (v : ℝ) / 2 := by linarith
  have hq2 : (0:ℝ) < q ^ 2 := by positivity
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = X / q ^ 2 - 1 := ⟨_, rfl⟩
  have hs1 : (-1:ℝ) ≤ s := by
    have : (0:ℝ) ≤ X / q ^ 2 := div_nonneg hX hq2.le
    rw [hs]; linarith
  have h1s : 1 + s = X / q ^ 2 := by rw [hs]; ring
  have hbern := one_add_mul_self_le_rpow_one_add hs1 ha
  have hqv : (q ^ 2) ^ ((v : ℝ) / 2) = q ^ v := by
    rw [show (q : ℝ) ^ (2:ℕ) = q ^ ((2:ℕ) : ℝ) from (Real.rpow_natCast q 2).symm,
      ← Real.rpow_mul hq.le,
      show ((2:ℕ) : ℝ) * ((v : ℝ) / 2) = ((v : ℕ) : ℝ) by push_cast; ring]
    exact Real.rpow_natCast q v
  have hcancel : X / q ^ 2 * q ^ 2 = X := by field_simp
  have hXsplit : X ^ ((v : ℝ) / 2) = (X / q ^ 2) ^ ((v : ℝ) / 2) * q ^ v := by
    rw [← hqv, ← Real.mul_rpow (div_nonneg hX hq2.le) hq2.le, hcancel]
  have hmul : (1 + (v : ℝ) / 2 * s) * q ^ v ≤ (1 + s) ^ ((v : ℝ) / 2) * q ^ v :=
    mul_le_mul_of_nonneg_right hbern (by positivity)
  rw [h1s, ← hXsplit] at hmul
  have hpow : q ^ v = q ^ (v - 2) * q ^ 2 := by
    rw [← pow_add]
    congr 1
    omega
  have hid : (1 + (v : ℝ) / 2 * s) * q ^ v
      = q ^ v + (v : ℝ) / 2 * q ^ (v - 2) * (X - q ^ 2) := by
    rw [hs, hpow]
    field_simp
  linarith [hid ▸ hmul]

/-! ## The quartic defect of `W` and the constants of the estimates -/

/-- The **quartic defect** `ε⁴ = ‖W - r_*‖₄⁴ = ∫∫ (W - r_*)⁴`, the right-hand quantity of
`eq:moment-and-cost-gap-bounds`. -/
noncomputable def defectQuart (d : ℕ) (W : Graphon) : ℝ :=
  ∫ z, (W.toFun z.1 z.2 - rStar d) ^ 4 ∂gμ

/-- The quartic defect is nonnegative. -/
theorem defectQuart_nonneg (d : ℕ) (W : Graphon) : 0 ≤ defectQuart d W :=
  integral_nonneg fun z => by positivity

/-- The **coercivity constant** `(r_*/2)^{d-2}`: the lower bound for `A^{d-2}` on the good
set `A ≥ r_*/2` of the proof of `lem:localization-rank-one`. -/
noncomputable def coerConst (d : ℕ) : ℝ := (rStar d / 2) ^ (d - 2)

/-- The **tail constant** `2^d · 20^{d-2}`: a crude uniform bound for
`∑_{k < d-2} binom(d,k) · 4^k · 5^{d-k-3}`, the coefficient with which `∫|E|³` dominates the
cubic-and-higher part of `eq:rank-one-reduction-bounds`. -/
noncomputable def tailConst (d : ℕ) : ℝ := 2 ^ d * 20 ^ (d - 2)

/-- The constant multiplying `‖E‖₄⁴` after Young's inequality has absorbed the tail. -/
noncomputable def tailQuartConst (d : ℕ) : ℝ := tailConst d ^ 2 / coerConst d

/-- The full `ε⁴`-constant of `eq:moment-and-cost-gap-bounds`, in terms of the two closeness
constants `C₁` (for `‖A - r_*‖₄⁴`) and `C₂` (for `‖E‖₄⁴`) of
`eq:rank-one-reduction-bounds`. -/
noncomputable def quartConst (d : ℕ) (C₁ C₂ : ℝ) : ℝ :=
  (d.choose (d - 2) : ℝ) * (400 / rStar d ^ 4) * C₁ + tailQuartConst d * C₂

/-- The constant `c` of the combined stability inequality `holder_stability`, for a lower
bound `q₀` on the rank-one moment `q`. -/
noncomputable def stabCoer (d v : ℕ) (q₀ : ℝ) : ℝ :=
  (v : ℝ) / 2 * q₀ ^ (v - 2) * (3 / 4 * coerConst d)

/-- The constant `C` of the combined stability inequality `holder_stability` multiplying
`‖W - r_*‖₄⁴`. -/
noncomputable def stabQuart (d v : ℕ) (C₁ C₂ : ℝ) : ℝ :=
  (v : ℝ) / 2 * ((2 : ℝ) ^ d) ^ (v - 2) * quartConst d C₁ C₂

/-- The coercivity constant is positive. -/
theorem coerConst_pos (hd : 2 ≤ d) : 0 < coerConst d :=
  pow_pos (by linarith [rStar_pos hd]) _

/-- The tail constant is positive. -/
theorem tailConst_pos (d : ℕ) : 0 < tailConst d := by
  unfold tailConst; positivity

/-- The Young constant for `‖E‖₄⁴` is nonnegative. -/
theorem tailQuartConst_nonneg (hd : 2 ≤ d) : 0 ≤ tailQuartConst d :=
  div_nonneg (by positivity) (coerConst_pos hd).le

/-- The `ε⁴`-constant of `eq:moment-and-cost-gap-bounds` is nonnegative. -/
theorem quartConst_nonneg (hd : 2 ≤ d) {C₁ C₂ : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) :
    0 ≤ quartConst d C₁ C₂ := by
  have hrp : (0:ℝ) < rStar d := rStar_pos hd
  have h1 : (0:ℝ) ≤ (d.choose (d - 2) : ℝ) * (400 / rStar d ^ 4) :=
    mul_nonneg (Nat.cast_nonneg _) (div_nonneg (by norm_num) (pow_pos hrp 4).le)
  exact add_nonneg (mul_nonneg h1 hC₁) (mul_nonneg (tailQuartConst_nonneg hd) hC₂)

/-- The constant `c` of the combined stability inequality is positive. -/
theorem stabCoer_pos (hd : 2 ≤ d) {v : ℕ} (hv : 2 ≤ v) {q₀ : ℝ} (hq₀ : 0 < q₀) :
    0 < stabCoer d v q₀ := by
  have hvR : (0:ℝ) < (v : ℝ) := by
    have : 0 < v := by omega
    exact_mod_cast this
  have hc : (0:ℝ) < coerConst d := coerConst_pos hd
  unfold stabCoer
  have h1 : (0:ℝ) < (v : ℝ) / 2 * q₀ ^ (v - 2) := by positivity
  nlinarith

/-- The constant `C` of the combined stability inequality is nonnegative. -/
theorem stabQuart_nonneg (hd : 2 ≤ d) {v : ℕ} {C₁ C₂ : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) :
    0 ≤ stabQuart d v C₁ C₂ := by
  unfold stabQuart
  exact mul_nonneg (by positivity) (quartConst_nonneg hd hC₁ hC₂)

namespace FactorDecomp

variable (P : FactorDecomp d W)

/-! ## The norms of the residual -/

/-- `‖E‖₂² = ∫∫ E²`. -/
noncomputable def residSq : ℝ := ∫ z, P.resid z.1 z.2 ^ 2 ∂gμ

/-- `∫∫ |E|³`, the quantity that dominates the cubic-and-higher tail of
`eq:rank-one-reduction-bounds`. -/
noncomputable def residCube : ℝ := ∫ z, |P.resid z.1 z.2| ^ 3 ∂gμ

/-- `‖E‖₄⁴ = ∫∫ E⁴`. -/
noncomputable def residQuart : ℝ := ∫ z, P.resid z.1 z.2 ^ 4 ∂gμ

/-- `‖A - r_*‖₄⁴ = ∫∫ (A - r_*)⁴` for the rank-one part `A = f ⊗ f`. -/
noncomputable def rankOneQuart : ℝ := ∫ z, (P.rankOne z.1 z.2 - rStar d) ^ 4 ∂gμ

/-- `‖E‖₂`, the quantity in which `eq:moment-and-cost-gap-bounds` is stated. -/
noncomputable def residNorm : ℝ := Real.sqrt P.residSq

/-! ### Integrability -/

/-- `E²` is integrable. -/
theorem integrable_resid_sq : Integrable (fun z : ℝ × ℝ => P.resid z.1 z.2 ^ 2) gμ := by
  simpa using P.integrable_rankOne_pow_mul_resid_pow 0 2

/-- `E⁴` is integrable. -/
theorem integrable_resid_quart : Integrable (fun z : ℝ × ℝ => P.resid z.1 z.2 ^ 4) gμ := by
  simpa using P.integrable_rankOne_pow_mul_resid_pow 0 4

/-- `|E|³` is integrable. -/
theorem integrable_resid_cube : Integrable (fun z : ℝ × ℝ => |P.resid z.1 z.2| ^ 3) gμ :=
  integrable_of_abs_le (P.measurable_resid.abs.pow_const 3) 125 fun z => by
    rw [abs_of_nonneg (pow_nonneg (abs_nonneg _) 3)]
    calc |P.resid z.1 z.2| ^ 3 ≤ (5:ℝ) ^ 3 :=
          pow_le_pow_left₀ (abs_nonneg _) (P.abs_resid_le z.1 z.2) 3
      _ = 125 := by norm_num

/-- `(A - r_*)⁴` is integrable. -/
theorem integrable_rankOne_quart :
    Integrable (fun z : ℝ × ℝ => (P.rankOne z.1 z.2 - rStar d) ^ 4) gμ :=
  integrable_of_abs_le ((P.measurable_rankOne.sub measurable_const).pow_const 4)
    ((4 + |rStar d|) ^ 4) fun z => by
      rw [abs_pow]
      refine pow_le_pow_left₀ (abs_nonneg _) ?_ 4
      calc |P.rankOne z.1 z.2 - rStar d| ≤ |P.rankOne z.1 z.2| + |rStar d| := abs_sub _ _
        _ ≤ 4 + |rStar d| := by linarith [P.abs_rankOne_le z.1 z.2]

/-! ### Nonnegativity and elementary identities -/

/-- `‖E‖₂² ≥ 0`. -/
theorem residSq_nonneg : 0 ≤ P.residSq := integral_nonneg fun _ => sq_nonneg _

/-- `∫∫|E|³ ≥ 0`. -/
theorem residCube_nonneg : 0 ≤ P.residCube :=
  integral_nonneg fun _ => pow_nonneg (abs_nonneg _) 3

/-- `‖E‖₂² = (‖E‖₂)²`. -/
theorem residNorm_sq : P.residNorm ^ 2 = P.residSq := Real.sq_sqrt P.residSq_nonneg

/-- `‖E‖₂ ≥ 0`. -/
theorem residNorm_nonneg : 0 ≤ P.residNorm := Real.sqrt_nonneg _

/-- `q = ∫ f^d ≥ 0`, since `f ≥ 0`. -/
theorem qVal_nonneg : 0 ≤ P.qVal := integral_nonneg fun x => pow_nonneg (P.f_nonneg x) d

/-- `q = ∫ f^d ≤ 2^d`, from the normalisation `f ≤ 2` of `FactorDecomp`. -/
theorem qVal_le : P.qVal ≤ 2 ^ d := by
  have h : P.qVal ≤ ∫ _ : ℝ, (2:ℝ) ^ d ∂unitμ :=
    integral_mono (P.integrable_f_pow d) (integrable_const _) fun x =>
      pow_le_pow_left₀ (P.f_nonneg x) (P.f_bdd x) d
  simpa using h

/-! ## Coercivity of the quadratic term -/

/-- **Coercivity of the quadratic term of `eq:rank-one-reduction-bounds`**:

`∫∫ A^{d-2} E² ≥ (r_*/2)^{d-2} ‖E‖₂² - (400/r_*⁴) ‖A - r_*‖₄⁴`.

This is the paper's Chebyshev split — "on the set where `A ≥ r_*/2` the quadratic coefficient
is bounded below by a positive constant; the complement has measure `O(ε⁴)`" — carried out
pointwise rather than by splitting the domain: on the bad set `A < r_*/2` the quartic defect
`(A - r_*)⁴` already exceeds `(r_*/2)⁴`, which pays for `θ^{d-2}E² ≤ 25`.  No closeness
hypothesis is needed here; the closeness of `A` to `r_*` enters only when `‖A - r_*‖₄⁴` is
compared with `ε⁴`. -/
theorem coercive_quadratic (hd : 2 ≤ d) :
    coerConst d * P.residSq - 400 / rStar d ^ 4 * P.rankOneQuart
      ≤ ∫ z, P.rankOne z.1 z.2 ^ (d - 2) * P.resid z.1 z.2 ^ 2 ∂gμ := by
  have hr0 : (0:ℝ) < rStar d := rStar_pos hd
  have hr1 : rStar d < 1 := rStar_lt_one hd
  have hθ0 : (0:ℝ) < rStar d / 2 := by linarith
  have hθ1 : rStar d / 2 ≤ 1 := by linarith
  have hpt : ∀ z : ℝ × ℝ,
      (rStar d / 2) ^ (d - 2) * P.resid z.1 z.2 ^ 2
          - 25 / (rStar d / 2) ^ 4 * (P.rankOne z.1 z.2 - rStar d) ^ 4
        ≤ P.rankOne z.1 z.2 ^ (d - 2) * P.resid z.1 z.2 ^ 2 := by
    intro z
    have hE : P.resid z.1 z.2 ^ 2 ≤ 25 := by
      calc P.resid z.1 z.2 ^ 2 = |P.resid z.1 z.2| ^ 2 := (sq_abs _).symm
        _ ≤ 5 ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (P.abs_resid_le z.1 z.2) 2
        _ = 25 := by norm_num
    have h := pointwise_coercive hθ0 hθ1 (P.rankOne_nonneg z.1 z.2) hE (d - 2)
    rwa [show 2 * (rStar d / 2) = rStar d by ring] at h
  have hi1 : Integrable (fun z : ℝ × ℝ =>
      (rStar d / 2) ^ (d - 2) * P.resid z.1 z.2 ^ 2
        - 25 / (rStar d / 2) ^ 4 * (P.rankOne z.1 z.2 - rStar d) ^ 4) gμ :=
    (P.integrable_resid_sq.const_mul _).sub (P.integrable_rankOne_quart.const_mul _)
  have hmono := integral_mono hi1 (P.integrable_rankOne_pow_mul_resid_pow (d - 2) 2) hpt
  rw [integral_sub (P.integrable_resid_sq.const_mul _)
      (P.integrable_rankOne_quart.const_mul _),
    integral_const_mul, integral_const_mul] at hmono
  have hconv : (25:ℝ) / (rStar d / 2) ^ 4 = 400 / rStar d ^ 4 := by
    rw [show (rStar d / 2) ^ 4 = rStar d ^ 4 / 16 by ring, div_div_eq_mul_div]
    norm_num
  simp only [coerConst, residSq, rankOneQuart]
  rw [← hconv]
  exact hmono

/-! ## The cubic-and-higher tail -/

/-- **The tail of `eq:rank-one-reduction-bounds` is `O(∫|E|³)`.**  Every term with `k < d-2` has
`E`-degree `d - k ≥ 3`; bounding `|A| ≤ 4`, `|E| ≤ 5` and pulling out three factors of `|E|`
gives `|∫∫ A^k E^{d-k}| ≤ 20^{d-2} ∫∫|E|³`, and `∑_{k ≤ d} binom(d,k) = 2^d`. -/
theorem abs_tail_le (hd : 2 ≤ d) :
    |∑ k ∈ Finset.range (d - 2), (d.choose k : ℝ) *
        ∫ z, P.rankOne z.1 z.2 ^ k * P.resid z.1 z.2 ^ (d - k) ∂gμ|
      ≤ tailConst d * P.residCube := by
  have hcube0 : 0 ≤ P.residCube := P.residCube_nonneg
  have hinner : ∀ k ∈ Finset.range (d - 2),
      |(d.choose k : ℝ) * ∫ z, P.rankOne z.1 z.2 ^ k * P.resid z.1 z.2 ^ (d - k) ∂gμ|
        ≤ (d.choose k : ℝ) * ((20:ℝ) ^ (d - 2) * P.residCube) := by
    intro k hk
    have hk' : k < d - 2 := Finset.mem_range.mp hk
    obtain ⟨j, hj⟩ : ∃ j, d - k = j + 3 := ⟨d - k - 3, by omega⟩
    have hjd : j ≤ d - 2 := by omega
    have hkd : k ≤ d - 2 := by omega
    have hpt : ∀ z : ℝ × ℝ, |P.rankOne z.1 z.2 ^ k * P.resid z.1 z.2 ^ (d - k)|
        ≤ (20:ℝ) ^ (d - 2) * |P.resid z.1 z.2| ^ 3 := by
      intro z
      rw [abs_mul, abs_pow, abs_pow, hj, pow_add]
      have e1 : |P.rankOne z.1 z.2| ^ k ≤ (4:ℝ) ^ (d - 2) :=
        le_trans (pow_le_pow_left₀ (abs_nonneg _) (P.abs_rankOne_le z.1 z.2) k)
          (pow_le_pow_right₀ (by norm_num) hkd)
      have e2 : |P.resid z.1 z.2| ^ j ≤ (5:ℝ) ^ (d - 2) :=
        le_trans (pow_le_pow_left₀ (abs_nonneg _) (P.abs_resid_le z.1 z.2) j)
          (pow_le_pow_right₀ (by norm_num) hjd)
      have e3 : (0:ℝ) ≤ |P.resid z.1 z.2| ^ 3 := pow_nonneg (abs_nonneg _) 3
      calc |P.rankOne z.1 z.2| ^ k * (|P.resid z.1 z.2| ^ j * |P.resid z.1 z.2| ^ 3)
          ≤ (4:ℝ) ^ (d - 2) * ((5:ℝ) ^ (d - 2) * |P.resid z.1 z.2| ^ 3) :=
            mul_le_mul e1 (mul_le_mul_of_nonneg_right e2 e3)
              (mul_nonneg (pow_nonneg (abs_nonneg _) j) e3) (by positivity)
        _ = (20:ℝ) ^ (d - 2) * |P.resid z.1 z.2| ^ 3 := by
            rw [show (20:ℝ) = 4 * 5 by norm_num, mul_pow]
            ring
    have hI : |∫ z, P.rankOne z.1 z.2 ^ k * P.resid z.1 z.2 ^ (d - k) ∂gμ|
        ≤ (20:ℝ) ^ (d - 2) * P.residCube := by
      calc |∫ z, P.rankOne z.1 z.2 ^ k * P.resid z.1 z.2 ^ (d - k) ∂gμ|
          ≤ ∫ z, |P.rankOne z.1 z.2 ^ k * P.resid z.1 z.2 ^ (d - k)| ∂gμ :=
            abs_integral_le_integral_abs
        _ ≤ ∫ z, (20:ℝ) ^ (d - 2) * |P.resid z.1 z.2| ^ 3 ∂gμ :=
            integral_mono (P.integrable_rankOne_pow_mul_resid_pow k (d - k)).abs
              (P.integrable_resid_cube.const_mul _) hpt
        _ = (20:ℝ) ^ (d - 2) * P.residCube := by rw [integral_const_mul]; rfl
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg (d.choose k) : (0:ℝ) ≤ _)]
    exact mul_le_mul_of_nonneg_left hI (Nat.cast_nonneg _)
  have hbin : (∑ k ∈ Finset.range (d - 2), (d.choose k : ℝ)) ≤ 2 ^ d := by
    have hsub : Finset.range (d - 2) ⊆ Finset.range (d + 1) := by
      intro x hx
      simp only [Finset.mem_range] at hx ⊢
      omega
    have h1 : (∑ k ∈ Finset.range (d - 2), (d.choose k : ℝ))
        ≤ ∑ k ∈ Finset.range (d + 1), (d.choose k : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub fun i _ _ => Nat.cast_nonneg _
    have h2 : (∑ k ∈ Finset.range (d + 1), (d.choose k : ℝ)) = 2 ^ d := by
      exact_mod_cast Nat.sum_range_choose d
    linarith
  calc |∑ k ∈ Finset.range (d - 2), (d.choose k : ℝ) *
        ∫ z, P.rankOne z.1 z.2 ^ k * P.resid z.1 z.2 ^ (d - k) ∂gμ|
      ≤ ∑ k ∈ Finset.range (d - 2), |(d.choose k : ℝ) *
          ∫ z, P.rankOne z.1 z.2 ^ k * P.resid z.1 z.2 ^ (d - k) ∂gμ| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range (d - 2), (d.choose k : ℝ) * ((20:ℝ) ^ (d - 2) * P.residCube) :=
        Finset.sum_le_sum hinner
    _ = (∑ k ∈ Finset.range (d - 2), (d.choose k : ℝ)) * ((20:ℝ) ^ (d - 2) * P.residCube) := by
        rw [Finset.sum_mul]
    _ ≤ (2:ℝ) ^ d * ((20:ℝ) ^ (d - 2) * P.residCube) :=
        mul_le_mul_of_nonneg_right hbin (mul_nonneg (by positivity) hcube0)
    _ = tailConst d * P.residCube := by unfold tailConst; ring

/-- **Young absorption of the tail.**  The `∫∫|E|³` bound of `abs_tail_le` is traded, by
`cube_absorption`, for a quarter of the coercive term plus a multiple of `‖E‖₄⁴`. -/
theorem tail_absorption (hd : 2 ≤ d) :
    tailConst d * P.residCube
      ≤ coerConst d / 4 * P.residSq + tailQuartConst d * P.residQuart := by
  have hc : (0:ℝ) < coerConst d := coerConst_pos hd
  have hα : (0:ℝ) < coerConst d / 4 := by linarith
  have hpt : ∀ z : ℝ × ℝ, tailConst d * |P.resid z.1 z.2| ^ 3
      ≤ coerConst d / 4 * P.resid z.1 z.2 ^ 2 + tailQuartConst d * P.resid z.1 z.2 ^ 4 := by
    intro z
    have hy := cube_absorption (K := tailConst d) (α := coerConst d / 4)
      (u := |P.resid z.1 z.2|) hα
    rw [show 4 * (coerConst d / 4) = coerConst d by ring, sq_abs, Even.pow_abs (n := 4) (by norm_num)] at hy
    exact hy
  have hi1 : Integrable (fun z : ℝ × ℝ => tailConst d * |P.resid z.1 z.2| ^ 3) gμ :=
    P.integrable_resid_cube.const_mul _
  have hi2 : Integrable (fun z : ℝ × ℝ =>
      coerConst d / 4 * P.resid z.1 z.2 ^ 2 + tailQuartConst d * P.resid z.1 z.2 ^ 4) gμ :=
    (P.integrable_resid_sq.const_mul _).add (P.integrable_resid_quart.const_mul _)
  have hmono := integral_mono hi1 hi2 hpt
  rw [integral_const_mul, integral_add (P.integrable_resid_sq.const_mul _)
      (P.integrable_resid_quart.const_mul _), integral_const_mul, integral_const_mul] at hmono
  exact hmono

/-! ## `eq:moment-and-cost-gap-bounds` -/

/-- **`eq:moment-and-cost-gap-bounds`**:

`∫ W^d - q² ≥ (3/4)(r_*/2)^{d-2}‖E‖₂² - binom(d,2)(400/r_*⁴)‖A - r_*‖₄⁴
              - tailQuartConst · ‖E‖₄⁴`.

The exact expansion `eq:rank-one-reduction-bounds` is peeled at `k = d-2`; the leading piece is
handled by `coercive_quadratic` and the rest by `abs_tail_le` and `tail_absorption`, which eat a
quarter of the coercive constant. -/
theorem Wmoment_sub_qsq_ge (hd : 2 ≤ d) :
    3 / 4 * coerConst d * P.residSq
        - (d.choose (d - 2) : ℝ) * (400 / rStar d ^ 4) * P.rankOneQuart
        - tailQuartConst d * P.residQuart
      ≤ W.Wmoment d - P.qVal ^ 2 := by
  have hexp := P.Wmoment_eq (by omega : 1 ≤ d)
  rw [show d - 1 = (d - 2) + 1 by omega, Finset.sum_range_succ,
    show d - (d - 2) = 2 by omega] at hexp
  have hb1 : (1:ℝ) ≤ (d.choose (d - 2) : ℝ) := by
    have h : 1 ≤ d.choose (d - 2) := Nat.choose_pos (by omega)
    exact_mod_cast h
  have hb0 : (0:ℝ) ≤ (d.choose (d - 2) : ℝ) := Nat.cast_nonneg _
  have hS0 : 0 ≤ P.residSq := P.residSq_nonneg
  have hc0 : (0:ℝ) ≤ coerConst d := (coerConst_pos hd).le
  have h1 : (d.choose (d - 2) : ℝ) *
        (coerConst d * P.residSq - 400 / rStar d ^ 4 * P.rankOneQuart)
      ≤ (d.choose (d - 2) : ℝ) *
        ∫ z, P.rankOne z.1 z.2 ^ (d - 2) * P.resid z.1 z.2 ^ 2 ∂gμ :=
    mul_le_mul_of_nonneg_left (P.coercive_quadratic hd) hb0
  have h2 : coerConst d * P.residSq ≤ (d.choose (d - 2) : ℝ) * (coerConst d * P.residSq) :=
    le_mul_of_one_le_left (mul_nonneg hc0 hS0) hb1
  have h3 := (abs_le.mp (P.abs_tail_le hd)).1
  have h4 := P.tail_absorption hd
  linarith

/-! ## The combined stability inequality -/

/-- **The combined stability inequality**, with
explicit constants: `eq:moment-and-cost-gap-bounds` fed through the tangent line at `q²` and joined
with the density-error hypothesis.

`T` stands for the homomorphism density `t(H,W)`; the hypothesis `hT` is precisely chunk
(III), `eq:rank-one-reduction-bounds`, which is *not* proved here.  The graph `H`
enters only through `v = |V(H)|`, `m = |E(H)|` and the `d`-regular handshake `2m = vd`
(`hvm`).  The hypotheses `hA4`, `hE4` and `hq` transcribe `eq:rank-one-reduction-bounds`
and the paper's "`q` stays bounded away from zero"; see the module docstring. -/
theorem holder_stability (hd : 2 ≤ d) {v m : ℕ} (hv : 2 ≤ v) (hvm : 2 * m = v * d)
    {C₁ C₂ C₃ q₀ T : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hq₀ : 0 < q₀) (hq : q₀ ≤ P.qVal)
    (hA4 : P.rankOneQuart ≤ C₁ * defectQuart d W)
    (hE4 : P.residQuart ≤ C₂ * defectQuart d W)
    (hT : |T - P.qVal ^ v| ≤ C₃ * P.residNorm ^ 3) :
    stabCoer d v q₀ * P.residNorm ^ 2 - stabQuart d v C₁ C₂ * defectQuart d W
        - C₃ * P.residNorm ^ 3
      ≤ W.Wmoment d ^ ((m : ℝ) / (d : ℝ)) - T := by
  have hrp : (0:ℝ) < rStar d := rStar_pos hd
  have hdne : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hD0 : (0:ℝ) ≤ defectQuart d W := defectQuart_nonneg d W
  have hS0 : (0:ℝ) ≤ P.residSq := P.residSq_nonneg
  have hq0 : (0:ℝ) < P.qVal := lt_of_lt_of_le hq₀ hq
  have hCq0 : (0:ℝ) ≤ quartConst d C₁ C₂ := quartConst_nonneg hd hC₁ hC₂
  have hcCo0 : (0:ℝ) ≤ 3 / 4 * coerConst d := by linarith [(coerConst_pos hd).le]
  -- the exponent `m/d` is `v/2`
  have hexp : (m : ℝ) / (d : ℝ) = (v : ℝ) / 2 := by
    have h : 2 * (m : ℝ) = (v : ℝ) * (d : ℝ) := by exact_mod_cast hvm
    field_simp
    linarith
  -- (56) with the closeness hypotheses inserted
  have hstep1 : 3 / 4 * coerConst d * P.residSq - quartConst d C₁ C₂ * defectQuart d W
      ≤ W.Wmoment d - P.qVal ^ 2 := by
    have h := P.Wmoment_sub_qsq_ge hd
    have hK0 : (0:ℝ) ≤ (d.choose (d - 2) : ℝ) * (400 / rStar d ^ 4) :=
      mul_nonneg (Nat.cast_nonneg _) (div_nonneg (by norm_num) (pow_pos hrp 4).le)
    have e1 : (d.choose (d - 2) : ℝ) * (400 / rStar d ^ 4) * P.rankOneQuart
        ≤ (d.choose (d - 2) : ℝ) * (400 / rStar d ^ 4) * (C₁ * defectQuart d W) :=
      mul_le_mul_of_nonneg_left hA4 hK0
    have e2 : tailQuartConst d * P.residQuart ≤ tailQuartConst d * (C₂ * defectQuart d W) :=
      mul_le_mul_of_nonneg_left hE4 (tailQuartConst_nonneg hd)
    simp only [quartConst]
    linarith
  -- the tangent line at the base point `q²`
  have hM0 : (0:ℝ) ≤ W.Wmoment d :=
    integral_nonneg fun z => pow_nonneg (W.nonneg' z.1 z.2) d
  have hbern : P.qVal ^ v + (v : ℝ) / 2 * P.qVal ^ (v - 2) * (W.Wmoment d - P.qVal ^ 2)
      ≤ W.Wmoment d ^ ((v : ℝ) / 2) :=
    pow_half_tangent hM0 hq0 hv
  -- the slope is bounded above and below
  have hhalf : (0:ℝ) ≤ (v : ℝ) / 2 := by positivity
  have hLnn : (0:ℝ) ≤ (v : ℝ) / 2 * P.qVal ^ (v - 2) :=
    mul_nonneg hhalf (pow_nonneg P.qVal_nonneg _)
  have hL0 : (v : ℝ) / 2 * q₀ ^ (v - 2) ≤ (v : ℝ) / 2 * P.qVal ^ (v - 2) :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hq₀.le hq _) hhalf
  have hL1 : (v : ℝ) / 2 * P.qVal ^ (v - 2) ≤ (v : ℝ) / 2 * ((2:ℝ) ^ d) ^ (v - 2) :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ P.qVal_nonneg P.qVal_le _) hhalf
  have h5 : (v : ℝ) / 2 * P.qVal ^ (v - 2) *
        (3 / 4 * coerConst d * P.residSq - quartConst d C₁ C₂ * defectQuart d W)
      ≤ (v : ℝ) / 2 * P.qVal ^ (v - 2) * (W.Wmoment d - P.qVal ^ 2) :=
    mul_le_mul_of_nonneg_left hstep1 hLnn
  have h5a : (v : ℝ) / 2 * q₀ ^ (v - 2) * (3 / 4 * coerConst d * P.residSq)
      ≤ (v : ℝ) / 2 * P.qVal ^ (v - 2) * (3 / 4 * coerConst d * P.residSq) :=
    mul_le_mul_of_nonneg_right hL0 (mul_nonneg hcCo0 hS0)
  have h5b : (v : ℝ) / 2 * P.qVal ^ (v - 2) * (quartConst d C₁ C₂ * defectQuart d W)
      ≤ (v : ℝ) / 2 * ((2:ℝ) ^ d) ^ (v - 2) * (quartConst d C₁ C₂ * defectQuart d W) :=
    mul_le_mul_of_nonneg_right hL1 (mul_nonneg hCq0 hD0)
  have hT' : T ≤ P.qVal ^ v + C₃ * P.residNorm ^ 3 := by
    have := (abs_le.mp hT).2
    linarith
  rw [hexp, P.residNorm_sq]
  simp only [stabCoer, stabQuart]
  linarith

end FactorDecomp

/-- **The combined stability inequality in `∃ c, C > 0` shape** (the shape of the
`lem:localization-rank-one`; the lemma states
`eq:moment-and-cost-gap-bounds` and `eq:rank-one-reduction-bounds` separately):
there are `c, C > 0`, depending only on `d`, on `H` (through `v`, `m`) and on the closeness
constants, such that every graphon carrying a Factor decomposition with the stated closeness
obeys

`(∫ W^d)^{m/d} - t(H,W) ≥ c‖E‖₂² - C‖W - r_*‖₄⁴ - C₃‖E‖₂³`.

As in `FactorDecomp.holder_stability`, `T` stands for `t(H,W)` and its hypothesis is chunk
(III), `eq:rank-one-reduction-bounds`, which is not proved here but in
`SingularEndpoint/FactorHDensity.lean`. -/
theorem exists_holder_stability (hd : 2 ≤ d) {v m : ℕ} (hv : 2 ≤ v) (hvm : 2 * m = v * d)
    {C₁ C₂ C₃ q₀ : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hq₀ : 0 < q₀) :
    ∃ c > 0, ∃ C ≥ 0, ∀ (W' : Graphon) (P : FactorDecomp d W'), q₀ ≤ P.qVal →
      P.rankOneQuart ≤ C₁ * defectQuart d W' → P.residQuart ≤ C₂ * defectQuart d W' →
      ∀ T : ℝ, |T - P.qVal ^ v| ≤ C₃ * P.residNorm ^ 3 →
        c * P.residNorm ^ 2 - C * defectQuart d W' - C₃ * P.residNorm ^ 3
          ≤ W'.Wmoment d ^ ((m : ℝ) / (d : ℝ)) - T :=
  ⟨stabCoer d v q₀, stabCoer_pos hd hv hq₀, stabQuart d v C₁ C₂,
    stabQuart_nonneg hd hC₁ hC₂,
    fun _ P hq hA4 hE4 _ hT => P.holder_stability hd hv hvm hC₁ hC₂ hq₀ hq hA4 hE4 hT⟩

end SingularEndpoint

end UpperTailOptimizers
