import UpperTailOptimizers.SingularEndpoint.FactorFix
import UpperTailOptimizers.SingularEndpoint.FactorSolution
import UpperTailOptimizers.SingularEndpoint.FactorHDensity

/-!
# `lem:localization-rank-one`, assembled (Section 7)

This file closes the last gap of `lem:localization-rank-one` of `paper/singular_endpoint.tex`
and assembles the four chunks into one statement.

## The gap

`SingularEndpoint/FactorSolution.lean` proves the pointwise bound, the orthogonality relation and the
closeness estimate for *any* solution of the nonlinear Factor equation, but seven of its
statements carry the hypothesis `hqlow : 1/2^d ≤ q`.  That hypothesis is unavoidable at that
level of generality — for the constant graphon `W ≡ c` the constant `f ≡ √c` solves the whole
Factor equation with `q = c^{d/2}` arbitrarily small — and it is what this file discharges,
along the family, from the smallness of `ε = ‖W - r_*‖₄`.

## The route

Let `φ` be the unit-mass contraction fixed point of `exists_contraction_fixedPoint`, `κ = contractionDen W d φ`
its denominator, `I = ∫φ^d`, and `s = √(κ/I)` the scale of `factorFix_rescale`, so that the
produced solution is `f = sφ` with `q = s^{d-2}κ = s^d·I`.

1. `contractionMap_closeness` applies to `φ` **itself** (`φ = N(φ)`), giving `‖φ - 1‖₄ ≤ C_close·ε`
   with no hypothesis on `q`: this is what makes the route non-circular
   (`factorMain_fixedPoint_Lnorm_le`).
2. Hence `|I - 1| ≤ d·M^{d-1}‖φ - 1‖₄` — `factorSolution_abs_integral_sub_pow_le` at `b = 1`,
   which needs only measurability and the bounds (`factorMain_abs_integral_pow_sub_one_le`).
3. `κ = r_*∫φ^{d-1} + ∫T_U(φ^{d-1})`, so `κ ≥ r_* - (d-1)M^{d-2}‖φ - 1‖₄ - εM^{d-1}`
   (`factorMain_den_lower`).
4. Therefore `I ≤ 4κ` below a threshold `ε₂(d)` (`factorMain_integral_pow_le_four_mul_den`),
   whence `s ≥ 1/2` and `q = s^d·I ≥ 2^{-d}` because `I ≥ 1` (Jensen).

**Crude bounds do not suffice**, which is the whole point of step 1: with only `κ ≥ r_*/2` and
`I ≤ M^{d-1}` one gets `s ≥ 2^{-d}` and hence `q ≳ 2^{-d²}`, far short of `2^{-d}`.  What is
used is that `I → 1` and `κ → r_* ≥ 1/2` as `ε → 0`; the target `1/4` for `κ/I` is then met
with a factor-of-two margin, and `2^{-d}` is met with the margin `r_*^{d/2} ≥ 2^{-d/2}`.

## Paper results realised

* `eq:rank-one-orthogonality` — through `exists_factorDecomp` (the `FactorDecomp.factor_eq`
  of the produced term);
* `eq:rank-one-orthogonality` — both halves: the orthogonality relation (the `ortho`
  field) and the pointwise clause `f ≤ q^{-1/d}` of `exists_factorDecomp`;
* `eq:rank-one-reduction-bounds` — the clause `‖f - u_*‖₄ + ‖E‖₄ ≤ Cε`;
* `eq:moment-and-cost-gap-bounds` and `eq:rank-one-reduction-bounds` — quoted, in the
  combined shape, from
  `SingularEndpoint/FactorStability.lean` and `SingularEndpoint/FactorHDensity.lean` in `localization_rankOne`, whose
  hypotheses `rankOneQuart ≤ C₁ε⁴` and `residQuart ≤ C₂ε⁴` are supplied here from the closeness
  clause (`factorMain_rankOneQuart_le`, `factorMain_residQuart_le`).

`localization_rankOne` is the construction half of `lem:localization-rank-one`.  The paper
states that lemma from `t(H,W) ≥ r_h^m` and `I_{p_h}(W) ≤ I_{p_h}(W_h)`, and derives the
`L⁴`-localization along the way; here the smallness `ε = ‖W - r_*‖₄ ≤ ε₂(d)` is taken as the
hypothesis instead, and the derivation from the cost comparison is `singular_endpoint_localization`
(`SingularEndpoint/LocalizationMain.lean`).  The paper asserts existence only; `factorMain_unique`
proves in addition uniqueness among solutions with `0 ≤ f ≤ M` and `q ≥ 2^{-d}` below a further
threshold `ε₃(d)`, a clause the paper does not state.

## Contents

* `factorMain_half_le_rStar` — `1/2 ≤ r_*`, the only arithmetic input of the `q`-bound;
* `factorMainConst`, `factorMainConst_nonneg`, `factorEps2`, `factorEps2_le`, `factorEps2_pos`,
  `factorMain_const_mul_eps_le_one` — the threshold;
* `factorMain_fixedPoint_Lnorm_le`, `factorMain_abs_integral_pow_sub_one_le`,
  `factorMain_den_lower`, `factorMain_integral_pow_le_four_mul_den` — steps 1–4;
* `exists_factor_solution_qlow` — the Factor solution **with** `2^{-d} ≤ q`;
* `exists_factorDecomp` — the `FactorDecomp` with all three quantitative clauses;
* `factorMain_Lnorm_pow_four`, `factorMain_contractionEps_pow_four`,
  `factorMain_Lnorm_rankOne_sub_le`, `factorMain_residQuart_le`, `factorMain_rankOneQuart_le` —
  the quartic form of the closeness bound, as `eq:moment-and-cost-gap-bounds` consumes it;
* `factorMain_closeConst_nonneg`, `factorMainC1`, `factorMainC2` and their nonnegativity,
  `factorMain_two_mul_card_edgeFinset` — the constants and the handshake identity;
* `localization_rankOne` — **the assembled lemma**;
* `factorMainMargin`, `factorMain_contractionM_mul_uStar`, `factorMainMargin_pos`, `factorEps3`,
  `factorEps3_le`, `factorMain_margin_bound`, `factorMain_integral_pos`,
  `factorMain_le_contractionM_mul_integral`, `factorMain_unique` — the uniqueness clause.
-/

namespace UpperTailOptimizers

namespace SingularEndpoint

open MeasureTheory

variable {d : ℕ} {W : Graphon} {φ : ℝ → ℝ}

/-! ## Elementary tools -/

/-- `1/2 ≤ r_* = (d-1)/d` for `d ≥ 2`.  This is the margin that makes the target `q ≥ 2^{-d}`
reachable: along the family `q → r_*^{d/2} ≥ 2^{-d/2}`. -/
theorem factorMain_half_le_rStar (hd : 2 ≤ d) : (1 : ℝ) / 2 ≤ rStar d := by
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  rw [rStar_eq, le_div_iff₀ (by linarith)]
  linarith

/-! ## The threshold `ε₂(d)` -/

/-- The constant `A(d) = (dM^{d-1} + 4(d-1)M^{d-2})·C_close(d) + 4M^{d-1}` of the threshold:
`A(d)·ε ≤ 1` is exactly what step 4 needs. -/
noncomputable def factorMainConst (d : ℕ) : ℝ :=
  ((d : ℝ) * contractionM d ^ (d - 1) + 4 * (((d : ℝ) - 1) * contractionM d ^ (d - 2)))
      * contractionCloseConst d
    + 4 * contractionM d ^ (d - 1)

/-- `A(d) ≥ 0`. -/
theorem factorMainConst_nonneg (hd : 2 ≤ d) : 0 ≤ factorMainConst d := by
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hM := contractionM_pos hd
  have h1 : (0 : ℝ) ≤ contractionM d ^ (d - 1) := pow_nonneg hM.le _
  have h2 : (0 : ℝ) ≤ contractionM d ^ (d - 2) := pow_nonneg hM.le _
  have hC := (contractionCloseConst_pos hd).le
  have t1 : (0 : ℝ) ≤ (d : ℝ) * contractionM d ^ (d - 1) := mul_nonneg (by linarith) h1
  have t2 : (0 : ℝ) ≤ 4 * (((d : ℝ) - 1) * contractionM d ^ (d - 2)) :=
    mul_nonneg (by norm_num) (mul_nonneg (by linarith) h2)
  have t3 : (0 : ℝ) ≤ ((d : ℝ) * contractionM d ^ (d - 1)
      + 4 * (((d : ℝ) - 1) * contractionM d ^ (d - 2))) * contractionCloseConst d :=
    mul_nonneg (by linarith) hC
  have t4 : (0 : ℝ) ≤ 4 * contractionM d ^ (d - 1) := by linarith
  simp only [factorMainConst]
  linarith

/-- The threshold `ε₂(d) = min(ε₁(d), 1/(A(d)+1))`: small enough for the Banach argument of
`SingularEndpoint/FactorFix.lean` *and* for `A(d)·ε ≤ 1`. -/
noncomputable def factorEps2 (d : ℕ) : ℝ := min (factorEps1 d) (1 / (factorMainConst d + 1))

/-- `ε₂(d) ≤ ε₁(d)`. -/
theorem factorEps2_le (d : ℕ) : factorEps2 d ≤ factorEps1 d := min_le_left _ _

/-- `ε₂(d) > 0`. -/
theorem factorEps2_pos (hd : 2 ≤ d) : 0 < factorEps2 d :=
  lt_min (factorEps1_pos hd) (div_pos one_pos (by linarith [factorMainConst_nonneg (d := d) hd]))

/-- The form in which the threshold is consumed: `A(d)·ε ≤ 1`. -/
theorem factorMain_const_mul_eps_le_one (hd : 2 ≤ d) (hε : contractionEps W d ≤ factorEps2 d) :
    factorMainConst d * contractionEps W d ≤ 1 := by
  have hA := factorMainConst_nonneg (d := d) hd
  have hpos : (0 : ℝ) < factorMainConst d + 1 := by linarith
  have h1 : contractionEps W d ≤ 1 / (factorMainConst d + 1) := le_trans hε (min_le_right _ _)
  have h2 : factorMainConst d * contractionEps W d
      ≤ factorMainConst d * (1 / (factorMainConst d + 1)) :=
    mul_le_mul_of_nonneg_left h1 hA
  have h3 : factorMainConst d * (1 / (factorMainConst d + 1)) ≤ 1 := by
    rw [mul_one_div, div_le_one hpos]
    linarith
  linarith

/-! ## Steps 1–3: the fixed point is close to the constant `1` -/

/-- **Step 1.**  The contraction fixed point is `O(ε)`-close to the constant `1` in `L⁴`.  This is
`contractionMap_closeness` applied to `φ` itself, and it carries **no** hypothesis on `q` — which is
what makes the whole route non-circular. -/
theorem factorMain_fixedPoint_Lnorm_le (hd : 2 ≤ d) (hφ : ContractionMem d φ)
    (hfix : ∀ x, contractionMap W d φ x = φ x) (hε : contractionEps W d ≤ contractionEps0 d) :
    Lnorm unitμ 4 (fun x => φ x - 1) ≤ contractionCloseConst d * contractionEps W d := by
  have h := contractionMap_closeness hd hφ hε
  have hfun : (fun x => contractionMap W d φ x - 1) = fun x => φ x - 1 :=
    funext fun x => by rw [hfix x]
  rwa [hfun] at h

/-- **Step 2.**  `|∫φ^n - 1| ≤ nM^{n-1}‖φ - 1‖₄`, the moment comparison of
`SingularEndpoint/FactorSolution.lean` at the constant `b = 1`.  Only measurability and the bounds
`0 ≤ φ ≤ M` are used; the unit mass of `φ` plays no part. -/
theorem factorMain_abs_integral_pow_sub_one_le (hd : 2 ≤ d) (hφ : ContractionMem d φ) (n : ℕ) :
    |(∫ x, φ x ^ n ∂unitμ) - 1|
      ≤ (n : ℝ) * contractionM d ^ (n - 1) * Lnorm unitμ 4 (fun x => φ x - 1) := by
  have h := factorSolution_abs_integral_sub_pow_le (d := d) hφ.meas hφ.nonneg hφ.le_bound
    (b := 1) zero_le_one (factorFix_one_le_contractionM hd) n
  rwa [one_pow] at h

/-- **Step 3.**  `κ = ∫T_W(φ^{d-1}) ≥ r_* - (d-1)M^{d-2}‖φ - 1‖₄ - εM^{d-1}`: the rank-one
splitting `κ = r_*∫φ^{d-1} + ∫T_U(φ^{d-1})` with the first moment estimated by step 2 and the
second by `abs_integral_contractionErr_le`. -/
theorem factorMain_den_lower (hd : 2 ≤ d) (hφ : ContractionMem d φ)
    (hε : contractionEps W d ≤ contractionEps0 d) :
    rStar d - ((d : ℝ) - 1) * contractionM d ^ (d - 2) * Lnorm unitμ 4 (fun x => φ x - 1)
        - contractionEps W d * contractionM d ^ (d - 1)
      ≤ contractionDen W d φ := by
  have hr0 := (rStar_pos hd).le
  have hr1 := (rStar_lt_one hd).le
  have hM := contractionM_pos hd
  have hΛ0 : (0 : ℝ) ≤ Lnorm unitμ 4 (fun x => φ x - 1) := Lnorm_nonneg _ _ _
  have hδ0 : (0 : ℝ) ≤ ((d : ℝ) - 1) * contractionM d ^ (d - 2)
      * Lnorm unitμ 4 (fun x => φ x - 1) := by
    have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    exact mul_nonneg (mul_nonneg (by linarith) (pow_nonneg hM.le _)) hΛ0
  have hsplit : contractionDen W d φ
      = rStar d * (∫ y, φ y ^ (d - 1) ∂unitμ) + ∫ x, contractionErr W d φ x ∂unitμ := by
    rw [contractionDen_eq hd hφ hε]
    exact contractionNum_integral_split hd hφ
  have hm := factorMain_abs_integral_pow_sub_one_le hd hφ (d - 1)
  rw [show ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 from by
      rw [Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_one],
    show d - 1 - 1 = d - 2 from by omega] at hm
  have hie := abs_integral_contractionErr_le hd W hφ
  have h1 : (1 : ℝ) - ((d : ℝ) - 1) * contractionM d ^ (d - 2)
      * Lnorm unitμ 4 (fun x => φ x - 1) ≤ ∫ y, φ y ^ (d - 1) ∂unitμ := by
    have := (abs_le.mp hm).1
    linarith
  have h2 : rStar d * (1 - ((d : ℝ) - 1) * contractionM d ^ (d - 2)
      * Lnorm unitμ 4 (fun x => φ x - 1))
      ≤ rStar d * ∫ y, φ y ^ (d - 1) ∂unitμ :=
    mul_le_mul_of_nonneg_left h1 hr0
  have hprod : rStar d * (((d : ℝ) - 1) * contractionM d ^ (d - 2)
      * Lnorm unitμ 4 (fun x => φ x - 1))
      ≤ 1 * (((d : ℝ) - 1) * contractionM d ^ (d - 2)
        * Lnorm unitμ 4 (fun x => φ x - 1)) :=
    mul_le_mul_of_nonneg_right hr1 hδ0
  have h3 := (abs_le.mp hie).1
  rw [hsplit]
  linarith

/-! ## Step 4: `I ≤ 4κ` -/

/-- **Step 4**, the heart of the `q`-bound: below the threshold `ε₂(d)` the `d`-th moment of the
fixed point is at most four times its contraction denominator,
`∫φ^d ≤ 4·∫T_W(φ^{d-1})`.

`I ≤ 1 + O(ε)` (step 2), `κ ≥ r_* - O(ε) ≥ 1/2 - O(ε)` (step 3) and `1/2 > 1/4`: the factor `4`
is met with a factor-of-two margin, which is where the smallness of `ε` is genuinely used. -/
theorem factorMain_integral_pow_le_four_mul_den (hd : 2 ≤ d) (hφ : ContractionMem d φ)
    (hfix : ∀ x, contractionMap W d φ x = φ x) (heps : contractionEps W d ≤ factorEps2 d) :
    (∫ x, φ x ^ d ∂unitμ) ≤ 4 * contractionDen W d φ := by
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hM := contractionM_pos hd
  have hε : contractionEps W d ≤ contractionEps0 d :=
    le_trans (le_trans heps (factorEps2_le d)) (factorEps1_le d)
  have hΛ0 : (0 : ℝ) ≤ Lnorm unitμ 4 (fun x => φ x - 1) := Lnorm_nonneg _ _ _
  have hΛ := factorMain_fixedPoint_Lnorm_le hd hφ hfix hε
  have hI := factorMain_abs_integral_pow_sub_one_le hd hφ d
  have hκ := factorMain_den_lower hd hφ hε
  have hhalf := factorMain_half_le_rStar (d := d) hd
  have hAeps := factorMain_const_mul_eps_le_one (W := W) hd heps
  have hcoef0 : (0 : ℝ) ≤ (d : ℝ) * contractionM d ^ (d - 1)
      + 4 * (((d : ℝ) - 1) * contractionM d ^ (d - 2)) := by
    have h1 : (0 : ℝ) ≤ (d : ℝ) * contractionM d ^ (d - 1) :=
      mul_nonneg (by linarith) (pow_nonneg hM.le _)
    have h2 : (0 : ℝ) ≤ 4 * (((d : ℝ) - 1) * contractionM d ^ (d - 2)) :=
      mul_nonneg (by norm_num) (mul_nonneg (by linarith) (pow_nonneg hM.le _))
    linarith
  have hstep : ((d : ℝ) * contractionM d ^ (d - 1) + 4 * (((d : ℝ) - 1) * contractionM d ^ (d - 2)))
      * Lnorm unitμ 4 (fun x => φ x - 1)
      ≤ ((d : ℝ) * contractionM d ^ (d - 1) + 4 * (((d : ℝ) - 1) * contractionM d ^ (d - 2)))
        * (contractionCloseConst d * contractionEps W d) :=
    mul_le_mul_of_nonneg_left hΛ hcoef0
  have hexpand : factorMainConst d * contractionEps W d
      = ((d : ℝ) * contractionM d ^ (d - 1) + 4 * (((d : ℝ) - 1) * contractionM d ^ (d - 2)))
          * (contractionCloseConst d * contractionEps W d)
        + 4 * contractionM d ^ (d - 1) * contractionEps W d := by
    simp only [factorMainConst]
    ring
  have hIup := (abs_le.mp hI).2
  linarith

/-! ## The rescaling, with the `q`-bound -/

/-- **The rescaling of `factorFix_rescale`, carrying the lower bound on `q`.**  The extra
hypothesis is `I ≤ 4κ`; the extra conclusion is `2^{-d} ≤ q`.

The scale is `s = √(κ/I)` and the produced `q` is `s^{d-2}κ = s^d·I`.  From `I ≤ 4κ` one gets
`s ≥ 1/2`, and `I ≥ 1` then gives `q ≥ 2^{-d}` directly.  Everything else is
`factorFix_rescale`, whose proof is repeated because the scale `s` is existentially quantified
there and the new clause needs it. -/
private theorem factorMain_rescale (hd : 2 ≤ d) (W : Graphon) {κ I : ℝ}
    (hmeas : Measurable φ) (hnn : ∀ x, 0 ≤ φ x) (hbd : ∀ x, φ x ≤ contractionM d)
    (hIeq : ∫ x, φ x ^ d ∂unitμ = I) (hI1 : 1 ≤ I) (hκpos : 0 < κ) (hκI : κ ≤ I)
    (hquarter : I ≤ 4 * κ)
    (heq : ∀ x, kernelOp W.toFun (fun y => φ y ^ (d - 1)) x = κ * φ x) :
    ∃ f : ℝ → ℝ, ∃ q : ℝ, Measurable f ∧ (∀ x, 0 ≤ f x) ∧ (∀ x, f x ≤ contractionM d) ∧ 0 < q ∧
      (∀ x, kernelOp W.toFun (fun y => f y ^ (d - 1)) x = q * f x) ∧
      q = ∫ x, f x ^ d ∂unitμ ∧ (1 : ℝ) / 2 ^ d ≤ q := by
  have hI0 : 0 < I := lt_of_lt_of_le zero_lt_one hI1
  have hqI : 0 < κ / I := div_pos hκpos hI0
  have hspos : 0 < Real.sqrt (κ / I) := Real.sqrt_pos.mpr hqI
  have hssq : Real.sqrt (κ / I) ^ 2 = κ / I := Real.sq_sqrt hqI.le
  have hs1 : Real.sqrt (κ / I) ≤ 1 := by
    have hle : κ / I ≤ 1 := (div_le_one hI0).mpr hκI
    calc Real.sqrt (κ / I) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hle
      _ = 1 := Real.sqrt_one
  have hshalf : (1 : ℝ) / 2 ≤ Real.sqrt (κ / I) := by
    have h1 : Real.sqrt ((1 : ℝ) / 2 * (1 / 2)) ≤ Real.sqrt (κ / I) := by
      refine Real.sqrt_le_sqrt ?_
      rw [le_div_iff₀ hI0]
      linarith
    rwa [Real.sqrt_mul_self (by norm_num : (0 : ℝ) ≤ 1 / 2)] at h1
  have hκeq : κ = Real.sqrt (κ / I) ^ 2 * I := by
    rw [hssq]
    exact (div_mul_cancel₀ κ hI0.ne').symm
  refine ⟨fun x => Real.sqrt (κ / I) * φ x, Real.sqrt (κ / I) ^ (d - 2) * κ,
    hmeas.const_mul _, fun x => mul_nonneg hspos.le (hnn x), fun x => ?_,
    mul_pos (pow_pos hspos _) hκpos, fun x => ?_, ?_, ?_⟩
  · calc Real.sqrt (κ / I) * φ x ≤ 1 * φ x := mul_le_mul_of_nonneg_right hs1 (hnn x)
      _ = φ x := one_mul _
      _ ≤ contractionM d := hbd x
  · have hpull : kernelOp W.toFun (fun y => (Real.sqrt (κ / I) * φ y) ^ (d - 1)) x
        = Real.sqrt (κ / I) ^ (d - 1) * kernelOp W.toFun (fun y => φ y ^ (d - 1)) x := by
      simp only [kernelOp]
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      simp only [mul_pow]
      ring
    have hpow : Real.sqrt (κ / I) ^ (d - 1)
        = Real.sqrt (κ / I) ^ (d - 2) * Real.sqrt (κ / I) := by
      rw [← pow_succ, show d - 2 + 1 = d - 1 from by omega]
    rw [hpull, heq x, hpow]
    ring
  · have hmom : ∫ x, (Real.sqrt (κ / I) * φ x) ^ d ∂unitμ = Real.sqrt (κ / I) ^ d * I := by
      rw [← hIeq, ← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only [mul_pow]
    have hpow : Real.sqrt (κ / I) ^ (d - 2) * Real.sqrt (κ / I) ^ 2
        = Real.sqrt (κ / I) ^ d := by
      rw [← pow_add, show d - 2 + 2 = d from by omega]
    rw [hmom]
    calc Real.sqrt (κ / I) ^ (d - 2) * κ
        = Real.sqrt (κ / I) ^ (d - 2) * (Real.sqrt (κ / I) ^ 2 * I) := by rw [← hκeq]
      _ = Real.sqrt (κ / I) ^ (d - 2) * Real.sqrt (κ / I) ^ 2 * I := by ring
      _ = Real.sqrt (κ / I) ^ d * I := by rw [hpow]
  · have hpow : Real.sqrt (κ / I) ^ (d - 2) * Real.sqrt (κ / I) ^ 2
        = Real.sqrt (κ / I) ^ d := by
      rw [← pow_add, show d - 2 + 2 = d from by omega]
    have hd2 : ((1 : ℝ) / 2) ^ d ≤ Real.sqrt (κ / I) ^ d :=
      pow_le_pow_left₀ (by norm_num) hshalf d
    have hmul : Real.sqrt (κ / I) ^ d * 1 ≤ Real.sqrt (κ / I) ^ d * I :=
      mul_le_mul_of_nonneg_left hI1 (pow_nonneg hspos.le d)
    have hval : Real.sqrt (κ / I) ^ (d - 2) * κ = Real.sqrt (κ / I) ^ d * I := by
      calc Real.sqrt (κ / I) ^ (d - 2) * κ
          = Real.sqrt (κ / I) ^ (d - 2) * (Real.sqrt (κ / I) ^ 2 * I) := by rw [← hκeq]
        _ = Real.sqrt (κ / I) ^ (d - 2) * Real.sqrt (κ / I) ^ 2 * I := by ring
        _ = Real.sqrt (κ / I) ^ d * I := by rw [hpow]
    rw [div_pow, one_pow] at hd2
    rw [hval]
    linarith

/-! ## The Factor solution, with the lower bound on `q` -/

/-- **The nonlinear Factor equation with `2^{-d} ≤ q`.**  Below the threshold `ε₂(d)` the
solution of `exists_factor_solution` can be produced with the extra clause `1/2^d ≤ q`, which is
exactly the hypothesis `hqlow` that seven statements of `SingularEndpoint/FactorSolution.lean` carry.

The construction is that of `exists_factor_solution` — the contraction fixed point `φ`, rescaled —
run through `factorMain_rescale` instead of `factorFix_rescale`, the extra input being step 4,
`∫φ^d ≤ 4·contractionDen W d φ`. -/
theorem exists_factor_solution_qlow (hd : 2 ≤ d) (W : Graphon)
    (heps : contractionEps W d ≤ factorEps2 d) :
    ∃ f : ℝ → ℝ, ∃ q : ℝ, Measurable f ∧ (∀ x, 0 ≤ f x) ∧ (∀ x, f x ≤ contractionM d) ∧ 0 < q ∧
      (∀ x, kernelOp W.toFun (fun y => f y ^ (d - 1)) x = q * f x) ∧
      q = ∫ x, f x ^ d ∂unitμ ∧ (1 : ℝ) / 2 ^ d ≤ q := by
  have heps1 : contractionEps W d ≤ factorEps1 d := le_trans heps (factorEps2_le d)
  have hε : contractionEps W d ≤ contractionEps0 d := le_trans heps1 (factorEps1_le d)
  obtain ⟨φ, hφ, hfix⟩ := exists_contraction_fixedPoint hd W heps1
  have hκpos : 0 < contractionDen W d φ := contractionDen_pos hd
  -- the unnormalised equation, with `κ` the (unfloored) denominator
  have heq : ∀ x, kernelOp W.toFun (fun y => φ y ^ (d - 1)) x = contractionDen W d φ * φ x := by
    intro x
    have h := hfix x
    simp only [contractionMap] at h
    have h2 : contractionNum W d φ x = φ x * contractionDen W d φ := (div_eq_iff hκpos.ne').mp h
    rw [mul_comm] at h2
    exact h2
  -- `∫φ^d ≥ 1`
  have hpowint : Integrable (fun x => φ x ^ d) unitμ :=
    integrable_of_abs_le (hφ.meas.pow_const d) (contractionM d ^ d) fun x => by
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (hφ.abs_le hd x) d
  have hI1 : 1 ≤ ∫ x, φ x ^ d ∂unitμ :=
    one_le_integral_pow hφ.nonneg (hφ.integrable hd) hφ.mass d hpowint
  -- `κ ≤ ∫φ^{d-1} ≤ ∫φ^d`
  have hnumint : Integrable (contractionNum W d φ) unitμ :=
    integrable_of_abs_le (measurable_contractionNum hφ) (1 * contractionM d ^ (d - 1))
      fun x => abs_kernelOp_le W.meas' hφ.measurable_pow
        (fun x y => abs_le.mpr ⟨by linarith [W.nonneg' x y], W.le_one' x y⟩)
        (hφ.abs_pow_le hd) x
  have hsubint : Integrable (fun y => 1 - φ y) unitμ :=
    (integrable_const 1).sub (hφ.integrable hd)
  have hzero : ∫ y, (1 - φ y) ∂unitμ = 0 := by
    rw [integral_sub (integrable_const 1) (hφ.integrable hd), hφ.mass, integral_const]
    simp
  have haddint : Integrable (fun y => φ y ^ d + (1 - φ y)) unitμ := hpowint.add hsubint
  have hstep : ∫ y, φ y ^ (d - 1) ∂unitμ ≤ ∫ x, φ x ^ d ∂unitμ := by
    have hmono := integral_mono (hφ.integrable_pow hd) haddint fun y =>
      factorFix_pow_sub_one_le hd (hφ.nonneg y)
    rwa [integral_add hpowint hsubint, hzero, add_zero] at hmono
  have hκI : contractionDen W d φ ≤ ∫ x, φ x ^ d ∂unitμ := by
    have hden : contractionDen W d φ = ∫ x, contractionNum W d φ x ∂unitμ := contractionDen_eq hd hφ hε
    have hnum : ∫ x, contractionNum W d φ x ∂unitμ ≤ ∫ y, φ y ^ (d - 1) ∂unitμ :=
      calc ∫ x, contractionNum W d φ x ∂unitμ
          ≤ ∫ _x : ℝ, (∫ y, φ y ^ (d - 1) ∂unitμ) ∂unitμ :=
            integral_mono hnumint (integrable_const _) (contractionNum_le hd hφ)
        _ = ∫ y, φ y ^ (d - 1) ∂unitμ := by simp
    rw [hden]
    linarith
  exact factorMain_rescale hd W hφ.meas hφ.nonneg hφ.le_bound rfl hI1 hκpos hκI
    (factorMain_integral_pow_le_four_mul_den hd hφ hfix heps) heq

/-! ## The `FactorDecomp` with all quantitative clauses -/

/-- **`lem:localization-rank-one`, existence half.**  For a graphon `W` with
`ε = ‖W - r_*‖₄ ≤ ε₂(d)` there is a `FactorDecomp d W` — that is, a nonnegative bounded
measurable `f` satisfying the orthogonality relation of `eq:rank-one-orthogonality`,
hence also `T_W(f^{d-1}) = qf` with `q = ∫f^d` (`eq:rank-one-orthogonality`,
`FactorDecomp.factor_eq`) — whose rank-one moment obeys `q ≥ 2^{-d}`, whose factor obeys the
pointwise bound `f ≤ q^{-1/d}` of `eq:rank-one-orthogonality`, and which satisfies
`eq:rank-one-reduction-bounds`,

`‖f - u_*‖₄ + ‖E‖₄ ≤ C(d)·ε`,  `C(d) = factorSolutionCloseConst d`.

The `q`-bound is the contribution of this file; the other three clauses are
`SingularEndpoint/FactorSolution.lean` with `hqlow` discharged. -/
theorem exists_factorDecomp (hd : 2 ≤ d) (W : Graphon) (heps : contractionEps W d ≤ factorEps2 d) :
    ∃ P : FactorDecomp d W, 0 < P.qVal ∧ (1 : ℝ) / 2 ^ d ≤ P.qVal ∧
      (∀ x, P.f x ≤ P.qVal ^ (-((d : ℝ)⁻¹))) ∧
      Lnorm unitμ 4 (fun x => P.f x - uStar d)
          + Lnorm gμ 4 (fun z : ℝ × ℝ => P.resid z.1 z.2)
        ≤ factorSolutionCloseConst d * contractionEps W d := by
  obtain ⟨f, q, hmeas, hnn, hMb, hq, heq, hqdef, hqlow⟩ := exists_factor_solution_qlow hd W heps
  obtain ⟨P, hPf, hPq⟩ := exists_factorDecomp_of_solution hd hmeas hnn hMb hq heq hqdef hqlow
  refine ⟨P, by rw [hPq]; exact hq, by rw [hPq]; exact hqlow, fun x => ?_, ?_⟩
  · rw [hPq, hPf x]
    exact factorSolution_pointwise_bound hd hmeas hnn hMb hq heq hqdef x
  · have h := factorSolution_closeness hd hmeas hnn hMb hq heq hqdef hqlow
    have hfun1 : (fun x => P.f x - uStar d) = fun x => f x - uStar d := by
      funext x
      rw [hPf x]
    have hfun2 : (fun z : ℝ × ℝ => P.resid z.1 z.2)
        = fun z : ℝ × ℝ => W.toFun z.1 z.2 - f z.1 * f z.2 := by
      funext z
      simp only [FactorDecomp.resid, hPf]
    rw [hfun1, hfun2]
    exact h

/-! ## The quartic form of the closeness bound

The stability bound — `eq:moment-and-cost-gap-bounds` in the combined shape — is stated in `SingularEndpoint/FactorStability.lean` with the
two closeness hypotheses in *quartic* form, `∫∫(A - r_*)⁴ ≤ C₁ε⁴` and `∫∫E⁴ ≤ C₂ε⁴`.  These three lemmas
convert `eq:rank-one-reduction-bounds` into that shape; the only work is that `Lnorm` is
defined with `Real.rpow` while the quartic defects are written with `Monoid.npow`.
-/

/-- `|t|^{(4:ℝ)} = t⁴`: the `rpow`/`npow` bridge at the exponent `4`. -/
private theorem factorMain_abs_rpow_four (t : ℝ) : |t| ^ (4 : ℝ) = t ^ 4 := by
  have h : |t| ^ (4 : ℝ) = |t| ^ (4 : ℕ) := by
    rw [← Real.rpow_natCast |t| 4]
    norm_num
  rw [h, ← abs_pow, abs_of_nonneg (by positivity : (0 : ℝ) ≤ t ^ 4)]

/-- `‖g‖₄⁴ = ∫ g⁴`: the quartic form of `Lnorm_rpow`. -/
theorem factorMain_Lnorm_pow_four {α : Type*} [MeasurableSpace α] (μ : Measure α) (g : α → ℝ) :
    Lnorm μ 4 g ^ 4 = ∫ x, g x ^ 4 ∂μ := by
  have h := Lnorm_rpow (μ := μ) (p := 4) (by norm_num) g
  have e1 : Lnorm μ 4 g ^ (4 : ℝ) = Lnorm μ 4 g ^ (4 : ℕ) := by
    rw [← Real.rpow_natCast (Lnorm μ 4 g) 4]
    norm_num
  rw [e1] at h
  rw [h]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => factorMain_abs_rpow_four (g x))

/-- `ε⁴ = ∫∫(W - r_*)⁴`: the smallness parameter of the contraction construction and the quartic
defect of `eq:moment-and-cost-gap-bounds` are the same quantity. -/
theorem factorMain_contractionEps_pow_four (d : ℕ) (W : Graphon) :
    contractionEps W d ^ 4 = defectQuart d W := by
  rw [contractionEps, factorMain_Lnorm_pow_four]
  simp only [contractionU, defectQuart]

/-- `∫∫E⁴ ≤ C⁴ε⁴`, from `‖E‖₄ ≤ Cε`. -/
theorem factorMain_residQuart_le {P : FactorDecomp d W} {C : ℝ}
    (hC : Lnorm gμ 4 (fun z : ℝ × ℝ => P.resid z.1 z.2) ≤ C * contractionEps W d) :
    P.residQuart ≤ C ^ 4 * defectQuart d W := by
  have h0 : (0 : ℝ) ≤ Lnorm gμ 4 (fun z : ℝ × ℝ => P.resid z.1 z.2) := Lnorm_nonneg _ _ _
  have h4 := pow_le_pow_left₀ h0 hC 4
  rw [factorMain_Lnorm_pow_four] at h4
  calc P.residQuart = ∫ z, P.resid z.1 z.2 ^ 4 ∂gμ := rfl
    _ ≤ (C * contractionEps W d) ^ 4 := h4
    _ = C ^ 4 * defectQuart d W := by rw [mul_pow, factorMain_contractionEps_pow_four]

/-- `‖A - r_*‖₄ ≤ ε + ‖E‖₄`: the rank-one part is close to the constant `r_*` because both `W`
and `A` are, `A - r_* = (W - r_*) - E`. -/
theorem factorMain_Lnorm_rankOne_sub_le (hd : 2 ≤ d) (P : FactorDecomp d W) :
    Lnorm gμ 4 (fun z : ℝ × ℝ => P.rankOne z.1 z.2 - rStar d)
      ≤ contractionEps W d + Lnorm gμ 4 (fun z : ℝ × ℝ => P.resid z.1 z.2) := by
  have hUm : Measurable fun z : ℝ × ℝ => contractionU W d z.1 z.2 := contraction_measurable_U W d
  have hcong : Lnorm gμ 4 (fun z : ℝ × ℝ => P.rankOne z.1 z.2 - rStar d)
      = Lnorm gμ 4 (fun z : ℝ × ℝ => contractionU W d z.1 z.2 + -P.resid z.1 z.2) :=
    lpBridge_Lnorm_congr 4 (Filter.Eventually.of_forall fun z => by
      simp only [contractionU, FactorDecomp.resid, FactorDecomp.rankOne]
      ring)
  rw [hcong]
  refine le_trans (factorSolutionLnorm_add_le hUm P.measurable_resid.neg
    (fun z => contraction_abs_U_le hd W z.1 z.2)
    (fun z => by rw [abs_neg]; exact P.abs_resid_le z.1 z.2)) ?_
  rw [factorSolutionLnorm_neg]
  exact le_rfl

/-- `∫∫(A - r_*)⁴ ≤ (C+1)⁴ε⁴`, from `‖E‖₄ ≤ Cε`. -/
theorem factorMain_rankOneQuart_le (hd : 2 ≤ d) {P : FactorDecomp d W} {C : ℝ}
    (hC : Lnorm gμ 4 (fun z : ℝ × ℝ => P.resid z.1 z.2) ≤ C * contractionEps W d) :
    P.rankOneQuart ≤ (C + 1) ^ 4 * defectQuart d W := by
  have h0 : (0 : ℝ) ≤ Lnorm gμ 4 (fun z : ℝ × ℝ => P.rankOne z.1 z.2 - rStar d) :=
    Lnorm_nonneg _ _ _
  have hle : Lnorm gμ 4 (fun z : ℝ × ℝ => P.rankOne z.1 z.2 - rStar d)
      ≤ (C + 1) * contractionEps W d := by
    have h := factorMain_Lnorm_rankOne_sub_le hd P
    linarith
  have h4 := pow_le_pow_left₀ h0 hle 4
  rw [factorMain_Lnorm_pow_four] at h4
  calc P.rankOneQuart = ∫ z, (P.rankOne z.1 z.2 - rStar d) ^ 4 ∂gμ := rfl
    _ ≤ ((C + 1) * contractionEps W d) ^ 4 := h4
    _ = (C + 1) ^ 4 * defectQuart d W := by rw [mul_pow, factorMain_contractionEps_pow_four]

/-! ## The assembled lemma -/

/-- `C(d) = factorSolutionCloseConst d ≥ 0`. -/
theorem factorMain_closeConst_nonneg (hd : 2 ≤ d) : 0 ≤ factorSolutionCloseConst d := by
  have h1 := uStar_nonneg hd
  have h2 := (contractionM_pos hd).le
  have h3 := factorSolutionK2_nonneg hd
  have h4 := factorSolutionDelta_nonneg hd
  have h5 : (0 : ℝ) ≤ (1 + uStar d + contractionM d) * (factorSolutionK2 d * factorSolutionDelta d) :=
    mul_nonneg (by linarith) (mul_nonneg h3 h4)
  simp only [factorSolutionCloseConst]
  linarith

/-- The constant `C₁` of the quartic closeness hypothesis feeding `eq:moment-and-cost-gap-bounds`:
`(C(d)+1)⁴`. -/
noncomputable def factorMainC1 (d : ℕ) : ℝ := (factorSolutionCloseConst d + 1) ^ 4

/-- The constant `C₂` of the quartic closeness hypothesis feeding `eq:moment-and-cost-gap-bounds`:
`C(d)⁴`. -/
noncomputable def factorMainC2 (d : ℕ) : ℝ := factorSolutionCloseConst d ^ 4

/-- `C₁(d) ≥ 0`. -/
theorem factorMainC1_nonneg (hd : 2 ≤ d) : 0 ≤ factorMainC1 d :=
  pow_nonneg (by linarith [factorMain_closeConst_nonneg (d := d) hd]) 4

/-- `C₂(d) ≥ 0`. -/
theorem factorMainC2_nonneg (hd : 2 ≤ d) : 0 ≤ factorMainC2 d :=
  pow_nonneg (factorMain_closeConst_nonneg (d := d) hd) 4

/-- The handshake identity `2|E(H)| = |V(H)|·d` for a `d`-regular `H`, in the form the
combined stability bound of `SingularEndpoint/FactorStability.lean` consumes it. -/
theorem factorMain_two_mul_card_edgeFinset {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (hreg : ∀ v, H.degree v = d) :
    2 * H.edgeFinset.card = Fintype.card V * d := by
  have h := H.sum_degrees_eq_twice_card_edges
  rw [Finset.sum_congr rfl fun v _ => hreg v] at h
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at h
  omega

/-- **`lem:localization-rank-one`, end to end.**  For a `d`-regular `H` on `v ≥ 2`
vertices and a graphon `W` with `ε = ‖W - r_*‖₄ ≤ ε₂(d)` there is a `FactorDecomp d W` — a
nonnegative `f` solving `eq:rank-one-orthogonality` together with the orthogonality
relation of `eq:rank-one-orthogonality` — such that, with `q = ∫f^d` and
`E = W - f ⊗ f`:

* `q > 0` and `q ≥ 2^{-d}`;
* `f ≤ q^{-1/d}` pointwise (the pointwise half of `eq:rank-one-orthogonality`);
* `‖f - u_*‖₄ + ‖E‖₄ ≤ C(d)·ε` `eq:rank-one-reduction-bounds`;
* `|t(H,W) - q^v| ≤ 40^{|E(H)|}‖E‖₂³` `eq:rank-one-reduction-bounds`;
* `c‖E‖₂² - C‖W - r_*‖₄⁴ - 40^{|E(H)|}‖E‖₂³ ≤ (∫W^d)^{m/d} - t(H,W)` — the combination of
  `eq:moment-and-cost-gap-bounds` and `eq:rank-one-reduction-bounds` that the paper
  displays unlabelled in the proof of `lem:localization-rank-one` — with
  `c = stabCoer d v 2^{-d} > 0`.

A **uniqueness** statement, beyond the paper, is proved separately as
`factorMain_unique`.  Every constant is explicit and depends only on `d` and `H`. -/
theorem localization_rankOne (hd : 2 ≤ d) {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (hreg : ∀ v, H.degree v = d)
    (hv : 2 ≤ Fintype.card V) (W : Graphon) (heps : contractionEps W d ≤ factorEps2 d) :
    ∃ P : FactorDecomp d W, 0 < P.qVal ∧ (1 : ℝ) / 2 ^ d ≤ P.qVal ∧
      (∀ x, P.f x ≤ P.qVal ^ (-((d : ℝ)⁻¹))) ∧
      Lnorm unitμ 4 (fun x => P.f x - uStar d)
          + Lnorm gμ 4 (fun z : ℝ × ℝ => P.resid z.1 z.2)
        ≤ factorSolutionCloseConst d * contractionEps W d ∧
      |W.tDensity H - P.qVal ^ Fintype.card V|
        ≤ (40 : ℝ) ^ H.edgeFinset.card * P.residNorm ^ 3 ∧
      stabCoer d (Fintype.card V) ((1 : ℝ) / 2 ^ d) * P.residNorm ^ 2
          - stabQuart d (Fintype.card V) (factorMainC1 d) (factorMainC2 d) * defectQuart d W
          - (40 : ℝ) ^ H.edgeFinset.card * P.residNorm ^ 3
        ≤ W.Wmoment d ^ ((H.edgeFinset.card : ℝ) / (d : ℝ)) - W.tDensity H := by
  obtain ⟨P, hqpos, hqlow, hptw, hclose⟩ := exists_factorDecomp hd W heps
  have hEnn : (0 : ℝ) ≤ Lnorm unitμ 4 (fun x => P.f x - uStar d) := Lnorm_nonneg _ _ _
  have hE : Lnorm gμ 4 (fun z : ℝ × ℝ => P.resid z.1 z.2)
      ≤ factorSolutionCloseConst d * contractionEps W d := by linarith
  have hT : |W.tDensity H - P.qVal ^ Fintype.card V|
      ≤ (40 : ℝ) ^ H.edgeFinset.card * P.residNorm ^ 3 := by
    have h := P.abs_tDensity_sub_qVal_pow_le H hreg
    rwa [FactorDecomp.residL2_eq_residNorm] at h
  refine ⟨P, hqpos, hqlow, hptw, hclose, hT, ?_⟩
  exact P.holder_stability hd hv (factorMain_two_mul_card_edgeFinset H hreg)
    (factorMainC1_nonneg (d := d) hd) (factorMainC2_nonneg (d := d) hd)
    (by positivity) hqlow (factorMain_rankOneQuart_le hd hE) (factorMain_residQuart_le hE) hT

/-! ## Uniqueness

`lem:localization-rank-one` asserts existence only, so this clause goes beyond the paper.  What `SingularEndpoint/FactorFix.lean` gives is
uniqueness of
the fixed point of the *normalised* contraction map inside the invariant set `S`.  The transfer is
this: a solution `f` with `0 ≤ f ≤ M` and `q ≥ 2^{-d}` normalises to `φ = f/∫f ∈ S`, which is a
fixed point of the normalised map; two solutions therefore have proportional factors, and the
Factor equation then forces the proportionality constant to be `1`.

The one quantitative input is `f ≤ M·∫f`, i.e. `φ ≤ M`: it comes from `f ≤ 2`
(`factorSolution_le_two`) and `∫f ≥ u_* - Cε` (`eq:rank-one-reduction-bounds` integrated),
because `M·u_* = 2/u_* > 2`.  The margin `ρ(d) = 2/u_* - 2` is positive but shrinks like `1/d`,
which is why uniqueness needs the further threshold `ε₃(d) ≤ ε₂(d)`.
-/

/-- The margin `ρ(d) = 2/u_* - 2 = M·u_* - 2 > 0` available in the bound `f ≤ M·∫f`. -/
noncomputable def factorMainMargin (d : ℕ) : ℝ := 2 / uStar d - 2

/-- `M·u_* = 2/u_*`, because `u_*² = r_*` and `M·r_* = 2`. -/
theorem factorMain_contractionM_mul_uStar (hd : 2 ≤ d) : contractionM d * uStar d = 2 / uStar d := by
  have hu := uStar_pos hd
  rw [eq_div_iff hu.ne']
  linear_combination contractionM d * uStar_sq hd + contractionM_mul_rStar hd

/-- `ρ(d) > 0`, since `u_* < 1`. -/
theorem factorMainMargin_pos (hd : 2 ≤ d) : 0 < factorMainMargin d := by
  have hu := uStar_pos hd
  have hu1 := uStar_lt_one hd
  have h : (2 : ℝ) < 2 / uStar d := by
    rw [lt_div_iff₀ hu]
    nlinarith
  simp only [factorMainMargin]
  linarith

/-- The uniqueness threshold `ε₃(d) = min(ε₂(d), ρ(d)/(M·C(d)+1))`. -/
noncomputable def factorEps3 (d : ℕ) : ℝ :=
  min (factorEps2 d) (factorMainMargin d / (contractionM d * factorSolutionCloseConst d + 1))

/-- `ε₃(d) ≤ ε₂(d)`: everything proved below `ε₂` is available below `ε₃`. -/
theorem factorEps3_le (d : ℕ) : factorEps3 d ≤ factorEps2 d := min_le_left _ _

/-- The form in which the uniqueness threshold is consumed: `M·C(d)·ε ≤ ρ(d)`. -/
theorem factorMain_margin_bound (hd : 2 ≤ d) (hε : contractionEps W d ≤ factorEps3 d) :
    contractionM d * factorSolutionCloseConst d * contractionEps W d ≤ factorMainMargin d := by
  have hM := contractionM_pos hd
  have hC := factorMain_closeConst_nonneg (d := d) hd
  have hρ := (factorMainMargin_pos (d := d) hd).le
  have hB : (0 : ℝ) ≤ contractionM d * factorSolutionCloseConst d := mul_nonneg hM.le hC
  have hden : (0 : ℝ) < contractionM d * factorSolutionCloseConst d + 1 := by linarith
  have h1 : contractionEps W d
      ≤ factorMainMargin d / (contractionM d * factorSolutionCloseConst d + 1) :=
    le_trans hε (min_le_right _ _)
  have h2 : contractionM d * factorSolutionCloseConst d * contractionEps W d
      ≤ contractionM d * factorSolutionCloseConst d
        * (factorMainMargin d / (contractionM d * factorSolutionCloseConst d + 1)) :=
    mul_le_mul_of_nonneg_left h1 hB
  have h3 : contractionM d * factorSolutionCloseConst d
      * (factorMainMargin d / (contractionM d * factorSolutionCloseConst d + 1))
      ≤ factorMainMargin d := by
    rw [mul_div_assoc', div_le_iff₀ hden]
    nlinarith
  linarith

/-- The mass of a Factor factor is positive: `q = ∫f^d ≤ M^{d-1}∫f`. -/
theorem factorMain_integral_pos (hd : 2 ≤ d) {f : ℝ → ℝ} {q : ℝ} (hmeas : Measurable f)
    (hnn : ∀ x, 0 ≤ f x) (hMb : ∀ x, f x ≤ contractionM d) (hq : 0 < q)
    (hqdef : q = ∫ x, f x ^ d ∂unitμ) : 0 < ∫ x, f x ∂unitμ := by
  have hM := contractionM_pos hd
  have hpt : ∀ x, f x ^ d ≤ contractionM d ^ (d - 1) * f x := by
    intro x
    have he : f x ^ (d - 1) * f x = f x ^ d := by
      rw [← pow_succ, show d - 1 + 1 = d from by omega]
    calc f x ^ d = f x ^ (d - 1) * f x := he.symm
      _ ≤ contractionM d ^ (d - 1) * f x :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (hnn x) (hMb x) _) (hnn x)
  have hint : Integrable f unitμ :=
    integrable_of_abs_le hmeas (contractionM d)
      fun x => abs_le.mpr ⟨by linarith [hnn x, hM.le], hMb x⟩
  have hle : q ≤ contractionM d ^ (d - 1) * ∫ x, f x ∂unitμ := by
    rw [hqdef, ← integral_const_mul]
    exact integral_mono (factorSolution_integrable_pow hmeas hnn hMb d) (hint.const_mul _) hpt
  by_contra hcon
  push Not at hcon
  nlinarith [pow_pos hM (d - 1)]

/-- **The normalisation bound** `f ≤ M·∫f`, the one quantitative input of the uniqueness
transfer.  `f ≤ 2` is `factorSolution_le_two`, `∫f ≥ u_* - Cε` is
`eq:rank-one-reduction-bounds` integrated against the unit mass, and `M·u_* - 2 = ρ(d)` is the
margin that `ε₃(d)` respects. -/
theorem factorMain_le_contractionM_mul_integral (hd : 2 ≤ d) {f : ℝ → ℝ} {q : ℝ}
    (hmeas : Measurable f) (hnn : ∀ x, 0 ≤ f x) (hMb : ∀ x, f x ≤ contractionM d) (hq : 0 < q)
    (heq : ∀ x, kernelOp W.toFun (fun y => f y ^ (d - 1)) x = q * f x)
    (hqdef : q = ∫ x, f x ^ d ∂unitμ) (hqlow : (1 : ℝ) / 2 ^ d ≤ q)
    (hε : contractionEps W d ≤ factorEps3 d) (x : ℝ) : f x ≤ contractionM d * ∫ y, f y ∂unitμ := by
  have hM := contractionM_pos hd
  have h2 := factorSolution_le_two hd hmeas hnn hMb hq heq hqdef hqlow x
  have hclose := factorSolution_closeness hd hmeas hnn hMb hq heq hqdef hqlow
  have hEnn : (0 : ℝ) ≤ Lnorm gμ 4 (fun z : ℝ × ℝ => W.toFun z.1 z.2 - f z.1 * f z.2) :=
    Lnorm_nonneg _ _ _
  have hL : Lnorm unitμ 4 (fun y => f y - uStar d)
      ≤ factorSolutionCloseConst d * contractionEps W d := by linarith
  have hbnd : ∀ y, |f y - uStar d| ≤ contractionM d := by
    intro y
    have h1 := hnn y
    have h3 := hMb y
    have h4 := uStar_nonneg hd
    have h5 := (uStar_lt_one hd).le
    have h6 : (1 : ℝ) ≤ contractionM d := factorFix_one_le_contractionM hd
    rw [abs_le]
    constructor <;> linarith
  have hint : Integrable f unitμ :=
    integrable_of_abs_le hmeas (contractionM d)
      fun y => abs_le.mpr ⟨by linarith [hnn y, hM.le], hMb y⟩
  have hstep : |(∫ y, f y ∂unitμ) - uStar d| ≤ Lnorm unitμ 4 (fun y => f y - uStar d) := by
    calc |(∫ y, f y ∂unitμ) - uStar d| = |∫ y, (f y - uStar d) ∂unitμ| := by
          rw [integral_sub hint (integrable_const _)]
          simp
      _ ≤ ∫ y, |f y - uStar d| ∂unitμ := abs_integral_le_integral_abs
      _ ≤ Lnorm unitμ 4 (fun y => f y - uStar d) :=
          contractionIntegral_abs_le_Lnorm_four (hmeas.sub_const (uStar d)) hbnd
  have hm : uStar d - factorSolutionCloseConst d * contractionEps W d ≤ ∫ y, f y ∂unitμ := by
    have := (abs_le.mp hstep).1
    linarith
  have hmul : contractionM d * (uStar d - factorSolutionCloseConst d * contractionEps W d)
      ≤ contractionM d * ∫ y, f y ∂unitμ :=
    mul_le_mul_of_nonneg_left hm hM.le
  have hMu := factorMain_contractionM_mul_uStar (d := d) hd
  have hmargin := factorMain_margin_bound (W := W) hd hε
  simp only [factorMainMargin] at hmargin
  nlinarith

/-- The normalised factor `φ = f/m` is a fixed point of the normalised contraction map, at every
point.  The denominator evaluates to `q/m^{d-2}`, and the floor is inactive because `φ ∈ S`
(`contractionDen_eq`). -/
private theorem factorMain_normalised_fixedPoint (hd : 2 ≤ d) {f : ℝ → ℝ} {q m : ℝ}
    (hmpos : 0 < m) (hq : 0 < q)
    (heq : ∀ x, kernelOp W.toFun (fun y => f y ^ (d - 1)) x = q * f x)
    (hmem : ContractionMem d (fun x => f x / m)) (hε : contractionEps W d ≤ contractionEps0 d) (x : ℝ) :
    contractionMap W d (fun x => f x / m) x = f x / m := by
  have hm1 : m ^ (d - 1) = m ^ (d - 2) * m := by
    rw [← pow_succ, show d - 2 + 1 = d - 1 from by omega]
  have hnum : ∀ x, contractionNum W d (fun x => f x / m) x = q / m ^ (d - 2) * (f x / m) := by
    intro x
    have hpt : ∀ y, W.toFun x y * (f y / m) ^ (d - 1)
        = 1 / m ^ (d - 1) * (W.toFun x y * f y ^ (d - 1)) := by
      intro y
      rw [div_pow]
      field_simp
    simp only [contractionNum, kernelOp]
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul,
      show (∫ y, W.toFun x y * f y ^ (d - 1) ∂unitμ) = q * f x from heq x, hm1]
    field_simp
  have hden : contractionDen W d (fun x => f x / m) = q / m ^ (d - 2) := by
    rw [contractionDen_eq hd hmem hε, integral_congr_ae (Filter.Eventually.of_forall hnum),
      integral_const_mul, hmem.mass, mul_one]
  have hc : q / m ^ (d - 2) ≠ 0 := ne_of_gt (div_pos hq (pow_pos hmpos _))
  simp only [contractionMap]
  rw [hnum x, hden, mul_div_cancel_left₀ _ hc]

/-- **Uniqueness of the Factor solution**, in normalised form: below
`ε₃(d)` any two solutions of `eq:rank-one-orthogonality` with `0 ≤ f ≤ M` and `q ≥ 2^{-d}`
have a.e. equal factors and equal rank-one moments.  `lem:localization-rank-one` asserts
existence only; this uniqueness clause goes beyond it.

The bounds `0 ≤ f ≤ M`, `q ≥ 2^{-d}` are the normalised form of "in a fixed
`L⁴`-neighbourhood of `u_*`" — by `eq:rank-one-reduction-bounds` any such solution *is* within
`Cε` of `u_*`, and `exists_factor_solution_qlow` produces one.

Proof: both factors normalise into the contraction invariant set (`factorMain_le_contractionM_mul_integral`)
and are fixed points there, so `factorFix_fixedPoint_unique` gives `f₁/∫f₁ = f₂/∫f₂` a.e., i.e.
`f₁ = t f₂` a.e. with `t = ∫f₁/∫f₂ > 0`.  Feeding that into the Factor equation gives
`q₁ = t^{d-2}q₂` (from the equation integrated) and `q₁ = t^d q₂` (from `q = ∫f^d`), whence
`t² = 1` and `t = 1`. -/
theorem factorMain_unique (hd : 2 ≤ d) (W : Graphon) (hε : contractionEps W d ≤ factorEps3 d)
    {f₁ f₂ : ℝ → ℝ} {q₁ q₂ : ℝ}
    (hme₁ : Measurable f₁) (hnn₁ : ∀ x, 0 ≤ f₁ x) (hbd₁ : ∀ x, f₁ x ≤ contractionM d) (hp₁ : 0 < q₁)
    (heq₁ : ∀ x, kernelOp W.toFun (fun y => f₁ y ^ (d - 1)) x = q₁ * f₁ x)
    (hdf₁ : q₁ = ∫ x, f₁ x ^ d ∂unitμ) (hlo₁ : (1 : ℝ) / 2 ^ d ≤ q₁)
    (hme₂ : Measurable f₂) (hnn₂ : ∀ x, 0 ≤ f₂ x) (hbd₂ : ∀ x, f₂ x ≤ contractionM d) (hp₂ : 0 < q₂)
    (heq₂ : ∀ x, kernelOp W.toFun (fun y => f₂ y ^ (d - 1)) x = q₂ * f₂ x)
    (hdf₂ : q₂ = ∫ x, f₂ x ^ d ∂unitμ) (hlo₂ : (1 : ℝ) / 2 ^ d ≤ q₂) :
    f₁ =ᵐ[unitμ] f₂ ∧ q₁ = q₂ := by
  have hε1 : contractionEps W d ≤ factorEps1 d :=
    le_trans (le_trans hε (factorEps3_le d)) (factorEps2_le d)
  have hε0 : contractionEps W d ≤ contractionEps0 d := le_trans hε1 (factorEps1_le d)
  obtain ⟨a, ha⟩ : ∃ a : ℝ, ∫ y, f₁ y ∂unitμ = a := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℝ, ∫ y, f₂ y ∂unitμ = b := ⟨_, rfl⟩
  have hapos : 0 < a := ha ▸ factorMain_integral_pos hd hme₁ hnn₁ hbd₁ hp₁ hdf₁
  have hbpos : 0 < b := hb ▸ factorMain_integral_pos hd hme₂ hnn₂ hbd₂ hp₂ hdf₂
  obtain ⟨t, ht⟩ : ∃ t : ℝ, a / b = t := ⟨_, rfl⟩
  have htpos : 0 < t := ht ▸ div_pos hapos hbpos
  have hab : a = t * b := by
    rw [← ht]
    field_simp
  -- both factors normalise into the invariant set
  have hmem₁ : ContractionMem d (fun x => f₁ x / a) := by
    refine ⟨hme₁.div_const _, fun x => div_nonneg (hnn₁ x) hapos.le, fun x => ?_, ?_⟩
    · rw [div_le_iff₀ hapos]
      exact ha ▸ factorMain_le_contractionM_mul_integral hd hme₁ hnn₁ hbd₁ hp₁ heq₁ hdf₁ hlo₁ hε x
    · rw [integral_div, ha, div_self hapos.ne']
  have hmem₂ : ContractionMem d (fun x => f₂ x / b) := by
    refine ⟨hme₂.div_const _, fun x => div_nonneg (hnn₂ x) hbpos.le, fun x => ?_, ?_⟩
    · rw [div_le_iff₀ hbpos]
      exact hb ▸ factorMain_le_contractionM_mul_integral hd hme₂ hnn₂ hbd₂ hp₂ heq₂ hdf₂ hlo₂ hε x
    · rw [integral_div, hb, div_self hbpos.ne']
  have hfix₁ : contractionMap W d (fun x => f₁ x / a) =ᵐ[unitμ] fun x => f₁ x / a :=
    Filter.Eventually.of_forall
      (factorMain_normalised_fixedPoint hd hapos hp₁ heq₁ hmem₁ hε0)
  have hfix₂ : contractionMap W d (fun x => f₂ x / b) =ᵐ[unitμ] fun x => f₂ x / b :=
    Filter.Eventually.of_forall
      (factorMain_normalised_fixedPoint hd hbpos hp₂ heq₂ hmem₂ hε0)
  have huniq := factorFix_fixedPoint_unique hd W hε1 hmem₁ hmem₂ hfix₁ hfix₂
  -- the two factors are proportional
  have hae : ∀ᵐ x ∂unitμ, f₁ x = t * f₂ x := by
    filter_upwards [huniq] with x hx
    have hx' : f₁ x * b = f₂ x * a := by
      field_simp at hx
      linarith
    rw [hab] at hx'
    have hcan : f₁ x = f₂ x * t := mul_right_cancel₀ hbpos.ne' (by linear_combination hx')
    linarith
  -- the two relations between `q₁`, `q₂` and `t`
  have hqa : q₁ = t ^ d * q₂ := by
    rw [hdf₁, hdf₂, ← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [hae] with x hx
    rw [hx, mul_pow]
  have hptw : ∀ x, q₁ * f₁ x = t ^ (d - 1) * (q₂ * f₂ x) := by
    intro x
    have h1 : kernelOp W.toFun (fun y => f₁ y ^ (d - 1)) x
        = t ^ (d - 1) * kernelOp W.toFun (fun y => f₂ y ^ (d - 1)) x := by
      simp only [kernelOp]
      rw [← integral_const_mul]
      refine integral_congr_ae ?_
      filter_upwards [hae] with y hy
      rw [hy, mul_pow]
      ring
    rw [← heq₁ x, h1, heq₂ x]
  have hmass : q₁ * a = t ^ (d - 1) * (q₂ * b) := by
    have h := integral_congr_ae (μ := unitμ) (Filter.Eventually.of_forall hptw)
    simp only [integral_const_mul] at h
    rwa [ha, hb] at h
  -- hence `t = 1`
  have hpow1 : t ^ (d - 1) = t ^ (d - 2) * t := by
    rw [← pow_succ, show d - 2 + 1 = d - 1 from by omega]
  have hpowd : t ^ d = t ^ (d - 2) * t ^ 2 := by
    rw [← pow_add, show d - 2 + 2 = d from by omega]
  have hc2 : q₁ * t = t ^ (d - 1) * q₂ := by
    rw [hab] at hmass
    exact mul_right_cancel₀ hbpos.ne' (by linear_combination hmass)
  have hc4 : q₁ = t ^ (d - 2) * q₂ :=
    mul_right_cancel₀ htpos.ne' (by rw [hc2, hpow1]; ring)
  have hne : t ^ (d - 2) * q₂ ≠ 0 := ne_of_gt (mul_pos (pow_pos htpos _) hp₂)
  have hsq : t ^ (d - 2) * q₂ * t ^ 2 = t ^ (d - 2) * q₂ * 1 := by
    linear_combination hc4 - hqa - q₂ * hpowd
  have ht1 : t = 1 := by
    have hfac : (t - 1) * (t + 1) = 0 := by
      have := mul_left_cancel₀ hne hsq
      linear_combination this
    rcases mul_eq_zero.mp hfac with h' | h' <;> linarith
  refine ⟨?_, ?_⟩
  · filter_upwards [hae] with x hx
    rw [hx, ht1, one_mul]
  · rw [hqa, ht1, one_pow, one_mul]

end SingularEndpoint

end UpperTailOptimizers
