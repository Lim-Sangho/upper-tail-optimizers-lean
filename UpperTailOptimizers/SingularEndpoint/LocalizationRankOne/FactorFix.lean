import UpperTailOptimizers.SingularEndpoint.LocalizationRankOne.FactorContraction
import UpperTailOptimizers.SingularEndpoint.LocalizationRankOne.FactorLpBridge

/-!
# Running Banach: a solution of the nonlinear Factor equation (Section 5)

`lem:localization-rank-one` of `paper/sections/singular.tex` produces, for a competitor `W`
localized near `r_*` (`eq:graphon-quartic-localization`), a nonnegative factor `f` solving the
**nonlinear Factor equation**

`T_W(f^{d-1}) = q f`,  `q = ∫ f^d`

— the first half of `eq:rank-one-orthogonality`.  This file proves exactly that, by running
Banach's fixed-point theorem on the normalised contraction map of `SingularEndpoint/LocalizationRankOne/FactorContraction.lean`
across the `L⁴` bridge of `SingularEndpoint/LocalizationRankOne/FactorLpBridge.lean`, and then rescaling.

## The three steps

1. **A smaller threshold.**  `SingularEndpoint/LocalizationRankOne/FactorContraction.lean` fixes all its constants before its
   threshold `ε₀`, so the threshold may legitimately be shrunk afterwards:
   `factorEps1 d = min (ε₀ d) (1/(2(C_contr(d)+1)))` additionally forces
   `C_contr(d)·ε ≤ 1/2 < 1` (`factorFix_contr_le_half`), which is what Banach needs.

2. **Crossing to `Lp`.**  `contractionMap` acts on raw functions, Banach on `Lp ℝ 4 unitμ`.  The
   crossing is by an explicit pointwise representative `factorFixRepr M F = max 0 (min M F̃)`
   (`F̃` a measurable representative), and back by `MemLp.toLp` (`factorFixMap`).  The choice of
   representative is harmless because the contraction map only sees the a.e. class of its argument:
   `factorFix_contractionMap_congr` proves the stronger statement that `φ =ᵐ ψ` forces
   `contractionMap W d φ = contractionMap W d ψ` **at every point**, both being partial integrals of `φ`.

3. **From an a.e. fixed point to a pointwise one.**  Banach gives `N F = F` in `Lp`, i.e. an
   a.e. fixed point `g` of `contractionMap`.  Its image `φ := contractionMap W d g` is then a fixed point
   **pointwise** (`exists_contraction_fixedPoint`), again by `factorFix_contractionMap_congr`.  That is
   what makes the Factor equation hold at every `x`, not just a.e.

## The rescaling

A fixed point `φ` of the *normalised* map satisfies `T_W(φ^{d-1}) = κφ` with
`κ = contractionDen W d φ`, which is not yet `eq:rank-one-orthogonality` because the paper's
normalisation is `q = ∫ f^d`, not `∫ f = 1`.  Put `f = sφ`.  Then
`T_W(f^{d-1}) = s^{d-1}κφ = (s^{d-2}κ)f`, so `q = s^{d-2}κ`, while `∫ f^d = s^d ∫ φ^d`; the two
agree iff `κ = s^2∫φ^d`, i.e.

`s = (κ / ∫ φ^d)^{1/2}`  (`factorFix_rescale`).

The uniform bound `f ≤ M` survives the rescaling because `s ≤ 1`: indeed `κ ≤ ∫φ^{d-1} ≤ ∫φ^d`,
the second inequality being the pointwise Bernoulli-type estimate
`a^{d-1} ≤ a^d + (1 - a)` (`factorFix_pow_sub_one_le`, an exact factorisation
`a^{d-1} - a^d - (1-a) = (1-a)(a^{d-1}-1) ≤ 0`) integrated against the unit mass of `φ`.  This
replaces the power-mean inequality `‖φ‖_{d-1} ≤ ‖φ‖_d`, which is not needed in this form.

## What is realised, and what is not

Realised: the **first** equation of `eq:rank-one-orthogonality`, `T_W(f^{d-1}) = qf` with
`q = ∫f^d`, together with `0 ≤ f ≤ M = 2/r_*` pointwise, `0 < q`, and the uniqueness of the
contraction fixed point in the invariant set.

*Not* realised here, and left to the assembly: the orthogonality half of
`eq:rank-one-orthogonality`; the sharp pointwise bound `f ≤ q^{-1/d}`
`eq:rank-one-orthogonality`, which is strictly stronger than the `M` of the invariant
set; `eq:rank-one-reduction-bounds`; the combined stability inequality; and
`eq:rank-one-reduction-bounds`.  The first three are `SingularEndpoint/LocalizationRankOne/FactorSolution.lean`,
the fourth `SingularEndpoint/LocalizationRankOne/FactorStability.lean` and the fifth `SingularEndpoint/LocalizationRankOne/FactorHDensity.lean`, joined in
`SingularEndpoint/LocalizationRankOne/FactorMain.lean`.  The uniqueness proved here is uniqueness of *a.e. fixed points of
the normalised map inside the invariant set* `S` (`factorFix_fixedPoint_unique`), which is what
Banach gives.  The paper states no uniqueness for the Factor equation
(`lem:localization-rank-one` asserts existence only); the Lean's uniqueness of its solutions
among `0 ≤ f ≤ M` with `q ≥ 2^{-d}` is `factorMain_unique` (`SingularEndpoint/LocalizationRankOne/FactorMain.lean`).

## Contents

* `factorEps1`, `factorEps1_pos`, `factorEps1_le`, `factorFix_contr_le_half`,
  `factorFix_contr_lt_one` — the shrunken threshold;
* `factorFix_contractionNum_congr`, `factorFix_contractionDen_congr`, `factorFix_contractionMap_congr` — the
  contraction map factors through a.e. equality;
* `factorFixRepr` and its four properties, `factorFixMemLp`, `factorFixMap`,
  `factorFix_repr_spec`, `factorFixMap_mapsTo`, `factorFixMap_dist_le` — the `Lp` crossing;
* `exists_contraction_fixedPoint` — Banach: a pointwise fixed point of the normalised map in `S`;
* `factorFix_pow_sub_one_le`, `factorFix_rescale` — the homogenisation `f = sφ`;
* `exists_factor_solution` — **the target**, a solution of `T_W(f^{d-1}) = qf`, `q = ∫f^d`;
* `factorFix_fixedPoint_unique` — the Banach uniqueness companion.
-/

namespace UpperTailOptimizers

namespace SingularEndpoint

open MeasureTheory

open scoped NNReal

variable {d : ℕ} {W : Graphon} {φ ψ : ℝ → ℝ}

/-- `|W| ≤ 1` for a graphon, in the form the kernel estimates consume. -/
private theorem factorFix_abs_W_le (W : Graphon) : ∀ x y, |W.toFun x y| ≤ 1 := fun x y =>
  abs_le.mpr ⟨by linarith [W.nonneg' x y], W.le_one' x y⟩

/-- `1 ≤ M = 2/r_*`, the hypothesis of `lpBridgeSet_nonempty`. -/
theorem factorFix_one_le_contractionM (hd : 2 ≤ d) : 1 ≤ contractionM d := by
  have hr := rStar_pos hd
  have hr1 := (rStar_lt_one hd).le
  have h2 : contractionM d * rStar d = 2 := contractionM_mul_rStar hd
  nlinarith [contractionM_pos hd]

/-! ## The shrunken threshold

Every constant of `SingularEndpoint/LocalizationRankOne/FactorContraction.lean` is fixed before its threshold `ε₀`, so the
threshold may be shrunk after the fact without circularity.  Banach needs the contraction
factor `C_contr(d)·ε` to be `< 1`, which `ε₀` alone does not give.
-/

/-- The threshold `ε₁(d) = min(ε₀(d), 1/(2(C_contr(d)+1)))`: small enough for all three contraction
estimates *and* for the contraction factor `C_contr(d)·ε` to be at most `1/2`. -/
noncomputable def factorEps1 (d : ℕ) : ℝ :=
  min (contractionEps0 d) (1 / (2 * (contractionContrConst d + 1)))

/-- `ε₁(d) ≤ ε₀(d)`: the shrunken threshold still licenses every estimate of
`SingularEndpoint/LocalizationRankOne/FactorContraction.lean`. -/
theorem factorEps1_le (d : ℕ) : factorEps1 d ≤ contractionEps0 d := min_le_left _ _

/-- `ε₁(d) > 0`. -/
theorem factorEps1_pos (hd : 2 ≤ d) : 0 < factorEps1 d := by
  have hC := contractionContrConst_nonneg (d := d) hd
  exact lt_min (contractionEps0_pos hd) (div_pos one_pos (by linarith))

/-- **The contraction factor is at most `1/2`** below the shrunken threshold:
`C_contr(d)·ε ≤ C_contr(d)/(2(C_contr(d)+1)) ≤ 1/2`. -/
theorem factorFix_contr_le_half (hd : 2 ≤ d) (hε : contractionEps W d ≤ factorEps1 d) :
    contractionContrConst d * contractionEps W d ≤ 1 / 2 := by
  have hC := contractionContrConst_nonneg (d := d) hd
  have hpos : 0 < 2 * (contractionContrConst d + 1) := by linarith
  have h1 : contractionEps W d ≤ 1 / (2 * (contractionContrConst d + 1)) :=
    le_trans hε (min_le_right _ _)
  have h2 : contractionContrConst d * contractionEps W d
      ≤ contractionContrConst d * (1 / (2 * (contractionContrConst d + 1))) :=
    mul_le_mul_of_nonneg_left h1 hC
  have h3 : contractionContrConst d * (1 / (2 * (contractionContrConst d + 1))) ≤ 1 / 2 := by
    rw [mul_one_div, div_le_iff₀ hpos]
    linarith
  linarith

/-- The form Banach consumes: the contraction factor is `< 1`. -/
theorem factorFix_contr_lt_one (hd : 2 ≤ d) (hε : contractionEps W d ≤ factorEps1 d) :
    contractionContrConst d * contractionEps W d < 1 := by
  have h := factorFix_contr_le_half hd hε
  linarith

/-! ## The contraction map factors through a.e. equality

`contractionMap` is built from partial integrals of `φ^{d-1}`, so it does not see the choice of a
representative — and not merely up to a.e. equality: two a.e. equal arguments give *literally
equal* values at every point.  This is what lets the `Lp` fixed point be upgraded to a
pointwise one.
-/

/-- `A(φ) = T_W(φ^{d-1})` depends on `φ` only through its a.e. class, pointwise in `x`. -/
theorem factorFix_contractionNum_congr (W : Graphon) (h : φ =ᵐ[unitμ] ψ) (x : ℝ) :
    contractionNum W d φ x = contractionNum W d ψ x := by
  simp only [contractionNum, kernelOp]
  refine integral_congr_ae ?_
  filter_upwards [h] with y hy
  rw [hy]

/-- The denominator `∫A(φ)` depends on `φ` only through its a.e. class. -/
theorem factorFix_contractionDen_congr (W : Graphon) (h : φ =ᵐ[unitμ] ψ) :
    contractionDen W d φ = contractionDen W d ψ := by
  simp only [contractionDen]
  rw [integral_congr_ae
    (Filter.Eventually.of_forall (factorFix_contractionNum_congr (d := d) W h))]

/-- **The normalised contraction map is well defined on a.e. classes**, in the strong form: a.e.
equal arguments give equal values at *every* point. -/
theorem factorFix_contractionMap_congr (W : Graphon) (h : φ =ᵐ[unitμ] ψ) (x : ℝ) :
    contractionMap W d φ x = contractionMap W d ψ x := by
  simp only [contractionMap]
  rw [factorFix_contractionNum_congr W h x, factorFix_contractionDen_congr W h]

/-! ## Crossing to `Lp ℝ 4 unitμ`

Banach's theorem needs a complete metric space, and `Lnorm` is only a pseudometric on raw
functions.  `SingularEndpoint/LocalizationRankOne/FactorLpBridge.lean` supplies the complete set `lpBridgeSet M`; what is
missing is a *definable* representative, since `lpBridgeSet_exists_repr` is an existence
statement.  `factorFixRepr` is that representative, written out.
-/

/-- The definable pointwise representative of an `L⁴` class: the `[0,M]`-truncation of a
measurable representative.  Unlike `lpBridge_exists_pointwise_repr`, this is a *function* of the
class, which is what defining a self-map of `Lp` requires. -/
noncomputable def factorFixRepr (M : ℝ) (F : Lp ℝ 4 unitμ) : ℝ → ℝ := fun x =>
  max 0 (min M ((Lp.aestronglyMeasurable F).mk (⇑F) x))

/-- `factorFixRepr M F` is measurable. -/
theorem factorFixRepr_measurable (M : ℝ) (F : Lp ℝ 4 unitμ) :
    Measurable (factorFixRepr M F) :=
  measurable_const.max (measurable_const.min (Lp.aestronglyMeasurable F).measurable_mk)

/-- `factorFixRepr M F ≥ 0` at every point. -/
theorem factorFixRepr_nonneg (M : ℝ) (F : Lp ℝ 4 unitμ) (x : ℝ) : 0 ≤ factorFixRepr M F x :=
  le_max_left _ _

/-- `factorFixRepr M F ≤ M` at every point, for `M ≥ 0`. -/
theorem factorFixRepr_le {M : ℝ} (hM : 0 ≤ M) (F : Lp ℝ 4 unitμ) (x : ℝ) :
    factorFixRepr M F x ≤ M :=
  max_le hM (min_le_left _ _)

/-- `factorFixRepr M F` represents `F` as soon as `F` itself is a.e. in `[0,M]`: the truncation
is then inactive a.e. -/
theorem factorFixRepr_ae {M : ℝ} {F : Lp ℝ 4 unitμ} (h0 : ∀ᵐ x ∂unitμ, 0 ≤ F x)
    (hle : ∀ᵐ x ∂unitμ, F x ≤ M) : factorFixRepr M F =ᵐ[unitμ] ⇑F := by
  filter_upwards [h0, hle, (Lp.aestronglyMeasurable F).ae_eq_mk] with x hx0 hxM hxg
  simp only [factorFixRepr]
  rw [← hxg, min_eq_right hxM, max_eq_right hx0]

/-- The image of `factorFixRepr` under the contraction map is in `L⁴`: it is measurable and bounded
by `M^{d-1}·M`, the denominator being floored at `r_*/2 > 0`.  No hypothesis on `F` is needed —
the truncation is bounded by construction — which is what makes `factorFixMap` total. -/
theorem factorFixMemLp (hd : 2 ≤ d) (W : Graphon) (F : Lp ℝ 4 unitμ) :
    MemLp (contractionMap W d (factorFixRepr (contractionM d) F)) 4 unitμ := by
  have hgm : Measurable (factorFixRepr (contractionM d) F) := factorFixRepr_measurable _ _
  have hgb : ∀ y, |factorFixRepr (contractionM d) F y ^ (d - 1)| ≤ contractionM d ^ (d - 1) := by
    intro y
    rw [abs_pow, abs_of_nonneg (factorFixRepr_nonneg _ _ y)]
    exact pow_le_pow_left₀ (factorFixRepr_nonneg _ _ y)
      (factorFixRepr_le (contractionM_pos hd).le _ y) _
  have hmeas : Measurable (contractionMap W d (factorFixRepr (contractionM d) F)) :=
    (measurable_kernelOp W.meas' (hgm.pow_const _)).div_const _
  refine lpBridge_memLp hmeas (contractionM d ^ (d - 1) * contractionM d) fun x => ?_
  have hD : 0 < contractionDen W d (factorFixRepr (contractionM d) F) := contractionDen_pos hd
  have hnum : |contractionNum W d (factorFixRepr (contractionM d) F) x| ≤ 1 * contractionM d ^ (d - 1) :=
    abs_kernelOp_le W.meas' (hgm.pow_const _) (factorFix_abs_W_le W) hgb x
  rw [one_mul] at hnum
  have h1D : 1 / contractionDen W d (factorFixRepr (contractionM d) F) ≤ contractionM d := by
    have h := one_div_le_one_div_of_le (half_pos (rStar_pos hd))
      (contractionDen_ge (W := W) (φ := factorFixRepr (contractionM d) F))
    rwa [one_div_div] at h
  have habs : |contractionMap W d (factorFixRepr (contractionM d) F) x|
      = |contractionNum W d (factorFixRepr (contractionM d) F) x|
        / contractionDen W d (factorFixRepr (contractionM d) F) := by
    simp only [contractionMap]
    rw [abs_div, abs_of_pos hD]
  rw [habs, div_eq_mul_one_div]
  exact mul_le_mul hnum h1D (one_div_nonneg.mpr hD.le) (pow_nonneg (contractionM_pos hd).le _)

/-- **The `Lp` avatar of the normalised contraction map**: truncate to a pointwise representative,
apply `contractionMap`, lift back.  It is total, and on `lpBridgeSet M` it agrees with the honest
normalised map (`factorFixMap_mapsTo`, `factorFixMap_dist_le`). -/
noncomputable def factorFixMap (hd : 2 ≤ d) (W : Graphon) (F : Lp ℝ 4 unitμ) : Lp ℝ 4 unitμ :=
  (factorFixMemLp hd W F).toLp (contractionMap W d (factorFixRepr (contractionM d) F))

/-- On `lpBridgeSet M` the truncated representative lies in the contraction invariant set `S` and
represents its class. -/
theorem factorFix_repr_spec (hd : 2 ≤ d) {F : Lp ℝ 4 unitμ}
    (hF : F ∈ lpBridgeSet (contractionM d)) :
    ContractionMem d (factorFixRepr (contractionM d) F) ∧ factorFixRepr (contractionM d) F =ᵐ[unitμ] ⇑F := by
  obtain ⟨h0, hle⟩ := lpBridgeSet_ae hF
  have hae := factorFixRepr_ae h0 hle
  refine ⟨⟨factorFixRepr_measurable _ _, factorFixRepr_nonneg _ _,
    factorFixRepr_le (contractionM_pos hd).le _, ?_⟩, hae⟩
  rw [integral_congr_ae hae]
  exact (mem_lpBridgeSet_iff.mp hF).2.2

/-- `factorFixMap` preserves `lpBridgeSet M`, by `contractionMap_mem` and `toLp_mem_lpBridgeSet`. -/
theorem factorFixMap_mapsTo (hd : 2 ≤ d) (W : Graphon) (hε : contractionEps W d ≤ contractionEps0 d) :
    Set.MapsTo (factorFixMap hd W) (lpBridgeSet (contractionM d)) (lpBridgeSet (contractionM d)) := by
  intro F hF
  obtain ⟨hmem, -⟩ := factorFix_repr_spec hd hF
  have hN := contractionMap_mem hd hmem hε
  exact toLp_mem_lpBridgeSet (factorFixMemLp hd W F) hN.nonneg hN.le_bound hN.mass

/-- `factorFixMap` contracts on `lpBridgeSet M` with factor `C_contr(d)·ε`: the raw-function
estimate `contractionMap_contraction` read through `lpBridge_dist_toLp`.  The choice of
representative is immaterial because `Lnorm` sees only a.e. classes. -/
theorem factorFixMap_dist_le (hd : 2 ≤ d) (W : Graphon) (hε : contractionEps W d ≤ contractionEps0 d)
    {F G : Lp ℝ 4 unitμ} (hF : F ∈ lpBridgeSet (contractionM d))
    (hG : G ∈ lpBridgeSet (contractionM d)) :
    dist (factorFixMap hd W F) (factorFixMap hd W G)
      ≤ contractionContrConst d * contractionEps W d * dist F G := by
  obtain ⟨hmF, haeF⟩ := factorFix_repr_spec hd hF
  obtain ⟨hmG, haeG⟩ := factorFix_repr_spec hd hG
  have h1 : dist (factorFixMap hd W F) (factorFixMap hd W G)
      = Lnorm unitμ 4 (fun x => contractionMap W d (factorFixRepr (contractionM d) F) x
          - contractionMap W d (factorFixRepr (contractionM d) G) x) :=
    lpBridge_dist_toLp (factorFixMemLp hd W F) (factorFixMemLp hd W G)
  have h2 : dist F G = Lnorm unitμ 4 (fun x => factorFixRepr (contractionM d) F x
      - factorFixRepr (contractionM d) G x) := by
    rw [lpBridge_dist_eq]
    refine (lpBridge_Lnorm_congr 4 ?_).symm
    filter_upwards [haeF, haeG] with x hx1 hx2
    rw [hx1, hx2]
  rw [h1, h2]
  exact contractionMap_contraction hd hmF hmG hε

/-! ## Banach -/

/-- **The fixed point.**  Below the shrunken threshold the normalised contraction map has a fixed
point in the invariant set `S`, *pointwise*: `N(φ)(x) = φ(x)` for every `x`.

Banach gives only an a.e. fixed point `g`; the pointwise statement is recovered by passing to
`φ := N(g)`, which is a.e. equal to `g` and therefore has the same image under `N`
(`factorFix_contractionMap_congr`). -/
theorem exists_contraction_fixedPoint (hd : 2 ≤ d) (W : Graphon)
    (heps : contractionEps W d ≤ factorEps1 d) :
    ∃ φ : ℝ → ℝ, ContractionMem d φ ∧ ∀ x, contractionMap W d φ x = φ x := by
  have hε : contractionEps W d ≤ contractionEps0 d := le_trans heps (factorEps1_le d)
  have hknn : 0 ≤ contractionContrConst d * contractionEps W d :=
    mul_nonneg (contractionContrConst_nonneg hd) (contractionEps_nonneg W d)
  have hk1 : (⟨contractionContrConst d * contractionEps W d, hknn⟩ : ℝ≥0) < 1 :=
    factorFix_contr_lt_one hd heps
  obtain ⟨F, hFS, hfix, -⟩ := lpBridgeSet_exists_fixedPoint (factorFix_one_le_contractionM hd)
    (factorFixMap_mapsTo hd W hε) hk1
    (fun _ hF _ hG => factorFixMap_dist_le hd W hε hF hG)
  obtain ⟨hmem, haeF⟩ := factorFix_repr_spec hd hFS
  have hcoe : ⇑((factorFixMemLp hd W F).toLp
      (contractionMap W d (factorFixRepr (contractionM d) F)))
      =ᵐ[unitμ] contractionMap W d (factorFixRepr (contractionM d) F) :=
    (factorFixMemLp hd W F).coeFn_toLp
  have hfix' : (factorFixMemLp hd W F).toLp
      (contractionMap W d (factorFixRepr (contractionM d) F)) = F := hfix
  rw [hfix'] at hcoe
  have hg : contractionMap W d (factorFixRepr (contractionM d) F)
      =ᵐ[unitμ] factorFixRepr (contractionM d) F := hcoe.symm.trans haeF.symm
  exact ⟨contractionMap W d (factorFixRepr (contractionM d) F), contractionMap_mem hd hmem hε,
    fun x => factorFix_contractionMap_congr W hg x⟩

/-! ## Homogenising the equation

The fixed point solves `T_W(φ^{d-1}) = κφ` with the *normalisation* `∫φ = 1`; the paper's
normalisation is `q = ∫f^d`.  The two are reconciled by a scalar rescaling `f = sφ`.
-/

/-- The pointwise estimate behind `∫φ^{d-1} ≤ ∫φ^d` for a nonnegative `φ` of unit mass:

`a^{d-1} ≤ a^d + (1 - a)`  for `a ≥ 0`, `2 ≤ d`,

an exact factorisation, `a^{d-1} - a^d - (1-a) = (1-a)(a^{d-1}-1) ≤ 0`, the two factors having
opposite signs on either side of `a = 1`.  Integrating against a probability measure of unit
mass kills the linear term, which is why no power-mean inequality is needed. -/
theorem factorFix_pow_sub_one_le (hd : 2 ≤ d) {a : ℝ} (ha : 0 ≤ a) :
    a ^ (d - 1) ≤ a ^ d + (1 - a) := by
  have hsplit : a ^ d = a ^ (d - 1) * a := by
    rw [← pow_succ, show d - 1 + 1 = d from by omega]
  have key : (1 - a) * (a ^ (d - 1) - 1) ≤ 0 := by
    rcases le_total a 1 with h | h
    · have h1 : a ^ (d - 1) ≤ 1 := pow_le_one₀ ha h
      nlinarith
    · have h1 : (1 : ℝ) ≤ a ^ (d - 1) := one_le_pow₀ h
      nlinarith
  rw [hsplit]
  nlinarith [key]

/-- **The rescaling.**  Given a nonnegative `φ ≤ M` solving the *unnormalised* Factor relation
`T_W(φ^{d-1}) = κφ` with `κ > 0` and `κ ≤ ∫φ^d`, the function `f = sφ` with

`s = (κ / ∫φ^d)^{1/2}`

solves `T_W(f^{d-1}) = qf` with `q = ∫f^d = s^{d-2}κ`, and still satisfies `0 ≤ f ≤ M`.

The exponent count is forced: `T_W` is homogeneous of degree `d-1` in `f` and the right-hand
side of degree `1`, so `q` scales like `s^{d-2}`, whereas `∫f^d` scales like `s^d`; the two
match exactly when `s^2 = κ/∫φ^d`.  The hypothesis `κ ≤ ∫φ^d` is what gives `s ≤ 1`, hence the
survival of the uniform bound. -/
theorem factorFix_rescale (hd : 2 ≤ d) (W : Graphon) {κ I : ℝ}
    (hmeas : Measurable φ) (hnn : ∀ x, 0 ≤ φ x) (hbd : ∀ x, φ x ≤ contractionM d)
    (hIeq : ∫ x, φ x ^ d ∂unitμ = I) (hI1 : 1 ≤ I) (hκpos : 0 < κ) (hκI : κ ≤ I)
    (heq : ∀ x, kernelOp W.toFun (fun y => φ y ^ (d - 1)) x = κ * φ x) :
    ∃ f : ℝ → ℝ, ∃ q : ℝ, Measurable f ∧ (∀ x, 0 ≤ f x) ∧ (∀ x, f x ≤ contractionM d) ∧ 0 < q ∧
      (∀ x, kernelOp W.toFun (fun y => f y ^ (d - 1)) x = q * f x) ∧
      q = ∫ x, f x ^ d ∂unitμ := by
  have hI0 : 0 < I := lt_of_lt_of_le zero_lt_one hI1
  have hqI : 0 < κ / I := div_pos hκpos hI0
  have hspos : 0 < Real.sqrt (κ / I) := Real.sqrt_pos.mpr hqI
  have hssq : Real.sqrt (κ / I) ^ 2 = κ / I := Real.sq_sqrt hqI.le
  have hs1 : Real.sqrt (κ / I) ≤ 1 := by
    have hle : κ / I ≤ 1 := (div_le_one hI0).mpr hκI
    calc Real.sqrt (κ / I) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hle
      _ = 1 := Real.sqrt_one
  have hκeq : κ = Real.sqrt (κ / I) ^ 2 * I := by
    rw [hssq]
    exact (div_mul_cancel₀ κ hI0.ne').symm
  refine ⟨fun x => Real.sqrt (κ / I) * φ x, Real.sqrt (κ / I) ^ (d - 2) * κ,
    hmeas.const_mul _, fun x => mul_nonneg hspos.le (hnn x), fun x => ?_,
    mul_pos (pow_pos hspos _) hκpos, fun x => ?_, ?_⟩
  · calc Real.sqrt (κ / I) * φ x ≤ 1 * φ x :=
        mul_le_mul_of_nonneg_right hs1 (hnn x)
      _ = φ x := one_mul _
      _ ≤ contractionM d := hbd x
  · have hpull : kernelOp W.toFun (fun y => (Real.sqrt (κ / I) * φ y) ^ (d - 1)) x
        = Real.sqrt (κ / I) ^ (d - 1)
          * kernelOp W.toFun (fun y => φ y ^ (d - 1)) x := by
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

/-! ## The Factor equation -/

/-- **A solution of the nonlinear Factor equation**, the first half of
`eq:rank-one-orthogonality` of `lem:localization-rank-one`:

for a graphon `W` with `ε = ‖W - r_*‖₄ ≤ ε₁(d)` there are a measurable `f` with
`0 ≤ f ≤ M = 2/r_*` pointwise and a `q > 0` with

`T_W(f^{d-1})(x) = q f(x)` for every `x`,  `q = ∫ f^d`.

`f` is the rescaling `sφ` of the pointwise fixed point `φ` of the normalised contraction map
(`exists_contraction_fixedPoint`), with `s` as in `factorFix_rescale`.  The bound `κ ≤ ∫φ^d` needed
there comes from `W ≤ 1` (which gives `κ = ∫T_W(φ^{d-1}) ≤ ∫φ^{d-1}`) followed by
`factorFix_pow_sub_one_le`.

Neither the orthogonality half of `eq:rank-one-orthogonality` nor the sharp pointwise bound
`f ≤ q^{-1/d}` of `eq:rank-one-orthogonality` is claimed here. -/
theorem exists_factor_solution (hd : 2 ≤ d) (W : Graphon)
    (heps : contractionEps W d ≤ factorEps1 d) :
    ∃ f : ℝ → ℝ, ∃ q : ℝ, Measurable f ∧ (∀ x, 0 ≤ f x) ∧ (∀ x, f x ≤ contractionM d) ∧ 0 < q ∧
      (∀ x, kernelOp W.toFun (fun y => f y ^ (d - 1)) x = q * f x) ∧
      q = ∫ x, f x ^ d ∂unitμ := by
  have hε : contractionEps W d ≤ contractionEps0 d := le_trans heps (factorEps1_le d)
  obtain ⟨φ, hφ, hfix⟩ := exists_contraction_fixedPoint hd W heps
  -- the unnormalised equation, with `κ` the (unfloored) denominator
  have hκpos : 0 < contractionDen W d φ := contractionDen_pos hd
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
      fun x => abs_kernelOp_le W.meas' hφ.measurable_pow (factorFix_abs_W_le W)
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
  exact factorFix_rescale hd W hφ.meas hφ.nonneg hφ.le_bound rfl hI1 hκpos hκI heq

/-! ## Uniqueness -/

/-- **The Banach uniqueness companion.**  Two a.e. fixed points of the normalised contraction map
inside the invariant set `S` are a.e. equal.

This is uniqueness *of the fixed point of `N` in `S`*, which is what the contraction gives (it
does not even need completeness: the contraction estimate alone forces the `L⁴` distance to
vanish).  It is **not** a uniqueness statement for the solutions of the Factor equation, and
`lem:localization-rank-one` asserts none; the Lean's uniqueness of those solutions,
`factorMain_unique`, is obtained from this one in the assembly. -/
theorem factorFix_fixedPoint_unique (hd : 2 ≤ d) (W : Graphon)
    (heps : contractionEps W d ≤ factorEps1 d) (hφ : ContractionMem d φ) (hψ : ContractionMem d ψ)
    (hfφ : contractionMap W d φ =ᵐ[unitμ] φ) (hfψ : contractionMap W d ψ =ᵐ[unitμ] ψ) :
    φ =ᵐ[unitμ] ψ := by
  have hε : contractionEps W d ≤ contractionEps0 d := le_trans heps (factorEps1_le d)
  have hcontr := contractionMap_contraction hd hφ hψ hε
  have hcong : Lnorm unitμ 4 (fun x => contractionMap W d φ x - contractionMap W d ψ x)
      = Lnorm unitμ 4 (fun x => φ x - ψ x) := by
    refine lpBridge_Lnorm_congr 4 ?_
    filter_upwards [hfφ, hfψ] with x hx1 hx2
    rw [hx1, hx2]
  rw [hcong] at hcontr
  have hnn : 0 ≤ Lnorm unitμ 4 (fun x => φ x - ψ x) := Lnorm_nonneg _ _ _
  have hzero : Lnorm unitμ 4 (fun x => φ x - ψ x) = 0 := by
    by_contra hne
    have hpos : 0 < Lnorm unitμ 4 (fun x => φ x - ψ x) := lt_of_le_of_ne hnn (Ne.symm hne)
    have hlt := mul_lt_mul_of_pos_right (factorFix_contr_lt_one hd heps) hpos
    rw [one_mul] at hlt
    linarith
  have hmφ : MemLp φ 4 unitμ := lpBridge_memLp hφ.meas _ (hφ.abs_le hd)
  have hmψ : MemLp ψ 4 unitμ := lpBridge_memLp hψ.meas _ (hψ.abs_le hd)
  have hdist : dist (hmφ.toLp φ) (hmψ.toLp ψ) = 0 := by
    rw [lpBridge_dist_toLp hmφ hmψ, hzero]
  have hLp : hmφ.toLp φ = hmψ.toLp ψ := dist_eq_zero.mp hdist
  have h1 : φ =ᵐ[unitμ] ⇑(hmφ.toLp φ) := hmφ.coeFn_toLp.symm
  rw [hLp] at h1
  exact h1.trans hmψ.coeFn_toLp

end SingularEndpoint

end UpperTailOptimizers
