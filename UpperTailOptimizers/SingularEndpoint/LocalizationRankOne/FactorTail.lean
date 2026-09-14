import UpperTailOptimizers.SingularEndpoint.LocalizationRankOne.FamilyLocalization
import UpperTailOptimizers.SingularEndpoint.LocalizationRankOne.FactorStability
import UpperTailOptimizers.SingularEndpoint.LocalizationRankOne.FactorSolution
import UpperTailOptimizers.SingularEndpoint.AuxiliaryLagrangian.DistributionMeasure

/-!
# The tail mass and a sharpened Factor clause for `lem:localization-rank-one` (Section 5)

`lem:localization-rank-one` of `paper/sections/singular.tex` states the `L⁴` localization
`eq:graphon-quartic-localization`, the decomposition `W = f ⊗ f + E` with
`eq:rank-one-orthogonality`, and the bounds `eq:rank-one-reduction-bounds`; its proof passes
through the moment and cost-gap bounds `eq:moment-and-cost-gap-bounds`.  The `L⁴` localization
is proved in `SingularEndpoint/LocalizationRankOne/L4Bound.lean` (`integral_dist_pow_four_localized`) and
`SingularEndpoint/LocalizationRankOne/FamilyLocalization.lean` (`family_localization`, `family_localization_sq`).
The sharp moment bound `0 ≤ ∫W^d - r_h^d ≤ Mh⁴`, the first half of
`eq:moment-and-cost-gap-bounds`, is `family_ld_sharp` in `SingularEndpoint/LocalizationRankOne/LdSharp.lean`: the
two files above instantiate `gamInt_localized` only for the `∫|W - r_*|⁴` half.  This file
proves two further estimates:

* **`eq:factor-tail-mass`** (stated in `sec:auxiliary-lagrangian` as
  `ν(𝒯_ρ) ≤ ρ^{-4}‖f - u_*‖₄⁴ ≤ C_{d,ρ}h⁴`), here `|{x : f(x) ∉ 𝓝_ρ}| ≤ M_ρ h⁴` for the closed
  window `𝓝_ρ = [u_* - ρ, u_* + ρ]`, which is Chebyshev at exponent four applied to the
  closeness bound `‖f - u_*‖₄ ≤ Cε` (the Lean form of the first bound of
  `eq:rank-one-reduction-bounds`) together with `ε⁴ = ‖W - r_*‖₄⁴ ≤ Mh⁴`
  (`family_localization`);
* a **Factor clause** `‖E‖₂ ≤ Mh²` and `|∫f^d - q_h| ≤ Mh⁴`, which the paper does not state:
  it improves by one resp. two powers of `h` on the rates `‖E‖₂ ≤ C_d h` and
  `|q(f) - q_h| ≤ C_d h²` of `eq:rank-one-reduction-bounds`.  The extra power comes from the
  combined stability inequality of `SingularEndpoint/LocalizationRankOne/FactorStability.lean`: under the
  competitiveness hypotheses the Hölder deficit `(∫W^d)^{m/d} - t(H,W)` is `O(h⁴)`, so

  `c‖E‖₂² ≤ O(h⁴) + C‖E‖₂³`,

  and the cubic term is absorbed once `‖E‖₂` is known small — which it is, by
  `‖E‖₂ ≤ ‖E‖₄ = O(h)` (Cauchy–Schwarz on the probability space `gμ`).  The moment clause
  `|q - q_h| ≤ Mh⁴` is then *derived*, not assumed: the binomial expansion of `∫W^d` (an
  unlabelled display in the proof of `lem:localization-rank-one`) gives
  `|∫W^d - q²| ≤ C‖E‖₂²`, and `∫W^d = q_h² + O(h⁴)` is the sharp `∫W^d` bound.

## What is a hypothesis here

The **existence** of the nonlinear Factor decomposition of `lem:localization-rank-one` is not
used.  Every statement below carries either a
`FactorDecomp d W` or the raw solution data (`f`, `q`, the pointwise Factor equation) as an
explicit hypothesis, exactly as `SingularEndpoint/LocalizationRankOne/FactorStability.lean` and
`SingularEndpoint/LocalizationRankOne/FactorSolution.lean` do, so that the join supplied elsewhere composes with them
without any change of statement.

Likewise the sharp `∫W^d` bound enters the moment clause as the hypothesis
`|∫W^d - q_h²| ≤ Kh⁴` (note `q_h² = r_h^d`, `KKTFamily.graphon_Wmoment`), and the
homomorphism-density bound of `eq:rank-one-reduction-bounds` as `|t(H,W) - q^v| ≤ C₃‖E‖₂³`,
which is how
`SingularEndpoint/LocalizationRankOne/FactorStability.lean` already phrases it.

## Axiom footprint

Every declaration here is `[propext, Classical.choice, Quot.sound]`-only except
`family_factor_tail_mass_of_closeness` and `family_factor_tail_mass`, which additionally carry
`generalized_holder`.  That is inherited verbatim from `family_localization` (whose own
footprint is the same): the localization bound uses generalized Hölder to get `r_h^d ≤ ∫W^d`
from feasibility.  No new axiom is introduced.

## Contents

* `factorTail_Lnorm_four_pow` — `‖g‖₄⁴ = ∫g⁴`, the one `rpow`/`pow` conversion needed;
* `factorTail_mem_centralWindow_iff` — `x ∈ 𝓝_ρ ↔ |x - u_*| ≤ ρ`;
* `factorTail_chebyshev` — Chebyshev at exponent four on `unitμ`;
* `factorTail_mass_le` — `eq:factor-tail-mass` from a raw `L⁴` bound on `f - u_*`;
* `factorTail_mass_of_closeness` — the same with `‖f - u_*‖₄ ≤ Cε` and `ε⁴ ≤ Kh⁴` inserted;
* `family_factor_tail_mass_of_closeness` — **`eq:factor-tail-mass`** along the singular endpoint
  family, with the closeness bound `‖f - u_*‖₄ ≤ Cε` as the only hypothesis about `f`;
* `family_factor_tail_mass` — the same with the nonlinear Factor equation as the only
  hypothesis about `f`, the closeness bound being discharged from it;
* `factorTail_residSq_sq_le_residQuart`, `factorTail_residNorm_le_of_quart` —
  `‖E‖₂ ≤ ‖E‖₄` on the probability square, in the powered form the absorption needs;
* `factorTail_abs_Wmoment_sub_qsq_le` — `|∫W^d - q²| ≤ 2^d20^{d-2}‖E‖₂²`, the two-sided
  companion of `FactorDecomp.Wmoment_sub_qsq_ge`;
* `factorTail_residNorm_le` — **`‖E‖₂ ≤ Mh²`**, with explicit constants;
* `factorTail_abs_qVal_sub_le` — **`|∫f^d - q_h| ≤ Mh⁴`**, with explicit constants;
* `exists_factorTail_factor_clause` — the two together in `∃M, ∃h₀` shape;
* `factorTail_le_of_pow_four_le` — `a⁴ ≤ b⁴ → a ≤ b` for nonnegative reals, shared with
  `SingularEndpoint/LocalizationRankOne/LdSharp.lean`.
-/

namespace UpperTailOptimizers

namespace SingularEndpoint

open Filter MeasureTheory Topology

variable {d : ℕ}

/-! ## Elementary conversions -/

/-- `a ≤ b` from `a⁴ ≤ b⁴` for nonnegative reals: two applications of Mathlib's
`le_of_sq_le_sq`.  The hypothesis `0 ≤ a` is kept for symmetry with the call sites. -/
theorem factorTail_le_of_pow_four_le {a b : ℝ} (_ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : a ^ 4 ≤ b ^ 4) : a ≤ b := by
  have h2 : (a ^ 2) ^ 2 ≤ (b ^ 2) ^ 2 := by
    calc (a ^ 2) ^ 2 = a ^ 4 := by ring
      _ ≤ b ^ 4 := h
      _ = (b ^ 2) ^ 2 := by ring
  exact le_of_sq_le_sq (le_of_sq_le_sq h2 (sq_nonneg b)) hb

/-- **`‖g‖₄⁴ = ∫g⁴`.**  `Lnorm` is defined with a real exponent and `Real.rpow`, while every
localization bound in `SingularEndpoint/` is stated with the natural fourth power; this is the only
conversion between the two vocabularies that the tail estimate needs.  No integrability
hypothesis is required: if `g ∉ L⁴` both sides are the Bochner junk value `0`. -/
theorem factorTail_Lnorm_four_pow {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (g : α → ℝ) : Lnorm μ 4 g ^ (4 : ℕ) = ∫ x, g x ^ (4 : ℕ) ∂μ := by
  have hI : (0 : ℝ) ≤ ∫ x, |g x| ^ (4 : ℝ) ∂μ := integral_abs_rpow_nonneg μ 4 g
  have hcong : ∫ x, |g x| ^ (4 : ℝ) ∂μ = ∫ x, g x ^ (4 : ℕ) ∂μ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show |g x| ^ (4 : ℝ) = g x ^ (4 : ℕ)
    have hx : |g x| ^ (4 : ℝ) = |g x| ^ (4 : ℕ) := by
      rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [hx, Even.pow_abs (n := 4) (by norm_num)]
  have hstep : Lnorm μ 4 g ^ (4 : ℕ) = ∫ x, |g x| ^ (4 : ℝ) ∂μ := by
    unfold Lnorm
    rw [← Real.rpow_natCast ((∫ x, |g x| ^ (4 : ℝ) ∂μ) ^ (1 / (4 : ℝ))) 4,
      ← Real.rpow_mul hI]
    norm_num
  rw [hstep, hcong]

/-! ## `eq:factor-tail-mass` -/

/-- Membership in the coalescence window `𝓝_ρ` is a bound on the distance to `u_*`. -/
theorem factorTail_mem_centralWindow_iff (d : ℕ) (ρ x : ℝ) :
    x ∈ centralWindow d ρ ↔ |x - uStar d| ≤ ρ := by
  rw [centralWindow, Set.mem_Icc, abs_le]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩

/-- **Chebyshev's inequality at exponent four** on the unit interval:
`ρ⁴·|{ρ < |g|}| ≤ ∫g⁴`.

Proved from `∫_S ρ⁴ ≤ ∫_S g⁴ ≤ ∫ g⁴` with `S = {ρ < |g|}`, the same
`setIntegral_mono_on` / `setIntegral_le_integral` sandwich as `DistributionLocal.chebyshev_tail`
one exponent lower. -/
theorem factorTail_chebyshev {g : ℝ → ℝ} (hg : Measurable g)
    (hint : Integrable (fun x => g x ^ (4 : ℕ)) unitμ) {ρ : ℝ} (hρ : 0 < ρ) :
    ρ ^ 4 * (unitμ {x | ρ < |g x|}).toReal ≤ ∫ x, g x ^ (4 : ℕ) ∂unitμ := by
  have hs : MeasurableSet {x : ℝ | ρ < |g x|} := measurableSet_lt measurable_const hg.abs
  have h1 : ρ ^ 4 * (unitμ {x | ρ < |g x|}).toReal
      ≤ ∫ x in {x | ρ < |g x|}, g x ^ (4 : ℕ) ∂unitμ := by
    have h := setIntegral_mono_on (f := fun _ : ℝ => ρ ^ 4)
      (g := fun x : ℝ => g x ^ (4 : ℕ)) (integrable_const _).integrableOn hint.integrableOn
      hs ?_
    · rw [setIntegral_const, smul_eq_mul, measureReal_def] at h
      linarith
    · intro x hx
      have hx' : ρ ≤ |g x| := le_of_lt hx
      calc ρ ^ 4 ≤ |g x| ^ 4 := pow_le_pow_left₀ hρ.le hx' 4
        _ = g x ^ (4 : ℕ) := Even.pow_abs (n := 4) (by norm_num) _
  have h2 : ∫ x in {x | ρ < |g x|}, g x ^ (4 : ℕ) ∂unitμ ≤ ∫ x, g x ^ (4 : ℕ) ∂unitμ :=
    setIntegral_le_integral hint (Filter.Eventually.of_forall fun _ => by positivity)
  linarith

/-- **`eq:factor-tail-mass` from a raw `L⁴` bound.**  If `∫(f - u_*)⁴ ≤ K` then the set on
which `f` leaves the window `𝓝_ρ` has measure at most `K/ρ⁴`.

The factor `f` is required only to be measurable and uniformly bounded — which is what makes
`(f - u_*)⁴` integrable — and no property of `u_*` is used. -/
theorem factorTail_mass_le {f : ℝ → ℝ} (hmeas : Measurable f) {C : ℝ}
    (hbd : ∀ x, |f x| ≤ C) {ρ K : ℝ} (hρ : 0 < ρ)
    (hK : ∫ x, (f x - uStar d) ^ (4 : ℕ) ∂unitμ ≤ K) :
    (unitμ {x | f x ∉ centralWindow d ρ}).toReal ≤ K / ρ ^ 4 := by
  have hgm : Measurable fun x => f x - uStar d := hmeas.sub measurable_const
  have hint : Integrable (fun x => (f x - uStar d) ^ (4 : ℕ)) unitμ := by
    refine Integrable.of_bound (hgm.pow_const 4).aestronglyMeasurable ((C + |uStar d|) ^ 4)
      (Filter.Eventually.of_forall fun x => ?_)
    have hx : |f x - uStar d| ≤ C + |uStar d| := by
      have h1 : |f x - uStar d| ≤ |f x| + |uStar d| := abs_sub _ _
      linarith [hbd x]
    have h0 : (0 : ℝ) ≤ C := le_trans (abs_nonneg _) (hbd x)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (f x - uStar d) ^ (4 : ℕ))]
    calc (f x - uStar d) ^ (4 : ℕ) = |f x - uStar d| ^ 4 := (Even.pow_abs (n := 4) (by norm_num) _).symm
      _ ≤ (C + |uStar d|) ^ 4 := pow_le_pow_left₀ (abs_nonneg _) hx 4
  have hset : {x : ℝ | f x ∉ centralWindow d ρ} = {x : ℝ | ρ < |f x - uStar d|} := by
    ext x
    simp only [Set.mem_ofPred_eq, factorTail_mem_centralWindow_iff, not_le]
  have hcheb := factorTail_chebyshev hgm hint hρ
  rw [hset, le_div_iff₀ (by positivity : (0 : ℝ) < ρ ^ 4)]
  calc (unitμ {x | ρ < |f x - uStar d|}).toReal * ρ ^ 4
      = ρ ^ 4 * (unitμ {x | ρ < |f x - uStar d|}).toReal := by ring
    _ ≤ ∫ x, (f x - uStar d) ^ (4 : ℕ) ∂unitμ := hcheb
    _ ≤ K := hK

/-- **`eq:factor-tail-mass` from `eq:rank-one-reduction-bounds`.**  With
`‖f - u_*‖₄ ≤ Cε` and `ε⁴ ≤ Kh⁴`, the tail mass is at most `(C⁴K/ρ⁴)h⁴`.

This is the shape in which the law layer consumes the estimate: `M_ρ = C⁴K/ρ⁴`.  Neither
`C ≥ 0` nor `ε ≥ 0` is needed: both enter only through the even power `(Cε)⁴`. -/
theorem factorTail_mass_of_closeness {f : ℝ → ℝ} (hmeas : Measurable f) {Cb : ℝ}
    (hbd : ∀ x, |f x| ≤ Cb) {ρ C K ε h : ℝ} (hρ : 0 < ρ)
    (hclose : Lnorm unitμ 4 (fun x => f x - uStar d) ≤ C * ε)
    (heps : ε ^ 4 ≤ K * h ^ 4) :
    (unitμ {x | f x ∉ centralWindow d ρ}).toReal ≤ C ^ 4 * K / ρ ^ 4 * h ^ 4 := by
  have hLnn : 0 ≤ Lnorm unitμ 4 (fun x => f x - uStar d) := Lnorm_nonneg _ _ _
  have hpow : Lnorm unitμ 4 (fun x => f x - uStar d) ^ (4 : ℕ) ≤ (C * ε) ^ 4 :=
    pow_le_pow_left₀ hLnn hclose 4
  rw [factorTail_Lnorm_four_pow] at hpow
  have hK : ∫ x, (f x - uStar d) ^ (4 : ℕ) ∂unitμ ≤ C ^ 4 * K * h ^ 4 := by
    have hCe : (C * ε) ^ 4 = C ^ 4 * ε ^ 4 := by ring
    have hmul : C ^ 4 * ε ^ 4 ≤ C ^ 4 * (K * h ^ 4) :=
      mul_le_mul_of_nonneg_left heps (by positivity)
    calc ∫ x, (f x - uStar d) ^ (4 : ℕ) ∂unitμ ≤ (C * ε) ^ 4 := hpow
      _ = C ^ 4 * ε ^ 4 := hCe
      _ ≤ C ^ 4 * (K * h ^ 4) := hmul
      _ = C ^ 4 * K * h ^ 4 := by ring
  have hmass := factorTail_mass_le (d := d) hmeas hbd hρ hK
  calc (unitμ {x | f x ∉ centralWindow d ρ}).toReal ≤ C ^ 4 * K * h ^ 4 / ρ ^ 4 := hmass
    _ = C ^ 4 * K / ρ ^ 4 * h ^ 4 := by ring

/-- **`eq:factor-tail-mass` along the singular endpoint family, from the closeness clause.**

For every `ρ > 0` and every constant `C` there are `M_ρ > 0` and `h_ρ > 0` such that, for
`0 < h < h_ρ`, every competitor `W` at `(p_h, r_h)` no more expensive than `W_h`, and every
bounded measurable `f` obeying the closeness bound `‖f - u_*‖₄ ≤ Cε` (the Lean form of the
first bound of `eq:rank-one-reduction-bounds`),

`|{x : f(x) ∉ 𝓝_ρ}| ≤ M_ρ h⁴`.

The only family input is `family_localization` (`ε⁴ = ∫|W - r_*|⁴ ≤ Mh⁴`); the constant is
`M_ρ = C⁴M/ρ⁴`.  Taking the closeness bound as a *hypothesis* rather than re-deriving it from
the nonlinear Factor equation is what lets the estimate be applied to the decomposition
produced by `family_factor_clause`, which forwards exactly this bound: see
`SingularEndpoint/LocalizationRankOne/LocalizationMain.lean`.  `family_factor_tail_mass` below is the specialisation in
which the hypothesis is discharged from the Factor equation instead. -/
theorem family_factor_tail_mass_of_closeness (hd : 2 ≤ d) {V : Type*} [Fintype V]
    [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj] (hreg : ∀ v, H.degree v = d)
    (hcard : 1 ≤ H.edgeFinset.card) (B : KKTFamily d) {ρ C : ℝ} (hρ : 0 < ρ) :
    ∃ Mρ : ℝ, 0 < Mρ ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ (h : ℝ) (hh : |h| < B.h₀), 0 < h → h < δ →
        ∀ W : Graphon, B.rVal h ^ H.edgeFinset.card ≤ W.tDensity H →
          W.Ip (B.p h) ≤ (B.graphon hh).Ip (B.p h) →
          ∀ (f : ℝ → ℝ) (Cb : ℝ), Measurable f → (∀ x, |f x| ≤ Cb) →
            Lnorm unitμ 4 (fun x => f x - uStar d) ≤ C * contractionEps W d →
              (unitμ {x | f x ∉ centralWindow d ρ}).toReal ≤ Mρ * h ^ 4 := by
  obtain ⟨M, hM0, δ, hδ, hbnd⟩ := family_localization hd H hreg hcard B
  have hMρ0 : (0 : ℝ) ≤ C ^ 4 * M / ρ ^ 4 :=
    div_nonneg (mul_nonneg (by positivity) hM0.le) (by positivity)
  refine ⟨C ^ 4 * M / ρ ^ 4 + 1, by linarith, δ, hδ, ?_⟩
  intro h hh hpos hlt W hfeas hcost f Cb hmeas hbd hclose
  -- `ε⁴ = ∫|W - r_*|⁴ ≤ Mh⁴`
  have hL : contractionEps W d ^ (4 : ℕ) = ∫ z, (W.toFun z.1 z.2 - rStar d) ^ (4 : ℕ) ∂gμ :=
    factorTail_Lnorm_four_pow gμ fun z : ℝ × ℝ => W.toFun z.1 z.2 - rStar d
  have hcong : ∫ z, (W.toFun z.1 z.2 - rStar d) ^ (4 : ℕ) ∂gμ
      = ∫ z, |W.toFun z.1 z.2 - rStar d| ^ 4 ∂gμ :=
    integral_congr_ae (Filter.Eventually.of_forall fun z => (Even.pow_abs (n := 4) (by norm_num) _).symm)
  have hepspow : contractionEps W d ^ (4 : ℕ) ≤ M * h ^ 4 := by
    rw [hL, hcong]
    exact hbnd h hh hpos hlt W hfeas hcost
  have hmain := factorTail_mass_of_closeness (d := d) hmeas hbd hρ hclose hepspow
  exact le_trans hmain (mul_le_mul_of_nonneg_right (by linarith) (by positivity))

/-- **`eq:factor-tail-mass` along the singular endpoint family.**

For every `ρ > 0` there are `M_ρ > 0` and `h_ρ > 0` such that, for `0 < h < h_ρ`, every
competitor `W` at `(p_h, r_h)` no more expensive than `W_h`, and every nonnegative bounded
solution `f` of the nonlinear Factor equation `T_W(f^{d-1}) = qf` with `q = ∫f^d ≥ 2^{-d}`,

`|{x : f(x) ∉ 𝓝_ρ}| ≤ M_ρ h⁴`.

This is `family_factor_tail_mass_of_closeness` at `C = C(d)`, with the closeness hypothesis
discharged by `factorSolution_closeness` (`‖f - u_*‖₄ ≤ C(d)ε`).  Nothing about the
*existence* of `f` is used. -/
theorem family_factor_tail_mass (hd : 2 ≤ d) {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (hreg : ∀ v, H.degree v = d)
    (hcard : 1 ≤ H.edgeFinset.card) (B : KKTFamily d) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ Mρ : ℝ, 0 < Mρ ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ (h : ℝ) (hh : |h| < B.h₀), 0 < h → h < δ →
        ∀ W : Graphon, B.rVal h ^ H.edgeFinset.card ≤ W.tDensity H →
          W.Ip (B.p h) ≤ (B.graphon hh).Ip (B.p h) →
          ∀ (f : ℝ → ℝ) (q : ℝ), Measurable f → (∀ x, 0 ≤ f x) → (∀ x, f x ≤ contractionM d) →
            0 < q → (∀ x, kernelOp W.toFun (fun y => f y ^ (d - 1)) x = q * f x) →
            q = ∫ x, f x ^ d ∂unitμ → (1 : ℝ) / 2 ^ d ≤ q →
              (unitμ {x | f x ∉ centralWindow d ρ}).toReal ≤ Mρ * h ^ 4 := by
  obtain ⟨Mρ, hMρ0, δ, hδ, hbnd⟩ := family_factor_tail_mass_of_closeness
    (C := factorSolutionCloseConst d) hd H hreg hcard B hρ
  refine ⟨Mρ, hMρ0, δ, hδ, ?_⟩
  intro h hh hpos hlt W hfeas hcost f q hmeas hnn hMb hq heq hqdef hqlow
  have hclose := factorSolution_closeness (W := W) hd hmeas hnn hMb hq heq hqdef hqlow
  have hfirst : Lnorm unitμ 4 (fun x => f x - uStar d)
      ≤ factorSolutionCloseConst d * contractionEps W d := by
    have hE : 0 ≤ Lnorm gμ 4 fun z : ℝ × ℝ => W.toFun z.1 z.2 - f z.1 * f z.2 :=
      Lnorm_nonneg _ _ _
    linarith [hclose]
  refine hbnd h hh hpos hlt W hfeas hcost f (contractionM d) hmeas (fun x => ?_) hfirst
  rw [abs_of_nonneg (hnn x)]
  exact hMb x

/-! ## `‖E‖₂ ≤ ‖E‖₄` on the probability square -/

variable {W : Graphon}

/-- `‖E‖₂⁴ ≤ ‖E‖₄⁴`, i.e. `(∫E²)² ≤ ∫E⁴`: Cauchy–Schwarz applied to `E²`. -/
theorem factorTail_residSq_sq_le_residQuart (P : FactorDecomp d W) :
    P.residSq ^ 2 ≤ P.residQuart := by
  have hq : Integrable (fun z : ℝ × ℝ => (P.resid z.1 z.2 ^ 2) ^ 2) gμ := by
    refine P.integrable_resid_quart.congr (Filter.Eventually.of_forall fun z => ?_)
    ring
  have h := sq_integral_le_integral_sq (f := fun z : ℝ × ℝ => P.resid z.1 z.2 ^ 2)
    P.integrable_resid_sq hq
  have hcong : ∫ z, (P.resid z.1 z.2 ^ 2) ^ 2 ∂gμ = P.residQuart :=
    integral_congr_ae (Filter.Eventually.of_forall fun z => by ring)
  rw [hcong] at h
  exact h

/-- **`‖E‖₂ ≤ (K)^{1/4}h`** from `‖E‖₄⁴ ≤ Kh⁴`: the smallness of `‖E‖₂` that the cubic
absorption below needs, obtained from an `L⁴` bound on `E` alone (the paper's proof of
`lem:localization-rank-one` likewise bounds `‖E‖₂ ≤ ‖E‖₄`).
-/
theorem factorTail_residNorm_le_of_quart (P : FactorDecomp d W) {A h : ℝ} (hA : 0 ≤ A)
    (hh : 0 ≤ h) (hquart : P.residQuart ≤ (A * h) ^ 4) : P.residNorm ≤ A * h := by
  refine factorTail_le_of_pow_four_le P.residNorm_nonneg (by positivity) ?_
  have hsq : P.residNorm ^ 4 = P.residSq ^ 2 := by
    rw [show P.residNorm ^ 4 = (P.residNorm ^ 2) ^ 2 by ring, P.residNorm_sq]
  rw [hsq]
  exact le_trans (factorTail_residSq_sq_le_residQuart P) hquart

/-! ## The two-sided moment expansion -/

/-- **`|∫W^d - q²| ≤ 2^d20^{d-2}‖E‖₂²`**, the two-sided companion of
`FactorDecomp.Wmoment_sub_qsq_ge`.

Every term of the exact expansion `FactorDecomp.Wmoment_eq` (the binomial expansion in the proof
of `lem:localization-rank-one`) carries `E^{d-k}` with `d - k ≥ 2`, so bounding
`|A| ≤ 4` and `|E| ≤ 5` on the excess degree gives `|∫∫A^kE^{d-k}| ≤ 20^{d-2}∫∫E²`, and
`∑_k binom(d,k) ≤ 2^d`.  Unlike `abs_tail_le`, which peels the quadratic term first and
bounds the rest by `∫|E|³`, this keeps the quadratic term inside the estimate — that is
exactly what is wanted for the moment clause, where no coercivity is needed. -/
theorem factorTail_abs_Wmoment_sub_qsq_le (hd : 2 ≤ d) (P : FactorDecomp d W) :
    |W.Wmoment d - P.qVal ^ 2| ≤ tailConst d * P.residSq := by
  have hsq0 : 0 ≤ P.residSq := P.residSq_nonneg
  have hexp := P.Wmoment_eq (by omega : 1 ≤ d)
  have hinner : ∀ k ∈ Finset.range (d - 1),
      |(d.choose k : ℝ) * ∫ z, P.rankOne z.1 z.2 ^ k * P.resid z.1 z.2 ^ (d - k) ∂gμ|
        ≤ (d.choose k : ℝ) * ((20 : ℝ) ^ (d - 2) * P.residSq) := by
    intro k hk
    have hk' : k < d - 1 := Finset.mem_range.mp hk
    obtain ⟨j, hj⟩ : ∃ j, d - k = j + 2 := ⟨d - k - 2, by omega⟩
    have hjd : j ≤ d - 2 := by omega
    have hkd : k ≤ d - 2 := by omega
    have hpt : ∀ z : ℝ × ℝ, |P.rankOne z.1 z.2 ^ k * P.resid z.1 z.2 ^ (d - k)|
        ≤ (20 : ℝ) ^ (d - 2) * P.resid z.1 z.2 ^ 2 := by
      intro z
      rw [abs_mul, abs_pow, abs_pow, hj, pow_add]
      have e1 : |P.rankOne z.1 z.2| ^ k ≤ (4 : ℝ) ^ (d - 2) :=
        le_trans (pow_le_pow_left₀ (abs_nonneg _) (P.abs_rankOne_le z.1 z.2) k)
          (pow_le_pow_right₀ (by norm_num) hkd)
      have e2 : |P.resid z.1 z.2| ^ j ≤ (5 : ℝ) ^ (d - 2) :=
        le_trans (pow_le_pow_left₀ (abs_nonneg _) (P.abs_resid_le z.1 z.2) j)
          (pow_le_pow_right₀ (by norm_num) hjd)
      have e3 : |P.resid z.1 z.2| ^ 2 = P.resid z.1 z.2 ^ 2 := sq_abs _
      rw [e3]
      calc |P.rankOne z.1 z.2| ^ k * (|P.resid z.1 z.2| ^ j * P.resid z.1 z.2 ^ 2)
          ≤ (4 : ℝ) ^ (d - 2) * ((5 : ℝ) ^ (d - 2) * P.resid z.1 z.2 ^ 2) :=
            mul_le_mul e1 (mul_le_mul_of_nonneg_right e2 (sq_nonneg _))
              (mul_nonneg (pow_nonneg (abs_nonneg _) j) (sq_nonneg _)) (by positivity)
        _ = (20 : ℝ) ^ (d - 2) * P.resid z.1 z.2 ^ 2 := by
            rw [show (20 : ℝ) = 4 * 5 by norm_num, mul_pow]
            ring
    have hI : |∫ z, P.rankOne z.1 z.2 ^ k * P.resid z.1 z.2 ^ (d - k) ∂gμ|
        ≤ (20 : ℝ) ^ (d - 2) * P.residSq := by
      calc |∫ z, P.rankOne z.1 z.2 ^ k * P.resid z.1 z.2 ^ (d - k) ∂gμ|
          ≤ ∫ z, |P.rankOne z.1 z.2 ^ k * P.resid z.1 z.2 ^ (d - k)| ∂gμ :=
            abs_integral_le_integral_abs
        _ ≤ ∫ z, (20 : ℝ) ^ (d - 2) * P.resid z.1 z.2 ^ 2 ∂gμ :=
            integral_mono (P.integrable_rankOne_pow_mul_resid_pow k (d - k)).abs
              (P.integrable_resid_sq.const_mul _) hpt
        _ = (20 : ℝ) ^ (d - 2) * P.residSq := by rw [integral_const_mul]; rfl
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg (d.choose k) : (0 : ℝ) ≤ _)]
    exact mul_le_mul_of_nonneg_left hI (Nat.cast_nonneg _)
  have hbin : (∑ k ∈ Finset.range (d - 1), (d.choose k : ℝ)) ≤ 2 ^ d := by
    have hsub : Finset.range (d - 1) ⊆ Finset.range (d + 1) := by
      intro x hx
      simp only [Finset.mem_range] at hx ⊢
      omega
    have h1 : (∑ k ∈ Finset.range (d - 1), (d.choose k : ℝ))
        ≤ ∑ k ∈ Finset.range (d + 1), (d.choose k : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub fun i _ _ => Nat.cast_nonneg _
    have h2 : (∑ k ∈ Finset.range (d + 1), (d.choose k : ℝ)) = 2 ^ d := by
      exact_mod_cast Nat.sum_range_choose d
    linarith
  have hsum : |∑ k ∈ Finset.range (d - 1), (d.choose k : ℝ) *
        ∫ z, P.rankOne z.1 z.2 ^ k * P.resid z.1 z.2 ^ (d - k) ∂gμ|
      ≤ tailConst d * P.residSq := by
    calc |∑ k ∈ Finset.range (d - 1), (d.choose k : ℝ) *
          ∫ z, P.rankOne z.1 z.2 ^ k * P.resid z.1 z.2 ^ (d - k) ∂gμ|
        ≤ ∑ k ∈ Finset.range (d - 1), |(d.choose k : ℝ) *
            ∫ z, P.rankOne z.1 z.2 ^ k * P.resid z.1 z.2 ^ (d - k) ∂gμ| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.range (d - 1), (d.choose k : ℝ) * ((20 : ℝ) ^ (d - 2) * P.residSq) :=
          Finset.sum_le_sum hinner
      _ = (∑ k ∈ Finset.range (d - 1), (d.choose k : ℝ))
            * ((20 : ℝ) ^ (d - 2) * P.residSq) := by rw [Finset.sum_mul]
      _ ≤ (2 : ℝ) ^ d * ((20 : ℝ) ^ (d - 2) * P.residSq) :=
          mul_le_mul_of_nonneg_right hbin (mul_nonneg (by positivity) hsq0)
      _ = tailConst d * P.residSq := by unfold tailConst; ring
  have hrw : W.Wmoment d - P.qVal ^ 2
      = ∑ k ∈ Finset.range (d - 1), (d.choose k : ℝ) *
          ∫ z, P.rankOne z.1 z.2 ^ k * P.resid z.1 z.2 ^ (d - k) ∂gμ := by
    rw [hexp]; ring
  rw [hrw]
  exact hsum

/-! ## The cubic absorption -/

/-- **The quadratic-inequality step.**  From `cS² ≤ Bh⁴ + C₃S³` with `S ≤ Ah` and
`C₃Ah ≤ c/2` one gets `S ≤ √(2B/c)h²`: the cubic term eats at most half of the coercive
term, and what remains is `(c/2)S² ≤ Bh⁴`.

The proof of `lem:localization-rank-one` has no such step (its bound on `‖E‖₂` is only
`O(h)`); the paper absorbs a cubic `‖E‖₂³` term into half of a quadratic one in the same way
at the end of the proof of `lem:graphon-lagrangian-bound`, by decreasing `h_ρ` so that
`C_{d,m}‖E‖₂ ≤ C_{d,ρ}^{-1}/2`.  It is the same idiom as `DistributionLocal.le_of_sq_bound`. -/
private theorem factorTail_absorb {c C₃ A B S h : ℝ} (hc : 0 < c) (hC₃ : 0 ≤ C₃)
    (hB : 0 ≤ B) (_hS : 0 ≤ S) (hh : 0 < h) (hSA : S ≤ A * h)
    (hthr : C₃ * (A * h) ≤ c / 2)
    (hquad : c * S ^ 2 ≤ B * h ^ 4 + C₃ * S ^ 3) :
    S ≤ Real.sqrt (2 * B / c) * h ^ 2 := by
  have hCS : C₃ * S ≤ c / 2 := le_trans (mul_le_mul_of_nonneg_left hSA hC₃) hthr
  have hcube : C₃ * S ^ 3 ≤ c / 2 * S ^ 2 := by nlinarith [sq_nonneg S]
  have hhalf : c / 2 * S ^ 2 ≤ B * h ^ 4 := by linarith
  have hsq : S ^ 2 ≤ 2 * B / c * h ^ 4 := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hc]
    nlinarith
  have hT0 : (0 : ℝ) ≤ Real.sqrt (2 * B / c) * h ^ 2 := by positivity
  refine le_of_sq_le_sq ?_ hT0
  have hTsq : (Real.sqrt (2 * B / c) * h ^ 2) ^ 2 = 2 * B / c * h ^ 4 := by
    rw [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 * B / c)]
    ring
  rw [hTsq]
  exact hsq

/-! ## The Factor clause -/

/-- **`‖E‖₂ ≤ Mh²`**, with explicit constants.

The hypotheses are those of `FactorDecomp.holder_stability` (the combined stability inequality
of `SingularEndpoint/LocalizationRankOne/FactorStability.lean`, with the homomorphism-density bound of
`eq:rank-one-reduction-bounds` as `hT`) together with two competitiveness inputs:

* `hloc : ‖W - r_*‖₄⁴ ≤ Kh⁴` — the `L⁴` localization `eq:graphon-quartic-localization`;
* `hdef : (∫W^d)^{m/d} - t(H,W) ≤ Kh⁴` — the Hölder deficit, which is `O(h⁴)` because
  `t(H,W) ≥ r_h^m` and the sharp `∫W^d` bound;

and the smallness threshold `hthr`, which says that the cubic term of the combined
stability inequality is dominated by half the coercive term.  The
bound `‖E‖₂ ≤ (C₂K)^{1/4}h` making that possible is `factorTail_residNorm_le_of_quart`. -/
theorem factorTail_residNorm_le (hd : 2 ≤ d) {v m : ℕ} (hv : 2 ≤ v) (hvm : 2 * m = v * d)
    (P : FactorDecomp d W) {C₁ C₂ C₃ q₀ T K h : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hC₃ : 0 ≤ C₃) (hq₀ : 0 < q₀) (hq : q₀ ≤ P.qVal) (hK : 0 ≤ K) (hh : 0 < h)
    (hA4 : P.rankOneQuart ≤ C₁ * defectQuart d W)
    (hE4 : P.residQuart ≤ C₂ * defectQuart d W)
    (hT : |T - P.qVal ^ v| ≤ C₃ * P.residNorm ^ 3)
    (hloc : defectQuart d W ≤ K * h ^ 4)
    (hdef : W.Wmoment d ^ ((m : ℝ) / (d : ℝ)) - T ≤ K * h ^ 4)
    (hthr : C₃ * (Real.sqrt (Real.sqrt (C₂ * K)) * h) ≤ stabCoer d v q₀ / 2) :
    P.residNorm
      ≤ Real.sqrt (2 * ((1 + stabQuart d v C₁ C₂) * K) / stabCoer d v q₀) * h ^ 2 := by
  have hcoer : 0 < stabCoer d v q₀ := stabCoer_pos hd hv hq₀
  have hquart : (0 : ℝ) ≤ stabQuart d v C₁ C₂ := stabQuart_nonneg hd hC₁ hC₂
  -- `‖E‖₂ ≤ (C₂K)^{1/4}h`, the smallness needed for the absorption
  have hCK : (0 : ℝ) ≤ C₂ * K := mul_nonneg hC₂ hK
  have hApow : (Real.sqrt (Real.sqrt (C₂ * K)) * h) ^ 4 = C₂ * K * h ^ 4 := by
    rw [mul_pow, show Real.sqrt (Real.sqrt (C₂ * K)) ^ 4
        = (Real.sqrt (Real.sqrt (C₂ * K)) ^ 2) ^ 2 by ring,
      Real.sq_sqrt (Real.sqrt_nonneg _), Real.sq_sqrt hCK]
  have hEsmall : P.residNorm ≤ Real.sqrt (Real.sqrt (C₂ * K)) * h := by
    refine factorTail_residNorm_le_of_quart P (Real.sqrt_nonneg _) hh.le ?_
    rw [hApow]
    calc P.residQuart ≤ C₂ * defectQuart d W := hE4
      _ ≤ C₂ * (K * h ^ 4) := mul_le_mul_of_nonneg_left hloc hC₂
      _ = C₂ * K * h ^ 4 := by ring
  -- the combined stability inequality with the two `O(h⁴)` inputs inserted
  have hstab := P.holder_stability hd hv hvm hC₁ hC₂ hq₀ hq hA4 hE4 hT
  have hquad : stabCoer d v q₀ * P.residNorm ^ 2
      ≤ (1 + stabQuart d v C₁ C₂) * K * h ^ 4 + C₃ * P.residNorm ^ 3 := by
    have hqK : stabQuart d v C₁ C₂ * defectQuart d W ≤ stabQuart d v C₁ C₂ * (K * h ^ 4) :=
      mul_le_mul_of_nonneg_left hloc hquart
    linarith
  exact factorTail_absorb hcoer hC₃ (mul_nonneg (by linarith) hK) P.residNorm_nonneg hh
    hEsmall hthr hquad

/-- **`|∫f^d - q_h| ≤ Mh⁴`**, the moment clause, derived from `‖E‖₂ ≤ M_Eh²`.

The two ingredients are `factorTail_abs_Wmoment_sub_qsq_le` (`|∫W^d - q²| ≤ C‖E‖₂²`, from the
exact expansion `FactorDecomp.Wmoment_eq`) and the sharp `∫W^d` bound in the form
`|∫W^d - q_h²| ≤ Kh⁴`, which is the hypothesis `hmom` — recall `q_h² = r_h^d`
(`KKTFamily.graphon_Wmoment`).  Together they give `|q² - q_h²| = O(h⁴)`, and the lower
bound `q ≥ q₀ > 0` divides it down to `|q - q_h| = O(h⁴)`. -/
theorem factorTail_abs_qVal_sub_le (hd : 2 ≤ d) (P : FactorDecomp d W)
    {q₀ qh ME K h : ℝ} (hq₀ : 0 < q₀) (hq : q₀ ≤ P.qVal) (hqh : 0 ≤ qh) (_hME : 0 ≤ ME)
    (hmom : |W.Wmoment d - qh ^ 2| ≤ K * h ^ 4)
    (hres : P.residNorm ≤ ME * h ^ 2) :
    |P.qVal - qh| ≤ (K + tailConst d * ME ^ 2) / q₀ * h ^ 4 := by
  have hh4 : (0 : ℝ) ≤ h ^ 4 := by positivity
  have hq0 : 0 < P.qVal := lt_of_lt_of_le hq₀ hq
  -- `‖E‖₂² ≤ M_E²h⁴`
  have hsq : P.residSq ≤ ME ^ 2 * h ^ 4 := by
    have h1 : P.residNorm ^ 2 ≤ (ME * h ^ 2) ^ 2 :=
      pow_le_pow_left₀ P.residNorm_nonneg hres 2
    rw [P.residNorm_sq] at h1
    calc P.residSq ≤ (ME * h ^ 2) ^ 2 := h1
      _ = ME ^ 2 * h ^ 4 := by ring
  -- `|∫W^d - q²| ≤ C‖E‖₂²`
  have htail : |W.Wmoment d - P.qVal ^ 2| ≤ tailConst d * ME ^ 2 * h ^ 4 := by
    have h1 := factorTail_abs_Wmoment_sub_qsq_le hd P
    have h2 : tailConst d * P.residSq ≤ tailConst d * (ME ^ 2 * h ^ 4) :=
      mul_le_mul_of_nonneg_left hsq (tailConst_pos d).le
    calc |W.Wmoment d - P.qVal ^ 2| ≤ tailConst d * P.residSq := h1
      _ ≤ tailConst d * (ME ^ 2 * h ^ 4) := h2
      _ = tailConst d * ME ^ 2 * h ^ 4 := by ring
  -- `|q² - q_h²| = O(h⁴)`
  have hdiffsq : |P.qVal ^ 2 - qh ^ 2| ≤ (K + tailConst d * ME ^ 2) * h ^ 4 := by
    have h1 : |P.qVal ^ 2 - qh ^ 2|
        ≤ |P.qVal ^ 2 - W.Wmoment d| + |W.Wmoment d - qh ^ 2| := by
      have hadd := abs_add_le (P.qVal ^ 2 - W.Wmoment d) (W.Wmoment d - qh ^ 2)
      have he : P.qVal ^ 2 - W.Wmoment d + (W.Wmoment d - qh ^ 2) = P.qVal ^ 2 - qh ^ 2 := by
        ring
      rwa [he] at hadd
    have h2 : |P.qVal ^ 2 - W.Wmoment d| = |W.Wmoment d - P.qVal ^ 2| := abs_sub_comm _ _
    calc |P.qVal ^ 2 - qh ^ 2|
        ≤ |P.qVal ^ 2 - W.Wmoment d| + |W.Wmoment d - qh ^ 2| := h1
      _ = |W.Wmoment d - P.qVal ^ 2| + |W.Wmoment d - qh ^ 2| := by rw [h2]
      _ ≤ tailConst d * ME ^ 2 * h ^ 4 + K * h ^ 4 := add_le_add htail hmom
      _ = (K + tailConst d * ME ^ 2) * h ^ 4 := by ring
  -- divide by `q + q_h ≥ q₀`
  have hfact : |P.qVal ^ 2 - qh ^ 2| = |P.qVal - qh| * (P.qVal + qh) := by
    rw [show P.qVal ^ 2 - qh ^ 2 = (P.qVal - qh) * (P.qVal + qh) by ring, abs_mul,
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ P.qVal + qh)]
  have hlow : q₀ * |P.qVal - qh| ≤ |P.qVal - qh| * (P.qVal + qh) := by
    have hle : q₀ ≤ P.qVal + qh := by linarith
    have hmul := mul_le_mul_of_nonneg_left hle (abs_nonneg (P.qVal - qh))
    linarith
  rw [div_mul_eq_mul_div, le_div_iff₀ hq₀]
  calc |P.qVal - qh| * q₀ = q₀ * |P.qVal - qh| := by ring
    _ ≤ |P.qVal - qh| * (P.qVal + qh) := hlow
    _ = |P.qVal ^ 2 - qh ^ 2| := hfact.symm
    _ ≤ (K + tailConst d * ME ^ 2) * h ^ 4 := hdiffsq

/-- **A sharpened Factor clause for `lem:localization-rank-one`**, in `∃ M, ∃ h₀` shape.

There are `M ≥ 0` and `h₀ > 0` such that for every `0 < h < h₀`, every competitor `W` with a
Factor decomposition `P` whose closeness constants are `C₁, C₂`, whose rank-one moment is
bounded below by `q₀`, and which satisfies the three `O(h⁴)` competitiveness inputs, one has

`‖E‖₂ ≤ Mh²`   and   `|∫f^d - q_h| ≤ Mh⁴`,

which improve by one resp. two powers of `h` on the bounds `‖E‖₂ ≤ C_d h` and
`|q(f) - q_h| ≤ C_d h²` of `eq:rank-one-reduction-bounds`.

The threshold `h₀ = c/(2(C₃(C₂K)^{1/4} + 1))` is what lets `factorTail_absorb` absorb the
cubic term of the combined stability inequality into half of its coercive term;
`c = stabCoer d v q₀` is the coercivity constant of that inequality
(`FactorDecomp.holder_stability`). -/
theorem exists_factorTail_factor_clause (hd : 2 ≤ d) {v m : ℕ} (hv : 2 ≤ v)
    (hvm : 2 * m = v * d) {C₁ C₂ C₃ q₀ K : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hC₃ : 0 ≤ C₃)
    (hq₀ : 0 < q₀) (hK : 0 ≤ K) :
    ∃ M : ℝ, 0 < M ∧ ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ h : ℝ, 0 < h → h < h₀ →
      ∀ (W' : Graphon) (P : FactorDecomp d W') (T qh : ℝ),
        q₀ ≤ P.qVal → 0 ≤ qh →
        P.rankOneQuart ≤ C₁ * defectQuart d W' →
        P.residQuart ≤ C₂ * defectQuart d W' →
        |T - P.qVal ^ v| ≤ C₃ * P.residNorm ^ 3 →
        defectQuart d W' ≤ K * h ^ 4 →
        W'.Wmoment d ^ ((m : ℝ) / (d : ℝ)) - T ≤ K * h ^ 4 →
        |W'.Wmoment d - qh ^ 2| ≤ K * h ^ 4 →
          P.residNorm ≤ M * h ^ 2 ∧ |P.qVal - qh| ≤ M * h ^ 4 := by
  have hcoer : 0 < stabCoer d v q₀ := stabCoer_pos hd hv hq₀
  have hquart : (0 : ℝ) ≤ stabQuart d v C₁ C₂ := stabQuart_nonneg hd hC₁ hC₂
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = Real.sqrt (Real.sqrt (C₂ * K)) := ⟨_, rfl⟩
  have hA0 : (0 : ℝ) ≤ A := by rw [hAdef]; exact Real.sqrt_nonneg _
  obtain ⟨ME, hMEdef⟩ : ∃ ME : ℝ,
      ME = Real.sqrt (2 * ((1 + stabQuart d v C₁ C₂) * K) / stabCoer d v q₀) := ⟨_, rfl⟩
  have hME0 : (0 : ℝ) ≤ ME := by rw [hMEdef]; exact Real.sqrt_nonneg _
  have hKq : (0 : ℝ) ≤ (K + tailConst d * ME ^ 2) / q₀ :=
    div_nonneg (add_nonneg hK (mul_nonneg (tailConst_pos d).le (sq_nonneg ME))) hq₀.le
  refine ⟨ME + (K + tailConst d * ME ^ 2) / q₀ + 1, by linarith,
    stabCoer d v q₀ / (2 * (C₃ * A + 1)),
    div_pos hcoer (by linarith [mul_nonneg hC₃ hA0]), ?_⟩
  intro h hh0 hhlt W' P T qh hq hqh hA4 hE4 hT hloc hdef hmom
  have hthr : C₃ * (Real.sqrt (Real.sqrt (C₂ * K)) * h) ≤ stabCoer d v q₀ / 2 := by
    have hpos : (0 : ℝ) < 2 * (C₃ * A + 1) := by linarith [mul_nonneg hC₃ hA0]
    have h1 : h * (2 * (C₃ * A + 1)) < stabCoer d v q₀ := (lt_div_iff₀ hpos).mp hhlt
    rw [← hAdef]
    nlinarith [hh0.le, mul_nonneg hC₃ hA0]
  have hres := factorTail_residNorm_le (W := W') hd hv hvm P hC₁ hC₂ hC₃ hq₀ hq hK hh0
    hA4 hE4 hT hloc hdef hthr
  rw [← hMEdef] at hres
  have hmomcl := factorTail_abs_qVal_sub_le (W := W') hd P hq₀ hq hqh hME0 hmom hres
  constructor
  · exact le_trans hres (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
  · exact le_trans hmomcl (mul_le_mul_of_nonneg_right (by linarith) (by positivity))

end SingularEndpoint

end UpperTailOptimizers
