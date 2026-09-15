import UpperTailOptimizers.SingularEndpoint.LocalizationRankOne.LdSharp

/-!
# A combined localization theorem for `lem:localization-rank-one` (Section 5)

`singular_endpoint_localization` gives **one** pair of
constants `(M, h₀)` for which four bounds hold simultaneously, for every graphon `W` that is
feasible at `(p_h, r_h)` and costs no more than the family candidate `W_h`:

* `∫|W - r_*|² ≤ Mh²` and `∫|W - r_*|⁴ ≤ Mh⁴` — the second is
  `eq:graphon-quartic-localization` raised to the fourth power, the first a Lean companion;
* the sharp `∫W^d` bound — `0 ≤ ∫W^d - r_h^d ≤ Mh⁴`, the moment half of
  `eq:moment-and-cost-gap-bounds` in the proof of `lem:localization-rank-one`;
* the nonlinear Factor decomposition `W = f ⊗ f + E` with `‖E‖₂ ≤ Mh²` and
  `|∫f^d - q_h| ≤ Mh⁴`, sharper than the rates `‖E‖₂ ≤ C_d h` and `|q(f) - q_h| ≤ C_d h²` of
  `eq:rank-one-reduction-bounds`;
* `eq:factor-tail-mass` (stated in `sec:auxiliary-lagrangian`) — `|{x : f(x) ∉ 𝓝_ρ}| ≤ M_ρ h⁴`.

This is a Lean strengthening rather than the statement of the lemma; the lemma in the paper's
form is `localization_rank_one_reduction` (`SingularEndpoint/LocalizationRankOne/LocalizationRankOne.lean`).

The four were proved separately, each with its own `(M, δ)`:  `family_localization_sq` and
`family_localization` (`SingularEndpoint/LocalizationRankOne/FamilyLocalization.lean`), `family_ld_sharp` and
`family_factor_clause` (`SingularEndpoint/LocalizationRankOne/LdSharp.lean`), and
`family_factor_tail_mass_of_closeness` (`SingularEndpoint/LocalizationRankOne/FactorTail.lean`).  This file is the merge:
`singular_endpoint_localization` takes the maximum of the five constants and the minimum of the five
widths.  That is the whole content of the file — no new analysis.

## The one substantive point: which `f`?

The paper's `eq:factor-tail-mass` is about *the* `f` of the decomposition furnished by
`lem:localization-rank-one`, so the merge is only
faithful if the tail estimate is applied to the factor `P.f` that `family_factor_clause`
produces.  The obstruction was that `family_factor_tail_mass` required the nonlinear Factor
equation `T_W(f^{d-1}) = qf` to hold **for every** `x`, whereas a `FactorDecomp` records only
the a.e. form (`FactorDecomp.ortho`, and hence `FactorDecomp.factor_eq`); the pointwise datum
produced inside `exists_factor_solution_qlow` is discarded by `exists_factorDecomp`.

The fix taken is neither of the two obvious ones — weakening the tail estimate to an a.e.
hypothesis (which would force an a.e. rewrite of `factorSolution_closeness` and of the whole
`SingularEndpoint/LocalizationRankOne/FactorSolution.lean` chain below it), nor threading the pointwise equation back out
of `localization_rankOne` (which would mean rebuilding, in `SingularEndpoint/LocalizationRankOne/LdSharp.lean`, the
assembly that `localization_rankOne` *is*).  Instead:

**the pointwise Factor equation was never what the tail estimate needed.**  It was used there
for one purpose only — to invoke `factorSolution_closeness` and obtain `‖f - u_*‖₄ ≤ C(d)ε`.
And `family_factor_clause` already *returns* that very bound, for its own `P.f`, having
obtained it from `localization_rankOne`.  So `family_factor_tail_mass_of_closeness` takes the
closeness bound as its hypothesis, and the two compose with no change to the Factor layer at
all; `family_factor_tail_mass` is retained, unchanged in statement, as its specialisation.
The pointwise equation is then genuinely absent from this statement rather than smuggled
through, and `localization_rankOne` remains the single source of the decomposition.

## Paper results realised

* a strengthened, combined form of **`lem:localization-rank-one`** together with
  `eq:factor-tail-mass`, with one `(M, δ)` — `singular_endpoint_localization` (the paper-form
  statement is `localization_rank_one_reduction`).

## What is deliberately *not* in the statement

`family_factor_clause` also yields `q ≥ 2^{-d}` and the closeness clause
`‖f - u_*‖₄ + ‖E‖₄ ≤ C(d)ε` for the same `P`; a consumer needing either should call it
directly.  The decomposition's remaining clauses — `f ≥ 0` and `T_E(f^{d-1}) = 0` —
are the `f_nonneg` and `ortho` fields of `FactorDecomp`, so they travel with `P`.

## Axiom footprint

`singular_endpoint_localization` is `[propext, Classical.choice, Quot.sound, generalized_holder]`,
inherited from `family_localization` / `holder_moment` exactly as its five inputs are.
No new axiom is introduced here.

## Contents

* `singular_endpoint_localization`.

That is the whole interface.
-/

namespace UpperTailOptimizers

open MeasureTheory

variable {d : ℕ}

/-- `‖g‖_{L^p} ≤ A^{1/p}` from `∫|g|^p ≤ A`: `rpow` is monotone in its base. -/
private theorem localization_Lnorm_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {p A : ℝ} (hp : 0 < p) {g : α → ℝ} (hint : (∫ x, |g x| ^ p ∂μ) ≤ A) :
    Lnorm μ p g ≤ A ^ (1 / p) :=
  Real.rpow_le_rpow (integral_abs_rpow_nonneg μ p g) hint (by positivity)

/-- **`contractionEps W d = ‖W - r_*‖₄ ≤ M^{1/4}h`** from the quartic localization bound.  This is
what turns `eq:rank-one-reduction-bounds` — which bounds `‖f - u_*‖₄` by a multiple of
`contractionEps` — into the `O(h)` statement the master estimate's `A_ρ` clause needs. -/
private theorem localization_contractionEps_le (d : ℕ) {W : Graphon} {M h : ℝ} (hM : 0 ≤ M)
    (hh : 0 ≤ h) (hquart : (∫ z, |W.toFun z.1 z.2 - rStar d| ^ 4 ∂gμ) ≤ M * h ^ 4) :
    contractionEps W d ≤ M ^ (1 / (4 : ℝ)) * h := by
  have hcast : ∀ z : ℝ × ℝ, |contractionU W d z.1 z.2| ^ (4 : ℝ)
      = |W.toFun z.1 z.2 - rStar d| ^ (4 : ℕ) := by
    intro z
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rfl
  have hint : (∫ z : ℝ × ℝ, |contractionU W d z.1 z.2| ^ (4 : ℝ) ∂gμ) ≤ M * h ^ 4 := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hcast)]
    exact hquart
  have hle := localization_Lnorm_le (μ := gμ) (p := 4) (by norm_num)
    (g := fun z : ℝ × ℝ => contractionU W d z.1 z.2) hint
  have hval : (M * h ^ 4) ^ (1 / (4 : ℝ)) = M ^ (1 / (4 : ℝ)) * h := by
    rw [Real.mul_rpow hM (by positivity)]
    congr 1
    rw [show (h ^ 4 : ℝ) = h ^ ((4 : ℕ) : ℝ) by rw [Real.rpow_natCast], ← Real.rpow_mul hh]
    norm_num
  rw [← hval]
  exact hle

/-- **A combined, strengthened form of `lem:localization-rank-one`.**

For a `d`-regular graph `H` with at least one edge, a singular endpoint family `B`, and a window
radius `ρ > 0`, there are `M > 0` and `δ > 0` such that for every `0 < h < δ` inside the
family window and every graphon `W` with

`t(H, W) ≥ r_h^m`   and   `I_{p_h}(W) ≤ I_{p_h}(W_h)`,

the following bounds hold at that single `M`:

* `∫|W - r_*|² ≤ Mh²` and `∫|W - r_*|⁴ ≤ Mh⁴`  `eq:graphon-quartic-localization`;
* `0 ≤ ∫W^d - r_h^d ≤ Mh⁴`  (the sharp `∫W^d` bound);
* a nonlinear Factor decomposition `W = f ⊗ f + E` — a `FactorDecomp d W`, whose fields carry
  `f ≥ 0` and `T_E(f^{d-1}) = 0` — with `‖E‖₂ ≤ Mh²`, `|∫f^d - q_h| ≤ Mh⁴`, and
  `|{x : f(x) ∉ 𝓝_ρ}| ≤ Mh⁴`  `eq:factor-tail-mass`.

The proof is bookkeeping: `M` is the sum of the five constants of `family_localization_sq`,
`family_localization`, `family_ld_sharp`, `family_factor_clause` and
`family_factor_tail_mass_of_closeness`, and `δ` the minimum of their five widths.  The tail
estimate is applied to the factor `P.f` of the *same* decomposition, using the closeness
clause that `family_factor_clause` forwards. -/
theorem singular_endpoint_localization (hd : 2 ≤ d) {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (hreg : ∀ v, H.degree v = d)
    (hcard : 1 ≤ H.edgeFinset.card) (B : KKTFamily d) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ M : ℝ, 0 < M ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ (h : ℝ) (hh : |h| < B.h₀), 0 < h → h < δ →
        ∀ W : Graphon, B.rVal h ^ H.edgeFinset.card ≤ W.tDensity H →
          W.Ip (B.p h) ≤ (B.graphon hh).Ip (B.p h) →
          (∫ z, |W.toFun z.1 z.2 - rStar d| ^ 2 ∂gμ ≤ M * h ^ 2 ∧
              ∫ z, |W.toFun z.1 z.2 - rStar d| ^ 4 ∂gμ ≤ M * h ^ 4) ∧
            (0 ≤ W.Wmoment d - B.rVal h ^ d ∧ W.Wmoment d - B.rVal h ^ d ≤ M * h ^ 4) ∧
            ∃ P : FactorDecomp d W, P.residNorm ≤ M * h ^ 2 ∧
              |P.qVal - B.qVal h| ≤ M * h ^ 4 ∧
              (unitμ {x | P.f x ∉ centralWindow d ρ}).toReal ≤ M * h ^ 4 ∧
              Lnorm unitμ 4 (fun x => P.f x - uStar d) ≤ M * h := by
  obtain ⟨M₁, hM₁, δ₁, hδ₁, hsq⟩ := family_localization_sq hd H hreg hcard B
  obtain ⟨M₂, hM₂, δ₂, hδ₂, hquart⟩ := family_localization hd H hreg hcard B
  obtain ⟨M₃, hM₃, δ₃, hδ₃, hmom⟩ := family_ld_sharp hd H hreg hcard B
  obtain ⟨M₄, hM₄, δ₄, hδ₄, hper⟩ := family_factor_clause hd H hreg hcard B
  obtain ⟨M₅, hM₅, δ₅, hδ₅, htail⟩ := family_factor_tail_mass_of_closeness
    (C := factorSolutionCloseConst d) hd H hreg hcard B hρ
  have hCnn0 : (0 : ℝ) ≤ factorSolutionCloseConst d := factorMain_closeConst_nonneg hd
  have hextra : (0 : ℝ) ≤ factorSolutionCloseConst d * M₂ ^ (1 / (4 : ℝ)) := by
    have : (0 : ℝ) ≤ M₂ ^ (1 / (4 : ℝ)) := Real.rpow_nonneg hM₂.le _
    positivity
  refine ⟨M₁ + M₂ + M₃ + M₄ + M₅ + factorSolutionCloseConst d * M₂ ^ (1 / (4 : ℝ)),
    by linarith,
    min (min δ₁ δ₂) (min δ₃ (min δ₄ δ₅)),
    lt_min (lt_min hδ₁ hδ₂) (lt_min hδ₃ (lt_min hδ₄ hδ₅)), ?_⟩
  intro h hh hpos hlt W hfeas hcost
  have hlt₁ : h < δ₁ := lt_of_lt_of_le hlt (le_trans (min_le_left _ _) (min_le_left _ _))
  have hlt₂ : h < δ₂ := lt_of_lt_of_le hlt (le_trans (min_le_left _ _) (min_le_right _ _))
  have hlt₃ : h < δ₃ := lt_of_lt_of_le hlt (le_trans (min_le_right _ _) (min_le_left _ _))
  have hlt₄ : h < δ₄ :=
    lt_of_lt_of_le hlt
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hlt₅ : h < δ₅ :=
    lt_of_lt_of_le hlt
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  have hh2 : (0 : ℝ) ≤ h ^ 2 := by positivity
  have hh4 : (0 : ℝ) ≤ h ^ 4 := by positivity
  obtain ⟨P, _hqlow, hclose, hres, hq⟩ := hper h hh hpos hlt₄ W hfeas hcost
  obtain ⟨hmomlow, hmomhigh⟩ := hmom h hh hpos hlt₃ W hfeas hcost
  -- the `L⁴` half of `eq:rank-one-reduction-bounds`, split off the sum
  have hEnn : (0 : ℝ) ≤ Lnorm gμ 4 fun z : ℝ × ℝ => P.resid z.1 z.2 := Lnorm_nonneg _ _ _
  have hfirst : Lnorm unitμ 4 (fun x => P.f x - uStar d)
      ≤ factorSolutionCloseConst d * contractionEps W d := by linarith
  have htailP := htail h hh hpos hlt₅ W hfeas hcost P.f 2 P.meas_f P.abs_f_le hfirst
  refine ⟨⟨?_, ?_⟩, ⟨hmomlow, ?_⟩, P, ?_, ?_, ?_, ?_⟩
  · exact le_trans (hsq h hh hpos hlt₁ W hfeas hcost)
      (mul_le_mul_of_nonneg_right (by linarith) hh2)
  · exact le_trans (hquart h hh hpos hlt₂ W hfeas hcost)
      (mul_le_mul_of_nonneg_right (by linarith) hh4)
  · exact le_trans hmomhigh (mul_le_mul_of_nonneg_right (by linarith) hh4)
  · exact le_trans hres (mul_le_mul_of_nonneg_right (by linarith) hh2)
  · exact le_trans hq (mul_le_mul_of_nonneg_right (by linarith) hh4)
  · exact le_trans htailP (mul_le_mul_of_nonneg_right (by linarith) hh4)
  · -- `‖f - u_*‖₄ ≤ C·contractionEps ≤ C·M₂^{1/4}h`
    have hq4 := hquart h hh hpos hlt₂ W hfeas hcost
    have hpe := localization_contractionEps_le d hM₂.le hpos.le hq4
    have hCnn : (0 : ℝ) ≤ factorSolutionCloseConst d := hCnn0
    have hM2q : (0 : ℝ) ≤ M₂ ^ (1 / (4 : ℝ)) := Real.rpow_nonneg hM₂.le _
    have hstep : factorSolutionCloseConst d * contractionEps W d
        ≤ factorSolutionCloseConst d * (M₂ ^ (1 / (4 : ℝ)) * h) :=
      mul_le_mul_of_nonneg_left hpe hCnn
    have hcoef : factorSolutionCloseConst d * (M₂ ^ (1 / (4 : ℝ)) * h)
        ≤ (M₁ + M₂ + M₃ + M₄ + M₅ + factorSolutionCloseConst d * M₂ ^ (1 / (4 : ℝ))) * h := by
      have h1 : factorSolutionCloseConst d * (M₂ ^ (1 / (4 : ℝ)) * h)
          = factorSolutionCloseConst d * M₂ ^ (1 / (4 : ℝ)) * h := by ring
      rw [h1]
      refine mul_le_mul_of_nonneg_right ?_ hpos.le
      linarith
    linarith [hfirst, hstep, hcoef]

end UpperTailOptimizers
