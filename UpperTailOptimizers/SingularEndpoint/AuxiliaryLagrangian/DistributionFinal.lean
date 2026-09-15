import UpperTailOptimizers.SingularEndpoint.AuxiliaryLagrangian.DistributionWindow
import UpperTailOptimizers.SingularEndpoint.AuxiliaryLagrangian.DistributionAbsorption

/-!
# `lem:auxiliary-lagrangian-bound`, assembled (Section 5, `paper/sections/singular.tex`)

`SingularEndpoint/AuxiliaryLagrangian/DistributionAbsorption.lean` proves the refined form of `eq:auxiliary-lagrangian-bound` and
`eq:auxiliary-lagrangian-bound` while still carrying the hypotheses that
`SingularEndpoint/AuxiliaryLagrangian/DistributionQuant.lean` deferred — the bounds `Cp`, `Cu` on the coefficients of `P_h`
and on `u_{0,h}`, `u_{d,h}` (the paper's proof of `lem:central-kernel-bound` has a single `C_d`),
the corner accuracy `|Θ_h - d³/4| ≤ δ`, the first-variation quartic bound, and
the membership of the two atoms in the window.  `SingularEndpoint/AuxiliaryLagrangian/DistributionWindow.lean` proves all of
them at once, on a single window radius, as `KKTFamily.DistributionWindow`.

This file is the composition.  Nothing new is proved: the two capstones are restated with the
hypothesis list discharged, so that what remains is `2 ≤ d`, smallness of `h`, the admissibility
of `ν`, and `eq:graphon-comparison-estimates` itself.

## Contents

* `exists_distributionGap_refined_window` — the refined form of `eq:auxiliary-lagrangian-bound`, hypothesis-free;
* **`exists_distributionGap_refined_window_forall`** — the same at every radius below a threshold,
  the form the Step-5 join of `lem:graphon-lagrangian-bound` needs (step numbers are those of
  `SingularEndpoint/GraphonComparison/GraphonComparisonMaster.lean`; the paper's proof has none);
* `exists_distributionGap_window` — `eq:auxiliary-lagrangian-bound`, hypothesis-free.

## Where the distribution-level uniqueness lives

The distribution-level analogue of the **uniqueness step** at the end of `sec:singular-proof`
is `KKTFamily.distribution_unique` in `SingularEndpoint/Proof/DistributionUnique.lean`, which imports this file:
for an exact minimiser with `m_d(ν) = q_h` the left-hand side of `eq:auxiliary-lagrangian-bound` is
non-positive while the right-hand side is nonnegative, forcing `ν(T_ρ) = 0` and `Q_h = 0`
`ν`-a.e., hence `ν = βδ_{s_h} + (1-β)δ_{t_h}` (`eq_two_atoms`), and the moment equation then
pins `β = α_h`.

As throughout the `SingularEndpoint` layer, the Lagrangian is the graph-free one: these statements
subtract `η_h·Δ_h(ν)` where the paper writes `μ_h{m_d(ν)^v - q_h^v}`.  The paper reduces one to
the other in the display following `eq:first-variation`, at the cost of an `O(Δ²)`
that the retained
`M·Δ²` absorbs.
-/

namespace UpperTailOptimizers

open MeasureTheory

variable {d : ℕ}

namespace KKTFamily

/-- **The refined form of `eq:auxiliary-lagrangian-bound`** with every deferred
hypothesis discharged.

`exists_distribution_window` supplies the window radius `ρ` together with the whole
`DistributionWindow` bundle, and `exists_distributionGap_refined` is applied at the pinned accuracy
`δ = d³/192`, which is `a/8` for the constant `a = d³/24` of `lem:first-variation-bound` (the
proof of `lem:central-kernel-bound` needs only the accuracy `a/4`).  The coefficient `d³/48` is
`a/2`. -/
theorem exists_distributionGap_refined_window (hd : 2 ≤ d) (B : KKTFamily d) {K : ℝ}
    (hK : 1 ≤ K) :
    ∃ ρ > 0, ∃ Cz : ℝ, 0 < Cz ∧ ∃ M : ℝ, 0 < M ∧ ∃ δ₀ > 0,
      ∀ h : ℝ, 0 < h → h < δ₀ → h ≤ 1 → |h| < B.h₀ →
      ∀ ν : Measure ℝ, IsProbabilityMeasure ν → ν (Set.Icc (0 : ℝ) 2)ᶜ = 0 →
        (ν (Set.Icc (0 : ℝ) 2 \ centralWindow d ρ)).toReal ≤ K * h ^ 4 →
        |(∫ x, x ^ d ∂ν) - B.qVal h| ≤ K * h ^ 4 →
          (d : ℝ) ^ 3 / 48 * (∫ x in centralWindow d ρ, B.Qh h x ^ 2 ∂ν)
              + (∫ x in Set.Icc (0 : ℝ) 2 \ centralWindow d ρ, B.PsiT h x ∂ν)
              - zeta Cz K h * (ν (Set.Icc (0 : ℝ) 2 \ centralWindow d ρ)).toReal
              - M * ((∫ x, x ^ d ∂ν) - B.qVal h) ^ 2
            ≤ B.distributionJ h ν - B.distributionJ h (B.distributionMeasure h)
                - B.etaVal h * ((∫ x, x ^ d ∂ν) - B.qVal h) := by
  obtain ⟨ρ, hρ0, Cu, hCu, Cp, hCp, C, _hC, hw, hw0, hρu, hρ1, hwin⟩ :=
    exists_distribution_window hd B
  obtain ⟨Cz, hCz, M, hM, δ₁, hδ₁, hgap⟩ :=
    exists_distributionGap_refined hd B hρ0 hρu hρ1 hCu.le hCp.le hK
  refine ⟨ρ, hρ0, Cz, hCz, M, hM, min hw δ₁, lt_min hw0 hδ₁, ?_⟩
  intro h hh0 hhδ hh1 hhb ν hν hνc htail hmom
  have hhw : h < hw := lt_of_lt_of_le hhδ (min_le_left _ _)
  have hhδ₁ : h < δ₁ := lt_of_lt_of_le hhδ (min_le_right _ _)
  obtain ⟨hs, ht, h00, hd0, h0d, hdd, hu0, hud, hcor, htw, hJ⟩ := hwin h hh0 hhw hhb
  exact hgap h hh0 hhδ₁ hh1 hhb ((d : ℝ) ^ 3 / 192) (by positivity) le_rfl
    h00 hd0 h0d hdd hu0 hud hcor htw hs ht ν hν hνc htail hmom

/-- **The refined gap bound at every small enough radius.**  Same statement as
`exists_distributionGap_refined_window`, with the window radius universally quantified below a
threshold instead of manufactured.  This is the law half of what the Step-5 join of
`lem:graphon-lagrangian-bound` needs: the residual half
(`SingularEndpoint/GraphonComparison/GraphonComparisonMain.lean`, `comparisonMain_exists_central_bound`) is in the same form, so a
single common `ρ` can be taken as the minimum of the two thresholds.  The radius is
quantified **before** `K`, because it does not depend on it — `exists_distribution_window_forall`
sees no `K` at all — and the Step-3 composition with `singular_endpoint_localization`, whose constant
depends on `ρ`, would otherwise be circular.

The coefficient `d³/48 = a/2` (with `a = d³/24` from `lem:first-variation-bound`) of
`A_ρ = ∫_{𝓝_ρ}Q_h² dν` is **independent of `ρ`**, which is what lets the
residual half's `θA_ρ` loss be beaten by choosing `θ = d³/96` once and for all. -/
theorem exists_distributionGap_refined_window_forall (hd : 2 ≤ d) (B : KKTFamily d) :
    ∃ ρ₀ > 0, ∀ K : ℝ, 1 ≤ K → ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ →
      ∃ Cz : ℝ, 0 < Cz ∧ ∃ M : ℝ, 0 < M ∧ ∃ δ₀ > 0,
        ∀ h : ℝ, 0 < h → h < δ₀ → h ≤ 1 → |h| < B.h₀ →
        ∀ ν : Measure ℝ, IsProbabilityMeasure ν → ν (Set.Icc (0 : ℝ) 2)ᶜ = 0 →
          (ν (Set.Icc (0 : ℝ) 2 \ centralWindow d ρ)).toReal ≤ K * h ^ 4 →
          |(∫ x, x ^ d ∂ν) - B.qVal h| ≤ K * h ^ 4 →
            (d : ℝ) ^ 3 / 48 * (∫ x in centralWindow d ρ, B.Qh h x ^ 2 ∂ν)
                + (∫ x in Set.Icc (0 : ℝ) 2 \ centralWindow d ρ, B.PsiT h x ∂ν)
                - zeta Cz K h * (ν (Set.Icc (0 : ℝ) 2 \ centralWindow d ρ)).toReal
                - M * ((∫ x, x ^ d ∂ν) - B.qVal h) ^ 2
              ≤ B.distributionJ h ν - B.distributionJ h (B.distributionMeasure h)
                  - B.etaVal h * ((∫ x, x ^ d ∂ν) - B.qVal h) := by
  obtain ⟨ρ₀, hρ₀0, hρ₀u, hρ₀1, hwinall⟩ := exists_distribution_window_forall hd B
  refine ⟨ρ₀, hρ₀0, ?_⟩
  intro K hK ρ hρ0 hρle
  have hρu : ρ ≤ uStar d / 2 := le_trans hρle hρ₀u
  have hρ1 : ρ ≤ (1 - uStar d) / 2 := le_trans hρle hρ₀1
  obtain ⟨Cu, hCu, Cp, hCp, C, _hC, hw, hw0, hwin⟩ := hwinall ρ hρ0 hρle
  obtain ⟨Cz, hCz, M, hM, δ₁, hδ₁, hgap⟩ :=
    exists_distributionGap_refined hd B hρ0 hρu hρ1 hCu.le hCp.le hK
  refine ⟨Cz, hCz, M, hM, min hw δ₁, lt_min hw0 hδ₁, ?_⟩
  intro h hh0 hhδ hh1 hhb ν hν hνc htail hmom
  have hhw : h < hw := lt_of_lt_of_le hhδ (min_le_left _ _)
  have hhδ₁ : h < δ₁ := lt_of_lt_of_le hhδ (min_le_right _ _)
  obtain ⟨hs, ht, h00, hd0, h0d, hdd, hu0, hud, hcor, htw, hJ⟩ := hwin h hh0 hhw hhb
  exact hgap h hh0 hhδ₁ hh1 hhb ((d : ℝ) ^ 3 / 192) (by positivity) le_rfl
    h00 hd0 h0d hdd hu0 hud hcor htw hs ht ν hν hνc htail hmom

/-- **`eq:auxiliary-lagrangian-bound`** with every deferred hypothesis discharged: the law gap
dominates `M⁻¹[A_ρ + ν(T_ρ)] - MΔ²`, where `A_ρ = ∫_{𝓝_ρ}Q_h² dν` and `T_ρ = [0,2] \ 𝓝_ρ` are
the closed-window counterparts of the paper's `A_{h,ρ}(ν)` and `𝒯_ρ`, with no side conditions
beyond `2 ≤ d`, smallness of `h`, admissibility of `ν`, and `eq:graphon-comparison-estimates`. -/
theorem exists_distributionGap_window (hd : 2 ≤ d) (B : KKTFamily d) {K : ℝ} (hK : 1 ≤ K) :
    ∃ ρ > 0, ∃ M : ℝ, 0 < M ∧ ∃ δ₀ > 0,
      ∀ h : ℝ, 0 < h → h < δ₀ → h ≤ 1 → |h| < B.h₀ →
      ∀ ν : Measure ℝ, IsProbabilityMeasure ν → ν (Set.Icc (0 : ℝ) 2)ᶜ = 0 →
        (ν (Set.Icc (0 : ℝ) 2 \ centralWindow d ρ)).toReal ≤ K * h ^ 4 →
        |(∫ x, x ^ d ∂ν) - B.qVal h| ≤ K * h ^ 4 →
          M⁻¹ * ((∫ x in centralWindow d ρ, B.Qh h x ^ 2 ∂ν)
                  + (ν (Set.Icc (0 : ℝ) 2 \ centralWindow d ρ)).toReal)
              - M * ((∫ x, x ^ d ∂ν) - B.qVal h) ^ 2
            ≤ B.distributionJ h ν - B.distributionJ h (B.distributionMeasure h)
                - B.etaVal h * ((∫ x, x ^ d ∂ν) - B.qVal h) := by
  obtain ⟨ρ, hρ0, Cu, hCu, Cp, hCp, C, _hC, hw, hw0, hρu, hρ1, hwin⟩ :=
    exists_distribution_window hd B
  obtain ⟨M, hM, δ₁, hδ₁, hgap⟩ := exists_distributionGap hd B hρ0 hρu hρ1 hCu.le hCp.le hK
  refine ⟨ρ, hρ0, M, hM, min hw δ₁, lt_min hw0 hδ₁, ?_⟩
  intro h hh0 hhδ hh1 hhb ν hν hνc htail hmom
  have hhw : h < hw := lt_of_lt_of_le hhδ (min_le_left _ _)
  have hhδ₁ : h < δ₁ := lt_of_lt_of_le hhδ (min_le_right _ _)
  obtain ⟨hs, ht, h00, hd0, h0d, hdd, hu0, hud, hcor, htw, hJ⟩ := hwin h hh0 hhw hhb
  exact hgap h hh0 hhδ₁ hh1 hhb ((d : ℝ) ^ 3 / 192) (by positivity) le_rfl
    h00 hd0 h0d hdd hu0 hud hcor htw hs ht ν hν hνc htail hmom

end KKTFamily

end UpperTailOptimizers
