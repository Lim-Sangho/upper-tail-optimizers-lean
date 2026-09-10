import UpperTailOptimizers.SingularEndpoint.FamilyBuild
import UpperTailOptimizers.SingularEndpoint.SingularEndpointOptimality
import UpperTailOptimizers.SingularEndpoint.TerminalTwoValued
import UpperTailOptimizers.SingularEndpoint.StrictImprovement
import UpperTailOptimizers.SingularEndpoint.CostRemainder

/-!
# `thm:endpoint-optimality`, uniqueness clause

`exists_singular_endpoint_rigidity` says that a competitor which costs no more than `W_h` in fact
satisfies `Δ = 0` and `R = 0`.  This file converts that into the theorem's uniqueness
statement: such a competitor *is* `W_h`, up to a measure-preserving relabelling of `[0,1]`.

The three ingredients are already in place:

* `ae_bipodalValue_of_R_zero` — `R = 0` makes `W` almost everywhere the two-block value with
  vertex class `A = [0,1] ∩ {f = s_h}` and levels `s_h², s_h t_h, t_h²`;
* `measure_eq_alph_of_qVal_eq` — `Δ = 0` forces `|A| = α_h`, because `0 < s_h < t_h` makes the
  two coefficients of `q = |A|s_h^d + (1-|A|)t_h^d` distinct;
* `exists_relabel_eq_bipodalGraphon` — a class of the right measure can be moved onto the
  standard block `[0, α_h]` by a measure-preserving `σ`, namely the distribution transport of
  `SingularEndpoint/CdfTransport.lean`.

Since `W_h = bipodalGraphon (Icc 0 α_h) s_h² (s_h t_h) t_h²` by definition, composing the three
gives `W(x,y) = W_h(σx, σy)` for `gμ`-a.e. `(x,y)`.

## Contents

* **`exists_singular_endpoint_uniqueness`** — the uniqueness clause.
* **`exists_singular_endpoint_full`** — feasibility, optimality and uniqueness for a given family
  with the canonical block `[0, α_h]`.
* **`singular_endpoint_full`** — Theorem 7.1, combining the family construction,
  analytic curve, base values, coalescence, optimality, uniqueness and leading cost gap.
* `SingularEndpointOptimizers` and `SingularEndpointStructure` — the conclusion structures;
  the latter adds base values and the cost gap to the introduction's conclusions.

`FamilyContinuity.lean` supplies the analytic curve and convergence facts;
`StrictImprovement.lean` supplies the cost gap with an `o(h⁴)` remainder instead of
`O(h⁶)`. Theorem 1.6 in `IntroSingularEndpointOptimizers.lean` is a direct projection
of `singular_endpoint_full`. The cost and arbitrary-block qualifications remain
in `FORMALISATION.md`, deviations [D1] and [D12].
-/

namespace UpperTailOptimizers

namespace SingularEndpoint

open MeasureTheory Filter Topology

open scoped Classical

variable {d : ℕ}

/-- **`thm:endpoint-optimality`, uniqueness clause.**

For every small `h > 0` inside the family window, any feasible graphon that costs no more than
`W_h` agrees with `W_h` after a measure-preserving relabelling of `[0,1]`.

Combined with `exists_singular_endpoint_optimality` — which says no feasible graphon costs *less* — this
says every minimiser is a measure-preserving pullback of the canonical `W_h`.
No graphon quotient is defined in this development. -/
theorem exists_singular_endpoint_uniqueness (hd : 2 ≤ d) {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (hreg : ∀ v, H.degree v = d)
    (hcard : 1 ≤ H.edgeFinset.card) (hv : 2 ≤ Fintype.card V) (B : KKTFamily d) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (h : ℝ) (hh : |h| < B.h₀), 0 < h → h < δ → h ≤ 1 →
      ∀ W : Graphon, Feasible H (B.rVal h) W → W.Ip (B.p h) ≤ (B.graphon hh).Ip (B.p h) →
        ∃ σ : ℝ → ℝ, IsRelabelling σ ∧
          ∀ᵐ z ∂gμ, W.toFun z.1 z.2 = (B.graphon hh).toFun (σ z.1) (σ z.2) := by
  obtain ⟨ρ, -, δ, hδ, hrig⟩ := exists_singular_endpoint_rigidity hd H hreg hcard hv B
  refine ⟨δ, hδ, fun h hhb hh0 hhδ hh1 W hfeas hcost => ?_⟩
  obtain ⟨P, hq, hE, hQ, hε, -⟩ := hrig h hhb hh0 hhδ hh1 W hfeas hcost
  -- the vertex class and its measure
  obtain ⟨A, hAdef⟩ : ∃ S : Set ℝ, S = Set.Icc (0 : ℝ) 1 ∩ {x | P.f x = B.sVal h} := ⟨_, rfl⟩
  have hA : MeasurableSet A := by
    rw [hAdef]; exact measurableSet_Icc.inter (P.meas_f (measurableSet_singleton _))
  have hAsub : A ⊆ Set.Icc 0 1 := by rw [hAdef]; exact Set.inter_subset_left
  have hvol : (volume A).toReal = B.alph h := by
    have hres : unitμ A = volume A := by
      rw [unitμ, Measure.restrict_apply hA, Set.inter_eq_self_of_subset_left hAsub]
    rw [← hres, hAdef]
    exact measure_eq_alph_of_qVal_eq hd P B hhb hh0 hQ hε hq
  -- the two-block representation and the transport
  have hbip := ae_bipodalValue_of_R_zero P B hE hQ hε
  rw [← hAdef] at hbip
  exact exists_relabel_eq_bipodalGraphon hA hAsub hvol
    (KKTFamily.sq_sVal_mem hhb) (KKTFamily.cross_mem hhb)
    (KKTFamily.sq_tVal_mem hhb) hbip

/-- **`thm:endpoint-optimality`.**  Optimality and uniqueness together: for every small
`h > 0` in the family window, `W_h` is itself feasible, it minimises `I_{p_h}` among the
graphons feasible for `t(H,·) ≥ r_h^m`, and every other minimiser is a relabelling of it.

The feasibility conjunct is what makes the second one a *minimality* claim rather than a bare
lower bound: without it the statement would not say that the infimum is attained. It is
`graphon_tDensity_eq_rVal_pow`, `t(H, W_h) = r_h^m`, weakened to an inequality. -/
theorem exists_singular_endpoint_full (hd : 2 ≤ d) {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (hreg : ∀ v, H.degree v = d)
    (hcard : 1 ≤ H.edgeFinset.card) (hv : 2 ≤ Fintype.card V) (B : KKTFamily d) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (h : ℝ) (hh : |h| < B.h₀), 0 < h → h < δ → h ≤ 1 →
      Feasible H (B.rVal h) (B.graphon hh) ∧
      ∀ W : Graphon, Feasible H (B.rVal h) W →
        (B.graphon hh).Ip (B.p h) ≤ W.Ip (B.p h) ∧
          (W.Ip (B.p h) ≤ (B.graphon hh).Ip (B.p h) →
            ∃ σ : ℝ → ℝ, IsRelabelling σ ∧
              ∀ᵐ z ∂gμ, W.toFun z.1 z.2 = (B.graphon hh).toFun (σ z.1) (σ z.2)) := by
  obtain ⟨δ₁, hδ₁, hopt⟩ := exists_singular_endpoint_optimality hd H hreg hcard hv B
  obtain ⟨δ₂, hδ₂, huniq⟩ := exists_singular_endpoint_uniqueness hd H hreg hcard hv B
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun h hhb hh0 hhδ hh1 => ?_⟩
  refine ⟨le_of_eq (KKTFamily.graphon_tDensity_eq_rVal_pow H hd hreg hhb).symm,
    fun W hfeas => ?_⟩
  exact ⟨hopt h hhb hh0 (lt_of_lt_of_le hhδ (min_le_left _ _)) hh1 W hfeas,
    huniq h hhb hh0 (lt_of_lt_of_le hhδ (min_le_right _ _)) hh1 W hfeas⟩

/-- The conclusions of Theorem 1.6 for a family and an optimality window.
All family properties and all optimizer conclusions refer to the same `B`. -/
structure SingularEndpointOptimizers {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] {d : ℕ} (B : KKTFamily d) (δ : ℝ) : Prop where
  delta_pos : 0 < δ
  analytic_curve : ∀ h : ℝ, |h| < B.h₀ → AnalyticAt ℝ B.p h ∧ AnalyticAt ℝ B.rVal h
  parameter_limits : Tendsto B.p (𝓝 0) (𝓝 (pcGlobal d (rStar d))) ∧
    Tendsto B.rVal (𝓝[≠] 0) (𝓝 (rStar d))
  block_limit : Tendsto B.alph (𝓝 0) (𝓝 (1 / 2))
  factor_limits : Tendsto B.sVal (𝓝[≠] 0) (𝓝 (uStar d)) ∧
    Tendsto B.tVal (𝓝[≠] 0) (𝓝 (uStar d))
  uniform_convergence : ∀ ε : ℝ, 0 < ε → ∃ δ' : ℝ, 0 < δ' ∧
    ∀ (h : ℝ) (hh : |h| < B.h₀), |h| < δ' →
      ∀ x y, |(B.graphon hh).toFun x y - rStar d| ≤ ε
  optimizers :
      ∀ (h : ℝ) (hh : |h| < B.h₀), 0 < h → h < δ → h ≤ 1 →
        (∃ f : ℝ → ℝ, Measurable f ∧ (∀ x, f x ∈ Set.Icc (0 : ℝ) 1) ∧
          ∀ x y, (B.graphon hh).toFun x y = f x * f y) ∧
        IsBipodal (B.graphon hh) ∧
        (¬ ∃ ρ : ℝ, ∀ᵐ z ∂gμ, (B.graphon hh).toFun z.1 z.2 = ρ) ∧
        (B.graphon hh).tDensity H = B.rVal h ^ H.edgeFinset.card ∧
        (∀ W : Graphon, Feasible H (B.rVal h) W →
          (B.graphon hh).Ip (B.p h) ≤ W.Ip (B.p h) ∧
            (W.Ip (B.p h) ≤ (B.graphon hh).Ip (B.p h) →
              ∃ σ : ℝ → ℝ, IsRelabelling σ ∧
                ∀ᵐ z ∂gμ, W.toFun z.1 z.2 = (B.graphon hh).toFun (σ z.1) (σ z.2)))

/-- **Pulling an a.e. statement back along a relabelling of both coordinates.** -/
private theorem ae_gμ_comp_relabel {σ : ℝ → ℝ} (hσ : MeasurePreserving σ unitμ unitμ)
    {P : ℝ → ℝ → Prop} (h : ∀ᵐ z ∂gμ, P z.1 z.2) : ∀ᵐ z ∂gμ, P (σ z.1) (σ z.2) :=
  (hσ.prod hσ).quasiMeasurePreserving.ae (p := fun z : ℝ × ℝ => P z.1 z.2) h

/-- **Theorem 7.1 for an arbitrary candidate block.**  The paper quantifies over every
measurable `A_h ⊆ [0,1]` of measure `α_h`; `KKTFamily.graphon` uses the representative
`[0, α_h]`.  Every other block gives a relabelling of that representative, and all the
functionals — `IsBipodal`, nonconstancy, `t(H,·)` and `I_p` — are relabelling-invariant, so the
whole conclusion transfers. -/
theorem anyBlock_of_singularEndpointOptimizers {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] {B : KKTFamily d} {δ : ℝ}
    (S : SingularEndpointOptimizers H B δ)
    {h : ℝ} (hh : |h| < B.h₀) (hh0 : 0 < h) (hhδ : h < δ) (hh1 : h ≤ 1)
    {A : Set ℝ} (hA : MeasurableSet A) (hAsub : A ⊆ Set.Icc 0 1)
    (hAvol : (volume A).toReal = B.alph h)
    {W : Graphon}
    (hW : ∀ᵐ z ∂gμ, W.toFun z.1 z.2
      = bipodalValue A (B.sVal h ^ 2) (B.sVal h * B.tVal h) (B.tVal h ^ 2) z) :
    IsBipodal W ∧
    (¬ ∃ ρ : ℝ, ∀ᵐ z ∂gμ, W.toFun z.1 z.2 = ρ) ∧
    W.tDensity H = B.rVal h ^ H.edgeFinset.card ∧
    (∀ W' : Graphon, Feasible H (B.rVal h) W' →
      W.Ip (B.p h) ≤ W'.Ip (B.p h) ∧
        (W'.Ip (B.p h) ≤ W.Ip (B.p h) →
          ∃ σ : ℝ → ℝ, IsRelabelling σ ∧
            ∀ᵐ z ∂gμ, W'.toFun z.1 z.2 = W.toFun (σ z.1) (σ z.2))) := by
  obtain ⟨σ, hσ, hWσ⟩ :=
    exists_relabel_eq_bipodalGraphon hA hAsub hAvol
      (KKTFamily.sq_sVal_mem hh) (KKTFamily.cross_mem hh) (KKTFamily.sq_tVal_mem hh) hW
  have hWσ' : ∀ᵐ z ∂gμ, W.toFun z.1 z.2 = (B.graphon hh).toFun (σ z.1) (σ z.2) := hWσ
  obtain ⟨-, hbip, hnc, htd, hopt⟩ := S.optimizers h hh hh0 hhδ hh1
  obtain ⟨τ, hτ, hτσ, hστ⟩ := hσ.exists_symm
  -- `B.graphon hh = W ∘ (τ,τ)` almost everywhere
  have hGW : ∀ᵐ z ∂gμ, (B.graphon hh).toFun z.1 z.2 = W.toFun (τ z.1) (τ z.2) := by
    have h1 := ae_gμ_comp_relabel (P := fun a b => W.toFun a b
        = (B.graphon hh).toFun (σ a) (σ b)) hτ.measurePreserving hWσ'
    have h2 := ae_gμ_of_ae_unitμ hστ
    filter_upwards [h1, h2] with z hz hz2
    rw [hz, hz2.1, hz2.2]
  have hIp : W.Ip (B.p h) = (B.graphon hh).Ip (B.p h) :=
    Graphon.Ip_relabel _ hσ.measurePreserving hWσ'
  refine ⟨isBipodal_of_relabel hσ hbip hWσ', ?_, ?_, ?_⟩
  · -- nonconstancy transfers back along the inverse
    rintro ⟨ρ, hρ⟩
    refine hnc ⟨ρ, ?_⟩
    filter_upwards [hGW, ae_gμ_comp_relabel (P := fun a b => W.toFun a b = ρ)
      hτ.measurePreserving hρ] with z hz hz'
    rw [hz]; exact hz'
  · rw [tDensity_relabel hσ.measurePreserving H hWσ']; exact htd
  · intro W' hW'
    obtain ⟨hle, huniq⟩ := hopt W' hW'
    refine ⟨by rw [hIp]; exact hle, fun hW'le => ?_⟩
    obtain ⟨σ', hσ', hrel⟩ := huniq (by rw [← hIp]; exact hW'le)
    refine ⟨fun x => τ (σ' x), hτ.comp hσ', ?_⟩
    have hpull := ae_gμ_comp_relabel (P := fun a b => (B.graphon hh).toFun a b
        = W.toFun (τ a) (τ b)) hσ'.measurePreserving hGW
    filter_upwards [hrel, hpull] with z hz hz2
    rw [hz, hz2]

/-- Theorem 7.1 for the canonical block, including its base values and the proved
leading cost expansion. The remainder is `o(h⁴)`, rather than the paper's `O(h⁶)`;
see FORMALISATION.md, deviations [D1] and [D12]. -/
structure SingularEndpointStructure {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] {d : ℕ} (B : KKTFamily d) (δ : ℝ)
    : Prop extends SingularEndpointOptimizers H B δ where
  base_values : B.p 0 = pStar d ∧ B.rVal 0 = rStar d ∧
    B.u 0 = uStar d ∧ B.alph 0 = 1 / 2
  cost_gap : ∃ C : ℝ, 0 < C ∧ ∀ (h : ℝ) (hh : |h| < B.h₀), |h| < δ →
    |((B.graphon hh).Ip (B.p h) - Jp (B.p h) (B.rVal h)) + (d : ℝ) ^ 3 / 3 * h ^ 4|
      ≤ C * |h| ^ 6

/-- **Theorem 7.1**, with the documented cost-remainder and canonical-block
qualifications. Theorem 1.6 is a direct projection of this result. -/
theorem singular_endpoint_full (hd : 2 ≤ d) {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (hreg : ∀ v, H.degree v = d)
    (hcard : 1 ≤ H.edgeFinset.card) (hv : 2 ≤ Fintype.card V) :
    ∃ (B : KKTFamily d) (δ : ℝ), SingularEndpointStructure H B δ := by
  obtain ⟨B⟩ := exists_kktFamily hd
  obtain ⟨δ, hδ, hfull⟩ := exists_singular_endpoint_full hd H hreg hcard hv B
  obtain ⟨Ccost, δcost, hCcost, hδcost, hcost⟩ := constant_graphon_comparison hd B
  refine ⟨B, min δ δcost, ?_⟩
  refine
    { delta_pos := lt_min hδ hδcost
      analytic_curve := fun h hh => ⟨B.analyticAt_p h hh, KKTFamily.analyticAt_rVal hh⟩
      parameter_limits := ⟨KKTFamily.tendsto_p_pcGlobal hd B, tendsto_rVal hd B⟩
      block_limit := tendsto_alph B
      factor_limits := ⟨tendsto_sVal B, tendsto_tVal B⟩
      uniform_convergence := fun ε hε => KKTFamily.exists_graphon_unif hd B hε
      optimizers := ?_
      base_values := ⟨B.p_zero, KKTFamily.rVal_zero hd B, B.u_zero, B.alph_zero⟩
      cost_gap := ⟨Ccost, hCcost, fun h hh hhδ =>
        hcost h hh (lt_of_lt_of_le hhδ (min_le_right _ _))⟩ }
  intro h hh hh0 hhδ hh1
  exact ⟨KKTFamily.graphon_rankOne hh, KKTFamily.graphon_isBipodal hh,
    KKTFamily.graphon_not_ae_const hd hh (ne_of_gt hh0),
    KKTFamily.graphon_tDensity_eq_rVal_pow H hd hreg hh,
    (hfull h hh hh0 (lt_of_lt_of_le hhδ (min_le_left _ _)) hh1).2⟩

end SingularEndpoint

end UpperTailOptimizers
