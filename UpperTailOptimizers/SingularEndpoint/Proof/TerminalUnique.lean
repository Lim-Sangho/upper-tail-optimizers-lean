import UpperTailOptimizers.SingularEndpoint.RankOneStationaryFamily.FamilyBuild
import UpperTailOptimizers.SingularEndpoint.Proof.SingularEndpointOptimality
import UpperTailOptimizers.SingularEndpoint.Proof.TerminalTwoValued
import UpperTailOptimizers.SingularEndpoint.ConstantGraphonComparison.StrictImprovement
import UpperTailOptimizers.SingularEndpoint.ConstantGraphonComparison.CostRemainder

/-!
# `thm:singular-endpoint`, uniqueness clause

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
  `SingularEndpoint/RankOneStationaryFamily/CdfTransport.lean`.

Since `W_h = bipodalGraphon (Icc 0 α_h) s_h² (s_h t_h) t_h²` by definition, composing the three
gives `W(x,y) = W_h(σx, σy)` for `gμ`-a.e. `(x,y)`.

## Contents

* **`exists_singular_endpoint_uniqueness`** — the uniqueness clause.
* **`exists_singular_endpoint_full`** — feasibility, optimality and uniqueness for a given family
  with the canonical block `[0, α_h]`.
* `SingularEndpointOptimizers H B C δ` — the conclusions of Theorem 1.6 for a family `B`, a
  remainder constant `C` and a window `(0, δ)` with `δ ≤ h₀`: analytic curve, `p_h < pc(r_h)`,
  the limits of `p_h, r_h, α_h, 1-α_h, s_h, t_h` and of the three block values, uniform
  convergence to `r_*`, the optimizer conclusions for the canonical block, and the two expansions
  `|e(W_h) - (r_h - (d-1)h²)| ≤ Ch⁴` and `|Φ_H(p_h,r_h) - (J_{p_h}(r_h) - d³h⁴/3)| ≤ Ch⁶`.
* `SingularEndpointStructure H B C δ` — adds the base values, analyticity of `u_h, α_h`, and the
  conclusions (existence of `f_h ⊗ f_h`, rank one, bipodality, nonconstancy, `t(H,W_h) = r_h^m`,
  optimality, uniqueness, edge expansion) for **every** measurable block `A_h ⊆ [0,1]` of
  measure `α_h`.
* **`anyBlock_of_singularEndpointOptimizers`** — transfers the optimizer conclusions and the
  edge expansion from the canonical block `[0, α_h]` to every block of measure `α_h`.
* **`singular_endpoint_full`** — Theorem 5.1: there are a family `B` and a constant `C > 0`,
  depending only on `d`, such that every `d`-regular `H` has a window `δ` with
  `SingularEndpointStructure H B C δ`.

`FamilyContinuity.lean` supplies the analytic curve and convergence facts;
`StrictImprovement.lean` supplies `p_h < pc(r_h)` (`singular_endpoint_symmetry_breaking`), and
`CostRemainder.lean` both expansions (`constant_graphon_comparison`), whose constant depends only
on `B`.  The window `δ` is the minimum of the optimality/uniqueness window (which depends on
`H`), the expansion and symmetry-breaking windows, `1` and `h₀`.  `Φ_H(p_h,r_h) = I_{p_h}(W_h)`
because `W_h` is feasible and optimal.  Theorem 1.6 in `IntroSingularEndpointOptimizers.lean`
is a direct projection of `singular_endpoint_full`.
-/

namespace UpperTailOptimizers

open MeasureTheory Filter Topology

open scoped Classical

variable {d : ℕ}

/-- **`thm:singular-endpoint`, uniqueness clause.**

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

/-- **`thm:singular-endpoint`.**  Optimality and uniqueness together: for every small
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

/-- The conclusions of Theorem 1.6 for a family `B`, a remainder constant `C` and a window
`(0, δ)`.  All family properties and all optimizer conclusions refer to the same `B`.  The
remainder constant `C` is a parameter, so that `singular_endpoint_optimizers` can choose it before
the graph, as the paper's `O_d` requires. -/
structure SingularEndpointOptimizers {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] {d : ℕ} (B : KKTFamily d) (C δ : ℝ) : Prop where
  delta_pos : 0 < δ
  delta_le : δ ≤ B.h₀
  analytic_curve : ∀ h : ℝ, |h| < B.h₀ → AnalyticAt ℝ B.p h ∧ AnalyticAt ℝ B.rVal h
  below_boundary : ∀ h : ℝ, 0 < h → h < δ → B.p h < pcGlobal d (B.rVal h)
  parameter_limits : Tendsto B.p (𝓝 0) (𝓝 (pcGlobal d (rStar d))) ∧
    Tendsto B.rVal (𝓝[≠] 0) (𝓝 (rStar d))
  block_limit : Tendsto B.alph (𝓝 0) (𝓝 (1 / 2)) ∧
    Tendsto (fun h => 1 - B.alph h) (𝓝 0) (𝓝 (1 / 2))
  factor_limits : Tendsto B.sVal (𝓝[≠] 0) (𝓝 (uStar d)) ∧
    Tendsto B.tVal (𝓝[≠] 0) (𝓝 (uStar d))
  density_limits : Tendsto (fun h => B.sVal h ^ 2) (𝓝[≠] 0) (𝓝 (rStar d)) ∧
    Tendsto (fun h => B.sVal h * B.tVal h) (𝓝[≠] 0) (𝓝 (rStar d)) ∧
    Tendsto (fun h => B.tVal h ^ 2) (𝓝[≠] 0) (𝓝 (rStar d))
  uniform_convergence : ∀ ε : ℝ, 0 < ε → ∃ δ' : ℝ, 0 < δ' ∧
    ∀ (h : ℝ) (hh : |h| < B.h₀), |h| < δ' →
      ∀ x y, |(B.graphon hh).toFun x y - rStar d| ≤ ε
  optimizers :
      ∀ (h : ℝ) (hh : |h| < B.h₀), 0 < h → h < δ →
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
  /-- `e(W_h) = r_h - (d-1)h² + O_d(h⁴)`. -/
  edge_gap : ∀ (h : ℝ) (hh : |h| < B.h₀), 0 < h → h < δ →
    |(B.graphon hh).edgeDensity - (B.rVal h - ((d : ℝ) - 1) * h ^ 2)| ≤ C * h ^ 4
  /-- `Φ_H(p_h,r_h) = J_{p_h}(r_h) - d³h⁴/3 + O_d(h⁶)`. -/
  cost_gap : ∀ h : ℝ, 0 < h → h < δ →
    |phiVar H (B.p h) (B.rVal h) - (Jp (B.p h) (B.rVal h) - (d : ℝ) ^ 3 / 3 * h ^ 4)|
      ≤ C * h ^ 6

/-- **Pulling an a.e. statement back along a relabelling of both coordinates.** -/
private theorem ae_gμ_comp_relabel {σ : ℝ → ℝ} (hσ : MeasurePreserving σ unitμ unitμ)
    {P : ℝ → ℝ → Prop} (h : ∀ᵐ z ∂gμ, P z.1 z.2) : ∀ᵐ z ∂gμ, P (σ z.1) (σ z.2) :=
  (hσ.prod hσ).quasiMeasurePreserving.ae (p := fun z : ℝ × ℝ => P z.1 z.2) h

/-- **Theorem 5.1 for an arbitrary candidate block.**  The paper quantifies over every
measurable `A_h ⊆ [0,1]` of measure `α_h`; `KKTFamily.graphon` uses the representative
`[0, α_h]`.  Every other block gives a relabelling of that representative, and all the
functionals — `IsBipodal`, nonconstancy, `t(H,·)` and `I_p` — are relabelling-invariant, so the
whole conclusion transfers. -/
theorem anyBlock_of_singularEndpointOptimizers {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] {B : KKTFamily d} {C δ : ℝ}
    (S : SingularEndpointOptimizers H B C δ)
    {h : ℝ} (hh : |h| < B.h₀) (hh0 : 0 < h) (hhδ : h < δ)
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
            ∀ᵐ z ∂gμ, W'.toFun z.1 z.2 = W.toFun (σ z.1) (σ z.2))) ∧
    |W.edgeDensity - (B.rVal h - ((d : ℝ) - 1) * h ^ 2)| ≤ C * h ^ 4 := by
  obtain ⟨σ, hσ, hWσ⟩ :=
    exists_relabel_eq_bipodalGraphon hA hAsub hAvol
      (KKTFamily.sq_sVal_mem hh) (KKTFamily.cross_mem hh) (KKTFamily.sq_tVal_mem hh) hW
  have hWσ' : ∀ᵐ z ∂gμ, W.toFun z.1 z.2 = (B.graphon hh).toFun (σ z.1) (σ z.2) := hWσ
  obtain ⟨-, hbip, hnc, htd, hopt⟩ := S.optimizers h hh hh0 hhδ
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
  refine ⟨isBipodal_of_relabel hσ hbip hWσ', ?_, ?_, ?_, ?_⟩
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
  · -- the edge density is relabelling-invariant
    rw [Graphon.edgeDensity_relabel hσ.measurePreserving hWσ']
    exact S.edge_gap h hh hh0 hhδ

/-- The conclusions of Theorem 5.1: those of Theorem 1.6 for the canonical block `[0, α_h]`,
the base values and analyticity of `u_h, α_h`, and the conclusions for **every** measurable
block `A_h ⊆ [0,1]` of measure `α_h`, with `f_h = s_h 1_{A_h} + t_h 1_{A_h^c}` and
`W_h = f_h ⊗ f_h`. -/
structure SingularEndpointStructure {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] {d : ℕ} (B : KKTFamily d) (C δ : ℝ)
    : Prop extends SingularEndpointOptimizers H B C δ where
  base_values : B.p 0 = pStar d ∧ B.rVal 0 = rStar d ∧
    B.u 0 = uStar d ∧ B.alph 0 = 1 / 2
  analytic_parameters : ∀ h : ℝ, |h| < B.h₀ → AnalyticAt ℝ B.u h ∧ AnalyticAt ℝ B.alph h
  any_block : ∀ h : ℝ, 0 < h → h < δ →
    ∀ A : Set ℝ, MeasurableSet A → A ⊆ Set.Icc 0 1 → (volume A).toReal = B.alph h →
      (∃ W : Graphon, ∀ x y, W.toFun x y
        = (A.indicator (fun _ => B.sVal h) x + Aᶜ.indicator (fun _ => B.tVal h) x)
          * (A.indicator (fun _ => B.sVal h) y + Aᶜ.indicator (fun _ => B.tVal h) y)) ∧
      ∀ W : Graphon, (∀ x y, W.toFun x y
        = (A.indicator (fun _ => B.sVal h) x + Aᶜ.indicator (fun _ => B.tVal h) x)
          * (A.indicator (fun _ => B.sVal h) y + Aᶜ.indicator (fun _ => B.tVal h) y)) →
        (∃ f : ℝ → ℝ, Measurable f ∧ (∀ x, f x ∈ Set.Icc (0 : ℝ) 1) ∧
          ∀ x y, W.toFun x y = f x * f y) ∧
        IsBipodal W ∧
        (¬ ∃ ρ : ℝ, ∀ᵐ z ∂gμ, W.toFun z.1 z.2 = ρ) ∧
        W.tDensity H = B.rVal h ^ H.edgeFinset.card ∧
        (∀ W' : Graphon, Feasible H (B.rVal h) W' →
          W.Ip (B.p h) ≤ W'.Ip (B.p h) ∧
            (W'.Ip (B.p h) ≤ W.Ip (B.p h) →
              ∃ σ : ℝ → ℝ, IsRelabelling σ ∧
                ∀ᵐ z ∂gμ, W'.toFun z.1 z.2 = W.toFun (σ z.1) (σ z.2))) ∧
        |W.edgeDensity - (B.rVal h - ((d : ℝ) - 1) * h ^ 2)| ≤ C * h ^ 4

universe u

/-- **Theorem 5.1.**  One family `B` and one remainder constant `C`, both depending only on
`d`, serve every `d`-regular graph `H`; the window `δ` depends on `H`.  Theorem 1.6 is a
projection of this result.  The clause `p_h < pc(r_h)` is `singular_endpoint_symmetry_breaking`,
which uses the Lubetzky–Zhao criterion. -/
theorem singular_endpoint_full (hd : 2 ≤ d) :
    ∃ (B : KKTFamily d) (C : ℝ), 0 < C ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj],
        (∀ v, H.degree v = d) → 1 ≤ H.edgeFinset.card → 2 ≤ Fintype.card V →
        ∃ δ : ℝ, SingularEndpointStructure H B C δ := by
  obtain ⟨B⟩ := exists_kktFamily hd
  obtain ⟨C, δc, hC, hδc, hcomp⟩ := constant_graphon_comparison hd B
  refine ⟨B, C, hC, fun {V} _ _ H _ hreg hcard hv => ?_⟩
  obtain ⟨δf, hδf, hfull⟩ := exists_singular_endpoint_full hd H hreg hcard hv B
  obtain ⟨δs, hδs, hsb⟩ := singular_endpoint_symmetry_breaking hd H hreg hcard B
  set δ : ℝ := min (min δf δc) (min δs (min 1 B.h₀)) with hδdef
  have hδpos : 0 < δ := lt_min (lt_min hδf hδc) (lt_min hδs (lt_min one_pos B.h₀_pos))
  have hδf' : δ ≤ δf := le_trans (min_le_left _ _) (min_le_left _ _)
  have hδc' : δ ≤ δc := le_trans (min_le_left _ _) (min_le_right _ _)
  have hδs' : δ ≤ δs := le_trans (min_le_right _ _) (min_le_left _ _)
  have hδ1 : δ ≤ 1 :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hδh₀ : δ ≤ B.h₀ :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  -- for `0 < h < δ`: the window and the three sub-windows
  have hwin : ∀ h : ℝ, 0 < h → h < δ → |h| < B.h₀ := fun h hh0 hhδ => by
    rw [abs_of_pos hh0]; exact lt_of_lt_of_le hhδ hδh₀
  have hcomp' : ∀ (h : ℝ) (hh : |h| < B.h₀), 0 < h → h < δ →
      |(B.graphon hh).edgeDensity - (B.rVal h - ((d : ℝ) - 1) * h ^ 2)| ≤ C * h ^ 4 ∧
      |(B.graphon hh).Ip (B.p h) - (Jp (B.p h) (B.rVal h) - (d : ℝ) ^ 3 / 3 * h ^ 4)|
        ≤ C * h ^ 6 := fun h hh hh0 hhδ => by
    have := hcomp h hh (by rw [abs_of_pos hh0]; exact lt_of_lt_of_le hhδ hδc')
    rwa [abs_of_pos hh0] at this
  have hfull' : ∀ (h : ℝ) (hh : |h| < B.h₀), 0 < h → h < δ →
      Feasible H (B.rVal h) (B.graphon hh) ∧
      ∀ W : Graphon, Feasible H (B.rVal h) W →
        (B.graphon hh).Ip (B.p h) ≤ W.Ip (B.p h) ∧
          (W.Ip (B.p h) ≤ (B.graphon hh).Ip (B.p h) →
            ∃ σ : ℝ → ℝ, IsRelabelling σ ∧
              ∀ᵐ z ∂gμ, W.toFun z.1 z.2 = (B.graphon hh).toFun (σ z.1) (σ z.2)) :=
    fun h hh hh0 hhδ =>
      hfull h hh hh0 (lt_of_lt_of_le hhδ hδf') (le_trans (le_of_lt hhδ) hδ1)
  have hsq := uStar_sq hd
  have S : SingularEndpointOptimizers H B C δ :=
    { delta_pos := hδpos
      delta_le := hδh₀
      analytic_curve := fun h hh => ⟨B.analyticAt_p h hh, KKTFamily.analyticAt_rVal hh⟩
      below_boundary := fun h hh0 hhδ =>
        hsb h (hwin h hh0 hhδ) hh0 (lt_of_lt_of_le hhδ hδs')
      parameter_limits := ⟨KKTFamily.tendsto_p_pcGlobal hd B, tendsto_rVal hd B⟩
      block_limit := ⟨tendsto_alph B, by
        have := (tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_alph B)
        norm_num at this ⊢
        exact this⟩
      factor_limits := ⟨tendsto_sVal B, tendsto_tVal B⟩
      density_limits := ⟨by simpa [hsq] using (tendsto_sVal B).pow 2,
        by simpa [← pow_two, hsq] using (tendsto_sVal B).mul (tendsto_tVal B),
        by simpa [hsq] using (tendsto_tVal B).pow 2⟩
      uniform_convergence := fun ε hε => KKTFamily.exists_graphon_unif hd B hε
      optimizers := fun h hh hh0 hhδ =>
        ⟨KKTFamily.graphon_rankOne hh, KKTFamily.graphon_isBipodal hh,
          KKTFamily.graphon_not_ae_const hd hh (ne_of_gt hh0),
          KKTFamily.graphon_tDensity_eq_rVal_pow H hd hreg hh, (hfull' h hh hh0 hhδ).2⟩
      edge_gap := fun h hh hh0 hhδ => (hcomp' h hh hh0 hhδ).1
      cost_gap := fun h hh0 hhδ => by
        have hh := hwin h hh0 hhδ
        obtain ⟨hfeas, hopt⟩ := hfull' h hh hh0 hhδ
        have hphi : phiVar H (B.p h) (B.rVal h) = (B.graphon hh).Ip (B.p h) := by
          unfold phiVar
          apply le_antisymm
          · exact csInf_le (phiVar_bddBelow H (B.p_mem h hh).1 (B.p_mem h hh).2)
              ⟨B.graphon hh, hfeas, rfl⟩
          · refine le_csInf ⟨_, B.graphon hh, hfeas, rfl⟩ ?_
            rintro y ⟨W, hW, rfl⟩
            exact (hopt W hW).1
        rw [hphi]
        exact (hcomp' h hh hh0 hhδ).2 }
  refine ⟨δ, { S with
    base_values := ⟨B.p_zero, KKTFamily.rVal_zero hd B, B.u_zero, B.alph_zero⟩
    analytic_parameters := fun h hh => ⟨B.analyticAt_u h hh, B.analyticAt_alph h hh⟩
    any_block := ?_ }⟩
  intro h hh0 hhδ A hA hAsub hAvol
  have hh := hwin h hh0 hhδ
  set f : ℝ → ℝ := fun x => A.indicator (fun _ => B.sVal h) x + Aᶜ.indicator (fun _ => B.tVal h) x
    with hfdef
  have hfm : Measurable f :=
    (measurable_const.indicator hA).add (measurable_const.indicator hA.compl)
  have hf01 : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1 := by
    intro x
    by_cases hx : x ∈ A
    · simp only [hfdef, Set.indicator_of_mem hx,
        Set.indicator_of_notMem (Set.notMem_compl_iff.mpr hx), add_zero]
      exact ⟨(KKTFamily.sVal_pos hh).le, (KKTFamily.sVal_lt_one hh).le⟩
    · simp only [hfdef, Set.indicator_of_notMem hx,
        Set.indicator_of_mem (Set.mem_compl hx), zero_add]
      exact ⟨(KKTFamily.tVal_pos hh).le, (KKTFamily.tVal_lt_one hh).le⟩
  have hfbip : ∀ x y, f x * f y
      = bipodalValue A (B.sVal h ^ 2) (B.sVal h * B.tVal h) (B.tVal h ^ 2) (x, y) := by
    intro x y
    by_cases hx : x ∈ A <;> by_cases hy : y ∈ A <;>
      simp [hfdef, bipodalValue, hx, hy] <;> ring
  let Wf : Graphon :=
    { toFun := fun x y => f x * f y
      symm' := fun x y => mul_comm _ _
      meas' := (hfm.comp measurable_fst).mul (hfm.comp measurable_snd)
      nonneg' := fun x y => mul_nonneg (hf01 x).1 (hf01 y).1
      le_one' := fun x y => mul_le_one₀ (hf01 x).2 (hf01 y).1 (hf01 y).2 }
  refine ⟨⟨Wf, fun x y => rfl⟩, fun W hWf => ?_⟩
  exact ⟨⟨f, hfm, hf01, hWf⟩,
    anyBlock_of_singularEndpointOptimizers H S hh hh0 hhδ hA hAsub hAvol
      (ae_of_all _ fun z => (hWf z.1 z.2).trans (hfbip z.1 z.2))⟩

end UpperTailOptimizers
