import UpperTailOptimizers.LocalOptimizer.SymmetryBreaking
import UpperTailOptimizers.LZBoundary.AnalyticIFT

/-!
# Section 6 of `paper/bipodal_optimizer.tex`: the analytic family (the "Furthermore" clause of
`thm:local-optimizer-structure`)

`thm:local-optimizer-structure` closes with the assertion that, on the symmetry-breaking side, `Φ_H(p,r)` and
`e(W_{p,r})` are **analytic functions of `(p,r)`**.  Since `e(W_{p,r}) = r - δ_*(p,r)` and
`Φ_H(p,r) = J_p(r) + G_r(δ_*(p,r)) - λ(p,r) δ_*(p,r)` (both established in
`symmetry_breaking_core`), the whole clause reduces to: **the critical point `δ_*` is an
analytic function of `(p,r)`**, which is what the paper obtains from the analytic implicit
function theorem applied to

`Ψ(p, r, δ) = G_r'(δ) - λ(p,r) = 0`,   `∂_δ Ψ = G_r''(δ) = A_H(r) > 0`.

`analytic_critical_family_of_chart` carries out exactly that step, using the scalar analytic
implicit function theorem `analytic_implicit_scalar` (`LZBoundary/AnalyticIFT.lean`) with the
chart's `∂_δ Gc` as `Ψ`, and taking the chart itself as a hypothesis.

`bipodal_family` is the assembly.  It takes **one** chart (`boundaryExcess_chart_full`) and
feeds it to *both* `symmetry_breaking_core` and `analytic_critical_family_of_chart`, so the
two `Gc`'s are literally the same witness.  The two-sided root-uniqueness clause of
`tilted_critical_point` then identifies the implicit-function family `Δ` with the critical
point `δ_*` of the tilted problem, and everything glues: on the window,

* `Φ_H(p,r) = J_p(r) + Gc(r, Δ(p,r)) - λ(p,r) Δ(p,r)` is analytic in `(p,r)`;
* every optimizer has edge density exactly `r - Δ(p,r)`, an analytic function of `(p,r)`;
* the four Kenyon–Radin–Ren–Sadun parameter maps, evaluated at
  `(ε, τ - ε^m) = (r - Δ(p,r), r^m - (r - Δ(p,r))^m)`, are analytic in `(p,r)`, and the
  concrete two-block graphon they describe **is itself an optimizer**.

`symmetry_breaking_analytic` is the projection of that assembly onto the paper's statement.

**Two conventions.**  (i) `Φ_H` is asserted analytic only at genuine symmetry-breaking points
`p < pc(r)` — that is all that is true, since across the boundary the value function switches
to `J_p(r)`.  (ii) The uniqueness clause of `kenyonRadinRenSadun` is one-directional (every
optimizer is the axiom's chosen maximizer relabelled, and `MeasurePreserving σ` carries no
inverse), so "the optimizer *is* the bipodal graphon with these parameters" is rendered as:
that concrete graphon `B` is an optimizer, and every optimizer — `B` included — is `W_*` up to
a measure-preserving relabelling.  This is the convention already used by
`symmetry_breaking_side`.

No patching of local familyes over a compact set is needed (contrast the paper's proof): the
whole of Section 6 runs inside one chart at `r₀`, so a single implicit-function family
suffices.
-/

namespace UpperTailOptimizers

open MeasureTheory Real Set Filter Topology

/-! ### Joint analyticity of the scalar ingredients -/

/-- `J_p(u)` is jointly real-analytic in `(p, u)` on `(0,1)²`. -/
theorem analyticAt_Jp_prod {p u : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hu0 : 0 < u) (hu1 : u < 1) :
    AnalyticAt ℝ (fun q : ℝ × ℝ => Jp q.1 q.2) (p, u) := by
  have hform : (fun q : ℝ × ℝ => Jp q.1 q.2)
      = fun q : ℝ × ℝ => q.2 * Real.log (q.2 / q.1)
        + (1 - q.2) * Real.log ((1 - q.2) / (1 - q.1)) := rfl
  rw [hform]
  have h1 : AnalyticAt ℝ (fun q : ℝ × ℝ => Real.log (q.2 / q.1)) (p, u) := by
    refine analyticAt_log_comp (analyticAt_snd.div analyticAt_fst (ne_of_gt hp0)) ?_
    exact div_pos hu0 hp0
  have h2 : AnalyticAt ℝ (fun q : ℝ × ℝ => Real.log ((1 - q.2) / (1 - q.1))) (p, u) := by
    refine analyticAt_log_comp
      ((analyticAt_const.sub analyticAt_snd).div (analyticAt_const.sub analyticAt_fst)
        (by simpa using (by linarith : (1:ℝ) - p ≠ 0))) ?_
    exact div_pos (by simpa using (by linarith : (0:ℝ) < 1 - u))
      (by simpa using (by linarith : (0:ℝ) < 1 - p))
  exact (analyticAt_snd.mul h1).add ((analyticAt_const.sub analyticAt_snd).mul h2)

/-- The log-odds displacement `λ(p,r)` is jointly real-analytic. -/
theorem analyticAt_lambdaDisp {d : ℕ} (M : LZBoundaryArc d) {p r : ℝ}
    (hrU : r ∈ M.U) (hp0 : 0 < p) (hp1 : p < 1) :
    AnalyticAt ℝ (fun q : ℝ × ℝ => lambdaDisp M q.1 q.2) (p, r) := by
  obtain ⟨hpc0, hpcr, hr1, -⟩ := M.ordering r hrU
  have hpc1 : M.pc r < 1 := lt_trans hpcr hr1
  have h1 : AnalyticAt ℝ (fun q : ℝ × ℝ => Real.log ((1 - q.1) / q.1)) (p, r) := by
    refine analyticAt_log_comp ((analyticAt_const.sub analyticAt_fst).div analyticAt_fst
      (ne_of_gt hp0)) ?_
    exact div_pos (by simpa using (by linarith : (0:ℝ) < 1 - p)) hp0
  have hpcA : AnalyticAt ℝ (fun q : ℝ × ℝ => M.pc q.2) (p, r) :=
    (M.analytic_pc r hrU).comp analyticAt_snd
  have h2 : AnalyticAt ℝ (fun q : ℝ × ℝ => Real.log ((1 - M.pc q.2) / M.pc q.2)) (p, r) := by
    refine analyticAt_log_comp ((analyticAt_const.sub hpcA).div hpcA (ne_of_gt hpc0)) ?_
    exact div_pos (by simpa using (by linarith : (0:ℝ) < 1 - M.pc r)) hpc0
  exact h1.sub h2

/-! ### The analytic critical family -/

/-- **The critical point is an analytic function of `(p,r)`, chart-relative form.**  Given the
Section-5 chart as hypotheses, near a boundary point `(pc(rb), rb)` there is a real-analytic
`Δ` with `Δ(pc(rb), rb) = 0` solving the critical-point equation `∂_δ Gc(r, Δ(p,r)) = λ(p,r)`.

Taking the chart as a hypothesis (rather than calling `boundaryExcess_chart` internally) is
what lets `bipodal_family` run this step and `symmetry_breaking_core` on the **same** `Gc`. -/
theorem analytic_critical_family_of_chart {d : ℕ} (hd : 2 ≤ d) (M : LZBoundaryArc d)
    {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (hreg : ∀ v, H.degree v = d) (hm : 1 ≤ H.edgeFinset.card)
    {r₀ w ρc : ℝ} (hρc0 : 0 < ρc)
    {Gc : ℝ × ℝ → ℝ}
    (hG1A : ∀ r δ : ℝ, |r - r₀| < w → |δ| ≤ ρc → AnalyticAt ℝ (dDelta Gc) (r, δ))
    (hG10 : ∀ r : ℝ, |r - r₀| < w → dDelta Gc (r, 0) = 0)
    (hG2AH : ∀ r : ℝ, |r - r₀| < w → dDelta (dDelta Gc) (r, 0) = AH H M r)
    {rb : ℝ} (hrbw : |rb - r₀| < w) (hrbU : rb ∈ M.U) (hrbex : rb ≠ rStar d) :
    ∃ Δ : ℝ × ℝ → ℝ,
      AnalyticAt ℝ Δ (M.pc rb, rb) ∧
      Δ (M.pc rb, rb) = 0 ∧
      (∀ᶠ q : ℝ × ℝ in 𝓝 (M.pc rb, rb), dDelta Gc (q.2, Δ q) = lambdaDisp M q.1 q.2) := by
  classical
  obtain ⟨hpc0, hpcr, hrb1, -⟩ := M.ordering rb hrbU
  have hpc1 : M.pc rb < 1 := lt_trans hpcr hrb1
  -- the second `δ`-derivative at the boundary is `A_H(rb) > 0`
  have hAH0 : 0 < AH H M rb := by
    obtain ⟨CA, -, -, hCA0, -, -, -, hAHlow, -⟩ :=
      boundaryExcess_taylor hd M (Set.singleton_subset_iff.mpr hrbU) isCompact_singleton
        ⟨rb, rfl⟩ (fun s hs => (Set.mem_singleton_iff.mp hs) ▸ hrbex) H hreg hm
    exact lt_of_lt_of_le hCA0 (hAHlow rb rfl)
  -- the implicit equation `Ψ(δ, (p,r)) = ∂_δ Gc (r, δ) - λ(p,r)`
  set Ψ : ℝ → ℝ × ℝ → ℝ := fun z q => dDelta Gc (q.2, z) - lambdaDisp M q.1 q.2 with hΨ_def
  have hΨ0 : Ψ 0 (M.pc rb, rb) = 0 := by
    rw [hΨ_def]
    simp only [lambdaDisp_self]
    rw [hG10 rb hrbw]
    ring
  -- joint analyticity of `Ψ`
  have hΨana : AnalyticAt ℝ (fun v : ℝ × (ℝ × ℝ) => Ψ v.1 v.2) (0, (M.pc rb, rb)) := by
    rw [hΨ_def]
    have hswap : AnalyticAt ℝ (fun v : ℝ × (ℝ × ℝ) => ((v.2.2, v.1) : ℝ × ℝ))
        (0, (M.pc rb, rb)) :=
      (analyticAt_snd.comp analyticAt_snd).prod analyticAt_fst
    have h1 : AnalyticAt ℝ (fun v : ℝ × (ℝ × ℝ) => dDelta Gc (v.2.2, v.1))
        (0, (M.pc rb, rb)) :=
      (hG1A rb 0 hrbw (by rw [abs_zero]; exact hρc0.le)).fun_comp_of_eq hswap rfl
    have h2 : AnalyticAt ℝ (fun v : ℝ × (ℝ × ℝ) => lambdaDisp M v.2.1 v.2.2)
        (0, (M.pc rb, rb)) :=
      (analyticAt_lambdaDisp M hrbU hpc0 hpc1).fun_comp_of_eq
        (f := fun v : ℝ × (ℝ × ℝ) => v.2) analyticAt_snd rfl
    exact h1.sub h2
  -- the partial `δ`-derivative at the base point is `A_H(rb) ≠ 0`
  have hslice : AnalyticAt ℝ (fun z : ℝ => Ψ z (M.pc rb, rb)) 0 := by
    rw [hΨ_def]
    have h1 : AnalyticAt ℝ (fun z : ℝ => dDelta Gc (rb, z)) 0 :=
      (hG1A rb 0 hrbw (by rw [abs_zero]; exact hρc0.le)).fun_comp_of_eq
        (f := fun z : ℝ => ((rb, z) : ℝ × ℝ)) (analyticAt_const.prod analyticAt_id) rfl
    exact h1.sub analyticAt_const
  have hstrict : HasStrictDerivAt (fun z : ℝ => Ψ z (M.pc rb, rb)) (AH H M rb) 0 := by
    have hsd := hslice.hasStrictFDerivAt.hasStrictDerivAt
    have hval : fderiv ℝ (fun z : ℝ => Ψ z (M.pc rb, rb)) 0 1 = AH H M rb := by
      have hD : HasDerivAt (fun z : ℝ => Ψ z (M.pc rb, rb))
          (dDelta (dDelta Gc) (rb, 0)) 0 := by
        have h1 : HasDerivAt (fun z : ℝ => dDelta Gc (rb, z)) (dDelta (dDelta Gc) (rb, 0)) 0 :=
          hasDerivAt_dDelta
            (hG1A rb 0 hrbw (by rw [abs_zero]; exact hρc0.le)).differentiableAt
        simpa [hΨ_def] using h1.sub_const (lambdaDisp M (M.pc rb) rb)
      have h2 := hsd.hasDerivAt.unique hD
      rw [h2, hG2AH rb hrbw]
    rw [← hval]
    exact hsd
  obtain ⟨Δ, hΔ0, hΔsol, hΔana⟩ :=
    analytic_implicit_scalar hΨana hΨ0 (ne_of_gt hAH0) hstrict
  refine ⟨Δ, hΔana, hΔ0, ?_⟩
  filter_upwards [hΔsol] with q hq
  have := hq
  rw [hΨ_def] at this
  linarith [this]

/-- **The critical point is an analytic function of `(p,r)`.**  Near each boundary point
`(pc(rb), rb)` of the Section-6 window there is a real-analytic `Δ` with `Δ(pc(rb), rb) = 0`
solving the critical-point equation `∂_δ G_r(Δ(p,r)) = λ(p,r)`, and the induced value function

`(p,r) ↦ J_p(r) + G_r(Δ(p,r)) - λ(p,r)·Δ(p,r)`

is real-analytic there too.  This is the implicit-function step of the paper's "Furthermore"
clause, stated on its own; the finished clause, in which `Δ` is *identified* with the critical
point of the tilted problem and the value function with `Φ_H`, is `symmetry_breaking_analytic`.

The chart function `Gc` is returned together with its defining property
`Gc(r,δ) = G_r(δ)` on the Kenyon–Radin–Ren–Sadun regime, so the statement is about the actual
boundary excess. -/
theorem exists_analytic_critical_family {d : ℕ} (hd : 2 ≤ d) (M : LZBoundaryArc d)
    {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (hreg : ∀ v, H.degree v = d) (hm : 1 ≤ H.edgeFinset.card)
    {r₀ : ℝ} (hr₀U : r₀ ∈ M.U) (hr₀ex : r₀ ≠ rStar d) :
    ∃ w ρc : ℝ, 0 < w ∧ 0 < ρc ∧ ∃ Gc : ℝ × ℝ → ℝ,
      (∀ r δ : ℝ, |r - r₀| < w → 0 < δ → δ < ρc → boundaryExcess H M r δ = Gc (r, δ)) ∧
      ∀ rb : ℝ, |rb - r₀| < w → rb ∈ M.U → rb ≠ rStar d →
        ∃ Δ : ℝ × ℝ → ℝ,
          AnalyticAt ℝ Δ (M.pc rb, rb) ∧
          Δ (M.pc rb, rb) = 0 ∧
          (∀ᶠ q : ℝ × ℝ in 𝓝 (M.pc rb, rb),
            dDelta Gc (q.2, Δ q) = lambdaDisp M q.1 q.2) ∧
          AnalyticAt ℝ (fun q : ℝ × ℝ =>
            Jp q.1 q.2 + Gc (q.2, Δ q) - lambdaDisp M q.1 q.2 * Δ q) (M.pc rb, rb) := by
  classical
  obtain ⟨w, ρc, Mch, hw0, hρc0, hMch0, Gc, hGcA, hG1A, heqG, -, hG10, hG2AH, -, -⟩ :=
    boundaryExcess_chart hd M H hreg hm hr₀U hr₀ex
  refine ⟨w, ρc, hw0, hρc0, Gc, heqG, ?_⟩
  intro rb hrbw hrbU hrbex
  obtain ⟨Δ, hΔana, hΔ0, hΔsol⟩ :=
    analytic_critical_family_of_chart hd M H hreg hm hρc0 hG1A hG10 hG2AH hrbw hrbU hrbex
  obtain ⟨hpc0, hpcr, hrb1, -⟩ := M.ordering rb hrbU
  have hrb0 : 0 < rb := lt_trans hpc0 hpcr
  have hpc1 : M.pc rb < 1 := lt_trans hpcr hrb1
  refine ⟨Δ, hΔana, hΔ0, hΔsol, ?_⟩
  have hJ : AnalyticAt ℝ (fun q : ℝ × ℝ => Jp q.1 q.2) (M.pc rb, rb) :=
    analyticAt_Jp_prod hpc0 hpc1 hrb0 hrb1
  have hGΔ : AnalyticAt ℝ (fun q : ℝ × ℝ => Gc (q.2, Δ q)) (M.pc rb, rb) := by
    have hpair : AnalyticAt ℝ (fun q : ℝ × ℝ => ((q.2, Δ q) : ℝ × ℝ)) (M.pc rb, rb) :=
      analyticAt_snd.prod hΔana
    have hbase : ((rb, Δ (M.pc rb, rb)) : ℝ × ℝ) = (rb, 0) := by rw [hΔ0]
    have hGat : AnalyticAt ℝ Gc (rb, Δ (M.pc rb, rb)) := by
      rw [hbase]
      exact hGcA rb 0 hrbw (by rw [abs_zero]; exact hρc0.le)
    exact hGat.fun_comp_of_eq hpair rfl
  have hlamA : AnalyticAt ℝ (fun q : ℝ × ℝ => lambdaDisp M q.1 q.2) (M.pc rb, rb) :=
    analyticAt_lambdaDisp M hrbU hpc0 hpc1
  exact (hJ.add hGΔ).sub (hlamA.mul hΔana)

/-! ### The analytic bipodal family -/

/-- **The analytic bipodal family: one chart for both halves of Section 6.**

On a window `|r - r₀| < ρ`, `pc(r) - η < p < pc(r)` there are an analytic edge-density deficit
`Δ = Dl` and the four Kenyon–Radin–Ren–Sadun parameter maps `q₁₁, q₁₂, q₂₂, c` such that

* `Φ_H` and `(p,r) ↦ r - Δ(p,r)` are analytic at `(p,r)`, and every optimizer has edge
  density **exactly** `r - Δ(p,r)`;
* the four parameter maps, composed with the substitution
  `(ε, τ - ε^m) = (r - Δ(p,r), r^m - (r - Δ(p,r))^m)`, are analytic at `(p,r)`;
* the concrete two-block graphon `B` with first pode `[0, c(ε,θ)]` and densities
  `q₁₁(ε,θ), q₁₂(ε,θ), q₂₂(ε,θ)` **is an optimizer**, and every optimizer (hence `B` too) is a
  measure-preserving relabelling of the bipodal, non-constant `W_*`;
* the family obeys `|Δ - λ/A_H| ≤ Cd λ²` and `Δ ≤ Cd λ`, and the parameters obey the a-priori
  bounds `|c| ≤ L Δ`, `|q₂₂ - r| ≤ L Δ`, `|q₁₂ - ζ_d(r)| ≤ L Δ`, `|q₁₁ - q₁₁⁰(r)| ≤ L Δ`
  with `ζ_d(r) = q₁₂(r,0)` and `q₁₁⁰(r) = q₁₁(r,0)` (the input `rmk:bipodal-parameter-expansions` linearises).

This is the theorem that closes the gap left open by the earlier pairing of
`symmetry_breaking_side` with `exists_analytic_critical_family`: both halves are run on the
*same* chart, and the two-sided root uniqueness of `tilted_critical_point` identifies the
implicit-function family with the tilted problem's critical point. -/
theorem bipodal_family {d : ℕ} (hd : 2 ≤ d) (M : LZBoundaryArc d)
    {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (hreg : ∀ v, H.degree v = d) (hm : 1 ≤ H.edgeFinset.card)
    {r₀ : ℝ} (hr₀U : r₀ ∈ M.U) (hr₀ex : r₀ ≠ rStar d) :
    ∃ ρ η L Cd : ℝ, 0 < ρ ∧ 0 < η ∧ 0 ≤ L ∧ 0 ≤ Cd ∧
      ∃ (Dl : ℝ × ℝ → ℝ) (q11 q12 q22 cc : ℝ → ℝ → ℝ),
        (∀ r : ℝ, |r - r₀| < ρ → r ∈ M.U ∧ r ≠ rStar d ∧ 0 < r ∧ r < 1 ∧
          cc r 0 = 0 ∧ q22 r 0 = r ∧ q11 r 0 ∈ Set.Ioo (0:ℝ) 1 ∧
          q12 r 0 ∈ Set.Ioo (0:ℝ) 1 ∧ q12 r 0 ≠ r ∧
          AnalyticAt ℝ (fun s : ℝ => q12 s 0) r) ∧
        ∀ r : ℝ, |r - r₀| < ρ → ∀ p : ℝ, M.pc r - η < p → p < M.pc r →
          0 < p ∧ p < r ∧ 0 < AH H M r ∧ 0 < lambdaDisp M p r ∧ 0 < Dl (p, r) ∧
          AnalyticAt ℝ Dl (p, r) ∧
          AnalyticAt ℝ (fun q : ℝ × ℝ => phiVar H q.1 q.2) (p, r) ∧
          AnalyticAt ℝ (fun q : ℝ × ℝ => q.2 - Dl q) (p, r) ∧
          AnalyticAt ℝ (fun q : ℝ × ℝ => q11 (q.2 - Dl q)
            (q.2 ^ H.edgeFinset.card - (q.2 - Dl q) ^ H.edgeFinset.card)) (p, r) ∧
          AnalyticAt ℝ (fun q : ℝ × ℝ => q12 (q.2 - Dl q)
            (q.2 ^ H.edgeFinset.card - (q.2 - Dl q) ^ H.edgeFinset.card)) (p, r) ∧
          AnalyticAt ℝ (fun q : ℝ × ℝ => q22 (q.2 - Dl q)
            (q.2 ^ H.edgeFinset.card - (q.2 - Dl q) ^ H.edgeFinset.card)) (p, r) ∧
          AnalyticAt ℝ (fun q : ℝ × ℝ => cc (q.2 - Dl q)
            (q.2 ^ H.edgeFinset.card - (q.2 - Dl q) ^ H.edgeFinset.card)) (p, r) ∧
          (∀ W : Graphon, Feasible H r W → W.Ip p = phiVar H p r →
            W.edgeDensity = r - Dl (p, r)) ∧
          (∃ Wstar : Graphon, Feasible H r Wstar ∧ Wstar.Ip p = phiVar H p r ∧
            IsBipodal Wstar ∧ (¬ ∃ c : ℝ, ∀ᵐ z ∂gμ, Wstar.toFun z.1 z.2 = c) ∧
            ∀ W : Graphon, Feasible H r W → W.Ip p = phiVar H p r →
              ∃ σ : ℝ → ℝ, IsRelabelling σ ∧
                ∀ᵐ z ∂gμ, W.toFun z.1 z.2 = Wstar.toFun (σ z.1) (σ z.2)) ∧
          |Dl (p, r) - lambdaDisp M p r / AH H M r| ≤ Cd * lambdaDisp M p r ^ 2 ∧
          Dl (p, r) ≤ Cd * lambdaDisp M p r ∧
          ∃ ε θ : ℝ, ε = r - Dl (p, r) ∧
            θ = r ^ H.edgeFinset.card - ε ^ H.edgeFinset.card ∧
            q11 ε θ ∈ Set.Icc (0:ℝ) 1 ∧ q12 ε θ ∈ Set.Icc (0:ℝ) 1 ∧
            q22 ε θ ∈ Set.Icc (0:ℝ) 1 ∧ cc ε θ ∈ Set.Icc (0:ℝ) 1 ∧
            |cc ε θ| ≤ L * Dl (p, r) ∧
            |q22 ε θ - r| ≤ L * Dl (p, r) ∧
            |q12 ε θ - q12 r 0| ≤ L * Dl (p, r) ∧
            |q11 ε θ - q11 r 0| ≤ L * Dl (p, r) ∧
            (∃ B : Graphon, Feasible H r B ∧ B.Ip p = phiVar H p r ∧
              B.edgeDensity = ε ∧ B.tDensity H = r ^ H.edgeFinset.card ∧
              (∀ᵐ z ∂gμ, B.toFun z.1 z.2
                = bipodalValue (Set.Icc 0 (cc ε θ)) (q11 ε θ) (q12 ε θ) (q22 ε θ) z)) := by
  classical
  -- ### One chart, used by both halves
  obtain ⟨w, ρch, Mch, hw0, hρch0, hMch0, Gc, q11, q12, q22, cc,
    hGcA, hG1A, heqG, -, hG10, hG2AH, hlipG, htayG, hparA, hparIoo, hbdry, hmaxKR⟩ :=
    boundaryExcess_chart_full hd M H hreg hm hr₀U hr₀ex
  have hhalf0 : (0:ℝ) < ρch / 2 := by linarith
  have hhalf : ∀ δ : ℝ, |δ| ≤ ρch / 2 → |δ| ≤ ρch := fun δ h => by linarith
  -- ### The scalar half, on the halved box
  obtain ⟨ρ₁, η₁, δ₀, C₁, hρ₁0, hη₁0, hδ₀0, hC₁0, hδ₀ρc, hρ₁w, hwin, hmain⟩ :=
    symmetry_breaking_core hd M H hreg hm hw0 hhalf0 hMch0 hr₀U hr₀ex
      (fun r δ hr hδ => hGcA r δ hr (hhalf δ hδ))
      (fun r δ hr hδ => hG1A r δ hr (hhalf δ hδ))
      (fun r δ hr hδ0 hδρ => heqG r δ hr hδ0 (by linarith))
      hG10
      (fun r δ hr hδ => hlipG r δ hr (hhalf δ hδ))
      (fun r δ hr hδ0 hδρ => htayG r δ hr hδ0 (by linarith))
  -- ### The analytic half, on the same chart, at the single base point `r₀`
  obtain ⟨Dl, hDlana, hDl0, hDlsol⟩ :=
    analytic_critical_family_of_chart hd M H hreg hm hhalf0
      (fun r δ hr hδ => hG1A r δ hr (hhalf δ hδ)) hG10 hG2AH
      (rb := r₀) (by rw [sub_self, abs_zero]; exact hw0) hr₀U hr₀ex
  -- ### The a-priori parameter bounds
  obtain ⟨L, hL0, hLip⟩ := krrs_parameter_lipschitz (r₀ := r₀) hw0 hρch0 hparA
    (fun r hr => ⟨(hbdry r hr).1, (hbdry r hr).2.1⟩)
  -- ### A ball around `(pc(r₀), r₀)` on which the family is analytic, solves, and is small
  have hEv : ∀ᶠ q : ℝ × ℝ in 𝓝 (M.pc r₀, r₀),
      AnalyticAt ℝ Dl q ∧ dDelta Gc (q.2, Dl q) = lambdaDisp M q.1 q.2 ∧
        Dl q ∈ Set.Ioo (-δ₀) δ₀ := by
    have e1 : ∀ᶠ q : ℝ × ℝ in 𝓝 (M.pc r₀, r₀), AnalyticAt ℝ Dl q :=
      (isOpen_analyticAt ℝ Dl).mem_nhds hDlana
    have e3 : ∀ᶠ q : ℝ × ℝ in 𝓝 (M.pc r₀, r₀), Dl q ∈ Set.Ioo (-δ₀) δ₀ :=
      hDlana.continuousAt.preimage_mem_nhds
        (isOpen_Ioo.mem_nhds (by rw [hDl0]; exact ⟨by linarith, hδ₀0⟩))
    filter_upwards [e1, hDlsol, e3] with q h1 h2 h3 using ⟨h1, h2, h3⟩
  obtain ⟨ν, hν0, hballν⟩ := Metric.eventually_nhds_iff_ball.mp hEv
  -- ### Shrinking the window so that it sits inside that ball
  obtain ⟨ρpc, hρpc0, hρpc⟩ :=
    Metric.continuousAt_iff.mp ((M.analytic_pc r₀ hr₀U).continuousAt) (ν / 2) (by linarith)
  obtain ⟨ρ, hρ_def⟩ : ∃ x : ℝ, x = min ρ₁ (min (ν / 4) ρpc) := ⟨_, rfl⟩
  have hρ0 : 0 < ρ := by
    rw [hρ_def]; exact lt_min hρ₁0 (lt_min (by linarith) hρpc0)
  have hρρ₁ : ρ ≤ ρ₁ := by rw [hρ_def]; exact min_le_left _ _
  have hρν : ρ ≤ ν / 4 := by rw [hρ_def]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hρpcle : ρ ≤ ρpc := by
    rw [hρ_def]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  obtain ⟨η, hη_def⟩ : ∃ x : ℝ, x = min η₁ (ν / 4) := ⟨_, rfl⟩
  have hη0 : 0 < η := by rw [hη_def]; exact lt_min hη₁0 (by linarith)
  have hηη₁ : η ≤ η₁ := by rw [hη_def]; exact min_le_left _ _
  have hην : η ≤ ν / 4 := by rw [hη_def]; exact min_le_right _ _
  have hballmem : ∀ r : ℝ, |r - r₀| < ρ → ∀ p : ℝ, M.pc r - η < p → p < M.pc r →
      ((p, r) : ℝ × ℝ) ∈ Metric.ball ((M.pc r₀, r₀) : ℝ × ℝ) ν := by
    intro r hrρ p hp_lo hp_hi
    have hpcd : dist (M.pc r) (M.pc r₀) < ν / 2 := by
      refine hρpc ?_
      rw [Real.dist_eq]
      linarith
    rw [Real.dist_eq] at hpcd
    rw [Metric.mem_ball, Prod.dist_eq]
    have h2 : dist r r₀ < ν := by rw [Real.dist_eq]; linarith
    have h1 : dist p (M.pc r₀) < ν := by
      rw [Real.dist_eq]
      have hpη : |p - M.pc r| < η := by rw [abs_lt]; constructor <;> linarith
      calc |p - M.pc r₀| ≤ |p - M.pc r| + |M.pc r - M.pc r₀| := abs_sub_le _ _ _
        _ < η + ν / 2 := by linarith
        _ ≤ ν := by linarith
    exact max_lt h1 h2
  -- ### The identification of the analytic family with the tilted critical point
  have key : ∀ r : ℝ, |r - r₀| < ρ → ∀ p : ℝ, M.pc r - η < p → p < M.pc r →
      0 < p ∧ p < r ∧ r ∈ M.U ∧ 0 < r ∧ r < 1 ∧
      0 < AH H M r ∧ 0 < lambdaDisp M p r ∧
      Dl (p, r) ∈ Set.Ioo (0:ℝ) δ₀ ∧
      AnalyticAt ℝ Dl (p, r) ∧
      phiVar H p r = Jp p r + Gc (r, Dl (p, r)) - lambdaDisp M p r * Dl (p, r) ∧
      phiVar H p r = reducedObjective H p (r - Dl (p, r)) (r ^ H.edgeFinset.card) ∧
      (∀ W : Graphon, Feasible H r W → W.Ip p = phiVar H p r →
        W.edgeDensity = r - Dl (p, r)) ∧
      |Dl (p, r) - lambdaDisp M p r / AH H M r| ≤ C₁ * lambdaDisp M p r ^ 2 ∧
      Dl (p, r) ≤ C₁ * lambdaDisp M p r ∧
      (∃ Wstar : Graphon, Feasible H r Wstar ∧ Wstar.Ip p = phiVar H p r ∧
        IsBipodal Wstar ∧ (¬ ∃ c : ℝ, ∀ᵐ z ∂gμ, Wstar.toFun z.1 z.2 = c) ∧
        ∀ W : Graphon, Feasible H r W → W.Ip p = phiVar H p r →
          ∃ σ : ℝ → ℝ, IsRelabelling σ ∧
            ∀ᵐ z ∂gμ, W.toFun z.1 z.2 = Wstar.toFun (σ z.1) (σ z.2)) := by
    intro r hrρ p hp_lo hp_hi
    have hrρ₁ : |r - r₀| < ρ₁ := lt_of_lt_of_le hrρ hρρ₁
    obtain ⟨hrU, -, hηpc⟩ := hwin r hrρ₁
    obtain ⟨hpc0, hpcr, hr1, -⟩ := M.ordering r hrU
    have hr0 : 0 < r := lt_trans hpc0 hpcr
    have hp0 : 0 < p := by linarith [hηη₁, hηpc]
    have hpr : p < r := lt_trans hp_hi hpcr
    obtain ⟨hAH0, hlam0, ds, hds, hdseq, hdsroot, hPhiF, hPhiG, hedge, -, hdsC,
      Wstar, hWfeas, hWopt, hWse, hWbip, hWnc, hWrel, hWedge, -⟩ :=
      hmain r hrρ₁ p (by linarith [hηη₁]) hp_hi
    obtain ⟨hDlA, hDleq, hDlIoo⟩ := hballν _ (hballmem r hrρ p hp_lo hp_hi)
    have hDlds : Dl (p, r) = ds :=
      hdsroot (Dl (p, r)) ⟨hDlIoo.1.le, hDlIoo.2.le⟩ hDleq
    rw [hDlds]
    refine ⟨hp0, hpr, hrU, hr0, hr1, hAH0, hlam0, hds, hDlA,
      by linarith [hPhiG], hPhiF, hedge, ?_, hdsC,
      Wstar, hWfeas, hWopt, hWbip, hWnc, hWrel⟩
    have h := hWedge
    rw [hWse] at h
    have hrw : |r - ds - (r - lambdaDisp M p r / AH H M r)|
        = |ds - lambdaDisp M p r / AH H M r| := by
      rw [abs_sub_comm]; congr 1; ring
    rw [hrw] at h
    exact h
  -- ### The output
  refine ⟨ρ, η, L, C₁, hρ0, hη0, hL0, hC₁0, Dl, q11, q12, q22, cc, ?_, ?_⟩
  · -- the boundary-value clause
    intro r hrρ
    have hrw : |r - r₀| < w := by linarith [hρρ₁, hρ₁w, hrρ]
    obtain ⟨hrU, hrex, -⟩ := hwin r (lt_of_lt_of_le hrρ hρρ₁)
    obtain ⟨hpc0, hpcr, hr1, -⟩ := M.ordering r hrU
    obtain ⟨hc0, hq220, hq110, hq120, hq12ne⟩ := hbdry r hrw
    have hq12A : AnalyticAt ℝ (fun s : ℝ => q12 s 0) r := by
      have h0 := (hparA r 0 hrw (by rw [abs_zero]; exact hρch0.le)).2.1
      have h1 : AnalyticAt ℝ (fun s : ℝ =>
          q12 (s - 0) (s ^ H.edgeFinset.card - (s - 0) ^ H.edgeFinset.card)) r :=
        h0.fun_comp_of_eq (analyticAt_id.prod analyticAt_const) rfl
      refine h1.congr ?_
      filter_upwards with s
      simp
    exact ⟨hrU, hrex, lt_trans hpc0 hpcr, hr1, hc0, hq220, hq110, hq120, hq12ne, hq12A⟩
  intro r hrρ p hp_lo hp_hi
  obtain ⟨hp0, hpr, hrU, hr0, hr1, hAH0, hlam0, hDls, hDlA, hPhiG, hPhiF, hedge,
    hDlexp, hDlC, hWpack⟩ := key r hrρ p hp_lo hp_hi
  have hrw : |r - r₀| < w := by linarith [hρρ₁, hρ₁w, hrρ]
  have hp1 : p < 1 := lt_trans hpr hr1
  have hDlabs : |Dl (p, r)| ≤ ρch := by
    rw [abs_of_pos hDls.1]; linarith [hDls.2, hδ₀ρc]
  have hDlabs' : |Dl (p, r)| ≤ ρch / 2 := by
    rw [abs_of_pos hDls.1]; linarith [hDls.2, hδ₀ρc]
  -- the pairing map `q ↦ (q.2, Dl q)`
  have hpair : AnalyticAt ℝ (fun q : ℝ × ℝ => ((q.2, Dl q) : ℝ × ℝ)) (p, r) :=
    analyticAt_snd.prod hDlA
  -- analyticity of `Φ_H`
  have hPhiA : AnalyticAt ℝ (fun q : ℝ × ℝ => phiVar H q.1 q.2) (p, r) := by
    have hJ : AnalyticAt ℝ (fun q : ℝ × ℝ => Jp q.1 q.2) (p, r) :=
      analyticAt_Jp_prod hp0 hp1 hr0 hr1
    have hG : AnalyticAt ℝ (fun q : ℝ × ℝ => Gc (q.2, Dl q)) (p, r) :=
      (hGcA r (Dl (p, r)) hrw hDlabs).fun_comp_of_eq hpair rfl
    have hlamA : AnalyticAt ℝ (fun q : ℝ × ℝ => lambdaDisp M q.1 q.2) (p, r) :=
      analyticAt_lambdaDisp M hrU hp0 hp1
    have hRHS : AnalyticAt ℝ
        (fun q : ℝ × ℝ => Jp q.1 q.2 + Gc (q.2, Dl q) - lambdaDisp M q.1 q.2 * Dl q) (p, r) :=
      (hJ.add hG).sub (hlamA.mul hDlA)
    refine hRHS.congr ?_
    have e1 : ∀ᶠ q : ℝ × ℝ in 𝓝 (p, r), |q.2 - r₀| < ρ := by
      refine IsOpen.mem_nhds ?_ hrρ
      exact isOpen_lt (continuous_abs.comp (continuous_snd.sub continuous_const))
        continuous_const
    have hpcAt : ContinuousAt (fun q : ℝ × ℝ => M.pc q.2) (p, r) :=
      ((M.analytic_pc r hrU).continuousAt).comp continuousAt_snd
    have e2 : ∀ᶠ q : ℝ × ℝ in 𝓝 (p, r), M.pc q.2 - η < q.1 :=
      (hpcAt.sub continuousAt_const).eventually_lt continuousAt_fst hp_lo
    have e3 : ∀ᶠ q : ℝ × ℝ in 𝓝 (p, r), q.1 < M.pc q.2 :=
      continuousAt_fst.eventually_lt hpcAt hp_hi
    filter_upwards [e1, e2, e3] with q h1 h2 h3
    exact ((key q.2 h1 q.1 h2 h3).2.2.2.2.2.2.2.2.2.1).symm
  -- analyticity of the composed parameter maps
  obtain ⟨hA11, hA12, hA22, hAcc⟩ := hparA r (Dl (p, r)) hrw hDlabs
  -- the parameter values
  obtain ⟨hI11, hI12, hI22⟩ := hparIoo r (Dl (p, r)) hrw hDlabs
  obtain ⟨hccIcc, Wk, hWke, hWkt, hWkmax, hWkae⟩ :=
    hmaxKR r (Dl (p, r)) hrw hDls.1 (by linarith [hDls.2, hδ₀ρc])
  obtain ⟨hLc, hL22, hL12, hL11⟩ := hLip r (Dl (p, r)) (by linarith [hρρ₁, hρ₁w, hrρ]) hDlabs'
  rw [abs_of_pos hDls.1] at hLc hL22 hL12 hL11
  -- the concrete bipodal optimizer
  obtain ⟨B, hB_def⟩ : ∃ B : Graphon, B = bipodalGraphon
      (Set.Icc 0 (cc (r - Dl (p, r))
        (r ^ H.edgeFinset.card - (r - Dl (p, r)) ^ H.edgeFinset.card)))
      measurableSet_Icc _ _ _ (Set.mem_Icc_of_Ioo hI11) (Set.mem_Icc_of_Ioo hI12)
      (Set.mem_Icc_of_Ioo hI22) := ⟨_, rfl⟩
  have hBae : ∀ᵐ z ∂gμ, Wk.toFun z.1 z.2 = B.toFun z.1 z.2 := by
    filter_upwards [hWkae] with z hz
    rw [hz, hB_def]
    rfl
  have hBe : B.edgeDensity = r - Dl (p, r) := by
    rw [← edgeDensity_congr_ae hBae]; exact hWke
  have hBt : B.tDensity H = r ^ H.edgeFinset.card := by
    rw [← tDensity_congr_ae H hBae]; exact hWkt
  have hBmax : ∀ W' : Graphon, W'.edgeDensity = r - Dl (p, r) →
      W'.tDensity H = r ^ H.edgeFinset.card → W'.entropy ≤ B.entropy := by
    intro W' h1 h2
    rw [← entropy_congr_ae hBae]
    exact hWkmax W' h1 h2
  have hBopt : B.Ip p = phiVar H p r := by
    rw [hPhiF, reducedObjective_eq_Ip H hp0 hp1 hBe hBt hBmax]
  refine ⟨hp0, hpr, hAH0, hlam0, hDls.1, hDlA, hPhiA, analyticAt_snd.sub hDlA,
    hA11.fun_comp_of_eq hpair rfl, hA12.fun_comp_of_eq hpair rfl,
    hA22.fun_comp_of_eq hpair rfl, hAcc.fun_comp_of_eq hpair rfl, hedge, hWpack, hDlexp, hDlC,
    r - Dl (p, r), r ^ H.edgeFinset.card - (r - Dl (p, r)) ^ H.edgeFinset.card,
    rfl, rfl, Set.mem_Icc_of_Ioo hI11, Set.mem_Icc_of_Ioo hI12, Set.mem_Icc_of_Ioo hI22,
    hccIcc, hLc, hL22, hL12, hL11, B, le_of_eq hBt.symm, hBopt, hBe, hBt, ?_⟩
  filter_upwards [hBae, hWkae] with z h1 h2
  rw [← h1, h2]

/-- **The "Furthermore" clause of `thm:local-optimizer-structure`.**  On the symmetry-breaking side of the window,

* the value function `Φ_H` is real-analytic in `(p,r)`;
* the edge density of the optimizer is `r - Δ(p,r)` for an analytic `Δ` with `Δ > 0` — the
  identity holds for *every* optimizer, so the clause carries its full content even though the
  development has no map `(p,r) ↦ W_{p,r}`;
* the four Kenyon–Radin–Ren–Sadun parameters, evaluated at
  `(ε, θ) = (e(W_{p,r}), r^m - e(W_{p,r})^m)`, are analytic in `(p,r)`;
* the optimizer is, up to relabelling, the bipodal graphon with first pode `[0, c(ε,θ)]` and
  densities `q₁₁(ε,θ), q₁₂(ε,θ), q₂₂(ε,θ)`: that concrete graphon `B` is itself an optimizer,
  and every optimizer — `B` included, by instantiating the last clause at `W := B` — is `W_*`
  up to a measure-preserving relabelling.

/-! ## Theorem 6.1(d): the block size vanishes at the boundary -/

/-- **`thm:local-optimizer-structure`(d), the pode size.**  For every `r` in the window supplied
by `bipodal_family` the first pode is nondegenerate, shrinks to nothing as `p ↑ pc(r)`, and is
therefore eventually the smaller of the two. -/
theorem exists_blockSize_pos_tendsto {d : ℕ} (hd : 2 ≤ d) (M : LZBoundaryArc d)
    {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (hreg : ∀ v, H.degree v = d) (hm : 1 ≤ H.edgeFinset.card)
    {r₀ : ℝ} (hr₀U : r₀ ∈ M.U) (hr₀ex : r₀ ≠ rStar d) :
    ∃ ρ η : ℝ, 0 < ρ ∧ 0 < η ∧ ∃ (Dl : ℝ × ℝ → ℝ) (cc : ℝ → ℝ → ℝ),
      ∀ r : ℝ, |r - r₀| < ρ →
        (∀ p : ℝ, M.pc r - η < p → p < M.pc r →
          0 < cc (r - Dl (p, r))
            (r ^ H.edgeFinset.card - (r - Dl (p, r)) ^ H.edgeFinset.card)) ∧
        Tendsto (fun p : ℝ => cc (r - Dl (p, r))
            (r ^ H.edgeFinset.card - (r - Dl (p, r)) ^ H.edgeFinset.card))
          (𝓝[<] (M.pc r)) (𝓝 0) ∧
        (∀ᶠ p in 𝓝[<] (M.pc r), cc (r - Dl (p, r))
            (r ^ H.edgeFinset.card - (r - Dl (p, r)) ^ H.edgeFinset.card) < 1 / 2) := by
  obtain ⟨ρ, η, L, Cd, hρ0, hη0, hL0, hCd0, Dl, q11, q12, q22, cc, hbase, hmain⟩ :=
    bipodal_family hd M H hreg hm hr₀U hr₀ex
  refine ⟨ρ, η, hρ0, hη0, Dl, cc, fun r hr => ?_⟩
  obtain ⟨hrU, -⟩ := hbase r hr
  -- positivity of the pode size
  have hpos : ∀ p : ℝ, M.pc r - η < p → p < M.pc r →
      0 < cc (r - Dl (p, r))
        (r ^ H.edgeFinset.card - (r - Dl (p, r)) ^ H.edgeFinset.card) := by
    intro p h1 h2
    obtain ⟨-, -, -, -, hDlpos, -, -, -, -, -, -, -, -, -, -, -, ε, θ, hε, hθ,
      -, -, -, hccI, -, -, -, -, Bg, -, -, hBe, hBtd, hBae⟩ := hmain r hr p h1 h2
    rw [← hε, ← hθ] at hccI ⊢
    refine blockSize_pos H hm Bg hccI.1 hBe ?_ hBtd hBae
    rw [hε]; linarith
  -- the limit
  have hlim : Tendsto (fun p : ℝ => cc (r - Dl (p, r))
      (r ^ H.edgeFinset.card - (r - Dl (p, r)) ^ H.edgeFinset.card))
      (𝓝[<] (M.pc r)) (𝓝 0) := by
    refine tendsto_blockSize_zero M hrU hη0 hL0 hCd0 ?_ ?_ ?_ <;> intro p h1 h2
    · exact (hpos p h1 h2).le
    · obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ε, θ, hε, hθ,
        -, -, -, -, hccb, -, -, -, -⟩ := hmain r hr p h1 h2
      rw [← hε, ← hθ] at hccb ⊢
      exact le_trans (le_abs_self _) hccb
    · obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hDlb, -⟩ := hmain r hr p h1 h2
      exact hDlb
  exact ⟨hpos, hlim, hlim.eventually (eventually_lt_nhds (by norm_num : (0:ℝ) < 1 / 2))⟩

/-- **The squeeze behind `c(p,r) → 0`.**  A nonnegative quantity bounded by a constant multiple
of `λ(p,r)` on a left neighbourhood of `pc(r)` tends to `0` as `p ↑ pc(r)`, because `λ` is
analytic and vanishes at `p = pc(r)`. -/
theorem tendsto_blockSize_zero {d : ℕ} (M : LZBoundaryArc d) {r : ℝ} (hrU : r ∈ M.U)
    {η L Cd : ℝ} (hη : 0 < η) (hL : 0 ≤ L) (hCd : 0 ≤ Cd)
    {Dl : ℝ × ℝ → ℝ} {c : ℝ → ℝ}
    (hc0 : ∀ p, M.pc r - η < p → p < M.pc r → 0 ≤ c p)
    (hcb : ∀ p, M.pc r - η < p → p < M.pc r → c p ≤ L * Dl (p, r))
    (hDl : ∀ p, M.pc r - η < p → p < M.pc r → Dl (p, r) ≤ Cd * lambdaDisp M p r) :
    Tendsto c (𝓝[<] (M.pc r)) (𝓝 0) := by
  obtain ⟨hpc0, hpcr, hr1, -⟩ := M.ordering r hrU
  have hpc1 : M.pc r < 1 := lt_trans hpcr hr1
  have hlam : Tendsto (fun p : ℝ => lambdaDisp M p r) (𝓝 (M.pc r)) (𝓝 0) := by
    have hcont : ContinuousAt (fun q : ℝ × ℝ => lambdaDisp M q.1 q.2) (M.pc r, r) :=
      (analyticAt_lambdaDisp M hrU hpc0 hpc1).continuousAt
    have hpair : Tendsto (fun p : ℝ => (p, r)) (𝓝 (M.pc r)) (𝓝 (M.pc r, r)) :=
      Continuous.tendsto (by fun_prop) _
    have h := hcont.tendsto.comp hpair
    simpa [Function.comp, lambdaDisp_self] using h
  have hup : Tendsto (fun p : ℝ => L * (Cd * lambdaDisp M p r)) (𝓝[<] (M.pc r)) (𝓝 0) := by
    have h := ((hlam.const_mul Cd).const_mul L).mono_left
      (nhdsWithin_le_nhds (a := M.pc r) (s := Set.Iio (M.pc r)))
    simpa using h
  have hev : ∀ᶠ p in 𝓝[<] (M.pc r), M.pc r - η < p ∧ p < M.pc r := by
    refine Filter.Eventually.and ?_ ?_
    · exact eventually_nhdsWithin_of_eventually_nhds
        (eventually_gt_nhds (by linarith : M.pc r - η < M.pc r))
    · exact eventually_nhdsWithin_of_forall fun p hp => hp
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [hev] with p hp using hc0 p hp.1 hp.2
  · filter_upwards [hev] with p hp
    exact le_trans (hcb p hp.1 hp.2)
      (mul_le_mul_of_nonneg_left (hDl p hp.1 hp.2) hL)


Analyticity is asserted only for `p < pc(r)`, which is exactly what the paper claims: at
`p = pc(r)` the value function is not analytic across the boundary.  This is a projection of
`bipodal_family`. -/
theorem symmetry_breaking_analytic {d : ℕ} (hd : 2 ≤ d) (M : LZBoundaryArc d)
    {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (hreg : ∀ v, H.degree v = d) (hm : 1 ≤ H.edgeFinset.card)
    {r₀ : ℝ} (hr₀U : r₀ ∈ M.U) (hr₀ex : r₀ ≠ rStar d) :
    ∃ ρ η : ℝ, 0 < ρ ∧ 0 < η ∧
      ∃ (Dl : ℝ × ℝ → ℝ) (q11 q12 q22 cc : ℝ → ℝ → ℝ),
        ∀ r : ℝ, |r - r₀| < ρ → ∀ p : ℝ, M.pc r - η < p → p < M.pc r →
          0 < Dl (p, r) ∧
          AnalyticAt ℝ (fun q : ℝ × ℝ => phiVar H q.1 q.2) (p, r) ∧
          AnalyticAt ℝ (fun q : ℝ × ℝ => q.2 - Dl q) (p, r) ∧
          (∀ W : Graphon, Feasible H r W → W.Ip p = phiVar H p r →
            W.edgeDensity = r - Dl (p, r)) ∧
          AnalyticAt ℝ (fun q : ℝ × ℝ => q11 (q.2 - Dl q)
            (q.2 ^ H.edgeFinset.card - (q.2 - Dl q) ^ H.edgeFinset.card)) (p, r) ∧
          AnalyticAt ℝ (fun q : ℝ × ℝ => q12 (q.2 - Dl q)
            (q.2 ^ H.edgeFinset.card - (q.2 - Dl q) ^ H.edgeFinset.card)) (p, r) ∧
          AnalyticAt ℝ (fun q : ℝ × ℝ => q22 (q.2 - Dl q)
            (q.2 ^ H.edgeFinset.card - (q.2 - Dl q) ^ H.edgeFinset.card)) (p, r) ∧
          AnalyticAt ℝ (fun q : ℝ × ℝ => cc (q.2 - Dl q)
            (q.2 ^ H.edgeFinset.card - (q.2 - Dl q) ^ H.edgeFinset.card)) (p, r) ∧
          ∃ ε θ : ℝ, ε = r - Dl (p, r) ∧
            θ = r ^ H.edgeFinset.card - ε ^ H.edgeFinset.card ∧
            ∃ Wstar B : Graphon,
              (Feasible H r Wstar ∧ Wstar.Ip p = phiVar H p r) ∧
              (Feasible H r B ∧ B.Ip p = phiVar H p r) ∧
              (∀ᵐ z ∂gμ, B.toFun z.1 z.2
                = bipodalValue (Set.Icc 0 (cc ε θ)) (q11 ε θ) (q12 ε θ) (q22 ε θ) z) ∧
              (∀ W : Graphon, Feasible H r W → W.Ip p = phiVar H p r →
                ∃ σ : ℝ → ℝ, IsRelabelling σ ∧
                  ∀ᵐ z ∂gμ, W.toFun z.1 z.2 = Wstar.toFun (σ z.1) (σ z.2)) := by
  classical
  obtain ⟨ρ, η, L, Cd, hρ0, hη0, -, -, Dl, q11, q12, q22, cc, -, hmain⟩ :=
    bipodal_family hd M H hreg hm hr₀U hr₀ex
  refine ⟨ρ, η, hρ0, hη0, Dl, q11, q12, q22, cc, ?_⟩
  intro r hrρ p hp_lo hp_hi
  obtain ⟨-, -, -, -, hDl0, -, hPhiA, hEdgeA, hA11, hA12, hA22, hAcc, hedge,
    ⟨Wstar, hWfeas, hWopt, -, -, hWrel⟩, -, -,
    ε, θ, hε, hθ, -, -, -, -, -, -, -, -, B, hBfeas, hBopt, -, -, hBae⟩ :=
    hmain r hrρ p hp_lo hp_hi
  exact ⟨hDl0, hPhiA, hEdgeA, hedge, hA11, hA12, hA22, hAcc, ε, θ, hε, hθ,
    Wstar, B, ⟨hWfeas, hWopt⟩, ⟨hBfeas, hBopt⟩, hBae, hWrel⟩

end UpperTailOptimizers
