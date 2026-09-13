import UpperTailOptimizers.LocalOptimizer.Analytic
import UpperTailOptimizers.LZBoundary.Curve

/-!
# `thm:nonexceptional-endpoint`: local structure of regular-graph optimizers

`local_structure` assembles `thm:nonexceptional-endpoint` (Theorem 4.1) in global boundary
coordinates, including the coefficient and analytic-family properties; its `analyticFamily`
field states parts (b)–(d), with the smaller-pode convention `0 < c < 1/2`, on one window.
`main_bipodal_optimizer` in `Global.lean` is its introduction corollary. The proof starts with
the two sides:

* `replica_symmetric_unique` — part (a), `p ≥ pc(r)`: the constant graphon `W ≡ r` is the
  unique optimizer;
* `symmetry_breaking_side` — parts (b) and (c), `p < pc(r)`: the optimizer is unique up to
  relabelling, non-constant and bipodal, with the expansions
  `e(W_{p,r}) = r - λ/A_H(r) + O(λ²)` and `Φ_H(p,r) = J_p(r) - λ²/(2A_H(r)) + O(λ³)`.

`local_structure_on_arc` states both on one window `|r - r₀| < ρ`, `|p - pc(r)| < η`, with `ρ`, `η`
and the expansion constant independent of `r` and `p` — the uniformity the paper asserts.
`arc_gap_bounds` turns compactness of the `r`-interval into one margin `c` with
`pc(r) + c ≤ min(r, p_*)` and `c ≤ pc(r)`, which is what makes the window width uniform.  The
window is needed only by (b) and (c): as in the paper, the replica-symmetric half holds on the
whole range `pc(r) ≤ p < r`, which is `replica_symmetric_unique_global`.
-/

namespace UpperTailOptimizers

open MeasureTheory Real Set

/-- **Uniform gaps along a compact subarc.**  On a compact `K ⊆ U` there is one margin
`c > 0` with `pc(r) + c ≤ r`, `pc(r) + c ≤ p_*` and `c ≤ pc(r)` for every `r ∈ K`.  (The three
orderings `0 < pc r < r` and `pc r < p_*` hold pointwise; compactness makes the gap uniform.) -/
theorem arc_gap_bounds {d : ℕ} (M : LZBoundaryArc d) {K : Set ℝ}
    (hK : K ⊆ M.U) (hKc : IsCompact K) (hKne : K.Nonempty) :
    ∃ c : ℝ, 0 < c ∧ ∀ r ∈ K, M.pc r + c ≤ r ∧ M.pc r + c ≤ pStar d ∧ c ≤ M.pc r := by
  have hpc : ContinuousOn M.pc K := M.continuousOn_pc.mono hK
  set g : ℝ → ℝ := fun r => min (min (r - M.pc r) (pStar d - M.pc r)) (M.pc r) with hg
  have hgc : ContinuousOn g K := by
    refine continuousOn_min (continuousOn_min (continuousOn_id.sub hpc) ?_) hpc
    exact continuousOn_const.sub hpc
  have hgpos : ∀ r ∈ K, 0 < g r := by
    intro r hr
    obtain ⟨hpc0, hpcr, -⟩ := M.ordering r (hK hr)
    have hps := M.pcLtPStar r (hK hr)
    rw [hg]
    exact lt_min (lt_min (by linarith) (by linarith)) hpc0
  obtain ⟨rmin, hrminK, hmin⟩ := hKc.exists_isMinOn hKne hgc
  refine ⟨g rmin, hgpos rmin hrminK, fun r hr => ?_⟩
  have hle : g rmin ≤ g r := isMinOn_iff.mp hmin r hr
  have h1 : g r ≤ r - M.pc r :=
    le_trans (min_le_left _ _) (min_le_left _ _)
  have h2 : g r ≤ pStar d - M.pc r :=
    le_trans (min_le_left _ _) (min_le_right _ _)
  have h3 : g r ≤ M.pc r := min_le_right _ _
  exact ⟨by linarith, by linarith, by linarith⟩

/-- **`thm:local-optimizer-structure` (local regular-graph bipodal local structure).**  Let `H` be `d`-regular with
`d ≥ 2` and let `r₀` be a non-exceptional point of a regular Lubetzky–Zhao boundary arc.  Then there are
`ρ, η > 0` and a constant `C ≥ 0` such that for every `r` with `|r - r₀| < ρ` and every `p`
with `|p - pc(r)| < η` (which forces `0 < p < r`):

**(a)** If `pc(r) ≤ p` then `Φ_H(p,r) = J_p(r)`, the constant graphon `W ≡ r` attains it, and it
is the unique optimizer: every optimizer equals `r` almost everywhere.

**(b)** If `p < pc(r)` then there is an optimizer `W_*` which is bipodal and non-constant, and
every optimizer is `W_*` up to a measure-preserving relabelling.

**(c)** On that side `A_H(r) > 0` and, with `λ = λ(p,r)` the log-odds displacement,
`|e(W) - (r - λ/A_H(r))| ≤ C λ²` for every optimizer `W`, and
`|Φ_H(p,r) - (J_p(r) - λ²/(2 A_H(r)))| ≤ C λ³`.

The constants `ρ`, `η`, `C` are uniform: they do not depend on `r` or `p` in the stated
range. -/
theorem local_structure_on_arc {d : ℕ} (hd : 2 ≤ d) (M : LZBoundaryArc d)
    {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (hreg : ∀ v, H.degree v = d) (hm : 1 ≤ H.edgeFinset.card)
    {r₀ : ℝ} (hr₀U : r₀ ∈ M.U) (hr₀ex : r₀ ≠ rStar d) :
    ∃ ρ η C : ℝ, 0 < ρ ∧ 0 < η ∧ 0 ≤ C ∧
      ∀ r : ℝ, |r - r₀| < ρ → ∀ p : ℝ, |p - M.pc r| < η →
        0 < p ∧ p < r ∧
        (M.pc r ≤ p →
          phiVar H p r = Jp p r ∧
          (∀ hr' : r ∈ Set.Icc (0:ℝ) 1, (constGraphon r hr').Ip p = phiVar H p r) ∧
          (∀ W : Graphon, Feasible H r W → W.Ip p = phiVar H p r →
            ∀ᵐ z ∂gμ, W.toFun z.1 z.2 = r)) ∧
        (p < M.pc r →
          0 < AH H M r ∧
          ∃ Wstar : Graphon, Feasible H r Wstar ∧ Wstar.Ip p = phiVar H p r ∧
            IsBipodal Wstar ∧
            (¬ ∃ c : ℝ, ∀ᵐ z ∂gμ, Wstar.toFun z.1 z.2 = c) ∧
            (∀ W : Graphon, Feasible H r W → W.Ip p = phiVar H p r →
              ∃ σ : ℝ → ℝ, IsRelabelling σ ∧
                ∀ᵐ z ∂gμ, W.toFun z.1 z.2 = Wstar.toFun (σ z.1) (σ z.2)) ∧
            |Wstar.edgeDensity - (r - lambdaDisp M p r / AH H M r)|
              ≤ C * lambdaDisp M p r ^ 2 ∧
            |phiVar H p r - (Jp p r - lambdaDisp M p r ^ 2 / (2 * AH H M r))|
              ≤ C * lambdaDisp M p r ^ 3) := by
  classical
  obtain ⟨ρb, ηb, C, hρb0, hηb0, hC0, hsb⟩ :=
    symmetry_breaking_side hd M H hreg hm hr₀U hr₀ex
  obtain ⟨εU, hεU0, hεUsub⟩ := Metric.isOpen_iff.mp M.isOpen_U r₀ hr₀U
  obtain ⟨ρ, hρ_def⟩ : ∃ x : ℝ, x = min ρb (εU / 2) := ⟨_, rfl⟩
  have hρ0 : 0 < ρ := by rw [hρ_def]; exact lt_min hρb0 (by linarith)
  have hρρb : ρ ≤ ρb := by rw [hρ_def]; exact min_le_left _ _
  have hρεU : ρ ≤ εU / 2 := by rw [hρ_def]; exact min_le_right _ _
  obtain ⟨K, hK_def⟩ : ∃ S : Set ℝ, S = Set.Icc (r₀ - ρ) (r₀ + ρ) := ⟨_, rfl⟩
  have hKmem : ∀ r : ℝ, |r - r₀| ≤ ρ → r ∈ K := by
    intro r hr
    rw [hK_def]
    have h := abs_le.mp hr
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  have hKabs : ∀ r ∈ K, |r - r₀| ≤ ρ := by
    intro r hr
    rw [hK_def] at hr
    exact abs_le.mpr ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have hKsub : K ⊆ M.U := by
    intro r hr
    refine hεUsub ?_
    rw [Metric.mem_ball, Real.dist_eq]
    linarith [hKabs r hr]
  have hKc : IsCompact K := by rw [hK_def]; exact isCompact_Icc
  have hKne : K.Nonempty := ⟨r₀, hKmem r₀ (by simp; linarith)⟩
  obtain ⟨cgap, hcgap0, hgap⟩ := arc_gap_bounds M hKsub hKc hKne
  obtain ⟨η, hη_def⟩ : ∃ x : ℝ, x = min ηb (cgap / 2) := ⟨_, rfl⟩
  have hη0 : 0 < η := by rw [hη_def]; exact lt_min hηb0 (by linarith)
  have hηηb : η ≤ ηb := by rw [hη_def]; exact min_le_left _ _
  have hηc : η ≤ cgap / 2 := by rw [hη_def]; exact min_le_right _ _
  refine ⟨ρ, η, C, hρ0, hη0, hC0, ?_⟩
  intro r hrρ p hpη
  have hrK : r ∈ K := hKmem r hrρ.le
  have hrU : r ∈ M.U := hKsub hrK
  obtain ⟨hgr, hgps, hgpc⟩ := hgap r hrK
  obtain ⟨hlo, hhi⟩ := abs_lt.mp hpη
  have hp0 : 0 < p := by linarith
  have hpr : p < r := by linarith
  refine ⟨hp0, hpr, ?_, ?_⟩
  · -- (a) the replica-symmetric side
    intro hge
    exact replica_symmetric_unique hd M hrU hge hpr H hreg hm
  · -- (b), (c) the symmetry-breaking side
    intro hlt
    exact hsb r (lt_of_lt_of_le hrρ hρρb) p (by linarith) hlt

/-- **`thm:local-optimizer-structure`(a) on its full range**, in global boundary coordinates.
The window `|p - pc(r)| < η` of `local_structure_on_arc` is what parts (b) and (c) need; the
paper notes that the replica-symmetric half needs no restriction on `p - pc(r)` at all, and holds
for every `p ∈ [pc(r), r)`.  That is this statement: for every nonexceptional `r ∈ (0,1)` and
every `p` with `pcGlobal(r) ≤ p < r`, the upper-tail value is `J_p(r)`, the constant graphon
`W ≡ r` attains it, and every optimizer equals `r` almost everywhere. -/
theorem replica_symmetric_unique_global {d : ℕ} (hd : 2 ≤ d)
    {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (hreg : ∀ v, H.degree v = d) (hm : 1 ≤ H.edgeFinset.card)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (hrex : r ≠ rStar d)
    {p : ℝ} (hp_ge : pcGlobal d r ≤ p) (hpr : p < r) :
    phiVar H p r = Jp p r ∧
    (∀ hr' : r ∈ Set.Icc (0:ℝ) 1, (constGraphon r hr').Ip p = phiVar H p r) ∧
    (∀ W : Graphon, Feasible H r W → W.Ip p = phiVar H p r →
      ∀ᵐ z ∂gμ, W.toFun z.1 z.2 = r) := by
  obtain ⟨M, hrU, hrne⟩ := scalar_lz_boundary_arcs hd hr0 hr1 hrex
  rw [pcGlobal_eq_pc hd M hrU] at hp_ge
  exact replica_symmetric_unique hd M hrU hp_ge hpr H hreg hm



open Filter Topology

/-- **The global second-variation coefficient `A_H`** (`thm:nonexceptional-endpoint`), stated against the
global boundary curve `pcGlobal` and therefore independent of any chosen Lubetzky–Zhao boundary arc:
`A_H(r) = lim_{δ↓0} 2 (𝓕_{pc(r),r}(r-δ) - J_{pc(r)}(r))/δ²`. -/
noncomputable def AHGlobal {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (d : ℕ) (r : ℝ) : ℝ :=
  limUnder (𝓝[>] (0:ℝ)) (fun δ =>
    2 * (reducedObjective H (pcGlobal d r) (r - δ) (r ^ H.edgeFinset.card)
      - Jp (pcGlobal d r) r) / δ ^ 2)

/-- Every arc's second-variation coefficient is the restriction of the global one: `AH H M r`
depends on `M` only through the value `M.pc r`, which is `pcGlobal d r`. -/
theorem AH_eq_AHGlobal {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] {d : ℕ} (hd : 2 ≤ d) (M : LZBoundaryArc d) {r : ℝ} (hr : r ∈ M.U) :
    AH H M r = AHGlobal H d r := by
  simp only [AH, AHGlobal, boundaryExcess, pcGlobal_eq_pc hd M hr]

/-- **The global log-odds displacement** `λ(p,r) = log((1-p)/p) - log((1-pc(r))/pc(r))`,
stated against `pcGlobal`. -/
noncomputable def lambdaGlobal (d : ℕ) (p r : ℝ) : ℝ := logOdds p - logOdds (pcGlobal d r)

/-- Every arc's log-odds displacement is the restriction of the global one. -/
theorem lambdaDisp_eq_lambdaGlobal {d : ℕ} (hd : 2 ≤ d) (M : LZBoundaryArc d) {p r : ℝ}
    (hr : r ∈ M.U) : lambdaDisp M p r = lambdaGlobal d p r := by
  simp only [lambdaDisp, lambdaGlobal, pcGlobal_eq_pc hd M hr]

/-! ## The global coefficient in `thm:nonexceptional-endpoint`

The coefficient is analytic and positive at every nonexceptional density. These
properties are included in `local_structure` and inherited by Theorem 1.5. -/

/-- **`A_H` is real-analytic and strictly positive at every non-exceptional density.**

Pick a Lubetzky–Zhao boundary arc through `r` and a closed ball inside its window that avoids the exceptional
density; `boundaryExcess_taylor` gives analyticity of the arc coefficient `AH H M` there
together with the uniform lower bound `0 < CA ≤ AH H M`, and `AH_eq_AHGlobal` transfers both to
`AHGlobal` because the two agree on the *open* window. -/
theorem analyticAt_AHGlobal_and_pos {d : ℕ} (hd : 2 ≤ d)
    {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (hreg : ∀ v, H.degree v = d) (hm : 1 ≤ H.edgeFinset.card)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (hrex : r ≠ rStar d) :
    AnalyticAt ℝ (AHGlobal H d) r ∧ 0 < AHGlobal H d r := by
  obtain ⟨M, hrU, -⟩ := scalar_lz_boundary_arcs hd hr0 hr1 hrex
  obtain ⟨ε₁, hε₁, hball⟩ := Metric.isOpen_iff.mp M.isOpen_U r hrU
  have hgap : 0 < |r - rStar d| := abs_pos.mpr (sub_ne_zero.mpr hrex)
  obtain ⟨ε, hε, hεsub, hεex⟩ : ∃ ε : ℝ, 0 < ε ∧ Metric.closedBall r ε ⊆ M.U ∧
      ∀ x ∈ Metric.closedBall r ε, x ≠ rStar d := by
    refine ⟨min (ε₁ / 2) (|r - rStar d| / 2), lt_min (by linarith) (by linarith), ?_, ?_⟩
    · intro x hx
      rw [Metric.mem_closedBall] at hx
      refine hball (Metric.mem_ball.mpr ?_)
      exact lt_of_le_of_lt (le_trans hx (min_le_left _ _)) (by linarith)
    · rintro x hx rfl
      rw [Metric.mem_closedBall, Real.dist_eq, abs_sub_comm] at hx
      exact absurd (le_trans hx (min_le_right _ _)) (by linarith)
  obtain ⟨CA, -, -, hCA, -, -, hana, hlow, -⟩ :=
    boundaryExcess_taylor hd M hεsub (isCompact_closedBall r ε)
      ⟨r, Metric.mem_closedBall_self hε.le⟩ hεex H hreg hm
  have hrK : r ∈ Metric.closedBall r ε := Metric.mem_closedBall_self hε.le
  have hcongr : AH H M =ᶠ[𝓝 r] AHGlobal H d := by
    filter_upwards [M.isOpen_U.mem_nhds hrU] with x hx using AH_eq_AHGlobal H hd M hx
  refine ⟨(hana r hrK).congr hcongr, ?_⟩
  rw [← AH_eq_AHGlobal H hd M hrU]
  exact lt_of_lt_of_le hCA (hlow r hrK)

/-- The conclusions presented in Theorem 1.5, including the global coefficient.
The replica-symmetric clause is retained from `thm:nonexceptional-endpoint`(a). -/
structure NonexceptionalOptimizers {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (d : ℕ) (r₀ : ℝ) : Prop where
  coefficient : ∀ r : ℝ, 0 < r → r < 1 → r ≠ rStar d →
    AnalyticAt ℝ (AHGlobal H d) r ∧ 0 < AHGlobal H d r
  window :
    ∃ ρ η C : ℝ, 0 < ρ ∧ 0 < η ∧ 0 ≤ C ∧
      ∀ r : ℝ, |r - r₀| < ρ → ∀ p : ℝ, |p - pcGlobal d r| < η →
        0 < p ∧ p < r ∧
        (pcGlobal d r ≤ p →
          phiVar H p r = Jp p r ∧
          (∀ hr' : r ∈ Set.Icc (0:ℝ) 1, (constGraphon r hr').Ip p = phiVar H p r) ∧
          (∀ W : Graphon, Feasible H r W → W.Ip p = phiVar H p r →
            ∀ᵐ z ∂gμ, W.toFun z.1 z.2 = r)) ∧
        (p < pcGlobal d r →
          0 < AHGlobal H d r ∧
          ∃ Wstar : Graphon, Feasible H r Wstar ∧ Wstar.Ip p = phiVar H p r ∧
            IsBipodal Wstar ∧
            (¬ ∃ c : ℝ, ∀ᵐ z ∂gμ, Wstar.toFun z.1 z.2 = c) ∧
            (∀ W : Graphon, Feasible H r W → W.Ip p = phiVar H p r →
              ∃ σ : ℝ → ℝ, IsRelabelling σ ∧
                ∀ᵐ z ∂gμ, W.toFun z.1 z.2 = Wstar.toFun (σ z.1) (σ z.2)) ∧
            |Wstar.edgeDensity - (r - lambdaGlobal d p r / AHGlobal H d r)|
              ≤ C * lambdaGlobal d p r ^ 2 ∧
            |phiVar H p r - (Jp p r - lambdaGlobal d p r ^ 2 / (2 * AHGlobal H d r))|
              ≤ C * lambdaGlobal d p r ^ 3)

/-- **`thm:nonexceptional-endpoint`**: optimizer structure and asymptotics, with the positive
analytic global coefficient.

* `window` (inherited from `NonexceptionalOptimizers`) carries parts (a)–(c) on
  `|r - r₀| < ρ`, `|p - pc(r)| < η`.
* `analyticFamily` carries parts (b)–(d) for **one** analytic bipodal family
  `Dl, q₁₁, q₁₂, q₂₂, c` on **one** window `|r - r₀| < ρ`, `pc(r) - η < p < pc(r)`: analyticity
  of `Φ_H`, of the edge density `r - Dl` and of the four parameters; the optimizer `B` with first
  pode `[0, c]`, uniqueness up to relabelling, the edge-density and value expansions with one
  constant `Cd`; the smaller-pode convention `0 < c < 1/2` at every point of the window; and
  `c → 0` as `p ↑ pc(r)` for every `r` of the window.

Both windows are of the form "`|r - r₀| < ρ` and `p` within `η` of `pc(r)`", so all clauses hold on
their intersection; part (a) holds on the whole replica-symmetric range by
`replica_symmetric_unique_global`. -/
structure LocalOptimizerStructure {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (d : ℕ) (r₀ : ℝ)
    : Prop extends NonexceptionalOptimizers H d r₀ where
  analyticFamily :
    ∃ ρ η L Cd : ℝ, 0 < ρ ∧ 0 < η ∧ 0 ≤ L ∧ 0 ≤ Cd ∧
      ∃ (Dl : ℝ × ℝ → ℝ) (q11 q12 q22 cc : ℝ → ℝ → ℝ),
        (∀ r : ℝ, |r - r₀| < ρ → r ≠ rStar d ∧ 0 < r ∧ r < 1 ∧
          cc r 0 = 0 ∧ q22 r 0 = r ∧ q11 r 0 ∈ Set.Ioo (0:ℝ) 1 ∧
          q12 r 0 ∈ Set.Ioo (0:ℝ) 1 ∧ q12 r 0 ≠ r ∧
          AnalyticAt ℝ (fun s : ℝ => q12 s 0) r ∧
          Tendsto (fun p : ℝ => cc (r - Dl (p, r))
              (r ^ H.edgeFinset.card - (r - Dl (p, r)) ^ H.edgeFinset.card))
            (𝓝[<] (pcGlobal d r)) (𝓝 0)) ∧
        ∀ r : ℝ, |r - r₀| < ρ → ∀ p : ℝ, pcGlobal d r - η < p → p < pcGlobal d r →
          0 < p ∧ p < r ∧ 0 < AHGlobal H d r ∧ 0 < lambdaGlobal d p r ∧ 0 < Dl (p, r) ∧
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
          |Dl (p, r) - lambdaGlobal d p r / AHGlobal H d r| ≤ Cd * lambdaGlobal d p r ^ 2 ∧
          Dl (p, r) ≤ Cd * lambdaGlobal d p r ∧
          |phiVar H p r - (Jp p r - lambdaGlobal d p r ^ 2 / (2 * AHGlobal H d r))|
            ≤ Cd * lambdaGlobal d p r ^ 3 ∧
          ∃ ε θ : ℝ, ε = r - Dl (p, r) ∧
            θ = r ^ H.edgeFinset.card - ε ^ H.edgeFinset.card ∧
            q11 ε θ ∈ Set.Icc (0:ℝ) 1 ∧ q12 ε θ ∈ Set.Icc (0:ℝ) 1 ∧
            q22 ε θ ∈ Set.Icc (0:ℝ) 1 ∧ cc ε θ ∈ Set.Ioo (0:ℝ) (1 / 2) ∧
            |cc ε θ| ≤ L * Dl (p, r) ∧
            |q22 ε θ - r| ≤ L * Dl (p, r) ∧
            |q12 ε θ - q12 r 0| ≤ L * Dl (p, r) ∧
            |q11 ε θ - q11 r 0| ≤ L * Dl (p, r) ∧
            (∃ B : Graphon, Feasible H r B ∧ B.Ip p = phiVar H p r ∧
              B.edgeDensity = ε ∧ B.tDensity H = r ^ H.edgeFinset.card ∧
              (∀ᵐ z ∂gμ, B.toFun z.1 z.2
                = bipodalValue (Set.Icc 0 (cc ε θ)) (q11 ε θ) (q12 ε θ) (q22 ε θ) z))

/-- **`thm:nonexceptional-endpoint`**, assembled in the global boundary coordinates.
The arc is constructed internally. Theorem 1.5 is the projection onto
`NonexceptionalOptimizers`, with no additional analytic or optimization argument.  The
`analyticFamily` field is `bipodal_family_smallBlock` in global coordinates. -/
theorem local_structure {d : ℕ} (hd : 2 ≤ d)
    {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (hreg : ∀ v, H.degree v = d) (hm : 1 ≤ H.edgeFinset.card)
    {r₀ : ℝ} (hr₀0 : 0 < r₀) (hr₀1 : r₀ < 1) (hr₀ex : r₀ ≠ rStar d) : LocalOptimizerStructure H d r₀ := by
  refine { coefficient := ?_, window := ?_, analyticFamily := ?_ }
  · intro r hr0 hr1 hrex
    exact analyticAt_AHGlobal_and_pos hd H hreg hm hr0 hr1 hrex
  · obtain ⟨M, hr₀U, hr₀ne⟩ := scalar_lz_boundary_arcs hd hr₀0 hr₀1 hr₀ex
    obtain ⟨ρ0, η, C, hρ00, hη0, hC0, hmain⟩ := local_structure_on_arc hd M H hreg hm hr₀U hr₀ne
    obtain ⟨εU, hεU0, hεUsub⟩ := Metric.isOpen_iff.mp M.isOpen_U r₀ hr₀U
    refine ⟨min ρ0 εU, η, C, lt_min hρ00 hεU0, hη0, hC0, ?_⟩
    intro r hrρ p hpη
    have hrU : r ∈ M.U := by
      refine hεUsub ?_
      rw [Metric.mem_ball, Real.dist_eq]
      exact lt_of_lt_of_le hrρ (min_le_right _ _)
    rw [pcGlobal_eq_pc hd M hrU] at hpη ⊢
    simp only [← AH_eq_AHGlobal H hd M hrU, ← lambdaDisp_eq_lambdaGlobal hd M hrU]
    exact hmain r (lt_of_lt_of_le hrρ (min_le_left _ _)) p hpη
  · obtain ⟨M, hrU, hrne⟩ := scalar_lz_boundary_arcs hd hr₀0 hr₀1 hr₀ex
    obtain ⟨ρ, η, L, Cd, hρ, hη, hL, hCd, Dl, q11, q12, q22, cc, hbase, hfamily⟩ :=
      bipodal_family_smallBlock hd M H hreg hm hrU hrne
    refine ⟨ρ, η, L, Cd, hρ, hη, hL, hCd, Dl, q11, q12, q22, cc, ?_, ?_⟩
    · intro r hr
      obtain ⟨hrU', hrest⟩ := hbase r hr
      rw [pcGlobal_eq_pc hd M hrU']
      exact hrest
    · intro r hr p hp_lo hp_hi
      have hrU' : r ∈ M.U := (hbase r hr).1
      rw [pcGlobal_eq_pc hd M hrU'] at hp_lo hp_hi
      simpa only [AH_eq_AHGlobal H hd M hrU', lambdaDisp_eq_lambdaGlobal hd M hrU'] using
        hfamily r hr p hp_lo hp_hi

end UpperTailOptimizers
