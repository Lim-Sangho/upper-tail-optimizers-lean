import UpperTailOptimizers.Graphon.Functionals
import UpperTailOptimizers.Graphon.HomDensity
import UpperTailOptimizers.Graphon.CutContinuity
import UpperTailOptimizers.Graphon.Attainment
import UpperTailOptimizers.LZBoundary.Uniqueness
import UpperTailOptimizers.LZBoundary.Existence
import UpperTailOptimizers.Nondegeneracy.ArcBounds
import UpperTailOptimizers.KRRS.Main

/-!
# Section 4: the local reduction (`sec:local-reduction` of `paper/bipodal_optimizer.tex`)

Near a regular Lubetzky–Zhao boundary point, on the symmetry-broken side, the graphon
upper-tail problem reduces to a one-variable problem in the edge density.  This file
formalises the results of Section 4:

* **`lem:active-constraint`** `active_constraint` — every optimizer satisfies `t(H,W) = r^m`.
* **`lem:edge-density-deficit`** `edgeDensity_lt_of_no_support` / `edgeDensity_lt_broken` — on the broken
  side every optimizer has `e(W) < r`.
* **`lem:boundary-convergence`** `edgeDensity_tendsto_boundary` — optimizers along a sequence approaching the
  boundary have `e(W_n) → r₀` (with the cut-metric companion `cutDist_tendsto_boundary`:
  the whole sequence converges in cut distance to the constant graphon `r₀`).
* **`cor:scalar-reduction`** `scalar_reduction` — the uniform reduction
  `Φ_H(p,r) = min_ε F_{p,r}(ε)` (equation `eq:contact-projected-mean`, `eq:edge-density-minimization`), whose
  underlying entropy-maximizer statement is `lem:fixed-density-bipodality`.

The reduction engine comes in two grades.  `krrs_strip` and `reduction_core_uniform` follow
the paper's own quantifier order — one confinement bound `ρ₀`, then *any* `0 < ρ ≤ ρ₀`, then
one window width `η(ρ)` valid for **every** `r` in a compact subarc `K` — and export the
KRR-S maximizer family `Ŵ_{ε,r}` as a function.  That uniformity is what Section 6 consumes.
The single-density `reduction_core` is the `K = {r}` instance of it, and the three headline
statements of this section are unchanged.

The external inputs consumed are Lubetzky–Zhao (`thm:lz-criterion`, axiom `lubetzkyZhao`),
Kenyon–Radin–Ren–Sadun (`thm:krrs-analytic-extension`, `kenyonRadinRenSadun` of `KRRS/Main.lean`), the
generalized Hölder inequality (equation `eq:generalized-holder`, axiom `generalized_holder`, entering through
`holder_moment` inside `boundary_uniqueness`), and the four
graph-limit axioms of `Graphon/CutContinuity.lean` (`cut_seqCompact`,
`edgeDensity_cutContinuous`, `tDensity_cutContinuous`, `Ip_cut_lowerSemicontinuous`;
also via the theorem `feasible_attains`).  The broken-side
orientation is taken from the `LZBoundaryArc` record's `brokenSide` field (the `p < pc(r)` half of
condition (M2) of `thm:scalar-lz-boundary`), which `scalar_lz_boundary_arcs` discharges via
`arcMaps_brokenSide` — so it is **not** an axiom.
-/

namespace UpperTailOptimizers

open MeasureTheory Filter Topology

/-- The constant graphon `W ≡ r` is feasible for `(p,r)`. -/
theorem feasible_constGraphon {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] {r : ℝ} (hr : r ∈ Set.Icc (0:ℝ) 1) :
    Feasible H r (constGraphon r hr) :=
  le_of_eq (tDensity_constGraphon hr H).symm

/-- `Φ_H(p,r) ≤ J_p(r)`: the constant graphon is an admissible competitor. -/
theorem phiVar_le_Jp {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] {p r : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hr : r ∈ Set.Icc (0:ℝ) 1) :
    phiVar H p r ≤ Jp p r := by
  refine csInf_le (phiVar_bddBelow H hp0 hp1) ⟨constGraphon r hr, feasible_constGraphon H hr, ?_⟩
  rw [Ip_constGraphon hr p]

/-- **`lem:edge-density-deficit` (edge density below `r` on the broken side), abstract form.**  If the broken
side hypothesis holds — no supporting line at `r^d`, equivalently `Φ_H(p,r) < J_p(r)` via
Lubetzky–Zhao — then every optimizer has edge density strictly below `r`. -/
theorem edgeDensity_lt_of_no_support {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] {d : ℕ} (hd : 2 ≤ d) (hreg : ∀ v, H.degree v = d)
    (hm : 1 ≤ H.edgeFinset.card) {p r : ℝ}
    (hp0 : 0 < p) (hpr : p < r) (hr1 : r < 1)
    (hbroken : ¬ ∃ a : ℝ, ∀ x ∈ Set.Icc (0:ℝ) 1, Jp p r + a * (x - r ^ d) ≤ phi p d x)
    (W : Graphon) (_hWfeas : Feasible H r W) (hWopt : W.Ip p = phiVar H p r) :
    W.edgeDensity < r := by
  have hr0 : 0 < r := lt_trans hp0 hpr
  have hp1 : p < 1 := lt_trans hpr hr1
  have hr_mem : r ∈ Set.Icc (0:ℝ) 1 := ⟨hr0.le, hr1.le⟩
  -- `Φ < J_p(r)`: `≤` from the constant competitor, `≠` from Lubetzky–Zhao + broken side.
  have hle : phiVar H p r ≤ Jp p r := phiVar_le_Jp H hp0 hp1 hr_mem
  have hne : phiVar H p r ≠ Jp p r := fun h => hbroken ((lubetzkyZhao H hd hreg hm hp0 hpr hr1).mp h)
  have hlt : W.Ip p < Jp p r := by rw [hWopt]; exact lt_of_le_of_ne hle hne
  -- Jensen: `J_p(e(W)) ≤ I_p(W) < J_p(r)`.
  have hjensen : Jp p W.edgeDensity ≤ W.Ip p := Ip_jensen W hp0 hp1
  -- if `e(W) ≥ r`, monotonicity of `J_p` on `[p,1]` gives `J_p(r) ≤ J_p(e(W))`, contradiction.
  by_contra hge
  push Not at hge
  have hmono := (Jp_strictMonoOn_right hp0 hp1).monotoneOn
  have hr_mem' : r ∈ Set.Icc p 1 := ⟨hpr.le, hr1.le⟩
  have heW_mem : W.edgeDensity ∈ Set.Icc p 1 := ⟨le_trans hpr.le hge, edgeDensity_le_one W⟩
  have hmono' : Jp p r ≤ Jp p W.edgeDensity := hmono hr_mem' heW_mem hge
  linarith

/-- **`lem:edge-density-deficit`, Lubetzky–Zhao-arc form.**  On the broken side
`0 < p < pc(r)` of a regular Lubetzky–Zhao boundary arc, every optimizer has `e(W) < r`. -/
theorem edgeDensity_lt_broken {d : ℕ} (hd : 2 ≤ d) (M : LZBoundaryArc d) {r : ℝ} (hr : r ∈ M.U)
    {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (hreg : ∀ v, H.degree v = d) (hm : 1 ≤ H.edgeFinset.card)
    {p : ℝ} (hp0 : 0 < p) (hp : p < M.pc r)
    (W : Graphon) (hWfeas : Feasible H r W) (hWopt : W.Ip p = phiVar H p r) :
    W.edgeDensity < r := by
  obtain ⟨hpc0, hpcr, hr1, _⟩ := M.ordering r hr
  exact edgeDensity_lt_of_no_support H hd hreg hm hp0 (lt_trans hp hpcr) hr1
    (M.brokenSide r hr p hp0 hp) W hWfeas hWopt

/-! ### `lem:boundary-convergence`: convergence to the boundary optimizer. -/

/-- Continuity of `p ↦ log(1-p)` along a sequence converging to `p₀ ∈ (0,1)`. -/
theorem tendsto_log_one_sub {pk : ℕ → ℝ} {p₀ : ℝ} (_hp00 : 0 < p₀) (hp01 : p₀ < 1)
    (h : Tendsto pk atTop (𝓝 p₀)) :
    Tendsto (fun k => Real.log (1 - pk k)) atTop (𝓝 (Real.log (1 - p₀))) := by
  have h1 : Tendsto (fun k => 1 - pk k) atTop (𝓝 (1 - p₀)) := tendsto_const_nhds.sub h
  exact (Real.continuousAt_log (show (0:ℝ) < 1 - p₀ by linarith).ne').tendsto.comp h1

/-- Continuity of `p ↦ log((1-p)/p)` along a sequence converging to `p₀ ∈ (0,1)`. -/
theorem tendsto_log_ratio {pk : ℕ → ℝ} {p₀ : ℝ} (hp00 : 0 < p₀) (hp01 : p₀ < 1)
    (h : Tendsto pk atTop (𝓝 p₀)) :
    Tendsto (fun k => Real.log ((1 - pk k) / pk k)) atTop (𝓝 (Real.log ((1 - p₀) / p₀))) := by
  have h1 : Tendsto (fun k => (1 - pk k) / pk k) atTop (𝓝 ((1 - p₀) / p₀)) :=
    (tendsto_const_nhds.sub h).div h hp00.ne'
  exact (Real.continuousAt_log
    (div_ne_zero (show (0:ℝ) < 1 - p₀ by linarith).ne' hp00.ne')).tendsto.comp h1

/-- **Shared core of `lem:boundary-convergence`.**  Along any index map `ns → ∞`, cut-compactness extracts a
further subsequence `ns ∘ φ` whose graphons cut-converge to a limit `W_*` that is `≡ r₀`
almost everywhere (feasibility from cut-continuity of `t(H,·)`; `I_{p₀}(W_*) ≤ J_{p₀}(r₀)`
from lower semicontinuity + the uniform-in-`p` modulus; then boundary uniqueness). -/
private theorem boundary_subseq_ae {d : ℕ} (hd : 2 ≤ d) (M : LZBoundaryArc d)
    {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (hreg : ∀ v, H.degree v = d) (hm : 1 ≤ H.edgeFinset.card)
    {K : Set ℝ} (hK : K ⊆ M.U) {r₀ : ℝ} (hr₀ : r₀ ∈ K)
    {rn pn : ℕ → ℝ} (hrnK : ∀ n, rn n ∈ K) (hrn : Tendsto rn atTop (𝓝 r₀))
    (hpn_pos : ∀ n, 0 < pn n) (hpn_lt : ∀ n, pn n < M.pc (rn n))
    (hpn_close : Tendsto (fun n => M.pc (rn n) - pn n) atTop (𝓝 0))
    (Wn : ℕ → Graphon) (hWn_feas : ∀ n, Feasible H (rn n) (Wn n))
    (hWn_opt : ∀ n, (Wn n).Ip (pn n) = phiVar H (pn n) (rn n))
    (ns : ℕ → ℕ) (hns : Tendsto ns atTop atTop) :
    ∃ (φ : ℕ → ℕ) (Wlim : Graphon), CutTendsto (fun k => Wn (ns (φ k))) Wlim ∧
      ∀ᵐ z ∂gμ, Wlim.toFun z.1 z.2 = r₀ := by
  obtain ⟨hp₀0, hp₀r, hr₀1, -⟩ := M.ordering r₀ (hK hr₀)
  have hr₀0 : 0 < r₀ := lt_trans hp₀0 hp₀r
  have hp₀1' : M.pc r₀ < 1 := lt_trans hp₀r hr₀1
  set p₀ := M.pc r₀ with hp₀def
  have hp₀1 : p₀ < 1 := hp₀1'
  have hpc_cont : ContinuousAt M.pc r₀ := (M.analytic_pc r₀ (hK hr₀)).continuousAt
  have hqn : Tendsto (fun n => M.pc (rn n)) atTop (𝓝 p₀) := hpc_cont.tendsto.comp hrn
  have hpn : Tendsto pn atTop (𝓝 p₀) := by
    have h := hqn.sub hpn_close
    rw [sub_zero] at h
    exact h.congr (fun n => by ring)
  have hrn_bounds : ∀ n, 0 < M.pc (rn n) ∧ M.pc (rn n) < rn n ∧ rn n < 1 :=
    fun n => by obtain ⟨a, b, c, -⟩ := M.ordering (rn n) (hK (hrnK n)); exact ⟨a, b, c⟩
  have hpn_lt1 : ∀ n, pn n < 1 := fun n =>
    lt_trans (hpn_lt n) (lt_trans (hrn_bounds n).2.1 (hrn_bounds n).2.2)
  have hrn_mem : ∀ n, rn n ∈ Set.Icc (0:ℝ) 1 := fun n =>
    ⟨(lt_trans (hrn_bounds n).1 (hrn_bounds n).2.1).le, (hrn_bounds n).2.2.le⟩
  obtain ⟨φ, Wlim, hφ, hcut⟩ := cut_seqCompact (fun k => Wn (ns k))
  refine ⟨φ, Wlim, hcut, ?_⟩
  have hidx : Tendsto (fun k => ns (φ k)) atTop atTop := hns.comp hφ.tendsto_atTop
  have hfeas_lim : Feasible H r₀ Wlim := by
    have ht_lim : Tendsto (fun k => (Wn (ns (φ k))).tDensity H) atTop (𝓝 (Wlim.tDensity H)) :=
      tDensity_cutContinuous H hcut
    have hrm_lim : Tendsto (fun k => rn (ns (φ k)) ^ H.edgeFinset.card) atTop
        (𝓝 (r₀ ^ H.edgeFinset.card)) := (hrn.comp hidx).pow _
    exact le_of_tendsto_of_tendsto' hrm_lim ht_lim (fun k => hWn_feas (ns (φ k)))
  have hJca : ContinuousAt (fun q : ℝ × ℝ => Jp q.1 q.2) (p₀, r₀) :=
    (Jp_continuousOn_prod).continuousAt
      ((isOpen_Ioo.prod isOpen_Ioo).mem_nhds ⟨⟨hp₀0, hp₀1⟩, ⟨hr₀0, hr₀1⟩⟩)
  have hub_lim : Wlim.Ip p₀ ≤ Jp p₀ r₀ := by
    have hbound_tendsto : Tendsto (fun k => Jp (pn (ns (φ k))) (rn (ns (φ k)))
        + (|Real.log (1 - p₀) - Real.log (1 - pn (ns (φ k)))|
          + |Real.log ((1 - p₀) / p₀) - Real.log ((1 - pn (ns (φ k))) / pn (ns (φ k)))|))
        atTop (𝓝 (Jp p₀ r₀)) := by
      have hjk : Tendsto (fun k => Jp (pn (ns (φ k))) (rn (ns (φ k)))) atTop (𝓝 (Jp p₀ r₀)) :=
        hJca.tendsto.comp ((hpn.comp hidx).prodMk_nhds (hrn.comp hidx))
      have hh1 : Tendsto (fun k => |Real.log (1 - p₀) - Real.log (1 - pn (ns (φ k)))|)
          atTop (𝓝 0) := by
        have hc : Tendsto (fun _ : ℕ => Real.log (1 - p₀)) atTop (𝓝 (Real.log (1 - p₀))) :=
          tendsto_const_nhds
        have hd : Tendsto (fun k => Real.log (1 - p₀) - Real.log (1 - pn (ns (φ k)))) atTop (𝓝 0) := by
          simpa using hc.sub (tendsto_log_one_sub hp₀0 hp₀1 (hpn.comp hidx))
        simpa using hd.abs
      have hh2 : Tendsto (fun k => |Real.log ((1 - p₀) / p₀)
          - Real.log ((1 - pn (ns (φ k))) / pn (ns (φ k)))|) atTop (𝓝 0) := by
        have hc : Tendsto (fun _ : ℕ => Real.log ((1 - p₀) / p₀)) atTop
            (𝓝 (Real.log ((1 - p₀) / p₀))) := tendsto_const_nhds
        have hd : Tendsto (fun k => Real.log ((1 - p₀) / p₀)
            - Real.log ((1 - pn (ns (φ k))) / pn (ns (φ k)))) atTop (𝓝 0) := by
          simpa using hc.sub (tendsto_log_ratio hp₀0 hp₀1 (hpn.comp hidx))
        simpa using hd.abs
      simpa using hjk.add (hh1.add hh2)
    have hIbound : ∀ k, (Wn (ns (φ k))).Ip p₀
        ≤ Jp (pn (ns (φ k))) (rn (ns (φ k)))
          + (|Real.log (1 - p₀) - Real.log (1 - pn (ns (φ k)))|
            + |Real.log ((1 - p₀) / p₀) - Real.log ((1 - pn (ns (φ k))) / pn (ns (φ k)))|) := by
      intro k
      have hpnk0 : 0 < pn (ns (φ k)) := hpn_pos _
      have hpnk1 : pn (ns (φ k)) < 1 := hpn_lt1 _
      have hopt : (Wn (ns (φ k))).Ip (pn (ns (φ k)))
          = phiVar H (pn (ns (φ k))) (rn (ns (φ k))) := hWn_opt _
      have hle_phi := phiVar_le_Jp H hpnk0 hpnk1 (hrn_mem (ns (φ k)))
      have habs := abs_Ip_sub_le (Wn (ns (φ k))) hp₀0 hp₀1 hpnk0 hpnk1
      have hdiff := le_trans (le_abs_self _) habs
      rw [hopt] at hdiff
      linarith
    refine le_of_forall_pos_le_add (fun ε hε => ?_)
    have hev : ∀ᶠ k in atTop, (Wn (ns (φ k))).Ip p₀ ≤ Jp p₀ r₀ + ε := by
      have hlt := hbound_tendsto.eventually
        (eventually_lt_nhds (show Jp p₀ r₀ < Jp p₀ r₀ + ε by linarith))
      filter_upwards [hlt] with k hk
      exact le_of_lt (lt_of_le_of_lt (hIbound k) hk)
    exact Ip_cut_lowerSemicontinuous hp₀0 hp₀1 hcut hev
  have hbu := boundary_uniqueness hd M (hK hr₀) H hreg hm
  have hopt_lim : Jp p₀ r₀ ≤ Wlim.Ip p₀ := hbu.2.1 Wlim hfeas_lim
  have heq : Wlim.Ip p₀ = Jp p₀ r₀ := le_antisymm hub_lim hopt_lim
  exact hbu.2.2 Wlim hfeas_lim heq

/-- **`lem:boundary-convergence` (convergence to the boundary optimizer), edge-density form.**  If
`r_n ∈ K → r₀ ∈ K` and `p_n ∈ (0, pc(r_n))` with `pc(r_n) − p_n → 0`, then the edge densities
of any optimizers `W_n` at `(p_n, r_n)` converge to `r₀`.  (Subsequence criterion on the real
sequence `e(W_n)` + the shared core `boundary_subseq_ae`.) -/
theorem edgeDensity_tendsto_boundary {d : ℕ} (hd : 2 ≤ d) (M : LZBoundaryArc d)
    {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (hreg : ∀ v, H.degree v = d) (hm : 1 ≤ H.edgeFinset.card)
    {K : Set ℝ} (hK : K ⊆ M.U) {r₀ : ℝ} (hr₀ : r₀ ∈ K)
    {rn pn : ℕ → ℝ} (hrnK : ∀ n, rn n ∈ K) (hrn : Tendsto rn atTop (𝓝 r₀))
    (hpn_pos : ∀ n, 0 < pn n) (hpn_lt : ∀ n, pn n < M.pc (rn n))
    (hpn_close : Tendsto (fun n => M.pc (rn n) - pn n) atTop (𝓝 0))
    (Wn : ℕ → Graphon) (hWn_feas : ∀ n, Feasible H (rn n) (Wn n))
    (hWn_opt : ∀ n, (Wn n).Ip (pn n) = phiVar H (pn n) (rn n)) :
    Tendsto (fun n => (Wn n).edgeDensity) atTop (𝓝 r₀) := by
  refine tendsto_of_subseq_tendsto (fun ns hns => ?_)
  obtain ⟨φ, Wlim, hcut, hae⟩ := boundary_subseq_ae hd M H hreg hm hK hr₀ hrnK hrn
    hpn_pos hpn_lt hpn_close Wn hWn_feas hWn_opt ns hns
  refine ⟨φ, ?_⟩
  have hgoal := edgeDensity_cutContinuous hcut
  rw [edgeDensity_ae_const Wlim hae] at hgoal
  exact hgoal

/-- **`lem:boundary-convergence`, cut-distance form.**  Under the same
hypotheses, the optimizers converge *in the cut metric* to the constant graphon `r₀`:
`δ_□(W_n, r₀) → 0`.  This is the paper's headline conclusion; the proof reuses the shared core
and the a.e.-invariance of `cutDist` (`cutDist_congr_right_ae`) to replace the subsequential
limit `W_*` by the constant graphon it equals a.e. -/
theorem cutDist_tendsto_boundary {d : ℕ} (hd : 2 ≤ d) (M : LZBoundaryArc d)
    {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (hreg : ∀ v, H.degree v = d) (hm : 1 ≤ H.edgeFinset.card)
    {K : Set ℝ} (hK : K ⊆ M.U) {r₀ : ℝ} (hr₀ : r₀ ∈ K) (hr₀mem : r₀ ∈ Set.Icc (0:ℝ) 1)
    {rn pn : ℕ → ℝ} (hrnK : ∀ n, rn n ∈ K) (hrn : Tendsto rn atTop (𝓝 r₀))
    (hpn_pos : ∀ n, 0 < pn n) (hpn_lt : ∀ n, pn n < M.pc (rn n))
    (hpn_close : Tendsto (fun n => M.pc (rn n) - pn n) atTop (𝓝 0))
    (Wn : ℕ → Graphon) (hWn_feas : ∀ n, Feasible H (rn n) (Wn n))
    (hWn_opt : ∀ n, (Wn n).Ip (pn n) = phiVar H (pn n) (rn n)) :
    CutTendsto Wn (constGraphon r₀ hr₀mem) := by
  refine tendsto_of_subseq_tendsto (fun ns hns => ?_)
  obtain ⟨φ, Wlim, hcut, hae⟩ := boundary_subseq_ae hd M H hreg hm hK hr₀ hrnK hrn
    hpn_pos hpn_lt hpn_close Wn hWn_feas hWn_opt ns hns
  refine ⟨φ, ?_⟩
  -- replace `W_*` by the constant graphon it equals a.e.
  have hcongr : ∀ W : Graphon, cutDist W Wlim = cutDist W (constGraphon r₀ hr₀mem) := by
    intro W
    refine cutDist_congr_right_ae ?_
    filter_upwards [hae] with z hz
    simp only [hz, constGraphon_apply]
  exact hcut.congr (fun k => hcongr (Wn (ns (φ k))))

/-! ### `lem:active-constraint`: the active constraint. -/

/-- **`lem:active-constraint` (active constraint).**  For `0 < p < r < 1`, every optimizer of the upper-tail
problem saturates the constraint: `t(H,W) = r^m`.

If `t(H,W) > r^m`, sliding `W` toward the constant `p` along `W_θ = (1-θ)p + θW` keeps
feasibility (the homomorphism density moves continuously, hitting `r^m` at some interior
`θ₀` by the intermediate value theorem) while strictly lowering `I_p` (convexity of `J_p`,
`J_p(p)=0`) unless `I_p(W) = 0`, i.e. `W ≡ p` a.e. — which would give `t(H,W) = p^m < r^m`,
a contradiction. -/
theorem active_constraint {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] {p r : ℝ} (hp0 : 0 < p) (hpr : p < r) (hr1 : r < 1)
    (hm : 1 ≤ H.edgeFinset.card)
    (W : Graphon) (hWfeas : Feasible H r W) (hWopt : W.Ip p = phiVar H p r) :
    W.tDensity H = r ^ H.edgeFinset.card := by
  have hr0 : 0 < r := lt_trans hp0 hpr
  have hp1 : p < 1 := lt_trans hpr hr1
  have hp_mem : p ∈ Set.Icc (0:ℝ) 1 := ⟨hp0.le, hp1.le⟩
  have hmne : H.edgeFinset.card ≠ 0 := by omega
  have hpm_lt : p ^ H.edgeFinset.card < r ^ H.edgeFinset.card := pow_lt_pow_left₀ hpr hp0.le hmne
  refine le_antisymm ?_ hWfeas
  by_contra hgt
  push Not at hgt
  -- find an interior `θ₀` with `t(H, W_{θ₀}) = r^m`
  have hg0 : mixTDensity W p H 0 = p ^ H.edgeFinset.card := mixTDensity_zero W p H
  have hg1 : mixTDensity W p H 1 = W.tDensity H := mixTDensity_one W p H
  have hmem : r ^ H.edgeFinset.card ∈ Set.Ioo (mixTDensity W p H 0) (mixTDensity W p H 1) := by
    rw [hg0, hg1]; exact ⟨hpm_lt, hgt⟩
  obtain ⟨θ0, hθ0, hθ0_eq⟩ :=
    intermediate_value_Ioo (zero_le_one) (mixTDensity_continuousOn W p hp_mem H) hmem
  have hθ0_mem : θ0 ∈ Set.Icc (0:ℝ) 1 := ⟨hθ0.1.le, hθ0.2.le⟩
  -- `W_{θ₀}` is feasible (its `H`-density is exactly `r^m`)
  have hfeas_mix : Feasible H r (Wmix W p hp_mem θ0 hθ0_mem) := by
    show r ^ H.edgeFinset.card ≤ (Wmix W p hp_mem θ0 hθ0_mem).tDensity H
    rw [← mixTDensity_eq_tDensity W hp_mem H hθ0_mem]
    exact le_of_eq hθ0_eq.symm
  -- convexity: `I_p(W_{θ₀}) ≤ θ₀ · I_p(W)`
  have hconv : (Wmix W p hp_mem θ0 hθ0_mem).Ip p ≤ θ0 * W.Ip p := by
    have hptwise : ∀ z : ℝ × ℝ, Jp p ((Wmix W p hp_mem θ0 hθ0_mem).toFun z.1 z.2)
        ≤ θ0 * Jp p (W.toFun z.1 z.2) := by
      intro z
      have hcv := (convexOn_Jp hp0 hp1).2 hp_mem (W.mem_Icc z.1 z.2)
        (by linarith [hθ0.2] : (0:ℝ) ≤ 1 - θ0) hθ0.1.le (by ring : (1 - θ0) + θ0 = 1)
      simp only [smul_eq_mul, Jp_self hp0 hp1, mul_zero, zero_add] at hcv
      rw [Wmix_apply]; exact hcv
    have int1 : Integrable
        (fun z : ℝ × ℝ => Jp p ((Wmix W p hp_mem θ0 hθ0_mem).toFun z.1 z.2)) gμ :=
      (Wmix W p hp_mem θ0 hθ0_mem).integrable_comp (measurable_Jp p) (continuousOn_Jp_Icc hp0 hp1)
    have int2 : Integrable (fun z : ℝ × ℝ => θ0 * Jp p (W.toFun z.1 z.2)) gμ :=
      (W.integrable_comp (measurable_Jp p) (continuousOn_Jp_Icc hp0 hp1)).const_mul θ0
    have h1 := integral_mono int1 int2 hptwise
    rwa [integral_const_mul] at h1
  -- optimality: `I_p(W) ≤ I_p(W_{θ₀})`
  have hge : W.Ip p ≤ (Wmix W p hp_mem θ0 hθ0_mem).Ip p := by
    rw [hWopt]
    exact csInf_le (phiVar_bddBelow H hp0 hp1)
      ⟨Wmix W p hp_mem θ0 hθ0_mem, hfeas_mix, rfl⟩
  -- hence `I_p(W) = 0`
  have hIple0 : W.Ip p ≤ 0 := by nlinarith [hge, hconv, hθ0.2, Ip_nonneg W hp0 hp1]
  have hIp0 : W.Ip p = 0 := le_antisymm hIple0 (Ip_nonneg W hp0 hp1)
  -- `I_p(W) = 0 ⟹ W ≡ p` a.e.
  have hJp_zero : ∀ᵐ z ∂gμ, W.toFun z.1 z.2 = p := by
    have hnn_ae : ∀ᵐ z ∂gμ, 0 ≤ Jp p (W.toFun z.1 z.2) := by
      filter_upwards with z
      rcases eq_or_ne (W.toFun z.1 z.2) p with h | h
      · have h0 : Jp p (W.toFun z.1 z.2) = 0 := by rw [h, Jp_self hp0 hp1]
        exact h0.ge
      · exact (Jp_pos_of_ne hp0 hp1 (W.nonneg' z.1 z.2) (W.le_one' z.1 z.2) h).le
    have hint : Integrable (fun z : ℝ × ℝ => Jp p (W.toFun z.1 z.2)) gμ :=
      W.integrable_comp (measurable_Jp p) (continuousOn_Jp_Icc hp0 hp1)
    have hintzero : ∫ z, Jp p (W.toFun z.1 z.2) ∂gμ = 0 := hIp0
    have hae0 := (integral_eq_zero_iff_of_nonneg_ae hnn_ae hint).mp hintzero
    filter_upwards [hae0] with z hz
    exact Jp_eq_zero_imp hp0 hp1 (W.nonneg' z.1 z.2) (W.le_one' z.1 z.2) (by simpa using hz)
  -- contradiction: `t(H,W) = p^m < r^m < t(H,W)`
  have htp : W.tDensity H = p ^ H.edgeFinset.card := tDensity_ae_const W H hJp_zero
  rw [htp] at hgt
  linarith

/-! ### `lem:fixed-density-bipodality`: uniform broken-side localization of the edge density. -/

/-- **`lem:fixed-density-bipodality`, the analytic core.**  On a regular Lubetzky–Zhao boundary arc, over
a compact subarc `K`, for every confinement radius `ρ > 0` there is a window width `η > 0`
such that *uniformly* for `r ∈ K` and `p ∈ (pc(r) − η, pc(r))`, every optimizer has edge
density in `(r − ρ, r)`.

This is the uniform broken-side confinement of Section 4: the upper bound `e(W) < r` is
`lem:edge-density-deficit`, and the lower bound `r − ρ < e(W)` is a compactness/contradiction argument fed by
`lem:boundary-convergence` → r₀`).  It is the step that
reduces the broken-side graphon problem to a one-variable problem in the edge density. -/
theorem uniform_localization {d : ℕ} (hd : 2 ≤ d) (M : LZBoundaryArc d)
    {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (hreg : ∀ v, H.degree v = d) (hm : 1 ≤ H.edgeFinset.card)
    {K : Set ℝ} (hK : K ⊆ M.U) (hKc : IsCompact K) (hKne : K.Nonempty)
    {ρ : ℝ} (hρ0 : 0 < ρ) :
    ∃ η : ℝ, 0 < η ∧ ∀ r ∈ K, ∀ p, M.pc r - η < p → p < M.pc r →
      ∀ W : Graphon, Feasible H r W → W.Ip p = phiVar H p r →
        W.edgeDensity ∈ Set.Ioo (r - ρ) r := by
  -- a uniform positive lower bound `c` for `pc` on the compact `K`
  have hpc_cont : ContinuousOn M.pc K := (M.analytic_pc.continuousOn).mono hK
  obtain ⟨rmin, hrminK, hmin⟩ := hKc.exists_isMinOn hKne hpc_cont
  set c := M.pc rmin with hcdef
  have hc_pos : 0 < c := (M.ordering rmin (hK hrminK)).1
  have hcmin : ∀ r ∈ K, c ≤ M.pc r := isMinOn_iff.mp hmin
  by_contra hcon
  push Not at hcon
  -- a vanishing sequence of admissible window widths `η_n = c/(n+2) ∈ (0, c)`
  set η : ℕ → ℝ := fun n => c / ((n : ℝ) + 2) with hηdef
  have hηpos : ∀ n, 0 < η n := fun n => div_pos hc_pos (by positivity)
  have hηltc : ∀ n, η n < c := fun n => by
    rw [hηdef]; rw [div_lt_iff₀ (by positivity)]; nlinarith [hc_pos]
  have hηlim : Tendsto η atTop (𝓝 0) := by
    have hbase : Tendsto (fun n : ℕ => ((n : ℝ) + 2)) atTop atTop :=
      tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop
    have := hbase.inv_tendsto_atTop.const_mul c
    simpa [hηdef, div_eq_mul_inv] using this
  -- extract the failing data at each `η_n`
  have hex : ∀ n, ∃ r ∈ K, ∃ p, M.pc r - η n < p ∧ p < M.pc r ∧ ∃ W : Graphon,
      Feasible H r W ∧ W.Ip p = phiVar H p r ∧ W.edgeDensity ∉ Set.Ioo (r - ρ) r :=
    fun n => hcon (η n) (hηpos n)
  choose r hrK p hp1 hp2 W hWfeas hWopt hWnotmem using hex
  -- a convergent subsequence `r (φ ·) → r₀ ∈ K`
  obtain ⟨r₀, hr₀K, φ, hφ, hφtend⟩ := hKc.tendsto_subseq hrK
  -- the subsequence satisfies the hypotheses of `lem:boundary-convergence`
  have hpn_pos : ∀ k, 0 < p (φ k) := fun k => by
    have := hp1 (φ k)
    have hcle : c ≤ M.pc (r (φ k)) := hcmin _ (hrK (φ k))
    have := hηltc (φ k)
    linarith
  have hpn_lt : ∀ k, p (φ k) < M.pc (r (φ k)) := fun k => hp2 (φ k)
  have hclose : Tendsto (fun k => M.pc (r (φ k)) - p (φ k)) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (hηlim.comp hφ.tendsto_atTop) (fun k => ?_) (fun k => ?_)
    · linarith [hp2 (φ k)]
    · show M.pc (r (φ k)) - p (φ k) ≤ η (φ k)
      linarith [hp1 (φ k)]
  have hconv := edgeDensity_tendsto_boundary hd M H hreg hm hK hr₀K
    (fun k => hrK (φ k)) hφtend hpn_pos hpn_lt hclose
    (fun k => W (φ k)) (fun k => hWfeas (φ k)) (fun k => hWopt (φ k))
  -- each subsequence optimizer has `e ≤ r - ρ` (upper bound from `lem:edge-density-deficit`)
  have hle : ∀ k, (W (φ k)).edgeDensity ≤ r (φ k) - ρ := by
    intro k
    have hlt_r : (W (φ k)).edgeDensity < r (φ k) :=
      edgeDensity_lt_broken hd M (hK (hrK (φ k))) H hreg hm (hpn_pos k) (hpn_lt k)
        (W (φ k)) (hWfeas (φ k)) (hWopt (φ k))
    by_contra hgt
    push Not at hgt
    exact (hWnotmem (φ k)) ⟨hgt, hlt_r⟩
  -- pass to the limit: `r₀ ≤ r₀ - ρ`, contradicting `ρ > 0`
  have hfinal : r₀ ≤ r₀ - ρ :=
    le_of_tendsto_of_tendsto' hconv (hφtend.sub_const ρ) hle
  linarith

/-! ### The scalar reduction `Φ_H(p,r) = min_ε F_{p,r}(ε)` (`cor:scalar-reduction`). -/

/-- The fixed-density **entropy envelope** `σ_H(ε,τ) = sup { s(W) : e(W)=ε, t(H,W)=τ }`. -/
noncomputable def entropyEnvelope {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (ε τ : ℝ) : ℝ :=
  sSup {s | ∃ W : Graphon, W.edgeDensity = ε ∧ W.tDensity H = τ ∧ W.entropy = s}

/-- The **reduced one-variable objective**
`F_{p,r}(ε) = −2 σ_H(ε, r^m) − log(1−p) + ε·log((1−p)/p)`: the value of `I_p` at the
fixed-`(e, t_H)` entropy maximizer with edge density `ε` and `H`-density `r^m`. -/
noncomputable def reducedObjective {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (p ε τ : ℝ) : ℝ :=
  -2 * entropyEnvelope H ε τ - Real.log (1 - p) + ε * Real.log ((1 - p) / p)

/-- The entropy envelope is bounded above (by `½ log 2`). -/
theorem entropyEnvelope_bddAbove {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (ε τ : ℝ) :
    BddAbove {s | ∃ W : Graphon, W.edgeDensity = ε ∧ W.tDensity H = τ ∧ W.entropy = s} := by
  refine bddAbove_def.mpr ⟨(1 / 2) * Real.log 2, ?_⟩
  rintro s ⟨W, -, -, rfl⟩
  exact entropy_le W

/-- If `Wmax` is a fixed-`(ε,τ)` entropy maximizer then the envelope equals its entropy. -/
theorem entropyEnvelope_eq_of_isMax {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] {ε τ : ℝ} {Wmax : Graphon} (he : Wmax.edgeDensity = ε)
    (ht : Wmax.tDensity H = τ)
    (hmax : ∀ W' : Graphon, W'.edgeDensity = ε → W'.tDensity H = τ → W'.entropy ≤ Wmax.entropy) :
    entropyEnvelope H ε τ = Wmax.entropy := by
  refine IsGreatest.csSup_eq ⟨⟨Wmax, he, ht, rfl⟩, ?_⟩
  rintro s ⟨W', hW'e, hW't, rfl⟩
  exact hmax W' hW'e hW't

/-- At a fixed-`(ε,τ)` entropy maximizer `Wmax`, `F_{p}(ε) = I_p(Wmax)`. -/
theorem reducedObjective_eq_Ip {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] {p ε τ : ℝ} (hp0 : 0 < p) (hp1 : p < 1) {Wmax : Graphon}
    (he : Wmax.edgeDensity = ε) (ht : Wmax.tDensity H = τ)
    (hmax : ∀ W' : Graphon, W'.edgeDensity = ε → W'.tDensity H = τ → W'.entropy ≤ Wmax.entropy) :
    reducedObjective H p ε τ = Wmax.Ip p := by
  unfold reducedObjective
  rw [entropyEnvelope_eq_of_isMax H he ht hmax, Wmax.Ip_eq_entropy hp0 hp1, he]

/-! ### The Kenyon–Radin–Ren–Sadun maximizer family on a uniform strip. -/

/-- **The KRR-S fixed-`(e, t_H)` entropy maximizer family `Ŵ_{ε,r}`, uniform over a compact
subarc.**  This is the "Moreover" clause of the paper's `lem:fixed-density-bipodality`
(`lem:fixed-density-bipodality`) — the localisation `e(W) ∈ (r−ρ, r)` is the lemma's first
clause and is `uniform_localization` — made uniform in `r` exactly as the paper does it: cover
`K` by finitely many KRR-S
neighbourhoods, take `Δ_*` to be the smallest of their surplus thresholds, and take `ρ₀`
small enough that (i) the `ρ₀`-thickening of `K` stays inside the union of the
neighbourhoods, (ii) the strip stays inside `(0,1)` (via the uniform arc margin
`arc_uniform_bounds`), and (iii) `m ρ₀ ≤ Δ_*/2`, so that the mean value bound
`r^m - ε^m ≤ m(r-ε) < m ρ₀ ≤ Δ_*/2` keeps the `H`-density surplus below every `Δ_i`
(the strictness comes from `r - ε < ρ₀`, not from the bound on `ρ₀`).

The maximizer is returned as an honest function `Ŵ : ℝ → ℝ → Graphon` (junk value off the
strip).  That matters downstream: two optimizers with the same edge density are relabellings
of the *same* graphon, which is what makes "unique up to relabelling" usable. -/
theorem krrs_strip {d : ℕ} (hd : 2 ≤ d) (M : LZBoundaryArc d)
    {K : Set ℝ} (hK : K ⊆ M.U) (hKc : IsCompact K) (hKne : K.Nonempty)
    (hKex : ∀ r ∈ K, r ≠ rStar d)
    {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (hreg : ∀ v, H.degree v = d) (hm : 1 ≤ H.edgeFinset.card) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∃ What : ℝ → ℝ → Graphon, ∀ r ∈ K, ∀ ε ∈ Set.Ioo (r - ρ₀) r,
      (What ε r).edgeDensity = ε ∧ (What ε r).tDensity H = r ^ H.edgeFinset.card ∧
      IsBipodal (What ε r) ∧
      (∀ W' : Graphon, W'.edgeDensity = ε → W'.tDensity H = r ^ H.edgeFinset.card →
          W'.entropy ≤ (What ε r).entropy) ∧
      (∀ W' : Graphon, W'.edgeDensity = ε → W'.tDensity H = r ^ H.edgeFinset.card →
          W'.entropy = (What ε r).entropy → ∃ σ : ℝ → ℝ, IsRelabelling σ ∧
            ∀ᵐ z ∂gμ, W'.toFun z.1 z.2 = (What ε r).toFun (σ z.1) (σ z.2)) := by
  classical
  have hmne : H.edgeFinset.card ≠ 0 := by omega
  have hmR : (0:ℝ) < (H.edgeFinset.card : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hmne
  obtain ⟨ηK, hηK0, -, hηK⟩ := arc_uniform_bounds M hK hKc hKne
  -- KRR-S data at every point of `K`
  have hpt : ∀ i : K, ∃ (U : Set ℝ) (Δ : ℝ), IsOpen U ∧ (i : ℝ) ∈ U ∧ 0 < Δ ∧
      ∀ ε ∈ U, ∀ τ : ℝ, 0 < τ - ε ^ (H.edgeFinset.card) →
        τ - ε ^ (H.edgeFinset.card) < Δ →
        ∃ W : Graphon, W.edgeDensity = ε ∧ W.tDensity H = τ ∧ IsBipodal W ∧
          (∀ W' : Graphon, W'.edgeDensity = ε → W'.tDensity H = τ → W'.entropy ≤ W.entropy) ∧
          (∀ W' : Graphon, W'.edgeDensity = ε → W'.tDensity H = τ → W'.entropy = W.entropy →
            ∃ σ : ℝ → ℝ, IsRelabelling σ ∧
              ∀ᵐ z ∂gμ, W'.toFun z.1 z.2 = W.toFun (σ z.1) (σ z.2)) := by
    intro i
    obtain ⟨hpc0, hpcr, hr1, -⟩ := M.ordering (i : ℝ) (hK i.2)
    exact kenyonRadinRenSadun H hd hreg (two_le_card_edgeFinset H hd hreg hm)
      (lt_trans hpc0 hpcr) hr1 (hKex (i : ℝ) i.2)
  choose U Δ hUopen hmemU hΔ0 hKRRS using hpt
  obtain ⟨T, hT⟩ := hKc.elim_finite_subcover (fun i : K => U i) (fun i => hUopen i)
    (fun x hx => Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hmemU ⟨x, hx⟩⟩)
  have hTne : T.Nonempty := by
    obtain ⟨x, hx⟩ := hKne
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hT hx)
    obtain ⟨hiT, -⟩ := Set.mem_iUnion.mp hi
    exact ⟨i, hiT⟩
  set Δstar : ℝ := T.inf' hTne (fun i => Δ i) with hΔstar_def
  have hΔstar0 : 0 < Δstar := by
    rw [hΔstar_def, Finset.lt_inf'_iff]
    exact fun i _ => hΔ0 i
  have hUstar_open : IsOpen (⋃ i ∈ T, U i) := isOpen_biUnion (fun i _ => hUopen i)
  obtain ⟨ρth, hρth0, hρth⟩ := hKc.exists_thickening_subset_open hUstar_open hT
  set ρ₀ : ℝ := min (min ρth (ηK / 2)) (Δstar / (2 * (H.edgeFinset.card : ℝ))) with hρ₀_def
  have hρ₀0 : 0 < ρ₀ := by
    rw [hρ₀_def]
    exact lt_min (lt_min hρth0 (by linarith)) (by positivity)
  have hρth' : ρ₀ ≤ ρth := le_trans (min_le_left _ _) (min_le_left _ _)
  have hρηK : ρ₀ ≤ ηK / 2 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hρΔ : ρ₀ ≤ Δstar / (2 * (H.edgeFinset.card : ℝ)) := min_le_right _ _
  -- the KRR-S maximizer at every `(ε, r)` of the uniform strip
  have hmain : ∀ r ∈ K, ∀ ε ∈ Set.Ioo (r - ρ₀) r, ∃ W : Graphon,
      W.edgeDensity = ε ∧ W.tDensity H = r ^ H.edgeFinset.card ∧ IsBipodal W ∧
      (∀ W' : Graphon, W'.edgeDensity = ε → W'.tDensity H = r ^ H.edgeFinset.card →
          W'.entropy ≤ W.entropy) ∧
      (∀ W' : Graphon, W'.edgeDensity = ε → W'.tDensity H = r ^ H.edgeFinset.card →
          W'.entropy = W.entropy → ∃ σ : ℝ → ℝ, IsRelabelling σ ∧
            ∀ᵐ z ∂gμ, W'.toFun z.1 z.2 = W.toFun (σ z.1) (σ z.2)) := by
    intro r hr ε hε
    obtain ⟨hηKr, hr1', -⟩ := hηK r hr
    have hε0 : 0 < ε := by linarith [hε.1]
    have hεr : ε < r := hε.2
    have hr_mem : r ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith, by linarith⟩
    have hε_mem : ε ∈ Set.Icc (0:ℝ) 1 := ⟨hε0.le, by linarith⟩
    -- `ε` lies in one of the finitely many KRR-S neighbourhoods
    have hεth : ε ∈ Metric.thickening ρth K := by
      rw [Metric.mem_thickening_iff]
      refine ⟨r, hr, ?_⟩
      rw [Real.dist_eq, abs_of_nonpos (by linarith : ε - r ≤ 0)]
      linarith [hε.1]
    obtain ⟨i, hiT, hεU⟩ := Set.mem_iUnion₂.mp (hρth hεth)
    have hpos : 0 < r ^ H.edgeFinset.card - ε ^ H.edgeFinset.card := by
      have := pow_lt_pow_left₀ hεr hε0.le hmne; linarith
    have hlt : r ^ H.edgeFinset.card - ε ^ H.edgeFinset.card < Δ i := by
      have hgap : r ^ H.edgeFinset.card - ε ^ H.edgeFinset.card
          ≤ (H.edgeFinset.card : ℝ) * (r - ε) := by
        have habs := abs_pow_sub_pow_le hr_mem hε_mem H.edgeFinset.card
        rwa [abs_of_pos hpos, abs_of_nonneg (by linarith : (0:ℝ) ≤ r - ε)] at habs
      have hre : r - ε < Δstar / (2 * (H.edgeFinset.card : ℝ)) := by linarith [hε.1]
      have hmul : (H.edgeFinset.card : ℝ) * (r - ε) < Δstar / 2 := by
        have h := mul_lt_mul_of_pos_left hre hmR
        rwa [show (H.edgeFinset.card : ℝ) * (Δstar / (2 * (H.edgeFinset.card : ℝ)))
            = Δstar / 2 from by field_simp] at h
      have hΔle : Δstar ≤ Δ i := Finset.inf'_le _ hiT
      linarith
    exact hKRRS i ε hεU (r ^ H.edgeFinset.card) hpos hlt
  -- turn the family into a function (junk value off the strip)
  have hchoice : ∀ e s : ℝ, ∃ W : Graphon, s ∈ K → e ∈ Set.Ioo (s - ρ₀) s →
      (W.edgeDensity = e ∧ W.tDensity H = s ^ H.edgeFinset.card ∧ IsBipodal W ∧
        (∀ W' : Graphon, W'.edgeDensity = e → W'.tDensity H = s ^ H.edgeFinset.card →
            W'.entropy ≤ W.entropy) ∧
        (∀ W' : Graphon, W'.edgeDensity = e → W'.tDensity H = s ^ H.edgeFinset.card →
            W'.entropy = W.entropy → ∃ σ : ℝ → ℝ, IsRelabelling σ ∧
              ∀ᵐ z ∂gμ, W'.toFun z.1 z.2 = W.toFun (σ z.1) (σ z.2))) := by
    intro e s
    by_cases hs : s ∈ K
    · by_cases he : e ∈ Set.Ioo (s - ρ₀) s
      · obtain ⟨W, hW⟩ := hmain s hs e he
        exact ⟨W, fun _ _ => hW⟩
      · exact ⟨constGraphon 0 ⟨le_rfl, zero_le_one⟩, fun _ h => absurd h he⟩
    · exact ⟨constGraphon 0 ⟨le_rfl, zero_le_one⟩, fun h _ => absurd h hs⟩
  choose What hWhat using hchoice
  exact ⟨ρ₀, hρ₀0, What, fun r hr ε hε => hWhat ε r hr hε⟩

/-- **Shared engine for the reduction, uniform over a compact subarc `K` and over the
confinement radius.**  Mirrors the paper's `lem:fixed-density-bipodality` and
`cor:scalar-reduction` in their actual quantifier order: one `ρ₀`, then *any*
`0 < ρ ≤ ρ₀`, then one window width `η = η(ρ)` valid for **every** `r ∈ K`, and — as the paper
also stipulates — small enough that `η ≤ pc(r)` on `K`, so every `p` in the window is a genuine
probability.

The first clause exports the KRR-S maximizer family `Ŵ_{ε,r}` together with the identity
`𝓕_{p,r}(ε) = I_p(Ŵ_{ε,r})` (eq. `reduced-objective-equality`), which is the *converse* half
of the corollary: every scalar competitor is realised by an admissible graphon.  The last
clause is the forward half: every optimizer is confined to the strip, realises the reduced
objective at its own edge density, is bipodal, and is a relabelling of the *same* maximizer
`Ŵ_{e(W),r}` — which is itself an optimizer. -/
theorem reduction_core_uniform {d : ℕ} (hd : 2 ≤ d) (M : LZBoundaryArc d)
    {K : Set ℝ} (hK : K ⊆ M.U) (hKc : IsCompact K) (hKne : K.Nonempty)
    (hKex : ∀ r ∈ K, r ≠ rStar d)
    {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (hreg : ∀ v, H.degree v = d) (hm : 1 ≤ H.edgeFinset.card) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∃ What : ℝ → ℝ → Graphon,
      (∀ r ∈ K, ∀ ε ∈ Set.Ioo (r - ρ₀) r,
        (What ε r).edgeDensity = ε ∧ Feasible H r (What ε r) ∧ IsBipodal (What ε r) ∧
        (What ε r).tDensity H = r ^ H.edgeFinset.card ∧
        ∀ p : ℝ, 0 < p → p < 1 →
          reducedObjective H p ε (r ^ H.edgeFinset.card) = (What ε r).Ip p) ∧
      (∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ η : ℝ, 0 < η ∧ (∀ r ∈ K, η ≤ M.pc r) ∧
        ∀ r ∈ K, ∀ p, M.pc r - η < p → p < M.pc r →
          (∀ ε ∈ Set.Ioo (r - ρ) r,
            phiVar H p r ≤ reducedObjective H p ε (r ^ H.edgeFinset.card)) ∧
          (∃ W0 : Graphon, Feasible H r W0 ∧ W0.Ip p = phiVar H p r) ∧
          (∀ Wopt : Graphon, Feasible H r Wopt → Wopt.Ip p = phiVar H p r →
            Wopt.edgeDensity ∈ Set.Ioo (r - ρ) r ∧
            phiVar H p r = reducedObjective H p Wopt.edgeDensity (r ^ H.edgeFinset.card) ∧
            IsBipodal Wopt ∧
            (What Wopt.edgeDensity r).Ip p = phiVar H p r ∧
            ∃ σ : ℝ → ℝ, IsRelabelling σ ∧
              ∀ᵐ z ∂gμ, Wopt.toFun z.1 z.2
                = (What Wopt.edgeDensity r).toFun (σ z.1) (σ z.2))) := by
  classical
  obtain ⟨ρ₀, hρ₀0, What, hWhat⟩ := krrs_strip hd M hK hKc hKne hKex H hreg hm
  obtain ⟨ηK, hηK0, -, hηK⟩ := arc_uniform_bounds M hK hKc hKne
  refine ⟨ρ₀, hρ₀0, What, ?_, ?_⟩
  · -- the maximizer family and the identity `F(ε) = I_p(Ŵ_{ε,r})`
    intro r hr ε hε
    obtain ⟨he, ht, hbip, hmax, -⟩ := hWhat r hr ε hε
    exact ⟨he, le_of_eq ht.symm, hbip, ht,
      fun p hp0 hp1 => reducedObjective_eq_Ip H hp0 hp1 he ht hmax⟩
  · -- the localization window, uniform over `K`
    intro ρ hρ0 hρub
    obtain ⟨ηloc, hηloc0, hloc⟩ := uniform_localization hd M H hreg hm hK hKc hKne hρ0
    refine ⟨min ηloc (ηK / 2), lt_min hηloc0 (by linarith), ?_, ?_⟩
    · -- `η ≤ pc(r)` uniformly: the window keeps `p` a genuine probability
      intro r hr
      obtain ⟨-, -, -, -, hηKpc, -⟩ := hηK r hr
      have := min_le_right ηloc (ηK / 2)
      linarith
    intro r hr p hp_lo hp_hi
    obtain ⟨hpc0, hpcr, hr1, -⟩ := M.ordering r (hK hr)
    obtain ⟨-, -, -, -, hηKpc, -⟩ := hηK r hr
    have hp0 : 0 < p := by
      have h1 : min ηloc (ηK / 2) ≤ ηK / 2 := min_le_right _ _
      linarith
    have hp1 : p < 1 := lt_trans hp_hi (lt_trans hpcr hr1)
    have hpr : p < r := lt_trans hp_hi hpcr
    have hloc_lo : M.pc r - ηloc < p := by
      have := min_le_left ηloc (ηK / 2); linarith
    have hsub : Set.Ioo (r - ρ) r ⊆ Set.Ioo (r - ρ₀) r :=
      Set.Ioo_subset_Ioo (by linarith) le_rfl
    -- `Φ ≤ F(ε)` on the whole strip (the maximizer is feasible)
    have hPhi_le_F : ∀ ε ∈ Set.Ioo (r - ρ) r,
        phiVar H p r ≤ reducedObjective H p ε (r ^ H.edgeFinset.card) := by
      intro ε hε
      obtain ⟨he, ht, -, hmax, -⟩ := hWhat r hr ε (hsub hε)
      rw [reducedObjective_eq_Ip H hp0 hp1 he ht hmax]
      exact csInf_le (phiVar_bddBelow H hp0 hp1) ⟨What ε r, le_of_eq ht.symm, rfl⟩
    refine ⟨hPhi_le_F, feasible_attains H hp0 hp1 (lt_trans hpc0 hpcr) hr1, ?_⟩
    intro Wopt hWoptfeas hWoptopt
    -- localize and saturate the constraint for the arbitrary optimizer `Wopt`
    have hWoptmem : Wopt.edgeDensity ∈ Set.Ioo (r - ρ) r :=
      hloc r hr p hloc_lo hp_hi Wopt hWoptfeas hWoptopt
    have hWoptactive : Wopt.tDensity H = r ^ H.edgeFinset.card :=
      active_constraint H hp0 hpr hr1 hm Wopt hWoptfeas hWoptopt
    -- the bipodal maximizer at `e(Wopt)`; it is itself an optimizer (entropy identity)
    obtain ⟨hWmaxe, hWmaxt, hbip, hWmaxmax, hWmaxuniq⟩ :=
      hWhat r hr Wopt.edgeDensity (hsub hWoptmem)
    have hfeas_max : Feasible H r (What Wopt.edgeDensity r) := le_of_eq hWmaxt.symm
    have hs_le : Wopt.entropy ≤ (What Wopt.edgeDensity r).entropy :=
      hWmaxmax Wopt rfl hWoptactive
    have hIp_le : (What Wopt.edgeDensity r).Ip p ≤ Wopt.Ip p := by
      have h1 := Wopt.Ip_eq_entropy hp0 hp1
      have h2 := (What Wopt.edgeDensity r).Ip_eq_entropy hp0 hp1
      rw [hWmaxe] at h2
      rw [h1, h2]; linarith [hs_le]
    have hWmax_opt : (What Wopt.edgeDensity r).Ip p = phiVar H p r :=
      le_antisymm (by rw [← hWoptopt]; exact hIp_le)
        (csInf_le (phiVar_bddBelow H hp0 hp1) ⟨What Wopt.edgeDensity r, hfeas_max, rfl⟩)
    -- equal `I_p` and equal edge density force equal entropy, so `Wopt` is also a maximizer
    have hs_eq : Wopt.entropy = (What Wopt.edgeDensity r).entropy := by
      have h1 := Wopt.Ip_eq_entropy hp0 hp1
      have h2 := (What Wopt.edgeDensity r).Ip_eq_entropy hp0 hp1
      rw [hWmaxe] at h2
      have hIpeq : Wopt.Ip p = (What Wopt.edgeDensity r).Ip p := by rw [hWoptopt, hWmax_opt]
      rw [hIpeq] at h1
      linarith
    -- uniqueness up to relabelling ⇒ `Wopt = Ŵ ∘ (σ × σ)` a.e., hence `Wopt` is bipodal
    obtain ⟨σ, hσ, hrelabel⟩ := hWmaxuniq Wopt rfl hWoptactive hs_eq
    have hbipopt : IsBipodal Wopt := isBipodal_of_relabel hσ hbip hrelabel
    have hphiF : phiVar H p r
        = reducedObjective H p Wopt.edgeDensity (r ^ H.edgeFinset.card) := by
      rw [reducedObjective_eq_Ip H hp0 hp1 hWmaxe hWmaxt hWmaxmax]; exact hWmax_opt.symm
    exact ⟨hWoptmem, hphiF, hbipopt, hWmax_opt, σ, hσ, hrelabel⟩

/-- **Shared engine for the reduction, at a single density `r`.**  The `K = {r}` instance of
`reduction_core_uniform`: for each broken-side `p` it returns the lower bound `Φ ≤ F(ε)` on
the strip; an attained optimizer; and, for *every* optimizer `Wopt`, that its edge density
realizes `Φ = F(e(Wopt))`, that `Wopt` is **bipodal**, and that `Wopt` equals the KRRS bipodal
maximizer at `(e(Wopt), r^m)` up to a measure-preserving relabelling. -/
private theorem reduction_core {d : ℕ} (hd : 2 ≤ d) (M : LZBoundaryArc d) {r : ℝ} (hr : r ∈ M.U)
    (hrexc : r ≠ rStar d) {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (hreg : ∀ v, H.degree v = d) (hm : 1 ≤ H.edgeFinset.card) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ η : ℝ, 0 < η ∧ ∀ p, M.pc r - η < p → p < M.pc r →
      (∀ ε ∈ Set.Ioo (r - ρ) r, phiVar H p r ≤ reducedObjective H p ε (r ^ H.edgeFinset.card)) ∧
      (∃ W0 : Graphon, Feasible H r W0 ∧ W0.Ip p = phiVar H p r) ∧
      (∀ Wopt : Graphon, Feasible H r Wopt → Wopt.Ip p = phiVar H p r →
        Wopt.edgeDensity ∈ Set.Ioo (r - ρ) r ∧
        phiVar H p r = reducedObjective H p Wopt.edgeDensity (r ^ H.edgeFinset.card) ∧
        IsBipodal Wopt ∧
        ∃ Wmax : Graphon, IsBipodal Wmax ∧ Feasible H r Wmax ∧ Wmax.Ip p = phiVar H p r ∧
          Wmax.edgeDensity = Wopt.edgeDensity ∧
          ∃ σ : ℝ → ℝ, IsRelabelling σ ∧
            ∀ᵐ z ∂gμ, Wopt.toFun z.1 z.2 = Wmax.toFun (σ z.1) (σ z.2)) := by
  obtain ⟨ρ₀, hρ₀0, What, hfam, hcore⟩ :=
    reduction_core_uniform hd M (Set.singleton_subset_iff.mpr hr) isCompact_singleton ⟨r, rfl⟩
      (fun s hs => (Set.mem_singleton_iff.mp hs) ▸ hrexc) H hreg hm
  obtain ⟨η, hη0, -, hcore'⟩ := hcore ρ₀ hρ₀0 le_rfl
  refine ⟨ρ₀, hρ₀0, η, hη0, fun p hlo hhi => ?_⟩
  obtain ⟨hF_lb, hattain, huniv⟩ := hcore' r rfl p hlo hhi
  refine ⟨hF_lb, hattain, fun Wopt hWfeas hWopt => ?_⟩
  obtain ⟨hmem, hphiF, hbip, hmaxopt, σ, hσ, hrel⟩ := huniv Wopt hWfeas hWopt
  obtain ⟨hWmaxe, hWmaxfeas, hWmaxbip, -, -⟩ := hfam r rfl Wopt.edgeDensity hmem
  exact ⟨hmem, hphiF, hbip, What Wopt.edgeDensity r, hWmaxbip, hWmaxfeas, hmaxopt, hWmaxe,
    σ, hσ, hrel⟩

/-- **`cor:scalar-reduction` (the scalar reduction).**  At a non-exceptional `r` on a regular Lubetzky–Zhao boundary arc,
there are a confinement radius `ρ > 0` and a window width `η > 0` such that for every
broken-side `p ∈ (pc(r) − η, pc(r))` the upper-tail value equals the minimum of the reduced
one-variable objective over `(r − ρ, r)`: there is a minimizing edge density `ε*` with
`Φ_H(p,r) = F_{p,r}(ε*)` and `F_{p,r}(ε*) ≤ F_{p,r}(ε)` for all `ε ∈ (r − ρ, r)`. -/
theorem scalar_reduction {d : ℕ} (hd : 2 ≤ d) (M : LZBoundaryArc d) {r : ℝ} (hr : r ∈ M.U)
    (hrexc : r ≠ rStar d) {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (hreg : ∀ v, H.degree v = d) (hm : 1 ≤ H.edgeFinset.card) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ η : ℝ, 0 < η ∧ ∀ p, M.pc r - η < p → p < M.pc r →
      ∃ ε ∈ Set.Ioo (r - ρ) r,
        phiVar H p r = reducedObjective H p ε (r ^ H.edgeFinset.card) ∧
        ∀ ε' ∈ Set.Ioo (r - ρ) r,
          reducedObjective H p ε (r ^ H.edgeFinset.card)
            ≤ reducedObjective H p ε' (r ^ H.edgeFinset.card) := by
  obtain ⟨ρ, hρ0, η, hη0, hcore⟩ := reduction_core hd M hr hrexc H hreg hm
  refine ⟨ρ, hρ0, η, hη0, fun p hlo hhi => ?_⟩
  obtain ⟨hF_lb, ⟨W0, hW0feas, hW0opt⟩, huniv⟩ := hcore p hlo hhi
  obtain ⟨hmem, hphiF, -⟩ := huniv W0 hW0feas hW0opt
  exact ⟨W0.edgeDensity, hmem, hphiF, fun ε' hε' => by rw [← hphiF]; exact hF_lb ε' hε'⟩

/-! ### Structure of the broken-side optimizers (`lem:fixed-density-bipodality` and `cor:scalar-reduction`). -/

/-- **Every broken-side optimizer is bipodal and is the entropy maximizer up to relabelling.**
At a non-exceptional `r`, for every broken-side `p ∈ (pc(r) − η, pc(r))`, every minimizer
`Wopt` of the upper-tail problem is **bipodal**, and equals — up to a measure-preserving
relabelling `σ` of `[0,1]` — the (also optimal) KRRS bipodal entropy maximizer `Wmax` at its own
edge density `(e(Wopt), r^m)`.  This is the full structural conclusion of the paper's `lem:fixed-density-bipodality`
together with the "Furthermore" clause of `cor:scalar-reduction`, available because `kenyonRadinRenSadun` now carries uniqueness up to relabelling
(arXiv:1509.05370, `thm:lz-criterion-informal`). -/
theorem optimizer_bipodal {d : ℕ} (hd : 2 ≤ d) (M : LZBoundaryArc d) {r : ℝ} (hr : r ∈ M.U)
    (hrexc : r ≠ rStar d) {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (hreg : ∀ v, H.degree v = d) (hm : 1 ≤ H.edgeFinset.card) :
    ∃ η : ℝ, 0 < η ∧ ∀ p, M.pc r - η < p → p < M.pc r →
      ∀ Wopt : Graphon, Feasible H r Wopt → Wopt.Ip p = phiVar H p r →
        IsBipodal Wopt ∧
        ∃ Wmax : Graphon, IsBipodal Wmax ∧ Feasible H r Wmax ∧ Wmax.Ip p = phiVar H p r ∧
          Wmax.edgeDensity = Wopt.edgeDensity ∧
          ∃ σ : ℝ → ℝ, IsRelabelling σ ∧
            ∀ᵐ z ∂gμ, Wopt.toFun z.1 z.2 = Wmax.toFun (σ z.1) (σ z.2) := by
  obtain ⟨_, _, η, hη0, hcore⟩ := reduction_core hd M hr hrexc H hreg hm
  refine ⟨η, hη0, fun p hlo hhi Wopt hWfeas hWopt => ?_⟩
  obtain ⟨-, -, huniv⟩ := hcore p hlo hhi
  obtain ⟨-, -, hbip, Wmax, hbipmax, hfeasmax, hmaxopt, hmaxe, σ, hσ, hrel⟩ := huniv Wopt hWfeas hWopt
  exact ⟨hbip, Wmax, hbipmax, hfeasmax, hmaxopt, hmaxe, σ, hσ, hrel⟩

/-- **Existence of a bipodal optimizer** (from `reduction_core`, whose universal clause
supplies bipodality of the attained optimizer): on the broken-side window the
upper-tail problem admits a bipodal minimizer.  The bipodality half of `thm:nonexceptional-optimizers`
(`thm:nonexceptional-optimizers`) / `thm:local-optimizer-structure`(b). -/
theorem exists_bipodal_optimizer {d : ℕ} (hd : 2 ≤ d) (M : LZBoundaryArc d) {r : ℝ} (hr : r ∈ M.U)
    (hrexc : r ≠ rStar d) {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (hreg : ∀ v, H.degree v = d) (hm : 1 ≤ H.edgeFinset.card) :
    ∃ η : ℝ, 0 < η ∧ ∀ p, M.pc r - η < p → p < M.pc r →
      ∃ W : Graphon, Feasible H r W ∧ W.Ip p = phiVar H p r ∧ IsBipodal W := by
  obtain ⟨_, _, η, hη0, hcore⟩ := reduction_core hd M hr hrexc H hreg hm
  refine ⟨η, hη0, fun p hlo hhi => ?_⟩
  obtain ⟨-, ⟨W0, hW0feas, hW0opt⟩, huniv⟩ := hcore p hlo hhi
  obtain ⟨-, -, hbip, -⟩ := huniv W0 hW0feas hW0opt
  exact ⟨W0, hW0feas, hW0opt, hbip⟩

end UpperTailOptimizers
