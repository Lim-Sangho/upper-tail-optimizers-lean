import UpperTailOptimizers.NonexceptionalEndpoint.LocalReduction.Main

/-!
# Section 4.1 in the paper's coordinates

`NonexceptionalEndpoint/LocalReduction/Main.lean` proves the results of `sec:local-reduction` on a Lubetzky–Zhao
boundary arc `M`, with the boundary curve `M.pc` and compact subsets `K` of the arc window.
This file states them as the paper does: with the global boundary curve `pcGlobal`, for
nonexceptional densities `r ∈ (0,1) ∖ {r_*}`, and with an open interval `I ∋ r₀`.

* `edge_density_deficit` — `lem:edge-density-deficit`;
* `boundary_convergence` — `lem:boundary-convergence`;
* `one_dimensional_reduction` — `cor:scalar-reduction`, for any `I`, `ρ₀`, `ρ` and `η` satisfying
  the clauses of `lem:fixed-density-bipodality`;
* `uniform_scalar_reduction` — `lem:fixed-density-bipodality` together with
  `cor:scalar-reduction` for the `I`, `ρ₀` and `η` it constructs;
* `fixed_density_bipodality` — `lem:fixed-density-bipodality` alone;
* `fixed_density_bipodality_Icc` — the same, with `I = (lo, hi)` of compact closure
  `[lo, hi] ⊆ (0,1) ∖ {r_*}`, as the paper's proof chooses it and Section 4.2 uses it.

In `uniform_scalar_reduction`, the interval is `I = (lo, hi)`, a scalar minimizer of `I_{p,r}`
over `(r-ρ, r)` is expressed with `IsMinOn`, and "the entropy maximizer `B_{ε,r^m}`" is any
graphon with edge density `ε`, `H`-density `r^m` and maximal entropy under these constraints;
the lemma's clause shows that it exists and is unique up to relabelling.

The proofs pick one arc `M ∋ r₀` (`lz_boundary_arcs`), a window
`K = [r₀ - w, r₀ + w] ⊆ M.U` avoiding `r_*` (`exists_Icc_window`), and use
`pcGlobal = M.pc` on `K` (`pcGlobal_eq_pc`).  For `boundary_convergence` a tail of `r_n` lies in
`K`; for `uniform_scalar_reduction`, `I = (r₀ - w/2, r₀ + w/2)` and the arc results `krrs_strip`
and `uniform_localization` on `K` do the work.  Uniqueness of `B_{ε,r^m}` is only up to
relabelling, so the corollary composes and inverts relabellings (`ae_relabel_trans`,
`exists_relabel_symm`).
-/

namespace UpperTailOptimizers

open MeasureTheory Filter Topology

/-! ### Helpers: a window around `r₀` inside one arc, and relabelling bookkeeping. -/

/-- **A closed window around a nonexceptional arc point.**  If `r₀ ∈ M.U` and `r₀ ≠ r_*`, then
some interval `[r₀ - w, r₀ + w]` with `w > 0` lies in the arc window `M.U` and avoids `r_*`. -/
theorem exists_Icc_window {d : ℕ} (M : LZBoundaryArc d) {r₀ : ℝ} (hr₀ : r₀ ∈ M.U)
    (hexc : r₀ ≠ rStar d) :
    ∃ w : ℝ, 0 < w ∧ Set.Icc (r₀ - w) (r₀ + w) ⊆ M.U ∧
      ∀ r ∈ Set.Icc (r₀ - w) (r₀ + w), r ≠ rStar d := by
  obtain ⟨δ, hδ0, hball⟩ := Metric.isOpen_iff.mp M.isOpen_U r₀ hr₀
  have hgap : 0 < |r₀ - rStar d| := abs_pos.mpr (sub_ne_zero.mpr hexc)
  have hwδ := min_le_left (δ / 2) (|r₀ - rStar d| / 2)
  have hwgap := min_le_right (δ / 2) (|r₀ - rStar d| / 2)
  refine ⟨min (δ / 2) (|r₀ - rStar d| / 2), lt_min (by linarith) (by linarith), ?_, ?_⟩
  · intro r hr
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hr.1, hr.2]
  · intro r hr hrs
    rw [hrs] at hr
    have habs : |r₀ - rStar d| ≤ min (δ / 2) (|r₀ - rStar d| / 2) :=
      abs_sub_le_iff.mpr ⟨by linarith [hr.1], by linarith [hr.2]⟩
    linarith

/-- **Relabellings compose almost everywhere.**  If `W₁ = W₂ ∘ (σ × σ)` and `W₂ = W₃ ∘ (τ × τ)`
almost everywhere, with `σ` measure preserving, then `W₁ = W₃ ∘ ((τ ∘ σ) × (τ ∘ σ))` almost
everywhere. -/
theorem ae_relabel_trans {W₁ W₂ W₃ : Graphon} {σ τ : ℝ → ℝ}
    (hσ : MeasurePreserving σ unitμ unitμ)
    (h₁ : ∀ᵐ z ∂gμ, W₁.toFun z.1 z.2 = W₂.toFun (σ z.1) (σ z.2))
    (h₂ : ∀ᵐ z ∂gμ, W₂.toFun z.1 z.2 = W₃.toFun (τ z.1) (τ z.2)) :
    ∀ᵐ z ∂gμ, W₁.toFun z.1 z.2 = W₃.toFun (τ (σ z.1)) (τ (σ z.2)) := by
  have hmp : MeasurePreserving (Prod.map σ σ) gμ gμ := hσ.prod hσ
  have hpull : ∀ᵐ z ∂gμ, W₂.toFun (σ z.1) (σ z.2) = W₃.toFun (τ (σ z.1)) (τ (σ z.2)) :=
    hmp.quasiMeasurePreserving.ae
      (p := fun z : ℝ × ℝ => W₂.toFun z.1 z.2 = W₃.toFun (τ z.1) (τ z.2)) h₂
  filter_upwards [h₁, hpull] with z hz hpz
  rw [hz, hpz]

/-- **Relabelling is symmetric.**  If `W = W' ∘ (σ × σ)` almost everywhere for a relabelling `σ`,
then `W' = W ∘ (τ × τ)` almost everywhere for a relabelling `τ` (the a.e. inverse of `σ`). -/
theorem exists_relabel_symm {W W' : Graphon} {σ : ℝ → ℝ} (hσ : IsRelabelling σ)
    (h : ∀ᵐ z ∂gμ, W.toFun z.1 z.2 = W'.toFun (σ z.1) (σ z.2)) :
    ∃ τ : ℝ → ℝ, IsRelabelling τ ∧
      ∀ᵐ z ∂gμ, W'.toFun z.1 z.2 = W.toFun (τ z.1) (τ z.2) := by
  obtain ⟨τ, hτ, -, hστ⟩ := hσ.exists_symm
  refine ⟨τ, hτ, ?_⟩
  have hmp : MeasurePreserving (Prod.map τ τ) gμ gμ :=
    hτ.measurePreserving.prod hτ.measurePreserving
  have hpull : ∀ᵐ z ∂gμ, W.toFun (τ z.1) (τ z.2) = W'.toFun (σ (τ z.1)) (σ (τ z.2)) :=
    hmp.quasiMeasurePreserving.ae
      (p := fun z : ℝ × ℝ => W.toFun z.1 z.2 = W'.toFun (σ z.1) (σ z.2)) h
  have h1 : ∀ᵐ z ∂gμ, σ (τ z.1) = z.1 := Measure.quasiMeasurePreserving_fst.ae hστ
  have h2 : ∀ᵐ z ∂gμ, σ (τ z.2) = z.2 := Measure.quasiMeasurePreserving_snd.ae hστ
  filter_upwards [hpull, h1, h2] with z hz hz1 hz2
  rw [hz, hz1, hz2]

/-! ### The results of Section 4.1 -/

/-- **`lem:edge-density-deficit` (strict edge-density deficit).**  Let `r ∈ (0,1) ∖ {r_*}` and
`0 < p < pc(r)`.  Every optimizer `W` satisfies `e(W) < r`. -/
theorem edge_density_deficit {d : ℕ} (hd : 2 ≤ d) {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (hreg : ∀ v, H.degree v = d)
    (hm : 1 ≤ H.edgeFinset.card) {r p : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (hr : r ≠ rStar d)
    (hp0 : 0 < p) (hp : p < pcGlobal d r)
    (W : Graphon) (hWfeas : Feasible H r W) (hWopt : W.Ip p = phiVar H p r) :
    W.edgeDensity < r := by
  obtain ⟨M, hrM, -⟩ := lz_boundary_arcs hd hr0 hr1 hr
  rw [pcGlobal_eq_pc hd M hrM] at hp
  exact edgeDensity_lt_broken hd M hrM H hreg hm hp0 hp W hWfeas hWopt

/-- **`lem:boundary-convergence` (boundary convergence of optimizers).**  Let
`r_n ∈ (0,1) ∖ {r_*}` and `p_n ∈ (0, pc(r_n))` with `r_n → r₀ ∈ (0,1) ∖ {r_*}` and
`pc(r_n) - p_n → 0`, and let `W_n` be an optimizer at `(p_n, r_n)`.  Then
`δ_□(W_n, r₀) → 0` and `e(W_n) → r₀`. -/
theorem boundary_convergence {d : ℕ} (hd : 2 ≤ d) {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (hreg : ∀ v, H.degree v = d)
    (hm : 1 ≤ H.edgeFinset.card)
    {rn pn : ℕ → ℝ} (_hrn : ∀ n, 0 < rn n ∧ rn n < 1 ∧ rn n ≠ rStar d)
    (hpn : ∀ n, 0 < pn n ∧ pn n < pcGlobal d (rn n))
    {r₀ : ℝ} (hr₀0 : 0 < r₀) (hr₀1 : r₀ < 1) (hr₀ : r₀ ≠ rStar d)
    (hrlim : Tendsto rn atTop (𝓝 r₀))
    (hpclim : Tendsto (fun n => pcGlobal d (rn n) - pn n) atTop (𝓝 0))
    (Wn : ℕ → Graphon) (hWfeas : ∀ n, Feasible H (rn n) (Wn n))
    (hWopt : ∀ n, (Wn n).Ip (pn n) = phiVar H (pn n) (rn n)) :
    CutTendsto Wn (constGraphon r₀ ⟨hr₀0.le, hr₀1.le⟩) ∧
      Tendsto (fun n => (Wn n).edgeDensity) atTop (𝓝 r₀) := by
  -- the hypothesis `_hrn` is not needed: a tail of `r_n` lies in one arc window around `r₀`
  obtain ⟨M, hr₀M, -⟩ := lz_boundary_arcs hd hr₀0 hr₀1 hr₀
  obtain ⟨w, hw0, hKM, -⟩ := exists_Icc_window M hr₀M hr₀
  have hr₀K : r₀ ∈ Set.Icc (r₀ - w) (r₀ + w) := ⟨by linarith, by linarith⟩
  -- eventually `r_n` lies in the compact window; pass to that tail
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (hrlim.eventually_mem (Icc_mem_nhds (by linarith : r₀ - w < r₀) (by linarith : r₀ < r₀ + w)))
  have hrK : ∀ n, rn (n + N) ∈ Set.Icc (r₀ - w) (r₀ + w) := fun n => hN _ (Nat.le_add_left N n)
  have hpc : ∀ n, pcGlobal d (rn (n + N)) = M.pc (rn (n + N)) :=
    fun n => pcGlobal_eq_pc hd M (hKM (hrK n))
  have hrlim' : Tendsto (fun n => rn (n + N)) atTop (𝓝 r₀) :=
    (tendsto_add_atTop_iff_nat N).mpr hrlim
  have hpclim' : Tendsto (fun n => M.pc (rn (n + N)) - pn (n + N)) atTop (𝓝 0) :=
    ((tendsto_add_atTop_iff_nat N).mpr hpclim).congr (fun n => by rw [hpc n])
  have hpos : ∀ n, 0 < pn (n + N) := fun n => (hpn (n + N)).1
  have hlt : ∀ n, pn (n + N) < M.pc (rn (n + N)) := fun n => hpc n ▸ (hpn (n + N)).2
  refine ⟨?_, ?_⟩
  · have h := cutDist_tendsto_boundary hd M H hreg hm hKM hr₀K ⟨hr₀0.le, hr₀1.le⟩ hrK hrlim'
      hpos hlt hpclim' (fun n => Wn (n + N)) (fun n => hWfeas (n + N)) (fun n => hWopt (n + N))
    exact (tendsto_add_atTop_iff_nat
      (f := fun n => cutDist (Wn n) (constGraphon r₀ ⟨hr₀0.le, hr₀1.le⟩)) N).mp h
  · exact (tendsto_add_atTop_iff_nat N).mp
      (edgeDensity_tendsto_boundary hd M H hreg hm hKM hr₀K hrK hrlim' hpos hlt hpclim'
        (fun n => Wn (n + N)) (fun n => hWfeas (n + N)) (fun n => hWopt (n + N)))

/-- **`cor:scalar-reduction` with the real-valued envelope**, for data as in
`lem:fixed-density-bipodality`: an interval `I = (lo, hi) ⊆ (0,1) ∖ {r_*}` and `ρ₀` such that the
entropy maximizers `B_{ε,r^m}` (`r ∈ I`, `ε ∈ (r-ρ₀, r)`) exist and are unique up to relabelling,
and `ρ < ρ₀`, `η < inf_{r∈I} pc(r)` such that every optimizer at `(p,r)` with `r ∈ I`,
`pc(r) - η < p < pc(r)` has `e(W) ∈ (r-ρ, r)`.  `one_dimensional_reduction` is the paper form. -/
theorem one_dimensional_reduction_real {d : ℕ} (hd : 2 ≤ d) {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (hm : 1 ≤ H.edgeFinset.card)
    {lo hi ρ₀ ρ η : ℝ} (hI : Set.Ioo lo hi ⊆ Set.Ioo (0:ℝ) 1 \ {rStar d})
    (hB : ∀ r ∈ Set.Ioo lo hi, ∀ ε ∈ Set.Ioo (r - ρ₀) r,
      ∃ B : Graphon, B.edgeDensity = ε ∧ B.tDensity H = r ^ H.edgeFinset.card ∧
        (∀ W : Graphon, W.edgeDensity = ε → W.tDensity H = r ^ H.edgeFinset.card →
          W.entropy ≤ B.entropy) ∧
        (∀ W : Graphon, W.edgeDensity = ε → W.tDensity H = r ^ H.edgeFinset.card →
          W.entropy = B.entropy →
          ∃ σ : ℝ → ℝ, IsRelabelling σ ∧
            ∀ᵐ z ∂gμ, W.toFun z.1 z.2 = B.toFun (σ z.1) (σ z.2)))
    (hρ : ρ < ρ₀) (hηinf : η < sInf (pcGlobal d '' Set.Ioo lo hi))
    (hloc : ∀ r ∈ Set.Ioo lo hi, ∀ p : ℝ, pcGlobal d r - η < p → p < pcGlobal d r →
      ∀ W : Graphon, Feasible H r W → W.Ip p = phiVar H p r →
        W.edgeDensity ∈ Set.Ioo (r - ρ) r) :
    ∀ r ∈ Set.Ioo lo hi, ∀ p : ℝ, pcGlobal d r - η < p → p < pcGlobal d r →
      (∃ ε ∈ Set.Ioo (r - ρ) r,
          IsMinOn (fun x => reducedObjectiveReal H p x (r ^ H.edgeFinset.card))
            (Set.Ioo (r - ρ) r) ε ∧
          phiVar H p r = reducedObjectiveReal H p ε (r ^ H.edgeFinset.card)) ∧
        (∀ W : Graphon, Feasible H r W → W.Ip p = phiVar H p r →
          (W.edgeDensity ∈ Set.Ioo (r - ρ) r ∧
            IsMinOn (fun x => reducedObjectiveReal H p x (r ^ H.edgeFinset.card))
              (Set.Ioo (r - ρ) r) W.edgeDensity) ∧
          ∀ B : Graphon, B.edgeDensity = W.edgeDensity →
            B.tDensity H = r ^ H.edgeFinset.card →
            (∀ W' : Graphon, W'.edgeDensity = W.edgeDensity →
              W'.tDensity H = r ^ H.edgeFinset.card → W'.entropy ≤ B.entropy) →
            ∃ σ : ℝ → ℝ, IsRelabelling σ ∧
              ∀ᵐ z ∂gμ, W.toFun z.1 z.2 = B.toFun (σ z.1) (σ z.2)) ∧
        (∀ ε ∈ Set.Ioo (r - ρ) r,
          IsMinOn (fun x => reducedObjectiveReal H p x (r ^ H.edgeFinset.card))
            (Set.Ioo (r - ρ) r) ε →
          ∀ B : Graphon, B.edgeDensity = ε → B.tDensity H = r ^ H.edgeFinset.card →
            (∀ W' : Graphon, W'.edgeDensity = ε →
              W'.tDensity H = r ^ H.edgeFinset.card → W'.entropy ≤ B.entropy) →
            Feasible H r B ∧ B.Ip p = phiVar H p r) ∧
        (∀ W₁ W₂ : Graphon, Feasible H r W₁ → W₁.Ip p = phiVar H p r →
          (∃ σ : ℝ → ℝ, IsRelabelling σ ∧
            ∀ᵐ z ∂gμ, W₂.toFun z.1 z.2 = W₁.toFun (σ z.1) (σ z.2)) →
          Feasible H r W₂ ∧ W₂.Ip p = phiVar H p r ∧
            W₂.edgeDensity = W₁.edgeDensity) ∧
        (∀ W₁ W₂ : Graphon, Feasible H r W₁ → W₁.Ip p = phiVar H p r →
          Feasible H r W₂ → W₂.Ip p = phiVar H p r →
          W₁.edgeDensity = W₂.edgeDensity →
          ∃ σ : ℝ → ℝ, IsRelabelling σ ∧
            ∀ᵐ z ∂gμ, W₂.toFun z.1 z.2 = W₁.toFun (σ z.1) (σ z.2)) ∧
        (∀ ε ∈ Set.Ioo (r - ρ) r,
          IsMinOn (fun x => reducedObjectiveReal H p x (r ^ H.edgeFinset.card))
            (Set.Ioo (r - ρ) r) ε →
          ∃ W : Graphon, Feasible H r W ∧ W.Ip p = phiVar H p r ∧ W.edgeDensity = ε) := by
  classical
  have : Nonempty Graphon := ⟨constGraphon 0 ⟨le_rfl, zero_le_one⟩⟩
  choose! What hWhat using hB
  intro r hr p hlo hhi
  have hrI := hI hr
  have hr0 : 0 < r := hrI.1.1
  have hr1 : r < 1 := hrI.1.2
  obtain ⟨M, hrM, -⟩ := lz_boundary_arcs hd hr0 hr1 hrI.2
  have hpcr : pcGlobal d r < r := by
    rw [pcGlobal_eq_pc hd M hrM]; exact (M.ordering r hrM).2.1
  have hηpc : η < pcGlobal d r := by
    refine lt_of_lt_of_le hηinf (csInf_le ⟨0, ?_⟩ ⟨r, hr, rfl⟩)
    rintro _ ⟨s, hs, rfl⟩
    exact (pcGlobal_pos_le hd (hI hs).1.1 (hI hs).1.2).1.le
  have hp0 : 0 < p := by linarith
  have hpr : p < r := by linarith
  have hp1 : p < 1 := by linarith
  have hsub : Set.Ioo (r - ρ) r ⊆ Set.Ioo (r - ρ₀) r :=
    Set.Ioo_subset_Ioo (by linarith) le_rfl
  -- `Φ ≤ I_{p,r}(ε)` on the strip: `B_{ε,r^m}` is feasible and realises `I_{p,r}(ε)`
  have hPhi_le : ∀ ε ∈ Set.Ioo (r - ρ) r,
      phiVar H p r ≤ reducedObjectiveReal H p ε (r ^ H.edgeFinset.card) := by
    intro ε hε
    obtain ⟨he, ht, hmax, -⟩ := hWhat r hr ε (hsub hε)
    rw [reducedObjective_eq_Ip H hp0 hp1 he ht hmax]
    exact csInf_le (phiVar_bddBelow H hp0 hp1) ⟨What r ε, le_of_eq ht.symm, rfl⟩
  -- every optimizer lies in the strip, saturates the constraint, has the maximal entropy at
  -- its densities, and realises `Φ = I_{p,r}(e(W))`
  have hopt : ∀ W : Graphon, Feasible H r W → W.Ip p = phiVar H p r →
      W.edgeDensity ∈ Set.Ioo (r - ρ) r ∧ W.tDensity H = r ^ H.edgeFinset.card ∧
      W.entropy = (What r W.edgeDensity).entropy ∧
      phiVar H p r = reducedObjectiveReal H p W.edgeDensity (r ^ H.edgeFinset.card) := by
    intro W hWfeas hWopt
    have hmem := hloc r hr p hlo hhi W hWfeas hWopt
    have hact := active_constraint H hp0 hpr hr1 hm W hWfeas hWopt
    obtain ⟨he, ht, hmax, -⟩ := hWhat r hr W.edgeDensity (hsub hmem)
    have hF := reducedObjective_eq_Ip H hp0 hp1 he ht hmax
    have hle : W.entropy ≤ (What r W.edgeDensity).entropy := hmax W rfl hact
    have hPhi := hPhi_le W.edgeDensity hmem
    have h1 := W.Ip_eq_entropy hp0 hp1
    have h2 := (What r W.edgeDensity).Ip_eq_entropy hp0 hp1
    rw [he] at h2
    have hs : W.entropy = (What r W.edgeDensity).entropy := by linarith
    exact ⟨hmem, hact, hs, by rw [hF]; linarith⟩
  -- every optimizer is a relabelling of `B_{e(W),r^m}`
  have hrel : ∀ W : Graphon, Feasible H r W → W.Ip p = phiVar H p r →
      ∃ σ : ℝ → ℝ, IsRelabelling σ ∧
        ∀ᵐ z ∂gμ, W.toFun z.1 z.2 = (What r W.edgeDensity).toFun (σ z.1) (σ z.2) := by
    intro W hWfeas hWopt
    obtain ⟨hmem, hact, hs, -⟩ := hopt W hWfeas hWopt
    exact (hWhat r hr W.edgeDensity (hsub hmem)).2.2.2 W rfl hact hs
  -- the edge density of every optimizer minimizes `I_{p,r}` on the strip
  have hmin : ∀ W : Graphon, Feasible H r W → W.Ip p = phiVar H p r →
      IsMinOn (fun x => reducedObjectiveReal H p x (r ^ H.edgeFinset.card))
        (Set.Ioo (r - ρ) r) W.edgeDensity := by
    intro W hWfeas hWopt
    obtain ⟨-, -, -, hF⟩ := hopt W hWfeas hWopt
    refine isMinOn_iff.mpr fun x hx => ?_
    show reducedObjectiveReal H p W.edgeDensity (r ^ H.edgeFinset.card)
      ≤ reducedObjectiveReal H p x (r ^ H.edgeFinset.card)
    rw [← hF]
    exact hPhi_le x hx
  -- an optimizer exists
  obtain ⟨W0, hW0feas, hW0opt⟩ := feasible_attains H hp0 hp1 hr0 hr1
  obtain ⟨hW0mem, -, -, hW0F⟩ := hopt W0 hW0feas hW0opt
  -- the converse: a maximizer at a minimizing `ε` is an optimizer
  have hconv : ∀ ε ∈ Set.Ioo (r - ρ) r,
      IsMinOn (fun x => reducedObjectiveReal H p x (r ^ H.edgeFinset.card))
        (Set.Ioo (r - ρ) r) ε →
      ∀ B : Graphon, B.edgeDensity = ε → B.tDensity H = r ^ H.edgeFinset.card →
        (∀ W' : Graphon, W'.edgeDensity = ε →
          W'.tDensity H = r ^ H.edgeFinset.card → W'.entropy ≤ B.entropy) →
        Feasible H r B ∧ B.Ip p = phiVar H p r := by
    intro ε _ hεmin B hBe hBt hBmax
    have hBfeas : Feasible H r B := le_of_eq hBt.symm
    refine ⟨hBfeas, le_antisymm ?_ (csInf_le (phiVar_bddBelow H hp0 hp1) ⟨B, hBfeas, rfl⟩)⟩
    rw [← reducedObjective_eq_Ip H hp0 hp1 hBe hBt hBmax, hW0F]
    exact isMinOn_iff.mp hεmin W0.edgeDensity hW0mem
  refine ⟨⟨W0.edgeDensity, hW0mem, hmin W0 hW0feas hW0opt, hW0F⟩, ?_, hconv, ?_, ?_, ?_⟩
  · -- every optimizer is `B_{e(W),r^m}` up to relabelling, for any choice of the maximizer
    intro W hWfeas hWopt
    refine ⟨⟨(hopt W hWfeas hWopt).1, hmin W hWfeas hWopt⟩, fun B hBe hBt hBmax => ?_⟩
    obtain ⟨hmem, hact, hs, -⟩ := hopt W hWfeas hWopt
    obtain ⟨he, ht, hmax, huniq⟩ := hWhat r hr W.edgeDensity (hsub hmem)
    have hsB : B.entropy = (What r W.edgeDensity).entropy :=
      le_antisymm (hmax B hBe hBt) (hBmax _ he ht)
    obtain ⟨σ, hσ, hWσ⟩ := huniq W rfl hact hs
    obtain ⟨τ, hτ, hBτ⟩ := huniq B hBe hBt hsB
    obtain ⟨τ', hτ', hτ'B⟩ := exists_relabel_symm hτ hBτ
    exact ⟨fun x => τ' (σ x), hτ'.comp hσ, ae_relabel_trans hσ.measurePreserving hWσ hτ'B⟩
  · -- `e(·)` is well defined on optimizers modulo relabelling
    rintro W₁ W₂ hW₁feas hW₁opt ⟨σ, hσ, h⟩
    have ht := tDensity_relabel hσ.measurePreserving H h
    refine ⟨?_, ?_, Graphon.edgeDensity_relabel hσ.measurePreserving h⟩
    · show r ^ H.edgeFinset.card ≤ W₂.tDensity H
      rw [ht]
      exact hW₁feas
    · rw [Graphon.Ip_relabel p hσ.measurePreserving h]
      exact hW₁opt
  · -- injectivity: optimizers with equal edge density are relabellings of each other
    intro W₁ W₂ hW₁feas hW₁opt hW₂feas hW₂opt heq
    obtain ⟨σ₁, hσ₁, h₁⟩ := hrel W₁ hW₁feas hW₁opt
    obtain ⟨σ₂, hσ₂, h₂⟩ := hrel W₂ hW₂feas hW₂opt
    rw [← heq] at h₂
    obtain ⟨τ₁, hτ₁, hB₁⟩ := exists_relabel_symm hσ₁ h₁
    exact ⟨fun x => τ₁ (σ₂ x), hτ₁.comp hσ₂, ae_relabel_trans hσ₂.measurePreserving h₂ hB₁⟩
  · -- surjectivity: every minimizer is the edge density of an optimizer
    intro ε hε hεmin
    obtain ⟨he, ht, hmax, -⟩ := hWhat r hr ε (hsub hε)
    obtain ⟨hfeas, hIp⟩ := hconv ε hε hεmin (What r ε) he ht hmax
    exact ⟨What r ε, hfeas, hIp, he⟩

/-- **`cor:scalar-reduction`.**  Let `I = (lo, hi) ⊆ (0,1) ∖ {r_*}` and `ρ₀` be as in
`lem:fixed-density-bipodality` (the entropy maximizers `B_{ε,r^m}` exist and are unique up to
relabelling for `r ∈ I`, `ε ∈ (r-ρ₀, r)`), let `ρ < ρ₀`, and let `η < inf_{r∈I} pc(r)` be as in that
lemma (optimizers at `r ∈ I`, `pc(r) - η < p < pc(r)` have `e(W) ∈ (r-ρ, r)`).  Then for such
`r, p`: `Φ_H(p,r) = min_{ε∈(r-ρ,r)} I_{p,r}(ε)`; every optimizer `W*` is `B_{e(W*),r^m}` up to
relabelling and `e(W*)` minimizes `I_{p,r}` on `(r-ρ,r)`; conversely `B_{ε,r^m}` is an optimizer for
every such minimizer `ε`; and `W* ↦ e(W*)` is a bijection from optimizers modulo relabelling onto
these minimizers (well defined, injective and onto). -/
theorem one_dimensional_reduction {d : ℕ} (hd : 2 ≤ d) {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (hm : 1 ≤ H.edgeFinset.card)
    {lo hi ρ₀ ρ η : ℝ} (hI : Set.Ioo lo hi ⊆ Set.Ioo (0:ℝ) 1 \ {rStar d})
    (hB : ∀ r ∈ Set.Ioo lo hi, ∀ ε ∈ Set.Ioo (r - ρ₀) r,
      ∃ B : Graphon, B.edgeDensity = ε ∧ B.tDensity H = r ^ H.edgeFinset.card ∧
        (∀ W : Graphon, W.edgeDensity = ε → W.tDensity H = r ^ H.edgeFinset.card →
          W.entropy ≤ B.entropy) ∧
        (∀ W : Graphon, W.edgeDensity = ε → W.tDensity H = r ^ H.edgeFinset.card →
          W.entropy = B.entropy →
          ∃ σ : ℝ → ℝ, IsRelabelling σ ∧
            ∀ᵐ z ∂gμ, W.toFun z.1 z.2 = B.toFun (σ z.1) (σ z.2)))
    (hρ : ρ < ρ₀) (hηinf : η < sInf (pcGlobal d '' Set.Ioo lo hi))
    (hloc : ∀ r ∈ Set.Ioo lo hi, ∀ p : ℝ, pcGlobal d r - η < p → p < pcGlobal d r →
      ∀ W : Graphon, Feasible H r W → W.Ip p = phiVar H p r →
        W.edgeDensity ∈ Set.Ioo (r - ρ) r) :
    ∀ r ∈ Set.Ioo lo hi, ∀ p : ℝ, pcGlobal d r - η < p → p < pcGlobal d r →
      (∃ ε ∈ Set.Ioo (r - ρ) r,
          IsMinOn (fun x => reducedObjective H p r x)
            (Set.Ioo (r - ρ) r) ε ∧
          (phiVar H p r : EReal) = reducedObjective H p r ε) ∧
        (∀ W : Graphon, Feasible H r W → W.Ip p = phiVar H p r →
          (W.edgeDensity ∈ Set.Ioo (r - ρ) r ∧
            IsMinOn (fun x => reducedObjective H p r x)
              (Set.Ioo (r - ρ) r) W.edgeDensity) ∧
          ∀ B : Graphon, B.edgeDensity = W.edgeDensity →
            B.tDensity H = r ^ H.edgeFinset.card →
            (∀ W' : Graphon, W'.edgeDensity = W.edgeDensity →
              W'.tDensity H = r ^ H.edgeFinset.card → W'.entropy ≤ B.entropy) →
            ∃ σ : ℝ → ℝ, IsRelabelling σ ∧
              ∀ᵐ z ∂gμ, W.toFun z.1 z.2 = B.toFun (σ z.1) (σ z.2)) ∧
        (∀ ε ∈ Set.Ioo (r - ρ) r,
          IsMinOn (fun x => reducedObjective H p r x)
            (Set.Ioo (r - ρ) r) ε →
          ∀ B : Graphon, B.edgeDensity = ε → B.tDensity H = r ^ H.edgeFinset.card →
            (∀ W' : Graphon, W'.edgeDensity = ε →
              W'.tDensity H = r ^ H.edgeFinset.card → W'.entropy ≤ B.entropy) →
            Feasible H r B ∧ B.Ip p = phiVar H p r) ∧
        (∀ W₁ W₂ : Graphon, Feasible H r W₁ → W₁.Ip p = phiVar H p r →
          (∃ σ : ℝ → ℝ, IsRelabelling σ ∧
            ∀ᵐ z ∂gμ, W₂.toFun z.1 z.2 = W₁.toFun (σ z.1) (σ z.2)) →
          Feasible H r W₂ ∧ W₂.Ip p = phiVar H p r ∧
            W₂.edgeDensity = W₁.edgeDensity) ∧
        (∀ W₁ W₂ : Graphon, Feasible H r W₁ → W₁.Ip p = phiVar H p r →
          Feasible H r W₂ → W₂.Ip p = phiVar H p r →
          W₁.edgeDensity = W₂.edgeDensity →
          ∃ σ : ℝ → ℝ, IsRelabelling σ ∧
            ∀ᵐ z ∂gμ, W₂.toFun z.1 z.2 = W₁.toFun (σ z.1) (σ z.2)) ∧
        (∀ ε ∈ Set.Ioo (r - ρ) r,
          IsMinOn (fun x => reducedObjective H p r x)
            (Set.Ioo (r - ρ) r) ε →
          ∃ W : Graphon, Feasible H r W ∧ W.Ip p = phiVar H p r ∧ W.edgeDensity = ε) := by
  intro r hr p hlo hhi
  have hne : ∀ ε ∈ Set.Ioo (r - ρ₀) r,
      ∃ W : Graphon, W.edgeDensity = ε ∧ W.tDensity H = r ^ H.edgeFinset.card := by
    intro ε hε
    obtain ⟨B, hBe, hBt, -⟩ := hB r hr ε hε
    exact ⟨B, hBe, hBt⟩
  have hcoe : ∀ ε ∈ Set.Ioo (r - ρ₀) r,
      reducedObjective H p r ε = (reducedObjectiveReal H p ε (r ^ H.edgeFinset.card) : EReal) :=
    fun ε hε => reducedObjective_eq_coe H (hne ε hε)
  have hsub : ∀ x ∈ Set.Ioo (r - ρ) r, x ∈ Set.Ioo (r - ρ₀) r :=
    fun x hx => ⟨by linarith [hx.1], hx.2⟩
  have hmin : ∀ ε ∈ Set.Ioo (r - ρ) r,
      (IsMinOn (fun x => reducedObjective H p r x) (Set.Ioo (r - ρ) r) ε ↔
        IsMinOn (fun x => reducedObjectiveReal H p x (r ^ H.edgeFinset.card))
          (Set.Ioo (r - ρ) r) ε) := by
    intro ε hε
    simp only [isMinOn_iff]
    refine forall₂_congr fun x hx => ?_
    rw [hcoe x (hsub x hx), hcoe ε (hsub ε hε), EReal.coe_le_coe_iff]
  obtain ⟨⟨ε, hε, hεmin, hΦ⟩, hopt, hconv, hwd, hinj, hsurj⟩ :=
    one_dimensional_reduction_real hd H hm hI hB hρ hηinf hloc r hr p hlo hhi
  refine ⟨⟨ε, hε, (hmin ε hε).mpr hεmin, by rw [hcoe ε (hsub ε hε), hΦ]⟩,
    fun W hWf hWo => ?_, fun ε hε hεmin => hconv ε hε ((hmin ε hε).mp hεmin), hwd,
    hinj, fun ε hε hεmin => hsurj ε hε ((hmin ε hε).mp hεmin)⟩
  obtain ⟨⟨hmem, hWmin⟩, hrel⟩ := hopt W hWf hWo
  exact ⟨⟨hmem, (hmin W.edgeDensity hmem).mpr hWmin⟩, hrel⟩

/-- **`uniform_scalar_reduction` with the real-valued envelope.**  The same statement with
`entropyEnvelopeReal` and `reducedObjectiveReal`; on the strip every constraint set is nonempty,
so it is equivalent to the paper form below. -/
theorem uniform_scalar_reduction_real {d : ℕ} (hd : 2 ≤ d) {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (hreg : ∀ v, H.degree v = d)
    (hm : 1 ≤ H.edgeFinset.card) {r₀ : ℝ} (hr₀0 : 0 < r₀) (hr₀1 : r₀ < 1)
    (hr₀ : r₀ ≠ rStar d) :
    ∃ ρ₀ lo hi : ℝ, 0 < ρ₀ ∧ lo < r₀ ∧ r₀ < hi ∧
      Set.Ioo lo hi ⊆ Set.Ioo (0:ℝ) 1 \ {rStar d} ∧
      (∀ r ∈ Set.Ioo lo hi, ∀ ε ∈ Set.Ioo (r - ρ₀) r,
        ∃ B : Graphon, B.edgeDensity = ε ∧ B.tDensity H = r ^ H.edgeFinset.card ∧
          (∀ W : Graphon, W.edgeDensity = ε → W.tDensity H = r ^ H.edgeFinset.card →
            W.entropy ≤ B.entropy) ∧
          (∀ W : Graphon, W.edgeDensity = ε → W.tDensity H = r ^ H.edgeFinset.card →
            W.entropy = B.entropy →
            ∃ σ : ℝ → ℝ, IsRelabelling σ ∧
              ∀ᵐ z ∂gμ, W.toFun z.1 z.2 = B.toFun (σ z.1) (σ z.2)) ∧
          IsBipodal B ∧
          B.entropy = entropyEnvelopeReal H ε (r ^ H.edgeFinset.card) ∧
          ∀ p : ℝ, 0 < p → p < 1 →
            reducedObjectiveReal H p ε (r ^ H.edgeFinset.card) = B.Ip p) ∧
      ∀ ρ : ℝ, 0 < ρ → ρ < ρ₀ →
        ∃ η : ℝ, 0 < η ∧ η < sInf (pcGlobal d '' Set.Ioo lo hi) ∧
          (∀ r ∈ Set.Ioo lo hi, ∀ p : ℝ, pcGlobal d r - η < p → p < pcGlobal d r →
            ∀ W : Graphon, Feasible H r W → W.Ip p = phiVar H p r →
              W.edgeDensity ∈ Set.Ioo (r - ρ) r) ∧
          ∀ r ∈ Set.Ioo lo hi, ∀ p : ℝ, pcGlobal d r - η < p → p < pcGlobal d r →
            -- `Φ_H(p,r) = min_{ε ∈ (r-ρ,r)} I_{p,r}(ε)`
            (∃ ε ∈ Set.Ioo (r - ρ) r,
              IsMinOn (fun x => reducedObjectiveReal H p x (r ^ H.edgeFinset.card))
                (Set.Ioo (r - ρ) r) ε ∧
              phiVar H p r = reducedObjectiveReal H p ε (r ^ H.edgeFinset.card)) ∧
            -- every optimizer is `B_{e(W*),r^m}` up to relabelling, and `e(W*)` is a minimizer
            (∀ W : Graphon, Feasible H r W → W.Ip p = phiVar H p r →
              (W.edgeDensity ∈ Set.Ioo (r - ρ) r ∧
                IsMinOn (fun x => reducedObjectiveReal H p x (r ^ H.edgeFinset.card))
                  (Set.Ioo (r - ρ) r) W.edgeDensity) ∧
              ∀ B : Graphon, B.edgeDensity = W.edgeDensity →
                B.tDensity H = r ^ H.edgeFinset.card →
                (∀ W' : Graphon, W'.edgeDensity = W.edgeDensity →
                  W'.tDensity H = r ^ H.edgeFinset.card → W'.entropy ≤ B.entropy) →
                ∃ σ : ℝ → ℝ, IsRelabelling σ ∧
                  ∀ᵐ z ∂gμ, W.toFun z.1 z.2 = B.toFun (σ z.1) (σ z.2)) ∧
            -- conversely, `B_{ε,r^m}` is an optimizer for every minimizer `ε`
            (∀ ε ∈ Set.Ioo (r - ρ) r,
              IsMinOn (fun x => reducedObjectiveReal H p x (r ^ H.edgeFinset.card))
                (Set.Ioo (r - ρ) r) ε →
              ∀ B : Graphon, B.edgeDensity = ε → B.tDensity H = r ^ H.edgeFinset.card →
                (∀ W' : Graphon, W'.edgeDensity = ε →
                  W'.tDensity H = r ^ H.edgeFinset.card → W'.entropy ≤ B.entropy) →
                Feasible H r B ∧ B.Ip p = phiVar H p r) ∧
            -- `W* ↦ e(W*)` is a bijection from optimizers modulo relabelling onto the minimizers
            (∀ W₁ W₂ : Graphon, Feasible H r W₁ → W₁.Ip p = phiVar H p r →
              (∃ σ : ℝ → ℝ, IsRelabelling σ ∧
                ∀ᵐ z ∂gμ, W₂.toFun z.1 z.2 = W₁.toFun (σ z.1) (σ z.2)) →
              Feasible H r W₂ ∧ W₂.Ip p = phiVar H p r ∧
                W₂.edgeDensity = W₁.edgeDensity) ∧
            (∀ W₁ W₂ : Graphon, Feasible H r W₁ → W₁.Ip p = phiVar H p r →
              Feasible H r W₂ → W₂.Ip p = phiVar H p r →
              W₁.edgeDensity = W₂.edgeDensity →
              ∃ σ : ℝ → ℝ, IsRelabelling σ ∧
                ∀ᵐ z ∂gμ, W₂.toFun z.1 z.2 = W₁.toFun (σ z.1) (σ z.2)) ∧
            (∀ ε ∈ Set.Ioo (r - ρ) r,
              IsMinOn (fun x => reducedObjectiveReal H p x (r ^ H.edgeFinset.card))
                (Set.Ioo (r - ρ) r) ε →
              ∃ W : Graphon, Feasible H r W ∧ W.Ip p = phiVar H p r ∧ W.edgeDensity = ε) := by
  classical
  -- one arc through `r₀`, a compact window `K = [r₀ - w, r₀ + w]` in it, and `I = (r₀ ± w/2)`
  obtain ⟨M, hr₀M, -⟩ := lz_boundary_arcs hd hr₀0 hr₀1 hr₀
  obtain ⟨w, hw0, hKM, hKex⟩ := exists_Icc_window M hr₀M hr₀
  have hKc : IsCompact (Set.Icc (r₀ - w) (r₀ + w)) := isCompact_Icc
  have hKne : (Set.Icc (r₀ - w) (r₀ + w)).Nonempty := Set.nonempty_Icc.mpr (by linarith)
  have hIK : Set.Ioo (r₀ - w / 2) (r₀ + w / 2) ⊆ Set.Icc (r₀ - w) (r₀ + w) :=
    fun r hr => ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have hpc : ∀ r ∈ Set.Ioo (r₀ - w / 2) (r₀ + w / 2), pcGlobal d r = M.pc r :=
    fun r hr => pcGlobal_eq_pc hd M (hKM (hIK hr))
  -- the KRR-S maximizer family on the strip, and a uniform lower bound `ηK ≤ pc` on `K`
  obtain ⟨ρ₀, hρ₀0, What, hWhat⟩ := krrs_strip hd M hKM hKc hKne hKex H hreg hm
  obtain ⟨ηK, hηK0, -, hηK⟩ := arc_uniform_bounds M hKM hKc hKne
  have hIsub : Set.Ioo (r₀ - w / 2) (r₀ + w / 2) ⊆ Set.Ioo (0:ℝ) 1 \ {rStar d} := by
    intro r hr
    obtain ⟨hpc0, hpcr, hr1, -⟩ := M.ordering r (hKM (hIK hr))
    exact ⟨⟨lt_trans hpc0 hpcr, hr1⟩, hKex r (hIK hr)⟩
  refine ⟨ρ₀, r₀ - w / 2, r₀ + w / 2, hρ₀0, by linarith, by linarith, hIsub, ?_, ?_⟩
  · -- the maximizer `B_{ε,r^m}` and `eq:reduced-objective-attainment`
    intro r hr ε hε
    obtain ⟨he, ht, hbip, hmax, huniq⟩ := hWhat r (hIK hr) ε hε
    exact ⟨What ε r, he, ht, hmax, huniq, hbip, (entropyEnvelope_eq_of_isMax H he ht hmax).symm,
      fun p hp0 hp1 => reducedObjective_eq_Ip H hp0 hp1 he ht hmax⟩
  intro ρ hρ0 hρ
  obtain ⟨ηloc, hηloc0, hloc⟩ := uniform_localization hd M H hreg hm hKM hKc hKne hρ0
  have hηle' : min ηloc (ηK / 2) ≤ ηK / 2 := min_le_right _ _
  have hηinf : ηK ≤ sInf (pcGlobal d '' Set.Ioo (r₀ - w / 2) (r₀ + w / 2)) := by
    refine le_csInf ⟨pcGlobal d r₀, r₀, ⟨by linarith, by linarith⟩, rfl⟩ ?_
    rintro _ ⟨r, hr, rfl⟩
    rw [hpc r hr]
    exact (hηK r (hIK hr)).2.2.2.2.1
  have hη' : min ηloc (ηK / 2) < sInf (pcGlobal d '' Set.Ioo (r₀ - w / 2) (r₀ + w / 2)) := by
    linarith
  -- the localization clause
  have hloc' : ∀ r ∈ Set.Ioo (r₀ - w / 2) (r₀ + w / 2), ∀ p : ℝ,
      pcGlobal d r - min ηloc (ηK / 2) < p → p < pcGlobal d r →
      ∀ W : Graphon, Feasible H r W → W.Ip p = phiVar H p r →
        W.edgeDensity ∈ Set.Ioo (r - ρ) r := by
    intro r hr p hlo hhi W hWfeas hWopt
    rw [hpc r hr] at hlo hhi
    exact hloc r (hIK hr) p (by linarith [min_le_left ηloc (ηK / 2)]) hhi W hWfeas hWopt
  refine ⟨min ηloc (ηK / 2), lt_min hηloc0 (by linarith), hη', hloc', ?_⟩
  -- the corollary
  refine one_dimensional_reduction_real hd H hm hIsub (fun r hr ε hε => ?_) hρ hη' hloc'
  obtain ⟨he, ht, -, hmax, huniq⟩ := hWhat r (hIK hr) ε hε
  exact ⟨What ε r, he, ht, hmax, huniq⟩

/-- **`lem:fixed-density-bipodality` and `cor:scalar-reduction`.**  Fix `r₀ ∈ (0,1) ∖ {r_*}`.
There are `ρ₀ > 0` and an open interval `I = (lo, hi) ⊆ (0,1) ∖ {r_*}` containing `r₀` such that:

* (lemma) for `r ∈ I` and `ε ∈ (r-ρ₀, r)` the entropy maximizer `B_{ε,r^m}` at edge density `ε`
  and `H`-density `r^m` exists, is bipodal and is unique up to relabelling, and for every
  `p ∈ (0,1)`, `s(B_{ε,r^m}) = S_H(ε,r^m)` and `I_{p,r}(ε) = I_p(B_{ε,r^m})`;
* (lemma) for every `0 < ρ < ρ₀` there is `0 < η < inf_{r∈I} pc(r)` such that every optimizer
  at `(p,r)` with `r ∈ I`, `pc(r) - η < p < pc(r)` has `e(W) ∈ (r-ρ, r)`;
* (corollary) for these `ρ, η, r, p`: `Φ_H(p,r) = min_{ε∈(r-ρ,r)} I_{p,r}(ε)`; every optimizer
  `W*` is `B_{e(W*),r^m}` up to relabelling and `e(W*)` minimizes `I_{p,r}` on `(r-ρ,r)`;
  conversely `B_{ε,r^m}` is an optimizer for every such minimizer `ε`; and `W* ↦ e(W*)` is a
  bijection from optimizers modulo relabelling onto the minimizers of `I_{p,r}` on `(r-ρ,r)`
  (it is well defined, injective and onto). -/
theorem uniform_scalar_reduction {d : ℕ} (hd : 2 ≤ d) {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (hreg : ∀ v, H.degree v = d)
    (hm : 1 ≤ H.edgeFinset.card) {r₀ : ℝ} (hr₀0 : 0 < r₀) (hr₀1 : r₀ < 1)
    (hr₀ : r₀ ≠ rStar d) :
    ∃ ρ₀ lo hi : ℝ, 0 < ρ₀ ∧ lo < r₀ ∧ r₀ < hi ∧
      Set.Ioo lo hi ⊆ Set.Ioo (0:ℝ) 1 \ {rStar d} ∧
      (∀ r ∈ Set.Ioo lo hi, ∀ ε ∈ Set.Ioo (r - ρ₀) r,
        ∃ B : Graphon, B.edgeDensity = ε ∧ B.tDensity H = r ^ H.edgeFinset.card ∧
          (∀ W : Graphon, W.edgeDensity = ε → W.tDensity H = r ^ H.edgeFinset.card →
            W.entropy ≤ B.entropy) ∧
          (∀ W : Graphon, W.edgeDensity = ε → W.tDensity H = r ^ H.edgeFinset.card →
            W.entropy = B.entropy →
            ∃ σ : ℝ → ℝ, IsRelabelling σ ∧
              ∀ᵐ z ∂gμ, W.toFun z.1 z.2 = B.toFun (σ z.1) (σ z.2)) ∧
          IsBipodal B ∧
          (B.entropy : EReal) = entropyEnvelope H ε (r ^ H.edgeFinset.card) ∧
          ∀ p : ℝ, 0 < p → p < 1 →
            reducedObjective H p r ε = (B.Ip p : EReal)) ∧
      ∀ ρ : ℝ, 0 < ρ → ρ < ρ₀ →
        ∃ η : ℝ, 0 < η ∧ η < sInf (pcGlobal d '' Set.Ioo lo hi) ∧
          (∀ r ∈ Set.Ioo lo hi, ∀ p : ℝ, pcGlobal d r - η < p → p < pcGlobal d r →
            ∀ W : Graphon, Feasible H r W → W.Ip p = phiVar H p r →
              W.edgeDensity ∈ Set.Ioo (r - ρ) r) ∧
          ∀ r ∈ Set.Ioo lo hi, ∀ p : ℝ, pcGlobal d r - η < p → p < pcGlobal d r →
            -- `Φ_H(p,r) = min_{ε ∈ (r-ρ,r)} I_{p,r}(ε)`
            (∃ ε ∈ Set.Ioo (r - ρ) r,
              IsMinOn (fun x => reducedObjective H p r x)
                (Set.Ioo (r - ρ) r) ε ∧
              (phiVar H p r : EReal) = reducedObjective H p r ε) ∧
            -- every optimizer is `B_{e(W*),r^m}` up to relabelling, and `e(W*)` is a minimizer
            (∀ W : Graphon, Feasible H r W → W.Ip p = phiVar H p r →
              (W.edgeDensity ∈ Set.Ioo (r - ρ) r ∧
                IsMinOn (fun x => reducedObjective H p r x)
                  (Set.Ioo (r - ρ) r) W.edgeDensity) ∧
              ∀ B : Graphon, B.edgeDensity = W.edgeDensity →
                B.tDensity H = r ^ H.edgeFinset.card →
                (∀ W' : Graphon, W'.edgeDensity = W.edgeDensity →
                  W'.tDensity H = r ^ H.edgeFinset.card → W'.entropy ≤ B.entropy) →
                ∃ σ : ℝ → ℝ, IsRelabelling σ ∧
                  ∀ᵐ z ∂gμ, W.toFun z.1 z.2 = B.toFun (σ z.1) (σ z.2)) ∧
            -- conversely, `B_{ε,r^m}` is an optimizer for every minimizer `ε`
            (∀ ε ∈ Set.Ioo (r - ρ) r,
              IsMinOn (fun x => reducedObjective H p r x)
                (Set.Ioo (r - ρ) r) ε →
              ∀ B : Graphon, B.edgeDensity = ε → B.tDensity H = r ^ H.edgeFinset.card →
                (∀ W' : Graphon, W'.edgeDensity = ε →
                  W'.tDensity H = r ^ H.edgeFinset.card → W'.entropy ≤ B.entropy) →
                Feasible H r B ∧ B.Ip p = phiVar H p r) ∧
            -- `W* ↦ e(W*)` is a bijection from optimizers modulo relabelling onto the minimizers
            (∀ W₁ W₂ : Graphon, Feasible H r W₁ → W₁.Ip p = phiVar H p r →
              (∃ σ : ℝ → ℝ, IsRelabelling σ ∧
                ∀ᵐ z ∂gμ, W₂.toFun z.1 z.2 = W₁.toFun (σ z.1) (σ z.2)) →
              Feasible H r W₂ ∧ W₂.Ip p = phiVar H p r ∧
                W₂.edgeDensity = W₁.edgeDensity) ∧
            (∀ W₁ W₂ : Graphon, Feasible H r W₁ → W₁.Ip p = phiVar H p r →
              Feasible H r W₂ → W₂.Ip p = phiVar H p r →
              W₁.edgeDensity = W₂.edgeDensity →
              ∃ σ : ℝ → ℝ, IsRelabelling σ ∧
                ∀ᵐ z ∂gμ, W₂.toFun z.1 z.2 = W₁.toFun (σ z.1) (σ z.2)) ∧
            (∀ ε ∈ Set.Ioo (r - ρ) r,
              IsMinOn (fun x => reducedObjective H p r x)
                (Set.Ioo (r - ρ) r) ε →
              ∃ W : Graphon, Feasible H r W ∧ W.Ip p = phiVar H p r ∧ W.edgeDensity = ε) := by
  obtain ⟨ρ₀, lo, hi, hρ₀, hlo, hhi, hI, hB, hη⟩ :=
    uniform_scalar_reduction_real hd H hreg hm hr₀0 hr₀1 hr₀
  have hB' : ∀ r ∈ Set.Ioo lo hi, ∀ ε ∈ Set.Ioo (r - ρ₀) r,
      ∃ B : Graphon, B.edgeDensity = ε ∧ B.tDensity H = r ^ H.edgeFinset.card ∧
        (∀ W : Graphon, W.edgeDensity = ε → W.tDensity H = r ^ H.edgeFinset.card →
          W.entropy ≤ B.entropy) ∧
        (∀ W : Graphon, W.edgeDensity = ε → W.tDensity H = r ^ H.edgeFinset.card →
          W.entropy = B.entropy →
          ∃ σ : ℝ → ℝ, IsRelabelling σ ∧
            ∀ᵐ z ∂gμ, W.toFun z.1 z.2 = B.toFun (σ z.1) (σ z.2)) := by
    intro r hr ε hε
    obtain ⟨B, hBe, hBt, hmax, huniq, -⟩ := hB r hr ε hε
    exact ⟨B, hBe, hBt, hmax, huniq⟩
  refine ⟨ρ₀, lo, hi, hρ₀, hlo, hhi, hI, fun r hr ε hε => ?_, fun ρ hρ0 hρ => ?_⟩
  · -- on the strip the constraint set is nonempty, so the paper values are the real ones
    obtain ⟨B, hBe, hBt, hmax, huniq, hbip, hent, hred⟩ := hB r hr ε hε
    refine ⟨B, hBe, hBt, hmax, huniq, hbip, ?_, fun p hp0 hp1 => ?_⟩
    · rw [entropyEnvelope_eq_coe H ⟨B, hBe, hBt⟩, hent]
    · rw [reducedObjective_eq_coe H ⟨B, hBe, hBt⟩, hred p hp0 hp1]
  obtain ⟨η, hη0, hηinf, hloc, -⟩ := hη ρ hρ0 hρ
  exact ⟨η, hη0, hηinf, hloc, one_dimensional_reduction hd H hm hI hB' hρ hηinf hloc⟩

/-- **`lem:fixed-density-bipodality` (uniform localization and fixed-density bipodality).**
The lemma's clauses of `uniform_scalar_reduction`. -/
theorem fixed_density_bipodality {d : ℕ} (hd : 2 ≤ d) {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (hreg : ∀ v, H.degree v = d)
    (hm : 1 ≤ H.edgeFinset.card) {r₀ : ℝ} (hr₀0 : 0 < r₀) (hr₀1 : r₀ < 1)
    (hr₀ : r₀ ≠ rStar d) :
    ∃ ρ₀ lo hi : ℝ, 0 < ρ₀ ∧ lo < r₀ ∧ r₀ < hi ∧
      Set.Ioo lo hi ⊆ Set.Ioo (0:ℝ) 1 \ {rStar d} ∧
      (∀ r ∈ Set.Ioo lo hi, ∀ ε ∈ Set.Ioo (r - ρ₀) r,
        ∃ B : Graphon, B.edgeDensity = ε ∧ B.tDensity H = r ^ H.edgeFinset.card ∧
          (∀ W : Graphon, W.edgeDensity = ε → W.tDensity H = r ^ H.edgeFinset.card →
            W.entropy ≤ B.entropy) ∧
          (∀ W : Graphon, W.edgeDensity = ε → W.tDensity H = r ^ H.edgeFinset.card →
            W.entropy = B.entropy →
            ∃ σ : ℝ → ℝ, IsRelabelling σ ∧
              ∀ᵐ z ∂gμ, W.toFun z.1 z.2 = B.toFun (σ z.1) (σ z.2)) ∧
          IsBipodal B ∧
          (B.entropy : EReal) = entropyEnvelope H ε (r ^ H.edgeFinset.card) ∧
          ∀ p : ℝ, 0 < p → p < 1 →
            reducedObjective H p r ε = (B.Ip p : EReal)) ∧
      ∀ ρ : ℝ, 0 < ρ → ρ < ρ₀ →
        ∃ η : ℝ, 0 < η ∧ η < sInf (pcGlobal d '' Set.Ioo lo hi) ∧
          ∀ r ∈ Set.Ioo lo hi, ∀ p : ℝ, pcGlobal d r - η < p → p < pcGlobal d r →
            ∀ W : Graphon, Feasible H r W → W.Ip p = phiVar H p r →
              W.edgeDensity ∈ Set.Ioo (r - ρ) r := by
  obtain ⟨ρ₀, lo, hi, hρ₀, hlo, hhi, hI, hB, hη⟩ :=
    uniform_scalar_reduction hd H hreg hm hr₀0 hr₀1 hr₀
  refine ⟨ρ₀, lo, hi, hρ₀, hlo, hhi, hI, hB, fun ρ hρ0 hρ => ?_⟩
  obtain ⟨η, hη0, hηinf, hloc, -⟩ := hη ρ hρ0 hρ
  exact ⟨η, hη0, hηinf, hloc⟩

/-- **`lem:fixed-density-bipodality`, with the compact closure of `I`.**  The clauses of
`fixed_density_bipodality`, for an interval `I = (lo, hi)` whose closure `[lo, hi]` lies in
`(0,1) ∖ {r_*}`.  The paper's proof of the lemma chooses `I` this way, and
`sec:nonexceptional-quadratic-growth` works on this `I`: `scalar_quadratic_bound_Icc` and
`graphon_quadratic_bound_Icc` (`NonexceptionalEndpoint/QuadraticGrowth/Global.lean`) hold on every such interval.

The interval is built as in `uniform_scalar_reduction_real`: `I = (r₀ - w/2, r₀ + w/2)` for the
window `[r₀ - w, r₀ + w]` of `exists_Icc_window`, which lies in one arc window and avoids `r_*`. -/
theorem fixed_density_bipodality_Icc {d : ℕ} (hd : 2 ≤ d) {V : Type*} [Fintype V]
    [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj] (hreg : ∀ v, H.degree v = d)
    (hm : 1 ≤ H.edgeFinset.card) {r₀ : ℝ} (hr₀0 : 0 < r₀) (hr₀1 : r₀ < 1)
    (hr₀ : r₀ ≠ rStar d) :
    ∃ ρ₀ lo hi : ℝ, 0 < ρ₀ ∧ lo < r₀ ∧ r₀ < hi ∧
      Set.Icc lo hi ⊆ Set.Ioo (0:ℝ) 1 \ {rStar d} ∧
      (∀ r ∈ Set.Ioo lo hi, ∀ ε ∈ Set.Ioo (r - ρ₀) r,
        ∃ B : Graphon, B.edgeDensity = ε ∧ B.tDensity H = r ^ H.edgeFinset.card ∧
          (∀ W : Graphon, W.edgeDensity = ε → W.tDensity H = r ^ H.edgeFinset.card →
            W.entropy ≤ B.entropy) ∧
          (∀ W : Graphon, W.edgeDensity = ε → W.tDensity H = r ^ H.edgeFinset.card →
            W.entropy = B.entropy →
            ∃ σ : ℝ → ℝ, IsRelabelling σ ∧
              ∀ᵐ z ∂gμ, W.toFun z.1 z.2 = B.toFun (σ z.1) (σ z.2)) ∧
          IsBipodal B ∧
          (B.entropy : EReal) = entropyEnvelope H ε (r ^ H.edgeFinset.card) ∧
          ∀ p : ℝ, 0 < p → p < 1 →
            reducedObjective H p r ε = (B.Ip p : EReal)) ∧
      ∀ ρ : ℝ, 0 < ρ → ρ < ρ₀ →
        ∃ η : ℝ, 0 < η ∧ η < sInf (pcGlobal d '' Set.Ioo lo hi) ∧
          ∀ r ∈ Set.Ioo lo hi, ∀ p : ℝ, pcGlobal d r - η < p → p < pcGlobal d r →
            ∀ W : Graphon, Feasible H r W → W.Ip p = phiVar H p r →
              W.edgeDensity ∈ Set.Ioo (r - ρ) r := by
  classical
  -- one arc through `r₀`, a compact window `K = [r₀ - w, r₀ + w]` in it, and `I = (r₀ ± w/2)`
  obtain ⟨M, hr₀M, -⟩ := lz_boundary_arcs hd hr₀0 hr₀1 hr₀
  obtain ⟨w, hw0, hKM, hKex⟩ := exists_Icc_window M hr₀M hr₀
  have hKc : IsCompact (Set.Icc (r₀ - w) (r₀ + w)) := isCompact_Icc
  have hKne : (Set.Icc (r₀ - w) (r₀ + w)).Nonempty := Set.nonempty_Icc.mpr (by linarith)
  have hIK : Set.Icc (r₀ - w / 2) (r₀ + w / 2) ⊆ Set.Icc (r₀ - w) (r₀ + w) :=
    Set.Icc_subset_Icc (by linarith) (by linarith)
  have hIoo : Set.Ioo (r₀ - w / 2) (r₀ + w / 2) ⊆ Set.Icc (r₀ - w) (r₀ + w) :=
    Set.Ioo_subset_Icc_self.trans hIK
  have hpc : ∀ r ∈ Set.Ioo (r₀ - w / 2) (r₀ + w / 2), pcGlobal d r = M.pc r :=
    fun r hr => pcGlobal_eq_pc hd M (hKM (hIoo hr))
  obtain ⟨ρ₀, hρ₀0, What, hWhat⟩ := krrs_strip hd M hKM hKc hKne hKex H hreg hm
  obtain ⟨ηK, hηK0, -, hηK⟩ := arc_uniform_bounds M hKM hKc hKne
  refine ⟨ρ₀, r₀ - w / 2, r₀ + w / 2, hρ₀0, by linarith, by linarith, ?_, ?_, ?_⟩
  · -- `[lo, hi] ⊆ (0,1) ∖ {r_*}`
    intro r hr
    obtain ⟨hpc0, hpcr, hr1, -⟩ := M.ordering r (hKM (hIK hr))
    exact ⟨⟨lt_trans hpc0 hpcr, hr1⟩, hKex r (hIK hr)⟩
  · -- the maximizer `B_{ε,r^m}` and `eq:reduced-objective-attainment`
    intro r hr ε hε
    obtain ⟨he, ht, hbip, hmax, huniq⟩ := hWhat r (hIoo hr) ε hε
    have hne : ∃ W : Graphon, W.edgeDensity = ε ∧ W.tDensity H = r ^ H.edgeFinset.card :=
      ⟨What ε r, he, ht⟩
    refine ⟨What ε r, he, ht, hmax, huniq, hbip, ?_, fun p hp0 hp1 => ?_⟩
    · rw [entropyEnvelope_eq_coe H hne, entropyEnvelope_eq_of_isMax H he ht hmax]
    · rw [reducedObjective_eq_coe H hne, reducedObjective_eq_Ip H hp0 hp1 he ht hmax]
  · -- the localization clause
    intro ρ hρ0 _
    obtain ⟨ηloc, hηloc0, hloc⟩ := uniform_localization hd M H hreg hm hKM hKc hKne hρ0
    have hηinf : ηK ≤ sInf (pcGlobal d '' Set.Ioo (r₀ - w / 2) (r₀ + w / 2)) := by
      refine le_csInf ⟨pcGlobal d r₀, r₀, ⟨by linarith, by linarith⟩, rfl⟩ ?_
      rintro _ ⟨r, hr, rfl⟩
      rw [hpc r hr]
      exact (hηK r (hIoo hr)).2.2.2.2.1
    have hηle : min ηloc (ηK / 2) ≤ ηloc := min_le_left _ _
    have hηle' : min ηloc (ηK / 2) ≤ ηK / 2 := min_le_right _ _
    refine ⟨min ηloc (ηK / 2), lt_min hηloc0 (by linarith), by linarith, ?_⟩
    intro r hr p hlo hhi W hWfeas hWopt
    rw [hpc r hr] at hlo hhi
    exact hloc r (hIoo hr) p (by linarith) hhi W hWfeas hWopt

end UpperTailOptimizers
