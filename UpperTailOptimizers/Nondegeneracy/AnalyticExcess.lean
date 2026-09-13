import UpperTailOptimizers.Nondegeneracy.AnalyticTools

/-!
# The full `thm:positive-second-variation`: the analytic second variation `A_H`

This file completes Section 5 of `paper/bipodal_optimizer.tex` by proving its **`thm:positive-second-variation`**
(`thm:positive-second-variation`, "Universal positivity of the scalar second variation",
eq. `G-quadratic-paper`): uniformly for `r` in a compact subarc `K`,

`G_r(δ) = ½ A_H(r) δ² + O_K(δ³)`,

where the coefficient `A_H` is **real-analytic** and **uniformly positive** on `K`.

The quantitative two-sided bound `C δ² ≤ G_r(δ) ≤ C' δ²` was established in
`Nondegeneracy/BoundaryExcess.lean` without any Kenyon–Radin–Ren–Sadun input.  The
missing analytic structure enters through `kenyonRadinRenSadunAnalytic`
(the analytic-parametrization clause of the paper's `thm:krrs-analytic-extension`, itself proved in
`KRRS/Main.lean`, with the Kenyon–Radin–Ren–Sadun theorems it uses proved in `KRRS/Psi*` and
`Bipodality/`): near each
`r₀ ∈ K` the entropy envelope, hence the boundary excess, agrees for `0 < δ` small
with the **chart function**

`Gc(r, δ) = -Σ(ε, t) - log(1 - pc r) + ε log((1-pc r)/pc r) - J_{pc r}(r)`,

`ε = r - δ`, `t = r^m - ε^m`, where `Σ` is the bipodal entropy formula composed with
the analytic KRRS parameter maps — a function jointly analytic near `(r₀, 0)`.

The second-variation coefficient is *defined* chart-independently as the right limit

`AH H M r = lim_{δ ↓ 0} 2 G_r(δ)/δ²` (`limUnder`),

and each chart identifies it with the analytic function `r ↦ ∂²_δ Gc(r, 0)`
(`limUnder_cubic`), which yields analyticity; positivity `AH ≥ 2C` follows from the
quantitative lower bound.  The cubic remainder is uniform on `K` by a finite cover of
charts.  The headline theorem is `boundaryExcess_taylor`.

The chart is exported in two forms: `boundaryExcess_chart_full`, which carries everything
Section 6 consumes (including the four Kenyon–Radin–Ren–Sadun parameter maps), and its
trimmed form `boundaryExcess_chart`, which carries only the clauses about `Gc`:
analyticity of `Gc` and of its `δ`-derivative on a **two-sided** box in `δ`, the boundary
values `Gc(r,0) = ∂_δ Gc(r,0) = 0` and `∂²_δ Gc(r,0) = A_H(r)`, and the two-sided Lipschitz
bound `|∂²_δ Gc(r,δ) - A_H(r)| ≤ Mc |δ|` (the paper's `G_r''(δ) = A_H(r) + O_K(|δ|)`).
-/

namespace UpperTailOptimizers

open MeasureTheory Real Set Filter Topology

/-- **The second-variation coefficient `A_H`** of the boundary excess (`thm:positive-second-variation`):
the right limit `A_H(r) = lim_{δ↓0} 2 G_r(δ)/δ²`.  This definition is global and
chart-independent; on a Lubetzky–Zhao boundary arc it agrees with `∂²_δ` of the analytic extension
of `G_r` (`boundaryExcess_taylor`). -/
noncomputable def AH {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] {d : ℕ} (M : LZBoundaryArc d) (r : ℝ) : ℝ :=
  limUnder (𝓝[>] (0:ℝ)) (fun δ => 2 * boundaryExcess H M r δ / δ ^ 2)

/-- **The local analytic chart of the boundary excess, full form.**  Near each non-exceptional
`r₀` of the arc there are a radius `w`, a `δ`-range `ρ`, a cubic constant `Mc`, a function
`Gc : ℝ × ℝ → ℝ`, **analytic on the whole two-sided box** `|r - r₀| < w`, `|δ| ≤ ρ`, and the
four Kenyon–Radin–Ren–Sadun parameter maps `q₁₁, q₁₂, q₂₂, c` of that chart, with:

* `Gc(r, δ) = G_r(δ)` on the Kenyon–Radin–Ren–Sadun regime `0 < δ < ρ`
  (one-sided: the regime needs a strictly positive `H`-density surplus);
* the degenerate boundary values `Gc(r,0) = 0`, `∂_δ Gc(r,0) = 0`,
  `∂²_δ Gc(r,0) = A_H(r)`;
* the **two-sided** Lipschitz control `|∂²_δ Gc(r,δ) - A_H(r)| ≤ Mc |δ|`, i.e. the paper's
  `G_r''(δ) = A_H(r) + O_K(|δ|)`;
* the cubic Taylor bound `|G_r(δ) - A_H(r) δ²/2| ≤ Mc δ³`;
* joint analyticity, in `(r, δ)`, of the four parameter maps evaluated at the chart
  substitution `(ε, τ - ε^m) = (r - δ, r^m - (r-δ)^m)`, their interior values, their
  degenerate boundary values `c(r,0) = 0`, `q₂₂(r,0) = r`, `q₁₂(r,0) ≠ r`, and — on the
  Kenyon–Radin–Ren–Sadun regime — the fact that the concrete two-block graphon they describe
  **is** the fixed-`(e, t_H)` entropy maximizer.

This is the chart form of `thm:positive-second-variation`; the two-sided clauses are what Section 6 needs (the
critical point `δ_*(p,r)` of the tilted objective must be located by an implicit function
theorem in a full neighbourhood of `δ = 0`, and its sign read off from a mean value estimate),
and the parameter clauses are what the "Furthermore" clause of `thm:local-optimizer-structure` and `rmk:bipodal-parameter-expansions`
need.  The trimmed form used by the Section-5 consumers is `boundaryExcess_chart`. -/
theorem boundaryExcess_chart_full {d : ℕ} (hd : 2 ≤ d) (M : LZBoundaryArc d)
    {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (hreg : ∀ v, H.degree v = d) (hm : 1 ≤ H.edgeFinset.card)
    {r₀ : ℝ} (hr₀U : r₀ ∈ M.U) (hr₀ex : r₀ ≠ rStar d) :
    ∃ w ρ Mc : ℝ, 0 < w ∧ 0 < ρ ∧ 0 ≤ Mc ∧
      ∃ (Gc : ℝ × ℝ → ℝ) (q11 q12 q22 cc : ℝ → ℝ → ℝ),
      (∀ r δ : ℝ, |r - r₀| < w → |δ| ≤ ρ → AnalyticAt ℝ Gc (r, δ)) ∧
      (∀ r δ : ℝ, |r - r₀| < w → |δ| ≤ ρ → AnalyticAt ℝ (dDelta Gc) (r, δ)) ∧
      (∀ r δ : ℝ, |r - r₀| < w → 0 < δ → δ < ρ → boundaryExcess H M r δ = Gc (r, δ)) ∧
      (∀ r : ℝ, |r - r₀| < w → Gc (r, 0) = 0) ∧
      (∀ r : ℝ, |r - r₀| < w → dDelta Gc (r, 0) = 0) ∧
      (∀ r : ℝ, |r - r₀| < w → dDelta (dDelta Gc) (r, 0) = AH H M r) ∧
      (∀ r δ : ℝ, |r - r₀| < w → |δ| ≤ ρ →
        |dDelta (dDelta Gc) (r, δ) - AH H M r| ≤ Mc * |δ|) ∧
      (∀ r δ : ℝ, |r - r₀| < w → 0 < δ → δ < ρ →
        |boundaryExcess H M r δ - AH H M r * δ ^ 2 / 2| ≤ Mc * δ ^ 3) ∧
      (∀ r δ : ℝ, |r - r₀| < w → |δ| ≤ ρ →
        AnalyticAt ℝ (fun x : ℝ × ℝ => q11 (x.1 - x.2)
          (x.1 ^ H.edgeFinset.card - (x.1 - x.2) ^ H.edgeFinset.card)) (r, δ) ∧
        AnalyticAt ℝ (fun x : ℝ × ℝ => q12 (x.1 - x.2)
          (x.1 ^ H.edgeFinset.card - (x.1 - x.2) ^ H.edgeFinset.card)) (r, δ) ∧
        AnalyticAt ℝ (fun x : ℝ × ℝ => q22 (x.1 - x.2)
          (x.1 ^ H.edgeFinset.card - (x.1 - x.2) ^ H.edgeFinset.card)) (r, δ) ∧
        AnalyticAt ℝ (fun x : ℝ × ℝ => cc (x.1 - x.2)
          (x.1 ^ H.edgeFinset.card - (x.1 - x.2) ^ H.edgeFinset.card)) (r, δ)) ∧
      (∀ r δ : ℝ, |r - r₀| < w → |δ| ≤ ρ →
        q11 (r - δ) (r ^ H.edgeFinset.card - (r - δ) ^ H.edgeFinset.card)
            ∈ Set.Ioo (0:ℝ) 1 ∧
        q12 (r - δ) (r ^ H.edgeFinset.card - (r - δ) ^ H.edgeFinset.card)
            ∈ Set.Ioo (0:ℝ) 1 ∧
        q22 (r - δ) (r ^ H.edgeFinset.card - (r - δ) ^ H.edgeFinset.card)
            ∈ Set.Ioo (0:ℝ) 1) ∧
      (∀ r : ℝ, |r - r₀| < w →
        cc r 0 = 0 ∧ q22 r 0 = r ∧ q11 r 0 ∈ Set.Ioo (0:ℝ) 1 ∧
        q12 r 0 ∈ Set.Ioo (0:ℝ) 1 ∧ q12 r 0 ≠ r) ∧
      (∀ r δ : ℝ, |r - r₀| < w → 0 < δ → δ < ρ →
        cc (r - δ) (r ^ H.edgeFinset.card - (r - δ) ^ H.edgeFinset.card)
            ∈ Set.Icc (0:ℝ) 1 ∧
        ∃ W : Graphon, W.edgeDensity = r - δ ∧
          W.tDensity H = r ^ H.edgeFinset.card ∧
          (∀ W' : Graphon, W'.edgeDensity = r - δ →
            W'.tDensity H = r ^ H.edgeFinset.card → W'.entropy ≤ W.entropy) ∧
          (∀ᵐ z ∂gμ, W.toFun z.1 z.2 = bipodalValue
            (Set.Icc 0 (cc (r - δ)
              (r ^ H.edgeFinset.card - (r - δ) ^ H.edgeFinset.card)))
            (q11 (r - δ) (r ^ H.edgeFinset.card - (r - δ) ^ H.edgeFinset.card))
            (q12 (r - δ) (r ^ H.edgeFinset.card - (r - δ) ^ H.edgeFinset.card))
            (q22 (r - δ) (r ^ H.edgeFinset.card - (r - δ) ^ H.edgeFinset.card)) z)) := by
  classical
  obtain ⟨hpc0, hpcr, hr₀1, _, _, _⟩ := M.ordering r₀ hr₀U
  have hr₀0 : 0 < r₀ := lt_trans hpc0 hpcr
  obtain ⟨U, Δ, q11, q12, q22, cc, hUopen, hr₀mem, hΔ0, hana, hbdry, hmaxi⟩ :=
    kenyonRadinRenSadunAnalytic H hd hreg (two_le_card_edgeFinset H hd hreg hm) hr₀0 hr₀1 hr₀ex
  have hm0 : H.edgeFinset.card ≠ 0 := by omega
  have hmR : (1:ℝ) ≤ (H.edgeFinset.card : ℝ) := by exact_mod_cast hm
  -- ### The chart function
  set em : ℝ × ℝ → ℝ × ℝ :=
    fun p => (p.1 - p.2, p.1 ^ H.edgeFinset.card - (p.1 - p.2) ^ H.edgeFinset.card)
    with hem_def
  set SB : ℝ × ℝ → ℝ := fun p =>
    shannonH (q11 (em p).1 (em p).2) * (cc (em p).1 (em p).2) ^ 2
    + shannonH (q12 (em p).1 (em p).2)
      * (2 * (cc (em p).1 (em p).2) * (1 - cc (em p).1 (em p).2))
    + shannonH (q22 (em p).1 (em p).2) * (1 - cc (em p).1 (em p).2) ^ 2 with hSB_def
  set Gc : ℝ × ℝ → ℝ := fun p =>
    -SB p - Real.log (1 - M.pc p.1)
      + (p.1 - p.2) * Real.log ((1 - M.pc p.1) / M.pc p.1)
      - Jp (M.pc p.1) p.1 with hGc_def
  -- ### The good neighbourhood of `(r₀, 0)`
  have hem_cont : Continuous em := by
    rw [hem_def]
    fun_prop
  have hem_base : em (r₀, 0) = (r₀, 0) := by
    rw [hem_def]
    simp
  -- the composed parameter maps are analytic and interior at `(r₀,0)`, eventually
  obtain ⟨ha11, ha12, ha22, hacc⟩ := hana r₀ hr₀mem
  obtain ⟨hcc0, hq220, hq110, hq120, _⟩ := hbdry r₀ hr₀mem
  have hEv : ∀ᶠ p : ℝ × ℝ in 𝓝 (r₀, 0),
      (AnalyticAt ℝ (fun x : ℝ × ℝ => q11 x.1 x.2) (em p)
        ∧ AnalyticAt ℝ (fun x : ℝ × ℝ => q12 x.1 x.2) (em p)
        ∧ AnalyticAt ℝ (fun x : ℝ × ℝ => q22 x.1 x.2) (em p)
        ∧ AnalyticAt ℝ (fun x : ℝ × ℝ => cc x.1 x.2) (em p))
      ∧ (q11 (em p).1 (em p).2 ∈ Set.Ioo (0:ℝ) 1
        ∧ q12 (em p).1 (em p).2 ∈ Set.Ioo (0:ℝ) 1
        ∧ q22 (em p).1 (em p).2 ∈ Set.Ioo (0:ℝ) 1)
      ∧ (p.1 ∈ M.U ∧ p.1 ∈ U ∧ M.pc p.1 ∈ Set.Ioo (0:ℝ) 1 ∧ p.1 ∈ Set.Ioo (0:ℝ) 1) := by
    have hcAt : ContinuousAt em (r₀, 0) := hem_cont.continuousAt
    -- analyticity sets are open; pull back along `em`
    have e11 : ∀ᶠ p : ℝ × ℝ in 𝓝 (r₀, 0),
        AnalyticAt ℝ (fun x : ℝ × ℝ => q11 x.1 x.2) (em p) := by
      have h1 : {x : ℝ × ℝ | AnalyticAt ℝ (fun x : ℝ × ℝ => q11 x.1 x.2) x}
          ∈ 𝓝 (em (r₀, 0)) := by
        rw [hem_base]
        exact (isOpen_analyticAt ℝ _).mem_nhds ha11
      filter_upwards [hcAt.preimage_mem_nhds h1] with p hp using hp
    have e12 : ∀ᶠ p : ℝ × ℝ in 𝓝 (r₀, 0),
        AnalyticAt ℝ (fun x : ℝ × ℝ => q12 x.1 x.2) (em p) := by
      have h1 : {x : ℝ × ℝ | AnalyticAt ℝ (fun x : ℝ × ℝ => q12 x.1 x.2) x}
          ∈ 𝓝 (em (r₀, 0)) := by
        rw [hem_base]
        exact (isOpen_analyticAt ℝ _).mem_nhds ha12
      filter_upwards [hcAt.preimage_mem_nhds h1] with p hp using hp
    have e22 : ∀ᶠ p : ℝ × ℝ in 𝓝 (r₀, 0),
        AnalyticAt ℝ (fun x : ℝ × ℝ => q22 x.1 x.2) (em p) := by
      have h1 : {x : ℝ × ℝ | AnalyticAt ℝ (fun x : ℝ × ℝ => q22 x.1 x.2) x}
          ∈ 𝓝 (em (r₀, 0)) := by
        rw [hem_base]
        exact (isOpen_analyticAt ℝ _).mem_nhds ha22
      filter_upwards [hcAt.preimage_mem_nhds h1] with p hp using hp
    have ecc : ∀ᶠ p : ℝ × ℝ in 𝓝 (r₀, 0),
        AnalyticAt ℝ (fun x : ℝ × ℝ => cc x.1 x.2) (em p) := by
      have h1 : {x : ℝ × ℝ | AnalyticAt ℝ (fun x : ℝ × ℝ => cc x.1 x.2) x}
          ∈ 𝓝 (em (r₀, 0)) := by
        rw [hem_base]
        exact (isOpen_analyticAt ℝ _).mem_nhds hacc
      filter_upwards [hcAt.preimage_mem_nhds h1] with p hp using hp
    -- interior values, by continuity of the composed parameter maps
    have hq11cont : ContinuousAt (fun p : ℝ × ℝ => q11 (em p).1 (em p).2) (r₀, 0) := by
      have h1 : ContinuousAt (fun x : ℝ × ℝ => q11 x.1 x.2) (em (r₀, 0)) := by
        rw [hem_base]; exact ha11.continuousAt
      exact h1.comp hcAt
    have hq12cont : ContinuousAt (fun p : ℝ × ℝ => q12 (em p).1 (em p).2) (r₀, 0) := by
      have h1 : ContinuousAt (fun x : ℝ × ℝ => q12 x.1 x.2) (em (r₀, 0)) := by
        rw [hem_base]; exact ha12.continuousAt
      exact h1.comp hcAt
    have hq22cont : ContinuousAt (fun p : ℝ × ℝ => q22 (em p).1 (em p).2) (r₀, 0) := by
      have h1 : ContinuousAt (fun x : ℝ × ℝ => q22 x.1 x.2) (em (r₀, 0)) := by
        rw [hem_base]; exact ha22.continuousAt
      exact h1.comp hcAt
    have v11 : ∀ᶠ p : ℝ × ℝ in 𝓝 (r₀, 0), q11 (em p).1 (em p).2 ∈ Set.Ioo (0:ℝ) 1 := by
      refine hq11cont.preimage_mem_nhds (isOpen_Ioo.mem_nhds ?_)
      rw [hem_base]
      exact hq110
    have v12 : ∀ᶠ p : ℝ × ℝ in 𝓝 (r₀, 0), q12 (em p).1 (em p).2 ∈ Set.Ioo (0:ℝ) 1 := by
      refine hq12cont.preimage_mem_nhds (isOpen_Ioo.mem_nhds ?_)
      rw [hem_base]
      exact hq120
    have v22 : ∀ᶠ p : ℝ × ℝ in 𝓝 (r₀, 0), q22 (em p).1 (em p).2 ∈ Set.Ioo (0:ℝ) 1 := by
      refine hq22cont.preimage_mem_nhds (isOpen_Ioo.mem_nhds ?_)
      rw [hem_base]
      rw [hq220]
      exact ⟨hr₀0, hr₀1⟩
    -- first-coordinate conditions
    have w1 : ∀ᶠ p : ℝ × ℝ in 𝓝 (r₀, 0), p.1 ∈ M.U :=
      continuousAt_fst.preimage_mem_nhds (M.isOpen_U.mem_nhds hr₀U)
    have w2 : ∀ᶠ p : ℝ × ℝ in 𝓝 (r₀, 0), p.1 ∈ U :=
      continuousAt_fst.preimage_mem_nhds (hUopen.mem_nhds hr₀mem)
    have w3 : ∀ᶠ p : ℝ × ℝ in 𝓝 (r₀, 0), M.pc p.1 ∈ Set.Ioo (0:ℝ) 1 := by
      have hpcCont : ContinuousAt (fun p : ℝ × ℝ => M.pc p.1) (r₀, 0) :=
        ((M.analytic_pc r₀ hr₀U).continuousAt).comp continuousAt_fst
      refine hpcCont.preimage_mem_nhds (isOpen_Ioo.mem_nhds ?_)
      exact ⟨hpc0, lt_trans hpcr hr₀1⟩
    have w4 : ∀ᶠ p : ℝ × ℝ in 𝓝 (r₀, 0), p.1 ∈ Set.Ioo (0:ℝ) 1 :=
      continuousAt_fst.preimage_mem_nhds (isOpen_Ioo.mem_nhds ⟨hr₀0, hr₀1⟩)
    filter_upwards [e11, e12, e22, ecc, v11, v12, v22, w1, w2, w3, w4] with
      p h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
    exact ⟨⟨h1, h2, h3, h4⟩, ⟨h5, h6, h7⟩, ⟨h8, h9, h10, h11⟩⟩
  obtain ⟨εA, hεA0, hball⟩ := Metric.eventually_nhds_iff_ball.mp hEv
  -- ### Analyticity of the chart function on the good ball
  have hGcAt : ∀ p ∈ Metric.ball ((r₀, 0) : ℝ × ℝ) εA, AnalyticAt ℝ Gc p := by
    intro p hp
    obtain ⟨⟨h11, h12, h22, hc⟩, ⟨v11, v12, v22⟩, hU1, _, hpc, hp1⟩ := hball p hp
    have hemA : AnalyticAt ℝ em p := by
      rw [hem_def]
      exact (analyticAt_fst.sub analyticAt_snd).prod
        ((analyticAt_fst.pow _).sub ((analyticAt_fst.sub analyticAt_snd).pow _))
    have hq11c : AnalyticAt ℝ (fun p => q11 (em p).1 (em p).2) p := h11.comp hemA
    have hq12c : AnalyticAt ℝ (fun p => q12 (em p).1 (em p).2) p := h12.comp hemA
    have hq22c : AnalyticAt ℝ (fun p => q22 (em p).1 (em p).2) p := h22.comp hemA
    have hccc : AnalyticAt ℝ (fun p => cc (em p).1 (em p).2) p := hc.comp hemA
    have hH11 : AnalyticAt ℝ (fun p => shannonH (q11 (em p).1 (em p).2)) p :=
      (analyticAt_shannonH v11.1 v11.2).comp
        (f := fun p => q11 (em p).1 (em p).2) hq11c
    have hH12 : AnalyticAt ℝ (fun p => shannonH (q12 (em p).1 (em p).2)) p :=
      (analyticAt_shannonH v12.1 v12.2).comp
        (f := fun p => q12 (em p).1 (em p).2) hq12c
    have hH22 : AnalyticAt ℝ (fun p => shannonH (q22 (em p).1 (em p).2)) p :=
      (analyticAt_shannonH v22.1 v22.2).comp
        (f := fun p => q22 (em p).1 (em p).2) hq22c
    have hSBA : AnalyticAt ℝ SB p := by
      rw [hSB_def]
      exact ((hH11.mul (hccc.pow 2)).add
        (hH12.mul (((analyticAt_const.mul hccc)).mul (analyticAt_const.sub hccc)))).add
        (hH22.mul ((analyticAt_const.sub hccc).pow 2))
    have hpcA : AnalyticAt ℝ (fun p : ℝ × ℝ => M.pc p.1) p :=
      (M.analytic_pc p.1 hU1).comp analyticAt_fst
    have hlog1 : AnalyticAt ℝ (fun p : ℝ × ℝ => Real.log (1 - M.pc p.1)) p :=
      analyticAt_log_comp (analyticAt_const.sub hpcA) (by linarith [hpc.2])
    have hlog2 : AnalyticAt ℝ
        (fun p : ℝ × ℝ => Real.log ((1 - M.pc p.1) / M.pc p.1)) p := by
      refine analyticAt_log_comp ((analyticAt_const.sub hpcA).div hpcA (ne_of_gt hpc.1)) ?_
      have h1 : (0:ℝ) < 1 - M.pc p.1 := by linarith [hpc.2]
      exact div_pos h1 hpc.1
    have hJpA : AnalyticAt ℝ (fun p : ℝ × ℝ => Jp (M.pc p.1) p.1) p := by
      have hform : (fun p : ℝ × ℝ => Jp (M.pc p.1) p.1)
          = fun p : ℝ × ℝ => p.1 * Real.log (p.1 / M.pc p.1)
            + (1 - p.1) * Real.log ((1 - p.1) / (1 - M.pc p.1)) := rfl
      rw [hform]
      have hl1 : AnalyticAt ℝ (fun p : ℝ × ℝ => Real.log (p.1 / M.pc p.1)) p := by
        refine analyticAt_log_comp (analyticAt_fst.div hpcA (ne_of_gt hpc.1)) ?_
        exact div_pos hp1.1 hpc.1
      have hl2 : AnalyticAt ℝ
          (fun p : ℝ × ℝ => Real.log ((1 - p.1) / (1 - M.pc p.1))) p := by
        refine analyticAt_log_comp
          ((analyticAt_const.sub analyticAt_fst).div (analyticAt_const.sub hpcA)
            (by linarith [hpc.2] : (1:ℝ) - M.pc p.1 ≠ 0)) ?_
        have h1 : (0:ℝ) < 1 - p.1 := by linarith [hp1.2]
        have h2 : (0:ℝ) < 1 - M.pc p.1 := by linarith [hpc.2]
        exact div_pos h1 h2
      exact (analyticAt_fst.mul hl1).add ((analyticAt_const.sub analyticAt_fst).mul hl2)
    rw [hGc_def]
    exact ((hSBA.neg.sub hlog1).add
      ((analyticAt_fst.sub analyticAt_snd).mul hlog2)).sub hJpA
  -- ### The composed Kenyon–Radin–Ren–Sadun parameter maps, in explicit `(r, δ)` form
  have hqA : ∀ p ∈ Metric.ball ((r₀, 0) : ℝ × ℝ) εA,
      AnalyticAt ℝ (fun x : ℝ × ℝ => q11 (x.1 - x.2)
        (x.1 ^ H.edgeFinset.card - (x.1 - x.2) ^ H.edgeFinset.card)) p ∧
      AnalyticAt ℝ (fun x : ℝ × ℝ => q12 (x.1 - x.2)
        (x.1 ^ H.edgeFinset.card - (x.1 - x.2) ^ H.edgeFinset.card)) p ∧
      AnalyticAt ℝ (fun x : ℝ × ℝ => q22 (x.1 - x.2)
        (x.1 ^ H.edgeFinset.card - (x.1 - x.2) ^ H.edgeFinset.card)) p ∧
      AnalyticAt ℝ (fun x : ℝ × ℝ => cc (x.1 - x.2)
        (x.1 ^ H.edgeFinset.card - (x.1 - x.2) ^ H.edgeFinset.card)) p := by
    intro p hp
    obtain ⟨⟨h11, h12, h22, hc⟩, -, -⟩ := hball p hp
    have hemA : AnalyticAt ℝ em p := by
      rw [hem_def]
      exact (analyticAt_fst.sub analyticAt_snd).prod
        ((analyticAt_fst.pow _).sub ((analyticAt_fst.sub analyticAt_snd).pow _))
    exact ⟨h11.comp hemA, h12.comp hemA, h22.comp hemA, hc.comp hemA⟩
  -- ### Radii
  obtain ⟨uU, huU0, huUsub⟩ := Metric.isOpen_iff.mp hUopen r₀ hr₀mem
  set rad : ℝ := εA / 2 with hrad_def
  have hrad0 : 0 < rad := by rw [hrad_def]; linarith
  set w : ℝ := min (rad / 2) (min (uU / 4) (min (r₀ / 2) ((1 - r₀) / 2))) with hw_def
  have hw0 : 0 < w := by
    rw [hw_def]
    have h1 : (0:ℝ) < (1 - r₀) / 2 := by linarith
    exact lt_min (by linarith) (lt_min (by linarith) (lt_min (by linarith) h1))
  set ρ : ℝ := min (rad / 2)
      (min (uU / 4) (min (Δ / ((H.edgeFinset.card : ℝ) + 1)) (r₀ / 2))) with hρ_def
  have hρ0 : 0 < ρ := by
    rw [hρ_def]
    have h1 : (0:ℝ) < Δ / ((H.edgeFinset.card : ℝ) + 1) := by positivity
    exact lt_min (by linarith) (lt_min (by linarith) (lt_min h1 (by linarith)))
  have hwrad : w ≤ rad / 2 := by rw [hw_def]; exact min_le_left _ _
  have hwuU : w ≤ uU / 4 := by
    rw [hw_def]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hwr₀ : w ≤ r₀ / 2 := by
    rw [hw_def]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hw1r₀ : w ≤ (1 - r₀) / 2 := by
    rw [hw_def]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  have hρrad : ρ ≤ rad / 2 := by rw [hρ_def]; exact min_le_left _ _
  have hρuU : ρ ≤ uU / 4 := by
    rw [hρ_def]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hρΔ : ρ ≤ Δ / ((H.edgeFinset.card : ℝ) + 1) := by
    rw [hρ_def]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hρr₀ : ρ ≤ r₀ / 2 := by
    rw [hρ_def]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  -- ball membership helpers
  have hmemball : ∀ r t : ℝ, |r - r₀| < w → |t| ≤ ρ →
      ((r, t) : ℝ × ℝ) ∈ Metric.ball ((r₀, 0) : ℝ × ℝ) εA := by
    intro r t hr ht
    rw [Metric.mem_ball, Prod.dist_eq]
    have h1 : dist r r₀ < εA := by
      rw [Real.dist_eq]
      calc |r - r₀| < w := hr
        _ ≤ rad / 2 := hwrad
        _ < εA := by rw [hrad_def]; linarith
    have h2 : dist t 0 < εA := by
      rw [Real.dist_eq, sub_zero]
      calc |t| ≤ ρ := ht
        _ ≤ rad / 2 := hρrad
        _ < εA := by rw [hrad_def]; linarith
    exact max_lt h1 h2
  have hmemcb : ∀ r t : ℝ, |r - r₀| < w → |t| ≤ ρ →
      ((r, t) : ℝ × ℝ) ∈ Metric.closedBall ((r₀, 0) : ℝ × ℝ) rad := by
    intro r t hr ht
    rw [Metric.mem_closedBall, Prod.dist_eq]
    have h1 : dist r r₀ ≤ rad := by
      rw [Real.dist_eq]
      calc |r - r₀| ≤ w := hr.le
        _ ≤ rad / 2 := hwrad
        _ ≤ rad := by linarith
    have h2 : dist t 0 ≤ rad := by
      rw [Real.dist_eq, sub_zero]
      calc |t| ≤ ρ := ht
        _ ≤ rad / 2 := hρrad
        _ ≤ rad := by linarith
    exact max_le h1 h2
  have hcbsub : Metric.closedBall ((r₀, 0) : ℝ × ℝ) rad
      ⊆ Metric.ball ((r₀, 0) : ℝ × ℝ) εA := by
    refine Metric.closedBall_subset_ball ?_
    rw [hrad_def]; linarith
  -- ### The nested `δ`-derivatives and the cubic constant
  set F1 : ℝ × ℝ → ℝ := dDelta Gc with hF1_def
  set F2 : ℝ × ℝ → ℝ := dDelta F1 with hF2_def
  set F3 : ℝ × ℝ → ℝ := dDelta F2 with hF3_def
  have hF1At : ∀ p ∈ Metric.ball ((r₀, 0) : ℝ × ℝ) εA, AnalyticAt ℝ F1 p := by
    intro p hp
    rw [hF1_def]
    exact analyticAt_dDelta (hGcAt p hp)
  have hF2At : ∀ p ∈ Metric.ball ((r₀, 0) : ℝ × ℝ) εA, AnalyticAt ℝ F2 p := by
    intro p hp
    rw [hF2_def]
    exact analyticAt_dDelta (hF1At p hp)
  have hF3At : ∀ p ∈ Metric.ball ((r₀, 0) : ℝ × ℝ) εA, AnalyticAt ℝ F3 p := by
    intro p hp
    rw [hF3_def]
    exact analyticAt_dDelta (hF2At p hp)
  obtain ⟨Mc₀, hMc₀⟩ := (isCompact_closedBall ((r₀, 0) : ℝ × ℝ) rad).exists_bound_of_continuousOn
    (fun p hp => ((hF3At p (hcbsub hp)).continuousAt).continuousWithinAt)
  set Mc : ℝ := max Mc₀ 0 with hMc_def
  have hMc0 : 0 ≤ Mc := by rw [hMc_def]; exact le_max_right _ _
  have hMcB : ∀ p ∈ Metric.closedBall ((r₀, 0) : ℝ × ℝ) rad, |F3 p| ≤ Mc := by
    intro p hp
    have := hMc₀ p hp
    rw [Real.norm_eq_abs] at this
    rw [hMc_def]
    exact le_trans this (le_max_left _ _)
  -- ### The Kenyon–Radin–Ren–Sadun regime: location facts
  have hloc : ∀ r : ℝ, |r - r₀| < w → ∀ δ : ℝ, 0 < δ → δ < ρ →
      0 < r ∧ r < 1 ∧ 0 < r - δ ∧ r - δ < 1 ∧ r - δ ∈ U ∧
      0 < r ^ H.edgeFinset.card - (r - δ) ^ H.edgeFinset.card ∧
      r ^ H.edgeFinset.card - (r - δ) ^ H.edgeFinset.card < Δ := by
    intro r hr δ hδ0 hδρ
    have hrlow : r₀ / 2 < r := by
      have h1 : |r - r₀| < r₀ / 2 := lt_of_lt_of_le hr hwr₀
      have h2 := abs_lt.mp h1
      linarith [h2.1]
    have hrhigh : r < 1 := by
      have h1 : |r - r₀| < (1 - r₀) / 2 := lt_of_lt_of_le hr hw1r₀
      have h2 := abs_lt.mp h1
      linarith [h2.2]
    have hr0 : 0 < r := lt_trans (by linarith) hrlow
    have hδr : δ < r := lt_of_lt_of_le hδρ (le_trans hρr₀ (by linarith))
    have hε0 : 0 < r - δ := by linarith
    have hε1 : r - δ < 1 := by linarith
    have hεU : r - δ ∈ U := by
      refine huUsub ?_
      rw [Metric.mem_ball, Real.dist_eq]
      have h1 : |r - r₀| < uU / 4 := lt_of_lt_of_le hr hwuU
      have h2 : δ < uU / 4 := lt_of_lt_of_le hδρ hρuU
      have h3 := abs_lt.mp h1
      rw [abs_lt]
      constructor <;> linarith [h3.1, h3.2]
    -- the H-density surplus
    have ht0 : 0 < r ^ H.edgeFinset.card - (r - δ) ^ H.edgeFinset.card := by
      have := pow_lt_pow_left₀ (by linarith : r - δ < r) hε0.le hm0
      linarith
    have htΔ : r ^ H.edgeFinset.card - (r - δ) ^ H.edgeFinset.card < Δ := by
      have h1 : |r ^ H.edgeFinset.card - (r - δ) ^ H.edgeFinset.card|
          ≤ (H.edgeFinset.card : ℝ) * |r - (r - δ)| :=
        abs_pow_sub_pow_le ⟨hr0.le, hrhigh.le⟩ ⟨hε0.le, hε1.le⟩ _
      have h2 : |r - (r - δ)| = δ := by
        rw [show r - (r - δ) = δ by ring, abs_of_pos hδ0]
      rw [h2] at h1
      have h3 : |r ^ H.edgeFinset.card - (r - δ) ^ H.edgeFinset.card|
          = r ^ H.edgeFinset.card - (r - δ) ^ H.edgeFinset.card := abs_of_pos ht0
      have h4 : δ < Δ / ((H.edgeFinset.card : ℝ) + 1) := lt_of_lt_of_le hδρ hρΔ
      have h5 : (H.edgeFinset.card : ℝ) * δ < Δ := by
        have h6 : (H.edgeFinset.card : ℝ) * δ
            < (H.edgeFinset.card : ℝ) * (Δ / ((H.edgeFinset.card : ℝ) + 1)) := by
          exact mul_lt_mul_of_pos_left h4 (by linarith)
        have h7 : (H.edgeFinset.card : ℝ) * (Δ / ((H.edgeFinset.card : ℝ) + 1)) < Δ := by
          have hpos : (0:ℝ) < (H.edgeFinset.card : ℝ) + 1 := by linarith
          rw [show (H.edgeFinset.card : ℝ) * (Δ / ((H.edgeFinset.card : ℝ) + 1))
              = (H.edgeFinset.card : ℝ) * Δ / ((H.edgeFinset.card : ℝ) + 1) from by ring,
            div_lt_iff₀ hpos]
          nlinarith [hΔ0]
        linarith
      linarith [h3 ▸ h1]
    exact ⟨hr0, hrhigh, hε0, hε1, hεU, ht0, htΔ⟩
  -- ### The concrete Kenyon–Radin–Ren–Sadun maximizer on the regime
  have hmax : ∀ r : ℝ, |r - r₀| < w → ∀ δ : ℝ, 0 < δ → δ < ρ →
      q11 (r - δ) (r ^ H.edgeFinset.card - (r - δ) ^ H.edgeFinset.card) ∈ Set.Icc (0:ℝ) 1 ∧
      q12 (r - δ) (r ^ H.edgeFinset.card - (r - δ) ^ H.edgeFinset.card) ∈ Set.Icc (0:ℝ) 1 ∧
      q22 (r - δ) (r ^ H.edgeFinset.card - (r - δ) ^ H.edgeFinset.card) ∈ Set.Icc (0:ℝ) 1 ∧
      cc (r - δ) (r ^ H.edgeFinset.card - (r - δ) ^ H.edgeFinset.card) ∈ Set.Icc (0:ℝ) 1 ∧
      ∃ W : Graphon, W.edgeDensity = r - δ ∧
        W.tDensity H = r ^ H.edgeFinset.card ∧
        (∀ W' : Graphon, W'.edgeDensity = r - δ →
          W'.tDensity H = r ^ H.edgeFinset.card → W'.entropy ≤ W.entropy) ∧
        (∀ᵐ z ∂gμ, W.toFun z.1 z.2 = bipodalValue
          (Set.Icc 0 (cc (r - δ)
            (r ^ H.edgeFinset.card - (r - δ) ^ H.edgeFinset.card)))
          (q11 (r - δ) (r ^ H.edgeFinset.card - (r - δ) ^ H.edgeFinset.card))
          (q12 (r - δ) (r ^ H.edgeFinset.card - (r - δ) ^ H.edgeFinset.card))
          (q22 (r - δ) (r ^ H.edgeFinset.card - (r - δ) ^ H.edgeFinset.card)) z) := by
    intro r hr δ hδ0 hδρ
    obtain ⟨-, -, -, -, hεU, ht0, htΔ⟩ := hloc r hr δ hδ0 hδρ
    exact hmaxi (r - δ) hεU (r ^ H.edgeFinset.card) ht0 htΔ
  -- ### The equality with the boundary excess on the KRRS regime
  have heq : ∀ r : ℝ, |r - r₀| < w → ∀ δ : ℝ, 0 < δ → δ < ρ →
      boundaryExcess H M r δ = Gc (r, δ) := by
    intro r hr δ hδ0 hδρ
    obtain ⟨h11, h12, h22, hcIcc, W, hWe, hWt, hWmax, hWae⟩ := hmax r hr δ hδ0 hδρ
    have hσ : entropyEnvelope H (r - δ) (r ^ H.edgeFinset.card) = W.entropy :=
      entropyEnvelope_eq_of_isMax H hWe hWt hWmax
    have hWent : W.entropy = (bipodalGraphon
        (Set.Icc 0 (cc (r - δ) (r ^ H.edgeFinset.card - (r - δ) ^ H.edgeFinset.card)))
        measurableSet_Icc _ _ _ h11 h12 h22).entropy := by
      refine entropy_congr_ae ?_
      filter_upwards [hWae] with z hz
      rw [hz]
      rfl
    rw [bipodalGraphon_entropy, unitμ_Icc_toReal hcIcc.1 hcIcc.2] at hWent
    -- location of `(r, δ)` for the pc-facts
    have hmem : ((r, δ) : ℝ × ℝ) ∈ Metric.ball ((r₀, 0) : ℝ × ℝ) εA :=
      hmemball r δ hr (by rw [abs_of_pos hδ0]; exact hδρ.le)
    obtain ⟨_, _, _, _, hpc, _⟩ := hball _ hmem
    have hpc1' : M.pc r < 1 := hpc.2
    have hpc0' : 0 < M.pc r := hpc.1
    -- assemble
    rw [boundaryExcess, reducedObjective, hσ, hWent, hGc_def]
    simp only [hSB_def, hem_def]
    ring
  -- ### SingularEndpoint values on the chart
  have hGc0 : ∀ r : ℝ, |r - r₀| < w → Gc (r, 0) = 0 := by
    intro r hr
    have hmem : ((r, 0) : ℝ × ℝ) ∈ Metric.ball ((r₀, 0) : ℝ × ℝ) εA :=
      hmemball r 0 hr (by rw [abs_zero]; exact hρ0.le)
    obtain ⟨_, _, ⟨hU1, hU2, hpc, hp1⟩⟩ := hball _ hmem
    obtain ⟨hcc0', hq220', _, _, _⟩ := hbdry r hU2
    have hem0 : em (r, 0) = (r, 0) := by
      rw [hem_def]
      simp
    have hSB0 : SB (r, 0) = shannonH r := by
      rw [hSB_def]
      simp only [hem0]
      rw [hcc0', hq220']
      ring
    rw [hGc_def]
    simp only [hSB0]
    have hJp : Jp (M.pc r) r = entIntegrand r - r * Real.log (M.pc r)
        - (1 - r) * Real.log (1 - M.pc r) :=
      Jp_eq_entIntegrand hpc.1 hpc.2 hp1.1.le hp1.2.le
    have hsh : entIntegrand r = -shannonH r := by
      rw [entIntegrand_eq_neg_shannonH]
    have hlogd : Real.log ((1 - M.pc r) / M.pc r)
        = Real.log (1 - M.pc r) - Real.log (M.pc r) :=
      Real.log_div (by linarith [hpc.2]) (ne_of_gt hpc.1)
    rw [hJp, hsh, hlogd]
    ring
  have hF10 : ∀ r : ℝ, |r - r₀| < w → F1 (r, 0) = 0 := by
    intro r hr
    have hmem : ((r, 0) : ℝ × ℝ) ∈ Metric.ball ((r₀, 0) : ℝ × ℝ) εA :=
      hmemball r 0 hr (by rw [abs_zero]; exact hρ0.le)
    obtain ⟨_, _, ⟨hU1, _, _, _⟩⟩ := hball _ hmem
    -- singleton quadratic bounds at this `r`
    obtain ⟨C, C', δq, hC, hC', hδq, hbq⟩ := boundaryExcess_quadratic hd M
      (Set.singleton_subset_iff.mpr hU1) isCompact_singleton
      (Set.singleton_nonempty r) H hreg hm
    have hDD : HasDerivAt (fun s => Gc (r, s)) (F1 (r, 0)) 0 := by
      rw [hF1_def]
      exact hasDerivAt_dDelta (hGcAt _ hmem).differentiableAt
    refine deriv_eq_zero_of_quadratic_bound
      (lt_min hδq hρ0) hDD (hGc0 r hr) (fun δ hδ0 hδlt => ?_) (C := C')
    have hδq' : δ < δq := lt_of_lt_of_le hδlt (min_le_left _ _)
    have hδρ' : δ < ρ := lt_of_lt_of_le hδlt (min_le_right _ _)
    obtain ⟨hlow, hup⟩ := hbq r rfl δ hδ0 hδq'
    have hGpos : 0 ≤ boundaryExcess H M r δ := by
      have h1 : 0 < C * δ ^ 2 := by positivity
      linarith
    rw [← heq r hr δ hδ0 hδρ']
    rw [abs_of_nonneg hGpos]
    exact hup
  -- ### The nested `δ`-derivatives on the *two-sided* box `|δ| ≤ ρ`
  have hmemT : ∀ r t : ℝ, |r - r₀| < w → t ∈ Set.Icc (-ρ) ρ →
      ((r, t) : ℝ × ℝ) ∈ Metric.ball ((r₀, 0) : ℝ × ℝ) εA :=
    fun r t hr ht => hmemball r t hr (abs_le.mpr ⟨ht.1, ht.2⟩)
  have hd1 : ∀ r : ℝ, |r - r₀| < w → ∀ t ∈ Set.Icc (-ρ) ρ,
      HasDerivAt (fun s => Gc (r, s)) (F1 (r, t)) t := by
    intro r hr t ht
    rw [hF1_def]
    exact hasDerivAt_dDelta (hGcAt _ (hmemT r t hr ht)).differentiableAt
  have hd2 : ∀ r : ℝ, |r - r₀| < w → ∀ t ∈ Set.Icc (-ρ) ρ,
      HasDerivAt (fun s => F1 (r, s)) (F2 (r, t)) t := by
    intro r hr t ht
    rw [hF2_def]
    exact hasDerivAt_dDelta (hF1At _ (hmemT r t hr ht)).differentiableAt
  have hd3 : ∀ r : ℝ, |r - r₀| < w → ∀ t ∈ Set.Icc (-ρ) ρ,
      HasDerivAt (fun s => F2 (r, s)) (F3 (r, t)) t := by
    intro r hr t ht
    rw [hF3_def]
    exact hasDerivAt_dDelta (hF2At _ (hmemT r t hr ht)).differentiableAt
  have hM3 : ∀ r : ℝ, |r - r₀| < w → ∀ t ∈ Set.Icc (-ρ) ρ, |F3 (r, t)| ≤ Mc :=
    fun r hr t ht => hMcB _ (hmemcb r t hr (abs_le.mpr ⟨ht.1, ht.2⟩))
  have hsub01 : Set.Icc (0:ℝ) ρ ⊆ Set.Icc (-ρ) ρ := Set.Icc_subset_Icc (by linarith) le_rfl
  -- ### The cubic Taylor bound with the chart coefficient `F2(·,0)`
  have htay : ∀ r : ℝ, |r - r₀| < w → ∀ δ : ℝ, 0 < δ → δ < ρ →
      |boundaryExcess H M r δ - F2 (r, 0) * δ ^ 2 / 2| ≤ Mc * δ ^ 3 := by
    intro r hr δ hδ0 hδρ
    have h := cubic_taylor_bound (fun t ht => hd1 r hr t (hsub01 ht))
      (fun t ht => hd2 r hr t (hsub01 ht)) (fun t ht => hd3 r hr t (hsub01 ht))
      (hGc0 r hr) (hF10 r hr) rfl (fun t ht => hM3 r hr t (hsub01 ht)) δ ⟨hδ0.le, hδρ.le⟩
    rw [heq r hr δ hδ0 hδρ]
    exact h
  -- ### `A_H` *is* the chart's second `δ`-derivative at the degenerate boundary
  have hAHeq : ∀ r : ℝ, |r - r₀| < w → AH H M r = F2 (r, 0) :=
    fun r hr => limUnder_cubic hρ0 (fun δ h1 h2 => htay r hr δ h1 h2)
  -- ### Two-sided Lipschitz control of the second `δ`-derivative
  have hlip : ∀ r : ℝ, |r - r₀| < w → ∀ δ : ℝ, |δ| ≤ ρ →
      |F2 (r, δ) - F2 (r, 0)| ≤ Mc * |δ| := fun r hr δ hδ =>
    abs_sub_le_of_deriv_bound (f := fun s => F2 (r, s)) (f' := fun s => F3 (r, s))
      (fun t ht => hd3 r hr t ht) (fun t ht => hM3 r hr t ht) δ
      (Set.mem_Icc.mpr (abs_le.mp hδ))
  -- ### The chart output
  refine ⟨w, ρ, Mc, hw0, hρ0, hMc0, Gc, q11, q12, q22, cc,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun r δ hr hδ => hGcAt _ (hmemball r δ hr hδ)
  · intro r δ hr hδ
    rw [← hF1_def]
    exact hF1At _ (hmemball r δ hr hδ)
  · exact fun r δ hr hδ0 hδρ => heq r hr δ hδ0 hδρ
  · exact fun r hr => hGc0 r hr
  · intro r hr
    rw [← hF1_def]
    exact hF10 r hr
  · intro r hr
    rw [← hF1_def, ← hF2_def]
    exact (hAHeq r hr).symm
  · intro r δ hr hδ
    rw [← hF1_def, ← hF2_def, hAHeq r hr]
    exact hlip r hr δ hδ
  · intro r δ hr hδ0 hδρ
    rw [hAHeq r hr]
    exact htay r hr δ hδ0 hδρ
  · exact fun r δ hr hδ => hqA _ (hmemball r δ hr hδ)
  · intro r δ hr hδ
    obtain ⟨-, hv, -⟩ := hball _ (hmemball r δ hr hδ)
    exact hv
  · intro r hr
    obtain ⟨-, -, ⟨-, hU2, -, -⟩⟩ := hball _ (hmemball r 0 hr (by rw [abs_zero]; exact hρ0.le))
    -- `kenyonRadinRenSadunAnalytic` also pins `q₁₂(r,0)` as the off-diagonal maximizer of
    -- `ψ_d(r,·)` and `q₁₁(r,0)` by the KRR–S boundary relation; Section 5 uses neither
    obtain ⟨b1, b2, b3, b4, b5, -⟩ := hbdry r hU2
    exact ⟨b1, b2, b3, b4, b5⟩
  · intro r δ hr hδ0 hδρ
    obtain ⟨-, -, -, hcIcc, hW⟩ := hmax r hr δ hδ0 hδρ
    exact ⟨hcIcc, hW⟩

/-- **The local analytic chart of the boundary excess.**  The trimmed form of
`boundaryExcess_chart_full`: only the eight clauses about the chart function `Gc` itself,
which is what the Section-5 consumers (`boundaryExcess_taylor`) and the scalar half of
Section 6 need. -/
theorem boundaryExcess_chart {d : ℕ} (hd : 2 ≤ d) (M : LZBoundaryArc d)
    {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (hreg : ∀ v, H.degree v = d) (hm : 1 ≤ H.edgeFinset.card)
    {r₀ : ℝ} (hr₀U : r₀ ∈ M.U) (hr₀ex : r₀ ≠ rStar d) :
    ∃ w ρ Mc : ℝ, 0 < w ∧ 0 < ρ ∧ 0 ≤ Mc ∧ ∃ Gc : ℝ × ℝ → ℝ,
      (∀ r δ : ℝ, |r - r₀| < w → |δ| ≤ ρ → AnalyticAt ℝ Gc (r, δ)) ∧
      (∀ r δ : ℝ, |r - r₀| < w → |δ| ≤ ρ → AnalyticAt ℝ (dDelta Gc) (r, δ)) ∧
      (∀ r δ : ℝ, |r - r₀| < w → 0 < δ → δ < ρ → boundaryExcess H M r δ = Gc (r, δ)) ∧
      (∀ r : ℝ, |r - r₀| < w → Gc (r, 0) = 0) ∧
      (∀ r : ℝ, |r - r₀| < w → dDelta Gc (r, 0) = 0) ∧
      (∀ r : ℝ, |r - r₀| < w → dDelta (dDelta Gc) (r, 0) = AH H M r) ∧
      (∀ r δ : ℝ, |r - r₀| < w → |δ| ≤ ρ →
        |dDelta (dDelta Gc) (r, δ) - AH H M r| ≤ Mc * |δ|) ∧
      (∀ r δ : ℝ, |r - r₀| < w → 0 < δ → δ < ρ →
        |boundaryExcess H M r δ - AH H M r * δ ^ 2 / 2| ≤ Mc * δ ^ 3) := by
  obtain ⟨w, ρ, Mc, hw0, hρ0, hMc0, Gc, q11, q12, q22, cc,
    h1, h2, h3, h4, h5, h6, h7, h8, -, -, -, -⟩ :=
    boundaryExcess_chart_full hd M H hreg hm hr₀U hr₀ex
  exact ⟨w, ρ, Mc, hw0, hρ0, hMc0, Gc, h1, h2, h3, h4, h5, h6, h7, h8⟩

/-- **A-priori `O(δ)` bounds on the chart's Kenyon–Radin–Ren–Sadun parameters.**  From the
joint analyticity of the four composed parameter maps and their degenerate boundary values
`c(r,0) = 0`, `q₂₂(r,0) = r`, one constant `L` controls all four deviations linearly in the
edge-density deficit `δ`:

`|c| ≤ L|δ|`, `|q₂₂ - r| ≤ L|δ|`, `|q₁₂ - ζ_d(r)| ≤ L|δ|`, `|q₁₁ - q₁₁⁰(r)| ≤ L|δ|`,

where `ζ_d(r) = q₁₂(r,0)` and `q₁₁⁰(r) = q₁₁(r,0)` are the maps' own boundary values.  This is
the paper's "`c(ε,δ) = O(δ)` by analyticity" remark, made uniform on a half-box, and is what
`rmk:bipodal-parameter-expansions` linearises around.  Purely a consequence of
`exists_lipschitz_bound_of_boundary_zero`; no Kenyon–Radin–Ren–Sadun input beyond the chart. -/
theorem krrs_parameter_lipschitz {m : ℕ} {q11 q12 q22 cc : ℝ → ℝ → ℝ} {r₀ w ρ : ℝ}
    (hw0 : 0 < w) (hρ0 : 0 < ρ)
    (hparA : ∀ r δ : ℝ, |r - r₀| < w → |δ| ≤ ρ →
      AnalyticAt ℝ (fun x : ℝ × ℝ => q11 (x.1 - x.2) (x.1 ^ m - (x.1 - x.2) ^ m)) (r, δ) ∧
      AnalyticAt ℝ (fun x : ℝ × ℝ => q12 (x.1 - x.2) (x.1 ^ m - (x.1 - x.2) ^ m)) (r, δ) ∧
      AnalyticAt ℝ (fun x : ℝ × ℝ => q22 (x.1 - x.2) (x.1 ^ m - (x.1 - x.2) ^ m)) (r, δ) ∧
      AnalyticAt ℝ (fun x : ℝ × ℝ => cc (x.1 - x.2) (x.1 ^ m - (x.1 - x.2) ^ m)) (r, δ))
    (hb0 : ∀ r : ℝ, |r - r₀| < w → cc r 0 = 0 ∧ q22 r 0 = r) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ r δ : ℝ, |r - r₀| ≤ w / 2 → |δ| ≤ ρ / 2 →
      |cc (r - δ) (r ^ m - (r - δ) ^ m)| ≤ L * |δ| ∧
      |q22 (r - δ) (r ^ m - (r - δ) ^ m) - r| ≤ L * |δ| ∧
      |q12 (r - δ) (r ^ m - (r - δ) ^ m) - q12 r 0| ≤ L * |δ| ∧
      |q11 (r - δ) (r ^ m - (r - δ) ^ m) - q11 r 0| ≤ L * |δ| := by
  classical
  -- the boundary slice `r ↦ f (r, 0)` of a box-analytic composed parameter map is analytic
  have hslice : ∀ f : ℝ → ℝ → ℝ,
      (∀ r δ : ℝ, |r - r₀| < w → |δ| ≤ ρ →
        AnalyticAt ℝ (fun x : ℝ × ℝ => f (x.1 - x.2) (x.1 ^ m - (x.1 - x.2) ^ m)) (r, δ)) →
      ∀ r δ : ℝ, |r - r₀| < w → |δ| ≤ ρ → AnalyticAt ℝ (fun x : ℝ × ℝ => f x.1 0) (r, δ) := by
    intro f hA r δ hr _
    have h0 : AnalyticAt ℝ (fun x : ℝ × ℝ => f (x.1 - x.2) (x.1 ^ m - (x.1 - x.2) ^ m)) (r, 0) :=
      hA r 0 hr (by rw [abs_zero]; exact hρ0.le)
    have h1 : AnalyticAt ℝ (fun s : ℝ => f (s - 0) (s ^ m - (s - 0) ^ m)) r :=
      h0.fun_comp_of_eq (analyticAt_id.prod analyticAt_const) rfl
    have h2 : AnalyticAt ℝ (fun s : ℝ => f s 0) r := by
      refine h1.congr ?_
      filter_upwards with s
      simp
    exact h2.fun_comp_of_eq (f := fun x : ℝ × ℝ => x.1) analyticAt_fst rfl
  obtain ⟨Lc, hLc0, hLc⟩ := exists_lipschitz_bound_of_boundary_zero (r₀ := r₀) hw0 hρ0
    (F := fun x : ℝ × ℝ => cc (x.1 - x.2) (x.1 ^ m - (x.1 - x.2) ^ m))
    (fun r δ hr hδ => (hparA r δ hr hδ).2.2.2)
    (fun r hr => by simp only [sub_zero, sub_self]; exact (hb0 r hr).1)
  obtain ⟨L22, hL220, hL22⟩ := exists_lipschitz_bound_of_boundary_zero (r₀ := r₀) hw0 hρ0
    (F := fun x : ℝ × ℝ => q22 (x.1 - x.2) (x.1 ^ m - (x.1 - x.2) ^ m) - x.1)
    (fun r δ hr hδ => (hparA r δ hr hδ).2.2.1.sub analyticAt_fst)
    (fun r hr => by simp only [sub_zero, sub_self]; rw [(hb0 r hr).2]; ring)
  obtain ⟨L12, hL120, hL12⟩ := exists_lipschitz_bound_of_boundary_zero (r₀ := r₀) hw0 hρ0
    (F := fun x : ℝ × ℝ => q12 (x.1 - x.2) (x.1 ^ m - (x.1 - x.2) ^ m) - q12 x.1 0)
    (fun r δ hr hδ => (hparA r δ hr hδ).2.1.sub
      (hslice q12 (fun a b ha hb => (hparA a b ha hb).2.1) r δ hr hδ))
    (fun r _ => by simp only [sub_zero, sub_self])
  obtain ⟨L11, hL110, hL11⟩ := exists_lipschitz_bound_of_boundary_zero (r₀ := r₀) hw0 hρ0
    (F := fun x : ℝ × ℝ => q11 (x.1 - x.2) (x.1 ^ m - (x.1 - x.2) ^ m) - q11 x.1 0)
    (fun r δ hr hδ => (hparA r δ hr hδ).1.sub
      (hslice q11 (fun a b ha hb => (hparA a b ha hb).1) r δ hr hδ))
    (fun r _ => by simp only [sub_zero, sub_self])
  obtain ⟨L, hL_def⟩ : ∃ x : ℝ, x = max (max Lc L22) (max L12 L11) := ⟨_, rfl⟩
  have hL0 : 0 ≤ L := by
    rw [hL_def]; exact le_trans hLc0 (le_trans (le_max_left _ _) (le_max_left _ _))
  refine ⟨L, hL0, ?_⟩
  intro r δ hr hδ
  have habs : (0:ℝ) ≤ |δ| := abs_nonneg δ
  have hc' := hLc r δ hr hδ
  have h22' := hL22 r δ hr hδ
  have h12' := hL12 r δ hr hδ
  have h11' := hL11 r δ hr hδ
  simp only at hc' h22' h12' h11'
  refine ⟨le_trans hc' (mul_le_mul_of_nonneg_right ?_ habs),
    le_trans h22' (mul_le_mul_of_nonneg_right ?_ habs),
    le_trans h12' (mul_le_mul_of_nonneg_right ?_ habs),
    le_trans h11' (mul_le_mul_of_nonneg_right ?_ habs)⟩
  · rw [hL_def]; exact le_trans (le_max_left _ _) (le_max_left _ _)
  · rw [hL_def]; exact le_trans (le_max_right _ _) (le_max_left _ _)
  · rw [hL_def]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  · rw [hL_def]; exact le_trans (le_max_right _ _) (le_max_right _ _)

/-- **`thm:positive-second-variation` of `paper/bipodal_optimizer.tex`, full form** ("Universal positivity of the scalar
second variation").  Uniformly for `r` in a compact subarc `K` avoiding the exceptional
density: the boundary excess has the expansion

`G_r(δ) = ½ A_H(r) δ² + O_K(δ³)`

with second-variation coefficient `A_H` (the definition `AH`, a chart-independent right
limit) that is **real-analytic at every `r ∈ K`** and **uniformly positive**
(`A_H ≥ CA > 0` on `K`, i.e. bounded away from zero).  Consumes `generalized_holder`
(through the quadratic lower bound and the chart) together with the footprint of
`kenyonRadinRenSadunAnalytic` (`thm:krrs-analytic-extension`, analytic-parametrization clause):
`generalized_holder` and the four cut axioms, which enter through the existence of fixed-density
entropy maximizers in `Bipodality/Existence.lean`. -/
theorem boundaryExcess_taylor {d : ℕ} (hd : 2 ≤ d) (M : LZBoundaryArc d)
    {K : Set ℝ} (hK : K ⊆ M.U) (hKc : IsCompact K) (hKne : K.Nonempty)
    (hKex : ∀ r ∈ K, r ≠ rStar d)
    {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (hreg : ∀ v, H.degree v = d) (hm : 1 ≤ H.edgeFinset.card) :
    ∃ CA Ccub δ₀ : ℝ, 0 < CA ∧ 0 ≤ Ccub ∧ 0 < δ₀ ∧
      (∀ r ∈ K, AnalyticAt ℝ (AH H M) r) ∧
      (∀ r ∈ K, CA ≤ AH H M r) ∧
      (∀ r ∈ K, ∀ δ : ℝ, 0 < δ → δ < δ₀ →
        |boundaryExcess H M r δ - AH H M r * δ ^ 2 / 2| ≤ Ccub * δ ^ 3) := by
  classical
  -- the two-sided quadratic bounds (for positivity of `A_H`)
  obtain ⟨C, C', δq, hC, hC', hδq, hbounds⟩ :=
    boundaryExcess_quadratic hd M hK hKc hKne H hreg hm
  -- charts at every point of `K`, read off from `boundaryExcess_chart`
  have hchart : ∀ r₀ : K, ∃ w ρ Mc : ℝ, 0 < w ∧ 0 < ρ ∧ 0 ≤ Mc ∧
      (∀ r ∈ Metric.ball (r₀ : ℝ) w, AnalyticAt ℝ (AH H M) r) ∧
      ∀ r ∈ Metric.ball (r₀ : ℝ) w, ∀ δ : ℝ, 0 < δ → δ < ρ →
        |boundaryExcess H M r δ - AH H M r * δ ^ 2 / 2| ≤ Mc * δ ^ 3 := by
    intro r₀
    obtain ⟨w, ρ, Mc, hw0, hρ0, hMc0, Gc, -, hG1A, -, -, -, hG2AH, -, htay⟩ :=
      boundaryExcess_chart hd M H hreg hm (hK r₀.2) (hKex r₀ r₀.2)
    refine ⟨w, ρ, Mc, hw0, hρ0, hMc0, ?_, ?_⟩
    · intro r hr
      rw [Metric.mem_ball, Real.dist_eq] at hr
      have hA : AnalyticAt ℝ (fun s : ℝ => dDelta (dDelta Gc) (s, 0)) r :=
        (analyticAt_dDelta (hG1A r 0 hr (by rw [abs_zero]; exact hρ0.le))).comp
          (f := fun s : ℝ => ((s, (0:ℝ)) : ℝ × ℝ)) (analyticAt_id.prod analyticAt_const)
      refine hA.congr ?_
      have hrb : r ∈ Metric.ball (r₀ : ℝ) w := by rw [Metric.mem_ball, Real.dist_eq]; exact hr
      filter_upwards [Metric.isOpen_ball.mem_nhds hrb] with s hs
      rw [Metric.mem_ball, Real.dist_eq] at hs
      exact hG2AH s hs
    · intro r hr δ hδ0 hδρ
      rw [Metric.mem_ball, Real.dist_eq] at hr
      exact htay r δ hr hδ0 hδρ
  choose w ρ Mc hw hρ hMc hAana hbnd using hchart
  -- finite subcover
  obtain ⟨T, hT⟩ := hKc.elim_finite_subcover (fun i : K => Metric.ball (i : ℝ) (w i))
    (fun i => Metric.isOpen_ball)
    (fun x hx => Set.mem_iUnion.mpr ⟨⟨x, hx⟩, Metric.mem_ball_self (hw ⟨x, hx⟩)⟩)
  have hTne : T.Nonempty := by
    obtain ⟨x, hx⟩ := hKne
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hT hx)
    obtain ⟨hiT, _⟩ := Set.mem_iUnion.mp hi
    exact ⟨i, hiT⟩
  -- the uniform constants
  set δ₀ : ℝ := min δq (T.inf' hTne (fun i => ρ i)) with hδ₀_def
  have hδ₀0 : 0 < δ₀ := by
    rw [hδ₀_def]
    refine lt_min hδq ?_
    rw [Finset.lt_inf'_iff]
    exact fun i _ => hρ i
  set Ccub : ℝ := T.sup' hTne (fun i => Mc i) with hCcub_def
  have hCcub0 : 0 ≤ Ccub := by
    obtain ⟨i, hi⟩ := hTne
    rw [hCcub_def]
    exact le_trans (hMc i) (Finset.le_sup' _ hi)
  -- per-point chart selection
  have hselect : ∀ r ∈ K, ∃ i ∈ T, r ∈ Metric.ball (i : ℝ) (w i) := by
    intro r hr
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hT hr)
    obtain ⟨hiT, hmem⟩ := Set.mem_iUnion.mp hi
    exact ⟨i, hiT, hmem⟩
  refine ⟨2 * C, Ccub, δ₀, by linarith, hCcub0, hδ₀0, ?_, ?_, ?_⟩
  · -- analyticity of `AH` at every point of `K`
    intro r hr
    obtain ⟨i, hiT, hmem⟩ := hselect r hr
    exact hAana i r hmem
  · -- uniform positivity: `AH ≥ 2C`
    intro r hr
    obtain ⟨i, hiT, hmem⟩ := hselect r hr
    have htends : Tendsto (fun δ => 2 * boundaryExcess H M r δ / δ ^ 2)
        (𝓝[>] (0:ℝ)) (𝓝 (AH H M r)) :=
      tendsto_cubic (hρ i) (fun δ h1 h2 => hbnd i r hmem δ h1 h2)
    have hev : ∀ᶠ δ in 𝓝[>] (0:ℝ), 2 * C ≤ 2 * boundaryExcess H M r δ / δ ^ 2 := by
      filter_upwards [Ioo_mem_nhdsGT (lt_min hδq (hρ i) : (0:ℝ) < min δq (ρ i))]
        with δ hδ
      have hδ0 : 0 < δ := hδ.1
      have hδq' : δ < δq := lt_of_lt_of_le hδ.2 (min_le_left _ _)
      have hlow := (hbounds r hr δ hδ0 hδq').1
      have hδsq : (0:ℝ) < δ ^ 2 := by positivity
      rw [le_div_iff₀ hδsq]
      linarith
    exact ge_of_tendsto htends hev
  · -- the uniform cubic remainder
    intro r hr δ hδ0 hδlt
    obtain ⟨i, hiT, hmem⟩ := hselect r hr
    have hδρ : δ < ρ i := by
      have h1 : δ₀ ≤ T.inf' hTne (fun i => ρ i) := by
        rw [hδ₀_def]; exact min_le_right _ _
      have h2 : T.inf' hTne (fun i => ρ i) ≤ ρ i := Finset.inf'_le _ hiT
      linarith
    have := hbnd i r hmem δ hδ0 hδρ
    refine le_trans this ?_
    have hMci : Mc i ≤ Ccub := by
      rw [hCcub_def]; exact Finset.le_sup' _ hiT
    have hδ3 : (0:ℝ) ≤ δ ^ 3 := by positivity
    exact mul_le_mul_of_nonneg_right hMci hδ3

end UpperTailOptimizers
