import UpperTailOptimizers.Preliminaries.KRRSAnalyticExtension.Main

/-!
# `thm:krrs-analytic-extension` in the paper's form

`krrs_rectangle` and its four public corollaries in `Preliminaries/KRRSAnalyticExtension/Main.lean` split the conclusions of
`thm:krrs-analytic-extension` across several declarations.  `krrs_analytic_extension` states
them together, on one neighbourhood `U ⊆ (0,1) ∖ {r_*}` and one width `Δ`:

* for `ε ∈ U` and `0 < ϑ = τ - ε^m < Δ` the entropy maximizer at `(e, t_H) = (ε, τ)` exists, is
  bipodal and is unique up to relabelling; after relabelling, its smaller block is the first
  block `[0, c(ε,ϑ)]`, with `0 < c(ε,ϑ) < 1/2`;
* the parameter maps `q₁₁, q₁₂, q₂₂, c` are real-analytic on `U × (-Δ, Δ)`;
* on `U × {0}`: `q₁₁(ε,0) ∈ (0,1)`, `q₁₂(ε,0) = ζ_d(ε) ≠ ε`, `q₂₂(ε,0) = ε`, `c(ε,0) = 0`;
* `c(ε,ϑ) = O_{H,U}(ϑ)` as `ϑ ↓ 0`, uniformly for `ε ∈ U`;
* the block-size derivative `eq:krrs-block-size-derivative`,
  `∂_ϑ c(ε,0) = 1/(n_d ε^{m-d} 𝒟_ε(ζ_d(ε))) > 0`, where `n_d = |V|` for `d`-regular `H`.

## Proof

The witnesses are the analytic family `F : KRRSFamily H d ε₀` of `krrs_family_exists`, with
`q₂₂ = Qmap ε q₁₁ q₁₂ c`, restricted to the optimality window of `KRRSFamily.isOptimal`.  The
window `U` is further cut down to a ball on which `exists_uniform_linear_bound` gives
`|c(ε,ϑ)| ≤ C|ϑ|`, and `Δ` to `C Δ ≤ 1/4`, which yields `c < 1/2`.  The block-size derivative
is `KRRSFamily.hasDerivAt_c_zero`: the chain rule applied to the density constraint
`𝒯̂(ε,q₁₁,q₁₂,c) = ε^m + ϑ` at `ϑ = 0`.
-/

namespace UpperTailOptimizers

open MeasureTheory Real Filter Topology

/-! ### The block-size derivative -/

/-- **`eq:krrs-block-size-derivative`**: `∂_ϑ c(ε,0) = 1/𝒜(ε,ζ_d(ε))`.

Differentiate the density constraint `𝒯̂(ε,q₁₁(ε,ϑ),q₁₂(ε,ϑ),c(ε,ϑ)) = ε^m + ϑ` at `ϑ = 0`
along the curve `ϑ ↦ (ε,q₁₁,q₁₂,c)`.  Since `𝒯̂(ε,a,b,0) = ε^m` for all `a,b`, the `a`- and
`b`-slots of `𝒯̂` vanish at `c(ε,0) = 0`, and the `c`-slot is `𝒜(ε,q₁₂(ε,0)) = 𝒜(ε,ζ_d(ε))`
(`partialC_That_zero`), so the chain rule reads `∂_ϑ c(ε,0) · 𝒜(ε,ζ_d(ε)) = 1`. -/
theorem KRRSFamily.hasDerivAt_c_zero {V : Type*} [Fintype V] [DecidableEq V]
    {H : SimpleGraph V} [DecidableRel H.Adj] {d : ℕ} {ε₀ : ℝ} (F : KRRSFamily H d ε₀)
    (hd : 2 ≤ d) (hreg : ∀ v, H.degree v = d) (hm : 2 ≤ H.edgeFinset.card)
    {ε : ℝ} (hε : ε ∈ F.U) :
    HasDerivAt (fun ϑ => F.c ε ϑ) (1 / Afun H d ε (zetaFun d ε)) 0 := by
  set Φ : ℝ × ℝ × ℝ × ℝ → ℝ := fun w => That H w.1 w.2.1 w.2.2.1 w.2.2.2 with hΦdef
  have h0 : |(0:ℝ)| < F.Δ := by rw [abs_zero]; exact F.Δ_pos
  obtain ⟨hc0, -, hb0⟩ := F.boundary ε hε
  obtain ⟨h11, h12, -, hcA⟩ := F.analytic ε hε 0 h0
  -- the three parameter curves along the vertical slice through `(ε,0)`
  have hslice : DifferentiableAt ℝ (fun ϑ : ℝ => ((ε, ϑ) : ℝ × ℝ)) 0 :=
    (differentiableAt_const ε).prodMk differentiableAt_id
  have ha : HasDerivAt (fun ϑ => F.q11 ε ϑ) (deriv (fun ϑ => F.q11 ε ϑ) 0) 0 :=
    (h11.differentiableAt.comp (0:ℝ) hslice).hasDerivAt
  have hb : HasDerivAt (fun ϑ => F.q12 ε ϑ) (deriv (fun ϑ => F.q12 ε ϑ) 0) 0 :=
    (h12.differentiableAt.comp (0:ℝ) hslice).hasDerivAt
  have hc : HasDerivAt (fun ϑ => F.c ε ϑ) (deriv (fun ϑ => F.c ε ϑ) 0) 0 :=
    (hcA.differentiableAt.comp (0:ℝ) hslice).hasDerivAt
  set a' := deriv (fun ϑ => F.q11 ε ϑ) 0
  set b' := deriv (fun ϑ => F.q12 ε ϑ) 0
  set c' := deriv (fun ϑ => F.c ε ϑ) 0
  set w₀ : ℝ × ℝ × ℝ × ℝ := (ε, F.q11 ε 0, F.q12 ε 0, 0) with hw₀
  have hΦ : AnalyticAt ℝ Φ w₀ := analyticAt_That H (by norm_num [hw₀])
  -- the chain rule along `ϑ ↦ (ε, q₁₁, q₁₂, c)`
  have hγ : HasDerivAt (fun ϑ => ((ε, F.q11 ε ϑ, F.q12 ε ϑ, F.c ε ϑ) : ℝ × ℝ × ℝ × ℝ))
      ((0, a', b', c') : ℝ × ℝ × ℝ × ℝ) 0 :=
    (hasDerivAt_const 0 ε).prodMk (ha.prodMk (hb.prodMk hc))
  have hchain := hasDerivAt_partialSlot hΦ hγ (by simp [hw₀, hc0])
  -- the density constraint makes the composite `ϑ ↦ ε^m + ϑ` near `0`
  have hlin : HasDerivAt (fun ϑ => Φ (ε, F.q11 ε ϑ, F.q12 ε ϑ, F.c ε ϑ)) 1 0 := by
    have hev : (fun ϑ => Φ (ε, F.q11 ε ϑ, F.q12 ε ϑ, F.c ε ϑ))
        =ᶠ[𝓝 0] fun ϑ => ε ^ H.edgeFinset.card + ϑ := by
      have hball : Set.Ioo (-F.Δ) F.Δ ∈ 𝓝 (0:ℝ) :=
        isOpen_Ioo.mem_nhds ⟨by linarith [F.Δ_pos], F.Δ_pos⟩
      filter_upwards [hball] with ϑ hϑ
      exact F.density ε hε ϑ (abs_lt.mpr hϑ)
    exact ((hasDerivAt_id (0:ℝ)).const_add _).congr_of_eventuallyEq hev
  have h1 : partialSlot ((0, a', b', c') : ℝ × ℝ × ℝ × ℝ) Φ w₀ = 1 := hchain.unique hlin
  -- at `c = 0` the `a`- and `b`-slots vanish, and the `c`-slot is `𝒜(ε,b)`
  have hpA : partialA Φ w₀ = 0 := by
    refine (hasDerivAt_partialA hΦ).unique ?_
    simp only [hΦdef, That_zero]
    exact hasDerivAt_const _ _
  have hpB : partialB Φ w₀ = 0 := by
    refine (hasDerivAt_partialB hΦ).unique ?_
    simp only [hΦdef, That_zero]
    exact hasDerivAt_const _ _
  have hpC : partialC Φ w₀ = Afun H d ε (zetaFun d ε) := by
    rw [hw₀, hΦdef, partialC_That_zero H hd hreg hm, hb0]
  have hsplit : ((0, a', b', c') : ℝ × ℝ × ℝ × ℝ)
      = a' • ((0, 1, 0, 0) : ℝ × ℝ × ℝ × ℝ) + b' • ((0, 0, 1, 0) : ℝ × ℝ × ℝ × ℝ)
        + c' • ((0, 0, 0, 1) : ℝ × ℝ × ℝ × ℝ) := by
    ext <;> simp
  have hkey : c' * Afun H d ε (zetaFun d ε) = 1 := by
    rw [← h1, ← hpC]
    simp only [partialSlot, partialA, partialB, partialC] at hpA hpB ⊢
    rw [hsplit, map_add, map_add, map_smul, map_smul, map_smul, hpA, hpB]
    simp [smul_eq_mul, mul_comm]
  rwa [eq_one_div_of_mul_eq_one_left hkey] at hc

/-! ### The theorem -/

/-- **`thm:krrs-analytic-extension`** (two-sided KRR–S extension for regular graphs), with the
block-size derivative `eq:krrs-block-size-derivative` from its proof. -/
theorem krrs_analytic_extension {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] {d : ℕ} (hd : 2 ≤ d)
    (hreg : ∀ v, H.degree v = d) (hm : 2 ≤ H.edgeFinset.card)
    {ε₀ : ℝ} (hε₀0 : 0 < ε₀) (hε₀1 : ε₀ < 1) (hε₀ : ε₀ ≠ rStar d) :
    ∃ (U : Set ℝ) (Δ : ℝ) (q11 q12 q22 c : ℝ → ℝ → ℝ),
      IsOpen U ∧ ε₀ ∈ U ∧ U ⊆ Set.Ioo (0:ℝ) 1 \ {rStar d} ∧ 0 < Δ ∧
      -- the entropy maximizer on the positive-excess side
      (∀ ε ∈ U, ∀ τ : ℝ, 0 < τ - ε ^ H.edgeFinset.card → τ - ε ^ H.edgeFinset.card < Δ →
        ∃ W : Graphon, W.edgeDensity = ε ∧ W.tDensity H = τ ∧
          (∀ W' : Graphon, W'.edgeDensity = ε → W'.tDensity H = τ →
            W'.entropy ≤ W.entropy) ∧
          (∀ W' : Graphon, W'.edgeDensity = ε → W'.tDensity H = τ →
            W'.entropy = W.entropy →
            ∃ σ : ℝ → ℝ, IsRelabelling σ ∧
              ∀ᵐ z ∂gμ, W'.toFun z.1 z.2 = W.toFun (σ z.1) (σ z.2)) ∧
          IsBipodal W ∧
          c ε (τ - ε ^ H.edgeFinset.card) ∈ Set.Ioo (0:ℝ) (1 / 2) ∧
          q11 ε (τ - ε ^ H.edgeFinset.card) ∈ Set.Ioo (0:ℝ) 1 ∧
          q12 ε (τ - ε ^ H.edgeFinset.card) ∈ Set.Ioo (0:ℝ) 1 ∧
          q22 ε (τ - ε ^ H.edgeFinset.card) ∈ Set.Ioo (0:ℝ) 1 ∧
          (∀ᵐ z ∂gμ, W.toFun z.1 z.2
            = bipodalValue (Set.Icc 0 (c ε (τ - ε ^ H.edgeFinset.card)))
                (q11 ε (τ - ε ^ H.edgeFinset.card))
                (q12 ε (τ - ε ^ H.edgeFinset.card))
                (q22 ε (τ - ε ^ H.edgeFinset.card)) z)) ∧
      -- the two-sided real-analytic extension
      AnalyticOnNhd ℝ (fun p : ℝ × ℝ => q11 p.1 p.2) (U ×ˢ Set.Ioo (-Δ) Δ) ∧
      AnalyticOnNhd ℝ (fun p : ℝ × ℝ => q12 p.1 p.2) (U ×ˢ Set.Ioo (-Δ) Δ) ∧
      AnalyticOnNhd ℝ (fun p : ℝ × ℝ => q22 p.1 p.2) (U ×ˢ Set.Ioo (-Δ) Δ) ∧
      AnalyticOnNhd ℝ (fun p : ℝ × ℝ => c p.1 p.2) (U ×ˢ Set.Ioo (-Δ) Δ) ∧
      -- the values on `U × {0}`
      (∀ ε ∈ U, q11 ε 0 ∈ Set.Ioo (0:ℝ) 1 ∧ q12 ε 0 = zetaFun d ε ∧ zetaFun d ε ≠ ε ∧
        q22 ε 0 = ε ∧ c ε 0 = 0) ∧
      -- `c(ε,ϑ) = O_{H,U}(ϑ)` as `ϑ ↓ 0`, uniformly for `ε ∈ U`
      (∃ C : ℝ, 0 < C ∧ ∀ ε ∈ U, ∀ ϑ : ℝ, 0 < ϑ → ϑ < Δ → |c ε ϑ| ≤ C * ϑ) ∧
      -- `eq:krrs-block-size-derivative`
      (∀ ε ∈ U,
        HasDerivAt (fun ϑ => c ε ϑ)
          (1 / ((Fintype.card V : ℝ) * ε ^ (H.edgeFinset.card - d)
            * Dfun d ε (zetaFun d ε))) 0 ∧
        0 < 1 / ((Fintype.card V : ℝ) * ε ^ (H.edgeFinset.card - d)
            * Dfun d ε (zetaFun d ε))) := by
  obtain ⟨F⟩ := krrs_family_exists H hd hreg hm hε₀0 hε₀1 hε₀
  obtain ⟨U', hU'open, hε₀U', hU'sub, Δ', hΔ'0, hΔ'le, hopt⟩ :=
    F.isOptimal hd hreg hm ⟨hε₀0, hε₀1⟩ hε₀
  -- the uniform bound `|c(ε,ϑ)| ≤ C|ϑ|` on a square around `(ε₀,0)`
  have hF0 : |(0:ℝ)| < F.Δ := by rw [abs_zero]; exact F.Δ_pos
  have hzero : ∀ᶠ x in 𝓝 ε₀, (fun p : ℝ × ℝ => F.c p.1 p.2) (x, 0) = 0 :=
    Filter.eventually_of_mem (F.isOpen_U.mem_nhds F.mem_U) fun x hx => (F.boundary x hx).1
  obtain ⟨r, C, hr0, hC0, hlin⟩ :=
    exists_uniform_linear_bound (f := fun p : ℝ × ℝ => F.c p.1 p.2)
      (F.analytic ε₀ F.mem_U 0 hF0).2.2.2 hzero
  set U : Set ℝ := U' ∩ Metric.ball ε₀ r
  set Δ : ℝ := min (min Δ' r) (1 / (4 * C)) with hΔdef
  have hΔ0 : 0 < Δ := lt_min (lt_min hΔ'0 hr0) (by positivity)
  have hΔF : Δ ≤ F.Δ := le_trans (min_le_left _ _) (le_trans (min_le_left _ _) hΔ'le)
  have hΔ' : Δ ≤ Δ' := le_trans (min_le_left _ _) (min_le_left _ _)
  have hΔr : Δ ≤ r := le_trans (min_le_left _ _) (min_le_right _ _)
  have hCΔ : C * Δ ≤ 1 / 4 := by
    have h := mul_le_mul_of_nonneg_left (min_le_right (min Δ' r) (1 / (4 * C))) hC0.le
    rw [← hΔdef] at h
    refine le_trans h (le_of_eq ?_)
    field_simp
  have hUF : ∀ ε ∈ U, ε ∈ F.U := fun ε hε => hU'sub hε.1
  have hbound : ∀ ε ∈ U, ∀ ϑ : ℝ, 0 < ϑ → ϑ < Δ → |F.c ε ϑ| ≤ C * ϑ := by
    intro ε hε ϑ hϑ0 hϑΔ
    have hx : |ε - ε₀| < r := by
      have := Metric.mem_ball.mp hε.2
      rwa [Real.dist_eq] at this
    have hy : |ϑ| < r := by
      rw [abs_of_pos hϑ0]; exact lt_of_lt_of_le hϑΔ hΔr
    have := hlin ε ϑ hx hy
    rwa [abs_of_pos hϑ0] at this
  have hstrip : ∀ p : ℝ × ℝ, p ∈ U ×ˢ Set.Ioo (-Δ) Δ → p.1 ∈ F.U ∧ |p.2| < F.Δ := by
    rintro ⟨ε, ϑ⟩ ⟨hε, hϑ1, hϑ2⟩
    exact ⟨hUF ε hε, lt_of_lt_of_le (abs_lt.mpr ⟨hϑ1, hϑ2⟩) hΔF⟩
  refine ⟨U, Δ, F.q11, F.q12, fun x y => Qmap x (F.q11 x y) (F.q12 x y) (F.c x y), F.c,
    hU'open.inter Metric.isOpen_ball, ⟨hε₀U', Metric.mem_ball_self hr0⟩, ?_, hΔ0, ?_,
    fun p hp => (F.analytic p.1 (hstrip p hp).1 p.2 (hstrip p hp).2).1,
    fun p hp => (F.analytic p.1 (hstrip p hp).1 p.2 (hstrip p hp).2).2.1,
    fun p hp => (F.analytic p.1 (hstrip p hp).1 p.2 (hstrip p hp).2).2.2.1,
    fun p hp => (F.analytic p.1 (hstrip p hp).1 p.2 (hstrip p hp).2).2.2.2,
    ?_, ⟨C, hC0, hbound⟩, ?_⟩
  · -- `U ⊆ (0,1) ∖ {r_*}`
    intro ε hε
    obtain ⟨hεI, hεr, -⟩ := F.interior ε (hUF ε hε) 0 hF0
    exact ⟨hεI, hεr⟩
  · -- the maximizer on the positive-excess side
    intro ε hε τ hs0 hsΔ
    set ϑ := τ - ε ^ H.edgeFinset.card with hϑdef
    have hεF := hUF ε hε
    obtain ⟨h11, h12, h22, -, hval, he, ht⟩ :=
      F.graphon_spec hεF hs0 (lt_of_lt_of_le hsΔ hΔF)
    have hτ : ε ^ H.edgeFinset.card + ϑ = τ := by rw [hϑdef]; ring
    have hc : F.c ε ϑ < 1 / 2 := by
      have h1 := hbound ε hε ϑ hs0 hsΔ
      have h2 : C * ϑ < C * Δ := mul_lt_mul_of_pos_left hsΔ hC0
      linarith [le_abs_self (F.c ε ϑ)]
    refine ⟨F.graphon ε ϑ, he, by rw [ht, hτ], ?_, ?_,
      ⟨Set.Icc 0 (F.c ε ϑ), _, _, _, measurableSet_Icc,
        ⟨h11.1.le, h11.2.le⟩, ⟨h12.1.le, h12.2.le⟩, ⟨h22.1.le, h22.2.le⟩,
        Filter.Eventually.of_forall hval⟩,
      ⟨F.pode_pos ε hεF ϑ hs0 (lt_of_lt_of_le hsΔ hΔF), hc⟩, h11, h12, h22,
      Filter.Eventually.of_forall hval⟩
    · intro W' h1 h2
      exact (hopt ε hε.1 ϑ hs0 (lt_of_lt_of_le hsΔ hΔ') W' h1 (by rw [h2, hτ])).1
    · intro W' h1 h2 h3
      exact (hopt ε hε.1 ϑ hs0 (lt_of_lt_of_le hsΔ hΔ') W' h1 (by rw [h2, hτ])).2 h3
  · -- the values on `U × {0}`
    intro ε hε
    have hεF := hUF ε hε
    obtain ⟨hεI, hεr, h11, -⟩ := F.interior ε hεF 0 hF0
    obtain ⟨hc0, -, hz⟩ := F.boundary ε hεF
    refine ⟨h11, hz, zetaFun_ne_self hd hεI hεr, ?_, hc0⟩
    show Qmap ε (F.q11 ε 0) (F.q12 ε 0) (F.c ε 0) = ε
    rw [hc0, Qmap_zero]
  · -- `eq:krrs-block-size-derivative`
    intro ε hε
    have hεF := hUF ε hε
    obtain ⟨hεI, hεr, -⟩ := F.interior ε hεF 0 hF0
    have hA : 0 < Afun H d ε (zetaFun d ε) :=
      Afun_pos H hd (by omega) hεI.1 (zetaFun_mem hd hεI).1.le (zetaFun_ne_self hd hεI hεr)
    exact ⟨F.hasDerivAt_c_zero hd hreg hm hεF, one_div_pos.mpr hA⟩

end UpperTailOptimizers
