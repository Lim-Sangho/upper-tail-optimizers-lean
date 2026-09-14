import UpperTailOptimizers.NonexceptionalEndpoint.QuadraticGrowth.AnalyticExtension
import UpperTailOptimizers.NonexceptionalEndpoint.QuadraticGrowth.GraphonLower
import UpperTailOptimizers.NonexceptionalEndpoint.QuadraticGrowth.QuadraticUpper

/-!
# Section 4.2 in the paper's coordinates

The files of `NonexceptionalEndpoint/QuadraticGrowth/` prove the results of `sec:nonexceptional-quadratic-growth` on a
Lubetzky–Zhao boundary arc `M`, uniformly over a compact subset `K` of the arc window.  The
paper fixes `r₀ ∈ (0,1) ∖ {r_*}` and works on the open interval `I ∋ r₀` of
`lem:fixed-density-bipodality`, with compact closure in `(0,1) ∖ {r_*}`, shrinking `I` around
`r₀` when needed.  This file states the results in that form, with the global boundary curve
`pcGlobal`: there is `w > 0` such that the conclusions hold on **every** open interval
`I = (lo, hi)` with `r₀ - w ≤ lo < r₀ < hi ≤ r₀ + w`.  Every such `I` has compact closure in
`(0,1) ∖ {r_*}`, and intersecting it with the interval of `lem:fixed-density-bipodality` gives
the shrunken interval that the paper uses.  `lem:scalar-quadratic-bound` and
`prop:graphon-quadratic-bound` need no shrinking in the paper; `scalar_quadratic_bound_Icc` and
`graphon_quadratic_bound_Icc` hold on every interval `I = (lo, hi)` with
`[lo, hi] ⊆ (0,1) ∖ {r_*}`, which includes the interval of `fixed_density_bipodality_Icc`.

The arc and `w` come from `exists_arc_window`.  `scalar_quadratic_bound`,
`bipodal_quadratic_bound` and `positive_second_variation_interval` apply their compact-set
versions from `NonexceptionalEndpoint/QuadraticGrowth/` to `K = [lo, hi]` and rewrite `M.pc` as `pcGlobal` with
`pcGlobal_eq_pc`.  `graphon_quadratic_bound` takes `w`, `C_{d,I}` and `δ₀` from
`scalar_quadratic_bound` and derives the graph clause from the scalar clause applied to
`X = W(U,V)` on `([0,1]², gμ)`, using `holder_moment` (`graphon_bound_of_scalar`).  So only the
graph clause uses the generalized Hölder inequality.  `scalar_quadratic_bound_Icc` covers
`[lo, hi]` by finitely many windows of `scalar_quadratic_bound` and takes the minima of the
constants (`exists_uniform_constants_of_local`).

* `exists_arc_window` — the arc `M ∋ r₀` and the radius `w`, with `[lo, hi] ⊆ M.U`,
  `[lo, hi] ⊆ (0,1) ∖ {r_*}`;
* `scalar_quadratic_bound` — `lem:scalar-quadratic-bound` on the small intervals;
* `graphon_bound_of_scalar` — the graph clause of `prop:graphon-quadratic-bound` from the scalar
  clause;
* `graphon_quadratic_bound` — `lem:scalar-quadratic-bound` and
  `prop:graphon-quadratic-bound` on the small intervals, with the same `C_{d,I}` and `δ₀` for
  every graph;
* `exists_uniform_constants_of_local` — local constants made uniform on a compact set;
* `scalar_quadratic_bound_Icc`, `graphon_quadratic_bound_Icc` — the same two results on every
  interval with compact closure in `(0,1) ∖ {r_*}`, in particular on the interval of
  `lem:fixed-density-bipodality`;
* `bipodal_quadratic_bound` — `lem:bipodal-quadratic-bound`;
* `positive_second_variation_interval` — `thm:positive-second-variation`, with
  `A_H(r) := ∂²_δG(r,0)` as in the paper.
-/

namespace UpperTailOptimizers

open MeasureTheory Real Set Filter Topology

universe u v

/-- **A window around a nonexceptional density.**  For `r₀ ∈ (0,1) ∖ {r_*}` there are a
Lubetzky–Zhao boundary arc `M` and `w > 0` such that, for every `lo < r₀ < hi` with
`r₀ - w ≤ lo` and `hi ≤ r₀ + w`, the closed interval `[lo, hi]` lies in the arc window `M.U`,
inside `(0,1)`, and avoids `r_*`.  The arc and `w` depend only on `d` and `r₀`. -/
theorem exists_arc_window {d : ℕ} (hd : 2 ≤ d) {r₀ : ℝ} (hr₀0 : 0 < r₀) (hr₀1 : r₀ < 1)
    (hr₀ : r₀ ≠ rStar d) :
    ∃ (M : LZBoundaryArc d) (w : ℝ), 0 < w ∧ ∀ lo hi : ℝ, lo < r₀ → r₀ < hi →
      r₀ - w ≤ lo → hi ≤ r₀ + w →
      Set.Icc lo hi ⊆ M.U ∧ (∀ r ∈ Set.Icc lo hi, r ≠ rStar d) ∧
        Set.Icc lo hi ⊆ Set.Ioo (0:ℝ) 1 \ {rStar d} := by
  obtain ⟨M, hr₀U, -⟩ := lz_boundary_arcs hd hr₀0 hr₀1 hr₀
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp M.isOpen_U r₀ hr₀U
  have hsep : 0 < |r₀ - rStar d| := abs_pos.mpr (sub_ne_zero.mpr hr₀)
  set w : ℝ := min (ε / 2) (|r₀ - rStar d| / 2) with hwdef
  have hwε : w ≤ ε / 2 := min_le_left _ _
  have hwsep : w ≤ |r₀ - rStar d| / 2 := min_le_right _ _
  refine ⟨M, w, lt_min (half_pos hε) (half_pos hsep), ?_⟩
  intro lo hi _ _ hwlo hwhi
  have hU : Set.Icc lo hi ⊆ M.U := by
    intro r hr
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hr.1, hr.2]
  have hexc : ∀ r ∈ Set.Icc lo hi, r ≠ rStar d := by
    intro r hr hrs
    have hdist : |r₀ - r| ≤ w := abs_le.mpr ⟨by linarith [hr.2], by linarith [hr.1]⟩
    rw [hrs] at hdist
    linarith
  refine ⟨hU, hexc, fun r hr => ⟨?_, hexc r hr⟩⟩
  obtain ⟨hpc0, hpcr, hr1, -⟩ := M.ordering r (hU hr)
  exact ⟨lt_trans hpc0 hpcr, hr1⟩

/-- **`lem:scalar-quadratic-bound` (scalar quadratic lower bound).**  For every small open
interval `I ∋ r₀` there are `C_{d,I} > 0` and `δ₀ > 0` such that, for `r ∈ I` and
`0 < δ < δ₀`, every random variable `X` with values in `[0,1]`, `E X = r - δ` and
`E X^d ≥ r^d` satisfies `E J_{pc(r)}(X) ≥ J_{pc(r)}(r) + C_{d,I} δ²`.

The constant is `C_{d,I} = γ / (1 + d/η_d)²` of `expectation_quadratic_lower`, with `γ` from
`quadSep_dist` and `η_d = η^d` from `arc_uniform_bounds` on `[lo, hi]`; `δ₀ = 1`. -/
theorem scalar_quadratic_bound {d : ℕ} (hd : 2 ≤ d) {r₀ : ℝ} (hr₀0 : 0 < r₀) (hr₀1 : r₀ < 1)
    (hr₀ : r₀ ≠ rStar d) :
    ∃ w : ℝ, 0 < w ∧ ∀ lo hi : ℝ, lo < r₀ → r₀ < hi → r₀ - w ≤ lo → hi ≤ r₀ + w →
      Set.Icc lo hi ⊆ Set.Ioo (0:ℝ) 1 \ {rStar d} ∧
      ∃ C δ₀ : ℝ, 0 < C ∧ 0 < δ₀ ∧
        ∀ r ∈ Set.Ioo lo hi, ∀ δ : ℝ, 0 < δ → δ < δ₀ →
          ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
            (X : Ω → ℝ), Measurable X → (∀ ω, X ω ∈ Set.Icc (0:ℝ) 1) →
            ∫ ω, X ω ∂μ = r - δ → r ^ d ≤ ∫ ω, X ω ^ d ∂μ →
            Jp (pcGlobal d r) r + C * δ ^ 2 ≤ ∫ ω, Jp (pcGlobal d r) (X ω) ∂μ := by
  obtain ⟨M, w, hw, hwin⟩ := exists_arc_window hd hr₀0 hr₀1 hr₀
  refine ⟨w, hw, fun lo hi hlo hhi hwlo hwhi => ?_⟩
  obtain ⟨hK, -, hIcc⟩ := hwin lo hi hlo hhi hwlo hwhi
  have hKne : (Set.Icc lo hi).Nonempty := Set.nonempty_Icc.mpr (hlo.trans hhi).le
  obtain ⟨γ, hγ, hsep⟩ := quadSep_dist hd M hK isCompact_Icc hKne
  obtain ⟨η, hη0, -, hηbd⟩ := arc_uniform_bounds M hK isCompact_Icc hKne
  have hd1 : 1 ≤ d := le_trans one_le_two hd
  -- the moment gap `η_d ≤ r^d - (sm r)^d` on the family `sm r < r`
  set ηd : ℝ := η ^ (d - 1) * η with hηddef
  have hηd0 : 0 < ηd := by positivity
  -- `C_{d,I}` depends only on `γ` and `η`, hence only on `d` and `I`
  refine ⟨hIcc, γ / (1 + d / ηd) ^ 2, 1, by positivity, one_pos, ?_⟩
  intro r hr δ hδ _ Ω _ μ _ X hX hXrange hmean hmom
  have hrK : r ∈ Set.Icc lo hi := Set.Ioo_subset_Icc_self hr
  obtain ⟨hpc0, hpcr, hr1, hsmne, hsm0, hsm1⟩ := M.ordering r (hK hrK)
  have hr0 : 0 < r := lt_trans hpc0 hpcr
  obtain ⟨-, -, hηs, -, -, hηdist⟩ := hηbd r hrK
  -- case dichotomy at the second contact, with the uniform moment gap on the lower side
  have hcase : r < M.sm r ∨ (M.sm r < r ∧ ηd ≤ r ^ d - (M.sm r) ^ d) := by
    rcases lt_or_gt_of_ne hsmne with hlt | hgt
    · right
      refine ⟨hlt, ?_⟩
      have hkey := pow_sub_pow_ge (x := r) (y := M.sm r) hr0.le hsm0.le hd1
      have habs1 : |r - M.sm r| = r - M.sm r := abs_of_pos (by linarith)
      have hpow_le : (M.sm r) ^ d ≤ r ^ d := pow_le_pow_left₀ hsm0.le hlt.le d
      have habs2 : |r ^ d - (M.sm r) ^ d| = r ^ d - (M.sm r) ^ d :=
        abs_of_nonneg (by linarith)
      rw [habs1, habs2] at hkey
      have h2 : η ≤ r - M.sm r := by
        have habs : |M.sm r - r| = r - M.sm r := by
          rw [abs_of_neg (by linarith : M.sm r - r < 0)]; ring
        linarith [habs]
      have hstep : ηd ≤ (M.sm r) ^ (d - 1) * (r - M.sm r) := by
        rw [hηddef]
        exact mul_le_mul (pow_le_pow_left₀ hη0.le hηs _) h2 hη0.le (pow_nonneg hsm0.le _)
      linarith
    · left; exact hgt
  rw [pcGlobal_eq_pc hd M (hK hrK)]
  exact expectation_quadratic_lower (μ := μ) hX hXrange hd1 hpc0 (lt_trans hpcr hr1) hr0 hr1
    hsm0 hsm1 hδ.le (slope_pos hd1 hpc0 hpcr hr1) hγ hηd0 (hsep r hrK) hcase hmean hmom

/-- **The graph clause of `prop:graphon-quadratic-bound` from the scalar clause.**  If the
conclusion of `lem:scalar-quadratic-bound` holds at `(r, δ)` for every random variable on a
probability space in `Type u`, then every graphon `W` with `e(W) = r - δ` and `t(H,W) ≥ r^m`, for a
`d`-regular `H`, satisfies `I_p(W) ≥ J_p(r) + C δ²`.  Apply the scalar clause to `X = W(U,V)` with
`(U,V)` uniform on `[0,1]²`, lifted to `Type u`; the generalized Hölder inequality
(`holder_moment`) gives `E X^d ≥ r^d`. -/
theorem graphon_bound_of_scalar {d : ℕ} (hd : 2 ≤ d) {r δ C p : ℝ} (hr0 : 0 ≤ r)
    (hscalar : ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (X : Ω → ℝ), Measurable X → (∀ ω, X ω ∈ Set.Icc (0:ℝ) 1) →
      ∫ ω, X ω ∂μ = r - δ → r ^ d ≤ ∫ ω, X ω ^ d ∂μ →
      Jp p r + C * δ ^ 2 ≤ ∫ ω, Jp p (X ω) ∂μ)
    {V : Type v} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (hreg : ∀ x, H.degree x = d) (hm : 1 ≤ H.edgeFinset.card) (W : Graphon)
    (hWe : W.edgeDensity = r - δ) (hWt : r ^ H.edgeFinset.card ≤ W.tDensity H) :
    Jp p r + C * δ ^ 2 ≤ W.Ip p := by
  -- `X = W(U,V)` on `([0,1]², gμ)`, transported to `ULift (ℝ × ℝ) : Type u`
  set e : ULift.{u} (ℝ × ℝ) ≃ᵐ ℝ × ℝ := MeasurableEquiv.ulift with hedef
  set μ' : Measure (ULift.{u} (ℝ × ℝ)) := gμ.map e.symm with hμ'def
  have : IsProbabilityMeasure μ' := Measure.isProbabilityMeasure_map e.symm.measurable.aemeasurable
  have hint : ∀ g : ℝ × ℝ → ℝ, ∫ ω, g (e ω) ∂μ' = ∫ z, g z ∂gμ := fun g => by
    rw [hμ'def, integral_map_equiv]
    simp
  -- the mean is the edge density, and the generalized Hölder inequality turns the
  -- `H`-density constraint into the `d`-th moment constraint
  have hmean : ∫ ω, W.toFun (e ω).1 (e ω).2 ∂μ' = r - δ :=
    (hint fun z => W.toFun z.1 z.2).trans hWe
  have hmom : r ^ d ≤ ∫ ω, W.toFun (e ω).1 (e ω).2 ^ d ∂μ' :=
    (holder_moment H hreg hd W hr0 hm hWt).trans_eq (hint fun z => W.toFun z.1 z.2 ^ d).symm
  have h := hscalar μ' (fun ω => W.toFun (e ω).1 (e ω).2)
    (W.measurable_uncurry.comp e.measurable) (fun ω => W.mem_Icc _ _) hmean hmom
  exact h.trans_eq (hint fun z => Jp p (W.toFun z.1 z.2))

/-- **`lem:scalar-quadratic-bound` and `prop:graphon-quadratic-bound`.**  For every small open
interval `I ∋ r₀` there are `C_{d,I} > 0` and `δ₀ > 0` such that, for `r ∈ I` and `0 < δ < δ₀`:

* every random variable `X` with values in `[0,1]`, `E X = r - δ` and `E X^d ≥ r^d` satisfies
  `E J_{pc(r)}(X) ≥ J_{pc(r)}(r) + C_{d,I} δ²`;
* for every `d`-regular graph `H`, every graphon `W` with `e(W) = r - δ` and `t(H,W) ≥ r^m`
  satisfies `I_{pc(r)}(W) ≥ J_{pc(r)}(r) + C_{d,I} δ²`, with the same `C_{d,I}` and `δ₀`.

The constants are those of `scalar_quadratic_bound`; the graph clause is its scalar clause for
`X = W(U,V)` with `(U,V)` uniform on `[0,1]²`, lifted to `Type u`. -/
theorem graphon_quadratic_bound {d : ℕ} (hd : 2 ≤ d) {r₀ : ℝ} (hr₀0 : 0 < r₀) (hr₀1 : r₀ < 1)
    (hr₀ : r₀ ≠ rStar d) :
    ∃ w : ℝ, 0 < w ∧ ∀ lo hi : ℝ, lo < r₀ → r₀ < hi → r₀ - w ≤ lo → hi ≤ r₀ + w →
      Set.Icc lo hi ⊆ Set.Ioo (0:ℝ) 1 \ {rStar d} ∧
      ∃ C δ₀ : ℝ, 0 < C ∧ 0 < δ₀ ∧
        (∀ r ∈ Set.Ioo lo hi, ∀ δ : ℝ, 0 < δ → δ < δ₀ →
          ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
            (X : Ω → ℝ), Measurable X → (∀ ω, X ω ∈ Set.Icc (0:ℝ) 1) →
            ∫ ω, X ω ∂μ = r - δ → r ^ d ≤ ∫ ω, X ω ^ d ∂μ →
            Jp (pcGlobal d r) r + C * δ ^ 2 ≤ ∫ ω, Jp (pcGlobal d r) (X ω) ∂μ) ∧
        (∀ {V : Type v} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj],
          (∀ x, H.degree x = d) → 1 ≤ H.edgeFinset.card →
          ∀ r ∈ Set.Ioo lo hi, ∀ δ : ℝ, 0 < δ → δ < δ₀ → ∀ W : Graphon,
            W.edgeDensity = r - δ → r ^ H.edgeFinset.card ≤ W.tDensity H →
            Jp (pcGlobal d r) r + C * δ ^ 2 ≤ W.Ip (pcGlobal d r)) := by
  obtain ⟨w, hw, hmain⟩ := scalar_quadratic_bound.{u} hd hr₀0 hr₀1 hr₀
  refine ⟨w, hw, fun lo hi hlo hhi hwlo hwhi => ?_⟩
  obtain ⟨hIcc, C, δ₀, hC, hδ₀, hscalar⟩ := hmain lo hi hlo hhi hwlo hwhi
  refine ⟨hIcc, C, δ₀, hC, hδ₀, hscalar, ?_⟩
  intro V _ _ H _ hreg hm r hr δ hδ hδ₀' W hWe hWt
  exact graphon_bound_of_scalar hd (hIcc (Set.Ioo_subset_Icc_self hr)).1.1.le
    (fun μ _ X => hscalar r hr δ hδ hδ₀' μ X) H hreg hm W hWe hWt

/-! ### Lemma 4.7 and Corollary 4.8 on an interval with compact closure

`sec:nonexceptional-quadratic-growth` states `lem:scalar-quadratic-bound` and
`prop:graphon-quadratic-bound` for every `r` in the interval `I` of `lem:fixed-density-bipodality`,
whose closure lies in `(0,1) ∖ {r_*}`, without shrinking `I`.  The two theorems below hold on every
interval `I = (lo, hi)` with `[lo, hi] ⊆ (0,1) ∖ {r_*}`, for all `r ∈ [lo, hi]`; the interval of
`fixed_density_bipodality_Icc` (`NonexceptionalEndpoint/LocalReduction/Global.lean`) is one of them.  The constants on the
small windows of `scalar_quadratic_bound` are made uniform on `[lo, hi]` by compactness
(`exists_uniform_constants_of_local`). -/

/-- **Uniform constants on a compact set from local constants.**  Let `P C δ₀ r` be a property that
survives decreasing `C` and `δ₀`.  If every point of a compact `K` has a neighbourhood on which
`P C δ₀ ·` holds for some `C > 0` and `δ₀ > 0`, then one pair `C > 0`, `δ₀ > 0` serves all of `K`:
take minima over a finite subcover (`IsCompact.induction_on`). -/
theorem exists_uniform_constants_of_local {K : Set ℝ} (hKc : IsCompact K)
    {P : ℝ → ℝ → ℝ → Prop}
    (hmono : ∀ C δ₀ C' δ₀' r : ℝ, P C δ₀ r → C' ≤ C → δ₀' ≤ δ₀ → P C' δ₀' r)
    (hloc : ∀ x ∈ K, ∃ t ∈ 𝓝 x, ∃ C δ₀ : ℝ, 0 < C ∧ 0 < δ₀ ∧ ∀ r ∈ t, P C δ₀ r) :
    ∃ C δ₀ : ℝ, 0 < C ∧ 0 < δ₀ ∧ ∀ r ∈ K, P C δ₀ r := by
  refine hKc.induction_on (p := fun S => ∃ C δ₀ : ℝ, 0 < C ∧ 0 < δ₀ ∧ ∀ r ∈ S, P C δ₀ r)
    ⟨1, 1, one_pos, one_pos, fun r hr => by simp at hr⟩ ?_ ?_ ?_
  · rintro S T hST ⟨C, δ₀, hC, hδ₀, h⟩
    exact ⟨C, δ₀, hC, hδ₀, fun r hr => h r (hST hr)⟩
  · rintro S T ⟨C₁, δ₁, hC₁, hδ₁, h₁⟩ ⟨C₂, δ₂, hC₂, hδ₂, h₂⟩
    refine ⟨min C₁ C₂, min δ₁ δ₂, lt_min hC₁ hC₂, lt_min hδ₁ hδ₂, ?_⟩
    rintro r (hr | hr)
    · exact hmono _ _ _ _ r (h₁ r hr) (min_le_left _ _) (min_le_left _ _)
    · exact hmono _ _ _ _ r (h₂ r hr) (min_le_right _ _) (min_le_right _ _)
  · intro x hx
    obtain ⟨t, ht, C, δ₀, hC, hδ₀, h⟩ := hloc x hx
    exact ⟨t, mem_nhdsWithin_of_mem_nhds ht, C, δ₀, hC, hδ₀, h⟩

/-- **`lem:scalar-quadratic-bound` (scalar quadratic lower bound) on the paper's interval.**  Let
`I = (lo, hi)` have closure `[lo, hi] ⊆ (0,1) ∖ {r_*}`, as the interval of
`lem:fixed-density-bipodality` does (`fixed_density_bipodality_Icc`).  There are `C_{d,I} > 0` and
`δ₀ > 0` such that, for every `r ∈ [lo, hi]` (in particular every `r ∈ I`) and `0 < δ < δ₀`, every
random variable `X` with values in `[0,1]`, `E X = r - δ` and `E X^d ≥ r^d` satisfies
`E J_{pc(r)}(X) ≥ J_{pc(r)}(r) + C_{d,I} δ²`.

The constants depend only on `d`, `lo` and `hi`.  Each point of `[lo, hi]` has a window on which
`scalar_quadratic_bound` gives constants; `exists_uniform_constants_of_local` takes their minima
over a finite subcover. -/
theorem scalar_quadratic_bound_Icc {d : ℕ} (hd : 2 ≤ d) {lo hi : ℝ}
    (hI : Set.Icc lo hi ⊆ Set.Ioo (0:ℝ) 1 \ {rStar d}) :
    ∃ C δ₀ : ℝ, 0 < C ∧ 0 < δ₀ ∧
      ∀ r ∈ Set.Icc lo hi, ∀ δ : ℝ, 0 < δ → δ < δ₀ →
        ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
          (X : Ω → ℝ), Measurable X → (∀ ω, X ω ∈ Set.Icc (0:ℝ) 1) →
          ∫ ω, X ω ∂μ = r - δ → r ^ d ≤ ∫ ω, X ω ^ d ∂μ →
          Jp (pcGlobal d r) r + C * δ ^ 2 ≤ ∫ ω, Jp (pcGlobal d r) (X ω) ∂μ := by
  refine exists_uniform_constants_of_local isCompact_Icc
    (P := fun C δ₀ r => ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : Ω → ℝ), Measurable X → (∀ ω, X ω ∈ Set.Icc (0:ℝ) 1) →
        ∫ ω, X ω ∂μ = r - δ → r ^ d ≤ ∫ ω, X ω ^ d ∂μ →
        Jp (pcGlobal d r) r + C * δ ^ 2 ≤ ∫ ω, Jp (pcGlobal d r) (X ω) ∂μ) ?_ ?_
  · -- decreasing `C` and `δ₀` keeps the bound
    intro C δ₀ C' δ₀' r h hC hδ δ hδ0 hδlt Ω _ μ _ X hX hXrange hmean hmom
    have h1 := h δ hδ0 (lt_of_lt_of_le hδlt hδ) μ X hX hXrange hmean hmom
    have h2 : C' * δ ^ 2 ≤ C * δ ^ 2 := mul_le_mul_of_nonneg_right hC (sq_nonneg δ)
    linarith
  · -- the window of `scalar_quadratic_bound` around each point
    intro x hx
    obtain ⟨⟨hx0, hx1⟩, hxex⟩ := hI hx
    obtain ⟨w, hw, hmain⟩ := scalar_quadratic_bound.{u} hd hx0 hx1 hxex
    obtain ⟨-, C, δ₀, hC, hδ₀, h⟩ :=
      hmain (x - w) (x + w) (by linarith) (by linarith) le_rfl le_rfl
    exact ⟨Set.Ioo (x - w) (x + w), Ioo_mem_nhds (by linarith) (by linarith), C, δ₀, hC, hδ₀, h⟩

/-- **`lem:scalar-quadratic-bound` and `prop:graphon-quadratic-bound` on the paper's interval.**  Let
`I = (lo, hi)` have closure `[lo, hi] ⊆ (0,1) ∖ {r_*}`, as the interval of
`lem:fixed-density-bipodality` does (`fixed_density_bipodality_Icc`).  There are `C_{d,I} > 0` and
`δ₀ > 0` such that, for every `r ∈ [lo, hi]` (in particular every `r ∈ I`) and `0 < δ < δ₀`:

* every random variable `X` with values in `[0,1]`, `E X = r - δ` and `E X^d ≥ r^d` satisfies
  `E J_{pc(r)}(X) ≥ J_{pc(r)}(r) + C_{d,I} δ²`;
* for every `d`-regular graph `H`, every graphon `W` with `e(W) = r - δ` and `t(H,W) ≥ r^m`
  satisfies `I_{pc(r)}(W) ≥ J_{pc(r)}(r) + C_{d,I} δ²`, with the same `C_{d,I}` and `δ₀`.

The constants are those of `scalar_quadratic_bound_Icc`; the graph clause is
`graphon_bound_of_scalar`. -/
theorem graphon_quadratic_bound_Icc {d : ℕ} (hd : 2 ≤ d) {lo hi : ℝ}
    (hI : Set.Icc lo hi ⊆ Set.Ioo (0:ℝ) 1 \ {rStar d}) :
    ∃ C δ₀ : ℝ, 0 < C ∧ 0 < δ₀ ∧
      (∀ r ∈ Set.Icc lo hi, ∀ δ : ℝ, 0 < δ → δ < δ₀ →
        ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
          (X : Ω → ℝ), Measurable X → (∀ ω, X ω ∈ Set.Icc (0:ℝ) 1) →
          ∫ ω, X ω ∂μ = r - δ → r ^ d ≤ ∫ ω, X ω ^ d ∂μ →
          Jp (pcGlobal d r) r + C * δ ^ 2 ≤ ∫ ω, Jp (pcGlobal d r) (X ω) ∂μ) ∧
      (∀ {V : Type v} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj],
        (∀ x, H.degree x = d) → 1 ≤ H.edgeFinset.card →
        ∀ r ∈ Set.Icc lo hi, ∀ δ : ℝ, 0 < δ → δ < δ₀ → ∀ W : Graphon,
          W.edgeDensity = r - δ → r ^ H.edgeFinset.card ≤ W.tDensity H →
          Jp (pcGlobal d r) r + C * δ ^ 2 ≤ W.Ip (pcGlobal d r)) := by
  obtain ⟨C, δ₀, hC, hδ₀, hscalar⟩ := scalar_quadratic_bound_Icc.{u} hd hI
  refine ⟨C, δ₀, hC, hδ₀, hscalar, ?_⟩
  intro V _ _ H _ hreg hm r hr δ hδ hδ₀' W hWe hWt
  exact graphon_bound_of_scalar hd (hI hr).1.1.le
    (fun μ _ X => hscalar r hr δ hδ hδ₀' μ X) H hreg hm W hWe hWt

/-- **`lem:bipodal-quadratic-bound` (quadratic upper bound).**  For every small open interval
`I ∋ r₀` there are `C_{H,I} > 0` and `δ₀ > 0` such that for `r ∈ I` and `0 < δ < δ₀` some bipodal
graphon `V_δ` has `e(V_δ) = r - δ`, `t(H,V_δ) = r^m` and
`I_{pc(r)}(V_δ) ≤ J_{pc(r)}(r) + C_{H,I} δ²`. -/
theorem bipodal_quadratic_bound {d : ℕ} (hd : 2 ≤ d) {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (hreg : ∀ x, H.degree x = d)
    (hm : 1 ≤ H.edgeFinset.card) {r₀ : ℝ} (hr₀0 : 0 < r₀) (hr₀1 : r₀ < 1)
    (hr₀ : r₀ ≠ rStar d) :
    ∃ w : ℝ, 0 < w ∧ ∀ lo hi : ℝ, lo < r₀ → r₀ < hi → r₀ - w ≤ lo → hi ≤ r₀ + w →
      Set.Icc lo hi ⊆ Set.Ioo (0:ℝ) 1 \ {rStar d} ∧
      ∃ C δ₀ : ℝ, 0 < C ∧ 0 < δ₀ ∧
        ∀ r ∈ Set.Ioo lo hi, ∀ δ : ℝ, 0 < δ → δ < δ₀ →
          ∃ Vδ : Graphon, IsBipodal Vδ ∧ Vδ.edgeDensity = r - δ ∧
            Vδ.tDensity H = r ^ H.edgeFinset.card ∧
            Vδ.Ip (pcGlobal d r) ≤ Jp (pcGlobal d r) r + C * δ ^ 2 := by
  obtain ⟨M, w, hw, hwin⟩ := exists_arc_window hd hr₀0 hr₀1 hr₀
  refine ⟨w, hw, fun lo hi hlo hhi hwlo hwhi => ?_⟩
  obtain ⟨hK, -, hIcc⟩ := hwin lo hi hlo hhi hwlo hwhi
  have hKne : (Set.Icc lo hi).Nonempty := Set.nonempty_Icc.mpr (hlo.trans hhi).le
  obtain ⟨C, δ₀, hC, hδ₀, hup⟩ := quadratic_upper hd M hK isCompact_Icc hKne H hreg hm
  refine ⟨hIcc, C, δ₀, hC, hδ₀, fun r hr δ hδ hδ₀' => ?_⟩
  have hrK : r ∈ Set.Icc lo hi := Set.Ioo_subset_Icc_self hr
  obtain ⟨W, hWe, hWt, hWb, hWI⟩ := hup r hrK δ hδ hδ₀'
  rw [pcGlobal_eq_pc hd M (hK hrK)]
  exact ⟨W, hWb, hWe, hWt, hWI⟩

/-- **`thm:positive-second-variation` (universal positivity of the scalar second variation).**
For every small open interval `I ∋ r₀` there are `δ̄ > 0`, an open `𝒩 ⊇ I × (-δ̄, δ̄)` and a
real-analytic `G : 𝒩 → ℝ` with `G(r,δ) = G_r(δ) = I_{pc(r),r}(r-δ) - J_{pc(r)}(r)` for `r ∈ I`,
`0 < δ < δ̄`, such that, with `A_H(r) := ∂²_δG(r,0)`:

* (i) `G(r,0) = 0` and `∂_δG(r,0) = 0` for `r ∈ I`;
* (ii) `A_H` is real-analytic on `I` and `A_H ≥ a₀ > 0` there;
* (iii) `|∂²_δG(r,δ) - A_H(r)| ≤ C₂|δ|` for `r ∈ I`, `|δ| < δ̄`, with `C₂ ≥ 1`;
* (iv) `|G_r(δ) - ½A_H(r)δ²| ≤ C₃δ³` for `r ∈ I`, `0 < δ < δ̄`. -/
theorem positive_second_variation_interval {d : ℕ} (hd : 2 ≤ d) {V : Type*} [Fintype V]
    [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj] (hreg : ∀ x, H.degree x = d)
    (hm : 1 ≤ H.edgeFinset.card) {r₀ : ℝ} (hr₀0 : 0 < r₀) (hr₀1 : r₀ < 1)
    (hr₀ : r₀ ≠ rStar d) :
    ∃ w : ℝ, 0 < w ∧ ∀ lo hi : ℝ, lo < r₀ → r₀ < hi → r₀ - w ≤ lo → hi ≤ r₀ + w →
      Set.Icc lo hi ⊆ Set.Ioo (0:ℝ) 1 \ {rStar d} ∧
      ∃ (δbar : ℝ) (N : Set (ℝ × ℝ)) (G : ℝ × ℝ → ℝ),
        0 < δbar ∧ IsOpen N ∧ Set.Ioo lo hi ×ˢ Set.Ioo (-δbar) δbar ⊆ N ∧
        AnalyticOnNhd ℝ G N ∧
        -- `eq:boundary-excess-extension`
        (∀ r ∈ Set.Ioo lo hi, ∀ δ : ℝ, 0 < δ → δ < δbar →
          (G (r, δ) : EReal)
            = reducedObjective H (pcGlobal d r) r (r - δ) - (Jp (pcGlobal d r) r : EReal)) ∧
        -- (i)
        (∀ r ∈ Set.Ioo lo hi, G (r, 0) = 0 ∧ dDelta G (r, 0) = 0) ∧
        -- (ii)
        AnalyticOnNhd ℝ (fun r => dDelta (dDelta G) (r, 0)) (Set.Ioo lo hi) ∧
        (∃ a₀ : ℝ, 0 < a₀ ∧ ∀ r ∈ Set.Ioo lo hi, a₀ ≤ dDelta (dDelta G) (r, 0)) ∧
        -- (iii) `eq:boundary-excess-curvature`
        (∃ C₂ : ℝ, 1 ≤ C₂ ∧ ∀ r ∈ Set.Ioo lo hi, ∀ δ : ℝ, |δ| < δbar →
          |dDelta (dDelta G) (r, δ) - dDelta (dDelta G) (r, 0)| ≤ C₂ * |δ|) ∧
        -- (iv) `eq:boundary-excess-expansion`
        (∃ C₃ : ℝ, 0 ≤ C₃ ∧ ∀ r ∈ Set.Ioo lo hi, ∀ δ : ℝ, 0 < δ → δ < δbar →
          |G (r, δ) - dDelta (dDelta G) (r, 0) / 2 * δ ^ 2| ≤ C₃ * δ ^ 3) := by
  obtain ⟨M, w, hw, hwin⟩ := exists_arc_window hd hr₀0 hr₀1 hr₀
  refine ⟨w, hw, fun lo hi hlo hhi hwlo hwhi => ?_⟩
  obtain ⟨hK, hKex, hIcc⟩ := hwin lo hi hlo hhi hwlo hwhi
  have hKne : (Set.Icc lo hi).Nonempty := Set.nonempty_Icc.mpr (hlo.trans hhi).le
  obtain ⟨δbar, a₀, C₂, Ccub, N, G, hδbar, ha₀, hC₂, hCcub, hNopen, hNmem, hGana, hGagree,
    hG0, hAH, hd2G0, hcurv, hcubic⟩ :=
    positive_second_variation hd M hK isCompact_Icc hKne hKex H hreg hm
  -- a graphon with edge density `r - δ` and `H`-density `r^m`, so `I_{pc(r),r}(r-δ)` is finite
  obtain ⟨Cup, δ₀, -, hδ₀, hup⟩ := quadratic_upper hd M hK isCompact_Icc hKne H hreg hm
  -- on `I` the boundary curve of the arc is `pcGlobal`, and `∂²_δG(r,0) = A_H(r)`
  have hpc : ∀ r ∈ Set.Ioo lo hi, pcGlobal d r = M.pc r := fun r hr =>
    pcGlobal_eq_pc hd M (hK (Set.Ioo_subset_Icc_self hr))
  have hd2 : ∀ r ∈ Set.Ioo lo hi, dDelta (dDelta G) (r, 0) = AH H M r := fun r hr =>
    hd2G0 r (Set.Ioo_subset_Icc_self hr)
  have hδ1 : min δbar δ₀ ≤ δbar := min_le_left _ _
  have hδ2 : min δbar δ₀ ≤ δ₀ := min_le_right _ _
  have hreal : ∀ r ∈ Set.Ioo lo hi, ∀ δ : ℝ, 0 < δ → δ < min δbar δ₀ →
      G (r, δ) = reducedObjectiveReal H (pcGlobal d r) (r - δ) (r ^ H.edgeFinset.card)
        - Jp (pcGlobal d r) r := by
    intro r hr δ hδ0 hδb
    rw [hGagree r (Set.Ioo_subset_Icc_self hr) δ hδ0 (lt_of_lt_of_le hδb hδ1), boundaryExcess,
      hpc r hr]
  refine ⟨hIcc, min δbar δ₀, N, G, lt_min hδbar hδ₀, hNopen, ?_, hGana, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨r, δ⟩ ⟨hr, hδ⟩
    exact hNmem r (Set.Ioo_subset_Icc_self hr) δ
      (lt_of_lt_of_le (abs_lt.mpr hδ) hδ1)
  · intro r hr δ hδ0 hδb
    obtain ⟨W, hWe, hWt, -, -⟩ :=
      hup r (Set.Ioo_subset_Icc_self hr) δ hδ0 (lt_of_lt_of_le hδb hδ2)
    rw [reducedObjective_eq_coe H ⟨W, hWe, hWt⟩, ← EReal.coe_sub, hreal r hr δ hδ0 hδb]
  · exact fun r hr => hG0 r (Set.Ioo_subset_Icc_self hr)
  · -- `r ↦ ∂²_δG(r,0)` agrees with the analytic `A_H` on the open set `I`
    intro r hr
    refine (hAH r (Set.Ioo_subset_Icc_self hr)).1.congr ?_
    filter_upwards [isOpen_Ioo.mem_nhds hr] with z hz using (hd2 z hz).symm
  · exact ⟨a₀, ha₀, fun r hr => by
      rw [hd2 r hr]; exact (hAH r (Set.Ioo_subset_Icc_self hr)).2⟩
  · refine ⟨C₂, hC₂, fun r hr δ hδ => ?_⟩
    rw [hd2 r hr]
    exact hcurv r (Set.Ioo_subset_Icc_self hr) δ (lt_of_lt_of_le hδ hδ1)
  · refine ⟨Ccub, hCcub, fun r hr δ hδ0 hδb => ?_⟩
    have h := hcubic r (Set.Ioo_subset_Icc_self hr) δ hδ0 (lt_of_lt_of_le hδb hδ1)
    rw [boundaryExcess, ← hpc r hr, ← hreal r hr δ hδ0 hδb] at h
    rw [hd2 r hr, div_mul_eq_mul_div]
    exact h

end UpperTailOptimizers
