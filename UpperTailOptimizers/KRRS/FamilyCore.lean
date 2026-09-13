import UpperTailOptimizers.KRRS.Family
import UpperTailOptimizers.KRRS.BasePoint
import UpperTailOptimizers.KRRS.MaximizerStationary

/-!
# The analytic bipodal family of Appendix A

`krrs_rectangle` (`KRRS/Main.lean`) needs the two-sided analytic family of stationary bipodal
parameters and the fact that its bipodal graphon is the fixed-density entropy maximizer.  The
construction of the family needs a base point `a₀` with `F₁(ε₀,a₀,b₀,0) = 0`, which
`KRRS/BasePoint.lean` supplies explicitly.

This file packages the construction as the structure `KRRSFamily` and proves
`krrs_family_exists`.  Optimality of the family's graphon is isolated as
`KRRSFamily.IsOptimal`; it is proved in `Bipodality/Optimal.lean` (`KRRSFamily.isOptimal`),
and `krrs_rectangle_of_isOptimal` turns it into `krrs_rectangle`.

## Contents

* `exists_ball_pode_pos` — positive surplus forces a positive pode size near the base point;
* `KRRSFamily` — the family, its constraints, stationarity and local uniqueness;
* `krrs_family_exists` — the family exists (no project axiom);
* `KRRSFamily.IsOptimal` — optimality of the family's graphon;
* `krrs_rectangle_of_isOptimal` — the conclusion of `krrs_rectangle` from optimality.
-/

namespace UpperTailOptimizers

open MeasureTheory Real Filter Topology

/-- **Positive surplus forces a positive pode size.**  Near `(ε₀,a₀,b₀,0)` with `b₀ ≠ ε₀` the
`c`-derivative of `𝒯̂` is positive, so `c ↦ 𝒯̂(ε,a,b,c)` is increasing through `𝒯̂(ε,a,b,0) = ε^m`. -/
theorem exists_ball_pode_pos {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] {d : ℕ} (hd : 2 ≤ d) (hreg : ∀ v, H.degree v = d)
    (hm : 2 ≤ H.edgeFinset.card) {ε₀ a₀ b₀ : ℝ} (hε₀ : 0 < ε₀) (hb0 : 0 ≤ b₀)
    (hbε : b₀ ≠ ε₀) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ ε a b c ϑ : ℝ,
      ((ε, a, b, c) : ℝ × ℝ × ℝ × ℝ) ∈ Metric.ball ((ε₀, a₀, b₀, 0) : ℝ × ℝ × ℝ × ℝ) ρ →
      ((ε, a, b, 0) : ℝ × ℝ × ℝ × ℝ) ∈ Metric.ball ((ε₀, a₀, b₀, 0) : ℝ × ℝ × ℝ × ℝ) ρ →
      That H ε a b c = ε ^ H.edgeFinset.card + ϑ → 0 < ϑ → 0 < c := by
  set base : ℝ × ℝ × ℝ × ℝ := (ε₀, a₀, b₀, 0) with hbase
  have hcont : ContinuousAt
      (partialC (fun v : ℝ × ℝ × ℝ × ℝ => That H v.1 v.2.1 v.2.2.1 v.2.2.2)) base :=
    (analyticAt_partialSlot _ (analyticAt_That H (p := base) (by norm_num))).continuousAt
  have hpos0 : 0 < partialC (fun v : ℝ × ℝ × ℝ × ℝ => That H v.1 v.2.1 v.2.2.1 v.2.2.2) base := by
    rw [hbase, partialC_That_zero H hd hreg hm ε₀ a₀ b₀]
    exact Afun_pos H hd (by omega) hε₀ hb0 hbε
  obtain ⟨ρ₁, hρ₁, hball⟩ := Metric.eventually_nhds_iff.mp (hcont.eventually_mem (Ioi_mem_nhds hpos0))
  refine ⟨min ρ₁ (1 / 2), lt_min hρ₁ (by norm_num), ?_⟩
  intro ε a b c ϑ hw hw0 hT hϑ
  by_contra hcle
  push Not at hcle
  -- every `(ε,a,b,t)` with `t ∈ [c,0]` lies in the ball
  have hseg : ∀ t ∈ Set.Icc c 0, dist ((ε, a, b, t) : ℝ × ℝ × ℝ × ℝ) base < min ρ₁ (1 / 2) := by
    intro t ht
    have h1 := Metric.mem_ball.mp hw
    have h2 := Metric.mem_ball.mp hw0
    simp only [hbase, Prod.dist_eq, Real.dist_eq, sub_zero] at h1 h2 ⊢
    have htc : |t| ≤ |c| := by
      rw [abs_of_nonpos ht.2, abs_of_nonpos hcle]; linarith [ht.1]
    refine lt_of_le_of_lt ?_ h1
    exact max_le_max le_rfl (max_le_max le_rfl (max_le_max le_rfl htc))
  have hderiv : ∀ t ∈ Set.Icc c 0, HasDerivAt (fun x => That H ε a b x)
      (partialC (fun v : ℝ × ℝ × ℝ × ℝ => That H v.1 v.2.1 v.2.2.1 v.2.2.2) (ε, a, b, t)) t := by
    intro t ht
    have htlt : |t| < 1 / 2 := by
      have := hseg t ht
      simp only [hbase, Prod.dist_eq, Real.dist_eq, sub_zero] at this
      exact lt_of_le_of_lt (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
        (le_max_right _ _))) (lt_of_lt_of_le this (min_le_right _ _))
    have hne : ((ε, a, b, t) : ℝ × ℝ × ℝ × ℝ).2.2.2 ≠ 1 := by
      show t ≠ 1
      intro h; rw [h] at htlt; norm_num at htlt
    exact hasDerivAt_partialSlot (analyticAt_That H hne)
      ((hasDerivAt_const t ε).prodMk ((hasDerivAt_const t a).prodMk
        ((hasDerivAt_const t b).prodMk (hasDerivAt_id t)))) rfl
  have hmono : MonotoneOn (fun x => That H ε a b x) (Set.Icc c 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc c 0)
      (fun t ht => (hderiv t ht).continuousAt.continuousWithinAt)
      (fun t ht => ((hderiv t (interior_subset ht)).differentiableAt).differentiableWithinAt)
      (fun t ht => ?_)
    rw [(hderiv t (interior_subset ht)).deriv]
    have hmem := hseg t (interior_subset ht)
    exact le_of_lt (hball (lt_of_lt_of_le hmem (min_le_left _ _)))
  have hle := hmono (Set.left_mem_Icc.mpr hcle) (Set.right_mem_Icc.mpr hcle) hcle
  simp only [That_zero] at hle
  linarith

/-! ### The family -/

/-- **The two-sided analytic family of stationary bipodal parameters** around a nonexceptional
edge density `ε₀` (Appendix A, paragraphs 2–4), with the properties that the proof of
bipodality consumes.  The second-pode density is `Qmap ε (q11 ε ϑ) (q12 ε ϑ) (c ε ϑ)`. -/
structure KRRSFamily {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (d : ℕ) (ε₀ : ℝ) where
  U : Set ℝ
  Δ : ℝ
  q11 : ℝ → ℝ → ℝ
  q12 : ℝ → ℝ → ℝ
  c : ℝ → ℝ → ℝ
  isOpen_U : IsOpen U
  mem_U : ε₀ ∈ U
  Δ_pos : 0 < Δ
  analytic : ∀ ε ∈ U, ∀ ϑ : ℝ, |ϑ| < Δ →
    AnalyticAt ℝ (fun p : ℝ × ℝ => q11 p.1 p.2) (ε, ϑ) ∧
    AnalyticAt ℝ (fun p : ℝ × ℝ => q12 p.1 p.2) (ε, ϑ) ∧
    AnalyticAt ℝ (fun p : ℝ × ℝ => Qmap p.1 (q11 p.1 p.2) (q12 p.1 p.2) (c p.1 p.2)) (ε, ϑ) ∧
    AnalyticAt ℝ (fun p : ℝ × ℝ => c p.1 p.2) (ε, ϑ)
  /-- The degenerate boundary: `c = 0`, `q₁₂ = ζ_d(ε)`, `q₁₁ = a_d(ε)`. -/
  boundary : ∀ ε ∈ U,
    c ε 0 = 0 ∧ q11 ε 0 = baseA H d ε (zetaFun d ε) ∧ q12 ε 0 = zetaFun d ε
  interior : ∀ ε ∈ U, ∀ ϑ : ℝ, |ϑ| < Δ →
    ε ∈ Set.Ioo (0:ℝ) 1 ∧ ε ≠ rStar d ∧
    q11 ε ϑ ∈ Set.Ioo (0:ℝ) 1 ∧ q12 ε ϑ ∈ Set.Ioo (0:ℝ) 1 ∧
    Qmap ε (q11 ε ϑ) (q12 ε ϑ) (c ε ϑ) ∈ Set.Ioo (0:ℝ) 1 ∧ c ε ϑ < 1 ∧ q12 ε ϑ ≠ ε
  pode_pos : ∀ ε ∈ U, ∀ ϑ : ℝ, 0 < ϑ → ϑ < Δ → 0 < c ε ϑ
  density : ∀ ε ∈ U, ∀ ϑ : ℝ, |ϑ| < Δ →
    That H ε (q11 ε ϑ) (q12 ε ϑ) (c ε ϑ) = ε ^ H.edgeFinset.card + ϑ
  stationary : ∀ ε ∈ U, ∀ ϑ : ℝ, |ϑ| < Δ →
    F1 H d ε (q11 ε ϑ) (q12 ε ϑ) (c ε ϑ) = 0 ∧ F2 H d ε (q11 ε ϑ) (q12 ε ϑ) (c ε ϑ) = 0
  /-- Local uniqueness of stationary bipodal parameters: the certificate that identifies a
  bipodal maximizer with the family. -/
  localUnique : ∃ N : Set (ℝ × ℝ × ℝ × ℝ), IsOpen N ∧
    ((ε₀, q11 ε₀ 0, q12 ε₀ 0, 0) : ℝ × ℝ × ℝ × ℝ) ∈ N ∧
    ∀ ε ∈ U, ∀ ϑ : ℝ, |ϑ| < Δ → ∀ a b c' : ℝ,
      ((ε, a, b, c') : ℝ × ℝ × ℝ × ℝ) ∈ N → ((ε, a, b, ϑ) : ℝ × ℝ × ℝ × ℝ) ∈ N →
      That H ε a b c' = ε ^ H.edgeFinset.card + ϑ →
      F1 H d ε a b c' = 0 → F2 H d ε a b c' = 0 →
      a = q11 ε ϑ ∧ b = q12 ε ϑ ∧ c' = c ε ϑ

/-! ### Existence -/

/-- **The family exists, with no project axiom.**  The base point is `a₀ = baseA`, and the
boundary values are read off the stationarity equations at `ϑ = 0`. -/
theorem krrs_family_exists {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] {d : ℕ} (hd : 2 ≤ d) (hreg : ∀ v, H.degree v = d)
    (hm : 2 ≤ H.edgeFinset.card) {ε₀ : ℝ} (hε₀0 : 0 < ε₀) (hε₀1 : ε₀ < 1)
    (hε₀ : ε₀ ≠ rStar d) : Nonempty (KRRSFamily H d ε₀) := by
  classical
  have hε₀I : ε₀ ∈ Set.Ioo (0:ℝ) 1 := ⟨hε₀0, hε₀1⟩
  set b₀ : ℝ := zetaFun d ε₀ with hb₀def
  set a₀ : ℝ := baseA H d ε₀ b₀ with ha₀def
  have hb₀I : b₀ ∈ Set.Ioo (0:ℝ) 1 := zetaFun_mem hd hε₀I
  have ha₀I : a₀ ∈ Set.Ioo (0:ℝ) 1 := baseA_mem H d ε₀ b₀
  have hb₀ε : b₀ ≠ ε₀ := zetaFun_ne_self hd hε₀I hε₀
  have hb₀u : b₀ ≠ rStar d := by
    intro h
    apply hε₀
    have hinv := zetaFun_involutive hd hε₀I
    rw [← hb₀def, h, zetaFun_rStar hd] at hinv
    exact hinv.symm
  have hmaxψ : ∀ w, 0 < w → w < 1 → w ≠ ε₀ → psiD d ε₀ w ≤ psiD d ε₀ b₀ :=
    fun w hw0 hw1 hwne => zetaFun_isMax hd hε₀I w ⟨hw0, hw1⟩ hwne
  obtain ⟨Sc, Tc, C, hScopen, hScmem, hTcopen, hTcmem, hCana, -, hCcon, -, hCzeroS,
    hCzeroev, hCuniq⟩ := exists_C_chart (a₀ := a₀) H hd hreg hm hε₀0 hb₀I.1.le hb₀ε
  have hC000 : C ε₀ a₀ b₀ 0 = 0 := hCzeroev.self_of_nhds
  have hF1base : F1 H d ε₀ a₀ b₀ 0 = 0 :=
    F1_baseA H hd hreg hm hε₀0 hε₀1 hb₀I.1 hb₀I.2 hb₀ε
  obtain ⟨Sb, r, astar, bstar, hSbopen, hSbmem, hr0, hastar0, hbstar0, hastarana,
    hbstarana, hfam, hbuniq⟩ :=
    exists_stationary_family H hd hreg hm hε₀0 hε₀1 ha₀I.1 ha₀I.2 hb₀I.1 hb₀I.2 hb₀ε hb₀u
      hmaxψ hCana hCzeroev hF1base
  obtain ⟨ρ, hρ0, hpode⟩ := exists_ball_pode_pos (a₀ := a₀) H hd hreg hm hε₀0 hb₀I.1.le hb₀ε
  set base : ℝ × ℝ × ℝ × ℝ := (ε₀, a₀, b₀, 0) with hbase
  -- analyticity of the two derived maps at `(ε₀,0)`
  have hbaseval : ((fun w : ℝ × ℝ =>
      ((w.1, astar w.1 w.2, bstar w.1 w.2, w.2) : ℝ × ℝ × ℝ × ℝ)) ((ε₀, 0) : ℝ × ℝ)) = base := by
    show ((ε₀, astar ε₀ 0, bstar ε₀ 0, (0:ℝ)) : ℝ × ℝ × ℝ × ℝ) = base
    rw [hastar0, hbstar0]
  have hPana : AnalyticAt ℝ (fun w : ℝ × ℝ =>
      ((w.1, astar w.1 w.2, bstar w.1 w.2, w.2) : ℝ × ℝ × ℝ × ℝ)) ((ε₀, 0) : ℝ × ℝ) :=
    analyticAt_fst.prod (hastarana.prod (hbstarana.prod analyticAt_snd))
  have hcana : AnalyticAt ℝ
      (fun w : ℝ × ℝ => C w.1 (astar w.1 w.2) (bstar w.1 w.2) w.2) ((ε₀, 0) : ℝ × ℝ) :=
    hCana.fun_comp_of_eq hPana hbaseval
  have hcval : C ε₀ (astar ε₀ 0) (bstar ε₀ 0) 0 = 0 := by rw [hastar0, hbstar0]; exact hC000
  have hbaseval2 : ((fun w : ℝ × ℝ =>
      ((w.1, astar w.1 w.2, bstar w.1 w.2, C w.1 (astar w.1 w.2) (bstar w.1 w.2) w.2) :
        ℝ × ℝ × ℝ × ℝ)) ((ε₀, 0) : ℝ × ℝ)) = base := by
    show ((ε₀, astar ε₀ 0, bstar ε₀ 0, C ε₀ (astar ε₀ 0) (bstar ε₀ 0) 0) : ℝ × ℝ × ℝ × ℝ) = base
    rw [hcval, hastar0, hbstar0]
  have hqana : AnalyticAt ℝ (fun w : ℝ × ℝ => Qmap w.1 (astar w.1 w.2) (bstar w.1 w.2)
      (C w.1 (astar w.1 w.2) (bstar w.1 w.2) w.2)) ((ε₀, 0) : ℝ × ℝ) :=
    (analyticAt_Qmap (p := base) (by norm_num)).fun_comp_of_eq
      (analyticAt_fst.prod (hastarana.prod (hbstarana.prod hcana))) hbaseval2
  have hqval : Qmap ε₀ (astar ε₀ 0) (bstar ε₀ 0) (C ε₀ (astar ε₀ 0) (bstar ε₀ 0) 0) = ε₀ := by
    rw [hcval, Qmap_zero]
  have hP4c : Continuous (fun p : ℝ × ℝ => ((p.1, (0:ℝ)) : ℝ × ℝ)) := by fun_prop
  -- the curves through the base point
  have hcurve1 : ContinuousAt (fun p : ℝ × ℝ =>
      ((p.1, astar p.1 p.2, bstar p.1 p.2, C p.1 (astar p.1 p.2) (bstar p.1 p.2) p.2) :
        ℝ × ℝ × ℝ × ℝ)) ((ε₀, 0) : ℝ × ℝ) :=
    continuous_fst.continuousAt.prodMk (hastarana.continuousAt.prodMk
      (hbstarana.continuousAt.prodMk hcana.continuousAt))
  have hcurve2 : ContinuousAt (fun p : ℝ × ℝ =>
      ((p.1, astar p.1 p.2, bstar p.1 p.2, p.2) : ℝ × ℝ × ℝ × ℝ)) ((ε₀, 0) : ℝ × ℝ) :=
    hPana.continuousAt
  have hcurve3 : ContinuousAt (fun p : ℝ × ℝ =>
      ((p.1, astar p.1 p.2, bstar p.1 p.2, (0:ℝ)) : ℝ × ℝ × ℝ × ℝ)) ((ε₀, 0) : ℝ × ℝ) :=
    continuous_fst.continuousAt.prodMk (hastarana.continuousAt.prodMk
      (hbstarana.continuousAt.prodMk continuousAt_const))
  have hval3 : ((ε₀, astar ε₀ 0, bstar ε₀ 0, (0:ℝ)) : ℝ × ℝ × ℝ × ℝ) = base := by
    rw [hastar0, hbstar0]
  have hN : IsOpen (Sc ∩ Tc ∩ Sb) := (hScopen.inter hTcopen).inter hSbopen
  have hbN : base ∈ Sc ∩ Tc ∩ Sb := ⟨⟨hScmem, hTcmem⟩, hSbmem⟩
  have hev : ∀ᶠ p in 𝓝 ((ε₀ : ℝ), (0:ℝ)),
      (AnalyticAt ℝ (fun w : ℝ × ℝ => astar w.1 w.2) ((p.1, p.2) : ℝ × ℝ) ∧
      AnalyticAt ℝ (fun w : ℝ × ℝ => bstar w.1 w.2) ((p.1, p.2) : ℝ × ℝ) ∧
      AnalyticAt ℝ (fun w : ℝ × ℝ => Qmap w.1 (astar w.1 w.2) (bstar w.1 w.2)
        (C w.1 (astar w.1 w.2) (bstar w.1 w.2) w.2)) ((p.1, p.2) : ℝ × ℝ) ∧
      AnalyticAt ℝ (fun w : ℝ × ℝ => C w.1 (astar w.1 w.2) (bstar w.1 w.2) w.2)
        ((p.1, p.2) : ℝ × ℝ)) ∧
      (astar p.1 p.2 ∈ Set.Ioo (0:ℝ) 1 ∧ bstar p.1 p.2 ∈ Set.Ioo (0:ℝ) 1 ∧
      Qmap p.1 (astar p.1 p.2) (bstar p.1 p.2)
        (C p.1 (astar p.1 p.2) (bstar p.1 p.2) p.2) ∈ Set.Ioo (0:ℝ) 1 ∧
      C p.1 (astar p.1 p.2) (bstar p.1 p.2) p.2 < 1 ∧ bstar p.1 p.2 ≠ p.1) ∧
      (((p.1, astar p.1 p.2, bstar p.1 p.2, (0:ℝ)) : ℝ × ℝ × ℝ × ℝ) ∈ Sc ∧
      ((p.1, astar p.1 p.2, bstar p.1 p.2, p.2) : ℝ × ℝ × ℝ × ℝ) ∈ Tc ∧
      ((p.1, astar p.1 p.2, bstar p.1 p.2, C p.1 (astar p.1 p.2) (bstar p.1 p.2) p.2) :
        ℝ × ℝ × ℝ × ℝ) ∈ Metric.ball base ρ ∧
      ((p.1, astar p.1 p.2, bstar p.1 p.2, (0:ℝ)) : ℝ × ℝ × ℝ × ℝ) ∈ Metric.ball base ρ) ∧
      (p.1 ∈ Set.Ioo (0:ℝ) 1 ∧ p.1 ≠ rStar d) := by
    have e5 := hastarana.continuousAt.eventually_mem
      (isOpen_Ioo.mem_nhds (by show astar ε₀ 0 ∈ Set.Ioo (0:ℝ) 1; rw [hastar0]; exact ha₀I))
    have e6 := hbstarana.continuousAt.eventually_mem
      (isOpen_Ioo.mem_nhds (by show bstar ε₀ 0 ∈ Set.Ioo (0:ℝ) 1; rw [hbstar0]; exact hb₀I))
    have e9 := hqana.continuousAt.eventually_mem (isOpen_Ioo.mem_nhds
      (by show Qmap ε₀ (astar ε₀ 0) (bstar ε₀ 0) (C ε₀ (astar ε₀ 0) (bstar ε₀ 0) 0)
            ∈ Set.Ioo (0:ℝ) 1
          rw [hqval]; exact hε₀I))
    have e8 := hcana.continuousAt.eventually_mem (Iio_mem_nhds
      (by show C ε₀ (astar ε₀ 0) (bstar ε₀ 0) 0 < 1; rw [hcval]; norm_num))
    have e10 : ∀ᶠ p in 𝓝 ((ε₀ : ℝ), (0:ℝ)), bstar p.1 p.2 - p.1 ≠ 0 := by
      refine (hbstarana.continuousAt.sub continuous_fst.continuousAt).eventually_ne ?_
      show bstar ε₀ 0 - ε₀ ≠ 0
      rw [hbstar0]; exact sub_ne_zero.mpr hb₀ε
    have e7 := hcurve3.eventually_mem (hScopen.mem_nhds
      (by show ((ε₀, astar ε₀ 0, bstar ε₀ 0, (0:ℝ)) : ℝ × ℝ × ℝ × ℝ) ∈ Sc
          rw [hval3]; exact hScmem))
    have e13 := hcurve2.eventually_mem (hTcopen.mem_nhds
      (by show ((ε₀, astar ε₀ 0, bstar ε₀ 0, (0:ℝ)) : ℝ × ℝ × ℝ × ℝ) ∈ Tc
          rw [hval3]; exact hTcmem))
    have e14 := hcurve1.eventually_mem (Metric.isOpen_ball.mem_nhds
      (by show ((ε₀, astar ε₀ 0, bstar ε₀ 0, C ε₀ (astar ε₀ 0) (bstar ε₀ 0) 0) :
              ℝ × ℝ × ℝ × ℝ) ∈ Metric.ball base ρ
          rw [hcval, hastar0, hbstar0]; exact Metric.mem_ball_self hρ0))
    have e15 := hcurve3.eventually_mem (Metric.isOpen_ball.mem_nhds
      (by show ((ε₀, astar ε₀ 0, bstar ε₀ 0, (0:ℝ)) : ℝ × ℝ × ℝ × ℝ) ∈ Metric.ball base ρ
          rw [hval3]; exact Metric.mem_ball_self hρ0))
    have e11 : ∀ᶠ p in 𝓝 ((ε₀ : ℝ), (0:ℝ)), p.1 ∈ Set.Ioo (0:ℝ) 1 :=
      continuous_fst.continuousAt.eventually_mem (isOpen_Ioo.mem_nhds hε₀I)
    have e12 : ∀ᶠ p in 𝓝 ((ε₀ : ℝ), (0:ℝ)), p.1 ≠ rStar d :=
      continuous_fst.continuousAt.eventually_ne hε₀
    filter_upwards [hastarana.eventually_analyticAt, hbstarana.eventually_analyticAt,
      hqana.eventually_analyticAt, hcana.eventually_analyticAt, e5, e6, e9, e8, e10, e7, e13,
      e14, e15, e11, e12] with p h1 h2 h3 h4 h5 h6 h9 h8 h10 h7 h13 h14 h15 h11 h12
    exact ⟨⟨h1, h2, h3, h4⟩, ⟨h5, h6, h9, h8, sub_ne_zero.mp h10⟩, ⟨h7, h13, h14, h15⟩,
      ⟨h11, h12⟩⟩
  obtain ⟨a₁, Δ₁, ha₁, hΔ₁, hrect⟩ := exists_rect (x₀ := ε₀) (P := fun x y =>
      (AnalyticAt ℝ (fun w : ℝ × ℝ => astar w.1 w.2) ((x, y) : ℝ × ℝ) ∧
      AnalyticAt ℝ (fun w : ℝ × ℝ => bstar w.1 w.2) ((x, y) : ℝ × ℝ) ∧
      AnalyticAt ℝ (fun w : ℝ × ℝ => Qmap w.1 (astar w.1 w.2) (bstar w.1 w.2)
        (C w.1 (astar w.1 w.2) (bstar w.1 w.2) w.2)) ((x, y) : ℝ × ℝ) ∧
      AnalyticAt ℝ (fun w : ℝ × ℝ => C w.1 (astar w.1 w.2) (bstar w.1 w.2) w.2)
        ((x, y) : ℝ × ℝ)) ∧
      (astar x y ∈ Set.Ioo (0:ℝ) 1 ∧ bstar x y ∈ Set.Ioo (0:ℝ) 1 ∧
      Qmap x (astar x y) (bstar x y)
        (C x (astar x y) (bstar x y) y) ∈ Set.Ioo (0:ℝ) 1 ∧
      C x (astar x y) (bstar x y) y < 1 ∧ bstar x y ≠ x) ∧
      (((x, astar x y, bstar x y, (0:ℝ)) : ℝ × ℝ × ℝ × ℝ) ∈ Sc ∧
      ((x, astar x y, bstar x y, y) : ℝ × ℝ × ℝ × ℝ) ∈ Tc ∧
      ((x, astar x y, bstar x y, C x (astar x y) (bstar x y) y) :
        ℝ × ℝ × ℝ × ℝ) ∈ Metric.ball base ρ ∧
      ((x, astar x y, bstar x y, (0:ℝ)) : ℝ × ℝ × ℝ × ℝ) ∈ Metric.ball base ρ) ∧
      (x ∈ Set.Ioo (0:ℝ) 1 ∧ x ≠ rStar d)) hev
  set a : ℝ := min a₁ r with hadef
  set Δ : ℝ := min Δ₁ r with hΔdef
  have ha0 : 0 < a := lt_min ha₁ hr0
  have hΔ0 : 0 < Δ := lt_min hΔ₁ hr0
  have hwin : ∀ ε ∈ Set.Ioo (ε₀ - a) (ε₀ + a), ∀ ϑ : ℝ, |ϑ| < Δ →
      |ε - ε₀| < a₁ ∧ |ϑ| < Δ₁ ∧ |ε - ε₀| < r ∧ |ϑ| < r := by
    intro ε hε ϑ hϑ
    have h1 : |ε - ε₀| < a := abs_lt.mpr ⟨by linarith [hε.1], by linarith [hε.2]⟩
    exact ⟨lt_of_lt_of_le h1 (min_le_left _ _), lt_of_lt_of_le hϑ (min_le_left _ _),
      lt_of_lt_of_le h1 (min_le_right _ _), lt_of_lt_of_le hϑ (min_le_right _ _)⟩
  have hV : 0 < (Fintype.card V : ℝ) := by
    have : Nonempty V := nonempty_of_edge H (by omega)
    exact_mod_cast Fintype.card_pos
  refine ⟨{
    U := Set.Ioo (ε₀ - a) (ε₀ + a)
    Δ := Δ
    q11 := astar
    q12 := bstar
    c := fun x y => C x (astar x y) (bstar x y) y
    isOpen_U := isOpen_Ioo
    mem_U := ⟨by linarith, by linarith⟩
    Δ_pos := hΔ0
    analytic := fun ε hε ϑ hϑ => (hrect ε (hwin ε hε ϑ hϑ).1 ϑ (hwin ε hε ϑ hϑ).2.1).1
    boundary := ?_
    interior := fun ε hε ϑ hϑ => by
      obtain ⟨-, ⟨h5, h6, h9, h8, h10⟩, -, ⟨h11, h12⟩⟩ :=
        hrect ε (hwin ε hε ϑ hϑ).1 ϑ (hwin ε hε ϑ hϑ).2.1
      exact ⟨h11, h12, h5, h6, h9, h8, h10⟩
    pode_pos := fun ε hε ϑ hϑ0 hϑΔ => by
      have hϑ : |ϑ| < Δ := by rw [abs_of_pos hϑ0]; exact hϑΔ
      obtain ⟨-, -, ⟨-, h13, h14, h15⟩, -⟩ :=
        hrect ε (hwin ε hε ϑ hϑ).1 ϑ (hwin ε hε ϑ hϑ).2.1
      exact hpode ε (astar ε ϑ) (bstar ε ϑ) _ ϑ h14 h15
        (hCcon ε (astar ε ϑ) (bstar ε ϑ) ϑ h13) hϑ0
    density := fun ε hε ϑ hϑ => by
      obtain ⟨-, -, ⟨-, h13, -, -⟩, -⟩ := hrect ε (hwin ε hε ϑ hϑ).1 ϑ (hwin ε hε ϑ hϑ).2.1
      exact hCcon ε (astar ε ϑ) (bstar ε ϑ) ϑ h13
    stationary := fun ε hε ϑ hϑ =>
      (hfam ε ϑ (hwin ε hε ϑ hϑ).2.2.1 (hwin ε hε ϑ hϑ).2.2.2).2
    localUnique := ?_ }⟩
  · intro ε hε
    have hϑ : |(0:ℝ)| < Δ := by rw [abs_zero]; exact hΔ0
    obtain ⟨-, ⟨h5, h6, -, -, h10⟩, ⟨h7, -, -, -⟩, ⟨h11, -⟩⟩ :=
      hrect ε (hwin ε hε 0 hϑ).1 0 (hwin ε hε 0 hϑ).2.1
    have hC0 : C ε (astar ε 0) (bstar ε 0) 0 = 0 := hCzeroS ε (astar ε 0) (bstar ε 0) h7
    obtain ⟨hF1, hF2⟩ := (hfam ε 0 (hwin ε hε 0 hϑ).2.2.1 (hwin ε hε 0 hϑ).2.2.2).2
    rw [hC0] at hF1 hF2
    rw [F2_zero_eq H hd hreg hm h11.1 h11.2 h5.1 h5.2 h6.1 h6.2] at hF2
    have hpow : (0:ℝ) < ε ^ (H.edgeFinset.card - d) := pow_pos h11.1 _
    have hWr : Wr d ε (bstar ε 0) = 0 := by
      rcases mul_eq_zero.mp hF2 with h | h
      · exact absurd h (ne_of_gt (mul_pos hV hpow))
      · exact h
    have hbz : bstar ε 0 = zetaFun d ε := zetaFun_eq_of_crit hd h11 h6 h10 hWr
    refine ⟨hC0, ?_, hbz⟩
    rw [← hbz]
    exact eq_baseA_of_F1 H hd hreg hm h11.1 h11.2 h5.1 h5.2 h6.1 h6.2 h10 hF1
  · refine ⟨Sc ∩ Tc ∩ Sb, hN, ?_, ?_⟩
    · show ((ε₀, astar ε₀ 0, bstar ε₀ 0, (0:ℝ)) : ℝ × ℝ × ℝ × ℝ) ∈ Sc ∩ Tc ∩ Sb
      rw [hval3]; exact hbN
    · intro ε hε ϑ hϑ a' b' c' hN1 hN2 hT hF1 hF2
      have hc' : c' = C ε a' b' ϑ := hCuniq ε a' b' c' ϑ hN1.1.1 hN2.1.2 hT
      rw [hc'] at hF1 hF2
      obtain ⟨ha', hb'⟩ := hbuniq ε a' b' ϑ hN2.2 (hwin ε hε ϑ hϑ).2.2.1
        (hwin ε hε ϑ hϑ).2.2.2 hF1 hF2
      refine ⟨ha', hb', ?_⟩
      show c' = C ε (astar ε ϑ) (bstar ε ϑ) ϑ
      rw [hc', ← ha', ← hb']

namespace KRRSFamily

variable {V : Type*} [Fintype V] [DecidableEq V] {H : SimpleGraph V} [DecidableRel H.Adj]
  {d : ℕ} {ε₀ : ℝ}

/-- The bipodal graphon of the family (parameters clamped to `[0,1]`, which changes nothing
inside the window). -/
noncomputable def graphon (F : KRRSFamily H d ε₀) (ε ϑ : ℝ) : Graphon :=
  bipodalGraphon (Set.Icc 0 (Set.projIcc (0:ℝ) 1 zero_le_one (F.c ε ϑ)))
    measurableSet_Icc
    (Set.projIcc (0:ℝ) 1 zero_le_one (F.q11 ε ϑ))
    (Set.projIcc (0:ℝ) 1 zero_le_one (F.q12 ε ϑ))
    (Set.projIcc (0:ℝ) 1 zero_le_one (Qmap ε (F.q11 ε ϑ) (F.q12 ε ϑ) (F.c ε ϑ)))
    (Set.projIcc (0:ℝ) 1 zero_le_one _).2 (Set.projIcc (0:ℝ) 1 zero_le_one _).2
    (Set.projIcc (0:ℝ) 1 zero_le_one _).2

/-- **Optimality of the family**: on a smaller window, the family's bipodal graphon is the
fixed-density entropy maximizer, unique up to relabelling (proved as `KRRSFamily.isOptimal`). -/
def IsOptimal (F : KRRSFamily H d ε₀) : Prop :=
  ∃ U' : Set ℝ, IsOpen U' ∧ ε₀ ∈ U' ∧ U' ⊆ F.U ∧ ∃ Δ' : ℝ, 0 < Δ' ∧ Δ' ≤ F.Δ ∧
    ∀ ε ∈ U', ∀ ϑ : ℝ, 0 < ϑ → ϑ < Δ' →
      ∀ W : Graphon, W.edgeDensity = ε → W.tDensity H = ε ^ H.edgeFinset.card + ϑ →
        W.entropy ≤ (F.graphon ε ϑ).entropy ∧
        (W.entropy = (F.graphon ε ϑ).entropy → ∃ σ : ℝ → ℝ, IsRelabelling σ ∧
          ∀ᵐ z ∂gμ, W.toFun z.1 z.2 = (F.graphon ε ϑ).toFun (σ z.1) (σ z.2))

/-- Inside the positive-surplus window the family's graphon is the bipodal graphon with its
parameters, with edge density `ε` and `H`-density `ε^m + ϑ`. -/
theorem graphon_spec (F : KRRSFamily H d ε₀) {ε ϑ : ℝ} (hε : ε ∈ F.U) (hϑ0 : 0 < ϑ)
    (hϑΔ : ϑ < F.Δ) :
    F.q11 ε ϑ ∈ Set.Ioo (0:ℝ) 1 ∧ F.q12 ε ϑ ∈ Set.Ioo (0:ℝ) 1 ∧
    Qmap ε (F.q11 ε ϑ) (F.q12 ε ϑ) (F.c ε ϑ) ∈ Set.Ioo (0:ℝ) 1 ∧
    F.c ε ϑ ∈ Set.Ioo (0:ℝ) 1 ∧
    (∀ z : ℝ × ℝ, (F.graphon ε ϑ).toFun z.1 z.2
      = bipodalValue (Set.Icc 0 (F.c ε ϑ)) (F.q11 ε ϑ) (F.q12 ε ϑ)
          (Qmap ε (F.q11 ε ϑ) (F.q12 ε ϑ) (F.c ε ϑ)) z) ∧
    (F.graphon ε ϑ).edgeDensity = ε ∧
    (F.graphon ε ϑ).tDensity H = ε ^ H.edgeFinset.card + ϑ := by
  have hϑ : |ϑ| < F.Δ := by rw [abs_of_pos hϑ0]; exact hϑΔ
  obtain ⟨-, -, h11, h12, h22, hc1, -⟩ := F.interior ε hε ϑ hϑ
  have hc0 := F.pode_pos ε hε ϑ hϑ0 hϑΔ
  have hval : ∀ z : ℝ × ℝ, (F.graphon ε ϑ).toFun z.1 z.2
      = bipodalValue (Set.Icc 0 (F.c ε ϑ)) (F.q11 ε ϑ) (F.q12 ε ϑ)
          (Qmap ε (F.q11 ε ϑ) (F.q12 ε ϑ) (F.c ε ϑ)) z := by
    intro z
    simp only [graphon, bipodalGraphon_apply,
      Set.projIcc_of_mem (zero_le_one) ⟨h11.1.le, h11.2.le⟩,
      Set.projIcc_of_mem (zero_le_one) ⟨h12.1.le, h12.2.le⟩,
      Set.projIcc_of_mem (zero_le_one) ⟨h22.1.le, h22.2.le⟩,
      Set.projIcc_of_mem (zero_le_one) ⟨hc0.le, hc1.le⟩]
  have hae : ∀ᵐ z ∂gμ, (F.graphon ε ϑ).toFun z.1 z.2
      = bipodalValue (Set.Icc 0
          ((F.q11 ε ϑ, F.q12 ε ϑ, Qmap ε (F.q11 ε ϑ) (F.q12 ε ϑ) (F.c ε ϑ), F.c ε ϑ) : Theta).2.2.2)
          ((F.q11 ε ϑ, F.q12 ε ϑ, Qmap ε (F.q11 ε ϑ) (F.q12 ε ϑ) (F.c ε ϑ), F.c ε ϑ) : Theta).1
          ((F.q11 ε ϑ, F.q12 ε ϑ, Qmap ε (F.q11 ε ϑ) (F.q12 ε ϑ) (F.c ε ϑ), F.c ε ϑ) : Theta).2.1
          ((F.q11 ε ϑ, F.q12 ε ϑ, Qmap ε (F.q11 ε ϑ) (F.q12 ε ϑ) (F.c ε ϑ), F.c ε ϑ) : Theta).2.2.1
          (id z.1, id z.2) :=
    Filter.Eventually.of_forall (fun z => by simpa using hval z)
  have htr := bipodal_transfer H
    (θ := ((F.q11 ε ϑ, F.q12 ε ϑ, Qmap ε (F.q11 ε ϑ) (F.q12 ε ϑ) (F.c ε ϑ), F.c ε ϑ) : Theta))
    ⟨h11.1.le, h11.2.le⟩ ⟨h12.1.le, h12.2.le⟩ ⟨h22.1.le, h22.2.le⟩ ⟨hc0.le, hc1.le⟩
    isRelabelling_id hae
  refine ⟨h11, h12, h22, ⟨hc0, hc1⟩, hval, ?_, ?_⟩
  · rw [htr.1]; exact bipEdge_Qmap (ne_of_lt hc1)
  · rw [htr.2.1, ← That_eq_bipTd]; exact F.density ε hε ϑ hϑ

end KRRSFamily

/-! ### From optimality of the family to `krrs_rectangle` -/

/-- **`krrs_rectangle` from `IsOptimal`.**  Once every family is optimal, the full conclusion of
`krrs_rectangle` follows with no further input. -/
theorem krrs_rectangle_of_isOptimal {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] {d : ℕ} (hd : 2 ≤ d) (hreg : ∀ v, H.degree v = d)
    (hm : 2 ≤ H.edgeFinset.card) {ε₀ : ℝ} (hε₀0 : 0 < ε₀) (hε₀1 : ε₀ < 1)
    (hε₀ : ε₀ ≠ rStar d) (hT : ∀ F : KRRSFamily H d ε₀, F.IsOptimal) :
    ∃ (U : Set ℝ) (Δ : ℝ) (q11 q12 q22 c : ℝ → ℝ → ℝ), IsOpen U ∧ ε₀ ∈ U ∧ 0 < Δ ∧
      (∀ ε ∈ U, ∀ ϑ : ℝ, |ϑ| < Δ →
        AnalyticAt ℝ (fun p : ℝ × ℝ => q11 p.1 p.2) (ε, ϑ) ∧
        AnalyticAt ℝ (fun p : ℝ × ℝ => q12 p.1 p.2) (ε, ϑ) ∧
        AnalyticAt ℝ (fun p : ℝ × ℝ => q22 p.1 p.2) (ε, ϑ) ∧
        AnalyticAt ℝ (fun p : ℝ × ℝ => c p.1 p.2) (ε, ϑ)) ∧
      (∀ ε ∈ U, c ε 0 = 0 ∧ q22 ε 0 = ε ∧
        q11 ε 0 ∈ Set.Ioo (0:ℝ) 1 ∧ q12 ε 0 ∈ Set.Ioo (0:ℝ) 1 ∧ q12 ε 0 ≠ ε ∧
        (∀ w ∈ Set.Ioo (0:ℝ) 1, w ≠ ε → psiD d ε w ≤ psiD d ε (q12 ε 0))) ∧
      (∀ ε ∈ U, ∀ τ : ℝ, 0 < τ - ε ^ H.edgeFinset.card →
        τ - ε ^ H.edgeFinset.card < Δ →
        q11 ε (τ - ε ^ H.edgeFinset.card) ∈ Set.Ioo (0:ℝ) 1 ∧
        q12 ε (τ - ε ^ H.edgeFinset.card) ∈ Set.Ioo (0:ℝ) 1 ∧
        q22 ε (τ - ε ^ H.edgeFinset.card) ∈ Set.Ioo (0:ℝ) 1 ∧
        c ε (τ - ε ^ H.edgeFinset.card) ∈ Set.Ioo (0:ℝ) 1 ∧
        ∃ W : Graphon, W.edgeDensity = ε ∧ W.tDensity H = τ ∧ IsBipodal W ∧
          (∀ᵐ z ∂gμ, W.toFun z.1 z.2
            = bipodalValue (Set.Icc 0 (c ε (τ - ε ^ H.edgeFinset.card)))
                (q11 ε (τ - ε ^ H.edgeFinset.card))
                (q12 ε (τ - ε ^ H.edgeFinset.card))
                (q22 ε (τ - ε ^ H.edgeFinset.card)) z) ∧
          (∀ W' : Graphon, W'.edgeDensity = ε → W'.tDensity H = τ →
            W'.entropy ≤ W.entropy) ∧
          (∀ W' : Graphon, W'.edgeDensity = ε → W'.tDensity H = τ →
            W'.entropy = W.entropy →
            ∃ σ : ℝ → ℝ, IsRelabelling σ ∧
              ∀ᵐ z ∂gμ, W'.toFun z.1 z.2 = W.toFun (σ z.1) (σ z.2))) := by
  obtain ⟨F⟩ := krrs_family_exists H hd hreg hm hε₀0 hε₀1 hε₀
  obtain ⟨U', hU'open, hε₀U', hU'sub, Δ', hΔ'0, hΔ'le, hopt⟩ := hT F
  refine ⟨U', Δ', F.q11, F.q12, fun x y => Qmap x (F.q11 x y) (F.q12 x y) (F.c x y), F.c,
    hU'open, hε₀U', hΔ'0, ?_, ?_, ?_⟩
  · intro ε hε ϑ hϑ
    exact F.analytic ε (hU'sub hε) ϑ (lt_of_lt_of_le hϑ hΔ'le)
  · intro ε hε
    have hεF := hU'sub hε
    have h0 : |(0:ℝ)| < F.Δ := by rw [abs_zero]; exact F.Δ_pos
    obtain ⟨hεI, -, h11, h12, -, -, hne⟩ := F.interior ε hεF 0 h0
    obtain ⟨hc0, -, hz⟩ := F.boundary ε hεF
    refine ⟨hc0, ?_, h11, h12, hne, ?_⟩
    · show Qmap ε (F.q11 ε 0) (F.q12 ε 0) (F.c ε 0) = ε
      rw [hc0, Qmap_zero]
    · intro w hw hwne
      rw [hz]
      exact zetaFun_isMax hd hεI w hw hwne
  · intro ε hε τ hs0 hsΔ
    have hεF := hU'sub hε
    obtain ⟨h11, h12, h22, hc, hval, he, ht⟩ :=
      F.graphon_spec hεF hs0 (lt_of_lt_of_le hsΔ hΔ'le)
    have hτ : ε ^ H.edgeFinset.card + (τ - ε ^ H.edgeFinset.card) = τ := by ring
    refine ⟨h11, h12, h22, hc, F.graphon ε (τ - ε ^ H.edgeFinset.card), he, by rw [ht, hτ],
      ⟨Set.Icc 0 (F.c ε (τ - ε ^ H.edgeFinset.card)), _, _, _, measurableSet_Icc,
        ⟨h11.1.le, h11.2.le⟩, ⟨h12.1.le, h12.2.le⟩, ⟨h22.1.le, h22.2.le⟩,
        Filter.Eventually.of_forall hval⟩,
      Filter.Eventually.of_forall hval, ?_, ?_⟩
    · intro W' h1 h2
      exact (hopt ε hε _ hs0 hsΔ W' h1 (by rw [h2, hτ])).1
    · intro W' h1 h2 h3
      exact (hopt ε hε _ hs0 hsΔ W' h1 (by rw [h2, hτ])).2 h3

end UpperTailOptimizers
