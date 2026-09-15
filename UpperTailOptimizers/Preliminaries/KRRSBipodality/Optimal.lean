import UpperTailOptimizers.Preliminaries.KRRSBipodality.BipodalUniform
import UpperTailOptimizers.Preliminaries.KRRSBipodality.Existence

/-!
# The analytic family is optimal

Every entropy maximizer at `(ε, ε^m + ϑ)` close to the degenerate boundary is bipodal with a
small first pode, second-pode density near `ζ_d(ε)` and first-pode density in a fixed compact
subset of `(0,1)` (`KRRSFamily.exists_bipodal`).  Its parameters are then stationary for the
reduced problem (`F_eq_zero_of_maximizer`, with the pode-size chart taken at the relevant
first-pode density — a compactness argument makes this uniform), and since `F₁(ε₀,a,ζ_d(ε₀),0)`
vanishes only at `a = a_d(ε₀)` (`eq_baseA_of_F1`), the first-pode density is close to `a_d(ε₀)`.
The local uniqueness certificate of the family then identifies the maximizer with the family's
graphon (draft `kb:sec:ident`).

## Contents

* `eventually_bipodal_stationary` — stationarity of bipodal maximizers, uniformly in `a`;
* `eventually_F1_ne_zero` — `F₁ ≠ 0` away from `a_d(ε₀)`, uniformly;
* **`KRRSFamily.isOptimal`** — KRR–S Theorem 1.1 (`thm:krrs-bipodality`) for `d`-regular `H`.
-/

set_option linter.unusedSectionVars false

namespace UpperTailOptimizers

open MeasureTheory Set Filter Topology

section Stationary

variable {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]

/-- **Stationarity of bipodal maximizers near the boundary, uniformly in the first pode.** -/
theorem eventually_bipodal_stationary {d : ℕ} (hd : 2 ≤ d) (hreg : ∀ v, H.degree v = d)
    (hm : 2 ≤ H.edgeFinset.card) {ε₀ b₀ : ℝ} (hε₀ : ε₀ ∈ Ioo (0:ℝ) 1) (hb₀ : b₀ ∈ Ioo (0:ℝ) 1)
    (hb₀ε : b₀ ≠ ε₀) {K : Set ℝ} (hK : IsCompact K) (hKsub : K ⊆ Ioo (0:ℝ) 1) :
    ∀ᶠ p in 𝓝 ((ε₀, b₀, 0, 0) : ℝ × ℝ × ℝ × ℝ), ∀ a ∈ K, ∀ q : ℝ, q ∈ Ioo (0:ℝ) 1 →
      0 ≤ p.2.2.1 → 0 < p.2.2.2 → ∀ W : Graphon,
      IsMaximizer H W p.1 (p.1 ^ H.edgeFinset.card + p.2.2.2) →
      (∀ᵐ z ∂gμ, W.toFun z.1 z.2 = bipodalValue (Icc 0 p.2.2.1) a p.2.1 q z) →
      F1 H d p.1 a p.2.1 p.2.2.1 = 0 ∧ F2 H d p.1 a p.2.1 p.2.2.1 = 0 := by
  refine hK.eventually_forall_of_forall_eventually fun a ha => ?_
  obtain ⟨S, T, C, hSo, hSm, hTo, hTm, hCana, -, hCcon, -, -, -, hCuniq⟩ :=
    exists_C_chart (a₀ := a) H hd hreg hm hε₀.1 hb₀.1.le hb₀ε
  have hφ : Continuous fun z : (ℝ × ℝ × ℝ × ℝ) × ℝ =>
      ((z.1.1, z.2, z.1.2.1, z.1.2.2.1) : ℝ × ℝ × ℝ × ℝ) := by fun_prop
  have hψ : Continuous fun z : (ℝ × ℝ × ℝ × ℝ) × ℝ =>
      ((z.1.1, z.2, z.1.2.1, z.1.2.2.2) : ℝ × ℝ × ℝ × ℝ) := by fun_prop
  have e1 : ∀ᶠ z : (ℝ × ℝ × ℝ × ℝ) × ℝ in 𝓝 (((ε₀, b₀, 0, 0) : ℝ × ℝ × ℝ × ℝ), a),
      ((z.1.1, z.2, z.1.2.1, z.1.2.2.1) : ℝ × ℝ × ℝ × ℝ) ∈ S :=
    hφ.continuousAt.eventually_mem (hSo.mem_nhds hSm)
  have e2 : ∀ᶠ z : (ℝ × ℝ × ℝ × ℝ) × ℝ in 𝓝 (((ε₀, b₀, 0, 0) : ℝ × ℝ × ℝ × ℝ), a),
      ((z.1.1, z.2, z.1.2.1, z.1.2.2.2) : ℝ × ℝ × ℝ × ℝ) ∈ T :=
    hψ.continuousAt.eventually_mem (hTo.mem_nhds hTm)
  have e3 : ∀ᶠ z : (ℝ × ℝ × ℝ × ℝ) × ℝ in 𝓝 (((ε₀, b₀, 0, 0) : ℝ × ℝ × ℝ × ℝ), a),
      AnalyticAt ℝ (fun w : ℝ × ℝ × ℝ × ℝ => C w.1 w.2.1 w.2.2.1 w.2.2.2)
        ((z.1.1, z.2, z.1.2.1, z.1.2.2.2) : ℝ × ℝ × ℝ × ℝ) :=
    hψ.continuousAt.eventually hCana.eventually_analyticAt
  have e4 : ∀ᶠ z : (ℝ × ℝ × ℝ × ℝ) × ℝ in 𝓝 (((ε₀, b₀, 0, 0) : ℝ × ℝ × ℝ × ℝ), a),
      partialC (fun v : ℝ × ℝ × ℝ × ℝ => That H v.1 v.2.1 v.2.2.1 v.2.2.2)
        ((z.1.1, z.2, z.1.2.1, z.1.2.2.1) : ℝ × ℝ × ℝ × ℝ) ≠ 0 :=
    (hφ.continuousAt (x := (((ε₀, b₀, 0, 0) : ℝ × ℝ × ℝ × ℝ), a))).eventually
      (p := fun w : ℝ × ℝ × ℝ × ℝ =>
        partialC (fun v : ℝ × ℝ × ℝ × ℝ => That H v.1 v.2.1 v.2.2.1 v.2.2.2) w ≠ 0)
      (eventually_partialC_That_ne_zero H hd hreg hm a hε₀.1 hb₀.1.le hb₀ε)
  have e5 : ∀ᶠ z : (ℝ × ℝ × ℝ × ℝ) × ℝ in 𝓝 (((ε₀, b₀, 0, 0) : ℝ × ℝ × ℝ × ℝ), a),
      z.2 ∈ Ioo (0:ℝ) 1 :=
    continuous_snd.continuousAt.eventually_mem (isOpen_Ioo.mem_nhds (hKsub ha))
  have e6 : ∀ᶠ z : (ℝ × ℝ × ℝ × ℝ) × ℝ in 𝓝 (((ε₀, b₀, 0, 0) : ℝ × ℝ × ℝ × ℝ), a),
      z.1.2.1 ∈ Ioo (0:ℝ) 1 := by
    have hc : Continuous fun z : (ℝ × ℝ × ℝ × ℝ) × ℝ => z.1.2.1 := by fun_prop
    exact hc.continuousAt.eventually_mem (isOpen_Ioo.mem_nhds hb₀)
  have e7 : ∀ᶠ z : (ℝ × ℝ × ℝ × ℝ) × ℝ in 𝓝 (((ε₀, b₀, 0, 0) : ℝ × ℝ × ℝ × ℝ), a),
      z.1.2.2.1 < 1 := by
    have hc : Continuous fun z : (ℝ × ℝ × ℝ × ℝ) × ℝ => z.1.2.2.1 := by fun_prop
    exact hc.continuousAt.eventually (Iio_mem_nhds (by norm_num))
  filter_upwards [e1, e2, e3, e4, e5, e6, e7] with z h1 h2 h3 h4 h5 h6 h7
  intro q hq hc0 hϑ W hW hWae
  obtain ⟨hWe, hWt, hWmax⟩ := hW
  exact F_eq_zero_of_maximizer H hreg hTo hCcon hCuniq h3 h1 h2 h4 h5 h6 hq hc0 h7 hϑ hWe hWt hWmax
    hWae

/-- **`F₁` does not vanish away from `a_d(ε₀)`, uniformly on a compact set of first-pode
densities.** -/
theorem eventually_F1_ne_zero {d : ℕ} (hd : 2 ≤ d) (hreg : ∀ v, H.degree v = d)
    (hm : 2 ≤ H.edgeFinset.card) {ε₀ b₀ : ℝ} (hε₀ : ε₀ ∈ Ioo (0:ℝ) 1) (hb₀ : b₀ ∈ Ioo (0:ℝ) 1)
    (hb₀ε : b₀ ≠ ε₀) {K : Set ℝ} (hK : IsCompact K) (hKsub : K ⊆ Ioo (0:ℝ) 1)
    (hKa : ∀ a ∈ K, a ≠ baseA H d ε₀ b₀) :
    ∀ᶠ p in 𝓝 ((ε₀, b₀, 0) : ℝ × ℝ × ℝ), ∀ a ∈ K, F1 H d p.1 a p.2.1 p.2.2 ≠ 0 := by
  refine hK.eventually_forall_of_forall_eventually fun a ha => ?_
  have hne : F1 H d ε₀ a b₀ 0 ≠ 0 := fun h =>
    hKa a ha (eq_baseA_of_F1 H hd hreg hm hε₀.1 hε₀.2 (hKsub ha).1 (hKsub ha).2 hb₀.1 hb₀.2 hb₀ε h)
  have hana := analyticAt_F1 H d (p := ((ε₀, a, b₀, 0) : ℝ × ℝ × ℝ × ℝ)) (by norm_num)
    (hKsub ha).1 (hKsub ha).2 hb₀.1 hb₀.2 (by simpa using hε₀.1) (by simpa using hε₀.2)
  have hφ : Continuous fun z : (ℝ × ℝ × ℝ) × ℝ => ((z.1.1, z.2, z.1.2.1, z.1.2.2) : ℝ × ℝ × ℝ × ℝ) := by
    fun_prop
  have hcomp := ContinuousAt.comp (x := (((ε₀, b₀, 0) : ℝ × ℝ × ℝ), a))
    (g := fun w : ℝ × ℝ × ℝ × ℝ => F1 H d w.1 w.2.1 w.2.2.1 w.2.2.2)
    (f := fun z : (ℝ × ℝ × ℝ) × ℝ => ((z.1.1, z.2, z.1.2.1, z.1.2.2) : ℝ × ℝ × ℝ × ℝ))
    hana.continuousAt hφ.continuousAt
  exact hcomp.eventually_ne hne

end Stationary

theorem logistic_antitone : Antitone logistic := by
  intro y y' h
  unfold logistic
  have h1 : Real.exp (2 * y) ≤ Real.exp (2 * y') := Real.exp_le_exp.mpr (by linarith)
  exact one_div_le_one_div_of_le (by positivity) (by linarith)

theorem mem_Icc_logistic_of_abs_dS0_le {a P : ℝ} (ha : a ∈ Ioo (0:ℝ) 1) (h : |dS0 a| ≤ P) :
    a ∈ Icc (logistic P) (logistic (-P)) := by
  rw [← logistic_dS0 ha.1 ha.2]
  obtain ⟨h1, h2⟩ := abs_le.mp h
  exact ⟨logistic_antitone h2, logistic_antitone h1⟩

theorem dist_prod4_lt {x y : ℝ × ℝ × ℝ × ℝ} {r : ℝ} (h1 : |x.1 - y.1| < r) (h2 : |x.2.1 - y.2.1| < r)
    (h3 : |x.2.2.1 - y.2.2.1| < r) (h4 : |x.2.2.2 - y.2.2.2| < r) : dist x y < r := by
  simp only [Prod.dist_eq, Real.dist_eq]
  exact max_lt h1 (max_lt h2 (max_lt h3 h4))

theorem dist_prod3_lt {x y : ℝ × ℝ × ℝ} {r : ℝ} (h1 : |x.1 - y.1| < r) (h2 : |x.2.1 - y.2.1| < r)
    (h3 : |x.2.2 - y.2.2| < r) : dist x y < r := by
  simp only [Prod.dist_eq, Real.dist_eq]
  exact max_lt h1 (max_lt h2 h3)

set_option maxHeartbeats 8000000 in
/-- **The analytic family is optimal** (KRR–S Theorem 1.1, for `d`-regular `H`):
on a smaller window the family's bipodal graphon maximizes the entropy at `(ε, ε^m + ϑ)`,
uniquely up to relabelling. -/
theorem KRRSFamily.isOptimal {V : Type*} [Fintype V] [DecidableEq V] {H : SimpleGraph V}
    [DecidableRel H.Adj] {d : ℕ} {ε₀ : ℝ} (F : KRRSFamily H d ε₀) (hd : 2 ≤ d)
    (hreg : ∀ v, H.degree v = d) (hm : 2 ≤ H.edgeFinset.card) (hε₀ : ε₀ ∈ Ioo (0:ℝ) 1)
    (hε₀r : ε₀ ≠ rStar d) : F.IsOptimal := by
  classical
  set m := H.edgeFinset.card with hmdef
  obtain ⟨η₂, P₀, hη₂, hbip⟩ := F.exists_bipodal hd hreg hm hε₀ hε₀r
  obtain ⟨hζ₀m, hζ₀ne, -⟩ := zetaFun_crit hd hε₀.1 hε₀.2 hε₀r
  have hbd := F.boundary ε₀ F.mem_U
  obtain ⟨N, hNo, hNm, hNuniq⟩ := F.localUnique
  rw [hbd.2.1, hbd.2.2] at hNm
  obtain ⟨rN, hrN, hballN⟩ := Metric.isOpen_iff.mp hNo _ hNm
  set a₀ := baseA H d ε₀ (zetaFun d ε₀) with ha₀
  set K : Set ℝ := Icc (logistic P₀) (logistic (-P₀)) with hKdef
  have hK : IsCompact K := isCompact_Icc
  have hKsub : K ⊆ Ioo (0:ℝ) 1 := fun a ha =>
    ⟨lt_of_lt_of_le (logistic_mem P₀).1 ha.1, lt_of_le_of_lt ha.2 (logistic_mem _).2⟩
  set K' : Set ℝ := K ∩ {a | rN / 2 ≤ |a - a₀|} with hK'def
  have hK' : IsCompact K' :=
    hK.inter_right (isClosed_le continuous_const (continuous_id.sub continuous_const).abs)
  have hK'a : ∀ a ∈ K', a ≠ a₀ := fun a ha h => by
    have h2 : rN / 2 ≤ |a - a₀| := ha.2
    rw [h, sub_self, abs_zero] at h2
    linarith
  obtain ⟨r₁, hr₁, hball₁⟩ := Metric.eventually_nhds_iff.mp
    (eventually_bipodal_stationary H hd hreg hm hε₀ hζ₀m hζ₀ne hK hKsub)
  obtain ⟨r₂, hr₂, hball₂⟩ := Metric.eventually_nhds_iff.mp
    (eventually_F1_ne_zero H hd hreg hm hε₀ hζ₀m hζ₀ne hK' (fun a ha => hKsub ha.1) hK'a)
  set ρ : ℝ := min (min r₁ r₂) (min rN 1) / 4 with hρ
  have hρ0 : 0 < ρ := by positivity
  have hρ₁ : ρ ≤ r₁ / 4 := by
    have h : min (min r₁ r₂) (min rN 1) ≤ r₁ := le_trans (min_le_left _ _) (min_le_left _ _)
    rw [hρ]; linarith
  have hρ₂ : ρ ≤ r₂ / 4 := by
    have h : min (min r₁ r₂) (min rN 1) ≤ r₂ := le_trans (min_le_left _ _) (min_le_right _ _)
    rw [hρ]; linarith
  have hρN : ρ ≤ rN / 4 := by
    have h : min (min r₁ r₂) (min rN 1) ≤ rN := le_trans (min_le_right _ _) (min_le_left _ _)
    rw [hρ]; linarith
  have hρ1 : ρ ≤ 1 / 4 := by
    have h : min (min r₁ r₂) (min rN 1) ≤ 1 := le_trans (min_le_right _ _) (min_le_right _ _)
    rw [hρ]; linarith
  obtain ⟨r₃, hr₃, hball₃⟩ := Metric.continuousAt_iff.mp (continuousAt_zetaFun hd hε₀) ρ hρ0
  obtain ⟨rU, hrU, hballU⟩ := Metric.isOpen_iff.mp F.isOpen_U ε₀ F.mem_U
  obtain ⟨Δ₃, hΔ₃, hbipρ⟩ := hbip ρ hρ0
  set ηU : ℝ := min (min η₂ rU) (min ρ r₃) with hηU
  have hηU0 : 0 < ηU := lt_min (lt_min hη₂ hrU) (lt_min hρ0 hr₃)
  set Δ' : ℝ := min (min Δ₃ F.Δ) ρ with hΔ'
  have hΔ'0 : 0 < Δ' := lt_min (lt_min hΔ₃ F.Δ_pos) hρ0
  have hUsub : Ioo (ε₀ - ηU) (ε₀ + ηU) ⊆ F.U := by
    intro ε hε
    apply hballU
    rw [Metric.mem_ball, Real.dist_eq]
    have h : ηU ≤ rU := le_trans (min_le_left _ _) (min_le_right _ _)
    exact abs_lt.mpr ⟨by linarith [hε.1], by linarith [hε.2]⟩
  refine ⟨Ioo (ε₀ - ηU) (ε₀ + ηU), isOpen_Ioo, ⟨by linarith, by linarith⟩, hUsub, Δ', hΔ'0,
    le_trans (min_le_left _ _) (min_le_right _ _), ?_⟩
  intro ε hε ϑ hϑ0 hϑΔ
  have hεε₀ : |ε - ε₀| < ηU := abs_lt.mpr ⟨by linarith [hε.1], by linarith [hε.2]⟩
  have hεη₂ : |ε - ε₀| < η₂ := lt_of_lt_of_le hεε₀ (le_trans (min_le_left _ _) (min_le_left _ _))
  have hερ : |ε - ε₀| < ρ := lt_of_lt_of_le hεε₀ (le_trans (min_le_right _ _) (min_le_left _ _))
  have hεr₃ : |ε - ε₀| < r₃ := lt_of_lt_of_le hεε₀ (le_trans (min_le_right _ _) (min_le_right _ _))
  have hϑΔ₃ : ϑ < Δ₃ := lt_of_lt_of_le hϑΔ (le_trans (min_le_left _ _) (min_le_left _ _))
  have hϑF : ϑ < F.Δ := lt_of_lt_of_le hϑΔ (le_trans (min_le_left _ _) (min_le_right _ _))
  have hϑρ : ϑ < ρ := lt_of_lt_of_le hϑΔ (min_le_right _ _)
  have hεU : ε ∈ F.U := hUsub hε
  have hζε : |zetaFun d ε - zetaFun d ε₀| < ρ := by
    have := hball₃ (show dist ε ε₀ < r₃ by rwa [Real.dist_eq])
    rwa [Real.dist_eq] at this
  -- every maximizer is a relabelling of the family graphon
  have hclaim : ∀ W : Graphon, IsMaximizer H W ε (ε ^ m + ϑ) → ∃ σ : ℝ → ℝ, IsRelabelling σ ∧
      ∀ᵐ z ∂gμ, W.toFun z.1 z.2 = (F.graphon ε ϑ).toFun (σ z.1) (σ z.2) := by
    intro W hW
    obtain ⟨-, -, J, a, b, q, hJm, hJsub, hJvol, ha, hda, hb, hbζ, hq, -, hae⟩ :=
      hbipρ ε ϑ W hεη₂ hϑ0 hϑΔ₃ hW
    set c' : ℝ := (volume J).toReal with hc'
    have hc'0 : 0 ≤ c' := ENNReal.toReal_nonneg
    have hc'1 : c' < 1 := by linarith
    have haI : a ∈ Icc (0:ℝ) 1 := ⟨ha.1.le, ha.2.le⟩
    have hbI : b ∈ Icc (0:ℝ) 1 := ⟨hb.1.le, hb.2.le⟩
    have hqI : q ∈ Icc (0:ℝ) 1 := ⟨hq.1.le, hq.2.le⟩
    obtain ⟨σ, hσ, hσae⟩ := exists_relabel_eq_bipodalGraphon hJm hJsub hc'.symm haI hbI hqI hae
    have hae₁ : ∀ᵐ z ∂gμ, W.toFun z.1 z.2
        = bipodalValue (Set.Icc 0 ((a, b, q, c') : Theta).2.2.2) ((a, b, q, c') : Theta).1
          ((a, b, q, c') : Theta).2.1 ((a, b, q, c') : Theta).2.2.1 (σ z.1, σ z.2) := by
      filter_upwards [hσae] with z hz
      rw [hz]; rfl
    have htr₁ := bipodal_transfer H (θ := ((a, b, q, c') : Theta)) haI hbI hqI ⟨hc'0, hc'1.le⟩ hσ
      hae₁
    set W₂ : Graphon := bipodalGraphon (Icc 0 c') measurableSet_Icc a b q haI hbI hqI with hW₂
    have hae₂ : ∀ᵐ z ∂gμ, W₂.toFun z.1 z.2
        = bipodalValue (Set.Icc 0 ((a, b, q, c') : Theta).2.2.2) ((a, b, q, c') : Theta).1
          ((a, b, q, c') : Theta).2.1 ((a, b, q, c') : Theta).2.2.1 (id z.1, id z.2) :=
      Filter.Eventually.of_forall fun z => rfl
    have htr₂ := bipodal_transfer H (θ := ((a, b, q, c') : Theta)) haI hbI hqI ⟨hc'0, hc'1.le⟩
      isRelabelling_id hae₂
    obtain ⟨hWe, hWt, hWmax⟩ := hW
    have hW₂max : IsMaximizer H W₂ ε (ε ^ m + ϑ) :=
      ⟨by rw [htr₂.1, ← htr₁.1, hWe], by rw [htr₂.2.1, ← htr₁.2.1, hWt],
        fun W' h1 h2 => by rw [htr₂.2.2, ← htr₁.2.2]; exact hWmax W' h1 h2⟩
    have hbζ₀ : |b - zetaFun d ε₀| < 2 * ρ := by
      have := abs_sub_le b (zetaFun d ε) (zetaFun d ε₀)
      linarith
    have hc'abs : |c' - 0| < ρ + ρ := by rw [sub_zero, abs_of_nonneg hc'0]; linarith
    have hϑabs : |ϑ - 0| < ρ := by rw [sub_zero, abs_of_pos hϑ0]; exact hϑρ
    have haK : a ∈ K := mem_Icc_logistic_of_abs_dS0_le ha hda
    have hp₁ : dist ((ε, b, c', ϑ) : ℝ × ℝ × ℝ × ℝ) ((ε₀, zetaFun d ε₀, 0, 0) : ℝ × ℝ × ℝ × ℝ) < r₁ :=
      dist_prod4_lt (by show |ε - ε₀| < r₁; linarith) (by show |b - zetaFun d ε₀| < r₁; linarith)
        (by show |c' - 0| < r₁; linarith) (by show |ϑ - 0| < r₁; linarith)
    have hFF := hball₁ hp₁ a haK q hq hc'0 hϑ0 W₂ hW₂max (Filter.Eventually.of_forall fun z => rfl)
    have hp₂ : dist ((ε, b, c') : ℝ × ℝ × ℝ) ((ε₀, zetaFun d ε₀, 0) : ℝ × ℝ × ℝ) < r₂ :=
      dist_prod3_lt (by show |ε - ε₀| < r₂; linarith) (by show |b - zetaFun d ε₀| < r₂; linarith)
        (by show |c' - 0| < r₂; linarith)
    have haa₀ : |a - a₀| < rN / 2 := by
      by_contra hcon
      push Not at hcon
      exact hball₂ hp₂ a ⟨haK, hcon⟩ hFF.1
    have hN1 : ((ε, a, b, c') : ℝ × ℝ × ℝ × ℝ) ∈ N := hballN (Metric.mem_ball.mpr
      (dist_prod4_lt (by show |ε - ε₀| < rN; linarith) (by show |a - a₀| < rN; linarith)
        (by show |b - zetaFun d ε₀| < rN; linarith) (by show |c' - 0| < rN; linarith)))
    have hN2 : ((ε, a, b, ϑ) : ℝ × ℝ × ℝ × ℝ) ∈ N := hballN (Metric.mem_ball.mpr
      (dist_prod4_lt (by show |ε - ε₀| < rN; linarith) (by show |a - a₀| < rN; linarith)
        (by show |b - zetaFun d ε₀| < rN; linarith) (by show |ϑ - 0| < rN; linarith)))
    have hE : bipEdge ((a, b, q, c') : Theta) = ε := by rw [← htr₁.1]; exact hWe
    have hc1' : (1:ℝ) - c' ≠ 0 := by linarith
    have hEexp : a * c' ^ 2 + b * (2 * c' * (1 - c')) + q * (1 - c') ^ 2 = ε := hE
    have hQq : Qmap ε a b c' = q := by
      unfold Qmap
      rw [div_eq_iff (pow_ne_zero 2 hc1')]
      linear_combination (-1 : ℝ) * hEexp
    have hThat : That H ε a b c' = ε ^ m + ϑ := by
      rw [That_eq_bipTd, hQq, ← htr₁.2.1]; exact hWt
    have hϑabsF : |ϑ| < F.Δ := by rw [abs_of_pos hϑ0]; exact hϑF
    obtain ⟨haeq, hbeq, hcc⟩ := hNuniq ε hεU ϑ hϑabsF a b c' hN1 hN2 hThat hFF.1 hFF.2
    refine ⟨σ, hσ, ?_⟩
    obtain ⟨-, -, -, -, hval, -, -⟩ := F.graphon_spec hεU hϑ0 hϑF
    filter_upwards [hσae] with z hz
    rw [hz, bipodalGraphon_apply, hval (σ z.1, σ z.2), ← hcc, ← haeq, ← hbeq, hQq]
  -- the family graphon attains the maximum
  obtain ⟨h11, h12, h22, hc, hval, hGe, hGt⟩ := F.graphon_spec hεU hϑ0 hϑF
  obtain ⟨Wm, hWme, hWmt, hWmmax⟩ := exists_entropy_maximizer H ⟨F.graphon ε ϑ, hGe, hGt⟩
  obtain ⟨σm, hσm, hσmae⟩ := hclaim Wm ⟨hWme, hWmt, hWmmax⟩
  have hentEq : Wm.entropy = (F.graphon ε ϑ).entropy := by
    set θ : Theta := (F.q11 ε ϑ, F.q12 ε ϑ, Qmap ε (F.q11 ε ϑ) (F.q12 ε ϑ) (F.c ε ϑ), F.c ε ϑ)
      with hθ
    have htrm := bipodal_transfer H (θ := θ) ⟨h11.1.le, h11.2.le⟩ ⟨h12.1.le, h12.2.le⟩
      ⟨h22.1.le, h22.2.le⟩ ⟨hc.1.le, hc.2.le⟩ hσm (by
        filter_upwards [hσmae] with z hz
        rw [hz, hval (σm z.1, σm z.2)])
    have htrg := bipodal_transfer H (θ := θ) ⟨h11.1.le, h11.2.le⟩ ⟨h12.1.le, h12.2.le⟩
      ⟨h22.1.le, h22.2.le⟩ ⟨hc.1.le, hc.2.le⟩ isRelabelling_id
      (Filter.Eventually.of_forall fun z => by rw [hval z]; rfl)
    rw [htrm.2.2, htrg.2.2]
  intro W hWe hWt
  refine ⟨?_, fun hEq => ?_⟩
  · rw [← hentEq]; exact hWmmax W hWe hWt
  · exact hclaim W ⟨hWe, hWt, fun W' h1 h2 => by rw [hEq, ← hentEq]; exact hWmmax W' h1 h2⟩

end UpperTailOptimizers
