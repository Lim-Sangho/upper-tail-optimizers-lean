import UpperTailOptimizers.Bipodality.Structure
import UpperTailOptimizers.Bipodality.FamilyEntropy
import UpperTailOptimizers.Bipodality.GapQuadratic

/-!
# The structure of competitors of the analytic family

A **competitor** at `(ε, ϑ)` is a graphon `W` with `e(W) = ε`, `t(H,W) = ε^m + ϑ` and
`s(W) ≥ s(Ŵ_{ε,ϑ})`, where `Ŵ` is the bipodal graphon of the analytic family.  Combining the
family entropy asymptotics (`FamilyEntropy`), first-order efficiency (`Efficiency`), the gap
function (`GapQuadratic`), strong concavity (`Concavity`) and the star reduction
(`StarReduction`) with the deterministic `structure_of_bounds`, every competitor is
`O(ϑ^{4/3})`-close in `L²` to a cross `W₀^I` with `|I| ≍ ϑ`, uniformly for `ε` near `ε₀`.

## Contents

* `rpow_add_le_taylor`, `rpow_excess_le` — concavity of `x ↦ x^{d/m}`;
* `integral_Dfun_eq_moment` — `∬ 𝒟_ε(W) = ∬ W^d - ε^d`;
* `exists_uniform_constants` — the constants of `structure_of_bounds`, uniform near `ε₀`;
* **`KRRSFamily.exists_competitor_structure`**.
-/

namespace UpperTailOptimizers

open MeasureTheory Set Filter Topology

/-- Concavity of `x ↦ x^α` for `0 ≤ α ≤ 1`: `(x + t)^α ≤ x^α + α x^{α-1} t`. -/
theorem rpow_add_le_taylor {x α t : ℝ} (hx : 0 < x) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (ht : 0 ≤ t) :
    (x + t) ^ α ≤ x ^ α + α * x ^ (α - 1) * t := by
  have hs : -1 ≤ t / x := le_trans (by norm_num) (div_nonneg ht hx.le)
  have h := rpow_one_add_le_one_add_mul_self hs hα0 hα1
  have hsplit : x + t = x * (1 + t / x) := by field_simp
  rw [hsplit, Real.mul_rpow hx.le (by linarith)]
  have hxα : 0 ≤ x ^ α := Real.rpow_nonneg hx.le α
  calc x ^ α * (1 + t / x) ^ α ≤ x ^ α * (1 + α * (t / x)) := mul_le_mul_of_nonneg_left h hxα
    _ = x ^ α + α * (x ^ α / x) * t := by ring
    _ = x ^ α + α * x ^ (α - 1) * t := by rw [Real.rpow_sub_one hx.ne']

/-- **The Hölder excess is at most linear**: for `d ≤ m`, `vd = 2m` and `ε > 0`,
`(ε^m + ϑ)^{d/m} - ε^d ≤ 2ϑ/(v ε^{m-d})`. -/
theorem rpow_excess_le {d m v : ℕ} (hdm : d ≤ m) (hm : 0 < m) (hvd : v * d = 2 * m)
    {ε ϑ : ℝ} (hε : 0 < ε) (hϑ : 0 ≤ ϑ) :
    Real.rpow (ε ^ m + ϑ) ((d : ℝ) / (m : ℝ)) - ε ^ d ≤ 2 * ϑ / ((v : ℝ) * ε ^ (m - d)) := by
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have hα0 : 0 ≤ (d : ℝ) / m := div_nonneg (Nat.cast_nonneg d) hmR.le
  have hα1 : (d : ℝ) / m ≤ 1 := by
    rw [div_le_one hmR]; exact_mod_cast hdm
  have hx : 0 < ε ^ m := pow_pos hε m
  have h := rpow_add_le_taylor hx hα0 hα1 hϑ
  have hpow1 : (ε ^ m) ^ ((d : ℝ) / m) = ε ^ d := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hε.le]
    rw [show (m : ℝ) * ((d : ℝ) / m) = d by field_simp]
    exact Real.rpow_natCast ε d
  have hpow2 : (ε ^ m) ^ ((d : ℝ) / m - 1) = 1 / ε ^ (m - d) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hε.le]
    rw [show (m : ℝ) * ((d : ℝ) / m - 1) = -((m - d : ℕ) : ℝ) by
      rw [Nat.cast_sub hdm]; field_simp; ring]
    rw [Real.rpow_neg hε.le, Real.rpow_natCast, one_div]
  have hv : (v : ℝ) * d = 2 * m := by exact_mod_cast hvd
  have hvpos : (0:ℝ) < v := by
    rcases Nat.eq_zero_or_pos v with h0 | h0
    · subst h0; simp at hvd; omega
    · exact_mod_cast h0
  have hcoef : (d : ℝ) / m * (1 / ε ^ (m - d)) = 2 / ((v : ℝ) * ε ^ (m - d)) := by
    have hεpow : 0 < ε ^ (m - d) := pow_pos hε _
    field_simp
    linarith
  show (ε ^ m + ϑ) ^ ((d : ℝ) / (m : ℝ)) - ε ^ d ≤ 2 * ϑ / ((v : ℝ) * ε ^ (m - d))
  rw [hpow1, hpow2, hcoef] at h
  have : 2 / ((v : ℝ) * ε ^ (m - d)) * ϑ = 2 * ϑ / ((v : ℝ) * ε ^ (m - d)) := by ring
  linarith

/-- `∬ 𝒟_ε(W) = ∬ W^d - ε^d` when `e(W) = ε`. -/
theorem integral_Dfun_eq_moment (W : Graphon) (d : ℕ) {ε : ℝ} (he : W.edgeDensity = ε) :
    ∫ z, Dfun d ε (W.toFun z.1 z.2) ∂gμ = W.Wmoment d - ε ^ d := by
  have hpow : Integrable (fun z : ℝ × ℝ => (W.toFun z.1 z.2) ^ d) gμ :=
    W.integrable_comp (g := fun u => u ^ d) (by fun_prop) (by fun_prop)
  have hW : Integrable (fun z : ℝ × ℝ => W.toFun z.1 z.2) gμ := W.integrable_self
  have hpt : (fun z : ℝ × ℝ => Dfun d ε (W.toFun z.1 z.2))
      = fun z => ((W.toFun z.1 z.2) ^ d - ε ^ d)
        - (d : ℝ) * ε ^ (d - 1) * (W.toFun z.1 z.2 - ε) := by
    funext z; unfold Dfun; ring
  rw [hpt, integral_sub (f := fun z : ℝ × ℝ => (W.toFun z.1 z.2) ^ d - ε ^ d)
    (g := fun z : ℝ × ℝ => (d : ℝ) * ε ^ (d - 1) * (W.toFun z.1 z.2 - ε))
    (hpow.sub (integrable_const _)) ((hW.sub (integrable_const _)).const_mul _),
    integral_sub (f := fun z : ℝ × ℝ => (W.toFun z.1 z.2) ^ d) (g := fun _ => ε ^ d)
      hpow (integrable_const _), integral_const_mul,
    integral_sub (f := fun z : ℝ × ℝ => W.toFun z.1 z.2) (g := fun _ => ε) hW (integrable_const _)]
  simp only [integral_const, smul_eq_mul, probReal_univ, one_mul]
  rw [show ∫ z, W.toFun z.1 z.2 ∂gμ = W.edgeDensity from rfl, he, sub_self, mul_zero, sub_zero]
  rfl

/-! ### Uniform constants near `ε₀` -/

theorem Dfun_half_sub_mid (d : ℕ) (ε ζ : ℝ) :
    Dfun d ε ζ / 2 - Dfun d ε ((ε + ζ) / 2) = (ε ^ d + ζ ^ d) / 2 - ((ε + ζ) / 2) ^ d := by
  unfold Dfun; ring

theorem mid_gap_pos {d : ℕ} (hd : 2 ≤ d) {ε ζ : ℝ} (hε : 0 ≤ ε) (hζ : 0 ≤ ζ) (hne : ε ≠ ζ) :
    0 < (ε ^ d + ζ ^ d) / 2 - ((ε + ζ) / 2) ^ d := by
  have h := (strictConvexOn_pow hd).2 (Set.mem_Ici.mpr hε) (Set.mem_Ici.mpr hζ) hne
    (by norm_num : (0:ℝ) < 1 / 2) (by norm_num : (0:ℝ) < 1 / 2) (by norm_num)
  simp only [smul_eq_mul] at h
  have e : (1 / 2 : ℝ) * ε + 1 / 2 * ζ = (ε + ζ) / 2 := by ring
  rw [e] at h
  linarith

theorem Dfun_le_one_add {d : ℕ} {ε u : ℝ} (hε : ε ∈ Icc (0:ℝ) 1) (hu : u ∈ Icc (0:ℝ) 1) :
    Dfun d ε u ≤ 1 + d := by
  unfold Dfun
  have h1 : u ^ d ≤ 1 := pow_le_one₀ hu.1 hu.2
  have h2 : 0 ≤ ε ^ d := pow_nonneg hε.1 d
  have h3 : ε ^ (d - 1) ≤ 1 := pow_le_one₀ hε.1 hε.2
  have h4 : 0 ≤ ε ^ (d - 1) := pow_nonneg hε.1 _
  have h5 : -(d : ℝ) * ε ^ (d - 1) * (u - ε) ≤ d := by
    have hd0 : (0:ℝ) ≤ d := Nat.cast_nonneg d
    have : ε ^ (d - 1) * (ε - u) ≤ 1 := by nlinarith [hu.1, hε.2]
    nlinarith
  linarith

/-- **The constants of the structure theorem, uniform near `ε₀`.** -/
theorem exists_uniform_constants {d : ℕ} (hd : 2 ≤ d) {ε₀ : ℝ} (hε₀ : ε₀ ∈ Ioo (0:ℝ) 1)
    (hε₀r : ε₀ ≠ rStar d) :
    ∃ η a₀ γ P₀ P₁ e₀ : ℝ, 0 < η ∧ 0 < a₀ ∧ 0 < γ ∧ 0 < P₀ ∧ 0 < e₀ ∧
      ∀ ε, |ε - ε₀| < η → ε ∈ Ioo (0:ℝ) 1 ∧ e₀ ≤ ε ∧ ε ≠ rStar d ∧
        a₀ ≤ |zetaFun d ε - ε| ∧
        γ ≤ Dfun d ε (zetaFun d ε) / 2 - Dfun d ε ((ε + zetaFun d ε) / 2) ∧
        P₀ ≤ -psiStar d ε ∧ -psiStar d ε ≤ P₁ := by
  obtain ⟨hζ₀m, hζ₀ne, -⟩ := zetaFun_crit hd hε₀.1 hε₀.2 hε₀r
  have hzc := continuousAt_zetaFun hd hε₀
  have hpc := continuousAt_psiStar hd hε₀ hε₀r
  set f₁ : ℝ → ℝ := fun ε => |zetaFun d ε - ε| with hf₁
  set f₂ : ℝ → ℝ := fun ε => (ε ^ d + zetaFun d ε ^ d) / 2 - ((ε + zetaFun d ε) / 2) ^ d with hf₂
  set f₃ : ℝ → ℝ := fun ε => -psiStar d ε with hf₃
  have hc₁ : ContinuousAt f₁ ε₀ := (hzc.sub continuousAt_id).abs
  have hc₂ : ContinuousAt f₂ ε₀ :=
    (((continuousAt_id.pow d).add (hzc.pow d)).div_const 2).sub
      (((continuousAt_id.add hzc).div_const 2).pow d)
  have hc₃ : ContinuousAt f₃ ε₀ := hpc.neg
  have hp₁ : 0 < f₁ ε₀ := abs_pos.mpr (sub_ne_zero.mpr hζ₀ne)
  have hp₂ : 0 < f₂ ε₀ := mid_gap_pos hd hε₀.1.le hζ₀m.1.le (Ne.symm hζ₀ne)
  have hp₃ : 0 < f₃ ε₀ := by
    simp only [hf₃]; linarith [psiStar_neg hd hε₀ hε₀r]
  have ev₁ := hc₁.eventually (Ioi_mem_nhds (half_lt_self hp₁))
  have ev₂ := hc₂.eventually (Ioi_mem_nhds (half_lt_self hp₂))
  have ev₃ := hc₃.eventually (Ioi_mem_nhds (half_lt_self hp₃))
  have ev₄ := hc₃.eventually (Iio_mem_nhds (lt_add_one (f₃ ε₀)))
  have ev₅ : ∀ᶠ ε in 𝓝 ε₀, ε ∈ Ioo (0:ℝ) 1 := isOpen_Ioo.mem_nhds hε₀
  have ev₆ : ∀ᶠ ε in 𝓝 ε₀, ε₀ / 2 < ε := Ioi_mem_nhds (half_lt_self hε₀.1)
  have ev₇ : ∀ᶠ ε in 𝓝 ε₀, ε ≠ rStar d := continuousAt_id.eventually_ne hε₀r
  obtain ⟨η, hη, hball⟩ := Metric.eventually_nhds_iff.mp
    (ev₁.and (ev₂.and (ev₃.and (ev₄.and (ev₅.and (ev₆.and ev₇))))))
  refine ⟨η, f₁ ε₀ / 2, f₂ ε₀ / 2, f₃ ε₀ / 2, f₃ ε₀ + 1, ε₀ / 2, hη, half_pos hp₁,
    half_pos hp₂, half_pos hp₃, half_pos hε₀.1, fun ε hε => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hball (show dist ε ε₀ < η by rwa [Real.dist_eq])
  refine ⟨h5, h6.le, h7, h1.le, ?_, h3.le, h4.le⟩
  rw [Dfun_half_sub_mid]
  exact h2.le

/-! ### Competitors of the family -/

theorem sqrt_cube_le_t4 {x K t : ℝ} (hx : 0 ≤ x) (hK : 0 ≤ K) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hxK : x ≤ K * t ^ 3) : Real.sqrt x ^ 3 ≤ K * Real.sqrt K * t ^ 4 := by
  have ht32 : t ^ 3 ≤ t ^ 2 := pow_le_pow_of_le_one ht0 ht1 (by norm_num)
  have hsq : Real.sqrt x ≤ Real.sqrt K * t := by
    calc Real.sqrt x ≤ Real.sqrt (K * t ^ 3) := Real.sqrt_le_sqrt hxK
      _ ≤ Real.sqrt (K * t ^ 2) := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left ht32 hK)
      _ = Real.sqrt K * t := by rw [Real.sqrt_mul hK, Real.sqrt_sq ht0]
  have hs0 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  calc Real.sqrt x ^ 3 = Real.sqrt x ^ 2 * Real.sqrt x := by ring
    _ = x * Real.sqrt x := by rw [Real.sq_sqrt hx]
    _ ≤ (K * t ^ 3) * (Real.sqrt K * t) := mul_le_mul hxK hsq hs0 (by positivity)
    _ = K * Real.sqrt K * t ^ 4 := by ring

theorem cube_rpow_third {ϑ : ℝ} (hϑ : 0 ≤ ϑ) : (ϑ ^ ((1:ℝ) / 3)) ^ 3 = ϑ := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hϑ]
  norm_num

set_option maxHeartbeats 1000000 in
/-- **The structure of competitors** (draft `kb:prop:structure`).  Uniformly for `ε` near `ε₀`
and small `ϑ > 0`, every graphon `W` with `e(W) = ε`, `t(H,W) = ε^m + ϑ` and
`s(W) ≥ s(Ŵ_{ε,ϑ})` satisfies `‖W - ε‖₂² ≤ Kϑ`, `∬ Γ(W) ≤ Kϑ²`, and is within
`K ϑ^{4/3}` in squared `L²` distance of a cross `W₀^I` with `ϑ/K ≤ |I| ≤ Kϑ`. -/
theorem KRRSFamily.exists_competitor_structure {V : Type*} [Fintype V] [DecidableEq V]
    {H : SimpleGraph V} [DecidableRel H.Adj] {d : ℕ} {ε₀ : ℝ} (F : KRRSFamily H d ε₀)
    (hd : 2 ≤ d) (hreg : ∀ v, H.degree v = d) (hm : 2 ≤ H.edgeFinset.card)
    (hε₀ : ε₀ ∈ Ioo (0:ℝ) 1) (hε₀r : ε₀ ≠ rStar d) :
    ∃ η Δ K : ℝ, 0 < η ∧ 0 < Δ ∧ 0 < K ∧ ∀ (ε ϑ : ℝ) (W : Graphon), |ε - ε₀| < η → 0 < ϑ →
      ϑ < Δ → W.edgeDensity = ε → W.tDensity H = ε ^ H.edgeFinset.card + ϑ →
      (F.graphon ε ϑ).entropy ≤ W.entropy →
      ε ∈ F.U ∧ ϑ < F.Δ ∧
      ∫ z, (W.toFun z.1 z.2 - ε) ^ 2 ∂gμ ≤ K * ϑ ∧
      ∫ z, gapFun d ε (W.toFun z.1 z.2) ∂gμ ≤ K * ϑ ^ 2 ∧
      ∃ I : Set ℝ, MeasurableSet I ∧ I ⊆ Icc 0 1 ∧ ϑ / K ≤ (unitμ I).toReal ∧
        (unitμ I).toReal ≤ K * ϑ ∧
        ∫ z, (W.toFun z.1 z.2 - crossProfile ε (zetaFun d ε) I z) ^ 2 ∂gμ
          ≤ K * (ϑ * ϑ ^ ((1:ℝ) / 3)) := by
  classical
  set m := H.edgeFinset.card with hmdef
  set v := Fintype.card V with hvdef
  have hvd : v * d = 2 * m := regular_handshake H hreg
  have hm0 : 0 < m := by omega
  have hdm : d ≤ m := by
    obtain ⟨u⟩ : Nonempty V := nonempty_of_edge H (by omega)
    rw [← hreg u, ← SimpleGraph.card_incidenceFinset_eq_degree]
    exact Finset.card_le_card (H.incidenceFinset_subset u)
  have hvpos : (0:ℝ) < v := by
    have : 0 < v := by
      rcases Nat.eq_zero_or_pos v with h0 | h0
      · rw [h0] at hvd; simp at hvd; omega
      · exact h0
    exact_mod_cast this
  obtain ⟨η₁, Δ₁, K_F, hη₁, hΔ₁, hK_F, hfam⟩ := KRRSFamily.exists_entropy_gap_le H F hd hreg hm hε₀ hε₀r
  obtain ⟨κ, hκ, η₂, hη₂, hgapq⟩ := gap_quadratic_lower hd hε₀ hε₀r
  obtain ⟨η₃, a₀, γ, P₀, P₁, e₀, hη₃, ha₀, hγ, hP₀, he₀, hunif⟩ :=
    exists_uniform_constants hd hε₀ hε₀r
  have hP₁ : 0 < P₁ := by
    obtain ⟨-, -, -, -, -, h1, h2⟩ := hunif ε₀ (by simpa using hη₃)
    linarith
  set B₀ : ℝ := (v : ℝ) * e₀ ^ (m - d) with hB₀
  set B₁ : ℝ := (v : ℝ) with hB₁
  have hB₀pos : 0 < B₀ := by positivity
  have he₀1 : e₀ < 1 := by
    obtain ⟨h1, h2, -⟩ := hunif ε₀ (by simpa using hη₃)
    linarith [h1.2]
  have hB₀₁ : B₀ ≤ B₁ := by
    have : e₀ ^ (m - d) ≤ 1 := pow_le_one₀ he₀.le he₀1.le
    calc B₀ = (v : ℝ) * e₀ ^ (m - d) := rfl
      _ ≤ (v : ℝ) * 1 := mul_le_mul_of_nonneg_left this hvpos.le
      _ = B₁ := by rw [hB₁, mul_one]
  set K₂ : ℝ := P₁ / B₀ + K_F / 2 with hK₂
  have hK₂0 : 0 ≤ K₂ := by positivity
  obtain ⟨K_S, t₀, hK_S, ht₀, hstruct⟩ := structure_of_bounds hd (K₁ := K_F / κ) (K₂ := K₂)
    (K₃ := K_F / P₀) (K₄ := 10 ^ m * (K₂ * Real.sqrt K₂)) (B₀ := B₀) (B₁ := B₁) (a₀ := a₀)
    (γ := γ) (Φ₁ := 1 + d) (by positivity) hK₂0 (by positivity) (by positivity) hB₀pos hB₀₁ ha₀
    hγ (by positivity)
  set K : ℝ := K_S + K₂ + K_F + 1 with hK
  refine ⟨min η₁ (min η₂ η₃), min Δ₁ (min 1 (t₀ ^ 3)), K, by positivity, by positivity,
    by positivity, ?_⟩
  intro ε ϑ W hε hϑ0 hϑ he ht hent
  have hε₁ : |ε - ε₀| < η₁ := lt_of_lt_of_le hε (min_le_left _ _)
  have hε₂ : |ε - ε₀| < η₂ := lt_of_lt_of_le hε (le_trans (min_le_right _ _) (min_le_left _ _))
  have hε₃ : |ε - ε₀| < η₃ := lt_of_lt_of_le hε (le_trans (min_le_right _ _) (min_le_right _ _))
  have hϑΔ₁ : ϑ < Δ₁ := lt_of_lt_of_le hϑ (min_le_left _ _)
  have hϑ1 : ϑ < 1 := lt_of_lt_of_le hϑ (le_trans (min_le_right _ _) (min_le_left _ _))
  have hϑt₀ : ϑ < t₀ ^ 3 := lt_of_lt_of_le hϑ (le_trans (min_le_right _ _) (min_le_right _ _))
  obtain ⟨hεU, hϑF, hgapfam⟩ := hfam ε ϑ hε₁ hϑ0 hϑΔ₁
  obtain ⟨hεI, -, hκq⟩ := hgapq ε hε₂
  obtain ⟨-, he₀ε, hεr, ha, hγε, hP₀ε, hP₁ε⟩ := hunif ε hε₃
  set ζ := zetaFun d ε with hζ
  obtain ⟨hζm, -, -⟩ := zetaFun_crit hd hεI.1 hεI.2 hεr
  have hεIcc : ε ∈ Icc (0:ℝ) 1 := ⟨hεI.1.le, hεI.2.le⟩
  have hζIcc : ζ ∈ Icc (0:ℝ) 1 := ⟨hζm.1.le, hζm.2.le⟩
  set τ : ℝ := Real.rpow (ε ^ m + ϑ) ((d : ℝ) / (m : ℝ)) with hτ
  -- the Hölder excess
  have hX_le : τ - ε ^ d ≤ 2 * ϑ / ((v : ℝ) * ε ^ (m - d)) :=
    rpow_excess_le hdm hm0 hvd hεI.1 hϑ0.le
  have hX_nonneg : 0 ≤ τ - ε ^ d := by
    have hx : 0 < ε ^ m := pow_pos hεI.1 m
    have h1 : (ε ^ m) ^ ((d : ℝ) / m) ≤ (ε ^ m + ϑ) ^ ((d : ℝ) / m) :=
      Real.rpow_le_rpow hx.le (by linarith) (div_nonneg (Nat.cast_nonneg d) (by positivity))
    have h2 : (ε ^ m) ^ ((d : ℝ) / m) = ε ^ d := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hεI.1.le]
      rw [show (m : ℝ) * ((d : ℝ) / m) = d by field_simp]
      exact Real.rpow_natCast ε d
    show 0 ≤ (ε ^ m + ϑ) ^ ((d : ℝ) / (m : ℝ)) - ε ^ d
    linarith
  set B : ℝ := (v : ℝ) * ε ^ (m - d) with hB
  have hBpos : 0 < B := mul_pos hvpos (pow_pos hεI.1 _)
  have hB₀B : B₀ ≤ B := by
    have : e₀ ^ (m - d) ≤ ε ^ (m - d) := pow_le_pow_left₀ he₀.le he₀ε _
    exact mul_le_mul_of_nonneg_left this hvpos.le
  have hBB₁ : B ≤ B₁ := by
    have : ε ^ (m - d) ≤ 1 := pow_le_one₀ hεI.1.le hεI.2.le
    calc B = (v : ℝ) * ε ^ (m - d) := rfl
      _ ≤ (v : ℝ) * 1 := mul_le_mul_of_nonneg_left this hvpos.le
      _ = B₁ := by rw [hB₁, mul_one]
  -- the entropy deficit of `W`
  have hdef : 2 * (S0 ε - W.entropy) ≤ -psiStar d ε * (τ - ε ^ d) + K_F * ϑ ^ 2 := by
    have : 2 * (S0 ε - W.entropy) ≤ 2 * (S0 ε - (F.graphon ε ϑ).entropy) := by linarith
    exact le_trans this hgapfam
  have hpsiX : -psiStar d ε * (τ - ε ^ d) ≤ P₁ * (2 * ϑ / B) := by
    calc -psiStar d ε * (τ - ε ^ d) ≤ P₁ * (τ - ε ^ d) :=
          mul_le_mul_of_nonneg_right hP₁ε hX_nonneg
      _ ≤ P₁ * (2 * ϑ / B) := mul_le_mul_of_nonneg_left hX_le hP₁.le
  have hϑ2 : ϑ ^ 2 ≤ ϑ := by nlinarith
  -- (H2) the `L²` deviation
  have hL2 : ∫ z, (W.toFun z.1 z.2 - ε) ^ 2 ∂gμ ≤ K₂ * ϑ := by
    have hconc := W.entropy_le_S0_sub_sq hεI.1 hεI.2 he
    have h2ϑB : 2 * ϑ / B ≤ 2 * ϑ / B₀ := div_le_div_of_nonneg_left (by positivity) hB₀pos hB₀B
    have h1 : P₁ * (2 * ϑ / B) ≤ P₁ * (2 * ϑ / B₀) := mul_le_mul_of_nonneg_left h2ϑB hP₁.le
    have h2 : K_F * ϑ ^ 2 ≤ K_F * ϑ := mul_le_mul_of_nonneg_left hϑ2 hK_F
    have h3 : K₂ * ϑ = (P₁ * (2 * ϑ / B₀) + K_F * ϑ) / 2 := by rw [hK₂]; field_simp
    linarith
  -- (H1) the gap integral
  have heff := W.efficiency_bound H hd hreg (by omega) hεI hεr he
  rw [ht] at heff
  have hgap : ∫ z, gapFun d ε (W.toFun z.1 z.2) ∂gμ ≤ K_F * ϑ ^ 2 := by linarith
  have hmin : ∫ z, min ((W.toFun z.1 z.2 - ε) ^ 2) ((W.toFun z.1 z.2 - ζ) ^ 2) ∂gμ
      ≤ K_F / κ * (ϑ ^ ((1:ℝ) / 3)) ^ 6 := by
    have hpt : ∀ z : ℝ × ℝ, min ((W.toFun z.1 z.2 - ε) ^ 2) ((W.toFun z.1 z.2 - ζ) ^ 2)
        ≤ gapFun d ε (W.toFun z.1 z.2) / κ := fun z => by
      rw [le_div_iff₀ hκ, mul_comm]; exact hκq _ (W.mem_Icc z.1 z.2)
    have hint1 : Integrable (fun z : ℝ × ℝ =>
        min ((W.toFun z.1 z.2 - ε) ^ 2) ((W.toFun z.1 z.2 - ζ) ^ 2)) gμ :=
      W.integrable_comp (g := fun u => min ((u - ε) ^ 2) ((u - ζ) ^ 2)) (by fun_prop)
        (by fun_prop)
    have hint2 : Integrable (fun z : ℝ × ℝ => gapFun d ε (W.toFun z.1 z.2) / κ) gμ :=
      (W.integrable_comp (g := fun u => gapFun d ε u) (continuous_gapFun d ε).measurable
        (continuous_gapFun d ε).continuousOn).div_const κ
    have h := integral_mono hint1 hint2 hpt
    rw [integral_div] at h
    have h6 : (ϑ ^ ((1:ℝ) / 3)) ^ 6 = ϑ ^ 2 := by
      rw [show (6:ℕ) = 3 * 2 by norm_num, pow_mul, cube_rpow_third hϑ0.le]
    rw [h6]
    calc _ ≤ (∫ z, gapFun d ε (W.toFun z.1 z.2) ∂gμ) / κ := h
      _ ≤ K_F * ϑ ^ 2 / κ := div_le_div_of_nonneg_right hgap hκ.le
      _ = K_F / κ * ϑ ^ 2 := by ring
  -- (H3) the moment
  have hmom : ∫ z, Dfun d ε (W.toFun z.1 z.2) ∂gμ ≤ 2 * ϑ / B + K_F / P₀ * ϑ ^ 2 := by
    rw [integral_Dfun_eq_moment W d he]
    have hid := W.integral_gapFun_eq (d := d) he
    have hgap0 : 0 ≤ ∫ z, gapFun d ε (W.toFun z.1 z.2) ∂gμ :=
      integral_nonneg fun z => gapFun_nonneg hd hεI (W.mem_Icc z.1 z.2)
    have h1 : -psiStar d ε * (W.Wmoment d - ε ^ d) ≤ -psiStar d ε * (τ - ε ^ d) + K_F * ϑ ^ 2 := by
      linarith
    have hψ : 0 < -psiStar d ε := lt_of_lt_of_le hP₀ hP₀ε
    have h2 : W.Wmoment d - ε ^ d ≤ (τ - ε ^ d) + K_F * ϑ ^ 2 / (-psiStar d ε) := by
      have h2' : W.Wmoment d - ε ^ d
          ≤ ((-psiStar d ε) * (τ - ε ^ d) + K_F * ϑ ^ 2) / (-psiStar d ε) := by
        rw [le_div_iff₀ hψ]; linarith
      rwa [add_div, mul_div_cancel_left₀ _ hψ.ne'] at h2'
    have h3 : K_F * ϑ ^ 2 / (-psiStar d ε) ≤ K_F / P₀ * ϑ ^ 2 := by
      rw [div_mul_eq_mul_div]
      exact div_le_div_of_nonneg_left (by positivity) hP₀ hP₀ε
    linarith
  -- (H4) the star reduction
  have hstar := abs_tDensity_sub_star_le H hd hreg W hεIcc he
  set t : ℝ := ϑ ^ ((1:ℝ) / 3) with htdef
  have ht0 : 0 < t := Real.rpow_pos_of_pos hϑ0 _
  have ht3 : t ^ 3 = ϑ := cube_rpow_third hϑ0.le
  have ht1 : t ≤ 1 := by
    by_contra h; push Not at h
    have := pow_lt_pow_left₀ h zero_le_one (by norm_num : (3:ℕ) ≠ 0)
    rw [ht3, one_pow] at this; linarith
  have htt₀ : t ≤ t₀ := by
    by_contra h; push Not at h
    have := pow_lt_pow_left₀ h ht₀.le (by norm_num : (3:ℕ) ≠ 0)
    rw [ht3] at this; linarith
  have hsqrt3 := sqrt_cube_le_t4 (integral_nonneg fun _ => sq_nonneg _) hK₂0 ht0.le ht1
    (by rw [ht3]; exact hL2)
  have hstar' : t ^ 3 ≤ B * ∫ x, Dfun d ε (W.degFun x) ∂unitμ
      + 10 ^ m * (K₂ * Real.sqrt K₂) * t ^ 4 := by
    have h1 := (abs_le.mp hstar).2
    rw [ht] at h1
    have h2 : (10:ℝ) ^ m * Real.sqrt (∫ z, (W.toFun z.1 z.2 - ε) ^ 2 ∂gμ) ^ 3
        ≤ 10 ^ m * (K₂ * Real.sqrt K₂ * t ^ 4) :=
      mul_le_mul_of_nonneg_left hsqrt3 (by positivity)
    have h3 : (10:ℝ) ^ m * (K₂ * Real.sqrt K₂ * t ^ 4) = 10 ^ m * (K₂ * Real.sqrt K₂) * t ^ 4 := by
      ring
    rw [ht3]
    have h4 : ε ^ m + ϑ - ε ^ m - B * ∫ x, Dfun d ε (W.degFun x) ∂unitμ
        ≤ 10 ^ m * Real.sqrt (∫ z, (W.toFun z.1 z.2 - ε) ^ 2 ∂gμ) ^ 3 := h1
    linarith
  obtain ⟨I, hIm, hIsub, hIlow, hIup, hIL2⟩ := hstruct W ε ζ B t hεIcc hζIcc ha hB₀B hBB₁ hγε
    (Dfun_le_one_add hεIcc hζIcc) ht0 htt₀ hmin
    (by rw [ht3]; exact hL2) (by rw [ht3, show t ^ 6 = (t ^ 3) ^ 2 by ring, ht3]; exact hmom)
    hstar'
  refine ⟨hεU, hϑF, ?_, ?_, I, hIm, hIsub, ?_, ?_, ?_⟩
  · exact le_trans hL2 (mul_le_mul_of_nonneg_right (by rw [hK]; linarith) hϑ0.le)
  · exact le_trans hgap (mul_le_mul_of_nonneg_right (by rw [hK]; linarith) (sq_nonneg _))
  · rw [← ht3]
    exact le_trans (div_le_div_of_nonneg_left (by positivity) hK_S (by rw [hK]; linarith)) hIlow
  · rw [← ht3]
    exact le_trans hIup (mul_le_mul_of_nonneg_right (by rw [hK]; linarith) (by positivity))
  · have ht4 : t ^ 4 = ϑ * t := by rw [← ht3]; ring
    rw [← ht4]
    exact le_trans hIL2 (mul_le_mul_of_nonneg_right (by rw [hK]; linarith) (by positivity))

end UpperTailOptimizers
