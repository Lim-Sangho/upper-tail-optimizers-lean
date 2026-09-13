import UpperTailOptimizers.Bipodality.Contraction
import UpperTailOptimizers.SingularEndpoint.BipodalTransport

/-!
# Exact bipodality of maximizers

Row balance places almost every row value `w(x)` near `ε` or near `ζ = ζ_d(ε)`; this splits
`[0,1]` into the class `J = {|w - ζ| < |w - ε|}` and its complement, with rows `L¹`-close to the
class value.  The contraction estimate then makes all rows in a class *equal*, so `Γ_W(x,y)`
depends only on the classes of `x` and `y`, and the Euler–Lagrange equation makes `W` a two-block
kernel (draft `kb:prop:bipodal`).

## Contents

* `eq_zero_of_le_mul_of_lt_one`, `Graphon.rowDist_le_integral_add`, `Graphon.rowDist_ge_of_ae_eq`;
* `Graphon.ae_eq_bipodalValue_of_reps` — the two-block form from class representatives;
* `QualDirs.bipodal_of_bounds` — exact bipodality under explicit smallness hypotheses.
-/

set_option linter.unusedSectionVars false

namespace UpperTailOptimizers

open MeasureTheory Set SingularEndpoint

theorem eq_zero_of_le_mul_of_lt_one {ρ θ : ℝ} (h0 : 0 ≤ ρ) (h : ρ ≤ θ * ρ) (hθ : θ < 1) :
    ρ = 0 := by
  by_contra hne
  have hpos : 0 < ρ := lt_of_le_of_ne h0 (Ne.symm hne)
  nlinarith

variable {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]

namespace Graphon

theorem rowDist_le_integral_add (W : Graphon) (x : ℝ) {w c : ℝ} (hw : w ∈ Icc (0:ℝ) 1) :
    W.rowDist c x ≤ ∫ t, |W.toFun x t - w| ∂unitμ + |w - c| := by
  have h1 : Integrable (fun t => |W.toFun x t - c|) unitμ :=
    integrable_of_abs_le ((measurable_toFun_right W x).sub measurable_const).abs (1 + |c|) fun t => by
      rw [abs_abs]
      calc |W.toFun x t - c| ≤ |W.toFun x t| + |c| := abs_sub _ _
        _ ≤ 1 + |c| := by gcongr; exact W.abs_toFun_le x t
  calc W.rowDist c x = ∫ t, |W.toFun x t - c| ∂unitμ := rfl
    _ ≤ ∫ t, (|W.toFun x t - w| + |w - c|) ∂unitμ :=
        integral_mono h1 ((W.integrable_abs_row_sub x hw).add (integrable_const _)) fun t => by
          have := abs_sub_le (W.toFun x t) w c
          simpa using this
    _ = ∫ t, |W.toFun x t - w| ∂unitμ + |w - c| := by
        rw [integral_add (W.integrable_abs_row_sub x hw) (integrable_const _)]
        simp

theorem rowDist_ge_of_ae_eq (W : Graphon) {x c val : ℝ} {J : Set ℝ} (hJ : MeasurableSet J)
    (h : ∀ᵐ t ∂unitμ, t ∉ J → W.toFun x t = val) :
    |val - c| * (1 - (unitμ J).toReal) ≤ W.rowDist c x := by
  have hc1 : Integrable (fun t => |W.toFun x t - c|) unitμ :=
    integrable_of_abs_le ((measurable_toFun_right W x).sub measurable_const).abs (1 + |c|) fun t => by
      rw [abs_abs]
      calc |W.toFun x t - c| ≤ |W.toFun x t| + |c| := abs_sub _ _
        _ ≤ 1 + |c| := by gcongr; exact W.abs_toFun_le x t
  have hind : Integrable (fun t => Jᶜ.indicator (fun _ => |val - c|) t) unitμ :=
    (integrable_const _).indicator hJ.compl
  have hle : ∫ t, Jᶜ.indicator (fun _ => |val - c|) t ∂unitμ ≤ ∫ t, |W.toFun x t - c| ∂unitμ := by
    refine integral_mono_ae hind hc1 ?_
    filter_upwards [h] with t ht
    by_cases htJ : t ∈ J
    · rw [Set.indicator_of_notMem (show t ∉ Jᶜ from fun h' => h' htJ)]; exact abs_nonneg _
    · rw [Set.indicator_of_mem htJ, ht htJ]
  rw [integral_indicator_const _ hJ.compl, probReal_compl_eq_one_sub hJ, smul_eq_mul,
    measureReal_def] at hle
  have : |val - c| * (1 - (unitμ J).toReal) = (1 - (unitμ J).toReal) * |val - c| := mul_comm _ _
  rw [this]
  exact hle

/-- **The two-block form from class representatives.** -/
theorem ae_eq_bipodalValue_of_reps (W : Graphon) {α β : ℝ} {J : Set ℝ} {P : ℝ → Prop}
    (hP : ∀ᵐ x ∂unitμ, P x)
    (hEL : ∀ᵐ p ∂gμ, W.toFun p.1 p.2 ∈ Ioo (0:ℝ) 1 ∧
      dS0 (W.toFun p.1 p.2) = α + β * W.gammaW H p.1 p.2)
    {xJ xc : ℝ}
    (hrepJ : ∀ x, P x → x ∈ J → ∀ y, W.gammaW H x y = W.gammaW H xJ y)
    (hrepc : ∀ x, P x → x ∉ J → ∀ y, W.gammaW H x y = W.gammaW H xc y) :
    ∀ᵐ z ∂gμ, W.toFun z.1 z.2 = bipodalValue J (logistic (α + β * W.gammaW H xJ xJ))
      (logistic (α + β * W.gammaW H xJ xc)) (logistic (α + β * W.gammaW H xc xc)) z := by
  classical
  filter_upwards [hEL, ae_gμ_of_ae_unitμ hP] with z hz hPz
  obtain ⟨hP1, hP2⟩ := hPz
  have hW : W.toFun z.1 z.2 = logistic (α + β * W.gammaW H z.1 z.2) := by
    rw [← hz.2, logistic_dS0 hz.1.1 hz.1.2]
  rw [hW]
  unfold bipodalValue
  by_cases h1 : z.1 ∈ J <;> by_cases h2 : z.2 ∈ J
  · simp only [h1, h2, if_true]
    rw [hrepJ z.1 hP1 h1, W.gammaW_symm H, hrepJ z.2 hP2 h2]
  · simp only [h1, h2, if_true, if_false]
    rw [hrepJ z.1 hP1 h1, W.gammaW_symm H, hrepc z.2 hP2 h2, W.gammaW_symm H]
  · simp only [h1, h2, if_true, if_false]
    rw [hrepc z.1 hP1 h1, W.gammaW_symm H, hrepJ z.2 hP2 h2]
  · simp only [h1, h2, if_false]
    rw [hrepc z.1 hP1 h1, W.gammaW_symm H, hrepc z.2 hP2 h2]

theorem gammaW_eq_of_rowDiff_zero (W : Graphon) {d : ℕ} (hreg : ∀ v, H.degree v = d) {x x' : ℝ}
    (h : ∫ s, |W.toFun x s - W.toFun x' s| ∂unitμ = 0) (y : ℝ) :
    W.gammaW H x y = W.gammaW H x' y := by
  have hb := W.abs_gammaW_sub_gammaW_crude H hreg x x' y
  rw [h, mul_zero, mul_zero] at hb
  exact sub_eq_zero.mp (abs_nonpos_iff.mp hb)

end Graphon

/-- The contraction coefficient at class value `c` with row distances at most `R`. -/
noncomputable def contrCoef (m d : ℕ) (β c ε R κ₁ : ℝ) : ℝ :=
  2 * (c * (1 - c)) * |β| * (m * (d - 1 : ℕ)) * (c ^ (d - 2) * ε ^ (m - d))
    + 2 * |β| ^ 2 * (m * (d - 1 : ℕ)) ^ 2 * m * (R + R + 2 * κ₁)
    + 2 * |β| * (m * (d - 1 : ℕ)) * (R + R)

set_option maxHeartbeats 4000000 in
/-- **Exact bipodality under explicit smallness hypotheses.** -/
theorem QualDirs.bipodal_of_bounds {W : Graphon} {ε t₀ : ℝ} (hmax : IsMaximizer H W ε t₀)
    (Q : QualDirs H W) {d : ℕ} (hd : 2 ≤ d) (hreg : ∀ v, H.degree v = d)
    (hm : 0 < H.edgeFinset.card) (hε : ε ∈ Ioo (0:ℝ) 1) (hεr : ε ≠ rStar d)
    {κg η r e₁ : ℝ} (hκg : 0 < κg)
    (hgap : ∀ u ∈ Icc (0:ℝ) 1, κg * min ((u - ε) ^ 2) ((u - zetaFun d ε) ^ 2) ≤ gapFun d ε u)
    (hη : 0 < η) (hη1 : η ≤ 1 / 2) (hεη : ε ∈ Icc η (1 - η))
    (hsmall : (|Q.beta| * (H.edgeFinset.card : ℝ) ^ 2 + 1) * W.constDist ε ≤ η / 2)
    (he₁ : |Q.beta| * (H.edgeFinset.card : ℝ) ^ 2 * W.constDist ε ≤ e₁) (hr0 : 0 ≤ r)
    (hr : (4 / η * ((|Q.beta| * (H.edgeFinset.card : ℝ) ^ 2 + 1) * W.constDist ε) ^ 2
        + 2 * (balErr H.edgeFinset.card (Fintype.card V) d Q.alpha Q.beta * W.constDist ε)
        + 2 * (2 * |Q.alpha - alpha₀ H.edgeFinset.card d ε|
          + Fintype.card V * |Q.beta - beta₀ H.edgeFinset.card d ε|)) / κg ≤ r ^ 2)
    (hsep : r + e₁ ≤ |zetaFun d ε - ε| / 2)
    (hJ : 2 * W.constDist ε / |zetaFun d ε - ε| ≤ 1 / 2)
    (hθε : contrCoef H.edgeFinset.card d Q.beta ε ε (e₁ + r) (W.constDist ε) < 1)
    (hθζ : contrCoef H.edgeFinset.card d Q.beta (zetaFun d ε) ε (e₁ + r) (W.constDist ε) < 1) :
    ∃ (J : Set ℝ) (a b q : ℝ), MeasurableSet J ∧ J ⊆ Icc 0 1 ∧
      (volume J).toReal ≤ 2 * W.constDist ε / |zetaFun d ε - ε| ∧
      a ∈ Ioo (0:ℝ) 1 ∧ |dS0 a| ≤ |Q.alpha| + |Q.beta| * H.edgeFinset.card ∧
      b ∈ Ioo (0:ℝ) 1 ∧ |b - zetaFun d ε| ≤ 2 * (e₁ + r) ∧
      q ∈ Ioo (0:ℝ) 1 ∧ |q - ε| ≤ 2 * (e₁ + r) ∧
      ∀ᵐ z ∂gμ, W.toFun z.1 z.2 = bipodalValue J a b q z := by
  classical
  set m := H.edgeFinset.card with hmdef
  set α := Q.alpha with hα
  set β := Q.beta with hβ
  set κ₁ := W.constDist ε with hκ₁
  set ζ := zetaFun d ε with hζ
  have hεI : ε ∈ Icc (0:ℝ) 1 := ⟨hε.1.le, hε.2.le⟩
  have hζm : ζ ∈ Ioo (0:ℝ) 1 := zetaFun_mem hd hε
  have hζI : ζ ∈ Icc (0:ℝ) 1 := ⟨hζm.1.le, hζm.2.le⟩
  have hζne : ζ ≠ ε := zetaFun_ne_self hd hε hεr
  have hsep0 : 0 < |ζ - ε| := abs_pos.mpr (sub_ne_zero.mpr hζne)
  have hκ₁0 : 0 ≤ κ₁ := W.constDist_nonneg ε
  have he₁0 : 0 ≤ e₁ := le_trans (by positivity) he₁
  have hEL := Q.el H hmax
  have hrow := Q.ae_row_el H hmax
  have hgapae := Q.ae_gapFun_rowVal_le H hmax hd hreg hm hε hεr hη hη1 hεη hsmall
  set w : ℝ → ℝ := fun x => W.rowVal m d α β ε x with hw
  have hwm : Measurable w := W.measurable_rowVal m d α β ε
  set J : Set ℝ := Icc 0 1 ∩ {x | |w x - ζ| < |w x - ε|} with hJdef
  have hJm : MeasurableSet J :=
    measurableSet_Icc.inter (measurableSet_lt ((hwm.sub measurable_const).abs)
      ((hwm.sub measurable_const).abs))
  -- the good rows
  set P : ℝ → Prop := fun x => x ∈ Icc (0:ℝ) 1 ∧
    (∀ᵐ y ∂unitμ, W.toFun x y ∈ Ioo (0:ℝ) 1 ∧ dS0 (W.toFun x y) = α + β * W.gammaW H x y) ∧
    (x ∈ J → W.rowDist ζ x ≤ e₁ + r) ∧ (x ∉ J → W.rowDist ε x ≤ e₁ + r) with hPdef
  have hP : ∀ᵐ x ∂unitμ, P x := by
    have hIcc : ∀ᵐ x ∂unitμ, x ∈ Icc (0:ℝ) 1 := ae_restrict_mem measurableSet_Icc
    filter_upwards [hrow, hgapae, hIcc] with x hx hg hxI
    have hwI : w x ∈ Icc (0:ℝ) 1 :=
      ⟨(W.rowVal_mem m d α β ε x).1.le, (W.rowVal_mem m d α β ε x).2.le⟩
    have hmin : min ((w x - ε) ^ 2) ((w x - ζ) ^ 2) ≤ r ^ 2 := by
      have h1 := hgap (w x) hwI
      have h2 : κg * min ((w x - ε) ^ 2) ((w x - ζ) ^ 2) ≤ κg * r ^ 2 := by
        have := (div_le_iff₀ hκg).mp hr
        linarith [h1, hg]
      exact le_of_mul_le_mul_left h2 hκg
    have hint := W.integral_abs_sub_rowVal_le H hreg hεI hx
    have hclose : |w x - ε| ≤ r ∨ |w x - ζ| ≤ r := by
      rcases min_le_iff.mp hmin with h | h
      · left
        have := sq_le_sq.mp h
        rwa [abs_of_nonneg hr0] at this
      · right
        have := sq_le_sq.mp h
        rwa [abs_of_nonneg hr0] at this
    refine ⟨hxI, hx, fun hxJ => ?_, fun hxJ => ?_⟩
    · have hlt : |w x - ζ| < |w x - ε| := hxJ.2
      have hwζ : |w x - ζ| ≤ r := by
        rcases hclose with h | h
        · linarith
        · exact h
      calc W.rowDist ζ x ≤ ∫ t, |W.toFun x t - w x| ∂unitμ + |w x - ζ| :=
            W.rowDist_le_integral_add x hwI
        _ ≤ e₁ + r := add_le_add (le_trans hint he₁) hwζ
    · have hle : |w x - ε| ≤ |w x - ζ| := by
        by_contra hcon
        exact hxJ ⟨hxI, lt_of_not_ge hcon⟩
      have hwε : |w x - ε| ≤ r := by
        rcases hclose with h | h
        · exact h
        · linarith
      calc W.rowDist ε x ≤ ∫ t, |W.toFun x t - w x| ∂unitμ + |w x - ε| :=
            W.rowDist_le_integral_add x hwI
        _ ≤ e₁ + r := add_le_add (le_trans hint he₁) hwε
  -- contraction within a class
  have hcoef : ∀ c ∈ Icc (0:ℝ) 1, ∀ {x x' : ℝ}, W.rowDist c x ≤ e₁ + r → W.rowDist c x' ≤ e₁ + r →
      (2 * (c * (1 - c)) * |β| * (m * (d - 1 : ℕ)) * (c ^ (d - 2) * ε ^ (m - d))
          + 2 * |β| ^ 2 * (m * (d - 1 : ℕ)) ^ 2 * m * (W.rowDist c x + W.rowDist c x' + 2 * κ₁)
          + 2 * |β| * (m * (d - 1 : ℕ)) * (W.rowDist c x + W.rowDist c x'))
        ≤ contrCoef m d β c ε (e₁ + r) κ₁ := by
    intro c _ x x' h1 h2
    unfold contrCoef
    have hM : (0:ℝ) ≤ (m : ℝ) * (d - 1 : ℕ) := by positivity
    gcongr
  have hcontr : ∀ x x', P x → P x' → (x ∈ J ↔ x' ∈ J) →
      ∫ s, |W.toFun x s - W.toFun x' s| ∂unitμ = 0 := by
    intro x x' hx hx' hiff
    have hρ0 : 0 ≤ ∫ s, |W.toFun x s - W.toFun x' s| ∂unitμ := integral_nonneg fun _ => abs_nonneg _
    by_cases hxJ : x ∈ J
    · have hx'J := hiff.mp hxJ
      have h := W.rowDiff_le_contraction H hreg hζI hεI hx.2.1 hx'.2.1
      have hc := hcoef ζ hζI (hx.2.2.1 hxJ) (hx'.2.2.1 hx'J)
      exact eq_zero_of_le_mul_of_lt_one hρ0 (h.trans (mul_le_mul_of_nonneg_right hc hρ0)) hθζ
    · have hx'J : x' ∉ J := fun h' => hxJ (hiff.mpr h')
      have h := W.rowDiff_le_contraction H hreg hεI hεI hx.2.1 hx'.2.1
      have hc := hcoef ε hεI (hx.2.2.2 hxJ) (hx'.2.2.2 hx'J)
      exact eq_zero_of_le_mul_of_lt_one hρ0 (h.trans (mul_le_mul_of_nonneg_right hc hρ0)) hθε
  have hΓeq : ∀ x x', P x → P x' → (x ∈ J ↔ x' ∈ J) → ∀ y, W.gammaW H x y = W.gammaW H x' y :=
    fun x x' hx hx' hiff y => W.gammaW_eq_of_rowDiff_zero H hreg (hcontr x x' hx hx' hiff) y
  -- the measure of `J`
  have hJvol : (unitμ J).toReal ≤ 2 * κ₁ / |ζ - ε| := by
    have hpt : ∀ᵐ x ∂unitμ, J.indicator (fun _ => |ζ - ε| / 2) x ≤ W.rowDist ε x := by
      filter_upwards [hP] with x hx
      by_cases hxJ : x ∈ J
      · rw [Set.indicator_of_mem hxJ]
        have h1 := hx.2.2.1 hxJ
        have h2 := W.abs_degFun_sub_le_rowDist ζ x
        have h3 := W.abs_degFun_sub_le_rowDist ε x
        have h4 : |ζ - ε| ≤ |W.degFun x - ζ| + |W.degFun x - ε| := by
          have := abs_sub_le ζ (W.degFun x) ε
          rw [abs_sub_comm ζ (W.degFun x)] at this
          exact this
        linarith
      · rw [Set.indicator_of_notMem hxJ]; exact W.rowDist_nonneg ε x
    have hint := integral_mono_ae ((integrable_const _).indicator hJm) (W.integrable_rowDist hεI) hpt
    rw [integral_indicator_const _ hJm, W.integral_rowDist ε, smul_eq_mul, measureReal_def] at hint
    rw [le_div_iff₀ hsep0]
    linarith
  have hJhalf : (unitμ J).toReal ≤ 1 / 2 := le_trans hJvol hJ
  have hJvolume : (volume J).toReal = (unitμ J).toReal := by
    have : unitμ J = volume J := by
      show volume.restrict (Icc (0:ℝ) 1) J = volume J
      rw [Measure.restrict_apply hJm, Set.inter_eq_left.mpr inter_subset_left]
    rw [this]
  have hPnull := ae_iff.mp hP
  -- a representative outside `J`
  obtain ⟨xc, hxcP, hxcJ⟩ : ∃ x, P x ∧ x ∉ J := by
    by_contra hcon
    push Not at hcon
    have hnull : unitμ Jᶜ = 0 := measure_mono_null (fun x hx hPx => hx (hcon x hPx)) hPnull
    have h1 : unitμ.real Jᶜ = 1 - unitμ.real J := probReal_compl_eq_one_sub hJm
    rw [measureReal_def, hnull, measureReal_def] at h1
    simp only [ENNReal.toReal_zero] at h1
    linarith
  have hq : ∀ᵐ t ∂unitμ, t ∉ J → W.toFun xc t = logistic (α + β * W.gammaW H xc xc) := by
    filter_upwards [hxcP.2.1, hP] with t ht hPt
    intro htJ
    rw [← logistic_dS0 ht.1.1 ht.1.2, ht.2, W.gammaW_symm H,
      hΓeq t xc hPt hxcP (iff_of_false htJ hxcJ) xc]
  have hqbound : |logistic (α + β * W.gammaW H xc xc) - ε| ≤ 2 * (e₁ + r) := by
    have h1 := W.rowDist_ge_of_ae_eq hJm hq (c := ε)
    have h2 := hxcP.2.2.2 hxcJ
    have h3 : (1:ℝ) / 2 ≤ 1 - (unitμ J).toReal := by linarith
    have h4 : |logistic (α + β * W.gammaW H xc xc) - ε| * (1 / 2)
        ≤ |logistic (α + β * W.gammaW H xc xc) - ε| * (1 - (unitμ J).toReal) :=
      mul_le_mul_of_nonneg_left h3 (abs_nonneg _)
    linarith
  have hdS0bound : ∀ y y', |dS0 (logistic (α + β * W.gammaW H y y'))| ≤ |α| + |β| * m := by
    intro y y'
    rw [dS0_logistic]
    calc |α + β * W.gammaW H y y'| ≤ |α| + |β * W.gammaW H y y'| := abs_add_le _ _
      _ = |α| + |β| * W.gammaW H y y' := by rw [abs_mul, abs_of_nonneg (W.gammaW_nonneg H y y')]
      _ ≤ |α| + |β| * m := by
          have := W.gammaW_le H y y'
          have := abs_nonneg β
          nlinarith
  by_cases hJne : ∃ x, P x ∧ x ∈ J
  · obtain ⟨xJ, hxJP, hxJJ⟩ := hJne
    have hb : ∀ᵐ t ∂unitμ, t ∉ J → W.toFun xJ t = logistic (α + β * W.gammaW H xJ xc) := by
      filter_upwards [hxJP.2.1, hP] with t ht hPt
      intro htJ
      rw [← logistic_dS0 ht.1.1 ht.1.2, ht.2, W.gammaW_symm H,
        hΓeq t xc hPt hxcP (iff_of_false htJ hxcJ) xJ, W.gammaW_symm H]
    have hbbound : |logistic (α + β * W.gammaW H xJ xc) - ζ| ≤ 2 * (e₁ + r) := by
      have h1 := W.rowDist_ge_of_ae_eq hJm hb (c := ζ)
      have h2 := hxJP.2.2.1 hxJJ
      have h3 : (1:ℝ) / 2 ≤ 1 - (unitμ J).toReal := by linarith
      have h4 : |logistic (α + β * W.gammaW H xJ xc) - ζ| * (1 / 2)
          ≤ |logistic (α + β * W.gammaW H xJ xc) - ζ| * (1 - (unitμ J).toReal) :=
        mul_le_mul_of_nonneg_left h3 (abs_nonneg _)
      linarith
    refine ⟨J, logistic (α + β * W.gammaW H xJ xJ), logistic (α + β * W.gammaW H xJ xc),
      logistic (α + β * W.gammaW H xc xc), hJm, inter_subset_left, by rw [hJvolume]; exact hJvol,
      logistic_mem _, hdS0bound xJ xJ, logistic_mem _, hbbound, logistic_mem _, hqbound, ?_⟩
    exact W.ae_eq_bipodalValue_of_reps H hP hEL
      (fun x hx hxJ y => hΓeq x xJ hx hxJP (iff_of_true hxJ hxJJ) y)
      (fun x hx hxJ y => hΓeq x xc hx hxcP (iff_of_false hxJ hxcJ) y)
  · push Not at hJne
    have hJnull : unitμ J = 0 := measure_mono_null (fun x hxJ hPx => hJne x hPx hxJ) hPnull
    refine ⟨J, logistic α, ζ, logistic (α + β * W.gammaW H xc xc), hJm, inter_subset_left,
      by rw [hJvolume]; exact hJvol, logistic_mem _, ?_, hζm, by simp; positivity, logistic_mem _,
      hqbound, ?_⟩
    · rw [dS0_logistic]
      have := abs_nonneg β
      have : (0:ℝ) ≤ |β| * m := by positivity
      linarith
    · have hnotJ : ∀ᵐ x ∂unitμ, x ∉ J := by
        rw [ae_iff]; simpa using hJnull
      have hEL' := hEL
      filter_upwards [hEL, ae_gμ_of_ae_unitμ (hnotJ.and hP)] with z hz hz12
      obtain ⟨⟨h1J, h1P⟩, ⟨h2J, h2P⟩⟩ := hz12
      unfold bipodalValue
      simp only [h1J, h2J, if_false]
      rw [← logistic_dS0 hz.1.1 hz.1.2, hz.2, W.gammaW_symm H,
        hΓeq z.2 xc h2P hxcP (iff_of_false h2J hxcJ) z.1, W.gammaW_symm H,
        hΓeq z.1 xc h1P hxcP (iff_of_false h1J hxcJ) xc]

end UpperTailOptimizers
