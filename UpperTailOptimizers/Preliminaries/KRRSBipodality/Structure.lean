import UpperTailOptimizers.Preliminaries.KRRSBipodality.CrossDefect
import UpperTailOptimizers.Preliminaries.KRRSBipodality.StarReduction
import UpperTailOptimizers.Preliminaries.KRRSAnalyticExtension.PsiExists

/-!
# The structure of efficient competitors

A graphon `W` of edge density `ε` whose values are, in `L²`, within `O(ϑ)` of the two values
`ε` and `ζ`, whose `d`-th moment exceeds `ε^d` by at most `2ϑ/B + O(ϑ²)`, and whose degree
profile carries at least `ϑ/B - O(ϑ^{3/2})` of `∫ 𝒟_ε(d_W)`, is close to a cross

  `W₀^I = ε + (ζ - ε)·1_{(I × Iᶜ) ∪ (Iᶜ × I)}`,   `|I| ≍ ϑ`,   `‖W - W₀^I‖₂² ≤ K ϑ^{4/3}`.

This is `kb:prop:structure` of the bipodality draft, with explicit rates.  The input bounds are
exactly what first-order efficiency, the gap function and the star reduction provide.

## Contents

* `abs_Dfun_sub_le` — a Lipschitz bound for `𝒟_ε` on `[0,1]`;
* `nearSet`, `crossProfile` — the set where `W` is nearer to `ζ` than to `ε`, and `W₀^I`;
* `structure_of_bounds` — the deterministic structure theorem.
-/

namespace UpperTailOptimizers

open MeasureTheory Set Filter

/-! ### A Lipschitz bound for `𝒟_ε` -/

/-- `|𝒟_ε(q) - 𝒟_ε(p)| ≤ d(d-1)(|p - ε| + |q - p|)|q - p|` on `[0,1]`. -/
theorem abs_Dfun_sub_le {d : ℕ} (hd : 1 ≤ d) {ε p q : ℝ} (hε : ε ∈ Icc (0:ℝ) 1)
    (hp : p ∈ Icc (0:ℝ) 1) (hq : q ∈ Icc (0:ℝ) 1) :
    |Dfun d ε q - Dfun d ε p| ≤ (d : ℝ) * ((d : ℝ) - 1) * (|p - ε| + |q - p|) * |q - p| := by
  have hbound : ∀ u ∈ Set.uIcc p q,
      ‖dD d ε u‖ ≤ (d : ℝ) * ((d : ℝ) - 1) * (|p - ε| + |q - p|) := by
    intro u hu
    have hu01 : u ∈ Icc (0:ℝ) 1 := Set.uIcc_subset_Icc hp hq hu
    have h1 : |u - p| ≤ |q - p| := Set.abs_sub_left_of_mem_uIcc hu
    have h2 : |u - ε| ≤ |p - ε| + |q - p| := by
      calc |u - ε| = |(u - p) + (p - ε)| := by ring_nf
        _ ≤ |u - p| + |p - ε| := abs_add_le _ _
        _ ≤ |p - ε| + |q - p| := by linarith
    have hpow := _root_.abs_pow_sub_pow_le (a := u) (b := ε) (n := d - 1)
    have hmax : max |u| |ε| ^ (d - 1 - 1) ≤ 1 := by
      apply pow_le_one₀ (le_max_of_le_left (abs_nonneg _))
      exact max_le (by rw [abs_of_nonneg hu01.1]; exact hu01.2)
        (by rw [abs_of_nonneg hε.1]; exact hε.2)
    have hcast : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
      rw [Nat.cast_sub hd, Nat.cast_one]
    rw [hcast] at hpow
    have hd1 : (0:ℝ) ≤ (d : ℝ) - 1 := by
      have : (1:ℝ) ≤ d := by exact_mod_cast hd
      linarith
    have h3 : |u ^ (d - 1) - ε ^ (d - 1)| ≤ ((d : ℝ) - 1) * (|p - ε| + |q - p|) := by
      calc |u ^ (d - 1) - ε ^ (d - 1)|
          ≤ |u - ε| * ((d : ℝ) - 1) * max |u| |ε| ^ (d - 1 - 1) := hpow
        _ ≤ |u - ε| * ((d : ℝ) - 1) * 1 :=
            mul_le_mul_of_nonneg_left hmax (mul_nonneg (abs_nonneg _) hd1)
        _ = ((d : ℝ) - 1) * |u - ε| := by ring
        _ ≤ ((d : ℝ) - 1) * (|p - ε| + |q - p|) := mul_le_mul_of_nonneg_left h2 hd1
    rw [Real.norm_eq_abs]
    unfold dD
    rw [← mul_sub, abs_mul, abs_of_nonneg (Nat.cast_nonneg d)]
    calc (d : ℝ) * |u ^ (d - 1) - ε ^ (d - 1)|
        ≤ (d : ℝ) * (((d : ℝ) - 1) * (|p - ε| + |q - p|)) :=
          mul_le_mul_of_nonneg_left h3 (Nat.cast_nonneg d)
      _ = (d : ℝ) * ((d : ℝ) - 1) * (|p - ε| + |q - p|) := by ring
  have h := (convex_uIcc p q).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun u _ => (hasDerivAt_Dfun d ε u).hasDerivWithinAt) hbound Set.left_mem_uIcc
    Set.right_mem_uIcc
  simpa only [Real.norm_eq_abs] using h

theorem Dfun_nonneg_of_mem {d : ℕ} (hd : 2 ≤ d) {ε u : ℝ} (hε : ε ∈ Icc (0:ℝ) 1)
    (hu : u ∈ Icc (0:ℝ) 1) : 0 ≤ Dfun d ε u := by
  rcases eq_or_lt_of_le hε.1 with h0 | hpos
  · subst h0
    unfold Dfun
    have : (0:ℝ) ^ d = 0 := zero_pow (by omega)
    rw [this]
    have : (0:ℝ) ^ (d - 1) = 0 := zero_pow (by omega)
    rw [this]
    simp only [sub_zero, mul_zero, zero_mul]
    exact pow_nonneg hu.1 d
  · by_cases hue : u = ε
    · subst hue; unfold Dfun; simp
    · exact (Dfun_pos hd hpos hu.1 hue).le

/-! ### The near set and the cross profile -/

/-- The set where `W` is nearer to `ζ` than to `ε`. -/
def nearSet (W : Graphon) (ε ζ : ℝ) : Set (ℝ × ℝ) :=
  {z | |W.toFun z.1 z.2 - ζ| < |W.toFun z.1 z.2 - ε|}

theorem measurableSet_nearSet (W : Graphon) (ε ζ : ℝ) : MeasurableSet (nearSet W ε ζ) :=
  measurableSet_lt ((W.measurable_uncurry.sub measurable_const).abs)
    ((W.measurable_uncurry.sub measurable_const).abs)

theorem nearSet_symm (W : Graphon) (ε ζ : ℝ) (x y : ℝ) :
    (x, y) ∈ nearSet W ε ζ ↔ (y, x) ∈ nearSet W ε ζ := by
  simp only [nearSet, Set.mem_ofPred_eq, W.symm' x y]

/-- The cross profile `W₀^I = ε + (ζ - ε)·1_{(I × Iᶜ) ∪ (Iᶜ × I)}`. -/
noncomputable def crossProfile (ε ζ : ℝ) (I : Set ℝ) (z : ℝ × ℝ) : ℝ :=
  ε + (ζ - ε) * (crossSet I).indicator (fun _ => (1:ℝ)) z

/-- The residual `W - ε - (ζ - ε)·1_S` squares to `min((W-ε)², (W-ζ)²)`. -/
theorem sq_resid_nearSet (W : Graphon) (ε ζ : ℝ) (z : ℝ × ℝ) :
    (W.toFun z.1 z.2 - ε - (ζ - ε) * (nearSet W ε ζ).indicator (fun _ => (1:ℝ)) z) ^ 2
      = min ((W.toFun z.1 z.2 - ε) ^ 2) ((W.toFun z.1 z.2 - ζ) ^ 2) := by
  by_cases hz : z ∈ nearSet W ε ζ
  · rw [Set.indicator_of_mem hz, mul_one]
    have h : |W.toFun z.1 z.2 - ζ| < |W.toFun z.1 z.2 - ε| := hz
    have hsq : (W.toFun z.1 z.2 - ζ) ^ 2 ≤ (W.toFun z.1 z.2 - ε) ^ 2 := by
      rw [← sq_abs, ← sq_abs (W.toFun z.1 z.2 - ε)]
      exact pow_le_pow_left₀ (abs_nonneg _) h.le 2
    rw [min_eq_right hsq]
    ring
  · rw [Set.indicator_of_notMem hz, mul_zero, sub_zero]
    have h : ¬ |W.toFun z.1 z.2 - ζ| < |W.toFun z.1 z.2 - ε| := hz
    have hsq : (W.toFun z.1 z.2 - ε) ^ 2 ≤ (W.toFun z.1 z.2 - ζ) ^ 2 := by
      rw [← sq_abs, ← sq_abs (W.toFun z.1 z.2 - ζ)]
      exact pow_le_pow_left₀ (abs_nonneg _) (not_lt.mp h) 2
    rw [min_eq_left hsq]

/-- On the near set, `W` is at distance at least `|ζ - ε|/2` from `ε`. -/
theorem indicator_nearSet_le (W : Graphon) {ε ζ : ℝ} (hne : ζ ≠ ε) (z : ℝ × ℝ) :
    (nearSet W ε ζ).indicator (fun _ => (1:ℝ)) z
      ≤ 4 / (ζ - ε) ^ 2 * (W.toFun z.1 z.2 - ε) ^ 2 := by
  have hpos : 0 < (ζ - ε) ^ 2 := by positivity
  by_cases hz : z ∈ nearSet W ε ζ
  · rw [Set.indicator_of_mem hz]
    have h : |W.toFun z.1 z.2 - ζ| < |W.toFun z.1 z.2 - ε| := hz
    have htri : |ζ - ε| ≤ |W.toFun z.1 z.2 - ζ| + |W.toFun z.1 z.2 - ε| := by
      calc |ζ - ε| = |(W.toFun z.1 z.2 - ε) - (W.toFun z.1 z.2 - ζ)| := by ring_nf
        _ ≤ |W.toFun z.1 z.2 - ε| + |W.toFun z.1 z.2 - ζ| := abs_sub _ _
        _ = _ := add_comm _ _
    have h2 : |ζ - ε| / 2 ≤ |W.toFun z.1 z.2 - ε| := by linarith
    have h3 : (ζ - ε) ^ 2 / 4 ≤ (W.toFun z.1 z.2 - ε) ^ 2 := by
      have := pow_le_pow_left₀ (by positivity) h2 2
      rw [div_pow, sq_abs, sq_abs] at this
      linarith
    rw [div_mul_eq_mul_div, le_div_iff₀ hpos]
    linarith
  · rw [Set.indicator_of_notMem hz]
    positivity

/-! ### Integrals over the near set -/

/-- The residual `W - ε - (ζ - ε)·1_S` of the near-set approximation. -/
noncomputable def nearResid (W : Graphon) (ε ζ : ℝ) (z : ℝ × ℝ) : ℝ :=
  W.toFun z.1 z.2 - ε - (ζ - ε) * (nearSet W ε ζ).indicator (fun _ => (1:ℝ)) z

theorem measurable_indicator_nearSet (W : Graphon) (ε ζ : ℝ) :
    Measurable ((nearSet W ε ζ).indicator (fun _ : ℝ × ℝ => (1:ℝ))) :=
  measurable_const.indicator (measurableSet_nearSet W ε ζ)

theorem measurable_nearResid (W : Graphon) (ε ζ : ℝ) : Measurable (nearResid W ε ζ) :=
  (W.measurable_uncurry.sub measurable_const).sub
    (measurable_const.mul (measurable_indicator_nearSet W ε ζ))

theorem abs_nearResid_le (W : Graphon) {ε ζ : ℝ} (hε : ε ∈ Icc (0:ℝ) 1)
    (hζ : ζ ∈ Icc (0:ℝ) 1) (z : ℝ × ℝ) : |nearResid W ε ζ z| ≤ 2 := by
  have hW := W.mem_Icc z.1 z.2
  have hind : (nearSet W ε ζ).indicator (fun _ => (1:ℝ)) z ∈ Icc (0:ℝ) 1 := by
    by_cases hz : z ∈ nearSet W ε ζ
    · rw [Set.indicator_of_mem hz]; exact ⟨zero_le_one, le_rfl⟩
    · rw [Set.indicator_of_notMem hz]; exact ⟨le_rfl, zero_le_one⟩
  unfold nearResid
  have h1 : |(ζ - ε) * (nearSet W ε ζ).indicator (fun _ => (1:ℝ)) z| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg hind.1]
    have : |ζ - ε| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hε.1, hε.2, hζ.1, hζ.2]
    nlinarith [hind.2, abs_nonneg (ζ - ε)]
  have h2 : |W.toFun z.1 z.2 - ε| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith [hε.1, hε.2, hW.1, hW.2]
  calc |W.toFun z.1 z.2 - ε - (ζ - ε) * (nearSet W ε ζ).indicator (fun _ => (1:ℝ)) z|
      ≤ |W.toFun z.1 z.2 - ε| + |(ζ - ε) * (nearSet W ε ζ).indicator (fun _ => (1:ℝ)) z| :=
        abs_sub _ _
    _ ≤ 2 := by linarith

theorem integrable_nearResid_sq (W : Graphon) {ε ζ : ℝ} (hε : ε ∈ Icc (0:ℝ) 1)
    (hζ : ζ ∈ Icc (0:ℝ) 1) : Integrable (fun z => nearResid W ε ζ z ^ 2) gμ :=
  integrable_of_abs_le ((measurable_nearResid W ε ζ).pow_const 2) 4 fun z => by
    rw [abs_of_nonneg (sq_nonneg _)]
    have h := abs_nearResid_le W hε hζ z
    nlinarith [abs_nonneg (nearResid W ε ζ z), sq_abs (nearResid W ε ζ z)]

/-- The section measure is the row integral of the indicator. -/
theorem sectionMeasure_eq_integral_indicator {S : Set (ℝ × ℝ)} (hS : MeasurableSet S) (x : ℝ) :
    sectionMeasure S x = ∫ y, S.indicator (fun _ => (1:ℝ)) (x, y) ∂unitμ := by
  have hmeas : MeasurableSet (Prod.mk x ⁻¹' S) := measurable_prodMk_left hS
  have hpt : (fun y => S.indicator (fun _ => (1:ℝ)) (x, y))
      = (Prod.mk x ⁻¹' S).indicator (fun _ => (1:ℝ)) := by
    funext y
    by_cases hy : (x, y) ∈ S
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem (show y ∈ Prod.mk x ⁻¹' S from hy)]
    · rw [Set.indicator_of_notMem hy,
        Set.indicator_of_notMem (show y ∉ Prod.mk x ⁻¹' S from hy)]
  rw [hpt]
  exact (integral_indicator_one hmeas).symm

/-- **The degree decomposition** `d_W(x) = ε + (ζ - ε) s_x + r(x)`. -/
theorem degFun_eq_near (W : Graphon) (ε ζ : ℝ) (x : ℝ) :
    W.degFun x = ε + (ζ - ε) * sectionMeasure (nearSet W ε ζ) x
      + ∫ y, nearResid W ε ζ (x, y) ∂unitμ := by
  have hind : Integrable (fun y => (nearSet W ε ζ).indicator (fun _ => (1:ℝ)) (x, y)) unitμ :=
    integrable_of_abs_le ((measurable_indicator_nearSet W ε ζ).comp
      (measurable_const.prodMk measurable_id)) 1 fun y => by
      by_cases hy : (x, y) ∈ nearSet W ε ζ
      · rw [Set.indicator_of_mem hy]; simp
      · rw [Set.indicator_of_notMem hy]; simp
  have hrow := W.integrable_row x
  have hres : ∫ y, nearResid W ε ζ (x, y) ∂unitμ
      = W.degFun x - ε - (ζ - ε) * sectionMeasure (nearSet W ε ζ) x := by
    rw [show ∫ y, nearResid W ε ζ (x, y) ∂unitμ
        = ∫ y, ((W.toFun x y - ε) - (ζ - ε) * (nearSet W ε ζ).indicator (fun _ => (1:ℝ)) (x, y))
          ∂unitμ from rfl]
    rw [integral_sub (f := fun y => W.toFun x y - ε)
      (g := fun y => (ζ - ε) * (nearSet W ε ζ).indicator (fun _ => (1:ℝ)) (x, y))
      (hrow.sub (integrable_const ε)) (hind.const_mul _),
      integral_sub (f := fun y => W.toFun x y) (g := fun _ => ε) hrow (integrable_const ε),
      integral_const_mul,
      sectionMeasure_eq_integral_indicator (measurableSet_nearSet W ε ζ)]
    simp [Graphon.degFun]
  rw [hres]
  ring

/-- `∫ r(x)² dx ≤ ∫∫ R²` for the row integrals `r(x) = ∫ R(x,y) dy`. -/
theorem integral_rowResid_sq_le (W : Graphon) {ε ζ : ℝ} (hε : ε ∈ Icc (0:ℝ) 1)
    (hζ : ζ ∈ Icc (0:ℝ) 1) :
    ∫ x, (∫ y, nearResid W ε ζ (x, y) ∂unitμ) ^ 2 ∂unitμ ≤ ∫ z, nearResid W ε ζ z ^ 2 ∂gμ := by
  have hrow : ∀ x, (∫ y, nearResid W ε ζ (x, y) ∂unitμ) ^ 2
      ≤ ∫ y, nearResid W ε ζ (x, y) ^ 2 ∂unitμ := by
    intro x
    have hm : Measurable fun y => nearResid W ε ζ (x, y) :=
      (measurable_nearResid W ε ζ).comp (measurable_const.prodMk measurable_id)
    have hi : Integrable (fun y => nearResid W ε ζ (x, y)) unitμ :=
      integrable_of_abs_le hm 2 fun y => abs_nearResid_le W hε hζ _
    have hi2 : Integrable (fun y => nearResid W ε ζ (x, y) ^ 2) unitμ :=
      integrable_of_abs_le (hm.pow_const 2) 4 fun y => by
        rw [abs_of_nonneg (sq_nonneg _)]
        have h := abs_nearResid_le W hε hζ (x, y)
        nlinarith [abs_nonneg (nearResid W ε ζ (x, y)), sq_abs (nearResid W ε ζ (x, y))]
    have h := integral_abs_le_sqrt hi hi2
    have h0 : 0 ≤ ∫ y, nearResid W ε ζ (x, y) ^ 2 ∂unitμ := integral_nonneg fun _ => sq_nonneg _
    calc (∫ y, nearResid W ε ζ (x, y) ∂unitμ) ^ 2
        = |∫ y, nearResid W ε ζ (x, y) ∂unitμ| ^ 2 := (sq_abs _).symm
      _ ≤ (∫ y, |nearResid W ε ζ (x, y)| ∂unitμ) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) (abs_integral_le_integral_abs) 2
      _ ≤ (Real.sqrt (∫ y, nearResid W ε ζ (x, y) ^ 2 ∂unitμ)) ^ 2 :=
          pow_le_pow_left₀ (integral_nonneg fun _ => abs_nonneg _) h 2
      _ = ∫ y, nearResid W ε ζ (x, y) ^ 2 ∂unitμ := Real.sq_sqrt h0
  have hint2 := integrable_nearResid_sq W hε hζ
  have hmeasr : Measurable fun x => ∫ y, nearResid W ε ζ (x, y) ∂unitμ :=
    ((measurable_nearResid W ε ζ).stronglyMeasurable).integral_prod_right'.measurable
  have hintr : Integrable (fun x => (∫ y, nearResid W ε ζ (x, y) ∂unitμ) ^ 2) unitμ :=
    integrable_of_abs_le (hmeasr.pow_const 2) 4 fun x => by
      rw [abs_of_nonneg (sq_nonneg _)]
      have hb : |∫ y, nearResid W ε ζ (x, y) ∂unitμ| ≤ 2 := by
        have h := norm_integral_le_of_norm_le_const (μ := unitμ)
          (f := fun y => nearResid W ε ζ (x, y))
          (Filter.Eventually.of_forall fun y => by
            simpa [Real.norm_eq_abs] using abs_nearResid_le W hε hζ (x, y))
        simpa [Real.norm_eq_abs, measureReal_def] using h
      nlinarith [abs_nonneg (∫ y, nearResid W ε ζ (x, y) ∂unitμ),
        sq_abs (∫ y, nearResid W ε ζ (x, y) ∂unitμ)]
  calc ∫ x, (∫ y, nearResid W ε ζ (x, y) ∂unitμ) ^ 2 ∂unitμ
      ≤ ∫ x, ∫ y, nearResid W ε ζ (x, y) ^ 2 ∂unitμ ∂unitμ :=
        integral_mono hintr hint2.integral_prod_left hrow
    _ = ∫ z, nearResid W ε ζ z ^ 2 ∂gμ := integral_integral hint2

/-! ### The profile `φ(s) = 𝒟_ε(ε + (ζ - ε)s)` -/

theorem convexOn_Dfun_affine (d : ℕ) {ε ζ : ℝ} (hε : ε ∈ Icc (0:ℝ) 1) (hζ : ζ ∈ Icc (0:ℝ) 1) :
    ConvexOn ℝ (Icc 0 1) (fun s => Dfun d ε (ε + (ζ - ε) * s)) := by
  refine ⟨convex_Icc 0 1, fun s₁ hs₁ s₂ hs₂ l₁ l₂ hl₁ hl₂ hl => ?_⟩
  have hu₁ : ε + (ζ - ε) * s₁ ∈ Set.Ici (0:ℝ) := by
    show 0 ≤ ε + (ζ - ε) * s₁
    nlinarith [hs₁.1, hs₁.2, hε.1, hζ.1]
  have hu₂ : ε + (ζ - ε) * s₂ ∈ Set.Ici (0:ℝ) := by
    show 0 ≤ ε + (ζ - ε) * s₂
    nlinarith [hs₂.1, hs₂.2, hε.1, hζ.1]
  have hpow := (convexOn_pow d).2 hu₁ hu₂ hl₁ hl₂ hl
  simp only [smul_eq_mul] at hpow ⊢
  have hu : ε + (ζ - ε) * (l₁ * s₁ + l₂ * s₂)
      = l₁ * (ε + (ζ - ε) * s₁) + l₂ * (ε + (ζ - ε) * s₂) := by
    linear_combination (-ε) * hl
  unfold Dfun
  rw [hu]
  have hlin : l₁ * ((ε + (ζ - ε) * s₁) ^ d - ε ^ d - (d : ℝ) * ε ^ (d - 1) * (ε + (ζ - ε) * s₁ - ε))
      + l₂ * ((ε + (ζ - ε) * s₂) ^ d - ε ^ d - (d : ℝ) * ε ^ (d - 1) * (ε + (ζ - ε) * s₂ - ε))
      = (l₁ * (ε + (ζ - ε) * s₁) ^ d + l₂ * (ε + (ζ - ε) * s₂) ^ d) - ε ^ d
        - (d : ℝ) * ε ^ (d - 1)
          * (l₁ * (ε + (ζ - ε) * s₁) + l₂ * (ε + (ζ - ε) * s₂) - ε) := by
    linear_combination (-(ε ^ d) + (d : ℝ) * ε ^ (d - 1) * ε) * hl
  rw [hlin]
  linarith

theorem Dfun_affine_le_sq {d : ℕ} (hd : 1 ≤ d) {ε ζ : ℝ} (hε : ε ∈ Icc (0:ℝ) 1)
    (hζ : ζ ∈ Icc (0:ℝ) 1) {s : ℝ} (hs : s ∈ Icc (0:ℝ) 1) :
    Dfun d ε (ε + (ζ - ε) * s) ≤ (d : ℝ) * ((d : ℝ) - 1) * s ^ 2 := by
  have hq : ε + (ζ - ε) * s ∈ Icc (0:ℝ) 1 := by
    constructor <;> nlinarith [hs.1, hs.2, hε.1, hε.2, hζ.1, hζ.2]
  have h := abs_Dfun_sub_le hd hε hε hq
  have hD0 : Dfun d ε ε = 0 := by unfold Dfun; simp
  rw [hD0, sub_zero, sub_self, abs_zero, zero_add, add_sub_cancel_left] at h
  have hd1 : (0:ℝ) ≤ (d : ℝ) * ((d : ℝ) - 1) := by
    have : (1:ℝ) ≤ d := by exact_mod_cast hd
    nlinarith
  have habs : |(ζ - ε) * s| ≤ s := by
    rw [abs_mul, abs_of_nonneg hs.1]
    have : |ζ - ε| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hε.1, hε.2, hζ.1, hζ.2]
    nlinarith [hs.1, abs_nonneg (ζ - ε)]
  calc Dfun d ε (ε + (ζ - ε) * s) ≤ |Dfun d ε (ε + (ζ - ε) * s)| := le_abs_self _
    _ ≤ (d : ℝ) * ((d : ℝ) - 1) * |(ζ - ε) * s| * |(ζ - ε) * s| := h
    _ ≤ (d : ℝ) * ((d : ℝ) - 1) * s * s := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left habs hd1) habs (abs_nonneg _)
        exact mul_nonneg hd1 hs.1
    _ = (d : ℝ) * ((d : ℝ) - 1) * s ^ 2 := by ring

theorem exists_abs_Dfun_le (d : ℕ) (ε : ℝ) : ∃ M, ∀ u ∈ Icc (0:ℝ) 1, |Dfun d ε u| ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0:ℝ)) (b := 1)).exists_bound_of_continuousOn
    (continuous_Dfun d ε).continuousOn
  exact ⟨M, fun u hu => by simpa [Real.norm_eq_abs] using hM u hu⟩

/-- **Degree profile versus section profile.** -/
theorem integral_Dfun_degFun_sub_le {d : ℕ} (hd : 1 ≤ d) (W : Graphon) {ε ζ : ℝ}
    (hε : ε ∈ Icc (0:ℝ) 1) (hζ : ζ ∈ Icc (0:ℝ) 1) :
    ∫ x, Dfun d ε (W.degFun x) ∂unitμ
        - ∫ x, Dfun d ε (ε + (ζ - ε) * sectionMeasure (nearSet W ε ζ) x) ∂unitμ
      ≤ (d : ℝ) * ((d : ℝ) - 1) * (Real.sqrt (gμ (nearSet W ε ζ)).toReal
          * Real.sqrt (∫ z, nearResid W ε ζ z ^ 2 ∂gμ) + ∫ z, nearResid W ε ζ z ^ 2 ∂gμ) := by
  set S := nearSet W ε ζ with hSdef
  have hSm : MeasurableSet S := measurableSet_nearSet W ε ζ
  set sx := sectionMeasure S with hsx
  set r : ℝ → ℝ := fun x => ∫ y, nearResid W ε ζ (x, y) ∂unitμ with hr
  have hsm : Measurable sx := measurable_sectionMeasure hSm
  have hrm : Measurable r :=
    ((measurable_nearResid W ε ζ).stronglyMeasurable).integral_prod_right'.measurable
  have hrb : ∀ x, |r x| ≤ 2 := fun x => by
    have h := norm_integral_le_of_norm_le_const (μ := unitμ)
      (f := fun y => nearResid W ε ζ (x, y))
      (Filter.Eventually.of_forall fun y => by
        simpa [Real.norm_eq_abs] using abs_nearResid_le W hε hζ (x, y))
    simpa [Real.norm_eq_abs, measureReal_def] using h
  have hd1 : (0:ℝ) ≤ (d : ℝ) * ((d : ℝ) - 1) := by
    have : (1:ℝ) ≤ d := by exact_mod_cast hd
    nlinarith
  -- the pointwise bound
  have hpt : ∀ x, Dfun d ε (W.degFun x) - Dfun d ε (ε + (ζ - ε) * sx x)
      ≤ (d : ℝ) * ((d : ℝ) - 1) * (sx x * |r x| + r x ^ 2) := by
    intro x
    have hsmem := sectionMeasure_mem_Icc S x
    have hp : ε + (ζ - ε) * sx x ∈ Icc (0:ℝ) 1 := by
      constructor <;> nlinarith [hsmem.1, hsmem.2, hε.1, hε.2, hζ.1, hζ.2]
    have hq := W.degFun_mem_Icc x
    have hdeg := degFun_eq_near W ε ζ x
    have h := abs_Dfun_sub_le hd hε hp hq
    have hqp : W.degFun x - (ε + (ζ - ε) * sx x) = r x := by rw [hdeg]; ring
    have hpe : |ε + (ζ - ε) * sx x - ε| ≤ sx x := by
      rw [add_sub_cancel_left, abs_mul, abs_of_nonneg hsmem.1]
      have : |ζ - ε| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hε.1, hε.2, hζ.1, hζ.2]
      nlinarith [hsmem.1, abs_nonneg (ζ - ε)]
    rw [hqp] at h
    calc Dfun d ε (W.degFun x) - Dfun d ε (ε + (ζ - ε) * sx x)
        ≤ |Dfun d ε (W.degFun x) - Dfun d ε (ε + (ζ - ε) * sx x)| := le_abs_self _
      _ ≤ (d : ℝ) * ((d : ℝ) - 1) * (|ε + (ζ - ε) * sx x - ε| + |r x|) * |r x| := h
      _ ≤ (d : ℝ) * ((d : ℝ) - 1) * (sx x + |r x|) * |r x| := by
          apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
          exact mul_le_mul_of_nonneg_left (add_le_add hpe le_rfl) hd1
      _ = (d : ℝ) * ((d : ℝ) - 1) * (sx x * |r x| + r x ^ 2) := by
          rw [← sq_abs (r x)]; ring
  -- integrability
  have hDdeg : Integrable (fun x => Dfun d ε (W.degFun x)) unitμ := by
    obtain ⟨M, hM⟩ := exists_abs_Dfun_le d ε
    exact integrable_of_abs_le ((continuous_Dfun d ε).measurable.comp W.measurable_degFun) M
      fun x => hM _ (W.degFun_mem_Icc x)
  have hDsec : Integrable (fun x => Dfun d ε (ε + (ζ - ε) * sx x)) unitμ := by
    obtain ⟨M, hM⟩ := exists_abs_Dfun_le d ε
    refine integrable_of_abs_le ((continuous_Dfun d ε).measurable.comp
      (measurable_const.add (measurable_const.mul hsm))) M fun x => hM _ ?_
    have hsmem := sectionMeasure_mem_Icc S x
    constructor <;> nlinarith [hsmem.1, hsmem.2, hε.1, hε.2, hζ.1, hζ.2]
  have hsr : Integrable (fun x => sx x * |r x|) unitμ :=
    integrable_of_abs_le (hsm.mul hrm.abs) 2 fun x => by
      have hsmem := sectionMeasure_mem_Icc S x
      rw [abs_mul, abs_abs, abs_of_nonneg hsmem.1]
      nlinarith [hrb x, abs_nonneg (r x), hsmem.1, hsmem.2]
  have hr2 : Integrable (fun x => r x ^ 2) unitμ :=
    integrable_of_abs_le (hrm.pow_const 2) 4 fun x => by
      rw [abs_of_nonneg (sq_nonneg _)]
      nlinarith [hrb x, abs_nonneg (r x), sq_abs (r x)]
  have hs2 : Integrable (fun x => sx x ^ 2) unitμ :=
    integrable_of_abs_le (hsm.pow_const 2) 1 fun x => by
      have hsmem := sectionMeasure_mem_Icc S x
      rw [abs_of_nonneg (sq_nonneg _)]
      nlinarith [hsmem.1, hsmem.2]
  have hrabs2 : Integrable (fun x => |r x| ^ 2) unitμ := by simpa [sq_abs] using hr2
  -- Cauchy–Schwarz
  have hcs := integral_mul_le_sqrt_mul_sqrt (μ := unitμ) (f := sx)
    (g := fun x => |r x|) hs2 hrabs2 hsr
  have hs2le : ∫ x, sx x ^ 2 ∂unitμ ≤ (gμ S).toReal := by
    rw [← integral_sectionMeasure hSm]
    exact integral_mono hs2 (sectionMeasure_integrable S hSm) fun x => by
      have hsmem := sectionMeasure_mem_Icc S x
      show sx x ^ 2 ≤ sx x
      nlinarith [hsmem.1, hsmem.2]
  have hr2le := integral_rowResid_sq_le W hε hζ
  have hrabs : ∫ x, |r x| ^ 2 ∂unitμ = ∫ x, r x ^ 2 ∂unitμ := by simp [sq_abs]
  rw [hrabs] at hcs
  have hsq1 : Real.sqrt (∫ x, sx x ^ 2 ∂unitμ) ≤ Real.sqrt (gμ S).toReal := Real.sqrt_le_sqrt hs2le
  have hsq2 : Real.sqrt (∫ x, r x ^ 2 ∂unitμ) ≤ Real.sqrt (∫ z, nearResid W ε ζ z ^ 2 ∂gμ) :=
    Real.sqrt_le_sqrt hr2le
  have hmain : ∫ x, (Dfun d ε (W.degFun x) - Dfun d ε (ε + (ζ - ε) * sx x)) ∂unitμ
      ≤ ∫ x, (d : ℝ) * ((d : ℝ) - 1) * (sx x * |r x| + r x ^ 2) ∂unitμ :=
    integral_mono (hDdeg.sub hDsec) ((hsr.add hr2).const_mul _) hpt
  rw [integral_sub hDdeg hDsec, integral_const_mul, integral_add hsr hr2] at hmain
  refine le_trans hmain (mul_le_mul_of_nonneg_left ?_ hd1)
  have h1 : ∫ x, sx x * |r x| ∂unitμ
      ≤ Real.sqrt (gμ S).toReal * Real.sqrt (∫ z, nearResid W ε ζ z ^ 2 ∂gμ) :=
    le_trans hcs (mul_le_mul hsq1 hsq2 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  linarith

/-- `∫ 1_S = |S|` on `gμ`. -/
theorem integral_indicator_nearSet (W : Graphon) (ε ζ : ℝ) :
    ∫ z, (nearSet W ε ζ).indicator (fun _ => (1:ℝ)) z ∂gμ = (gμ (nearSet W ε ζ)).toReal :=
  integral_indicator_one (measurableSet_nearSet W ε ζ)

/-- **The moment carries the near set**: `𝒟_ε(ζ)|S| - 2d(d-1)|S|^{1/2}‖R‖₂ ≤ ∬ 𝒟_ε(W)`. -/
theorem Dfun_zeta_measure_le {d : ℕ} (hd : 2 ≤ d) (W : Graphon) {ε ζ : ℝ}
    (hε : ε ∈ Icc (0:ℝ) 1) (hζ : ζ ∈ Icc (0:ℝ) 1) :
    Dfun d ε ζ * (gμ (nearSet W ε ζ)).toReal
        - 2 * ((d : ℝ) * ((d : ℝ) - 1)) * (Real.sqrt (gμ (nearSet W ε ζ)).toReal
          * Real.sqrt (∫ z, nearResid W ε ζ z ^ 2 ∂gμ))
      ≤ ∫ z, Dfun d ε (W.toFun z.1 z.2) ∂gμ := by
  set S := nearSet W ε ζ with hSdef
  set ind : ℝ × ℝ → ℝ := S.indicator (fun _ => (1:ℝ)) with hind
  have hd1 : (0:ℝ) ≤ (d : ℝ) * ((d : ℝ) - 1) := by
    have : (2:ℝ) ≤ d := by exact_mod_cast hd
    nlinarith
  have hindm : Measurable ind := measurable_indicator_nearSet W ε ζ
  have hind01 : ∀ z, ind z ∈ Icc (0:ℝ) 1 := fun z => by
    by_cases hz : z ∈ S
    · rw [hind, Set.indicator_of_mem hz]; exact ⟨zero_le_one, le_rfl⟩
    · rw [hind, Set.indicator_of_notMem hz]; exact ⟨le_rfl, zero_le_one⟩
  have hpt : ∀ z, ind z * (Dfun d ε ζ - 2 * ((d : ℝ) * ((d : ℝ) - 1)) * |nearResid W ε ζ z|)
      ≤ Dfun d ε (W.toFun z.1 z.2) := by
    intro z
    by_cases hz : z ∈ S
    · have h1 : ind z = 1 := by rw [hind, Set.indicator_of_mem hz]
      have hR : nearResid W ε ζ z = W.toFun z.1 z.2 - ζ := by
        unfold nearResid; rw [← hSdef, Set.indicator_of_mem hz]; ring
      rw [h1, one_mul, hR]
      have h := abs_Dfun_sub_le (by omega : 1 ≤ d) hε hζ (W.mem_Icc z.1 z.2)
      have hζε : |ζ - ε| ≤ 1 := by
        rw [abs_le]; constructor <;> linarith [hε.1, hε.2, hζ.1, hζ.2]
      have hWζ : |W.toFun z.1 z.2 - ζ| ≤ 1 := by
        have := W.mem_Icc z.1 z.2
        rw [abs_le]; constructor <;> linarith [hζ.1, hζ.2, this.1, this.2]
      have h2 : (d : ℝ) * ((d : ℝ) - 1) * (|ζ - ε| + |W.toFun z.1 z.2 - ζ|)
          * |W.toFun z.1 z.2 - ζ| ≤ 2 * ((d : ℝ) * ((d : ℝ) - 1)) * |W.toFun z.1 z.2 - ζ| := by
        apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
        nlinarith
      have h3 := le_trans h h2
      have h4 := neg_abs_le (Dfun d ε (W.toFun z.1 z.2) - Dfun d ε ζ)
      linarith
    · have h0 : ind z = 0 := by rw [hind, Set.indicator_of_notMem hz]
      rw [h0, zero_mul]
      exact Dfun_nonneg_of_mem hd hε (W.mem_Icc z.1 z.2)
  -- integrability
  obtain ⟨M, hM⟩ := exists_abs_Dfun_le d ε
  have hDint : Integrable (fun z : ℝ × ℝ => Dfun d ε (W.toFun z.1 z.2)) gμ :=
    integrable_of_abs_le ((continuous_Dfun d ε).measurable.comp W.measurable_uncurry) M
      fun z => hM _ (W.mem_Icc z.1 z.2)
  have hRabs : Measurable fun z => |nearResid W ε ζ z| := (measurable_nearResid W ε ζ).abs
  have hindint : Integrable ind gμ :=
    integrable_of_abs_le hindm 1 fun z => by
      rw [abs_of_nonneg (hind01 z).1]; exact (hind01 z).2
  have hindR : Integrable (fun z => ind z * |nearResid W ε ζ z|) gμ :=
    integrable_of_abs_le (hindm.mul hRabs) 2 fun z => by
      rw [abs_mul, abs_abs, abs_of_nonneg (hind01 z).1]
      nlinarith [(hind01 z).1, (hind01 z).2, abs_nearResid_le W hε hζ z,
        abs_nonneg (nearResid W ε ζ z)]
  have hlhs : Integrable (fun z => ind z * (Dfun d ε ζ
      - 2 * ((d : ℝ) * ((d : ℝ) - 1)) * |nearResid W ε ζ z|)) gμ := by
    have : (fun z => ind z * (Dfun d ε ζ - 2 * ((d : ℝ) * ((d : ℝ) - 1)) * |nearResid W ε ζ z|))
        = fun z => Dfun d ε ζ * ind z
          - 2 * ((d : ℝ) * ((d : ℝ) - 1)) * (ind z * |nearResid W ε ζ z|) := by
      funext z; ring
    rw [this]
    exact (hindint.const_mul _).sub (hindR.const_mul _)
  have hint := integral_mono hlhs hDint hpt
  have hexp : ∫ z, ind z * (Dfun d ε ζ - 2 * ((d : ℝ) * ((d : ℝ) - 1)) * |nearResid W ε ζ z|) ∂gμ
      = Dfun d ε ζ * (gμ S).toReal
        - 2 * ((d : ℝ) * ((d : ℝ) - 1)) * ∫ z, ind z * |nearResid W ε ζ z| ∂gμ := by
    have : (fun z => ind z * (Dfun d ε ζ - 2 * ((d : ℝ) * ((d : ℝ) - 1)) * |nearResid W ε ζ z|))
        = fun z => Dfun d ε ζ * ind z
          - 2 * ((d : ℝ) * ((d : ℝ) - 1)) * (ind z * |nearResid W ε ζ z|) := by
      funext z; ring
    rw [this, integral_sub (hindint.const_mul _) (hindR.const_mul _), integral_const_mul,
      integral_const_mul, hind, integral_indicator_nearSet]
  -- Cauchy–Schwarz for `∫ 1_S |R|`
  have hind2 : Integrable (fun z => ind z ^ 2) gμ :=
    integrable_of_abs_le (hindm.pow_const 2) 1 fun z => by
      rw [abs_of_nonneg (sq_nonneg _)]
      nlinarith [(hind01 z).1, (hind01 z).2]
  have hR2 : Integrable (fun z => |nearResid W ε ζ z| ^ 2) gμ := by
    simpa [sq_abs] using integrable_nearResid_sq W hε hζ
  have hcs := integral_mul_le_sqrt_mul_sqrt (μ := gμ) (f := ind)
    (g := fun z => |nearResid W ε ζ z|) hind2 hR2 hindR
  have hind2eq : ∫ z, ind z ^ 2 ∂gμ = (gμ S).toReal := by
    have : (fun z => ind z ^ 2) = ind := by
      funext z
      by_cases hz : z ∈ S
      · rw [hind, Set.indicator_of_mem hz]; norm_num
      · rw [hind, Set.indicator_of_notMem hz]; norm_num
    rw [this, hind, integral_indicator_nearSet]
  have hR2eq : ∫ z, |nearResid W ε ζ z| ^ 2 ∂gμ = ∫ z, nearResid W ε ζ z ^ 2 ∂gμ := by
    simp [sq_abs]
  rw [hind2eq, hR2eq] at hcs
  rw [hexp] at hint
  nlinarith [hcs, hd1]

/-! ### The structure theorem -/

theorem ae_gμ_mem_Icc : ∀ᵐ z ∂gμ, z.1 ∈ Icc (0:ℝ) 1 ∧ z.2 ∈ Icc (0:ℝ) 1 := by
  have h : ∀ᵐ x ∂unitμ, x ∈ Icc (0:ℝ) 1 := ae_restrict_mem measurableSet_Icc
  have h1 : ∀ᵐ z ∂gμ, z.1 ∈ Icc (0:ℝ) 1 := Measure.quasiMeasurePreserving_fst.ae h
  have h2 : ∀ᵐ z ∂gμ, z.2 ∈ Icc (0:ℝ) 1 := Measure.quasiMeasurePreserving_snd.ae h
  filter_upwards [h1, h2] with z hz1 hz2 using ⟨hz1, hz2⟩

/-- `√x √y ≤ √(AB) t⁴` from `x ≤ A t³`, `y ≤ B t⁶`, `0 ≤ t ≤ 1`. -/
theorem sqrt_mul_sqrt_le_t4 {x y A B t : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hxA : x ≤ A * t ^ 3) (hyB : y ≤ B * t ^ 6) :
    Real.sqrt x * Real.sqrt y ≤ Real.sqrt (A * B) * t ^ 4 := by
  rw [← Real.sqrt_mul hx]
  have ht9 : t ^ 9 ≤ t ^ 8 := pow_le_pow_of_le_one ht0 ht1 (by norm_num)
  have hxy : x * y ≤ A * B * (t ^ 4) ^ 2 := by
    calc x * y ≤ (A * t ^ 3) * (B * t ^ 6) := mul_le_mul hxA hyB hy (by positivity)
      _ = A * B * t ^ 9 := by ring
      _ ≤ A * B * t ^ 8 := mul_le_mul_of_nonneg_left ht9 (mul_nonneg hA hB)
      _ = A * B * (t ^ 4) ^ 2 := by ring
  calc Real.sqrt (x * y) ≤ Real.sqrt (A * B * (t ^ 4) ^ 2) := Real.sqrt_le_sqrt hxy
    _ = Real.sqrt (A * B) * t ^ 4 := by
        rw [Real.sqrt_mul (mul_nonneg hA hB), Real.sqrt_sq (by positivity)]

/-- `|S| ≤ 4‖W - ε‖₂²/(ζ - ε)²`. -/
theorem measure_nearSet_le (W : Graphon) {ε ζ : ℝ} (hne : ζ ≠ ε) :
    (gμ (nearSet W ε ζ)).toReal ≤ 4 / (ζ - ε) ^ 2 * ∫ z, (W.toFun z.1 z.2 - ε) ^ 2 ∂gμ := by
  have hint1 : Integrable ((nearSet W ε ζ).indicator (fun _ : ℝ × ℝ => (1:ℝ))) gμ :=
    integrable_of_abs_le (measurable_indicator_nearSet W ε ζ) 1 fun z => by
      by_cases hz : z ∈ nearSet W ε ζ
      · rw [Set.indicator_of_mem hz]; simp
      · rw [Set.indicator_of_notMem hz]; simp
  have hint2 : Integrable (fun z : ℝ × ℝ => 4 / (ζ - ε) ^ 2 * (W.toFun z.1 z.2 - ε) ^ 2) gμ :=
    (W.integrable_comp (g := fun u => (u - ε) ^ 2) (by fun_prop) (by fun_prop)).const_mul _
  have h := integral_mono hint1 hint2 (indicator_nearSet_le W hne)
  rwa [integral_indicator_nearSet, integral_const_mul] at h

/-- `∫ R² = ∫ min((W-ε)², (W-ζ)²)`. -/
theorem integral_nearResid_sq (W : Graphon) (ε ζ : ℝ) :
    ∫ z, nearResid W ε ζ z ^ 2 ∂gμ
      = ∫ z, min ((W.toFun z.1 z.2 - ε) ^ 2) ((W.toFun z.1 z.2 - ζ) ^ 2) ∂gμ :=
  integral_congr_ae (Filter.Eventually.of_forall fun z => sq_resid_nearSet W ε ζ z)

/-- The cross profile is `L²`-close to `W` when the near set is close to the cross:
`‖W - W₀^I‖₂² ≤ 2‖R‖₂² + 2|S △ X|`. -/
theorem integral_sub_crossProfile_sq_le (W : Graphon) {ε ζ : ℝ} (hε : ε ∈ Icc (0:ℝ) 1)
    (hζ : ζ ∈ Icc (0:ℝ) 1) {I : Set ℝ} (hI : MeasurableSet I) :
    ∫ z, (W.toFun z.1 z.2 - crossProfile ε ζ I z) ^ 2 ∂gμ
      ≤ 2 * ∫ z, nearResid W ε ζ z ^ 2 ∂gμ
        + 2 * (gμ ((nearSet W ε ζ \ crossSet I) ∪ (crossSet I \ nearSet W ε ζ))).toReal := by
  set S := nearSet W ε ζ with hSdef
  set X := crossSet I with hX
  have hSm : MeasurableSet S := measurableSet_nearSet W ε ζ
  have hXm : MeasurableSet X := measurableSet_crossSet hI
  set D : Set (ℝ × ℝ) := (S \ X) ∪ (X \ S) with hD
  have hDm : MeasurableSet D := (hSm.diff hXm).union (hXm.diff hSm)
  have hζε : (ζ - ε) ^ 2 ≤ 1 := by
    have : |ζ - ε| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hε.1, hε.2, hζ.1, hζ.2]
    rw [← sq_abs]; nlinarith [abs_nonneg (ζ - ε)]
  have hpt : ∀ z, (W.toFun z.1 z.2 - crossProfile ε ζ I z) ^ 2
      ≤ 2 * nearResid W ε ζ z ^ 2 + 2 * D.indicator (fun _ => (1:ℝ)) z := by
    intro z
    have hdecomp : W.toFun z.1 z.2 - crossProfile ε ζ I z
        = nearResid W ε ζ z + (ζ - ε) * (S.indicator (fun _ => (1:ℝ)) z
          - X.indicator (fun _ => (1:ℝ)) z) := by
      unfold nearResid crossProfile; ring
    have hind : (S.indicator (fun _ => (1:ℝ)) z - X.indicator (fun _ => (1:ℝ)) z) ^ 2
        = D.indicator (fun _ => (1:ℝ)) z := by
      by_cases hS : z ∈ S <;> by_cases hXz : z ∈ X
      · have hzD : z ∉ D := by
          rw [hD]; rintro (⟨-, h⟩ | ⟨-, h⟩)
          · exact h hXz
          · exact h hS
        simp [Set.indicator_of_mem hS, Set.indicator_of_mem hXz, Set.indicator_of_notMem hzD]
      · have hzD : z ∈ D := Or.inl ⟨hS, hXz⟩
        simp [Set.indicator_of_mem hS, Set.indicator_of_notMem hXz, Set.indicator_of_mem hzD]
      · have hzD : z ∈ D := Or.inr ⟨hXz, hS⟩
        simp [Set.indicator_of_notMem hS, Set.indicator_of_mem hXz, Set.indicator_of_mem hzD]
      · have hzD : z ∉ D := by
          rw [hD]; rintro (⟨h, -⟩ | ⟨h, -⟩)
          · exact hS h
          · exact hXz h
        simp [Set.indicator_of_notMem hS, Set.indicator_of_notMem hXz,
          Set.indicator_of_notMem hzD]
    have hD0 : 0 ≤ D.indicator (fun _ => (1:ℝ)) z := Set.indicator_nonneg (fun _ _ => zero_le_one) z
    rw [hdecomp]
    have h1 := two_mul_le_add_sq (nearResid W ε ζ z)
      ((ζ - ε) * (S.indicator (fun _ => (1:ℝ)) z - X.indicator (fun _ => (1:ℝ)) z))
    have h2 : ((ζ - ε) * (S.indicator (fun _ => (1:ℝ)) z - X.indicator (fun _ => (1:ℝ)) z)) ^ 2
        ≤ D.indicator (fun _ => (1:ℝ)) z := by
      rw [mul_pow, hind]
      calc (ζ - ε) ^ 2 * D.indicator (fun _ => (1:ℝ)) z ≤ 1 * D.indicator (fun _ => (1:ℝ)) z :=
            mul_le_mul_of_nonneg_right hζε hD0
        _ = D.indicator (fun _ => (1:ℝ)) z := one_mul _
    nlinarith [h1, h2]
  have hint1 : Integrable (fun z => (W.toFun z.1 z.2 - crossProfile ε ζ I z) ^ 2) gμ := by
    have hm : Measurable fun z : ℝ × ℝ => (W.toFun z.1 z.2 - crossProfile ε ζ I z) ^ 2 := by
      unfold crossProfile
      exact (W.measurable_uncurry.sub (measurable_const.add (measurable_const.mul
        (measurable_const.indicator hXm)))).pow_const 2
    refine integrable_of_abs_le hm 4 fun z => ?_
    rw [abs_of_nonneg (sq_nonneg _)]
    have hW := W.mem_Icc z.1 z.2
    have hind01 : X.indicator (fun _ => (1:ℝ)) z ∈ Icc (0:ℝ) 1 := by
      by_cases hz : z ∈ X
      · rw [Set.indicator_of_mem hz]; exact ⟨zero_le_one, le_rfl⟩
      · rw [Set.indicator_of_notMem hz]; exact ⟨le_rfl, zero_le_one⟩
    have hb : |W.toFun z.1 z.2 - crossProfile ε ζ I z| ≤ 2 := by
      unfold crossProfile
      have : |(ζ - ε) * X.indicator (fun _ => (1:ℝ)) z| ≤ 1 := by
        rw [abs_mul, abs_of_nonneg hind01.1]
        have : |ζ - ε| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hε.1, hε.2, hζ.1, hζ.2]
        nlinarith [hind01.2, abs_nonneg (ζ - ε)]
      rw [abs_le] at this ⊢
      constructor <;> linarith [hW.1, hW.2, hε.1, hε.2, this.1, this.2]
    nlinarith [abs_nonneg (W.toFun z.1 z.2 - crossProfile ε ζ I z),
      sq_abs (W.toFun z.1 z.2 - crossProfile ε ζ I z)]
  have hint2 : Integrable (fun z => 2 * nearResid W ε ζ z ^ 2
      + 2 * D.indicator (fun _ => (1:ℝ)) z) gμ :=
    ((integrable_nearResid_sq W hε hζ).const_mul 2).add
      ((integrable_of_abs_le (measurable_const.indicator hDm) 1 fun z => by
        by_cases hz : z ∈ D
        · rw [Set.indicator_of_mem hz]; simp
        · rw [Set.indicator_of_notMem hz]; simp).const_mul 2)
  have h := integral_mono hint1 hint2 hpt
  rw [integral_add ((integrable_nearResid_sq W hε hζ).const_mul 2)
    ((integrable_of_abs_le (measurable_const.indicator hDm) 1 fun z => by
        by_cases hz : z ∈ D
        · rw [Set.indicator_of_mem hz]; simp
        · rw [Set.indicator_of_notMem hz]; simp).const_mul 2),
    integral_const_mul, integral_const_mul] at h
  have hDint : ∫ z, D.indicator (fun _ => (1:ℝ)) z ∂gμ = (gμ D).toReal :=
    integral_indicator_one hDm
  rw [hDint] at h
  exact h

theorem unitμ_inter_Icc {I : Set ℝ} (hI : MeasurableSet I) : unitμ (I ∩ Icc 0 1) = unitμ I := by
  unfold unitμ
  rw [Measure.restrict_apply (hI.inter measurableSet_Icc), Measure.restrict_apply hI,
    Set.inter_assoc, Set.inter_self]

theorem integral_crossProfile_inter_Icc (W : Graphon) (ε ζ : ℝ) (I : Set ℝ) :
    ∫ z, (W.toFun z.1 z.2 - crossProfile ε ζ (I ∩ Icc 0 1) z) ^ 2 ∂gμ
      = ∫ z, (W.toFun z.1 z.2 - crossProfile ε ζ I z) ^ 2 ∂gμ := by
  refine integral_congr_ae ?_
  filter_upwards [ae_gμ_mem_Icc] with z hz
  have e1 : z.1 ∈ I ∩ Icc 0 1 ↔ z.1 ∈ I := ⟨fun h => h.1, fun h => ⟨h, hz.1⟩⟩
  have e2 : z.2 ∈ I ∩ Icc 0 1 ↔ z.2 ∈ I := ⟨fun h => h.1, fun h => ⟨h, hz.2⟩⟩
  have hiff : z ∈ crossSet (I ∩ Icc 0 1) ↔ z ∈ crossSet I := by
    show (z.1 ∈ I ∩ Icc 0 1 ∧ z.2 ∉ I ∩ Icc 0 1) ∨ (z.1 ∉ I ∩ Icc 0 1 ∧ z.2 ∈ I ∩ Icc 0 1)
      ↔ (z.1 ∈ I ∧ z.2 ∉ I) ∨ (z.1 ∉ I ∧ z.2 ∈ I)
    rw [e1, e2]
  unfold crossProfile
  by_cases h : z ∈ crossSet I
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hiff.mpr h)]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h (hiff.mp h'))]

/-- The cross lemma with defect, specialised to the profile `φ(s) = 𝒟_ε(ε + (ζ - ε)s)`. -/
theorem nearSet_cross_bounds {d : ℕ} (hd : 2 ≤ d) (W : Graphon) {ε ζ : ℝ}
    (hε : ε ∈ Icc (0:ℝ) 1) (hζ : ζ ∈ Icc (0:ℝ) 1) {γ : ℝ} (hγ : 0 < γ)
    (hγle : γ ≤ Dfun d ε ζ / 2 - Dfun d ε ((ε + ζ) / 2)) {t : ℝ} (ht0 : 0 < t)
    (ht : t ≤ 1 / 2) :
    (gμ ((nearSet W ε ζ \ crossSet {x | 1 / 2 ≤ sectionMeasure (nearSet W ε ζ) x})
        ∪ (crossSet {x | 1 / 2 ≤ sectionMeasure (nearSet W ε ζ) x} \ nearSet W ε ζ))).toReal
      ≤ ((gμ (nearSet W ε ζ)).toReal / t) ^ 2 + 2 / γ * ((Dfun d ε ζ * (gμ (nearSet W ε ζ)).toReal / 2
          - ∫ x, Dfun d ε (ε + (ζ - ε) * sectionMeasure (nearSet W ε ζ) x) ∂unitμ)
          + Dfun d ε ζ * ((gμ (nearSet W ε ζ)).toReal / t) ^ 2 / 2
          + (d : ℝ) * ((d : ℝ) - 1) * t * (gμ (nearSet W ε ζ)).toReal) ∧
    ∫ x, Dfun d ε (ε + (ζ - ε) * sectionMeasure (nearSet W ε ζ) x) ∂unitμ
      ≤ Dfun d ε ζ * (unitμ {x | 1 / 2 ≤ sectionMeasure (nearSet W ε ζ) x}).toReal
        + (d : ℝ) * ((d : ℝ) - 1) * (1 / (2 * γ) * ((Dfun d ε ζ * (gμ (nearSet W ε ζ)).toReal / 2
          - ∫ x, Dfun d ε (ε + (ζ - ε) * sectionMeasure (nearSet W ε ζ) x) ∂unitμ)
          + Dfun d ε ζ * ((gμ (nearSet W ε ζ)).toReal / t) ^ 2 / 2
          + (d : ℝ) * ((d : ℝ) - 1) * t * (gμ (nearSet W ε ζ)).toReal)
          + t * (gμ (nearSet W ε ζ)).toReal) := by
  have hφ1 : (fun s => Dfun d ε (ε + (ζ - ε) * s)) 1 = Dfun d ε ζ := by
    simp only [mul_one, add_sub_cancel]
  have hφh : (fun s => Dfun d ε (ε + (ζ - ε) * s)) (1 / 2) = Dfun d ε ((ε + ζ) / 2) := by
    simp only
    congr 1; ring
  have hφ0 : (fun s => Dfun d ε (ε + (ζ - ε) * s)) 0 = 0 := by
    simp only [mul_zero, add_zero]; unfold Dfun; simp
  have hφm : Measurable (fun s => Dfun d ε (ε + (ζ - ε) * s)) :=
    ((continuous_Dfun d ε).comp (continuous_const.add (continuous_const.mul continuous_id))).measurable
  have hφq : ∀ s ∈ Icc (0:ℝ) 1, (fun s => Dfun d ε (ε + (ζ - ε) * s)) s
      ≤ (d : ℝ) * ((d : ℝ) - 1) * s ^ 2 := fun s hs =>
    Dfun_affine_le_sq (by omega) hε hζ hs
  have hφnn : ∀ s ∈ Icc (0:ℝ) 1, 0 ≤ (fun s => Dfun d ε (ε + (ζ - ε) * s)) s := fun s hs => by
    apply Dfun_nonneg_of_mem hd hε
    constructor <;> nlinarith [hs.1, hs.2, hε.1, hε.2, hζ.1, hζ.2]
  have hγle' : γ ≤ (fun s => Dfun d ε (ε + (ζ - ε) * s)) 1 / 2
      - (fun s => Dfun d ε (ε + (ζ - ε) * s)) (1 / 2) := by
    rw [hφ1, hφh]; exact hγle
  have h := cross_structure (measurableSet_nearSet W ε ζ) (nearSet_symm W ε ζ) hφm
    (convexOn_Dfun_affine d hε hζ) hφ0 hφq hφnn hγ hγle' ht0 ht
  have hφ1' : Dfun d ε (ε + (ζ - ε) * 1) = Dfun d ε ζ := by simp only [mul_one, add_sub_cancel]
  rw [hφ1'] at h
  exact h

set_option maxHeartbeats 1000000 in
/-- **The structure theorem** (draft `kb:prop:structure`, deterministic form).  With `ϑ = t³`:
if `W` is `L²`-close to the two values `ε, ζ` at scale `ϑ`, has `L²` deviation `O(ϑ)`, `d`-th
moment excess at most `2ϑ/B + O(ϑ²)`, and degree profile at least `ϑ/B - O(ϑ^{4/3})`, then `W`
is within `O(ϑ^{4/3})` in `L²` of a cross with block `|I| ≍ ϑ`. -/
theorem structure_of_bounds {d : ℕ} (hd : 2 ≤ d) {K₁ K₂ K₃ K₄ B₀ B₁ a₀ γ Φ₁ : ℝ}
    (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂) (hK₃ : 0 ≤ K₃) (hK₄ : 0 ≤ K₄) (hB₀ : 0 < B₀)
    (hB₀₁ : B₀ ≤ B₁) (ha₀ : 0 < a₀) (hγ : 0 < γ) (hΦ₁ : 0 < Φ₁) :
    ∃ K t₀ : ℝ, 0 < K ∧ 0 < t₀ ∧ ∀ (W : Graphon) (ε ζ B t : ℝ),
      ε ∈ Icc (0:ℝ) 1 → ζ ∈ Icc (0:ℝ) 1 → a₀ ≤ |ζ - ε| → B₀ ≤ B → B ≤ B₁ →
      γ ≤ Dfun d ε ζ / 2 - Dfun d ε ((ε + ζ) / 2) → Dfun d ε ζ ≤ Φ₁ →
      0 < t → t ≤ t₀ →
      ∫ z, min ((W.toFun z.1 z.2 - ε) ^ 2) ((W.toFun z.1 z.2 - ζ) ^ 2) ∂gμ ≤ K₁ * t ^ 6 →
      ∫ z, (W.toFun z.1 z.2 - ε) ^ 2 ∂gμ ≤ K₂ * t ^ 3 →
      ∫ z, Dfun d ε (W.toFun z.1 z.2) ∂gμ ≤ 2 * t ^ 3 / B + K₃ * t ^ 6 →
      t ^ 3 ≤ B * ∫ x, Dfun d ε (W.degFun x) ∂unitμ + K₄ * t ^ 4 →
      ∃ I : Set ℝ, MeasurableSet I ∧ I ⊆ Icc 0 1 ∧
        t ^ 3 / K ≤ (unitμ I).toReal ∧ (unitμ I).toReal ≤ K * t ^ 3 ∧
        ∫ z, (W.toFun z.1 z.2 - crossProfile ε ζ I z) ^ 2 ∂gμ ≤ K * t ^ 4 := by
  classical
  have hB₁ : 0 < B₁ := lt_of_lt_of_le hB₀ hB₀₁
  set dd : ℝ := (d : ℝ) * ((d : ℝ) - 1) with hdd
  have hdd0 : 0 ≤ dd := by
    have : (2:ℝ) ≤ d := by exact_mod_cast hd
    rw [hdd]; nlinarith
  set A₂ : ℝ := 4 * K₂ / a₀ ^ 2 with hA₂
  have hA₂0 : 0 ≤ A₂ := by positivity
  set c₃ : ℝ := Real.sqrt (A₂ * K₁) with hc₃
  have hc₃0 : 0 ≤ c₃ := Real.sqrt_nonneg _
  set c₄ : ℝ := K₃ / 2 + 2 * dd * c₃ + K₄ / B₀ + dd * K₁ with hc₄
  have hc₄0 : 0 ≤ c₄ := by positivity
  set c₅ : ℝ := c₄ + Φ₁ * A₂ ^ 2 / 2 + dd * A₂ with hc₅
  have hc₅0 : 0 ≤ c₅ := by positivity
  set c₆ : ℝ := A₂ ^ 2 + 2 / γ * c₅ with hc₆
  have hc₆0 : 0 ≤ c₆ := by positivity
  set c₇ : ℝ := K₄ / B₀ + dd * (c₃ + K₁) + dd * (1 / (2 * γ) * c₅ + A₂) with hc₇
  have hc₇0 : 0 ≤ c₇ := by positivity
  refine ⟨max (max (2 * K₁ + 2 * c₆) (2 * A₂)) (max (2 * B₁ * Φ₁) 1),
    min (1 / 2) (1 / (2 * B₁ * (c₇ + 1))), by positivity, by positivity, ?_⟩
  intro W ε ζ B t hε hζ ha hB₀B hBB₁ hγle hΦ ht0 ht hmin hL2 hmom hstar
  have ht12 : t ≤ 1 / 2 := le_trans ht (min_le_left _ _)
  have ht1 : t ≤ 1 := le_trans ht12 (by norm_num)
  have htc : t ≤ 1 / (2 * B₁ * (c₇ + 1)) := le_trans ht (min_le_right _ _)
  have hB : 0 < B := lt_of_lt_of_le hB₀ hB₀B
  have hne : ζ ≠ ε := by
    intro h; rw [h, sub_self, abs_zero] at ha; exact absurd ha (not_le.mpr ha₀)
  have ha2 : a₀ ^ 2 ≤ (ζ - ε) ^ 2 := by
    rw [← sq_abs (ζ - ε)]; exact pow_le_pow_left₀ ha₀.le ha 2
  set S := nearSet W ε ζ with hSdef
  set σ : ℝ := (gμ S).toReal with hσ
  have hσ0 : 0 ≤ σ := ENNReal.toReal_nonneg
  set Q : ℝ := ∫ z, nearResid W ε ζ z ^ 2 ∂gμ with hQ
  have hQ0 : 0 ≤ Q := integral_nonneg fun _ => sq_nonneg _
  have hQle : Q ≤ K₁ * t ^ 6 := by rw [hQ, integral_nearResid_sq]; exact hmin
  have hσle : σ ≤ A₂ * t ^ 3 := by
    have h := measure_nearSet_le W hne
    have hint0 : 0 ≤ ∫ z, (W.toFun z.1 z.2 - ε) ^ 2 ∂gμ := integral_nonneg fun _ => sq_nonneg _
    have h1 : 4 / (ζ - ε) ^ 2 ≤ 4 / a₀ ^ 2 :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) ha2
    calc σ ≤ 4 / (ζ - ε) ^ 2 * ∫ z, (W.toFun z.1 z.2 - ε) ^ 2 ∂gμ := h
      _ ≤ 4 / a₀ ^ 2 * (K₂ * t ^ 3) := mul_le_mul h1 hL2 hint0 (by positivity)
      _ = A₂ * t ^ 3 := by rw [hA₂]; ring
  have hsq := sqrt_mul_sqrt_le_t4 hσ0 hQ0 hA₂0 hK₁ ht0.le ht1 hσle hQle
  have ht64 : t ^ 6 ≤ t ^ 4 := pow_le_pow_of_le_one ht0.le ht1 (by norm_num)
  have hK₁t : K₁ * t ^ 6 ≤ K₁ * t ^ 4 := mul_le_mul_of_nonneg_left ht64 hK₁
  have hK₃t : K₃ * t ^ 6 ≤ K₃ * t ^ 4 := mul_le_mul_of_nonneg_left ht64 hK₃
  have hsqQ : Real.sqrt σ * Real.sqrt Q + Q ≤ (c₃ + K₁) * t ^ 4 := by
    have : (c₃ + K₁) * t ^ 4 = c₃ * t ^ 4 + K₁ * t ^ 4 := by ring
    linarith
  set Φs : ℝ := ∫ x, Dfun d ε (ε + (ζ - ε) * sectionMeasure S x) ∂unitμ with hΦs
  -- the degree and moment inputs
  have hE1 : ∫ x, Dfun d ε (W.degFun x) ∂unitμ - Φs ≤ dd * (Real.sqrt σ * Real.sqrt Q + Q) :=
    integral_Dfun_degFun_sub_le (by omega) W hε hζ
  have hE2 : Dfun d ε ζ * σ - 2 * dd * (Real.sqrt σ * Real.sqrt Q) ≤ ∫ z, Dfun d ε (W.toFun z.1 z.2) ∂gμ :=
    Dfun_zeta_measure_le hd W hε hζ
  have hdeg : t ^ 3 / B - K₄ / B₀ * t ^ 4 ≤ ∫ x, Dfun d ε (W.degFun x) ∂unitμ := by
    have h1 : t ^ 3 - K₄ * t ^ 4 ≤ B * ∫ x, Dfun d ε (W.degFun x) ∂unitμ := by linarith
    have h2 : (t ^ 3 - K₄ * t ^ 4) / B ≤ ∫ x, Dfun d ε (W.degFun x) ∂unitμ := by
      rw [div_le_iff₀ hB]; linarith
    have h3 : K₄ * t ^ 4 / B ≤ K₄ / B₀ * t ^ 4 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ hB hB₀]
      exact mul_le_mul_of_nonneg_left hB₀B (by positivity)
    have h4 : (t ^ 3 - K₄ * t ^ 4) / B = t ^ 3 / B - K₄ * t ^ 4 / B := sub_div _ _ _
    linarith
  have hddsq : dd * (Real.sqrt σ * Real.sqrt Q + Q) ≤ dd * (c₃ + K₁) * t ^ 4 := by
    calc dd * (Real.sqrt σ * Real.sqrt Q + Q) ≤ dd * ((c₃ + K₁) * t ^ 4) :=
          mul_le_mul_of_nonneg_left hsqQ hdd0
      _ = dd * (c₃ + K₁) * t ^ 4 := by ring
  have hΦs_low : t ^ 3 / B - (K₄ / B₀ + dd * (c₃ + K₁)) * t ^ 4 ≤ Φs := by
    have : (K₄ / B₀ + dd * (c₃ + K₁)) * t ^ 4 = K₄ / B₀ * t ^ 4 + dd * (c₃ + K₁) * t ^ 4 := by ring
    linarith
  have hDef : Dfun d ε ζ * σ / 2 - Φs ≤ c₄ * t ^ 4 := by
    have h1 : 2 * dd * (Real.sqrt σ * Real.sqrt Q) ≤ 2 * dd * c₃ * t ^ 4 := by
      calc 2 * dd * (Real.sqrt σ * Real.sqrt Q) ≤ 2 * dd * (c₃ * t ^ 4) :=
            mul_le_mul_of_nonneg_left hsq (by positivity)
        _ = 2 * dd * c₃ * t ^ 4 := by ring
    have h2 : Dfun d ε ζ * σ ≤ 2 * t ^ 3 / B + K₃ * t ^ 4 + 2 * dd * c₃ * t ^ 4 := by linarith
    have h3 : 2 * t ^ 3 / B = 2 * (t ^ 3 / B) := by ring
    have h4 : c₄ * t ^ 4 = K₃ / 2 * t ^ 4 + dd * c₃ * t ^ 4 + (K₄ / B₀ + dd * (c₃ + K₁)) * t ^ 4 := by
      rw [hc₄]; ring
    linarith
  -- the cross bounds
  obtain ⟨hsymmdiff, hlow⟩ := nearSet_cross_bounds hd W hε hζ hγ hγle ht0 ht12
  have hSm : MeasurableSet S := measurableSet_nearSet W ε ζ
  set I₀ : Set ℝ := {x | 1 / 2 ≤ sectionMeasure S x} with hI₀
  have hI₀m : MeasurableSet I₀ := measurableSet_le measurable_const (measurable_sectionMeasure hSm)
  set E : ℝ := (Dfun d ε ζ * σ / 2 - Φs) + Dfun d ε ζ * (σ / t) ^ 2 / 2 + dd * t * σ with hE
  have hD0 : 0 ≤ Dfun d ε ζ := Dfun_nonneg_of_mem hd hε hζ
  have hσt : σ / t ≤ A₂ * t ^ 2 := by
    rw [div_le_iff₀ ht0]
    calc σ ≤ A₂ * t ^ 3 := hσle
      _ = A₂ * t ^ 2 * t := by ring
  have hσt0 : 0 ≤ σ / t := div_nonneg hσ0 ht0.le
  have hσt2 : (σ / t) ^ 2 ≤ A₂ ^ 2 * t ^ 4 := by
    calc (σ / t) ^ 2 ≤ (A₂ * t ^ 2) ^ 2 := pow_le_pow_left₀ hσt0 hσt 2
      _ = A₂ ^ 2 * t ^ 4 := by ring
  have htσ : t * σ ≤ A₂ * t ^ 4 := by
    calc t * σ ≤ t * (A₂ * t ^ 3) := mul_le_mul_of_nonneg_left hσle ht0.le
      _ = A₂ * t ^ 4 := by ring
  have hEle : E ≤ c₅ * t ^ 4 := by
    have h1 : Dfun d ε ζ * (σ / t) ^ 2 ≤ Φ₁ * (A₂ ^ 2 * t ^ 4) :=
      mul_le_mul hΦ hσt2 (sq_nonneg _) hΦ₁.le
    have h2 : dd * t * σ ≤ dd * A₂ * t ^ 4 := by
      calc dd * t * σ = dd * (t * σ) := by ring
        _ ≤ dd * (A₂ * t ^ 4) := mul_le_mul_of_nonneg_left htσ hdd0
        _ = dd * A₂ * t ^ 4 := by ring
    have h3 : c₅ * t ^ 4 = c₄ * t ^ 4 + Φ₁ * (A₂ ^ 2 * t ^ 4) / 2 + dd * A₂ * t ^ 4 := by
      rw [hc₅]; ring
    rw [hE]
    linarith
  have hsd : (gμ ((S \ crossSet I₀) ∪ (crossSet I₀ \ S))).toReal ≤ c₆ * t ^ 4 := by
    have h1 : 2 / γ * E ≤ 2 / γ * (c₅ * t ^ 4) := mul_le_mul_of_nonneg_left hEle (by positivity)
    have h2 : c₆ * t ^ 4 = A₂ ^ 2 * t ^ 4 + 2 / γ * (c₅ * t ^ 4) := by rw [hc₆]; ring
    have h3 : (gμ ((S \ crossSet I₀) ∪ (crossSet I₀ \ S))).toReal ≤ (σ / t) ^ 2 + 2 / γ * E :=
      hsymmdiff
    linarith
  have hL2' : ∫ z, (W.toFun z.1 z.2 - crossProfile ε ζ I₀ z) ^ 2 ∂gμ
      ≤ (2 * K₁ + 2 * c₆) * t ^ 4 := by
    have h := integral_sub_crossProfile_sq_le W hε hζ hI₀m
    have h2 : (2 * K₁ + 2 * c₆) * t ^ 4 = 2 * (K₁ * t ^ 4) + 2 * (c₆ * t ^ 4) := by ring
    rw [← hSdef, ← hQ] at h
    linarith
  have hIup : (unitμ I₀).toReal ≤ 2 * A₂ * t ^ 3 := by
    have h := measure_sectionMeasure_ge_le hSm (by norm_num : (0:ℝ) < 1 / 2)
    calc (unitμ I₀).toReal ≤ σ / (1 / 2) := h
      _ = 2 * σ := by ring
      _ ≤ 2 * (A₂ * t ^ 3) := by linarith
      _ = 2 * A₂ * t ^ 3 := by ring
  have hIlow : t ^ 3 / (2 * B₁ * Φ₁) ≤ (unitμ I₀).toReal := by
    have hlow' : Φs ≤ Dfun d ε ζ * (unitμ I₀).toReal + dd * (1 / (2 * γ) * E + t * σ) := hlow
    have h1 : dd * (1 / (2 * γ) * E + t * σ) ≤ dd * (1 / (2 * γ) * c₅ + A₂) * t ^ 4 := by
      have h11 : 1 / (2 * γ) * E ≤ 1 / (2 * γ) * (c₅ * t ^ 4) :=
        mul_le_mul_of_nonneg_left hEle (by positivity)
      have h12 : 1 / (2 * γ) * E + t * σ ≤ (1 / (2 * γ) * c₅ + A₂) * t ^ 4 := by
        have : (1 / (2 * γ) * c₅ + A₂) * t ^ 4 = 1 / (2 * γ) * (c₅ * t ^ 4) + A₂ * t ^ 4 := by
          ring
        linarith
      calc dd * (1 / (2 * γ) * E + t * σ) ≤ dd * ((1 / (2 * γ) * c₅ + A₂) * t ^ 4) :=
            mul_le_mul_of_nonneg_left h12 hdd0
        _ = dd * (1 / (2 * γ) * c₅ + A₂) * t ^ 4 := by ring
    have h2 : t ^ 3 / B - c₇ * t ^ 4 ≤ Dfun d ε ζ * (unitμ I₀).toReal := by
      have h3 : c₇ * t ^ 4 = (K₄ / B₀ + dd * (c₃ + K₁)) * t ^ 4
          + dd * (1 / (2 * γ) * c₅ + A₂) * t ^ 4 := by rw [hc₇]; ring
      linarith
    have hI0 : 0 ≤ (unitμ I₀).toReal := ENNReal.toReal_nonneg
    have h4 : Dfun d ε ζ * (unitμ I₀).toReal ≤ Φ₁ * (unitμ I₀).toReal :=
      mul_le_mul_of_nonneg_right hΦ hI0
    have h5 : t ^ 3 / B₁ ≤ t ^ 3 / B := div_le_div_of_nonneg_left (by positivity) hB hBB₁
    have h6 : c₇ * t ^ 4 ≤ t ^ 3 / (2 * B₁) := by
      have hct : (c₇ + 1) * t ≤ 1 / (2 * B₁) := by
        have hpos : 0 < 2 * B₁ * (c₇ + 1) := by positivity
        rw [le_div_iff₀ hpos] at htc
        rw [le_div_iff₀ (by positivity)]
        linarith
      calc c₇ * t ^ 4 ≤ (c₇ + 1) * t ^ 4 :=
            mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        _ = (c₇ + 1) * t * t ^ 3 := by ring
        _ ≤ 1 / (2 * B₁) * t ^ 3 := mul_le_mul_of_nonneg_right hct (by positivity)
        _ = t ^ 3 / (2 * B₁) := by ring
    have h7 : t ^ 3 / (2 * B₁) ≤ Φ₁ * (unitμ I₀).toReal := by
      have : t ^ 3 / B₁ = 2 * (t ^ 3 / (2 * B₁)) := by field_simp
      linarith
    rw [div_le_iff₀ (by positivity)]
    have h8 := mul_le_mul_of_nonneg_left h7 (by positivity : (0:ℝ) ≤ 2 * B₁)
    calc t ^ 3 = 2 * B₁ * (t ^ 3 / (2 * B₁)) := by field_simp
      _ ≤ 2 * B₁ * (Φ₁ * (unitμ I₀).toReal) := h8
      _ = (unitμ I₀).toReal * (2 * B₁ * Φ₁) := by ring
  -- pass to `I₀ ∩ [0,1]`
  have hμ : unitμ (I₀ ∩ Icc 0 1) = unitμ I₀ := unitμ_inter_Icc hI₀m
  have hKge1 : 2 * K₁ + 2 * c₆ ≤ max (max (2 * K₁ + 2 * c₆) (2 * A₂)) (max (2 * B₁ * Φ₁) 1) :=
    le_trans (le_max_left _ _) (le_max_left _ _)
  have hKge2 : 2 * A₂ ≤ max (max (2 * K₁ + 2 * c₆) (2 * A₂)) (max (2 * B₁ * Φ₁) 1) :=
    le_trans (le_max_right _ _) (le_max_left _ _)
  have hKge3 : 2 * B₁ * Φ₁ ≤ max (max (2 * K₁ + 2 * c₆) (2 * A₂)) (max (2 * B₁ * Φ₁) 1) :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  refine ⟨I₀ ∩ Icc 0 1, hI₀m.inter measurableSet_Icc, Set.inter_subset_right, ?_, ?_, ?_⟩
  · rw [hμ]
    exact le_trans (div_le_div_of_nonneg_left (by positivity) (by positivity) hKge3) hIlow
  · rw [hμ]
    exact le_trans hIup (mul_le_mul_of_nonneg_right hKge2 (by positivity))
  · rw [integral_crossProfile_inter_Icc W ε ζ I₀]
    exact le_trans hL2' (mul_le_mul_of_nonneg_right hKge1 (by positivity))

end UpperTailOptimizers
