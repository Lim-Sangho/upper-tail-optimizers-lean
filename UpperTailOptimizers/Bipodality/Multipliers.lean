import UpperTailOptimizers.Bipodality.PinnedRow

/-!
# Qualifying directions from two regions, and the multipliers

If `W` is close to a value `c_k` on a symmetric region `E_k` of positive measure where `Γ_W` is
close to `γ_k`, and `γ₁ ≠ γ₂`, then the indicators of `E₁, E₂` are qualifying directions, and
the Euler–Lagrange multipliers satisfy

  `α + β A_k = S_k`,  `A_k = avg_{E_k} Γ_W ≈ γ_k`,  `S_k = avg_{E_k} S₀'(W) ≈ S₀'(c_k)`,

so `(α, β)` is close to the solution `(α₀, β₀)` of `α₀ + β₀ γ_k = S₀'(c_k)`.

## Contents

* `ratio_approx` — perturbation of a ratio;
* `Graphon.exists_qualDirs_of_regions` — the construction with multiplier estimates.
-/

namespace UpperTailOptimizers

open MeasureTheory Set

/-- Perturbation of a ratio: `|N/D - N₀/D₀| ≤ 4δ(|N₀| + |D₀|)/g²` when `|N - N₀|, |D - D₀| ≤ 2δ`,
`|D₀| ≥ g` and `δ ≤ g/4`. -/
theorem ratio_approx {N N₀ D D₀ δ g : ℝ} (hg : 0 < g) (hD₀ : g ≤ |D₀|) (hδ : 0 ≤ δ)
    (hδg : δ ≤ g / 4) (hN : |N - N₀| ≤ 2 * δ) (hD : |D - D₀| ≤ 2 * δ) :
    |N / D - N₀ / D₀| ≤ 4 * δ * (|N₀| + |D₀|) / g ^ 2 := by
  have hD₀pos : 0 < |D₀| := lt_of_lt_of_le hg hD₀
  have hDlow : g / 2 ≤ |D| := by
    have := abs_sub_abs_le_abs_sub D₀ (D₀ - D)
    rw [sub_sub_cancel] at this
    have h2 : |D₀ - D| = |D - D₀| := abs_sub_comm _ _
    linarith
  have hDpos : 0 < |D| := by linarith
  have hDne : D ≠ 0 := abs_pos.mp hDpos
  have hD₀ne : D₀ ≠ 0 := abs_pos.mp hD₀pos
  have e : N / D - N₀ / D₀ = ((N - N₀) * D₀ + N₀ * (D₀ - D)) / (D * D₀) := by
    field_simp; ring
  rw [e, abs_div, abs_mul]
  have hnum : |(N - N₀) * D₀ + N₀ * (D₀ - D)| ≤ 2 * δ * |D₀| + |N₀| * (2 * δ) := by
    calc |(N - N₀) * D₀ + N₀ * (D₀ - D)| ≤ |(N - N₀) * D₀| + |N₀ * (D₀ - D)| := abs_add_le _ _
      _ = |N - N₀| * |D₀| + |N₀| * |D₀ - D| := by rw [abs_mul, abs_mul]
      _ ≤ 2 * δ * |D₀| + |N₀| * (2 * δ) := by
          rw [abs_sub_comm D₀ D]
          exact add_le_add (mul_le_mul_of_nonneg_right hN (abs_nonneg _))
            (mul_le_mul_of_nonneg_left hD (abs_nonneg _))
  have hden : g / 2 * g ≤ |D| * |D₀| := mul_le_mul hDlow hD₀ hg.le (abs_nonneg _)
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : |(N - N₀) * D₀ + N₀ * (D₀ - D)| * g ^ 2 ≤ (2 * δ * |D₀| + |N₀| * (2 * δ)) * g ^ 2 :=
    mul_le_mul_of_nonneg_right hnum (by positivity)
  have h2 : (2 * δ * |D₀| + |N₀| * (2 * δ)) * g ^ 2
      ≤ 4 * δ * (|N₀| + |D₀|) * (|D| * |D₀|) := by
    have : (2 * δ * |D₀| + |N₀| * (2 * δ)) * g ^ 2 = 4 * δ * (|N₀| + |D₀|) * (g / 2 * g) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left hden (by positivity)
  linarith

/-- Integrating a function that is `e`-close to `γ` on `E`: `|∫ 1_E f - γ|E|| ≤ e|E|`. -/
theorem abs_integral_indicator_mul_sub_le {E : Set (ℝ × ℝ)} (hE : MeasurableSet E)
    {f : ℝ × ℝ → ℝ} (hf : Measurable f) {γ e B : ℝ} (hfb : ∀ p, |E.indicator (fun _ => (1:ℝ)) p * f p| ≤ B)
    (hclose : ∀ p ∈ E, |f p - γ| ≤ e) :
    |∫ p, E.indicator (fun _ => (1:ℝ)) p * f p ∂gμ - γ * (gμ E).toReal| ≤ e * (gμ E).toReal := by
  have he : 0 ≤ e ∨ E = ∅ := by
    by_cases hne : E.Nonempty
    · obtain ⟨p, hp⟩ := hne
      exact Or.inl (le_trans (abs_nonneg _) (hclose p hp))
    · exact Or.inr (Set.not_nonempty_iff_eq_empty.mp hne)
  have hind : Measurable fun p : ℝ × ℝ => E.indicator (fun _ => (1:ℝ)) p :=
    measurable_const.indicator hE
  have hint1 : Integrable (fun p => E.indicator (fun _ => (1:ℝ)) p * f p) gμ :=
    integrable_of_abs_le (hind.mul hf) B hfb
  have hint2 : Integrable (fun p : ℝ × ℝ => E.indicator (fun _ => (1:ℝ)) p) gμ :=
    integrable_of_abs_le hind 1 fun p => by
      by_cases hp : p ∈ E
      · rw [Set.indicator_of_mem hp]; simp
      · rw [Set.indicator_of_notMem hp]; simp
  have hE1 : ∫ p : ℝ × ℝ, E.indicator (fun _ => (1:ℝ)) p ∂gμ = (gμ E).toReal :=
    integral_indicator_one hE
  have hsub : ∫ p, E.indicator (fun _ => (1:ℝ)) p * f p ∂gμ - γ * (gμ E).toReal
      = ∫ p, E.indicator (fun _ => (1:ℝ)) p * (f p - γ) ∂gμ := by
    rw [← hE1, ← integral_const_mul, ← integral_sub hint1 (hint2.const_mul γ)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    simp only; ring
  rw [hsub]
  rcases he with he | he
  · have hpt : ∀ p, |E.indicator (fun _ => (1:ℝ)) p * (f p - γ)|
        ≤ e * E.indicator (fun _ => (1:ℝ)) p := by
      intro p
      by_cases hp : p ∈ E
      · rw [Set.indicator_of_mem hp, one_mul, mul_one]; exact hclose p hp
      · rw [Set.indicator_of_notMem hp, zero_mul, abs_zero, mul_zero]
    calc |∫ p, E.indicator (fun _ => (1:ℝ)) p * (f p - γ) ∂gμ|
        ≤ ∫ p, |E.indicator (fun _ => (1:ℝ)) p * (f p - γ)| ∂gμ := abs_integral_le_integral_abs
      _ ≤ ∫ p, e * E.indicator (fun _ => (1:ℝ)) p ∂gμ :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun p => abs_nonneg _)
            (hint2.const_mul e) (Filter.Eventually.of_forall hpt)
      _ = e * (gμ E).toReal := by rw [integral_const_mul, hE1]
  · subst he
    simp

namespace Graphon

variable {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]

set_option maxHeartbeats 2000000 in
/-- **Qualifying directions from two regions, with the multipliers.** -/
theorem exists_qualDirs_of_regions (W : Graphon) {E₁ E₂ : Set (ℝ × ℝ)}
    (hE₁m : MeasurableSet E₁) (hE₂m : MeasurableSet E₂)
    (hE₁s : ∀ x y, (x, y) ∈ E₁ ↔ (y, x) ∈ E₁) (hE₂s : ∀ x y, (x, y) ∈ E₂ ↔ (y, x) ∈ E₂)
    {η c₁ c₂ γ₁ γ₂ τ e L g : ℝ} (hη : 0 < η) (hη1 : η ≤ 1 / 2)
    (hE₁pos : 0 < (gμ E₁).toReal) (hE₂pos : 0 < (gμ E₂).toReal)
    (hW₁ : ∀ p ∈ E₁, |W.toFun p.1 p.2 - c₁| ≤ τ) (hW₂ : ∀ p ∈ E₂, |W.toFun p.1 p.2 - c₂| ≤ τ)
    (hin₁ : ∀ p ∈ E₁, W.toFun p.1 p.2 ∈ Icc η (1 - η)) (hin₂ : ∀ p ∈ E₂, W.toFun p.1 p.2 ∈ Icc η (1 - η))
    (hc₁ : c₁ ∈ Icc η (1 - η)) (hc₂ : c₂ ∈ Icc η (1 - η))
    (hΓ₁ : ∀ p ∈ E₁, |W.gammaW H p.1 p.2 - γ₁| ≤ e) (hΓ₂ : ∀ p ∈ E₂, |W.gammaW H p.1 p.2 - γ₂| ≤ e)
    (hL : ∀ w ∈ Icc η (1 - η), ∀ w' ∈ Icc η (1 - η), |dS0 w - dS0 w'| ≤ L * |w - w'|)
    (hg : 0 < g) (hγ : g ≤ |γ₂ - γ₁|) (he0 : 0 ≤ e) (hL0 : 0 ≤ L)
    (he : e ≤ g / 4) (hLτ : L * τ ≤ g / 4) :
    ∃ Q : QualDirs H W,
      |Q.beta - (dS0 c₂ - dS0 c₁) / (γ₂ - γ₁)|
        ≤ 4 * max e (L * τ) * (|dS0 c₂ - dS0 c₁| + |γ₂ - γ₁|) / g ^ 2 ∧
      |Q.alpha - (dS0 c₁ - (dS0 c₂ - dS0 c₁) / (γ₂ - γ₁) * γ₁)|
        ≤ L * τ + |Q.beta| * e
          + 4 * max e (L * τ) * (|dS0 c₂ - dS0 c₁| + |γ₂ - γ₁|) / g ^ 2 * |γ₁| := by
  classical
  set χ₁ : ℝ → ℝ → ℝ := fun x y => E₁.indicator (fun _ => (1:ℝ)) (x, y) with hχ₁
  set χ₂ : ℝ → ℝ → ℝ := fun x y => E₂.indicator (fun _ => (1:ℝ)) (x, y) with hχ₂
  have hχm : ∀ {E : Set (ℝ × ℝ)}, MeasurableSet E →
      Measurable fun p : ℝ × ℝ => E.indicator (fun _ => (1:ℝ)) (p.1, p.2) := fun hE =>
    measurable_const.indicator hE
  have hχs : ∀ {E : Set (ℝ × ℝ)}, (∀ x y, (x, y) ∈ E ↔ (y, x) ∈ E) →
      ∀ x y, E.indicator (fun _ => (1:ℝ)) (x, y) = E.indicator (fun _ => (1:ℝ)) (y, x) := by
    intro E hs x y
    by_cases h : (x, y) ∈ E
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem ((hs x y).mp h)]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h ((hs x y).mpr h'))]
  have hχb : ∀ (E : Set (ℝ × ℝ)) x y, |E.indicator (fun _ => (1:ℝ)) (x, y)| ≤ 1 := by
    intro E x y
    by_cases h : (x, y) ∈ E
    · rw [Set.indicator_of_mem h]; simp
    · rw [Set.indicator_of_notMem h]; simp
  have hsupp : ∀ x y, χ₁ x y ≠ 0 ∨ χ₂ x y ≠ 0 → W.toFun x y ∈ Icc η (1 - η) := by
    intro x y h
    rcases h with h | h
    · by_contra hc
      apply h; simp only [hχ₁]
      rw [Set.indicator_of_notMem (fun hmem => hc (hin₁ (x, y) hmem))]
    · by_contra hc
      apply h; simp only [hχ₂]
      rw [Set.indicator_of_notMem (fun hmem => hc (hin₂ (x, y) hmem))]
  -- the constraint integrals
  set m₁ : ℝ := (gμ E₁).toReal with hm₁
  set m₂ : ℝ := (gμ E₂).toReal with hm₂
  have hc₁int : ∫ p : ℝ × ℝ, χ₁ p.1 p.2 ∂gμ = m₁ := integral_indicator_one hE₁m
  have hc₂int : ∫ p : ℝ × ℝ, χ₂ p.1 p.2 ∂gμ = m₂ := integral_indicator_one hE₂m
  set g₁ : ℝ := ∫ p : ℝ × ℝ, χ₁ p.1 p.2 * W.gammaW H p.1 p.2 ∂gμ with hg₁
  set g₂ : ℝ := ∫ p : ℝ × ℝ, χ₂ p.1 p.2 * W.gammaW H p.1 p.2 ∂gμ with hg₂
  have hΓb : ∀ (E : Set (ℝ × ℝ)) p, |E.indicator (fun _ => (1:ℝ)) p * W.gammaW H p.1 p.2|
      ≤ H.edgeFinset.card := by
    intro E p
    rw [abs_mul, abs_of_nonneg (W.gammaW_nonneg H _ _)]
    calc |E.indicator (fun _ => (1:ℝ)) p| * W.gammaW H p.1 p.2 ≤ 1 * H.edgeFinset.card :=
          mul_le_mul (hχb E p.1 p.2) (W.gammaW_le H _ _) (W.gammaW_nonneg H _ _) zero_le_one
      _ = H.edgeFinset.card := one_mul _
  have hg₁b : |g₁ - γ₁ * m₁| ≤ e * m₁ :=
    abs_integral_indicator_mul_sub_le hE₁m (W.measurable_gammaW H) (hΓb E₁) hΓ₁
  have hg₂b : |g₂ - γ₂ * m₂| ≤ e * m₂ :=
    abs_integral_indicator_mul_sub_le hE₂m (W.measurable_gammaW H) (hΓb E₂) hΓ₂
  obtain ⟨Lη, hLη⟩ := exists_abs_dS0_le hη
  set s₁ : ℝ := ∫ p : ℝ × ℝ, dS0 (W.toFun p.1 p.2) * χ₁ p.1 p.2 ∂gμ with hs₁
  set s₂ : ℝ := ∫ p : ℝ × ℝ, dS0 (W.toFun p.1 p.2) * χ₂ p.1 p.2 ∂gμ with hs₂
  have hdSb : ∀ (E : Set (ℝ × ℝ)), (∀ p ∈ E, W.toFun p.1 p.2 ∈ Icc η (1 - η)) →
      ∀ p, |E.indicator (fun _ => (1:ℝ)) p * dS0 (W.toFun p.1 p.2)| ≤ max Lη 0 := by
    intro E hin p
    by_cases hp : p ∈ E
    · rw [Set.indicator_of_mem hp, one_mul]; exact le_trans (hLη _ (hin p hp)) (le_max_left _ _)
    · rw [Set.indicator_of_notMem hp, zero_mul, abs_zero]; exact le_max_right _ _
  have hdS_close : ∀ {E : Set (ℝ × ℝ)} {c : ℝ}, (∀ p ∈ E, |W.toFun p.1 p.2 - c| ≤ τ) →
      (∀ p ∈ E, W.toFun p.1 p.2 ∈ Icc η (1 - η)) → c ∈ Icc η (1 - η) →
      ∀ p ∈ E, |dS0 (W.toFun p.1 p.2) - dS0 c| ≤ L * τ := by
    intro E c hWc hin hc p hp
    calc |dS0 (W.toFun p.1 p.2) - dS0 c| ≤ L * |W.toFun p.1 p.2 - c| := hL _ (hin p hp) c hc
      _ ≤ L * τ := mul_le_mul_of_nonneg_left (hWc p hp) hL0
  have hs₁b : |s₁ - dS0 c₁ * m₁| ≤ L * τ * m₁ := by
    have h := abs_integral_indicator_mul_sub_le (f := fun p : ℝ × ℝ => dS0 (W.toFun p.1 p.2)) hE₁m
      (measurable_dS0.comp W.measurable_uncurry) (hdSb E₁ hin₁) (hdS_close hW₁ hin₁ hc₁)
    have e1 : ∫ p, E₁.indicator (fun _ => (1:ℝ)) p * dS0 (W.toFun p.1 p.2) ∂gμ = s₁ :=
      integral_congr_ae (Filter.Eventually.of_forall fun p => mul_comm _ _)
    rwa [e1] at h
  have hs₂b : |s₂ - dS0 c₂ * m₂| ≤ L * τ * m₂ := by
    have h := abs_integral_indicator_mul_sub_le (f := fun p : ℝ × ℝ => dS0 (W.toFun p.1 p.2)) hE₂m
      (measurable_dS0.comp W.measurable_uncurry) (hdSb E₂ hin₂) (hdS_close hW₂ hin₂ hc₂)
    have e1 : ∫ p, E₂.indicator (fun _ => (1:ℝ)) p * dS0 (W.toFun p.1 p.2) ∂gμ = s₂ :=
      integral_congr_ae (Filter.Eventually.of_forall fun p => mul_comm _ _)
    rwa [e1] at h
  -- the normalized averages
  set A₁ : ℝ := g₁ / m₁ with hA₁
  set A₂ : ℝ := g₂ / m₂ with hA₂
  set S₁ : ℝ := s₁ / m₁ with hS₁
  set S₂ : ℝ := s₂ / m₂ with hS₂
  have hA₁b : |A₁ - γ₁| ≤ e := by
    rw [hA₁, show g₁ / m₁ - γ₁ = (g₁ - γ₁ * m₁) / m₁ by field_simp, abs_div,
      abs_of_pos hE₁pos, div_le_iff₀ hE₁pos]; exact hg₁b
  have hA₂b : |A₂ - γ₂| ≤ e := by
    rw [hA₂, show g₂ / m₂ - γ₂ = (g₂ - γ₂ * m₂) / m₂ by field_simp, abs_div,
      abs_of_pos hE₂pos, div_le_iff₀ hE₂pos]; exact hg₂b
  have hS₁b : |S₁ - dS0 c₁| ≤ L * τ := by
    rw [hS₁, show s₁ / m₁ - dS0 c₁ = (s₁ - dS0 c₁ * m₁) / m₁ by field_simp, abs_div,
      abs_of_pos hE₁pos, div_le_iff₀ hE₁pos]; exact hs₁b
  have hS₂b : |S₂ - dS0 c₂| ≤ L * τ := by
    rw [hS₂, show s₂ / m₂ - dS0 c₂ = (s₂ - dS0 c₂ * m₂) / m₂ by field_simp, abs_div,
      abs_of_pos hE₂pos, div_le_iff₀ hE₂pos]; exact hs₂b
  set δ : ℝ := max e (L * τ) with hδ
  have hδ0 : 0 ≤ δ := le_trans he0 (le_max_left _ _)
  have hδg : δ ≤ g / 4 := max_le he hLτ
  have hN : |(S₂ - S₁) - (dS0 c₂ - dS0 c₁)| ≤ 2 * δ := by
    have := abs_sub (S₂ - dS0 c₂) (S₁ - dS0 c₁)
    have e1 : (S₂ - S₁) - (dS0 c₂ - dS0 c₁) = (S₂ - dS0 c₂) - (S₁ - dS0 c₁) := by ring
    rw [e1]
    have h1 : L * τ ≤ δ := le_max_right _ _
    linarith
  have hD : |(A₂ - A₁) - (γ₂ - γ₁)| ≤ 2 * δ := by
    have := abs_sub (A₂ - γ₂) (A₁ - γ₁)
    have e1 : (A₂ - A₁) - (γ₂ - γ₁) = (A₂ - γ₂) - (A₁ - γ₁) := by ring
    rw [e1]
    have h1 : e ≤ δ := le_max_left _ _
    linarith
  have hDne : A₂ - A₁ ≠ 0 := by
    intro h0
    have : |γ₂ - γ₁| ≤ 2 * δ := by
      rw [h0, zero_sub, abs_neg] at hD; exact hD
    linarith
  have hdet : m₁ * g₂ - m₂ * g₁ = m₁ * m₂ * (A₂ - A₁) := by
    rw [hA₁, hA₂]; field_simp
  have hdet_ne : (∫ p : ℝ × ℝ, χ₁ p.1 p.2 ∂gμ) * g₂ - (∫ p : ℝ × ℝ, χ₂ p.1 p.2 ∂gμ) * g₁ ≠ 0 := by
    rw [hc₁int, hc₂int, hdet]
    exact mul_ne_zero (mul_ne_zero hE₁pos.ne' hE₂pos.ne') hDne
  set Q : QualDirs H W := QualDirs.mk η hη hη1 χ₁ χ₂ (hχm hE₁m) (hχm hE₂m) (hχs hE₁s)
    (hχs hE₂s) (hχb E₁) (hχb E₂) hsupp hdet_ne with hQ
  refine ⟨Q, ?_⟩
  -- identify the multipliers
  have hQc₁ : Q.c₁ = m₁ := hc₁int
  have hQc₂ : Q.c₂ = m₂ := hc₂int
  have hQg₁ : Q.g₁ = g₁ := rfl
  have hQg₂ : Q.g₂ = g₂ := rfl
  have hQs₁ : Q.s₁ = s₁ := rfl
  have hQs₂ : Q.s₂ = s₂ := rfl
  have hQdet : Q.det = m₁ * m₂ * (A₂ - A₁) := by
    unfold QualDirs.det; rw [hQc₁, hQc₂, hQg₁, hQg₂, hdet]
  have hbeta : Q.beta = (S₂ - S₁) / (A₂ - A₁) := by
    unfold QualDirs.beta
    rw [hQdet, hQc₁, hQc₂, hQs₁, hQs₂, hS₁, hS₂]
    field_simp
  have hs₁' : s₁ = S₁ * m₁ := by rw [hS₁]; field_simp
  have hs₂' : s₂ = S₂ * m₂ := by rw [hS₂]; field_simp
  have hg₁' : g₁ = A₁ * m₁ := by rw [hA₁]; field_simp
  have hg₂' : g₂ = A₂ * m₂ := by rw [hA₂]; field_simp
  have halpha : Q.alpha = S₁ - Q.beta * A₁ := by
    unfold QualDirs.alpha
    rw [hbeta, hQdet, hQs₁, hQs₂, hQg₁, hQg₂, hs₁', hs₂', hg₁', hg₂']
    field_simp
    ring
  have hβ := ratio_approx hg hγ hδ0 hδg hN hD
  rw [← hbeta] at hβ
  refine ⟨hβ, ?_⟩
  set β₀ : ℝ := (dS0 c₂ - dS0 c₁) / (γ₂ - γ₁) with hβ₀
  rw [halpha]
  have e1 : S₁ - Q.beta * A₁ - (dS0 c₁ - β₀ * γ₁)
      = (S₁ - dS0 c₁) - Q.beta * (A₁ - γ₁) - (Q.beta - β₀) * γ₁ := by ring
  rw [e1]
  calc |(S₁ - dS0 c₁) - Q.beta * (A₁ - γ₁) - (Q.beta - β₀) * γ₁|
      ≤ |S₁ - dS0 c₁| + |Q.beta * (A₁ - γ₁)| + |(Q.beta - β₀) * γ₁| := by
        have h1 := abs_sub ((S₁ - dS0 c₁) - Q.beta * (A₁ - γ₁)) ((Q.beta - β₀) * γ₁)
        have h2 := abs_sub (S₁ - dS0 c₁) (Q.beta * (A₁ - γ₁))
        linarith
    _ = |S₁ - dS0 c₁| + |Q.beta| * |A₁ - γ₁| + |Q.beta - β₀| * |γ₁| := by rw [abs_mul, abs_mul]
    _ ≤ L * τ + |Q.beta| * e
          + 4 * max e (L * τ) * (|dS0 c₂ - dS0 c₁| + |γ₂ - γ₁|) / g ^ 2 * |γ₁| :=
        add_le_add (add_le_add hS₁b (mul_le_mul_of_nonneg_left hA₁b (abs_nonneg _)))
          (mul_le_mul_of_nonneg_right hβ (abs_nonneg _))

end Graphon

end UpperTailOptimizers
