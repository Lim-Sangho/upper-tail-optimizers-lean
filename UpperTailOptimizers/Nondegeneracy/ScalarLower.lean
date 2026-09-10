import UpperTailOptimizers.Nondegeneracy.ArcBounds
import UpperTailOptimizers.Graphon.Basic

/-!
# The scalar quadratic lower bound (`lem:scalar-quadratic-bound` of `paper/bipodal_optimizer.tex`)

**`lem:scalar-quadratic-bound` (scalar quadratic lower bound).**  Let `X` be a `[0,1]`-valued random
variable with `E X = r - δ` and `E X^d ≥ r^d`.  If the quadratic separation
`γ · min(|u-r|, |u-s|)² ≤ J_{p₀}(u) - (J_{p₀}(r) + L(u^d - r^d))` holds on `[0,1]`
(with a positive supporting-line slope `L`), then
`E J_{p₀}(X) ≥ J_{p₀}(r) + C δ²`.

The paper proves this by a compactness/contradiction argument along sequences
`δ_n ↓ 0`.  Here we give a **direct quantitative proof** with the explicit constant
`C = γ / (1 + d/η_d)²`, where `η_d` is a positive lower bound for `r^d - s^d` in the
case `s < r` (in the case `r < s` only the mean constraint is used).  In particular no
smallness assumption `δ < δ₀` is needed.

The argument: let `Y` be the measurable nearest-point projection of `X` onto the
two-point contact set `{r, s}` and `e' = E|X - Y|`.  The separation bound and
Cauchy–Schwarz give `E g_r(X) ≥ γ (e')²`; the mean and moment constraints force
`δ ≤ (1 + d/η_d) e'`, and the supporting-line slope `L > 0` absorbs the moment
surplus `E X^d - r^d ≥ 0`.
-/

namespace UpperTailOptimizers

open MeasureTheory Real Set

/-- **`lem:scalar-quadratic-bound`, quantitative form.**
For a `[0,1]`-valued random variable `f` with mean `r - δ` and `d`-th moment `≥ r^d`,
the quadratic separation of the supporting line at the contact pair `{r, s}` forces
`E J_{p₀}(f) ≥ J_{p₀}(r) + (γ / (1 + d/η_d)²) δ²`. -/
theorem expectation_quadratic_lower
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {f : α → ℝ} (hmeas : Measurable f) (hrange : ∀ ω, f ω ∈ Set.Icc (0:ℝ) 1)
    {d : ℕ} (_hd : 1 ≤ d) {p₀ r s L γ ηd δ : ℝ}
    (hp₀0 : 0 < p₀) (hp₀1 : p₀ < 1)
    (hr0 : 0 < r) (hr1 : r < 1) (hs0 : 0 < s) (hs1 : s < 1)
    (hδ : 0 ≤ δ) (hL : 0 < L) (hγ : 0 < γ) (hηd : 0 < ηd)
    (hquad : ∀ u ∈ Set.Icc (0:ℝ) 1,
      γ * (min |u - r| |u - s|) ^ 2 ≤ Jp p₀ u - (Jp p₀ r + L * (u ^ d - r ^ d)))
    (hcase : r < s ∨ (s < r ∧ ηd ≤ r ^ d - s ^ d))
    (hmean : ∫ ω, f ω ∂μ = r - δ)
    (hmom : r ^ d ≤ ∫ ω, (f ω) ^ d ∂μ) :
    Jp p₀ r + (γ / (1 + d / ηd) ^ 2) * δ ^ 2 ≤ ∫ ω, Jp p₀ (f ω) ∂μ := by
  -- ### Integrability toolkit: bounded measurable functions are integrable
  have hbdd : ∀ (g : α → ℝ) (C : ℝ), Measurable g → (∀ ω, |g ω| ≤ C) → Integrable g μ := by
    intro g C hg hC
    exact Integrable.of_bound hg.aestronglyMeasurable C
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hC ω)
  have habs_f : ∀ ω, |f ω| ≤ 1 := fun ω =>
    abs_le.mpr ⟨by linarith [(hrange ω).1], (hrange ω).2⟩
  have int_f : Integrable f μ := hbdd f 1 hmeas habs_f
  have hmeas_fd : Measurable (fun ω => (f ω) ^ d) := hmeas.pow_const d
  have habs_fd : ∀ ω, |(f ω) ^ d| ≤ 1 := by
    intro ω
    rw [abs_of_nonneg (pow_nonneg (hrange ω).1 d)]
    exact pow_le_one₀ (hrange ω).1 (hrange ω).2
  have int_fd : Integrable (fun ω => (f ω) ^ d) μ := hbdd _ 1 hmeas_fd habs_fd
  -- ### The nearest-point distance `D` and the projection `Y` onto `{r, s}`
  set D : α → ℝ := fun ω => min |f ω - r| |f ω - s| with hD
  have hmeasD : Measurable D :=
    ((hmeas.sub measurable_const).abs).min ((hmeas.sub measurable_const).abs)
  have hD0 : ∀ ω, 0 ≤ D ω := fun ω => le_min (abs_nonneg _) (abs_nonneg _)
  have hD1 : ∀ ω, D ω ≤ 1 := by
    intro ω
    have h1 := (hrange ω).1
    have h2 := (hrange ω).2
    have habs : |f ω - r| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
    exact le_trans (min_le_left _ _) habs
  have habsD : ∀ ω, |D ω| ≤ 1 := fun ω => by
    rw [abs_of_nonneg (hD0 ω)]; exact hD1 ω
  have int_D : Integrable D μ := hbdd D 1 hmeasD habsD
  have int_Dsq : Integrable (fun ω => D ω ^ 2) μ := by
    refine hbdd _ 1 (hmeasD.pow_const 2) fun ω => ?_
    rw [abs_of_nonneg (sq_nonneg _)]
    calc D ω ^ 2 ≤ 1 ^ 2 := pow_le_pow_left₀ (hD0 ω) (hD1 ω) 2
      _ = 1 := one_pow 2
  set B : Set α := {ω | |f ω - s| < |f ω - r|} with hBdef
  have hB : MeasurableSet B :=
    measurableSet_lt ((hmeas.sub measurable_const).abs) ((hmeas.sub measurable_const).abs)
  set c : ℝ := (μ B).toReal with hcdef
  have hc0 : 0 ≤ c := ENNReal.toReal_nonneg
  set Y : α → ℝ := fun ω => r + (s - r) * B.indicator (fun _ => (1:ℝ)) ω with hYdef
  have hYmem : ∀ ω ∈ B, Y ω = s := by
    intro ω hω; simp [hYdef, Set.indicator_of_mem hω]
  have hYnot : ∀ ω ∉ B, Y ω = r := by
    intro ω hω; simp [hYdef, Set.indicator_of_notMem hω]
  have hYmeas : Measurable Y :=
    measurable_const.add ((measurable_one.indicator hB).const_mul (s - r))
  have hYrange : ∀ ω, Y ω ∈ Set.Icc (0:ℝ) 1 := by
    intro ω
    by_cases hω : ω ∈ B
    · rw [hYmem ω hω]; exact ⟨hs0.le, hs1.le⟩
    · rw [hYnot ω hω]; exact ⟨hr0.le, hr1.le⟩
  have habs_Y : ∀ ω, |Y ω| ≤ 1 := fun ω =>
    abs_le.mpr ⟨by linarith [(hYrange ω).1], (hYrange ω).2⟩
  have int_Y : Integrable Y μ := hbdd Y 1 hYmeas habs_Y
  -- `|f - Y| = D` pointwise
  have hfY : ∀ ω, |f ω - Y ω| = D ω := by
    intro ω
    by_cases hω : ω ∈ B
    · rw [hYmem ω hω, hD]
      exact (min_eq_right (le_of_lt hω)).symm
    · rw [hYnot ω hω, hD]
      exact (min_eq_left (not_lt.mp hω)).symm
  -- ### First and `d`-th moments of the projection `Y`
  have int_ind : Integrable (fun ω => B.indicator (fun _ => (1:ℝ)) ω) μ :=
    (integrable_const (1:ℝ)).indicator hB
  have hind_int : ∫ ω, B.indicator (fun _ => (1:ℝ)) ω ∂μ = c := by
    rw [show (fun _ : α => (1:ℝ)) = (1 : α → ℝ) from rfl,
      MeasureTheory.integral_indicator_one hB]
    simp [measureReal_def, hcdef]
  have hYint : ∫ ω, Y ω ∂μ = r + (s - r) * c := by
    rw [hYdef]
    rw [integral_add (integrable_const r) (int_ind.const_mul (s - r)),
      integral_const, integral_const_mul, hind_int]
    simp
  have hYd_pt : ∀ ω, (Y ω) ^ d = r ^ d + (s ^ d - r ^ d) * B.indicator (fun _ => (1:ℝ)) ω := by
    intro ω
    by_cases hω : ω ∈ B
    · rw [hYmem ω hω, Set.indicator_of_mem hω]; ring
    · rw [hYnot ω hω, Set.indicator_of_notMem hω]; ring
  have int_Yd : Integrable (fun ω => (Y ω) ^ d) μ := by
    refine hbdd _ 1 (hYmeas.pow_const d) fun ω => ?_
    rw [abs_of_nonneg (pow_nonneg (hYrange ω).1 d)]
    exact pow_le_one₀ (hYrange ω).1 (hYrange ω).2
  have hYdint : ∫ ω, (Y ω) ^ d ∂μ = r ^ d + (s ^ d - r ^ d) * c := by
    have hfun : (fun ω => (Y ω) ^ d)
        = fun ω => r ^ d + (s ^ d - r ^ d) * B.indicator (fun _ => (1:ℝ)) ω :=
      funext hYd_pt
    rw [hfun, integral_add (integrable_const _) (int_ind.const_mul _),
      integral_const, integral_const_mul, hind_int]
    simp
  -- ### The displacement `e' = E|f - Y| = E D` controls both moment errors
  set e' : ℝ := ∫ ω, D ω ∂μ with he'def
  have he'0 : 0 ≤ e' := integral_nonneg hD0
  have hmean_diff : |(r - δ) - (r + (s - r) * c)| ≤ e' := by
    have h1 : ∫ ω, (f ω - Y ω) ∂μ = (r - δ) - (r + (s - r) * c) := by
      rw [integral_sub int_f int_Y, hmean, hYint]
    have h2 : |∫ ω, (f ω - Y ω) ∂μ| ≤ ∫ ω, |f ω - Y ω| ∂μ := abs_integral_le_integral_abs
    rw [h1] at h2
    refine le_trans h2 (le_of_eq ?_)
    exact integral_congr_ae (ae_of_all _ hfY)
  have hmom_diff : |(∫ ω, (f ω) ^ d ∂μ) - (r ^ d + (s ^ d - r ^ d) * c)| ≤ d * e' := by
    have h1 : ∫ ω, ((f ω) ^ d - (Y ω) ^ d) ∂μ
        = (∫ ω, (f ω) ^ d ∂μ) - (r ^ d + (s ^ d - r ^ d) * c) := by
      rw [integral_sub int_fd int_Yd, hYdint]
    have h2 : |∫ ω, ((f ω) ^ d - (Y ω) ^ d) ∂μ| ≤ ∫ ω, |(f ω) ^ d - (Y ω) ^ d| ∂μ :=
      abs_integral_le_integral_abs
    rw [h1] at h2
    refine le_trans h2 ?_
    have hpt : ∀ ω, |(f ω) ^ d - (Y ω) ^ d| ≤ d * D ω := by
      intro ω
      calc |(f ω) ^ d - (Y ω) ^ d| ≤ d * |f ω - Y ω| :=
            abs_pow_sub_pow_le (hrange ω) (hYrange ω) d
        _ = d * D ω := by rw [hfY ω]
    have int_absdiff : Integrable (fun ω => |(f ω) ^ d - (Y ω) ^ d|) μ :=
      (int_fd.sub int_Yd).abs
    calc ∫ ω, |(f ω) ^ d - (Y ω) ^ d| ∂μ ≤ ∫ ω, (d : ℝ) * D ω ∂μ :=
          integral_mono int_absdiff (int_D.const_mul _) hpt
      _ = d * e' := by rw [integral_const_mul]
  -- ### Cauchy–Schwarz: `(e')² ≤ E D²`
  have hCS : e' ^ 2 ≤ ∫ ω, D ω ^ 2 ∂μ := by
    have hnn : 0 ≤ ∫ ω, (D ω - e') ^ 2 ∂μ := integral_nonneg fun ω => sq_nonneg _
    have h1 : ∫ ω, (D ω - e') ^ 2 ∂μ
        = ∫ ω, (D ω ^ 2 - 2 * e' * D ω + e' ^ 2) ∂μ :=
      integral_congr_ae (ae_of_all _ fun ω => by ring)
    have h2 : ∫ ω, (D ω ^ 2 - 2 * e' * D ω + e' ^ 2) ∂μ
        = (∫ ω, (D ω ^ 2 - 2 * e' * D ω) ∂μ) + ∫ _ω : α, e' ^ 2 ∂μ :=
      integral_add (int_Dsq.sub (int_D.const_mul (2 * e'))) (integrable_const _)
    have h3 : ∫ ω, (D ω ^ 2 - 2 * e' * D ω) ∂μ
        = (∫ ω, D ω ^ 2 ∂μ) - ∫ ω, 2 * e' * D ω ∂μ :=
      integral_sub int_Dsq (int_D.const_mul (2 * e'))
    have h4 : ∫ ω, 2 * e' * D ω ∂μ = 2 * e' * e' := by
      rw [integral_const_mul]
    have h5 : ∫ _ω : α, e' ^ 2 ∂μ = e' ^ 2 := by simp
    rw [h1, h2, h3, h4, h5] at hnn
    nlinarith [hnn]
  -- ### The separation bound integrates to `γ E D² ≤ E J_{p₀}(f) - J_{p₀}(r) - L(E f^d - r^d)`
  have hJpint : Integrable (fun ω => Jp p₀ (f ω)) μ := by
    obtain ⟨CJ, hCJ⟩ := isCompact_Icc.exists_bound_of_continuousOn
      (continuousOn_Jp_Icc hp₀0 hp₀1)
    refine hbdd _ CJ ((measurable_Jp p₀).comp hmeas) fun ω => ?_
    have := hCJ (f ω) (hrange ω)
    rwa [Real.norm_eq_abs] at this
  have int_LB : Integrable (fun ω => L * ((f ω) ^ d - r ^ d)) μ :=
    (int_fd.sub (integrable_const _)).const_mul L
  have hsep_int : γ * ∫ ω, D ω ^ 2 ∂μ
      ≤ (∫ ω, Jp p₀ (f ω) ∂μ) - Jp p₀ r - L * ((∫ ω, (f ω) ^ d ∂μ) - r ^ d) := by
    have hpt : ∀ ω, γ * D ω ^ 2 ≤ Jp p₀ (f ω) - (Jp p₀ r + L * ((f ω) ^ d - r ^ d)) :=
      fun ω => hquad (f ω) (hrange ω)
    have int_rhs : Integrable
        (fun ω => Jp p₀ (f ω) - (Jp p₀ r + L * ((f ω) ^ d - r ^ d))) μ :=
      hJpint.sub ((integrable_const _).add int_LB)
    have hmono := integral_mono (int_Dsq.const_mul γ) int_rhs hpt
    have hLHS : ∫ ω, γ * D ω ^ 2 ∂μ = γ * ∫ ω, D ω ^ 2 ∂μ := integral_const_mul γ _
    have hR1 : ∫ ω, (Jp p₀ (f ω) - (Jp p₀ r + L * ((f ω) ^ d - r ^ d))) ∂μ
        = (∫ ω, Jp p₀ (f ω) ∂μ) - ∫ ω, (Jp p₀ r + L * ((f ω) ^ d - r ^ d)) ∂μ :=
      integral_sub hJpint ((integrable_const _).add int_LB)
    have hR2 : ∫ ω, (Jp p₀ r + L * ((f ω) ^ d - r ^ d)) ∂μ
        = (∫ _ω : α, Jp p₀ r ∂μ) + ∫ ω, L * ((f ω) ^ d - r ^ d) ∂μ :=
      integral_add (integrable_const _) int_LB
    have hR3 : ∫ _ω : α, Jp p₀ r ∂μ = Jp p₀ r := by simp
    have hR4 : ∫ ω, L * ((f ω) ^ d - r ^ d) ∂μ = L * ((∫ ω, (f ω) ^ d ∂μ) - r ^ d) := by
      rw [integral_const_mul, integral_sub int_fd (integrable_const _)]
      simp
    rw [hLHS, hR1, hR2, hR3, hR4] at hmono
    linarith
  -- ### The mean/moment constraints force `δ ≤ (1 + d/ηd) e'`
  have hδe : δ ≤ (1 + d / ηd) * e' := by
    obtain ⟨hml, hmr⟩ := abs_le.mp hmean_diff
    have hdnn : (0:ℝ) ≤ (d : ℝ) / ηd := by positivity
    rcases hcase with hrs | ⟨hsr, hηdle⟩
    · -- case `r < s`: the projected mean is `≥ r`, so `δ ≤ e'`
      have ht0 : 0 ≤ (s - r) * c := mul_nonneg (by linarith) hc0
      -- from `hml`: `-e' ≤ (r - δ) - (r + (s-r)c)`, i.e. `δ + (s-r)c ≤ e'`
      have hδe' : δ ≤ e' := by linarith
      calc δ ≤ e' := hδe'
        _ = 1 * e' := (one_mul e').symm
        _ ≤ (1 + d / ηd) * e' := by
            exact mul_le_mul_of_nonneg_right (by linarith) he'0
    · -- case `s < r`: the moment constraint caps the mass `c` at the far contact
      obtain ⟨hdl, hdr⟩ := abs_le.mp hmom_diff
      -- `-(s-r)c ≥ δ - e'` from the mean; `-(s^d-r^d)c ≤ d e'` from the moment
      have h1 : δ - e' ≤ -((s - r) * c) := by linarith
      have h2 : -((s ^ d - r ^ d) * c) ≤ d * e' := by linarith [hmom]
      -- hence `ηd c ≤ d e'`
      have h3 : c * ηd ≤ d * e' := by
        have hstep : c * ηd ≤ c * (r ^ d - s ^ d) := mul_le_mul_of_nonneg_left hηdle hc0
        have heq : c * (r ^ d - s ^ d) = -((s ^ d - r ^ d) * c) := by ring
        linarith [hstep, heq ▸ hstep]
      -- and `-(s-r)c = c(r-s) ≤ c` since `r - s ≤ 1`
      have h4 : -((s - r) * c) ≤ c := by
        have hrs1 : r - s ≤ 1 := by linarith
        have := mul_le_mul_of_nonneg_left hrs1 hc0
        -- `c * (r - s) ≤ c * 1`
        have heq : c * (r - s) = -((s - r) * c) := by ring
        linarith [heq ▸ this]
      have h5 : c ≤ d * e' / ηd := by
        rw [le_div_iff₀ hηd]
        linarith [h3]
      have hfinal : (1 + d / ηd) * e' = e' + d * e' / ηd := by
        field_simp
      linarith [h1, h4, h5, hfinal ▸ le_refl ((1 + d / ηd) * e')]
  -- ### Conclusion
  have hBfac : (0:ℝ) < 1 + d / ηd := by
    have : (0:ℝ) ≤ (d : ℝ) / ηd := by positivity
    linarith
  have hδsq : δ ^ 2 ≤ (1 + d / ηd) ^ 2 * e' ^ 2 := by
    calc δ ^ 2 ≤ ((1 + d / ηd) * e') ^ 2 := pow_le_pow_left₀ hδ hδe 2
      _ = (1 + d / ηd) ^ 2 * e' ^ 2 := by ring
  have hmomL : 0 ≤ L * ((∫ ω, (f ω) ^ d ∂μ) - r ^ d) := by
    have : 0 ≤ (∫ ω, (f ω) ^ d ∂μ) - r ^ d := by linarith
    positivity
  have hCfac : (γ / (1 + d / ηd) ^ 2) * ((1 + d / ηd) ^ 2 * e' ^ 2) = γ * e' ^ 2 := by
    field_simp
  have hchain : (γ / (1 + d / ηd) ^ 2) * δ ^ 2 ≤ γ * ∫ ω, D ω ^ 2 ∂μ := by
    have h1 : (γ / (1 + d / ηd) ^ 2) * δ ^ 2
        ≤ (γ / (1 + d / ηd) ^ 2) * ((1 + d / ηd) ^ 2 * e' ^ 2) :=
      mul_le_mul_of_nonneg_left hδsq (by positivity)
    have h3 : γ * e' ^ 2 ≤ γ * ∫ ω, D ω ^ 2 ∂μ := mul_le_mul_of_nonneg_left hCS hγ.le
    linarith [hCfac ▸ h1]
  linarith [hsep_int, hchain, hmomL]

end UpperTailOptimizers
