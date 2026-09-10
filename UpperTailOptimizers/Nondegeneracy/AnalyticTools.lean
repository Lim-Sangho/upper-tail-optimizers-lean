import UpperTailOptimizers.Nondegeneracy.BoundaryExcess
import UpperTailOptimizers.LZBoundary.AnalyticEntropy

/-!
# Analytic toolkit for the full `thm:positive-second-variation`

Generic lemmas feeding the proof of `thm:positive-second-variation` (Section 5 of
`paper/bipodal_optimizer.tex`), i.e. the analytic upgrade of the boundary-excess theorem carried out in
`Nondegeneracy/AnalyticExcess.lean`:

* `hasDerivAt_slice` — the `δ`-slice derivative of a two-variable function is the
  partial derivative `fderiv _ F p (0,1)`;
* `analyticAt_deltaDeriv` — the partial `δ`-derivative of an analytic function of
  two variables is analytic (via `AnalyticAt.fderiv`);
* `cubic_taylor_bound` — a quantitative second-order Taylor bound with explicit
  cubic remainder, from a bound on the third derivative (three nested mean-value
  estimates; no Taylor-series API needed);
* `deriv_eq_zero_of_quadratic_bound` — a derivative at `0` vanishes if the function
  is `O(δ²)` on the right;
* `tendsto_cubic`, `limUnder_cubic` — the second Taylor coefficient is recovered as
  the limit of `2 G(δ)/δ²` along `δ ↓ 0` (used to give the coefficient function
  `A_H` a global, chart-independent definition).
-/

namespace UpperTailOptimizers

open MeasureTheory Real Set Filter Topology

-- `analyticAt_shannonH` now lives in `LZBoundary/AnalyticEntropy.lean`, above both this file and
-- `KRRS/Reduced.lean`: importing it from the KRR–S development would otherwise close the
-- cycle `KRRS/Reduced → AnalyticTools → … → LocalReduction → KRRS/Main → … → KRRS/Reduced`.

/-- The `δ`-slice derivative of a two-variable function is the partial derivative
`fderiv ℝ F p (0,1)`. -/
theorem hasDerivAt_slice {F : ℝ × ℝ → ℝ} {r t : ℝ} (hF : DifferentiableAt ℝ F (r, t)) :
    HasDerivAt (fun s => F (r, s)) (fderiv ℝ F (r, t) ((0 : ℝ), (1 : ℝ))) t := by
  have hι : HasDerivAt (fun s : ℝ => ((r, s) : ℝ × ℝ)) (((0 : ℝ), (1 : ℝ)) : ℝ × ℝ) t :=
    (hasDerivAt_const t r).prodMk (hasDerivAt_id t)
  exact hF.hasFDerivAt.comp_hasDerivAt t hι

/-- The partial `δ`-derivative of an analytic function of two variables is analytic. -/
theorem analyticAt_deltaDeriv {F : ℝ × ℝ → ℝ} {p : ℝ × ℝ} (hF : AnalyticAt ℝ F p) :
    AnalyticAt ℝ (fun q => fderiv ℝ F q ((0 : ℝ), (1 : ℝ))) p :=
  ((ContinuousLinearMap.apply ℝ ℝ (((0 : ℝ), (1 : ℝ)) : ℝ × ℝ)).analyticAt
    (fderiv ℝ F p)).comp hF.fderiv

/-- **The partial `δ`-derivative operator** on functions of `(r, δ)`.  Iterating it gives the
higher `δ`-derivatives of a chart function; `dDelta` keeps the statements of the chart lemmas
readable. -/
noncomputable def dDelta (F : ℝ × ℝ → ℝ) : ℝ × ℝ → ℝ :=
  fun p => fderiv ℝ F p ((0 : ℝ), (1 : ℝ))

/-- `dDelta F (r, t)` is the derivative of the `δ`-slice `s ↦ F (r, s)` at `t`. -/
theorem hasDerivAt_dDelta {F : ℝ × ℝ → ℝ} {r t : ℝ} (hF : DifferentiableAt ℝ F (r, t)) :
    HasDerivAt (fun s => F (r, s)) (dDelta F (r, t)) t := hasDerivAt_slice hF

/-- `dDelta` preserves analyticity. -/
theorem analyticAt_dDelta {F : ℝ × ℝ → ℝ} {p : ℝ × ℝ} (hF : AnalyticAt ℝ F p) :
    AnalyticAt ℝ (dDelta F) p := analyticAt_deltaDeriv hF

/-- **Two-sided Lipschitz bound from a derivative bound.**  If `f` has derivative `f'` on
`[-ρ, ρ]` with `|f'| ≤ Mc` there, then `|f δ - f 0| ≤ Mc |δ|` on `[-ρ, ρ]`.  (Used for the
`δ`-Lipschitz control of the chart's second derivative, on both sides of `δ = 0`.) -/
theorem abs_sub_le_of_deriv_bound {f f' : ℝ → ℝ} {ρ Mc : ℝ}
    (hd : ∀ t ∈ Set.Icc (-ρ) ρ, HasDerivAt f (f' t) t)
    (hM : ∀ t ∈ Set.Icc (-ρ) ρ, |f' t| ≤ Mc) :
    ∀ δ ∈ Set.Icc (-ρ) ρ, |f δ - f 0| ≤ Mc * |δ| := by
  intro δ hδ
  have hρ0 : (0:ℝ) ≤ ρ := by linarith [hδ.1, hδ.2]
  have h0mem : (0:ℝ) ∈ Set.Icc (-ρ) ρ := ⟨by linarith, hρ0⟩
  have hsub : Set.uIcc (0:ℝ) δ ⊆ Set.Icc (-ρ) ρ := Set.uIcc_subset_Icc h0mem hδ
  have hD : ∀ s ∈ Set.uIcc (0:ℝ) δ,
      HasDerivWithinAt f (f' s) (Set.uIcc (0:ℝ) δ) s :=
    fun s hs => (hd s (hsub hs)).hasDerivWithinAt
  have hB : ∀ s ∈ Set.uIcc (0:ℝ) δ, ‖f' s‖ ≤ Mc := fun s hs => by
    rw [Real.norm_eq_abs]; exact hM s (hsub hs)
  have := (convex_uIcc (0:ℝ) δ).norm_image_sub_le_of_norm_hasDerivWithin_le hD hB
    Set.left_mem_uIcc Set.right_mem_uIcc
  rwa [Real.norm_eq_abs, Real.norm_eq_abs, sub_zero] at this

/-- **A uniform `O(δ)` bound from analyticity and a vanishing boundary value.**  If `F` is
analytic on the box `|r - r₀| < w`, `|δ| ≤ ρ` and vanishes identically on the slice `δ = 0`,
then on the half-box it satisfies `|F(r,δ)| ≤ L |δ|` for one constant `L`.

This is the generic device behind the a-priori estimates on the Kenyon–Radin–Ren–Sadun
parameters: `c(ε,0) = 0` and `q₂₂(ε,0) = ε` turn into `c = O(δ)` and `q₂₂ - ε = O(δ)`, and
subtracting the boundary values of `q₁₂`, `q₁₁` does the same for those.  The proof is the
`Mc₀` pattern of the chart: `dDelta F` is analytic, hence continuous, hence bounded on the
compact box, and the mean value theorem in `δ` finishes. -/
theorem exists_lipschitz_bound_of_boundary_zero {F : ℝ × ℝ → ℝ} {r₀ w ρ : ℝ}
    (hw : 0 < w) (hρ : 0 < ρ)
    (hF : ∀ r δ : ℝ, |r - r₀| < w → |δ| ≤ ρ → AnalyticAt ℝ F (r, δ))
    (hF0 : ∀ r : ℝ, |r - r₀| < w → F (r, 0) = 0) :
    ∃ L : ℝ, 0 ≤ L ∧
      ∀ r δ : ℝ, |r - r₀| ≤ w / 2 → |δ| ≤ ρ / 2 → |F (r, δ)| ≤ L * |δ| := by
  classical
  obtain ⟨S, hS_def⟩ : ∃ S : Set (ℝ × ℝ),
      S = Set.Icc (r₀ - w / 2) (r₀ + w / 2) ×ˢ Set.Icc (-(ρ / 2)) (ρ / 2) := ⟨_, rfl⟩
  have hScomp : IsCompact S := by rw [hS_def]; exact isCompact_Icc.prod isCompact_Icc
  have hSmem : ∀ r δ : ℝ, |r - r₀| ≤ w / 2 → |δ| ≤ ρ / 2 → ((r, δ) : ℝ × ℝ) ∈ S := by
    intro r δ hr hδ
    rw [hS_def]
    have h1 := abs_le.mp hr
    have h2 := abs_le.mp hδ
    exact ⟨⟨by linarith [h1.1], by linarith [h1.2]⟩, ⟨h2.1, h2.2⟩⟩
  have hSbox : ∀ q ∈ S, |q.1 - r₀| < w ∧ |q.2| ≤ ρ := by
    intro q hq
    rw [hS_def] at hq
    obtain ⟨hq1, hq2⟩ := hq
    refine ⟨abs_lt.mpr ⟨by linarith [hq1.1], by linarith [hq1.2]⟩, ?_⟩
    exact abs_le.mpr ⟨by linarith [hq2.1], by linarith [hq2.2]⟩
  have hFA : ∀ q ∈ S, AnalyticAt ℝ F q := by
    intro q hq
    obtain ⟨h1, h2⟩ := hSbox q hq
    have := hF q.1 q.2 h1 h2
    rwa [Prod.mk.eta] at this
  obtain ⟨L₀, hL₀⟩ := hScomp.exists_bound_of_continuousOn
    (fun q hq => ((analyticAt_dDelta (hFA q hq)).continuousAt).continuousWithinAt)
  obtain ⟨L, hL_def⟩ : ∃ x : ℝ, x = max L₀ 0 := ⟨_, rfl⟩
  have hL0 : 0 ≤ L := by rw [hL_def]; exact le_max_right _ _
  refine ⟨L, hL0, ?_⟩
  intro r δ hr hδ
  have hrw : |r - r₀| < w := lt_of_le_of_lt hr (by linarith)
  have hdiff : ∀ t ∈ Set.Icc (-(ρ / 2)) (ρ / 2),
      HasDerivAt (fun s => F (r, s)) (dDelta F (r, t)) t := by
    intro t ht
    have htρ : |t| ≤ ρ := le_trans (abs_le.mpr ⟨ht.1, ht.2⟩) (by linarith)
    exact hasDerivAt_dDelta (hF r t hrw htρ).differentiableAt
  have hbd : ∀ t ∈ Set.Icc (-(ρ / 2)) (ρ / 2), |dDelta F (r, t)| ≤ L := by
    intro t ht
    have hmem : ((r, t) : ℝ × ℝ) ∈ S := hSmem r t hr (abs_le.mpr ⟨ht.1, ht.2⟩)
    have := hL₀ _ hmem
    rw [Real.norm_eq_abs] at this
    rw [hL_def]
    exact le_trans this (le_max_left _ _)
  have hmain := abs_sub_le_of_deriv_bound (f := fun s => F (r, s))
    (f' := fun s => dDelta F (r, s)) hdiff hbd δ (Set.mem_Icc.mpr (abs_le.mp hδ))
  rwa [hF0 r hrw, sub_zero] at hmain

/-- **Quantitative second-order Taylor bound.**  If `h(0) = h'(0) = 0`, `h''(0) = A`, and
`|h'''| ≤ M` on `[0, ρ]`, then `|h(δ) - A δ²/2| ≤ M δ³` on `[0, ρ]` (three nested
mean-value estimates; the constant `M` instead of `M/6` costs nothing downstream). -/
theorem cubic_taylor_bound {h h1 h2 h3 : ℝ → ℝ} {ρ Mc A : ℝ}
    (hd1 : ∀ t ∈ Set.Icc (0:ℝ) ρ, HasDerivAt h (h1 t) t)
    (hd2 : ∀ t ∈ Set.Icc (0:ℝ) ρ, HasDerivAt h1 (h2 t) t)
    (hd3 : ∀ t ∈ Set.Icc (0:ℝ) ρ, HasDerivAt h2 (h3 t) t)
    (h00 : h 0 = 0) (h10 : h1 0 = 0) (h20 : h2 0 = A)
    (hM : ∀ t ∈ Set.Icc (0:ℝ) ρ, |h3 t| ≤ Mc) :
    ∀ δ ∈ Set.Icc (0:ℝ) ρ, |h δ - A * δ ^ 2 / 2| ≤ Mc * δ ^ 3 := by
  intro δ hδ
  have hδ0 : 0 ≤ δ := hδ.1
  have hδρ : δ ≤ ρ := hδ.2
  have h0ρ : (0:ℝ) ∈ Set.Icc (0:ℝ) ρ := ⟨le_rfl, le_trans hδ0 hδρ⟩
  have hMc0 : 0 ≤ Mc := le_trans (abs_nonneg _) (hM 0 h0ρ)
  -- Step 1: `|h2 t - A| ≤ Mc t` on `[0, δ]`.
  have hstep1 : ∀ t ∈ Set.Icc (0:ℝ) δ, |h2 t - A| ≤ Mc * t := by
    intro t ht
    have hsub : Set.Icc (0:ℝ) t ⊆ Set.Icc (0:ℝ) ρ :=
      Set.Icc_subset_Icc le_rfl (le_trans ht.2 hδρ)
    have hD : ∀ s ∈ Set.Icc (0:ℝ) t, HasDerivWithinAt h2 (h3 s) (Set.Icc (0:ℝ) t) s :=
      fun s hs => (hd3 s (hsub hs)).hasDerivWithinAt
    have hB : ∀ s ∈ Set.Icc (0:ℝ) t, ‖h3 s‖ ≤ Mc := fun s hs => by
      rw [Real.norm_eq_abs]; exact hM s (hsub hs)
    have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hD hB (convex_Icc 0 t)
      (Set.left_mem_Icc.mpr ht.1) (Set.right_mem_Icc.mpr ht.1)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, h20, sub_zero, abs_of_nonneg ht.1] at this
    exact this
  -- Step 2: `|h1 t - A t| ≤ Mc t²` on `[0, δ]`.
  have hstep2 : ∀ t ∈ Set.Icc (0:ℝ) δ, |h1 t - A * t| ≤ Mc * t ^ 2 := by
    intro t ht
    have hsub : Set.Icc (0:ℝ) t ⊆ Set.Icc (0:ℝ) ρ :=
      Set.Icc_subset_Icc le_rfl (le_trans ht.2 hδρ)
    have hD : ∀ s ∈ Set.Icc (0:ℝ) t,
        HasDerivWithinAt (fun s => h1 s - A * s) (h2 s - A) (Set.Icc (0:ℝ) t) s := by
      intro s hs
      have hAs : HasDerivAt (fun s : ℝ => A * s) A s := by
        simpa using (hasDerivAt_id s).const_mul A
      exact ((hd2 s (hsub hs)).sub hAs).hasDerivWithinAt
    have hB : ∀ s ∈ Set.Icc (0:ℝ) t, ‖h2 s - A‖ ≤ Mc * t := fun s hs => by
      rw [Real.norm_eq_abs]
      refine le_trans (hstep1 s ⟨hs.1, le_trans hs.2 ht.2⟩) ?_
      exact mul_le_mul_of_nonneg_left hs.2 hMc0
    have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hD hB (convex_Icc 0 t)
      (Set.left_mem_Icc.mpr ht.1) (Set.right_mem_Icc.mpr ht.1)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, h10, sub_zero, abs_of_nonneg ht.1] at this
    calc |h1 t - A * t| = |h1 t - A * t - (0 - A * 0)| := by norm_num
      _ ≤ Mc * t * t := this
      _ = Mc * t ^ 2 := by ring
  -- Step 3: `|h δ - A δ²/2| ≤ Mc δ³`.
  have hD : ∀ s ∈ Set.Icc (0:ℝ) δ,
      HasDerivWithinAt (fun s => h s - A * s ^ 2 / 2) (h1 s - A * s) (Set.Icc (0:ℝ) δ) s := by
    intro s hs
    have hsub : Set.Icc (0:ℝ) δ ⊆ Set.Icc (0:ℝ) ρ := Set.Icc_subset_Icc le_rfl hδρ
    have hAs : HasDerivAt (fun s : ℝ => A * s ^ 2 / 2) (A * s) s := by
      have := ((hasDerivAt_pow 2 s).const_mul (A / 2))
      -- `d/ds (A/2 · s²) = (A/2) · 2s = A s`
      have heq : (fun s : ℝ => A / 2 * s ^ 2) = fun s : ℝ => A * s ^ 2 / 2 := by
        funext s; ring
      rw [heq] at this
      convert this using 1
      all_goals try rfl
      push_cast
      ring
    exact ((hd1 s (hsub hs)).sub hAs).hasDerivWithinAt
  have hB : ∀ s ∈ Set.Icc (0:ℝ) δ, ‖h1 s - A * s‖ ≤ Mc * δ ^ 2 := fun s hs => by
    rw [Real.norm_eq_abs]
    refine le_trans (hstep2 s hs) ?_
    refine mul_le_mul_of_nonneg_left ?_ hMc0
    exact pow_le_pow_left₀ hs.1 hs.2 2
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hD hB (convex_Icc 0 δ)
    (Set.left_mem_Icc.mpr hδ0) (Set.right_mem_Icc.mpr hδ0)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, h00, sub_zero, abs_of_nonneg hδ0] at this
  calc |h δ - A * δ ^ 2 / 2| = |h δ - A * δ ^ 2 / 2 - (0 - A * 0 ^ 2 / 2)| := by norm_num
    _ ≤ Mc * δ ^ 2 * δ := this
    _ = Mc * δ ^ 3 := by ring

/-- A derivative at `0` vanishes if the function vanishes at `0` and is `O(δ²)` on the
right of `0`. -/
theorem deriv_eq_zero_of_quadratic_bound {h : ℝ → ℝ} {D C ρ : ℝ} (hρ : 0 < ρ)
    (hd : HasDerivAt h D 0) (h0 : h 0 = 0)
    (hb : ∀ δ : ℝ, 0 < δ → δ < ρ → |h δ| ≤ C * δ ^ 2) : D = 0 := by
  have h1 : Tendsto (_root_.slope h 0) (𝓝[≠] (0:ℝ)) (𝓝 D) := hd.tendsto_slope
  have hsub : Set.Ioi (0:ℝ) ⊆ {x | x ≠ (0:ℝ)} := fun x hx => ne_of_gt hx
  have h2 : Tendsto (_root_.slope h 0) (𝓝[>] (0:ℝ)) (𝓝 D) :=
    h1.mono_left (nhdsWithin_mono 0 hsub)
  have h3 : Tendsto (_root_.slope h 0) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have hev : ∀ᶠ δ in 𝓝[>] (0:ℝ), ‖_root_.slope h 0 δ‖ ≤ C * δ := by
      filter_upwards [Ioo_mem_nhdsGT hρ] with δ hδ
      have hδ0 : 0 < δ := hδ.1
      have habs := hb δ hδ0 hδ.2
      rw [Real.norm_eq_abs, _root_.slope_def_field, h0, sub_zero, sub_zero, abs_div,
        abs_of_pos hδ0]
      rw [div_le_iff₀ hδ0]
      calc |h δ| ≤ C * δ ^ 2 := habs
        _ = C * δ * δ := by ring
    have hlim : Tendsto (fun δ : ℝ => C * δ) (𝓝[>] (0:ℝ)) (𝓝 0) := by
      have hc : Continuous (fun δ : ℝ => C * δ) := continuous_const.mul continuous_id
      have h4 := hc.tendsto (0 : ℝ)
      rw [mul_zero] at h4
      exact h4.mono_left nhdsWithin_le_nhds
    exact squeeze_zero_norm' hev hlim
  exact tendsto_nhds_unique h2 h3

/-- **The second Taylor coefficient as a right limit.**  If `|G(δ) - A δ²/2| ≤ M δ³` for
`0 < δ < ρ`, then `2 G(δ)/δ² → A` as `δ ↓ 0`; in particular the `limUnder` along
`𝓝[>] 0` recovers `A`. -/
theorem tendsto_cubic {G : ℝ → ℝ} {A Mc ρ : ℝ} (hρ : 0 < ρ)
    (hb : ∀ δ : ℝ, 0 < δ → δ < ρ → |G δ - A * δ ^ 2 / 2| ≤ Mc * δ ^ 3) :
    Tendsto (fun δ => 2 * G δ / δ ^ 2) (𝓝[>] (0:ℝ)) (𝓝 A) := by
  have hev : ∀ᶠ δ in 𝓝[>] (0:ℝ), ‖2 * G δ / δ ^ 2 - A‖ ≤ 2 * Mc * δ := by
    filter_upwards [Ioo_mem_nhdsGT hρ] with δ hδ
    have hδ0 : 0 < δ := hδ.1
    have hδsq : (0:ℝ) < δ ^ 2 := by positivity
    have heq : 2 * G δ / δ ^ 2 - A = (G δ - A * δ ^ 2 / 2) * (2 / δ ^ 2) := by
      field_simp
    rw [Real.norm_eq_abs, heq, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 / δ ^ 2)]
    calc |G δ - A * δ ^ 2 / 2| * (2 / δ ^ 2) ≤ Mc * δ ^ 3 * (2 / δ ^ 2) := by
          exact mul_le_mul_of_nonneg_right (hb δ hδ0 hδ.2) (by positivity)
      _ = 2 * Mc * δ := by field_simp
  have hlim : Tendsto (fun δ : ℝ => 2 * Mc * δ) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have hc : Continuous (fun δ : ℝ => 2 * Mc * δ) := continuous_const.mul continuous_id
    have h4 := hc.tendsto (0 : ℝ)
    rw [mul_zero] at h4
    exact h4.mono_left nhdsWithin_le_nhds
  have hzero : Tendsto (fun δ => 2 * G δ / δ ^ 2 - A) (𝓝[>] (0:ℝ)) (𝓝 0) :=
    squeeze_zero_norm' hev hlim
  have := hzero.add (tendsto_const_nhds (α := ℝ) (x := A) (f := 𝓝[>] (0:ℝ)))
  simpa using this

/-- The `limUnder` form of `tendsto_cubic`. -/
theorem limUnder_cubic {G : ℝ → ℝ} {A Mc ρ : ℝ} (hρ : 0 < ρ)
    (hb : ∀ δ : ℝ, 0 < δ → δ < ρ → |G δ - A * δ ^ 2 / 2| ≤ Mc * δ ^ 3) :
    limUnder (𝓝[>] (0:ℝ)) (fun δ => 2 * G δ / δ ^ 2) = A :=
  (tendsto_cubic hρ hb).limUnder_eq

end UpperTailOptimizers
