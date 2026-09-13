import UpperTailOptimizers.Nondegeneracy.BoundaryExcess
import UpperTailOptimizers.LZBoundary.AnalyticEntropy
import UpperTailOptimizers.Nondegeneracy.SliceDeriv

/-!
# Analytic toolkit for the full `thm:positive-second-variation`

Generic lemmas feeding the proof of `thm:positive-second-variation` (Section 5 of
`paper/bipodal_optimizer.tex`), i.e. the analytic upgrade of the boundary-excess theorem carried out in
`Nondegeneracy/AnalyticExcess.lean`:

* the `δ`-slice derivative `dDelta`, its analyticity and the uniform `O(δ)` bound
  `exists_lipschitz_bound_of_boundary_zero` live in `Nondegeneracy/SliceDeriv.lean`;
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
