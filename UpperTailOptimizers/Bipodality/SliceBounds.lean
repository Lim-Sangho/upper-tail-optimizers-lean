import UpperTailOptimizers.KRRS.Stationarity
import UpperTailOptimizers.Nondegeneracy.SliceDeriv

/-!
# Uniform bounds from vanishing on the slice `c = 0`

For functions `Φ(ε,a,b,c)` analytic near a compact set of `(ε,a,b)` times an interval in `c`:

* `exists_bound_slice_zero` — `Φ(·,0) = 0` gives `|Φ| ≤ L|c|`;
* `exists_sq_bound_slice_zero` — if moreover `∂_cΦ(·,0) = 0`, then `|Φ| ≤ L c²`.

These give the uniform `O(ϑ)` and `O(ϑ²)` estimates along the analytic bipodal family without
differentiating the family itself.
-/

namespace UpperTailOptimizers

open Real Set Filter Topology

private theorem isCompact_box {K : Set (ℝ × ℝ × ℝ)} (hK : IsCompact K) (ρ : ℝ) :
    IsCompact ((fun q : (ℝ × ℝ × ℝ) × ℝ => ((q.1.1, q.1.2.1, q.1.2.2, q.2) : ℝ × ℝ × ℝ × ℝ)) ''
      (K ×ˢ Icc (-ρ) ρ)) :=
  (hK.prod isCompact_Icc).image (by fun_prop)

theorem exists_bound_slice_zero {Φ : ℝ × ℝ × ℝ × ℝ → ℝ} {K : Set (ℝ × ℝ × ℝ)} (hK : IsCompact K)
    {ρ : ℝ} (hΦ : ∀ x ∈ K, ∀ c ∈ Icc (-ρ) ρ, AnalyticAt ℝ Φ (x.1, x.2.1, x.2.2, c))
    (h0 : ∀ x ∈ K, Φ (x.1, x.2.1, x.2.2, 0) = 0) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x ∈ K, ∀ c ∈ Icc (-ρ) ρ, |Φ (x.1, x.2.1, x.2.2, c)| ≤ L * |c| := by
  set S := (fun q : (ℝ × ℝ × ℝ) × ℝ => ((q.1.1, q.1.2.1, q.1.2.2, q.2) : ℝ × ℝ × ℝ × ℝ)) ''
      (K ×ˢ Icc (-ρ) ρ) with hS
  have hSc : IsCompact S := isCompact_box hK ρ
  have hcont : ContinuousOn (partialC Φ) S := by
    rintro _ ⟨⟨x, c⟩, ⟨hx, hc⟩, rfl⟩
    exact (analyticAt_partialSlot _ (hΦ x hx c hc)).continuousAt.continuousWithinAt
  obtain ⟨L₀, hL₀⟩ := hSc.exists_bound_of_continuousOn hcont
  refine ⟨max L₀ 0, le_max_right _ _, fun x hx c hc => ?_⟩
  have hd : ∀ t ∈ Icc (-ρ) ρ, HasDerivAt (fun s => Φ (x.1, x.2.1, x.2.2, s))
      (partialC Φ (x.1, x.2.1, x.2.2, t)) t := by
    intro t ht
    exact hasDerivAt_partialSlot (hΦ x hx t ht) ((hasDerivAt_const t x.1).prodMk
      ((hasDerivAt_const t x.2.1).prodMk ((hasDerivAt_const t x.2.2).prodMk
        (hasDerivAt_id t)))) rfl
  have hM : ∀ t ∈ Icc (-ρ) ρ, |partialC Φ (x.1, x.2.1, x.2.2, t)| ≤ max L₀ 0 := by
    intro t ht
    have := hL₀ _ ⟨(x, t), ⟨hx, ht⟩, rfl⟩
    rw [Real.norm_eq_abs] at this
    exact le_trans this (le_max_left _ _)
  have h := abs_sub_le_of_deriv_bound (f := fun s => Φ (x.1, x.2.1, x.2.2, s)) hd hM c hc
  simpa [h0 x hx] using h

theorem exists_sq_bound_slice_zero {Φ : ℝ × ℝ × ℝ × ℝ → ℝ} {K : Set (ℝ × ℝ × ℝ)}
    (hK : IsCompact K) {ρ : ℝ}
    (hΦ : ∀ x ∈ K, ∀ c ∈ Icc (-ρ) ρ, AnalyticAt ℝ Φ (x.1, x.2.1, x.2.2, c))
    (h0 : ∀ x ∈ K, Φ (x.1, x.2.1, x.2.2, 0) = 0)
    (h1 : ∀ x ∈ K, partialC Φ (x.1, x.2.1, x.2.2, 0) = 0) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x ∈ K, ∀ c ∈ Icc (-ρ) ρ, |Φ (x.1, x.2.1, x.2.2, c)| ≤ L * c ^ 2 := by
  obtain ⟨L, hL0, hL⟩ := exists_bound_slice_zero (Φ := partialC Φ) hK
    (fun x hx c hc => analyticAt_partialSlot _ (hΦ x hx c hc)) h1
  refine ⟨L, hL0, fun x hx c hc => ?_⟩
  have hcabs : |c| ≤ ρ := abs_le.mpr ⟨hc.1, hc.2⟩
  have hsub : ∀ t ∈ Icc (-|c|) |c|, t ∈ Icc (-ρ) ρ := fun t ht =>
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hd : ∀ t ∈ Icc (-|c|) |c|, HasDerivAt (fun s => Φ (x.1, x.2.1, x.2.2, s))
      (partialC Φ (x.1, x.2.1, x.2.2, t)) t := by
    intro t ht
    exact hasDerivAt_partialSlot (hΦ x hx t (hsub t ht)) ((hasDerivAt_const t x.1).prodMk
      ((hasDerivAt_const t x.2.1).prodMk ((hasDerivAt_const t x.2.2).prodMk
        (hasDerivAt_id t)))) rfl
  have hM : ∀ t ∈ Icc (-|c|) |c|, |partialC Φ (x.1, x.2.1, x.2.2, t)| ≤ L * |c| := by
    intro t ht
    refine le_trans (hL x hx t (hsub t ht)) (mul_le_mul_of_nonneg_left ?_ hL0)
    exact abs_le.mpr ⟨ht.1, ht.2⟩
  have h := abs_sub_le_of_deriv_bound (f := fun s => Φ (x.1, x.2.1, x.2.2, s)) hd hM c
    ⟨neg_abs_le c, le_abs_self c⟩
  simp only [h0 x hx, sub_zero] at h
  calc |Φ (x.1, x.2.1, x.2.2, c)| ≤ L * |c| * |c| := h
    _ = L * c ^ 2 := by rw [mul_assoc, ← sq, sq_abs]

/-- **Uniform Lipschitz bound in the second variable** for a function analytic on a closed box. -/
theorem exists_lipschitz_snd {Ψ : ℝ × ℝ → ℝ} {x₀ y₀ w ρ : ℝ}
    (hΨ : ∀ x y, |x - x₀| ≤ w → |y - y₀| ≤ ρ → AnalyticAt ℝ Ψ (x, y)) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x y y', |x - x₀| ≤ w → |y - y₀| ≤ ρ → |y' - y₀| ≤ ρ →
      |Ψ (x, y) - Ψ (x, y')| ≤ L * |y - y'| := by
  set S : Set (ℝ × ℝ) := Icc (x₀ - w) (x₀ + w) ×ˢ Icc (y₀ - ρ) (y₀ + ρ) with hS
  have hSc : IsCompact S := isCompact_Icc.prod isCompact_Icc
  have hmemS : ∀ x y, |x - x₀| ≤ w → |y - y₀| ≤ ρ → ((x, y) : ℝ × ℝ) ∈ S := fun x y hx hy =>
    ⟨⟨by linarith [(abs_le.mp hx).1], by linarith [(abs_le.mp hx).2]⟩,
      ⟨by linarith [(abs_le.mp hy).1], by linarith [(abs_le.mp hy).2]⟩⟩
  have hS' : ∀ q ∈ S, |q.1 - x₀| ≤ w ∧ |q.2 - y₀| ≤ ρ := fun q hq =>
    ⟨abs_le.mpr ⟨by linarith [hq.1.1], by linarith [hq.1.2]⟩,
      abs_le.mpr ⟨by linarith [hq.2.1], by linarith [hq.2.2]⟩⟩
  have hcont : ContinuousOn (dDelta Ψ) S := fun q hq => by
    obtain ⟨h1, h2⟩ := hS' q hq
    exact (analyticAt_dDelta (hΨ q.1 q.2 h1 h2)).continuousAt.continuousWithinAt
  obtain ⟨L₀, hL₀⟩ := hSc.exists_bound_of_continuousOn hcont
  refine ⟨max L₀ 0, le_max_right _ _, fun x y y' hx hy hy' => ?_⟩
  have hsub : uIcc y y' ⊆ Icc (y₀ - ρ) (y₀ + ρ) := by
    apply uIcc_subset_Icc
    · exact ⟨by linarith [(abs_le.mp hy).1], by linarith [(abs_le.mp hy).2]⟩
    · exact ⟨by linarith [(abs_le.mp hy').1], by linarith [(abs_le.mp hy').2]⟩
  have hD : ∀ t ∈ uIcc y y', HasDerivWithinAt (fun s => Ψ (x, s)) (dDelta Ψ (x, t))
      (uIcc y y') t := by
    intro t ht
    have htb := hsub ht
    have ht' : |t - y₀| ≤ ρ := abs_le.mpr ⟨by linarith [htb.1], by linarith [htb.2]⟩
    exact (hasDerivAt_dDelta (hΨ x t hx ht').differentiableAt).hasDerivWithinAt
  have hB : ∀ t ∈ uIcc y y', ‖dDelta Ψ (x, t)‖ ≤ max L₀ 0 := by
    intro t ht
    have htb := hsub ht
    have ht' : |t - y₀| ≤ ρ := abs_le.mpr ⟨by linarith [htb.1], by linarith [htb.2]⟩
    exact le_trans (hL₀ _ (hmemS x t hx ht')) (le_max_left _ _)
  have h := (convex_uIcc y y').norm_image_sub_le_of_norm_hasDerivWithin_le hD hB
    right_mem_uIcc left_mem_uIcc
  rwa [Real.norm_eq_abs, Real.norm_eq_abs] at h

end UpperTailOptimizers
