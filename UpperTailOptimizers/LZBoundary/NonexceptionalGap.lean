import UpperTailOptimizers.LZBoundary.DensityGap

/-!
# (M3) of Theorem 3.1: the quadratic expansion of the supporting cost gap

This file completes condition (M3) of `thm:lz-boundary` in `paper/paper.tex`.  Fix a compact
`K ⊆ (0,1) ∖ {r_*}`.  Uniformly for `r ∈ K` and for either contact density `u ∈ {r, s_c(r)}`:

* the curvature `g_{d,r}''(u) = h_{p_c(r),d}(u)/u` of `DensityGap.lean` is bounded **above and
  below** by positive constants depending only on `d` and `K`
  (`exists_nonexceptional_gap_curvature_bounds`);
* the gap has the quadratic expansion `eq:contact-gap-expansion`
  `g_{d,r}(z) = ½g_{d,r}''(u)(z-u)² + O_{d,K}(|z-u|³)` on a window of a common radius
  (`exists_nonexceptional_gap_expansion`);
* the global quadratic separation `eq:contact-quadratic-separation`
  `g_{d,r}(z) ≥ γ_{d,K} dist(z,{r,s_c(r)})²` holds on all of `[0,1]`
  (`exists_nonexceptional_gap_quadratic_lower`).

The last item is the form in which `sec:nonexceptional-quadratic-growth` uses the gap.  The
paper derives it from the expansion by a compactness argument on the ratio
`g_{d,r}(z)/dist(z,{r,s_c(r)})²`; here it is obtained from the `x`-coordinate separation
`lz_boundary_quadSep` of `PaperForm.lean` and the elementary comparison
`|z^d - u^d| ≥ η^{d-1}|z - u|`, which keeps the constant explicit in terms of the
`x`-coordinate one.

The cubic Taylor step is `cubic_taylor_gap`, the one-sided mean-value chain that
`NonexceptionalEndpoint/QuadraticGrowth/AnalyticTools.lean` also runs (there for the boundary
excess in the density deficit); it is repeated here to keep `LZBoundary` independent of
Section 4.

`lz_boundary_nonexceptional_gap` states (M3) in one theorem.  It is the deliberate twin of
`lz_boundary_exceptional_gap` of `SingularEndpoint/ExceptionalGap.lean`, which states (M4) with
the same conjuncts in the same order; the two are the entry points for comparing the quadratic
regime of `sec:nonexceptional-endpoint` with the quartic regime of `sec:singular-endpoint`.
-/

namespace UpperTailOptimizers

open Real Set Filter Topology

variable {d : ℕ}

/-! ### The third derivative of the gap -/

/-- `J_p''(z) = 1/(z(1-z))` has derivative `(2z-1)/(z²(1-z)²)`.  Kept private: Section 5
restates the same fact as `hasDerivAt_Jp''` with the named third derivative `Jp3`
(`SingularEndpoint/RankOneStationaryFamily/Defs.lean`), which is not available upstream here. -/
private theorem hasDerivAt_Jp''_explicit {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    HasDerivAt Jp'' ((2 * z - 1) / (z ^ 2 * (1 - z) ^ 2)) z := by
  have hzne : z ≠ 0 := ne_of_gt hz0
  have h1zne : (1 : ℝ) - z ≠ 0 := ne_of_gt (by linarith)
  have hden : z * (1 - z) ≠ 0 := mul_ne_zero hzne h1zne
  have hinner : HasDerivAt (fun y : ℝ => y * (1 - y)) (1 - 2 * z) z := by
    have h : HasDerivAt (fun y : ℝ => y * (1 - y)) (1 * (1 - z) + z * (0 - 1)) z :=
      (hasDerivAt_id z).mul ((hasDerivAt_const z (1 : ℝ)).sub (hasDerivAt_id z))
    convert h using 1
    ring
  have hfun : Jp'' = fun y : ℝ => (y * (1 - y))⁻¹ := by
    funext y; simp [Jp'', one_div]
  have h := hinner.inv hden
  have hval : -(1 - 2 * z) / (z * (1 - z)) ^ 2 = (2 * z - 1) / (z ^ 2 * (1 - z) ^ 2) := by
    rw [mul_pow]; ring
  rw [hfun, ← hval]
  exact h

/-- The third `z`-derivative of the gap, as an explicit function. -/
noncomputable def gapD3 (d : ℕ) (r z : ℝ) : ℝ :=
  (2 * z - 1) / (z ^ 2 * (1 - z) ^ 2)
    - slope d (pcGlobal d) r * ((d : ℝ) * ((d : ℝ) - 1) * (((d : ℝ) - 2) * z ^ (d - 3)))

/-- `gapD2` is differentiable in `z` on `(0,1)`, with derivative `gapD3`. -/
theorem hasDerivAt_gapD2 (hd : 2 ≤ d) {r : ℝ} {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    HasDerivAt (gapD2 d r) (gapD3 d r z) z := by
  have hJ := hasDerivAt_Jp''_explicit hz0 hz1
  have hcast : ((d - 2 : ℕ) : ℝ) = (d : ℝ) - 2 := by
    have h2 : (2 : ℕ) ≤ d := hd
    push_cast [Nat.cast_sub h2]
    ring
  have hpow : HasDerivAt (fun y : ℝ => y ^ (d - 2)) (((d : ℝ) - 2) * z ^ (d - 3)) z := by
    have h := hasDerivAt_pow (d - 2) z
    rw [hcast] at h
    have hdd : d - 2 - 1 = d - 3 := by omega
    rwa [hdd] at h
  have hlin : HasDerivAt
      (fun y : ℝ => slope d (pcGlobal d) r * ((d : ℝ) * ((d : ℝ) - 1) * y ^ (d - 2)))
      (slope d (pcGlobal d) r * ((d : ℝ) * ((d : ℝ) - 1) * (((d : ℝ) - 2) * z ^ (d - 3)))) z := by
    have := (hpow.const_mul ((d : ℝ) * ((d : ℝ) - 1))).const_mul (slope d (pcGlobal d) r)
    simpa [mul_assoc] using this
  exact hJ.sub hlin

/-! ### A uniform cubic Taylor step -/

/-- **One-sided cubic Taylor bound.**  If `f` vanishes to first order at `0` with
`f''(0) = A` and `|f'''| ≤ M` on `[0,ρ]`, then `|f(t) - A t²/2| ≤ M t³` there. -/
theorem cubic_taylor_gap {f f1 f2 f3 : ℝ → ℝ} {ρ M A : ℝ}
    (hd1 : ∀ t ∈ Set.Icc (0 : ℝ) ρ, HasDerivAt f (f1 t) t)
    (hd2 : ∀ t ∈ Set.Icc (0 : ℝ) ρ, HasDerivAt f1 (f2 t) t)
    (hd3 : ∀ t ∈ Set.Icc (0 : ℝ) ρ, HasDerivAt f2 (f3 t) t)
    (h00 : f 0 = 0) (h10 : f1 0 = 0) (h20 : f2 0 = A)
    (hM : ∀ t ∈ Set.Icc (0 : ℝ) ρ, |f3 t| ≤ M) :
    ∀ t ∈ Set.Icc (0 : ℝ) ρ, |f t - A * t ^ 2 / 2| ≤ M * t ^ 3 := by
  intro t ht
  have ht0 : 0 ≤ t := ht.1
  have htρ : t ≤ ρ := ht.2
  have h0ρ : (0 : ℝ) ∈ Set.Icc (0 : ℝ) ρ := ⟨le_rfl, le_trans ht0 htρ⟩
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0 h0ρ)
  -- `|f2 s - A| ≤ M s`
  have hstep1 : ∀ s ∈ Set.Icc (0 : ℝ) t, |f2 s - A| ≤ M * s := by
    intro s hs
    have hsub : Set.Icc (0 : ℝ) s ⊆ Set.Icc (0 : ℝ) ρ :=
      Set.Icc_subset_Icc le_rfl (le_trans hs.2 htρ)
    have hD : ∀ x ∈ Set.Icc (0 : ℝ) s, HasDerivWithinAt f2 (f3 x) (Set.Icc (0 : ℝ) s) x :=
      fun x hx => (hd3 x (hsub hx)).hasDerivWithinAt
    have hB : ∀ x ∈ Set.Icc (0 : ℝ) s, ‖f3 x‖ ≤ M := fun x hx => by
      rw [Real.norm_eq_abs]; exact hM x (hsub hx)
    have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hD hB (convex_Icc 0 s)
      (Set.left_mem_Icc.mpr hs.1) (Set.right_mem_Icc.mpr hs.1)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, h20, sub_zero, abs_of_nonneg hs.1] at h
    exact h
  -- `|f1 s - A s| ≤ M s²`
  have hstep2 : ∀ s ∈ Set.Icc (0 : ℝ) t, |f1 s - A * s| ≤ M * s ^ 2 := by
    intro s hs
    have hsub : Set.Icc (0 : ℝ) s ⊆ Set.Icc (0 : ℝ) ρ :=
      Set.Icc_subset_Icc le_rfl (le_trans hs.2 htρ)
    have hsubt : Set.Icc (0 : ℝ) s ⊆ Set.Icc (0 : ℝ) t := Set.Icc_subset_Icc le_rfl hs.2
    have hD : ∀ x ∈ Set.Icc (0 : ℝ) s,
        HasDerivWithinAt (fun y => f1 y - A * y) (f2 x - A) (Set.Icc (0 : ℝ) s) x := by
      intro x hx
      have h1 := hd2 x (hsub hx)
      have h2 : HasDerivAt (fun y : ℝ => A * y) A x := by
        simpa using (hasDerivAt_id x).const_mul A
      exact (h1.sub h2).hasDerivWithinAt
    have hB : ∀ x ∈ Set.Icc (0 : ℝ) s, ‖f2 x - A‖ ≤ M * s := by
      intro x hx
      rw [Real.norm_eq_abs]
      refine le_trans (hstep1 x (hsubt hx)) ?_
      have hxs := hx.2
      nlinarith [hM0, hx.1]
    have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hD hB (convex_Icc 0 s)
      (Set.left_mem_Icc.mpr hs.1) (Set.right_mem_Icc.mpr hs.1)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, h10] at h
    have e1 : f1 s - A * s - (0 - A * 0) = f1 s - A * s := by ring
    have e2 : |s - 0| = s := by rw [sub_zero, abs_of_nonneg hs.1]
    rw [e1, e2] at h
    calc |f1 s - A * s| ≤ M * s * s := h
      _ = M * s ^ 2 := by ring
  -- conclude
  have hD : ∀ x ∈ Set.Icc (0 : ℝ) t,
      HasDerivWithinAt (fun y => f y - A * y ^ 2 / 2) (f1 x - A * x) (Set.Icc (0 : ℝ) t) x := by
    intro x hx
    have hsub : Set.Icc (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) ρ := Set.Icc_subset_Icc le_rfl htρ
    have h1 := hd1 x (hsub hx)
    have h2 : HasDerivAt (fun y : ℝ => A * y ^ 2 / 2) (A * x) x := by
      have hp : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
        simpa using hasDerivAt_pow 2 x
      have h := (hp.const_mul A).div_const 2
      have hval : A * (2 * x) / 2 = A * x := by ring
      rw [← hval]
      exact h
    exact (h1.sub h2).hasDerivWithinAt
  have hB : ∀ x ∈ Set.Icc (0 : ℝ) t, ‖f1 x - A * x‖ ≤ M * t ^ 2 := by
    intro x hx
    rw [Real.norm_eq_abs]
    refine le_trans (hstep2 x hx) ?_
    have hxt : x ^ 2 ≤ t ^ 2 := by nlinarith [hx.1, hx.2]
    nlinarith [hM0]
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hD hB (convex_Icc 0 t)
    (Set.left_mem_Icc.mpr ht0) (Set.right_mem_Icc.mpr ht0)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, h00] at h
  have e1 : f t - A * t ^ 2 / 2 - (0 - A * 0 ^ 2 / 2) = f t - A * t ^ 2 / 2 := by ring
  have e2 : |t - 0| = t := by rw [sub_zero, abs_of_nonneg ht0]
  rw [e1, e2] at h
  calc |f t - A * t ^ 2 / 2| ≤ M * t ^ 2 * t := h
    _ = M * t ^ 3 := by ring

/-! ### Elementary inputs -/

/-- **Reverse Lipschitz bound for powers**: `v^{k-1}|z - v| ≤ |z^k - v^k|` for `z, v ≥ 0`.
The same elementary inequality as `pow_sub_pow_ge` of
`NonexceptionalEndpoint/QuadraticGrowth/PowBounds.lean`, repeated here to keep `LZBoundary`
independent of Section 4. -/
theorem pow_sub_pow_ge_lz {z v : ℝ} (hz : 0 ≤ z) (hv : 0 ≤ v) {k : ℕ} (hk : 1 ≤ k) :
    v ^ (k - 1) * |z - v| ≤ |z ^ k - v ^ k| := by
  have hfac : z ^ k - v ^ k = (z - v) * ∑ i ∈ Finset.range k, z ^ i * v ^ (k - 1 - i) := by
    rw [mul_comm]
    exact ((Commute.all z v).geom_sum₂_mul k).symm
  have hnn : 0 ≤ ∑ i ∈ Finset.range k, z ^ i * v ^ (k - 1 - i) :=
    Finset.sum_nonneg fun i _ => mul_nonneg (pow_nonneg hz i) (pow_nonneg hv _)
  rw [hfac, abs_mul, mul_comm (v ^ (k - 1)) |z - v|]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  rw [abs_of_nonneg hnn]
  have h0 : (0 : ℕ) ∈ Finset.range k := Finset.mem_range.mpr hk
  calc v ^ (k - 1) = z ^ 0 * v ^ (k - 1 - 0) := by rw [pow_zero, one_mul, Nat.sub_zero]
    _ ≤ ∑ i ∈ Finset.range k, z ^ i * v ^ (k - 1 - i) :=
        Finset.single_le_sum (f := fun i => z ^ i * v ^ (k - 1 - i))
          (fun i _ => mul_nonneg (pow_nonneg hz i) (pow_nonneg hv _)) h0

/-- The tangent-line slope `r ↦ ℓ_r'` is continuous on `(0,1)`. -/
theorem continuousOn_slope_pcGlobal (hd : 2 ≤ d) :
    ContinuousOn (fun r => slope d (pcGlobal d) r) (Set.Ioo (0 : ℝ) 1) := by
  have hpair : ContinuousOn (fun r => (pcGlobal d r, r)) (Set.Ioo (0 : ℝ) 1) :=
    (continuousOn_pcGlobal hd).prodMk continuousOn_id
  have hmaps : ∀ r ∈ Set.Ioo (0 : ℝ) 1,
      (pcGlobal d r, r) ∈ Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (0 : ℝ) 1 := by
    intro r hr
    obtain ⟨hp0, hple⟩ := pcGlobal_pos_le hd hr.1 hr.2
    exact Set.mem_prod.mpr ⟨⟨hp0, lt_of_le_of_lt hple (pStar_lt_one hd)⟩, hr⟩
  exact ((sCM_continuousOn_prod hd).comp hpair hmaps).congr fun r _ => rfl

/-! ### Uniform bounds on a compact set of nonexceptional densities -/

/-- **A uniform margin for both contact densities.**  On a compact `K ⊆ (0,1) ∖ {r_*}` the two
contact densities stay in `[η, 1-η]` for some `η > 0`. -/
theorem exists_contact_margin (hd : 2 ≤ d) {K : Set ℝ} (hKS : K ⊆ Set.Ioo 0 1 \ {rStar d})
    (hKc : IsCompact K) :
    ∃ η : ℝ, 0 < η ∧ η < 1 ∧ ∀ r ∈ K,
      η ≤ r ∧ r ≤ 1 - η ∧ η ≤ scGlobal d r ∧ scGlobal d r ≤ 1 - η := by
  rcases Set.eq_empty_or_nonempty K with hempty | hne
  · exact ⟨1 / 2, by norm_num, by norm_num, fun r hr => absurd hr (by simp [hempty])⟩
  have hKsub : K ⊆ Set.Ioo (0 : ℝ) 1 := fun r hr => (hKS hr).1
  have hsc := continuousOn_scGlobal hd
  have hpair : ContinuousOn (fun r => (r, scGlobal d r)) K :=
    (continuousOn_id.mono hKsub).prodMk (hsc.mono hKsub)
  have hlow : ContinuousOn (fun r => min r (scGlobal d r)) K :=
    continuous_min.comp_continuousOn hpair
  have hhigh : ContinuousOn (fun r => max r (scGlobal d r)) K :=
    continuous_max.comp_continuousOn hpair
  obtain ⟨r₁, hr₁K, hr₁⟩ := hKc.exists_isMinOn hne hlow
  obtain ⟨r₂, hr₂K, hr₂⟩ := hKc.exists_isMaxOn hne hhigh
  have h₁pos : 0 < min r₁ (scGlobal d r₁) := by
    have hr₁mem := hKsub hr₁K
    exact lt_min hr₁mem.1 (scGlobal_mem_Ioo hd hr₁mem.1 hr₁mem.2).1
  have h₂lt : max r₂ (scGlobal d r₂) < 1 := by
    have hr₂mem := hKsub hr₂K
    exact max_lt hr₂mem.2 (scGlobal_mem_Ioo hd hr₂mem.1 hr₂mem.2).2
  refine ⟨min (min r₁ (scGlobal d r₁)) (min (1 - max r₂ (scGlobal d r₂)) (1 / 2)),
    lt_min h₁pos (lt_min (by linarith) (by norm_num)), ?_, ?_⟩
  · exact lt_of_le_of_lt (min_le_right _ _) (lt_of_le_of_lt (min_le_right _ _) (by norm_num))
  · intro r hr
    have hlowr : min r₁ (scGlobal d r₁) ≤ min r (scGlobal d r) := hr₁ hr
    have hhighr : max r (scGlobal d r) ≤ max r₂ (scGlobal d r₂) := hr₂ hr
    have hm1 : min (min r₁ (scGlobal d r₁)) (min (1 - max r₂ (scGlobal d r₂)) (1 / 2))
        ≤ min r (scGlobal d r) := le_trans (min_le_left _ _) hlowr
    have hm2 : min (min r₁ (scGlobal d r₁)) (min (1 - max r₂ (scGlobal d r₂)) (1 / 2))
        ≤ 1 - max r (scGlobal d r) := by
      have hstep : (1 : ℝ) - max r₂ (scGlobal d r₂) ≤ 1 - max r (scGlobal d r) := by linarith
      exact le_trans (le_trans (min_le_right _ _) (min_le_left _ _)) hstep
    refine ⟨le_trans hm1 (min_le_left _ _), by linarith [le_max_left r (scGlobal d r)],
      le_trans hm1 (min_le_right _ _), by linarith [le_max_right r (scGlobal d r)]⟩

/-- **(M3), the two-sided curvature bounds.**  On a compact `K ⊆ (0,1) ∖ {r_*}` the curvature
`g_{d,r}''(u) = h_{p_c(r),d}(u)/u` at the two contact densities is bounded above and below by
positive constants depending only on `d` and `K`. -/
theorem exists_nonexceptional_gap_curvature_bounds (hd : 2 ≤ d) {K : Set ℝ}
    (hKS : K ⊆ Set.Ioo 0 1 \ {rStar d}) (hKc : IsCompact K) :
    ∃ c C : ℝ, 0 < c ∧ ∀ r ∈ K, ∀ u : ℝ, (u = r ∨ u = scGlobal d r) →
      c ≤ gapD2 d r u ∧ gapD2 d r u ≤ C := by
  rcases Set.eq_empty_or_nonempty K with hempty | hne
  · exact ⟨1, 1, one_pos, fun r hr => absurd hr (by simp [hempty])⟩
  have hKsub : K ⊆ Set.Ioo (0 : ℝ) 1 := fun r hr => (hKS hr).1
  have hcont : ∀ w : ℝ → ℝ, ContinuousOn w K → (∀ r ∈ K, w r ∈ Set.Ioo (0 : ℝ) 1) →
      ContinuousOn (fun r => hpd (pcGlobal d r) d (w r) / w r) K := by
    intro w hw hwmem
    have hpair : ContinuousOn (fun r => (pcGlobal d r, w r)) K :=
      ((continuousOn_pcGlobal hd).mono hKsub).prodMk hw
    have hmaps : ∀ r ∈ K, (pcGlobal d r, w r) ∈ Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (0 : ℝ) 1 := by
      intro r hr
      obtain ⟨hp0, hple⟩ := pcGlobal_pos_le hd (hKsub hr).1 (hKsub hr).2
      exact Set.mem_prod.mpr ⟨⟨hp0, lt_of_le_of_lt hple (pStar_lt_one hd)⟩, hwmem r hr⟩
    exact (hpd_continuousOn_prod.comp hpair hmaps).div hw
      fun r hr => ne_of_gt (hwmem r hr).1
  have hc1 : ContinuousOn (fun r => hpd (pcGlobal d r) d r / r) K :=
    hcont (fun r => r) (continuousOn_id.mono hKsub) fun r hr => hKsub hr
  have hc2 : ContinuousOn (fun r => hpd (pcGlobal d r) d (scGlobal d r) / scGlobal d r) K :=
    hcont (scGlobal d) ((continuousOn_scGlobal hd).mono hKsub) fun r hr =>
      scGlobal_mem_Ioo hd (hKsub hr).1 (hKsub hr).2
  obtain ⟨a₁, ha₁K, ha₁⟩ := hKc.exists_isMinOn hne hc1
  obtain ⟨a₂, ha₂K, ha₂⟩ := hKc.exists_isMinOn hne hc2
  obtain ⟨b₁, hb₁K, hb₁⟩ := hKc.exists_isMaxOn hne hc1
  obtain ⟨b₂, hb₂K, hb₂⟩ := hKc.exists_isMaxOn hne hc2
  have hval : ∀ r ∈ K, ∀ u : ℝ, (u = r ∨ u = scGlobal d r) →
      gapD2 d r u = hpd (pcGlobal d r) d u / u ∧ 0 < gapD2 d r u := by
    intro r hr u hu
    obtain ⟨hr0, hr1⟩ := hKsub hr
    have hexc : r ≠ rStar d := fun h => (hKS hr).2 (by simp [h])
    have hu0 : 0 < u := by
      rcases hu with h | h
      · rw [h]; exact hr0
      · rw [h]; exact (scGlobal_mem_Ioo hd hr0 hr1).1
    exact ⟨gapD2_contact hd hr0 hr1 hexc hu hu0, gapD2_contact_pos hd hr0 hr1 hexc hu hu0⟩
  refine ⟨min (hpd (pcGlobal d a₁) d a₁ / a₁)
      (hpd (pcGlobal d a₂) d (scGlobal d a₂) / scGlobal d a₂),
    max (hpd (pcGlobal d b₁) d b₁ / b₁)
      (hpd (pcGlobal d b₂) d (scGlobal d b₂) / scGlobal d b₂), ?_, ?_⟩
  · refine lt_min ?_ ?_
    · have h := hval a₁ ha₁K a₁ (Or.inl rfl)
      rw [← h.1]; exact h.2
    · have h := hval a₂ ha₂K (scGlobal d a₂) (Or.inr rfl)
      rw [← h.1]; exact h.2
  · intro r hr u hu
    obtain ⟨heq, -⟩ := hval r hr u hu
    rw [heq]
    rcases hu with h | h
    · subst h
      exact ⟨le_trans (min_le_left _ _) (ha₁ hr), le_trans (hb₁ hr) (le_max_left _ _)⟩
    · subst h
      exact ⟨le_trans (min_le_right _ _) (ha₂ hr), le_trans (hb₂ hr) (le_max_right _ _)⟩

/-! ### The uniform third-derivative bound and the expansion -/

/-- A uniform bound for `g_{d,r}'''` over `r ∈ K` and `z` in a closed subinterval of `(0,1)`. -/
theorem exists_gapD3_bound (hd : 2 ≤ d) {K : Set ℝ} (hKS : K ⊆ Set.Ioo 0 1 \ {rStar d})
    (hKc : IsCompact K) {a b : ℝ} (ha : 0 < a) (hb : b < 1) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ r ∈ K, ∀ z ∈ Set.Icc a b, |gapD3 d r z| ≤ M := by
  rcases Set.eq_empty_or_nonempty K with hempty | hne
  · exact ⟨0, le_rfl, fun r hr => absurd hr (by simp [hempty])⟩
  rcases Set.eq_empty_or_nonempty (Set.Icc a b) with hI | hIne
  · exact ⟨0, le_rfl, fun r _ z hz => absurd hz (by simp [hI])⟩
  have hKsub : K ⊆ Set.Ioo (0 : ℝ) 1 := fun r hr => (hKS hr).1
  have hzmem : ∀ q : ℝ × ℝ, q ∈ K ×ˢ Set.Icc a b → 0 < q.2 ∧ q.2 < 1 := by
    intro q hq
    obtain ⟨-, hz⟩ := Set.mem_prod.mp hq
    exact ⟨lt_of_lt_of_le ha hz.1, lt_of_le_of_lt hz.2 hb⟩
  have h1 : ContinuousOn (fun q : ℝ × ℝ => (2 * q.2 - 1) / (q.2 ^ 2 * (1 - q.2) ^ 2))
      (K ×ˢ Set.Icc a b) := by
    refine ContinuousOn.div ((continuous_const.mul continuous_snd).sub
      continuous_const).continuousOn
      ((continuous_snd.pow 2).mul ((continuous_const.sub continuous_snd).pow 2)).continuousOn ?_
    intro q hq
    obtain ⟨hz0, hz1⟩ := hzmem q hq
    have h2 : 0 < q.2 ^ 2 * (1 - q.2) ^ 2 := by
      have : (0 : ℝ) < 1 - q.2 := by linarith
      positivity
    exact ne_of_gt h2
  have h2 : ContinuousOn (fun q : ℝ × ℝ => slope d (pcGlobal d) q.1) (K ×ˢ Set.Icc a b) :=
    ((continuousOn_slope_pcGlobal hd).mono hKsub).comp continuous_fst.continuousOn
      fun q hq => (Set.mem_prod.mp hq).1
  have hcont : ContinuousOn (fun q : ℝ × ℝ => |gapD3 d q.1 q.2|) (K ×ˢ Set.Icc a b) := by
    have h3 : ContinuousOn (fun q : ℝ × ℝ => gapD3 d q.1 q.2) (K ×ˢ Set.Icc a b) := by
      unfold gapD3
      exact h1.sub (h2.mul (continuousOn_const.mul
        (continuousOn_const.mul (continuous_snd.pow (d - 3)).continuousOn)))
    exact h3.abs
  obtain ⟨q₀, hq₀mem, hq₀⟩ := (hKc.prod isCompact_Icc).exists_isMaxOn (hne.prod hIne) hcont
  refine ⟨|gapD3 d q₀.1 q₀.2|, abs_nonneg _, ?_⟩
  intro r hr z hz
  exact hq₀ (show (r, z) ∈ K ×ˢ Set.Icc a b from Set.mem_prod.mpr ⟨hr, hz⟩)

/-- **(M3), the quadratic expansion** `eq:contact-gap-expansion`: on a compact
`K ⊆ (0,1) ∖ {r_*}` there are a radius `ρ > 0` and a constant `M` such that, for every `r ∈ K`
and either contact density `u`, `|g_{d,r}(z) - ½g_{d,r}''(u)(z-u)²| ≤ M|z-u|³` for
`|z - u| ≤ ρ`. -/
theorem exists_nonexceptional_gap_expansion (hd : 2 ≤ d) {K : Set ℝ}
    (hKS : K ⊆ Set.Ioo 0 1 \ {rStar d}) (hKc : IsCompact K) :
    ∃ ρ M : ℝ, 0 < ρ ∧ 0 ≤ M ∧ ∀ r ∈ K, ∀ u : ℝ, (u = r ∨ u = scGlobal d r) →
      ∀ z : ℝ, |z - u| ≤ ρ →
        |gapD d r z - gapD2 d r u / 2 * (z - u) ^ 2| ≤ M * |z - u| ^ 3 := by
  obtain ⟨η, hη0, hη1, hηbd⟩ := exists_contact_margin hd hKS hKc
  obtain ⟨M, hM0, hM⟩ := exists_gapD3_bound hd hKS hKc (a := η / 2) (b := 1 - η / 2)
    (by linarith) (by linarith)
  refine ⟨η / 2, M, by linarith, hM0, ?_⟩
  intro r hr u hu z hz
  have hKsub : K ⊆ Set.Ioo (0 : ℝ) 1 := fun r hr => (hKS hr).1
  obtain ⟨hr0, hr1⟩ := hKsub hr
  have hexc : r ≠ rStar d := fun h => (hKS hr).2 (by simp [h])
  obtain ⟨hηr, hr1', hηs, hs1⟩ := hηbd r hr
  -- the contact density and its window
  have hu0 : η ≤ u ∧ u ≤ 1 - η := by
    rcases hu with h | h
    · rw [h]; exact ⟨hηr, hr1'⟩
    · rw [h]; exact ⟨hηs, hs1⟩
  have hwin : ∀ y : ℝ, |y - u| ≤ η / 2 → y ∈ Set.Icc (η / 2) (1 - η / 2) := by
    intro y hy
    have h1 := abs_le.mp hy
    exact ⟨by linarith [hu0.1, h1.1], by linarith [hu0.2, h1.2]⟩
  have hwin01 : ∀ y : ℝ, |y - u| ≤ η / 2 → 0 < y ∧ y < 1 := by
    intro y hy
    obtain ⟨h1, h2⟩ := hwin y hy
    exact ⟨by linarith, by linarith⟩
  -- derivative data on the window, in the shifted variable
  have hgap1 : ∀ y : ℝ, |y - u| ≤ η / 2 → HasDerivAt (gapD d r) (gapD1 d r y) y := by
    intro y hy
    obtain ⟨hy0, hy1⟩ := hwin01 y hy
    exact hasDerivAt_gapD hd hr0 hr1 hy0 hy1
  have hgap2 : ∀ y : ℝ, |y - u| ≤ η / 2 → HasDerivAt (gapD1 d r) (gapD2 d r y) y := by
    intro y hy
    obtain ⟨hy0, hy1⟩ := hwin01 y hy
    exact hasDerivAt_gapD1 hd hr0 hr1 hy0 hy1
  have hgap3 : ∀ y : ℝ, |y - u| ≤ η / 2 → HasDerivAt (gapD2 d r) (gapD3 d r y) y := by
    intro y hy
    obtain ⟨hy0, hy1⟩ := hwin01 y hy
    exact hasDerivAt_gapD2 hd hy0 hy1
  have hbnd : ∀ y : ℝ, |y - u| ≤ η / 2 → |gapD3 d r y| ≤ M := fun y hy =>
    hM r hr y (hwin y hy)
  have hzero : gapD d r u = 0 := by
    rcases hu with h | h
    · rw [h]; exact gapD_self d r
    · rw [h]
      exact (gapD_eq_zero_iff hd hr0 hr1 hexc
        ⟨(scGlobal_mem_Ioo hd hr0 hr1).1.le, (scGlobal_mem_Ioo hd hr0 hr1).2.le⟩).mpr (Or.inr rfl)
  have hzero1 : gapD1 d r u = 0 := gapD1_contact hd hr0 hr1 hexc hu
  rcases le_or_gt u z with hzu | hzu
  · -- right of the contact
    have hshift : ∀ t ∈ Set.Icc (0 : ℝ) (η / 2), |u + t - u| ≤ η / 2 := by
      intro t ht
      rw [add_sub_cancel_left, abs_of_nonneg ht.1]
      exact ht.2
    have hinner : ∀ t : ℝ, HasDerivAt (fun s : ℝ => u + s) 1 t := by
      intro t; simpa using (hasDerivAt_id t).const_add u
    have h := cubic_taylor_gap (f := fun t => gapD d r (u + t))
      (f1 := fun t => gapD1 d r (u + t)) (f2 := fun t => gapD2 d r (u + t))
      (f3 := fun t => gapD3 d r (u + t)) (A := gapD2 d r u) (M := M)
      (fun t ht => by simpa [Function.comp_def] using (hgap1 (u + t) (hshift t ht)).comp t (hinner t))
      (fun t ht => by simpa [Function.comp_def] using (hgap2 (u + t) (hshift t ht)).comp t (hinner t))
      (fun t ht => by simpa [Function.comp_def] using (hgap3 (u + t) (hshift t ht)).comp t (hinner t))
      (by simpa using hzero) (by simpa using hzero1) (by simp)
      (fun t ht => hbnd (u + t) (hshift t ht))
    have hzt : z - u ∈ Set.Icc (0 : ℝ) (η / 2) := by
      refine ⟨by linarith, ?_⟩
      have := abs_le.mp hz
      linarith [this.2]
    have h' := h (z - u) hzt
    rw [add_sub_cancel] at h'
    calc |gapD d r z - gapD2 d r u / 2 * (z - u) ^ 2|
        = |gapD d r z - gapD2 d r u * (z - u) ^ 2 / 2| := by ring_nf
      _ ≤ M * (z - u) ^ 3 := h'
      _ = M * |z - u| ^ 3 := by rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ z - u)]
  · -- left of the contact
    have hshift : ∀ t ∈ Set.Icc (0 : ℝ) (η / 2), |u - t - u| ≤ η / 2 := by
      intro t ht
      have : u - t - u = -t := by ring
      rw [this, abs_neg, abs_of_nonneg ht.1]
      exact ht.2
    have hcomp : ∀ t : ℝ, HasDerivAt (fun s : ℝ => u - s) (-1) t := by
      intro t
      simpa using (hasDerivAt_id t).const_sub u
    have h := cubic_taylor_gap (f := fun t => gapD d r (u - t))
      (f1 := fun t => -gapD1 d r (u - t)) (f2 := fun t => gapD2 d r (u - t))
      (f3 := fun t => -gapD3 d r (u - t)) (A := gapD2 d r u) (M := M)
      (fun t ht => by
        simpa [Function.comp_def] using (hgap1 (u - t) (hshift t ht)).comp t (hcomp t))
      (fun t ht => by
        have h := ((hgap2 (u - t) (hshift t ht)).comp t (hcomp t)).neg
        have hval : -(gapD2 d r (u - t) * -1) = gapD2 d r (u - t) := by ring
        rw [← hval]
        exact h.congr_deriv rfl)
      (fun t ht => by
        simpa [Function.comp_def] using (hgap3 (u - t) (hshift t ht)).comp t (hcomp t))
      (by simpa using hzero) (by simpa using hzero1) (by simp)
      (fun t ht => by
        rw [abs_neg]
        exact hbnd (u - t) (hshift t ht))
    have hzt : u - z ∈ Set.Icc (0 : ℝ) (η / 2) := by
      refine ⟨by linarith, ?_⟩
      have := abs_le.mp hz
      linarith [this.1]
    have h' := h (u - z) hzt
    rw [sub_sub_cancel] at h'
    have habs : |z - u| = u - z := by
      rw [abs_of_nonpos (by linarith : z - u ≤ 0)]; ring
    calc |gapD d r z - gapD2 d r u / 2 * (z - u) ^ 2|
        = |gapD d r z - gapD2 d r u * (u - z) ^ 2 / 2| := by
          rw [show (z - u) ^ 2 = (u - z) ^ 2 by ring]; ring_nf
      _ ≤ M * (u - z) ^ 3 := h'
      _ = M * |z - u| ^ 3 := by rw [habs]

/-! ### The density form of the quadratic separation -/

/-- **`eq:contact-quadratic-separation` in the density variable.**  On a compact
`K ⊆ (0,1) ∖ {r_*}` there is `γ_{d,K} > 0` with
`g_{d,r}(z) ≥ γ_{d,K} dist(z,{r,s_c(r)})²` for all `r ∈ K` and `z ∈ [0,1]`. -/
theorem exists_nonexceptional_gap_quadratic_lower (hd : 2 ≤ d) {K : Set ℝ}
    (hKS : K ⊆ Set.Ioo 0 1 \ {rStar d}) (hKc : IsCompact K) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ r ∈ K, ∀ z ∈ Set.Icc (0 : ℝ) 1,
      γ * (min |z - r| |z - scGlobal d r|) ^ 2 ≤ gapD d r z := by
  obtain ⟨γ₀, hγ₀, hsep⟩ := lz_boundary_quadSep hd hKS hKc
  obtain ⟨η, hη0, hη1, hηbd⟩ := exists_contact_margin hd hKS hKc
  refine ⟨γ₀ * (η ^ (d - 1)) ^ 2, by positivity, ?_⟩
  intro r hr z hz
  have hKsub : K ⊆ Set.Ioo (0 : ℝ) 1 := fun r hr => (hKS hr).1
  obtain ⟨hr0, hr1⟩ := hKsub hr
  obtain ⟨hηr, -, hηs, -⟩ := hηbd r hr
  obtain ⟨hp0, hple⟩ := pcGlobal_pos_le hd hr0 hr1
  have hp1 : pcGlobal d r < 1 := lt_of_le_of_lt hple (pStar_lt_one hd)
  have hd1 : 1 ≤ d := le_trans (by norm_num) hd
  have hzd : z ^ d ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨pow_nonneg hz.1 d, pow_le_one₀ hz.1 hz.2⟩
  -- pass from the `x`-coordinate distance to the density distance
  have hkey : ∀ v : ℝ, η ≤ v → η ^ (d - 1) * |z - v| ≤ |z ^ d - v ^ d| := by
    intro v hv
    have hv0 : 0 ≤ v := le_trans hη0.le hv
    calc η ^ (d - 1) * |z - v| ≤ v ^ (d - 1) * |z - v| :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hη0.le hv _) (abs_nonneg _)
      _ ≤ |z ^ d - v ^ d| := pow_sub_pow_ge_lz hz.1 hv0 hd1
  have hmin : η ^ (d - 1) * min |z - r| |z - scGlobal d r|
      ≤ min |z ^ d - r ^ d| |z ^ d - (scGlobal d r) ^ d| := by
    refine le_min ?_ ?_
    · exact le_trans (mul_le_mul_of_nonneg_left (min_le_left _ _) (by positivity)) (hkey r hηr)
    · exact le_trans (mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity))
        (hkey (scGlobal d r) hηs)
  have hminnn : 0 ≤ η ^ (d - 1) * min |z - r| |z - scGlobal d r| := by
    have h : (0 : ℝ) ≤ min |z - r| |z - scGlobal d r| := le_min (abs_nonneg _) (abs_nonneg _)
    positivity
  have hsq : (η ^ (d - 1) * min |z - r| |z - scGlobal d r|) ^ 2
      ≤ (min |z ^ d - r ^ d| |z ^ d - (scGlobal d r) ^ d|) ^ 2 :=
    pow_le_pow_left₀ hminnn hmin 2
  have hgap : gapD d r z = phi (pcGlobal d r) d (z ^ d)
      - (phi (pcGlobal d r) d (r ^ d)
        + deriv (phi (pcGlobal d r) d) (r ^ d) * (z ^ d - r ^ d)) := by
    rw [gapD_eq_phi_sub hd hr0.le hz.1,
      slope_eq_deriv_phi (pc := pcGlobal d) hd hp0 hp1 hr0 hr1]
  rw [hgap]
  calc γ₀ * (η ^ (d - 1)) ^ 2 * (min |z - r| |z - scGlobal d r|) ^ 2
      = γ₀ * (η ^ (d - 1) * min |z - r| |z - scGlobal d r|) ^ 2 := by ring
    _ ≤ γ₀ * (min |z ^ d - r ^ d| |z ^ d - (scGlobal d r) ^ d|) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq hγ₀.le
    _ ≤ phi (pcGlobal d r) d (z ^ d) - (phi (pcGlobal d r) d (r ^ d)
          + deriv (phi (pcGlobal d r) d) (r ^ d) * (z ^ d - r ^ d)) := hsep r hr (z ^ d) hzd

/-! ### (M3) in paper form -/

/-- **(M3) of Theorem 3.1**, with the global bound that follows it in `sec:lz-boundary`:
`eq:supporting-cost-gap`, the nonnegativity and the two-point contact set of the gap, the paper's
curvature formula `g_{d,r}''(u) = h_{p_c(r),d}(u)/u` at each contact, its two-sided bounds, the
quadratic expansion `eq:contact-gap-expansion` and the quadratic lower bound
`eq:contact-quadratic-separation`.

This is the nonexceptional twin of `lz_boundary_exceptional_gap`: the two theorems are the
entry points for comparing the quadratic regime of `sec:nonexceptional-endpoint` with the
quartic regime of `sec:singular-endpoint`, and their conjuncts are in the same order. -/
theorem lz_boundary_nonexceptional_gap (hd : 2 ≤ d) :
    (∀ r ∈ Set.Ioo (0 : ℝ) 1 \ {rStar d}, ∀ z : ℝ, 0 ≤ z →
        gapD d r z = phi (pcGlobal d r) d (z ^ d)
          - (phi (pcGlobal d r) d (r ^ d)
            + deriv (phi (pcGlobal d r) d) (r ^ d) * (z ^ d - r ^ d))) ∧
      (∀ r ∈ Set.Ioo (0 : ℝ) 1 \ {rStar d}, ∀ z ∈ Set.Icc (0 : ℝ) 1,
        0 ≤ gapD d r z ∧ (gapD d r z = 0 ↔ z = r ∨ z = scGlobal d r)) ∧
      (∀ r ∈ Set.Ioo (0 : ℝ) 1 \ {rStar d}, ∀ u : ℝ, (u = r ∨ u = scGlobal d r) → 0 < u →
        gapD2 d r u = hpd (pcGlobal d r) d u / u ∧ 0 < gapD2 d r u) ∧
      (∀ K : Set ℝ, K ⊆ Set.Ioo 0 1 \ {rStar d} → IsCompact K →
        ∃ c C : ℝ, 0 < c ∧ ∀ r ∈ K, ∀ u : ℝ, (u = r ∨ u = scGlobal d r) →
          c ≤ gapD2 d r u ∧ gapD2 d r u ≤ C) ∧
      (∀ K : Set ℝ, K ⊆ Set.Ioo 0 1 \ {rStar d} → IsCompact K →
        ∃ ρ M : ℝ, 0 < ρ ∧ 0 ≤ M ∧ ∀ r ∈ K, ∀ u : ℝ, (u = r ∨ u = scGlobal d r) →
          ∀ z : ℝ, |z - u| ≤ ρ →
            |gapD d r z - gapD2 d r u / 2 * (z - u) ^ 2| ≤ M * |z - u| ^ 3) ∧
      (∀ K : Set ℝ, K ⊆ Set.Ioo 0 1 \ {rStar d} → IsCompact K →
        ∃ γ : ℝ, 0 < γ ∧ ∀ r ∈ K, ∀ z ∈ Set.Icc (0 : ℝ) 1,
          γ * (min |z - r| |z - scGlobal d r|) ^ 2 ≤ gapD d r z) := by
  refine ⟨?_, ?_, ?_,
    fun K hKS hKc => exists_nonexceptional_gap_curvature_bounds hd hKS hKc,
    fun K hKS hKc => exists_nonexceptional_gap_expansion hd hKS hKc,
    fun K hKS hKc => exists_nonexceptional_gap_quadratic_lower hd hKS hKc⟩
  · intro r hr z hz
    obtain ⟨⟨hr0, hr1⟩, -⟩ := hr
    obtain ⟨hp0, hple⟩ := pcGlobal_pos_le hd hr0 hr1
    have hp1 : pcGlobal d r < 1 := lt_of_le_of_lt hple (pStar_lt_one hd)
    rw [gapD_eq_phi_sub hd hr0.le hz,
      slope_eq_deriv_phi (pc := pcGlobal d) hd hp0 hp1 hr0 hr1]
  · intro r hr z hz
    have hexc : r ≠ rStar d := fun h => hr.2 (by simp [h])
    exact ⟨gapD_nonneg hd hr.1.1 hr.1.2 hexc hz,
      gapD_eq_zero_iff hd hr.1.1 hr.1.2 hexc hz⟩
  · intro r hr u hu hu0
    have hexc : r ≠ rStar d := fun h => hr.2 (by simp [h])
    exact ⟨gapD2_contact hd hr.1.1 hr.1.2 hexc hu hu0,
      gapD2_contact_pos hd hr.1.1 hr.1.2 hexc hu hu0⟩

end UpperTailOptimizers
