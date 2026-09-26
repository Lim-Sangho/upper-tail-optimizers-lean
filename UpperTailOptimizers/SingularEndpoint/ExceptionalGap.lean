import UpperTailOptimizers.LZBoundary.NonexceptionalGap
import UpperTailOptimizers.SingularEndpoint.ConstantGraphonComparison.GamTaylor
import UpperTailOptimizers.SingularEndpoint.LocalizationRankOne.Quartic

/-!
# (M4) of Theorem 3.1: the supporting cost gap at the exceptional density

`sec:lz-boundary` of `paper/paper.tex` defines, at the exceptional density `r_*` where the two
contacts merge, the supporting cost gap `eq:endpoint-supporting-gap`

`Γ_d(z) = J_{p_*}(z) - ℓ_{r_*}(z^d)`,

records that it is the limit of the gaps `g_{d,r}` of `eq:supporting-cost-gap` as `r → r_*`, and
gives its quartic expansion `eq:endpoint-gap-expansion` together with the global bounds
`eq:endpoint-gap-positivity` and `eq:endpoint-gap-quartic-bound`.

In Lean the exceptional gap is `Gam` (`SingularEndpoint/RankOneStationaryFamily/Defs.lean`), defined
by the explicit formula `J_{p_*}(z) - J_{p_*}(r_*) - β_d(z^d - r_*^d)`, and its analytic theory
(positivity, the fourth-derivative value, the quartic expansion and the quartic lower bound) is
developed in `SingularEndpoint/`, since that is where Section 5 consumes it.  This file supplies
the missing link to Section 3: the slope `β_d` **is** the tangent slope of `φ_{p_*,d}` at `r_*^d`,
so `Gam` is the tangent gap of the paper, and `Gam` is the `r = r_*` member of the family `gapD`
of `LZBoundary/DensityGap.lean`.

## Contents

* `slope_pcGlobal_rStar`, `deriv_phi_pStar_rStar` — the tangent slope at the merged contact is
  `β_d`;
* `gapD_rStar` — `g_{d,r_*} = Γ_d`, so the two definitions agree;
* `Gam_eq_phi_sub_tangent` — `eq:endpoint-supporting-gap` exactly as the paper writes it;
* `phi''_pStar_rStar` — the first identity of `eq:endpoint-contact-derivatives`
  (the higher ones are the `Γ_d`-derivative ladder of `LstarTaylor.lean`, which the chain rule
  transports to `φ_{p_*,d}`);
* `exists_exceptional_gap_expansion` — `eq:endpoint-gap-expansion` in the `O`-form the paper
  displays;
* `tendsto_gapD_rStar` — `Γ_d(z) = lim_{r → r_*} g_{d,r}(z)`;
* `lz_boundary_exceptional_gap` — (M4) in one statement, with the two global bounds.  It is the
  deliberate twin of `lz_boundary_nonexceptional_gap` of `LZBoundary/NonexceptionalGap.lean`, which
  states (M3) with the same conjuncts in the same order; comparing the two is comparing the
  quadratic regime of `sec:nonexceptional-endpoint` with the quartic regime of
  `sec:singular-endpoint`.
-/

namespace UpperTailOptimizers

open Real Set Filter Topology

variable {d : ℕ}

/-- The tangent slope at the merged contact is `β_d`. -/
theorem slope_pcGlobal_rStar (hd : 2 ≤ d) : slope d (pcGlobal d) (rStar d) = betaD d := by
  have hr0 : 0 < rStar d := rStar_pos hd
  have hdne : (d : ℝ) ≠ 0 := ne_of_gt (dpos hd)
  have hpow : rStar d ^ (d - 1) ≠ 0 := pow_ne_zero _ (ne_of_gt hr0)
  unfold slope
  rw [pcGlobal_rStar hd, triple_contact_one hd, betaD]
  field_simp

/-- `g_{d,r_*} = Γ_d`: the exceptional gap is the `r = r_*` member of the family. -/
theorem gapD_rStar (hd : 2 ≤ d) (z : ℝ) : gapD d (rStar d) z = Gam d z := by
  unfold gapD Gam
  rw [pcGlobal_rStar hd, slope_pcGlobal_rStar hd]
  ring

/-- `φ_{p_*,d}'(r_*^d) = β_d`. -/
theorem deriv_phi_pStar_rStar (hd : 2 ≤ d) :
    deriv (phi (pStar d) d) (rStar d ^ d) = betaD d := by
  have hr0 : 0 < rStar d := rStar_pos hd
  have hr1 : rStar d < 1 := rStar_lt_one hd
  have hp0 : 0 < pStar d := pStar_pos hd
  have hp1 : pStar d < 1 := pStar_lt_one hd
  have hdne : (d : ℝ) ≠ 0 := ne_of_gt (dpos hd)
  have hpow : rStar d ^ (d - 1) ≠ 0 := pow_ne_zero _ (ne_of_gt hr0)
  rw [deriv_phi_pow_eq_sCM hd hp0 hp1 hr0 hr1, sCM, triple_contact_one hd, betaD]
  field_simp

/-- **`eq:endpoint-supporting-gap`**: `Γ_d(z) = J_{p_*}(z) - ℓ_{r_*}(z^d)`, where `ℓ_{r_*}` is
the tangent line of `φ_{p_*,d}` at `r_*^d`. -/
theorem Gam_eq_phi_sub_tangent (hd : 2 ≤ d) {z : ℝ} (hz : 0 ≤ z) :
    Gam d z = phi (pStar d) d (z ^ d)
      - (phi (pStar d) d (rStar d ^ d)
        + deriv (phi (pStar d) d) (rStar d ^ d) * (z ^ d - rStar d ^ d)) := by
  have hr0 : 0 < rStar d := rStar_pos hd
  rw [← gapD_rStar hd z, gapD_eq_phi_sub hd hr0.le hz, pcGlobal_rStar hd,
    slope_pcGlobal_rStar hd, deriv_phi_pStar_rStar hd]

/-- **The first identity of `eq:endpoint-contact-derivatives`**: `φ_{p_*,d}''(r_*^d) = 0`, the
degeneracy that makes the merged contact quartic. -/
theorem phi''_pStar_rStar (hd : 2 ≤ d) : phi'' (pStar d) d (rStar d ^ d) = 0 := by
  have hr0 : 0 < rStar d := rStar_pos hd
  have hp0 : 0 < pStar d := pStar_pos hd
  have hp1 : pStar d < 1 := pStar_lt_one hd
  have hroot : Real.rpow (rStar d ^ d) (1 / (d : ℝ)) = rStar d := by
    rw [one_div]
    exact Real.pow_rpow_inv_natCast hr0.le (by omega)
  have hzero : hpd (pStar d) d (rStar d) = 0 :=
    (hpd_rStar_eq_zero_iff hd hp0 hp1).mpr rfl
  unfold phi''
  rw [hroot, hzero, zero_div]

/-- **`eq:endpoint-gap-expansion`** in the paper's `O`-form: on a window of `r_*`,
`|Γ_d(z) - d^5/(24(d-1)^2)(z - r_*)^4| ≤ C|z - r_*|^5`.  The exact identity behind it, with the
analytic tail `GamTail`, is `Gam_expand`. -/
theorem exists_exceptional_gap_expansion (hd : 2 ≤ d) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧ ∀ z : ℝ, |z - rStar d| ≤ δ →
      |Gam d z - (d : ℝ) ^ 5 / ((d : ℝ) - 1) ^ 2 / 24 * (z - rStar d) ^ 4|
        ≤ C * |z - rStar d| ^ 5 := by
  set C : ℝ := |GamTail d (rStar d)| + 1 with hCdef
  have hC0 : 0 ≤ C := by
    rw [hCdef]; positivity
  have hmem : Set.Iio C ∈ 𝓝 |GamTail d (rStar d)| := by
    refine gt_mem_nhds ?_
    rw [hCdef]; linarith
  have hev : ∀ᶠ z in 𝓝 (rStar d), |GamTail d z| ∈ Set.Iio C :=
    ((continuousAt_GamTail hd).abs).eventually hmem
  obtain ⟨δ, hδ0, hδ⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨C, δ / 2, hC0, by linarith, ?_⟩
  intro z hz
  have hdist : dist z (rStar d) < δ := by
    rw [Real.dist_eq]
    linarith
  have hbound : |GamTail d z| ≤ C := le_of_lt (hδ hdist)
  have hexp := Gam_expand hd z
  have hrw : Gam d z - (d : ℝ) ^ 5 / ((d : ℝ) - 1) ^ 2 / 24 * (z - rStar d) ^ 4
      = (z - rStar d) ^ 5 * GamTail d z := by
    rw [hexp]; ring
  rw [hrw, abs_mul, abs_pow]
  calc |z - rStar d| ^ 5 * |GamTail d z| ≤ |z - rStar d| ^ 5 * C :=
        mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = C * |z - rStar d| ^ 5 := by ring

/-- `J_p(z)` is continuous in the parameter `p` on `(0,1)`, for every fixed `z ∈ [0,1]`. -/
theorem continuousOn_Jp_param {z : ℝ} (hz : z ∈ Set.Icc (0 : ℝ) 1) :
    ContinuousOn (fun p => Jp p z) (Set.Ioo (0 : ℝ) 1) := by
  have hterm : ∀ w : ℝ, 0 ≤ w →
      ContinuousOn (fun p : ℝ => w * Real.log (w / p)) (Set.Ioo (0 : ℝ) 1) := by
    intro w hw
    rcases eq_or_lt_of_le hw with h | h
    · have hfun : (fun p : ℝ => w * Real.log (w / p)) = fun _ => 0 := by
        funext p; rw [← h]; simp
      rw [hfun]; exact continuousOn_const
    · refine continuousOn_const.mul (ContinuousOn.log ?_ ?_)
      · exact continuousOn_const.div continuousOn_id fun p hp => ne_of_gt hp.1
      · intro p hp; exact ne_of_gt (div_pos h hp.1)
  have h1 := hterm z hz.1
  have h2 : ContinuousOn (fun p : ℝ => (1 - z) * Real.log ((1 - z) / (1 - p)))
      (Set.Ioo (0 : ℝ) 1) := by
    have hw : (0 : ℝ) ≤ 1 - z := by linarith [hz.2]
    rcases eq_or_lt_of_le hw with h | h
    · have hfun : (fun p : ℝ => (1 - z) * Real.log ((1 - z) / (1 - p))) = fun _ => 0 := by
        funext p; rw [← h]; simp
      rw [hfun]; exact continuousOn_const
    · refine continuousOn_const.mul (ContinuousOn.log ?_ ?_)
      · refine continuousOn_const.div (continuousOn_const.sub continuousOn_id) ?_
        intro p hp; exact ne_of_gt (by linarith [hp.2])
      · intro p hp; exact ne_of_gt (div_pos h (by linarith [hp.2]))
  exact h1.add h2

/-- **`Γ_d` is the limit of the gaps `g_{d,r}` as `r → r_*`**, the identification stated in
(M4). -/
theorem tendsto_gapD_rStar (hd : 2 ≤ d) {z : ℝ} (hz : z ∈ Set.Icc (0 : ℝ) 1) :
    Tendsto (fun r => gapD d r z) (𝓝[Set.Ioo (0 : ℝ) 1] (rStar d)) (𝓝 (Gam d z)) := by
  have hrmem : rStar d ∈ Set.Ioo (0 : ℝ) 1 := rStar_mem_Ioo hd
  have hpc := continuousOn_pcGlobal hd
  have hmapsIoo : ∀ r ∈ Set.Ioo (0 : ℝ) 1, pcGlobal d r ∈ Set.Ioo (0 : ℝ) 1 := by
    intro r hr
    obtain ⟨hp0, hple⟩ := pcGlobal_pos_le hd hr.1 hr.2
    exact ⟨hp0, lt_of_le_of_lt hple (pStar_lt_one hd)⟩
  -- the three `r`-dependent pieces of the gap
  have hA : ContinuousOn (fun r => Jp (pcGlobal d r) z) (Set.Ioo (0 : ℝ) 1) :=
    (continuousOn_Jp_param hz).comp hpc hmapsIoo
  have hB : ContinuousOn (fun r => Jp (pcGlobal d r) r) (Set.Ioo (0 : ℝ) 1) := by
    have hpair : ContinuousOn (fun r => (pcGlobal d r, r)) (Set.Ioo (0 : ℝ) 1) :=
      hpc.prodMk continuousOn_id
    have hmaps : ∀ r ∈ Set.Ioo (0 : ℝ) 1,
        (pcGlobal d r, r) ∈ Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (0 : ℝ) 1 :=
      fun r hr => Set.mem_prod.mpr ⟨hmapsIoo r hr, hr⟩
    exact Jp_continuousOn_prod.comp hpair hmaps
  have hC : ContinuousOn (fun r => slope d (pcGlobal d) r * (z ^ d - r ^ d))
      (Set.Ioo (0 : ℝ) 1) :=
    (continuousOn_slope_pcGlobal hd).mul
      (continuousOn_const.sub (continuousOn_pow _))
  have hcont : ContinuousOn (fun r => gapD d r z) (Set.Ioo (0 : ℝ) 1) := by
    unfold gapD
    exact hA.sub (hB.add hC)
  have h := (hcont (rStar d) hrmem).tendsto
  rw [gapD_rStar hd z] at h
  exact h

/-- **(M4) of Theorem 3.1**, with the two global bounds that follow it in `sec:lz-boundary`:
`eq:endpoint-supporting-gap`, the identification of `Γ_d` as the limit of `g_{d,r}`,
`eq:endpoint-gap-positivity`, the quartic expansion `eq:endpoint-gap-expansion` and the
quartic lower bound `eq:endpoint-gap-quartic-bound`. -/
theorem lz_boundary_exceptional_gap (hd : 2 ≤ d) :
    (∀ z : ℝ, 0 ≤ z → Gam d z = phi (pStar d) d (z ^ d)
        - (phi (pStar d) d (rStar d ^ d)
          + deriv (phi (pStar d) d) (rStar d ^ d) * (z ^ d - rStar d ^ d))) ∧
      (∀ z : ℝ, gapD d (rStar d) z = Gam d z) ∧
      (∀ z ∈ Set.Icc (0 : ℝ) 1,
        Tendsto (fun r => gapD d r z) (𝓝[Set.Ioo (0 : ℝ) 1] (rStar d)) (𝓝 (Gam d z))) ∧
      (∀ z ∈ Set.Icc (0 : ℝ) 1, 0 ≤ Gam d z ∧ (Gam d z = 0 ↔ z = rStar d)) ∧
      (∀ z : ℝ, Gam d z
        = (d : ℝ) ^ 5 / ((d : ℝ) - 1) ^ 2 / 24 * (z - rStar d) ^ 4
          + (z - rStar d) ^ 5 * GamTail d z) ∧
      (∃ c : ℝ, 0 < c ∧ ∀ z ∈ Set.Icc (0 : ℝ) 1, c * |z - rStar d| ^ 4 ≤ Gam d z) := by
  refine ⟨fun z hz => Gam_eq_phi_sub_tangent hd hz, fun z => gapD_rStar hd z,
    fun z hz => tendsto_gapD_rStar hd hz, fun z hz => ⟨Gam_nonneg hd hz.1 hz.2,
      Gam_eq_zero_iff hd hz.1 hz.2⟩, fun z => Gam_expand hd z,
    exists_exceptional_gap_quartic_lower hd⟩

end UpperTailOptimizers
