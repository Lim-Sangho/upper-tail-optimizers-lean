import UpperTailOptimizers.SingularEndpoint.RankOneStationaryFamily.Contact
import UpperTailOptimizers.NonexceptionalEndpoint.QuadraticGrowth.PowBounds
import UpperTailOptimizers.LZBoundary.Curve

/-!
# The singular endpoint supporting gap is positive (Section 5, `paper/sections/singular.tex`)

This file proves `eq:endpoint-gap-positivity` of `sec:localization-rank-one`: the singular endpoint
supporting gap `Γ_d(z) = J_{p_*}(z) - J_{p_*}(r_*) - β_d (z^d - r_*^d)` is nonnegative on
`[0,1]` and vanishes only at the exceptional density `r_* = (d-1)/d`.  It also records the
elementary facts about the scalar convexity defect `R_d` of `SingularEndpoint/RankOneStationaryFamily/Defs.lean`, which
the paper does not name: its proof of `lem:localization-rank-one` uses the unnormalised bound
`0 ≤ z^d - r_*^d - d r_*^{d-1}(z - r_*)` directly.

The paper deduces the positivity from the convexity of `x ↦ J_{p_*}(x^{1/d})`.  The route
taken here avoids the coordinate change: writing `𝓛_* = Γ_d'` for the rank-one KKT function
of `eq:kkt-quartic-expansion`, the normalised quotient `𝓛_*(z)/z^{d-1}` has derivative

```
d/dz [ 𝓛_*(z) / z^{d-1} ] = h_{p_*,d}(z) / z^d ,
```

because `z 𝓛_*'(z) - (d-1) 𝓛_*(z) = z J_{p_*}''(z) - (d-1) J_{p_*}'(z)` — the two `γ_*`
terms cancel exactly.  The right-hand side is the convexity defect `h_{p_*,d}` of Section 3,
which is positive on `(0,1)` away from `r_*` and vanishes there.  So the quotient is
strictly increasing and vanishes at `r_*`, whence `𝓛_* < 0` below `r_*` and `𝓛_* > 0` above,
and `Γ_d` is strictly decreasing then strictly increasing with minimum value `Γ_d(r_*) = 0`.

## Contents

* `Lstar_neg`, `Lstar_pos` — the sign of `𝓛_*` on either side of `r_*`;
* `continuousOn_Gam`, `Gam_strictAntiOn`, `Gam_strictMonoOn` — the shape of `Γ_d` on
  `[0,1]`;
* `Gam_nonneg`, `Gam_pos_of_ne`, `Gam_eq_zero_iff` — `eq:endpoint-gap-positivity`;
* `Rd_nonneg`, `Rd_rStar`, `Rd_pos_of_ne` — the scalar convexity defect `R_d` (see
  the edge/moment identity) is nonnegative, with equality only at `r_*`;
* `sub_rStar_eq` — the pointwise form of the edge/moment identity.

The quartic lower bound `eq:endpoint-gap-quartic-bound` is *not* proved here.
-/

namespace UpperTailOptimizers

namespace SingularEndpoint

open Real

variable {d : ℕ}

/-! ## The normalised KKT function `𝓛_*(z)/z^{d-1}` -/

/-- The normalised rank-one KKT function `𝓛_*(z)/z^{d-1}`.  Its derivative is the Section 3
convexity defect divided by `z^d`, which is what makes the sign of `𝓛_*` transparent. -/
private noncomputable def LstarNorm (d : ℕ) (z : ℝ) : ℝ := Lstar d z / z ^ (d - 1)

/-- `d/dz [𝓛_*(z)/z^{d-1}] = h_{p_*,d}(z)/z^d`: the `γ_*` terms cancel, leaving exactly the
convexity defect `h_{p,d}(z) = z J_p''(z) - (d-1) J_p'(z)` of Section 3. -/
private theorem hasDerivAt_LstarNorm (hd : 2 ≤ d) {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    HasDerivAt (LstarNorm d) (hpd (pStar d) d z / z ^ d) z := by
  have hzne : z ≠ 0 := ne_of_gt hz0
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, d = m + 2 := ⟨d - 2, by omega⟩
  have hL : HasDerivAt (Lstar (m + 2)) (Lstar1 (m + 2) z) z := hasDerivAt_Lstar hd hz0 hz1
  have hg : HasDerivAt (fun x : ℝ => x ^ (m + 2 - 1))
      (((m + 2 - 1 : ℕ) : ℝ) * z ^ (m + 2 - 1 - 1)) z := hasDerivAt_pow _ z
  have e := hL.div hg (pow_ne_zero _ hzne)
  have hval : (Lstar1 (m + 2) z * z ^ (m + 2 - 1)
        - Lstar (m + 2) z * (((m + 2 - 1 : ℕ) : ℝ) * z ^ (m + 2 - 1 - 1)))
        / (z ^ (m + 2 - 1)) ^ 2
      = hpd (pStar (m + 2)) (m + 2) z / z ^ (m + 2) := by
    simp only [Lstar1, Lstar, Fkkt, hpd, show m + 2 - 1 = m + 1 from by omega,
      Nat.add_sub_cancel]
    push_cast
    field_simp
    ring
  rw [hval] at e
  exact e

/-- `𝓛_*(r_*)/r_*^{d-1} = 0`: the first contact identity in normalised form. -/
private theorem LstarNorm_rStar (hd : 2 ≤ d) : LstarNorm d (rStar d) = 0 := by
  rw [LstarNorm, Lstar_rStar hd, zero_div]

private theorem LstarNorm_strictMonoOn_Ioc (hd : 2 ≤ d) :
    StrictMonoOn (LstarNorm d) (Set.Ioc 0 (rStar d)) := by
  have hr1 := rStar_lt_one hd
  apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Ioc _ _)
    (fun z hz => (hasDerivAt_LstarNorm hd hz.1
      (lt_of_le_of_lt hz.2 hr1)).continuousAt.continuousWithinAt)
    (f' := fun z => hpd (pStar d) d z / z ^ d)
  · intro z hz
    rw [interior_Ioc] at hz
    exact (hasDerivAt_LstarNorm hd hz.1 (lt_trans hz.2 hr1)).hasDerivWithinAt
  · intro z hz
    rw [interior_Ioc] at hz
    exact div_pos (hpd_pStar_pos hd hz.1 (lt_trans hz.2 hr1) (ne_of_lt hz.2)) (pow_pos hz.1 d)

private theorem LstarNorm_strictMonoOn_Ico (hd : 2 ≤ d) :
    StrictMonoOn (LstarNorm d) (Set.Ico (rStar d) 1) := by
  have hr0 := rStar_pos hd
  apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Ico _ _)
    (fun z hz => (hasDerivAt_LstarNorm hd (lt_of_lt_of_le hr0 hz.1)
      hz.2).continuousAt.continuousWithinAt)
    (f' := fun z => hpd (pStar d) d z / z ^ d)
  · intro z hz
    rw [interior_Ico] at hz
    exact (hasDerivAt_LstarNorm hd (lt_trans hr0 hz.1) hz.2).hasDerivWithinAt
  · intro z hz
    rw [interior_Ico] at hz
    exact div_pos (hpd_pStar_pos hd (lt_trans hr0 hz.1) hz.2 (ne_of_gt hz.1))
      (pow_pos (lt_trans hr0 hz.1) d)

/-! ## The sign of `𝓛_*` -/

/-- `𝓛_* < 0` strictly below the exceptional density. -/
theorem Lstar_neg (hd : 2 ≤ d) {z : ℝ} (hz0 : 0 < z) (hz : z < rStar d) : Lstar d z < 0 := by
  have hzne : z ≠ 0 := ne_of_gt hz0
  have hmono := LstarNorm_strictMonoOn_Ioc hd ⟨hz0, hz.le⟩ ⟨rStar_pos hd, le_refl _⟩ hz
  rw [LstarNorm_rStar hd] at hmono
  have heq : Lstar d z = LstarNorm d z * z ^ (d - 1) := by
    rw [LstarNorm]; field_simp
  rw [heq]
  exact mul_neg_of_neg_of_pos hmono (pow_pos hz0 _)

/-- `𝓛_* > 0` strictly above the exceptional density. -/
theorem Lstar_pos (hd : 2 ≤ d) {z : ℝ} (hz : rStar d < z) (hz1 : z < 1) : 0 < Lstar d z := by
  have hz0 : 0 < z := lt_trans (rStar_pos hd) hz
  have hzne : z ≠ 0 := ne_of_gt hz0
  have hmono := LstarNorm_strictMonoOn_Ico hd ⟨le_refl _, rStar_lt_one hd⟩ ⟨hz.le, hz1⟩ hz
  rw [LstarNorm_rStar hd] at hmono
  have heq : Lstar d z = LstarNorm d z * z ^ (d - 1) := by
    rw [LstarNorm]; field_simp
  rw [heq]
  exact mul_pos hmono (pow_pos hz0 _)

/-! ## The shape of `Γ_d` -/

/-- `Γ_d` is continuous on `[0,1]`: it is `J_{p_*}` minus an affine function of `z^d`. -/
theorem continuousOn_Gam (hd : 2 ≤ d) : ContinuousOn (Gam d) (Set.Icc 0 1) := by
  have h1 : ContinuousOn (Jp (pStar d)) (Set.Icc 0 1) :=
    continuousOn_Jp_Icc (pStar_pos hd) (pStar_lt_one hd)
  have h2 : Continuous fun z : ℝ => betaD d * (z ^ d - rStar d ^ d) :=
    continuous_const.mul ((continuous_pow d).sub continuous_const)
  exact (h1.sub continuousOn_const).sub h2.continuousOn

/-- `Γ_d` is strictly decreasing on `[0, r_*]`, since `Γ_d' = 𝓛_* < 0` there. -/
theorem Gam_strictAntiOn (hd : 2 ≤ d) : StrictAntiOn (Gam d) (Set.Icc 0 (rStar d)) := by
  have hr1 := rStar_lt_one hd
  apply strictAntiOn_of_hasDerivWithinAt_neg (convex_Icc _ _)
    ((continuousOn_Gam hd).mono (Set.Icc_subset_Icc le_rfl hr1.le))
    (f' := fun z => Lstar d z)
  · intro z hz
    rw [interior_Icc] at hz
    exact (hasDerivAt_Gam hd hz.1 (lt_trans hz.2 hr1)).hasDerivWithinAt
  · intro z hz
    rw [interior_Icc] at hz
    exact Lstar_neg hd hz.1 hz.2

/-- `Γ_d` is strictly increasing on `[r_*, 1]`, since `Γ_d' = 𝓛_* > 0` there. -/
theorem Gam_strictMonoOn (hd : 2 ≤ d) : StrictMonoOn (Gam d) (Set.Icc (rStar d) 1) := by
  have hr0 := rStar_pos hd
  apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc _ _)
    ((continuousOn_Gam hd).mono (Set.Icc_subset_Icc hr0.le le_rfl))
    (f' := fun z => Lstar d z)
  · intro z hz
    rw [interior_Icc] at hz
    exact (hasDerivAt_Gam hd (lt_trans hr0 hz.1) hz.2).hasDerivWithinAt
  · intro z hz
    rw [interior_Icc] at hz
    exact Lstar_pos hd hz.1 hz.2

/-! ## `eq:endpoint-gap-positivity` -/

/-- The strict half of `eq:endpoint-gap-positivity`: `Γ_d(z) > 0` for `z ∈ [0,1]`, `z ≠ r_*`.
-/
theorem Gam_pos_of_ne (hd : 2 ≤ d) {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1)
    (hne : z ≠ rStar d) : 0 < Gam d z := by
  have hr0 := rStar_pos hd
  have hr1 := rStar_lt_one hd
  rcases lt_trichotomy z (rStar d) with h | h | h
  · have hlt := Gam_strictAntiOn hd ⟨hz0, h.le⟩ ⟨hr0.le, le_refl _⟩ h
    rw [Gam_rStar hd] at hlt
    exact hlt
  · exact absurd h hne
  · have hlt := Gam_strictMonoOn hd ⟨le_refl _, hr1.le⟩ ⟨h.le, hz1⟩ h
    rw [Gam_rStar hd] at hlt
    exact hlt

/-- `Γ_d ≥ 0` on `[0,1]` `eq:endpoint-gap-positivity`: the supporting function at `r_*`
never exceeds `J_{p_*}`. -/
theorem Gam_nonneg (hd : 2 ≤ d) {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) : 0 ≤ Gam d z := by
  by_cases h : z = rStar d
  · rw [h, Gam_rStar hd]
  · exact (Gam_pos_of_ne hd hz0 hz1 h).le

/-- **`eq:endpoint-gap-positivity`.**  On `[0,1]` the singular endpoint supporting gap vanishes exactly
at the exceptional density `r_*`. -/
theorem Gam_eq_zero_iff (hd : 2 ≤ d) {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    Gam d z = 0 ↔ z = rStar d := by
  constructor
  · intro h
    by_contra hne
    exact absurd h (ne_of_gt (Gam_pos_of_ne hd hz0 hz1 hne))
  · intro h
    rw [h, Gam_rStar hd]

/-! ## The scalar convexity defect `R_d` (see the edge/moment identity) -/

/-- `R_d ≥ 0` on `[0,∞)`: the Jensen gap of `u ↦ u^d` at `r_*` (`pow_convex_gap_ge`). -/
theorem Rd_nonneg (hd : 2 ≤ d) {u : ℝ} (hu0 : 0 ≤ u) : 0 ≤ Rd d u := by
  have hr0 := rStar_pos hd
  have hden : 0 < (d : ℝ) * rStar d ^ (d - 1) := mul_pos (dpos hd) (pow_pos hr0 _)
  have hnum := pow_convex_gap_ge hr0.le hu0 hd
  have hsq : 0 ≤ rStar d ^ (d - 2) * (u - rStar d) ^ 2 := by positivity
  exact div_nonneg (by linarith) hden.le

/-- `R_d(r_*) = 0`: the defect vanishes at the point of tangency. -/
theorem Rd_rStar (hd : 2 ≤ d) : Rd d (rStar d) = 0 := by
  have _hd : 2 ≤ d := hd
  have hzero : rStar d ^ d - rStar d ^ d
      - (d : ℝ) * rStar d ^ (d - 1) * (rStar d - rStar d) = 0 := by ring
  rw [Rd, hzero, zero_div]

/-- `R_d > 0` away from `r_*` (`pow_convex_gap_pos`): `u ↦ u^d` is strictly convex. -/
theorem Rd_pos_of_ne (hd : 2 ≤ d) {u : ℝ} (hu0 : 0 ≤ u) (hne : u ≠ rStar d) : 0 < Rd d u := by
  have hr0 := rStar_pos hd
  have hden : 0 < (d : ℝ) * rStar d ^ (d - 1) := mul_pos (dpos hd) (pow_pos hr0 _)
  exact div_pos (pow_convex_gap_pos hr0 hu0 hne hd) hden

/-- The pointwise form of the edge/moment identity: the deviation of `u` from `r_*` equals the
linearised `d`-th moment deviation minus the convexity defect. -/
theorem sub_rStar_eq (hd : 2 ≤ d) (u : ℝ) :
    u - rStar d = (u ^ d - rStar d ^ d) / ((d : ℝ) * rStar d ^ (d - 1)) - Rd d u := by
  have hr0 := rStar_pos hd
  have hden : ((d : ℝ) * rStar d ^ (d - 1)) ≠ 0 := ne_of_gt (mul_pos (dpos hd) (pow_pos hr0 _))
  rw [Rd]
  field_simp
  ring

end SingularEndpoint

end UpperTailOptimizers
