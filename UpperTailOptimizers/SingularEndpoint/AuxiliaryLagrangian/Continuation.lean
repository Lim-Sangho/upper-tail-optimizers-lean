import UpperTailOptimizers.SingularEndpoint.LocalizationRankOne.Quartic

/-!
# The continuation of the singular endpoint gap to `[0,4]` (Section 5, `paper/sections/singular.tex`)

The one-dimensional law problem of `sec:auxiliary-lagrangian` is formulated
for probability measures supported on the fixed interval `[0,2]` of rank-one factor values,
so the products `x y` that enter the double integral range over `[0,4]`.  The entropy
density `J_{p_*}` — and with it the singular endpoint supporting gap
`Γ_d(z) = J_{p_*}(z) - J_{p_*}(r_*) - β_d (z^d - r_*^d)` — has a graphon meaning only for
`0 ≤ z ≤ 1`.  The paper therefore replaces `Γ_d` by the real continuation

```
Γ̃_d(z) = Γ_d(z)              for 0 ≤ z ≤ 1,
Γ̃_d(z) = Γ_d(1) + (z-1)^2    for 1 < z ≤ 4,
```

which is exactly what enters `eq:entropy-continuation`,

```
J̃_{p_*}(z) := J_{p_*}(r_*) + β_d (z^d - r_*^d) + Γ̃_d(z),   0 ≤ z ≤ 4.
```

The continuation is *not* an extension of `J_{p_*}` itself; it is chosen so that the two
properties of `Γ_d` that the law argument actually uses survive on all of `[0,4]`: the
gap still vanishes only at the exceptional density `r_*`, and it still dominates the fourth
power of the distance to `r_*`.  Both are proved here.  Above `1` the quadratic bump is
harmless because it is bounded below by `Γ_d(1) > 0`, so the whole of `(1,4]` sits at a
definite distance from the zero set.

## Contents

* `GamTilde` — the continuation `Γ̃_d` of the display preceding
  `eq:entropy-continuation`, together with its two defining equations
  `GamTilde_of_le_one` and `GamTilde_of_one_lt`;
* `GamTilde_nonneg`, `GamTilde_pos_of_ne`, `GamTilde_eq_zero_iff` — the continuation of
  `eq:endpoint-gap-positivity` to `[0,4]`;
* `GamTilde_one` — the two familyes agree at `1`;
* `continuousOn_GamTilde` — `Γ̃_d` is continuous on `[0,4]`;
* `exists_quartic_le_GamTilde` — the continuation of
  `eq:endpoint-gap-quartic-bound`: `|z - r_*|^4 ≤ C Γ̃_d(z)` on `[0,4]`.
-/

namespace UpperTailOptimizers

namespace SingularEndpoint

open Real

variable {d : ℕ}

/-! ## The continuation `Γ̃_d` -/

/-- The continuation `Γ̃_d` of the singular endpoint supporting gap from `[0,1]` to `[0,4]`, as in the
display preceding `eq:entropy-continuation`: it agrees with `Γ_d` on `[0,1]` and is
continued by the quadratic bump `Γ_d(1) + (u-1)^2` above `1`. -/
noncomputable def GamTilde (d : ℕ) (z : ℝ) : ℝ :=
  if z ≤ 1 then Gam d z else Gam d 1 + (z - 1) ^ 2

/-- The lower family of `Γ̃_d` `eq:entropy-continuation`: below `1` the continuation is
the genuine singular endpoint gap `Γ_d`. -/
theorem GamTilde_of_le_one {z : ℝ} (hz : z ≤ 1) : GamTilde d z = Gam d z := by
  rw [GamTilde, if_pos hz]

/-- The upper family of `Γ̃_d` `eq:entropy-continuation`: above `1` the continuation is
the quadratic bump `Γ_d(1) + (z-1)^2`. -/
theorem GamTilde_of_one_lt {z : ℝ} (hz : 1 < z) : GamTilde d z = Gam d 1 + (z - 1) ^ 2 := by
  rw [GamTilde, if_neg (not_le.mpr hz)]

/-- The value of `Γ̃_d` at the matching point `z = 1`: both familyes give `Γ_d(1)`. -/
theorem GamTilde_one : GamTilde d 1 = Gam d 1 := GamTilde_of_le_one le_rfl

/-! ## Positivity of the continuation -/

/-- `Γ_d(1) > 0`: the right endpoint of `[0,1]` is not the exceptional density, since
`r_* < 1`.  This is what keeps the upper family of `Γ̃_d` away from zero. -/
private theorem Gam_one_pos (hd : 2 ≤ d) : 0 < Gam d 1 :=
  Gam_pos_of_ne hd zero_le_one le_rfl (rStar_lt_one hd).ne'

/-- `Γ̃_d ≥ 0` on `[0,4]`: on `[0,1]` this is `eq:endpoint-gap-positivity`, and above `1` the
continuation is `Γ_d(1) ≥ 0` plus a square. -/
theorem GamTilde_nonneg (hd : 2 ≤ d) {z : ℝ} (hz0 : 0 ≤ z) : 0 ≤ GamTilde d z := by
  rcases le_or_gt z 1 with hz | hz
  · rw [GamTilde_of_le_one hz]
    exact Gam_nonneg hd hz0 hz
  · rw [GamTilde_of_one_lt hz]
    have h1 : 0 ≤ Gam d 1 := (Gam_one_pos hd).le
    positivity

/-- The strict half of the continued `eq:endpoint-gap-positivity`: `Γ̃_d(z) > 0` for `z ≥ 0`
with `z ≠ r_*`.  Below `1` this is `Gam_pos_of_ne`; above `1` the value is at least
`Γ_d(1) > 0`. -/
theorem GamTilde_pos_of_ne (hd : 2 ≤ d) {z : ℝ} (hz0 : 0 ≤ z) (hne : z ≠ rStar d) :
    0 < GamTilde d z := by
  rcases le_or_gt z 1 with hz | hz
  · rw [GamTilde_of_le_one hz]
    exact Gam_pos_of_ne hd hz0 hz hne
  · rw [GamTilde_of_one_lt hz]
    have h1 := Gam_one_pos hd
    have h2 : (0 : ℝ) ≤ (z - 1) ^ 2 := sq_nonneg _
    linarith

/-- **The continuation of `eq:endpoint-gap-positivity`.**  On `[0,∞)` — in particular on the
interval `[0,4]` of `eq:entropy-continuation` — the continued gap vanishes exactly at the
exceptional density `r_*`. -/
theorem GamTilde_eq_zero_iff (hd : 2 ≤ d) {z : ℝ} (hz0 : 0 ≤ z) :
    GamTilde d z = 0 ↔ z = rStar d := by
  constructor
  · intro h
    by_contra hne
    exact absurd h (ne_of_gt (GamTilde_pos_of_ne hd hz0 hne))
  · intro h
    have hz1 : z ≤ 1 := by
      rw [h]; exact (rStar_lt_one hd).le
    rw [GamTilde_of_le_one hz1, h, Gam_rStar hd]

/-! ## Continuity on `[0,4]` -/

/-- `Γ̃_d` is continuous on `[0,4]`, as asserted after `eq:entropy-continuation`.  The two
familyes are continuous on the closed pieces `[0,1]` and `[1,4]` and agree at the matching
point `z = 1`, so `ContinuousOn.union_of_isClosed` applies. -/
theorem continuousOn_GamTilde (hd : 2 ≤ d) : ContinuousOn (GamTilde d) (Set.Icc 0 4) := by
  have hlow : ContinuousOn (GamTilde d) (Set.Icc (0 : ℝ) 1) :=
    (continuousOn_Gam hd).congr (fun z hz => GamTilde_of_le_one hz.2)
  have hhigh : ContinuousOn (GamTilde d) (Set.Icc (1 : ℝ) 4) := by
    have hcont : ContinuousOn (fun z : ℝ => Gam d 1 + (z - 1) ^ 2) (Set.Icc (1 : ℝ) 4) :=
      (continuousOn_const.add (((continuousOn_id).sub continuousOn_const).pow 2))
    refine hcont.congr ?_
    intro z hz
    rcases eq_or_lt_of_le hz.1 with h | h
    · rw [← h, GamTilde_one]
      norm_num
    · rw [GamTilde_of_one_lt h]
  have hunion : Set.Icc (0 : ℝ) 1 ∪ Set.Icc (1 : ℝ) 4 = Set.Icc (0 : ℝ) 4 :=
    Set.Icc_union_Icc_eq_Icc (by norm_num) (by norm_num)
  have := hlow.union_of_isClosed hhigh isClosed_Icc isClosed_Icc
  rwa [hunion] at this

/-! ## The quartic bound on `[0,4]` -/

/-- **The continuation of `eq:endpoint-gap-quartic-bound`.**  There is `C < ∞` with
`|z - r_*|^4 ≤ C Γ̃_d(z)` for `0 ≤ z ≤ 4`.

On `[0,1]` this is `exists_gam_quartic_lower` inverted, with `C ≥ 1/c_d`.  On `(1,4]` the
continued gap is bounded below by `Γ_d(1) > 0` while `|z - r_*| ≤ 4`, so `C ≥ 256/Γ_d(1)`
suffices; the constant is the maximum of the two. -/
theorem exists_quartic_le_GamTilde (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ z ∈ Set.Icc (0 : ℝ) 4, |z - rStar d| ^ 4 ≤ C * GamTilde d z := by
  obtain ⟨c, hc, hcbound⟩ := exists_gam_quartic_lower hd
  have hG1 : 0 < Gam d 1 := Gam_one_pos hd
  have hr0 := rStar_pos hd
  have hr1 := rStar_lt_one hd
  have hcinv : 0 < 1 / c := by positivity
  refine ⟨max (1 / c) (256 / Gam d 1), lt_of_lt_of_le hcinv (le_max_left _ _), ?_⟩
  intro z hz
  rcases le_or_gt z 1 with hz1 | hz1
  · -- lower family: invert the quartic bound of `eq:endpoint-gap-quartic-bound`
    have hkey := hcbound z ⟨hz.1, hz1⟩
    rw [GamTilde_of_le_one hz1]
    have hstep : |z - rStar d| ^ 4 ≤ 1 / c * Gam d z := by
      rw [one_div, inv_mul_eq_div, le_div_iff₀ hc, mul_comm]
      exact hkey
    refine le_trans hstep ?_
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Gam_nonneg hd hz.1 hz1)
  · -- upper family: the gap is at least `Γ_d(1) > 0` while the distance is at most `4`
    rw [GamTilde_of_one_lt hz1]
    have habs : |z - rStar d| ≤ 4 := by
      rw [abs_le]
      constructor <;> [linarith; linarith [hz.2]]
    have h256 : |z - rStar d| ^ 4 ≤ 256 := by
      calc |z - rStar d| ^ 4 ≤ (4 : ℝ) ^ 4 := pow_le_pow_left₀ (abs_nonneg _) habs 4
        _ = 256 := by norm_num
    have hlow : 256 / Gam d 1 * Gam d 1
        ≤ max (1 / c) (256 / Gam d 1) * (Gam d 1 + (z - 1) ^ 2) := by
      refine mul_le_mul (le_max_right _ _) (by nlinarith [sq_nonneg (z - 1)]) hG1.le ?_
      exact le_trans (by positivity) (le_max_right _ _)
    have hcancel : 256 / Gam d 1 * Gam d 1 = 256 := div_mul_cancel₀ _ hG1.ne'
    linarith
