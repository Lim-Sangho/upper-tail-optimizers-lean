import UpperTailOptimizers.SingularEndpoint.RankOneStationaryFamily.Defs

/-!
# The singular endpoint contact identities (Section 5, `paper/sections/singular.tex`)

At the exceptional density `r_* = (d-1)/d` the two scalar Lubetzky–Zhao contacts of Section 3
coalesce.  This file proves the resulting *triple-contact identities*
`eq:endpoint-entropy-derivatives`,

```
J_{p_*}'(r_*)   = γ_* r_*^{d-1},
J_{p_*}''(r_*)  = γ_* (d-1) r_*^{d-2},
J_{p_*}^{(3)}(r_*) = γ_* (d-1)(d-2) r_*^{d-3},
```

which say exactly that the rank-one KKT function `𝓛_*(z) = J_{p_*}'(z) - γ_* z^{d-1}` of
`eq:kkt-quartic-expansion` vanishes to order at least three at `r_*`.  The order is
*exactly* three: the third derivative of `𝓛_*` at `r_*` equals `d^5/(d-1)^2`, the
non-degeneracy constant behind `eq:endpoint-gap-expansion`.  Since
`Γ_d' = 𝓛_*` (because `β_d d = γ_*`), this is `Γ_d^{(4)}(r_*) = d^5/(d-1)^2`.

## Contents

* `ell_pStar`, `Jp'_pStar_rStar` — the singular endpoint log-odds `ℓ(p_*) = ℓ_*` and the value
  `J_{p_*}'(r_*) = d/(d-1)`;
* `gammaStar_mul_rStar_pow_sub` — `γ_* r_*^{d-k} = r_*^{-k}` for `k ≤ d`, and its `k = 1`
  case `gammaStar_mul_rStar_pow_pred` — `γ_* r_*^{d-1} = d/(d-1)`;
* `cast_sub_one`, `cast_sub_two` — `((d-1 : ℕ) : ℝ) = (d : ℝ) - 1` and its `d - 2` companion
  under `2 ≤ d`, shared with `SingularEndpoint/RankOneStationaryFamily/FamilyBase.lean`, `SingularEndpoint/RankOneStationaryFamily/FamilyDeriv.lean`,
  `SingularEndpoint/RankOneStationaryFamily/FkktDeriv.lean` and `SingularEndpoint/AuxiliaryLagrangian/FirstVariationBound.lean`;
* `triple_contact_one`, `triple_contact_two`, `triple_contact_three` — the three
  identities of `eq:endpoint-entropy-derivatives`;
* `Lstar1`, `Lstar2`, `Lstar3` — the successive derivatives of `𝓛_*`, with their
  `HasDerivAt` chain `hasDerivAt_Lstar`, `hasDerivAt_Lstar1`, `hasDerivAt_Lstar2`;
* `Lstar_rStar`, `Lstar1_rStar`, `Lstar2_rStar` — the vanishing of `𝓛_*` to order three,
  and `Lstar3_rStar : 𝓛_*'''(r_*) = d^5/(d-1)^2`;
* `hasDerivAt_Gam`, `Gam_rStar` — `Γ_d' = 𝓛_*` and `Γ_d(r_*) = 0`.
-/

namespace UpperTailOptimizers

open Real

variable {d : ℕ}

/-! ## Casts of the truncated exponents

The exponents `d - 1`, `d - 2`, `d - 3`, `d - 4` are natural-number subtractions, so their
casts to `ℝ` agree with the real subtractions only above the truncation point. -/

theorem cast_sub_one (hd : 2 ≤ d) : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
  rw [Nat.cast_sub (by omega : 1 ≤ d)]; norm_num

theorem cast_sub_two (hd : 2 ≤ d) : ((d - 2 : ℕ) : ℝ) = (d : ℝ) - 2 := by
  rw [Nat.cast_sub hd]; norm_num

/-! ## The singular endpoint values -/

/-- `ℓ(p_*) = ℓ_* = d/(d-1) - log(d-1)`: the singular endpoint log-odds. -/
theorem ell_pStar (hd : 2 ≤ d) : ell (pStar d) = ellStar d := by
  have h1 : (1 : ℝ) < (d : ℝ) := one_lt_d hd
  have hd1 : ((d : ℝ) - 1) ≠ 0 := by linarith
  have hEpos : (0 : ℝ) < Real.exp ((d : ℝ) / ((d : ℝ) - 1)) := Real.exp_pos _
  have hden : ((d : ℝ) - 1) + Real.exp ((d : ℝ) / ((d : ℝ) - 1)) ≠ 0 :=
    ne_of_gt (by linarith)
  have hstep : (1 - pStar d) / pStar d
      = Real.exp ((d : ℝ) / ((d : ℝ) - 1)) / ((d : ℝ) - 1) := by
    rw [pStar]
    field_simp
    ring
  rw [ell, hstep, Real.log_div (ne_of_gt hEpos) hd1, Real.log_exp, ellStar]

/-- `J_{p_*}'(r_*) = d/(d-1)`: the singular endpoint slope of the relative entropy. -/
theorem Jp'_pStar_rStar (hd : 2 ≤ d) : Jp' (pStar d) (rStar d) = (d : ℝ) / ((d : ℝ) - 1) := by
  rw [Jp'_eq_ell_sub (pStar_pos hd) (pStar_lt_one hd) (rStar_pos hd) (rStar_lt_one hd),
    ell_pStar hd, ell_rStar hd, ellStar]
  ring

/-- `γ_* r_*^{d-k} = r_*^{-k}` for `k ≤ d`: the workhorse behind the contact identities, and
behind the fourth-order coefficient of `SingularEndpoint/ConstantGraphonComparison/Fkkt4.lean`. -/
theorem gammaStar_mul_rStar_pow_sub (hd : 2 ≤ d) {k : ℕ} (hk : k ≤ d) :
    gammaStar d * rStar d ^ (d - k) = 1 / rStar d ^ k := by
  have hr : rStar d ≠ 0 := rStar_ne_zero hd
  have h : gammaStar d * rStar d ^ (d - k) * rStar d ^ k = 1 := by
    rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hk]
    exact gammaStar_mul_rStar_pow hd
  rw [eq_div_iff (pow_ne_zero k hr)]
  exact h

/-- `γ_* r_*^{d-1} = d/(d-1)`, the right-hand side of the first contact identity. -/
theorem gammaStar_mul_rStar_pow_pred (hd : 2 ≤ d) :
    gammaStar d * rStar d ^ (d - 1) = (d : ℝ) / ((d : ℝ) - 1) := by
  have h1 : (1 : ℝ) < (d : ℝ) := one_lt_d hd
  have hd0 : (d : ℝ) ≠ 0 := by linarith
  have hd1 : ((d : ℝ) - 1) ≠ 0 := by linarith
  rw [gammaStar_mul_rStar_pow_sub hd (by omega : 1 ≤ d), rStar_eq]
  field_simp

/-! ## The triple-contact identities `eq:endpoint-entropy-derivatives` -/

/-- First contact identity: `J_{p_*}'(r_*) = γ_* r_*^{d-1}`. -/
theorem triple_contact_one (hd : 2 ≤ d) :
    Jp' (pStar d) (rStar d) = gammaStar d * rStar d ^ (d - 1) := by
  rw [Jp'_pStar_rStar hd, gammaStar_mul_rStar_pow_pred hd]

/-- Second contact identity: `J_{p_*}''(r_*) = γ_* (d-1) r_*^{d-2}`.  Both sides equal
`d²/(d-1)`. -/
theorem triple_contact_two (hd : 2 ≤ d) :
    Jp'' (rStar d) = gammaStar d * ((d : ℝ) - 1) * rStar d ^ (d - 2) := by
  have h1 : (1 : ℝ) < (d : ℝ) := one_lt_d hd
  have hd0 : (d : ℝ) ≠ 0 := by linarith
  have hd1 : ((d : ℝ) - 1) ≠ 0 := by linarith
  have hrhs : gammaStar d * ((d : ℝ) - 1) * rStar d ^ (d - 2)
      = ((d : ℝ) - 1) * (1 / rStar d ^ 2) := by
    rw [← gammaStar_mul_rStar_pow_sub hd hd]; ring
  rw [hrhs, Jp'', one_sub_rStar hd, rStar_eq]
  field_simp

/-- Third contact identity: `J_{p_*}^{(3)}(r_*) = γ_* (d-1)(d-2) r_*^{d-3}`.

At `d = 2` the natural-number exponent `d - 3` truncates to `0`, but the real factor
`(d:ℝ) - 2` vanishes, and `J^{(3)}(1/2) = -4 + 4 = 0`, so the identity still holds. -/
theorem triple_contact_three (hd : 2 ≤ d) :
    Jp3 (rStar d) = gammaStar d * ((d : ℝ) - 1) * ((d : ℝ) - 2) * rStar d ^ (d - 3) := by
  have h1 : (1 : ℝ) < (d : ℝ) := one_lt_d hd
  have hd0 : (d : ℝ) ≠ 0 := by linarith
  have hd1 : ((d : ℝ) - 1) ≠ 0 := by linarith
  rcases eq_or_lt_of_le hd with hd2 | hd3
  · -- `d = 2`: both sides vanish
    have hdeq : (d : ℝ) = 2 := by rw [← hd2]; norm_num
    have hr : rStar d = 1 / 2 := by rw [rStar_eq, hdeq]; norm_num
    rw [hr, Jp3, hdeq]
    norm_num
  · -- `3 ≤ d`
    have hd3' : 3 ≤ d := hd3
    have hrhs : gammaStar d * ((d : ℝ) - 1) * ((d : ℝ) - 2) * rStar d ^ (d - 3)
        = ((d : ℝ) - 1) * ((d : ℝ) - 2) * (1 / rStar d ^ 3) := by
      rw [← gammaStar_mul_rStar_pow_sub hd hd3']; ring
    rw [hrhs, Jp3, one_sub_rStar hd, rStar_eq]
    field_simp
    ring

/-! ## The successive derivatives of `𝓛_*` -/

/-- `𝓛_*'(z) = J_{p_*}''(z) - γ_* (d-1) z^{d-2}`. -/
noncomputable def Lstar1 (d : ℕ) (z : ℝ) : ℝ :=
  Jp'' z - gammaStar d * ((d : ℝ) - 1) * z ^ (d - 2)

/-- `𝓛_*''(z) = J_{p_*}^{(3)}(z) - γ_* (d-1)(d-2) z^{d-3}`. -/
noncomputable def Lstar2 (d : ℕ) (z : ℝ) : ℝ :=
  Jp3 z - gammaStar d * ((d : ℝ) - 1) * ((d : ℝ) - 2) * z ^ (d - 3)

/-- `𝓛_*'''(z) = J_{p_*}^{(4)}(z) - γ_* (d-1)(d-2)(d-3) z^{d-4}`.

The last factor is deliberately the cast of the **natural-number** difference `d - 3`:
differentiating `z ↦ z^{d-3}` produces `((d-3 : ℕ) : ℝ) z^{d-4}`, and at `d = 2` that
coefficient is `0` whereas `(d:ℝ) - 3 = -1`. -/
noncomputable def Lstar3 (d : ℕ) (z : ℝ) : ℝ :=
  Jp4 z - gammaStar d * ((d : ℝ) - 1) * ((d : ℝ) - 2) * ((d - 3 : ℕ) : ℝ) * z ^ (d - 4)

theorem hasDerivAt_Lstar (hd : 2 ≤ d) {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    HasDerivAt (Lstar d) (Lstar1 d z) z := by
  have h1 : HasDerivAt (Jp' (pStar d)) (Jp'' z) z :=
    hasDerivAt_Jp' (pStar_pos hd) (pStar_lt_one hd) hz0 hz1
  have h2 : HasDerivAt (fun x : ℝ => gammaStar d * x ^ (d - 1))
      (gammaStar d * (((d - 1 : ℕ) : ℝ) * z ^ (d - 1 - 1))) z :=
    (hasDerivAt_pow (d - 1) z).const_mul _
  have e := h1.sub h2
  have hval : Jp'' z - gammaStar d * (((d - 1 : ℕ) : ℝ) * z ^ (d - 1 - 1)) = Lstar1 d z := by
    rw [Lstar1, cast_sub_one hd, show d - 1 - 1 = d - 2 from by omega]
    ring
  rw [hval] at e
  exact e

theorem hasDerivAt_Lstar1 (hd : 2 ≤ d) {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    HasDerivAt (Lstar1 d) (Lstar2 d z) z := by
  have h1 : HasDerivAt Jp'' (Jp3 z) z := hasDerivAt_Jp'' hz0 hz1
  have h2 : HasDerivAt (fun x : ℝ => gammaStar d * ((d : ℝ) - 1) * x ^ (d - 2))
      (gammaStar d * ((d : ℝ) - 1) * (((d - 2 : ℕ) : ℝ) * z ^ (d - 2 - 1))) z :=
    (hasDerivAt_pow (d - 2) z).const_mul _
  have e := h1.sub h2
  have hval : Jp3 z - gammaStar d * ((d : ℝ) - 1) * (((d - 2 : ℕ) : ℝ) * z ^ (d - 2 - 1))
      = Lstar2 d z := by
    rw [Lstar2, cast_sub_two hd, show d - 2 - 1 = d - 3 from by omega]
    ring
  rw [hval] at e
  exact e

theorem hasDerivAt_Lstar2 (hd : 2 ≤ d) {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    HasDerivAt (Lstar2 d) (Lstar3 d z) z := by
  have _hd : 2 ≤ d := hd
  have h1 : HasDerivAt Jp3 (Jp4 z) z := hasDerivAt_Jp3 hz0 hz1
  have h2 : HasDerivAt
      (fun x : ℝ => gammaStar d * ((d : ℝ) - 1) * ((d : ℝ) - 2) * x ^ (d - 3))
      (gammaStar d * ((d : ℝ) - 1) * ((d : ℝ) - 2) * (((d - 3 : ℕ) : ℝ) * z ^ (d - 3 - 1))) z :=
    (hasDerivAt_pow (d - 3) z).const_mul _
  have e := h1.sub h2
  have hval :
      Jp4 z - gammaStar d * ((d : ℝ) - 1) * ((d : ℝ) - 2) *
        (((d - 3 : ℕ) : ℝ) * z ^ (d - 3 - 1)) = Lstar3 d z := by
    rw [Lstar3, show d - 3 - 1 = d - 4 from by omega]
    ring
  rw [hval] at e
  exact e

/-! ## Vanishing to order three at `r_*` -/

/-- `𝓛_*(r_*) = 0`: the first contact identity. -/
theorem Lstar_rStar (hd : 2 ≤ d) : Lstar d (rStar d) = 0 := by
  rw [Lstar, Fkkt, triple_contact_one hd, sub_self]

/-- `𝓛_*'(r_*) = 0`: the second contact identity. -/
theorem Lstar1_rStar (hd : 2 ≤ d) : Lstar1 d (rStar d) = 0 := by
  rw [Lstar1, ← triple_contact_two hd, sub_self]

/-- `𝓛_*''(r_*) = 0`: the third contact identity. -/
theorem Lstar2_rStar (hd : 2 ≤ d) : Lstar2 d (rStar d) = 0 := by
  rw [Lstar2, ← triple_contact_three hd, sub_self]

/-- The non-degeneracy `𝓛_*'''(r_*) = d^5/(d-1)^2`, i.e. `Γ_d^{(4)}(r_*) = d^5/(d-1)^2`
(the constant of `eq:endpoint-gap-expansion`). -/
theorem Lstar3_rStar (hd : 2 ≤ d) : Lstar3 d (rStar d) = (d : ℝ) ^ 5 / ((d : ℝ) - 1) ^ 2 := by
  have h1 : (1 : ℝ) < (d : ℝ) := one_lt_d hd
  have hd0 : (d : ℝ) ≠ 0 := by linarith
  have hd1 : ((d : ℝ) - 1) ≠ 0 := by linarith
  rcases eq_or_lt_of_le hd with hd2 | hd3
  · -- `d = 2`: the correction term carries the factor `((2-3 : ℕ) : ℝ) = 0`
    have hdeq : (d : ℝ) = 2 := by rw [← hd2]; norm_num
    have hnat : ((d - 3 : ℕ) : ℝ) = 0 := by
      rw [← hd2]; norm_num
    have hr : rStar d = 1 / 2 := by rw [rStar_eq, hdeq]; norm_num
    rw [Lstar3, hnat, hr, Jp4, hdeq]
    norm_num
  · have hd3' : 3 ≤ d := hd3
    rcases eq_or_lt_of_le hd3' with hd3e | hd4
    · -- `d = 3`: again `((3-3 : ℕ) : ℝ) = 0`
      have hdeq : (d : ℝ) = 3 := by rw [← hd3e]; norm_num
      have hnat : ((d - 3 : ℕ) : ℝ) = 0 := by rw [← hd3e]; norm_num
      have hr : rStar d = 2 / 3 := by rw [rStar_eq, hdeq]; norm_num
      rw [Lstar3, hnat, hr, Jp4, hdeq]
      norm_num
    · -- `4 ≤ d`
      have hd4' : 4 ≤ d := hd4
      have hnat : ((d - 3 : ℕ) : ℝ) = (d : ℝ) - 3 := by
        rw [Nat.cast_sub (by omega : 3 ≤ d)]; norm_num
      have hrhs : gammaStar d * ((d : ℝ) - 1) * ((d : ℝ) - 2) * ((d : ℝ) - 3)
            * rStar d ^ (d - 4)
          = ((d : ℝ) - 1) * ((d : ℝ) - 2) * ((d : ℝ) - 3) * (1 / rStar d ^ 4) := by
        rw [← gammaStar_mul_rStar_pow_sub hd hd4']; ring
      rw [Lstar3, hnat, hrhs, Jp4, one_sub_rStar hd, rStar_eq]
      field_simp
      ring

/-! ## The singular endpoint supporting gap `Γ_d` -/

/-- `Γ_d' = 𝓛_*` on `(0,1)`: differentiating `eq:endpoint-supporting-gap` and using
`β_d d = γ_*`. -/
theorem hasDerivAt_Gam (hd : 2 ≤ d) {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    HasDerivAt (Gam d) (Lstar d z) z := by
  have h1 : HasDerivAt (Jp (pStar d)) (Jp' (pStar d) z) z :=
    hasDerivAt_Jp (pStar_pos hd) (pStar_lt_one hd) hz0 hz1
  have h2 : HasDerivAt (fun x : ℝ => betaD d * (x ^ d - rStar d ^ d))
      (betaD d * ((d : ℝ) * z ^ (d - 1))) z := by
    simpa using ((hasDerivAt_pow d z).sub_const (rStar d ^ d)).const_mul (betaD d)
  have e := (h1.sub_const (Jp (pStar d) (rStar d))).sub h2
  have hval : Jp' (pStar d) z - betaD d * ((d : ℝ) * z ^ (d - 1)) = Lstar d z := by
    rw [Lstar, Fkkt, ← betaD_mul_d hd]
    ring
  rw [hval] at e
  exact e

/-- `Γ_d(r_*) = 0`: the supporting line touches `J_{p_*}` at the exceptional density. -/
theorem Gam_rStar (hd : 2 ≤ d) : Gam d (rStar d) = 0 := by
  have _hd : 2 ≤ d := hd
  rw [Gam, sub_self, sub_self, mul_zero, sub_zero]

end UpperTailOptimizers
