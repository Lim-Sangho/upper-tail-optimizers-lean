import UpperTailOptimizers.SingularEndpoint.RankOneStationaryFamily.FkktDeriv

/-!
# The fourth derivative of the rank-one KKT function (Section 5, `paper/sections/singular.tex`)

`SingularEndpoint/RankOneStationaryFamily/Contact.lean` differentiates the KKT function
`𝓛_*(z) = J_{p_*}'(z) - γ_* z^{d-1}` three times and records the non-degeneracy
`𝓛_*'''(r_*) = d⁵/(d-1)²`; `SingularEndpoint/RankOneStationaryFamily/FkktDeriv.lean` does the same for a general multiplier
`γ`.  Those three derivatives pin the `h⁴` order of the increments
`A_h = 𝓜_h(s_h²) - 𝓜_h(s_h t_h)` and `B_h = 𝓜_h(t_h²) - 𝓜_h(s_h t_h)` (Lean names for the two
differences in `eq:block-proportion-formula`), because a three-node Lagrange remainder evaluated
at an unknown intermediate point is only good to leading order.

The `h⁵` order needs one derivative more: the quotient `R` in the paper's factorisation
`eq:mh-derivative-factorization`, `𝓜_h'(z) = (z - s_h²)(z - s_h t_h)(z - t_h²)R(h,z)` (where
`𝓜_h' = 𝓛_h`), has `R(0,r_*) = 𝓛_*'''(r_*)/6` and `∂_zR(0,r_*) = 𝓛_*^{(4)}(r_*)/24` (the
paper's constants `k_3` and `k_4`), and it is the ratio of these two that produces the
coefficient `a_1 = α'(0) = 2d²u_*/(3(d-1))` of the block weight.  This file supplies the
missing derivative, in the style of `SingularEndpoint/RankOneStationaryFamily/FkktDeriv.lean`, and evaluates it at `r_*`:

```
𝓛_*^{(4)}(r_*) = 5 d⁶ (d-2) / (d-1)³.
```

Note that this vanishes at `d = 2`, where `r_* = 1/2` is the symmetry point of `J_p''` and
the whole picture degenerates; `d ≥ 3` is where it is a genuine non-degeneracy statement.

## Contents

* `Fkkt4` — the fourth `z`-derivative of `F_{p,γ}`, with `hasDerivAt_Fkkt3` closing the
  chain begun in `SingularEndpoint/RankOneStationaryFamily/FkktDeriv.lean`;
* `Lstar4`, `hasDerivAt_Lstar3` — the same at the singular endpoint parameters, continuing the chain
  of `SingularEndpoint/RankOneStationaryFamily/Contact.lean`.  `Lstar4 d = Fkkt4 d (gammaStar d)` holds definitionally, so no
  transfer lemma is needed;
* `Lstar4_rStar` — the closed form `5 d⁶(d-2)/(d-1)³`.
-/

namespace UpperTailOptimizers

variable {d : ℕ}

/-! ## The derivative -/

/-- `F_{p,γ}^{(4)}(z) = J_p^{(5)}(z) - γ(d-1)(d-2)(d-3)(d-4)z^{d-5}`.  Independent of `p`.

**Which factors are casts of natural-number differences.**  Differentiating the power in
`Fkkt3 d γ z = J_p^{(4)}(z) - γ(d-1)(d-2)·((d-3 : ℕ) : ℝ)·z^{d-4}` means applying
`(hasDerivAt_pow (d - 4) z).const_mul _`, whose derivative value is literally
`γ ((d:ℝ)-1) ((d:ℝ)-2) ((d-3 : ℕ) : ℝ) * (((d-4 : ℕ) : ℝ) * z ^ (d - 4 - 1))`: the exponent
that comes down is the *cast of the natural-number* exponent `d - 4`, and the surviving
exponent is `d - 4 - 1 = d - 5`, again a natural-number difference.

So the two trailing factors `((d-3 : ℕ) : ℝ)` and `((d-4 : ℕ) : ℝ)` must stay Nat casts:
natural subtraction truncates at `0`, and that truncation is exactly right.  At `d = 2` the
real number `(d:ℝ) - 3 = -1` is nonzero while `z ↦ z^{d-3} = z^0` is constant, so only the
Nat cast `((2-3 : ℕ) : ℝ) = 0` records the correct derivative; likewise `((d-4 : ℕ) : ℝ)`
vanishes at `d = 2, 3, 4` where `(d:ℝ) - 4` does not.

The two leading factors `(d:ℝ) - 1` and `(d:ℝ) - 2` may be honest real subtractions,
because `hd : 2 ≤ d` makes `((d-1 : ℕ) : ℝ) = (d:ℝ) - 1` and `((d-2 : ℕ) : ℝ) = (d:ℝ) - 2`
(this is what `cast_sub_one` and `cast_sub_two` are for), i.e. no truncation has happened
yet at those two steps. -/
noncomputable def Fkkt4 (d : ℕ) (γ z : ℝ) : ℝ :=
  Jp5 z - γ * ((d : ℝ) - 1) * ((d : ℝ) - 2) * ((d - 3 : ℕ) : ℝ) * ((d - 4 : ℕ) : ℝ)
    * z ^ (d - 5)

/-- The fourth derivative of `F_{p,γ}`, closing the chain
`hasDerivAt_Fkkt'`, `hasDerivAt_Fkkt1`, `hasDerivAt_Fkkt2` of `SingularEndpoint/RankOneStationaryFamily/FkktDeriv.lean`.

The degree bound is carried for uniformity with the rest of the chain but is not used: the
natural-subtraction bookkeeping `d - 4 - 1 = d - 5` holds for every `d`, and the two
truncating cast factors already encode the small-`d` degeneracies. -/
theorem hasDerivAt_Fkkt3 (_hd : 2 ≤ d) {γ z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    HasDerivAt (Fkkt3 d γ) (Fkkt4 d γ z) z := by
  have h1 : HasDerivAt Jp4 (Jp5 z) z := hasDerivAt_Jp4 hz0 hz1
  have h2 : HasDerivAt
      (fun x : ℝ => γ * ((d : ℝ) - 1) * ((d : ℝ) - 2) * ((d - 3 : ℕ) : ℝ) * x ^ (d - 4))
      (γ * ((d : ℝ) - 1) * ((d : ℝ) - 2) * ((d - 3 : ℕ) : ℝ) *
        (((d - 4 : ℕ) : ℝ) * z ^ (d - 4 - 1))) z :=
    (hasDerivAt_pow (d - 4) z).const_mul _
  have e := h1.sub h2
  have hval :
      Jp5 z - γ * ((d : ℝ) - 1) * ((d : ℝ) - 2) * ((d - 3 : ℕ) : ℝ) *
        (((d - 4 : ℕ) : ℝ) * z ^ (d - 4 - 1)) = Fkkt4 d γ z := by
    rw [Fkkt4, show d - 4 - 1 = d - 5 from by omega]
    ring
  rw [hval] at e
  exact e

/-! ## The fourth derivative at the singular endpoint -/

/-- `𝓛_*^{(4)}(z) = J_{p_*}^{(5)}(z) - γ_*(d-1)(d-2)(d-3)(d-4)z^{d-5}`: the specialisation
of `Fkkt4` at `γ = γ_*`, continuing `Lstar1`, `Lstar2`, `Lstar3` of
`SingularEndpoint/RankOneStationaryFamily/Contact.lean`.  The two trailing factors are Nat casts for the reason explained
at `Fkkt4`. -/
noncomputable def Lstar4 (d : ℕ) (z : ℝ) : ℝ := Fkkt4 d (gammaStar d) z

/-- The fourth derivative of `𝓛_*`, closing the chain `hasDerivAt_Lstar`,
`hasDerivAt_Lstar1`, `hasDerivAt_Lstar2` of `SingularEndpoint/RankOneStationaryFamily/Contact.lean`. -/
theorem hasDerivAt_Lstar3 (hd : 2 ≤ d) {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    HasDerivAt (Lstar3 d) (Lstar4 d z) z := by
  -- `Lstar3 d = Fkkt3 d (gammaStar d)` and `Lstar4 d = Fkkt4 d (gammaStar d)` hold
  -- definitionally, so no rewriting is needed.
  exact hasDerivAt_Fkkt3 (γ := gammaStar d) hd hz0 hz1

/-! ## The value at `r_*` -/

/-- **The fourth-order singular endpoint coefficient** `𝓛_*^{(4)}(r_*) = 5 d⁶(d-2)/(d-1)³`, i.e.
`Γ_d^{(5)}(r_*) = 5 d⁶(d-2)/(d-1)³`.

Together with `Lstar3_rStar : 𝓛_*'''(r_*) = d⁵/(d-1)²` this is what fixes the `h⁵`
coefficients of the increments at the contacts `A_h` and `B_h`, hence the block-weight slope
`a_1 = α'(0)`.

The proof splits off `d = 2, 3, 4`, where a Nat-cast factor truncates to `0` and the
correction term disappears, from `d ≥ 5`, where all four falling-factorial factors are
genuine and `γ_* r_*^{d-5} = r_*^{-5}` normalises the correction.  At `d = 2` the value
is `0`: there `r_* = 1/2` and `J_p^{(5)}` is odd about `1/2`. -/
theorem Lstar4_rStar (hd : 2 ≤ d) :
    Lstar4 d (rStar d) = 5 * (d : ℝ) ^ 6 * ((d : ℝ) - 2) / ((d : ℝ) - 1) ^ 3 := by
  have h1 : (1 : ℝ) < (d : ℝ) := one_lt_d hd
  have hd0 : (d : ℝ) ≠ 0 := by linarith
  have hd1 : ((d : ℝ) - 1) ≠ 0 := by linarith
  rcases eq_or_lt_of_le hd with hd2 | hd3
  · -- `d = 2`: the factor `((2-3 : ℕ) : ℝ)` is `0`, and `J_p^{(5)}(1/2) = 0`
    have hdeq : (d : ℝ) = 2 := by rw [← hd2]; norm_num
    have hnat : ((d - 3 : ℕ) : ℝ) = 0 := by rw [← hd2]; norm_num
    have hr : rStar d = 1 / 2 := by rw [rStar_eq, hdeq]; norm_num
    rw [Lstar4, Fkkt4, hnat, hr, Jp5, hdeq]
    norm_num
  · have hd3' : 3 ≤ d := hd3
    rcases eq_or_lt_of_le hd3' with hd3e | hd4
    · -- `d = 3`: again `((3-3 : ℕ) : ℝ) = 0`
      have hdeq : (d : ℝ) = 3 := by rw [← hd3e]; norm_num
      have hnat : ((d - 3 : ℕ) : ℝ) = 0 := by rw [← hd3e]; norm_num
      have hr : rStar d = 2 / 3 := by rw [rStar_eq, hdeq]; norm_num
      rw [Lstar4, Fkkt4, hnat, hr, Jp5, hdeq]
      norm_num
    · have hd4' : 4 ≤ d := hd4
      rcases eq_or_lt_of_le hd4' with hd4e | hd5
      · -- `d = 4`: now it is `((4-4 : ℕ) : ℝ)` that vanishes
        have hdeq : (d : ℝ) = 4 := by rw [← hd4e]; norm_num
        have hnat : ((d - 4 : ℕ) : ℝ) = 0 := by rw [← hd4e]; norm_num
        have hr : rStar d = 3 / 4 := by rw [rStar_eq, hdeq]; norm_num
        rw [Lstar4, Fkkt4, hnat, hr, Jp5, hdeq]
        norm_num
      · -- `5 ≤ d`: all four factors are genuine
        have hd5' : 5 ≤ d := hd5
        have hnat3 : ((d - 3 : ℕ) : ℝ) = (d : ℝ) - 3 := by
          rw [Nat.cast_sub (by omega : 3 ≤ d)]; norm_num
        have hnat4 : ((d - 4 : ℕ) : ℝ) = (d : ℝ) - 4 := by
          rw [Nat.cast_sub (by omega : 4 ≤ d)]; norm_num
        have hrhs : gammaStar d * ((d : ℝ) - 1) * ((d : ℝ) - 2) * ((d : ℝ) - 3)
              * ((d : ℝ) - 4) * rStar d ^ (d - 5)
            = ((d : ℝ) - 1) * ((d : ℝ) - 2) * ((d : ℝ) - 3) * ((d : ℝ) - 4)
              * (1 / rStar d ^ 5) := by
          rw [← gammaStar_mul_rStar_pow_sub hd hd5']; ring
        rw [Lstar4, Fkkt4, hnat3, hnat4, hrhs, Jp5, one_sub_rStar hd, rStar_eq]
        field_simp
        ring

/-! ## Continuity -/

end UpperTailOptimizers
