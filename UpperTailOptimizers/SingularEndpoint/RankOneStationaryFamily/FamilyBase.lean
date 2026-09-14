import UpperTailOptimizers.SingularEndpoint.RankOneStationaryFamily.FamilySystem
import UpperTailOptimizers.SingularEndpoint.RankOneStationaryFamily.Contact

/-!
# The base point of the family system (Section 5, `paper/sections/singular.tex`)

`SingularEndpoint/RankOneStationaryFamily/FamilySystem.lean` replaces the degenerate rank-one KKT system
`eq:three-value-kkt` of `lem:rank-one-kkt-family` by the desingularized
system `(E₁, E₂, E₃)`, in which the two exact divisions by `h` and `h²` have already been
carried out.  **This file evaluates that system at the base point**

  `(u, ℓ, γ, h) = (u_*, ℓ_*, γ_*, 0)`

and shows that all three components vanish.  That is the hypothesis `F(z₀, 0) = 0` of the
analytic implicit function theorem which constructs the family of
`lem:rank-one-kkt-family`.

The point of the reformulation is that the vanishing reduces *exactly* to the three
contact identities `eq:endpoint-entropy-derivatives` already proved in
`SingularEndpoint/RankOneStationaryFamily/Contact.lean`.  Indeed, at `h = 0` the values recorded by `Esys2_zero`,
`Esys3_zero` are `4u·𝓛′(u²)` and `4𝓛′(u²) + 4u²·𝓛″(u²)`, so with `u = u_*` and
`u_*² = r_*` the three components become

  `E₁ = 𝓛_*(r_*)`,   `E₂ = 4u_*·𝓛_*′(r_*)`,   `E₃ = 4𝓛_*′(r_*) + 4r_*·𝓛_*″(r_*)`,

which are `Lstar_rStar`, `Lstar1_rStar` and `Lstar2_rStar`.  The two "bridges" below are the
algebraic identifications of the closed forms of `Esys2_zero`, `Esys3_zero` with those
combinations; both are elementary, the only delicate point being the truncated
natural-number exponents `d - 2`, `d - 3`, which force a case split at `d = 2`.

## Contents

* `Fsys`, `zBase` — the desingularized system of `lem:rank-one-kkt-family` packaged
  as a map `ℝ × ℝ × ℝ → ℝ → ℝ × ℝ × ℝ` in the coordinates `(u, ℓ, γ)` of the Jacobian, and
  its base point `(u_*, ℓ_*, γ_*)`;
* `Esys1_base` — `E₁(u_*, ℓ_*, γ_*, 0) = 0`, i.e. the first contact identity;
* `Esys2_base` — `E₂(u_*, γ_*, 0) = 0`, i.e. the second contact identity;
* `Esys3_base` — `E₃(u_*, γ_*, 0) = 0`, i.e. the second and third contact identities;
* `Fsys_base` — the three together, the hypothesis `hF0` of the implicit function theorem.
-/

namespace UpperTailOptimizers

namespace SingularEndpoint

open Real

variable {d : ℕ}

/-! ## The packaged system and its base point -/

/-- The desingularized system of `lem:rank-one-kkt-family` packaged as a single
map, with the unknowns collected in the order `(u, ℓ, γ)` used by the Jacobian `jac3`:

  `Fsys d (u, ℓ, γ) h = (E₁, E₂, E₃)`.

This is the map to which the analytic implicit function theorem is applied, with `h` the
parameter and `(u, ℓ, γ)` the unknown. -/
noncomputable def Fsys (d : ℕ) (z : ℝ × ℝ × ℝ) (h : ℝ) : ℝ × ℝ × ℝ :=
  (Esys1 d z.2.1 z.2.2 z.1 h, Esys2 d z.2.2 z.1 h, Esys3 d z.2.2 z.1 h)

/-- The base point `(u_*, ℓ_*, γ_*)` of `lem:rank-one-kkt-family`, at which the
family is anchored: the coalescing factor value, the singular endpoint log-odds and the singular endpoint
scalar multiplier. -/
noncomputable def zBase (d : ℕ) : ℝ × ℝ × ℝ := (uStar d, ellStar d, gammaStar d)

/-! ## The three components at the base point

The exponents `d - 1`, `d - 2` are natural-number subtractions; their casts to `ℝ` agree
with the real subtractions only above the truncation point, which is what `cast_sub_one` and
`cast_sub_two` of `SingularEndpoint/RankOneStationaryFamily/Contact.lean` record. -/

/-- **First component at the base point**: `E₁(u_*, ℓ_*, γ_*, 0) = 0`.

At `h = 0` the middle root `s_h t_h` of `eq:three-value-kkt` is `u_*² = r_*`, so
`E₁` is the value `𝓛_*(r_*)`, which vanishes by the first contact identity
`eq:endpoint-entropy-derivatives`. -/
theorem Esys1_base (hd : 2 ≤ d) : Esys1 d (ellStar d) (gammaStar d) (uStar d) 0 = 0 := by
  have harg : (uStar d - 0) * (uStar d + 0) = rStar d := by
    rw [sub_zero, add_zero, ← uStar_sq hd]; ring
  have hL : Lstar d (rStar d) = 0 := Lstar_rStar hd
  rw [Lstar] at hL
  rw [Esys1, harg, ← ell_pStar hd,
    Lell_eq_Fkkt (pStar_pos hd) (pStar_lt_one hd) (rStar_pos hd) (rStar_lt_one hd)]
  exact hL

/-- **Second component at the base point**: `E₂(u_*, γ_*, 0) = 0`.

By `Esys2_zero` the value is `4u/(1-u²) + 4/u - 4γu(d-1)(u²)^{d-2}`, and the scalar identity
`4u/(1-u²) + 4/u = 4u/(u²(1-u²))` turns it into `4u·𝓛_*′(u²)`.  At `u = u_*` this is
`4u_*·𝓛_*′(r_*) = 0` by the second contact identity
`eq:endpoint-entropy-derivatives`. -/
theorem Esys2_base (hd : 2 ≤ d) : Esys2 d (gammaStar d) (uStar d) 0 = 0 := by
  set u : ℝ := uStar d with hu
  have hu0 : 0 < u := uStar_pos hd
  have hune : u ≠ 0 := ne_of_gt hu0
  have husq : u ^ 2 = rStar d := uStar_sq hd
  have hu1 : u ^ 2 < 1 := by rw [husq]; exact rStar_lt_one hd
  have hden : (1 : ℝ) - u ^ 2 ≠ 0 := by linarith
  have bridge : 4 * u / (1 - u ^ 2) + 4 / u
        - 4 * gammaStar d * u * (((d - 1 : ℕ) : ℝ) * (u ^ 2) ^ (d - 2))
      = 4 * u * Lstar1 d (u ^ 2) := by
    rw [Lstar1, Jp'', cast_sub_one hd]
    field_simp
    ring
  rw [Esys2_zero hd hu0 hu1, bridge, husq, Lstar1_rStar hd, mul_zero]

/-- **Third component at the base point**: `E₃(u_*, γ_*, 0) = 0`.

By `Esys3_zero` the value is
`4/(1-u²)² - 4γ((d-1)(u²)^{d-2} + u·(d-1)u^{d-2}·(d-2)u^{d-3})`, and the scalar identity
`4/(1-w)² = 4(1/w + 1/(1-w)) + 4w(-(1/w²) + 1/(1-w)²)` at `w = u²` turns it into
`4𝓛_*′(u²) + 4u²·𝓛_*″(u²)`.  At `u = u_*` this vanishes by the second and third contact
identities `eq:endpoint-entropy-derivatives`.

The exponent bookkeeping needs a case split: for `3 ≤ d` one has
`u·u^{d-2}·u^{d-3} = u²·(u²)^{d-3}`, while at `d = 2` both `((d-2 : ℕ) : ℝ)` and `(d:ℝ) - 2`
vanish and the two offending terms disappear. -/
theorem Esys3_base (hd : 2 ≤ d) : Esys3 d (gammaStar d) (uStar d) 0 = 0 := by
  set u : ℝ := uStar d with hu
  have hu0 : 0 < u := uStar_pos hd
  have hune : u ≠ 0 := ne_of_gt hu0
  have husq : u ^ 2 = rStar d := uStar_sq hd
  have hu1 : u ^ 2 < 1 := by rw [husq]; exact rStar_lt_one hd
  have hden : (1 : ℝ) - u ^ 2 ≠ 0 := by linarith
  -- the truncated-exponent identity behind the mixed term
  have hpow : u * (((d - 1 : ℕ) : ℝ) * u ^ (d - 2)) * (((d - 2 : ℕ) : ℝ) * u ^ (d - 3))
      = u ^ 2 * (((d : ℝ) - 1) * ((d : ℝ) - 2) * (u ^ 2) ^ (d - 3)) := by
    rcases eq_or_lt_of_le hd with hd2 | hd3
    · -- `d = 2`: both `((d-2 : ℕ) : ℝ)` and `(d:ℝ) - 2` vanish
      rw [← hd2]
      norm_num
    · have hd3' : 3 ≤ d := hd3
      have e1 : u ^ (d - 2) * u ^ (d - 3) = (u ^ 2) ^ (d - 3) * u := by
        rw [← pow_add, ← pow_mul, ← pow_succ]
        congr 1
        omega
      rw [cast_sub_one hd, cast_sub_two hd]
      linear_combination ((d : ℝ) - 1) * ((d : ℝ) - 2) * u * e1
  have bridge : 4 / (1 - u ^ 2) ^ 2
        - 4 * gammaStar d * (((d - 1 : ℕ) : ℝ) * (u ^ 2) ^ (d - 2)
            + u * (((d - 1 : ℕ) : ℝ) * u ^ (d - 2)) * (((d - 2 : ℕ) : ℝ) * u ^ (d - 3)))
      = 4 * Lstar1 d (u ^ 2) + 4 * u ^ 2 * Lstar2 d (u ^ 2) := by
    rw [hpow, cast_sub_one hd, Lstar1, Lstar2, Jp'', Jp3]
    have hsq : (u : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 hune
    field_simp
    ring
  rw [Esys3_zero hd hu0 hu1, bridge, husq, Lstar1_rStar hd, Lstar2_rStar hd]
  ring

/-! ## The base point of the implicit function theorem -/

/-- **The desingularized system vanishes at the base point**:

  `Fsys d (u_*, ℓ_*, γ_*) 0 = 0`.

This is the hypothesis `F(z₀, 0) = 0` of the analytic implicit function theorem that
constructs the coalescing family of `lem:rank-one-kkt-family`; by
`Esys1_base`–`Esys3_base` it is exactly the triple-contact system
`eq:endpoint-entropy-derivatives`. -/
theorem Fsys_base (hd : 2 ≤ d) : Fsys d (zBase d) 0 = 0 := by
  have hsplit : Fsys d (zBase d) 0
      = (Esys1 d (ellStar d) (gammaStar d) (uStar d) 0,
          Esys2 d (gammaStar d) (uStar d) 0, Esys3 d (gammaStar d) (uStar d) 0) := rfl
  rw [hsplit, Esys1_base hd, Esys2_base hd, Esys3_base hd]
  rfl

end SingularEndpoint

end UpperTailOptimizers
