import UpperTailOptimizers.SingularEndpoint.RankOneStationaryFamily.Contact
import UpperTailOptimizers.SingularEndpoint.RankOneStationaryFamily.Bipodality

/-!
# Derivatives of the rank-one KKT function (Section 5, `paper/sections/singular.tex`)

`SingularEndpoint/RankOneStationaryFamily/Contact.lean` differentiates `𝓛_*` — the rank-one KKT function
`F_{p,γ}(z) = J_p'(z) - γ z^{d-1}` frozen at the *singular endpoint* parameters `(p_*, γ_*)` — three
times, and shows it vanishes to order exactly three at `r_*`.  Along the coalescing family
of `lem:rank-one-kkt-family` the parameters move, so the same derivatives are
needed for a general admissible `(p, γ)`.  This file supplies them.

The one thing worth noticing is that **`p` disappears after the first derivative**: `J_p'`
differs from `J_{p'}'` by an additive constant (the `ℓ(p)` term of `J_p'(u) = ℓ(p) - ℓ(u)`,
used inline in `app:rank-one-kkt-family`, which is `Jp'_eq_ell_sub`), so
`F_{p,γ}' = J_p'' - γ(d-1)z^{d-2}` no longer mentions `p`.  Accordingly `Fkkt1`, `Fkkt2` and
`Fkkt3` carry only `γ`, and the `Lstar`-level statements of `SingularEndpoint/RankOneStationaryFamily/Contact.lean` are
their specialisations at `γ = γ_*` — definitionally so, which is what `Lstar3_eq` records
and what lets the `Lstar`-level statements be proved by `exact` from the `Fkkt`-level ones.

## Contents

* `Fkkt1`, `Fkkt2`, `Fkkt3` — the first three `z`-derivatives of `F_{p,γ}`;
* `hasDerivAt_Fkkt'`, `hasDerivAt_Fkkt1`, `hasDerivAt_Fkkt2` — the chain, on `(0,1)`;
* `Lstar3_eq` — agreement with `SingularEndpoint/RankOneStationaryFamily/Contact.lean`;
* `Fkkt3_gammaStar_rStar` — `Lstar3_rStar` in `Fkkt3` phrasing;
* `continuousAt_Jp4`, `continuousAt_Fkkt3` — joint continuity in `(γ, z)`, which is how the
  singular endpoint value `Lstar3 d r_* = d⁵/(d-1)²` of `Lstar3_rStar` is transported along the family.
-/

namespace UpperTailOptimizers

namespace SingularEndpoint

variable {d : ℕ}

/-! ## The derivatives -/

/-- `F_{p,γ}'(z) = J_p''(z) - γ(d-1)z^{d-2}`.  Independent of `p`. -/
noncomputable def Fkkt1 (d : ℕ) (γ z : ℝ) : ℝ :=
  Jp'' z - γ * ((d : ℝ) - 1) * z ^ (d - 2)

/-- `F_{p,γ}''(z) = J_p^{(3)}(z) - γ(d-1)(d-2)z^{d-3}`. -/
noncomputable def Fkkt2 (d : ℕ) (γ z : ℝ) : ℝ :=
  Jp3 z - γ * ((d : ℝ) - 1) * ((d : ℝ) - 2) * z ^ (d - 3)

/-- `F_{p,γ}'''(z) = J_p^{(4)}(z) - γ(d-1)(d-2)(d-3)z^{d-4}`.

As in `Lstar3`, the last factor is the cast of the **natural-number** difference `d - 3`:
differentiating `z ↦ z^{d-3}` produces `((d-3 : ℕ) : ℝ) z^{d-4}`, and at `d = 2` that
coefficient is `0` whereas `(d:ℝ) - 3 = -1`. -/
noncomputable def Fkkt3 (d : ℕ) (γ z : ℝ) : ℝ :=
  Jp4 z - γ * ((d : ℝ) - 1) * ((d : ℝ) - 2) * ((d - 3 : ℕ) : ℝ) * z ^ (d - 4)

/-- The first derivative, in `Fkkt1` notation.  `SingularEndpoint/RankOneStationaryFamily/Bipodality.lean` already proves
this with the derivative written out; `Fkkt1` is by definition that expression, so this is
only a renaming. -/
theorem hasDerivAt_Fkkt' (hd : 2 ≤ d) {p γ z : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hz0 : 0 < z) (hz1 : z < 1) : HasDerivAt (Fkkt d p γ) (Fkkt1 d γ z) z :=
  hasDerivAt_Fkkt hd hp0 hp1 hz0 hz1

theorem hasDerivAt_Fkkt1 (hd : 2 ≤ d) {γ z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    HasDerivAt (Fkkt1 d γ) (Fkkt2 d γ z) z := by
  have h1 : HasDerivAt Jp'' (Jp3 z) z := hasDerivAt_Jp'' hz0 hz1
  have h2 : HasDerivAt (fun x : ℝ => γ * ((d : ℝ) - 1) * x ^ (d - 2))
      (γ * ((d : ℝ) - 1) * (((d - 2 : ℕ) : ℝ) * z ^ (d - 2 - 1))) z :=
    (hasDerivAt_pow (d - 2) z).const_mul _
  have e := h1.sub h2
  have hval : Jp3 z - γ * ((d : ℝ) - 1) * (((d - 2 : ℕ) : ℝ) * z ^ (d - 2 - 1))
      = Fkkt2 d γ z := by
    rw [Fkkt2, cast_sub_two hd, show d - 2 - 1 = d - 3 from by omega]
    ring
  rw [hval] at e
  exact e

theorem hasDerivAt_Fkkt2 (hd : 2 ≤ d) {γ z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    HasDerivAt (Fkkt2 d γ) (Fkkt3 d γ z) z := by
  have _hd : 2 ≤ d := hd
  have h1 : HasDerivAt Jp3 (Jp4 z) z := hasDerivAt_Jp3 hz0 hz1
  have h2 : HasDerivAt (fun x : ℝ => γ * ((d : ℝ) - 1) * ((d : ℝ) - 2) * x ^ (d - 3))
      (γ * ((d : ℝ) - 1) * ((d : ℝ) - 2) * (((d - 3 : ℕ) : ℝ) * z ^ (d - 3 - 1))) z :=
    (hasDerivAt_pow (d - 3) z).const_mul _
  have e := h1.sub h2
  have hval : Jp4 z - γ * ((d : ℝ) - 1) * ((d : ℝ) - 2) *
      (((d - 3 : ℕ) : ℝ) * z ^ (d - 3 - 1)) = Fkkt3 d γ z := by
    rw [Fkkt3, show d - 3 - 1 = d - 4 from by omega]
    ring
  rw [hval] at e
  exact e

/-! ## Agreement with the derivatives at the singular endpoint of `SingularEndpoint/RankOneStationaryFamily/Contact.lean` -/

theorem Lstar3_eq (d : ℕ) (z : ℝ) : Lstar3 d z = Fkkt3 d (gammaStar d) z := rfl

/-- The third derivative at the singular endpoint parameters, in `Fkkt3` form: this is
`Lstar3_rStar` transported across `Lstar3_eq`, and it is the non-degeneracy constant of the
`h⁴` order argument. -/
theorem Fkkt3_gammaStar_rStar (hd : 2 ≤ d) :
    Fkkt3 d (gammaStar d) (rStar d) = (d : ℝ) ^ 5 / ((d : ℝ) - 1) ^ 2 := by
  rw [← Lstar3_eq]; exact Lstar3_rStar hd

/-! ## Continuity -/

/-- `Jp4` is continuous on `(0,1)` — it is differentiable there, with derivative `Jp5`. -/
theorem continuousAt_Jp4 {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) : ContinuousAt Jp4 z :=
  (hasDerivAt_Jp4 hz0 hz1).continuousAt

/-- **Joint continuity of `F_{p,γ}'''` in `(γ, z)`.**

This is what carries the non-degeneracy `Fkkt3 d γ_* r_* = d⁵/(d-1)² ≠ 0` along the
coalescing family: as `h → 0` the parameter `γ_h` tends to `γ_*` and the three nodes — hence
any point `ξ_h` between them — tend to `r_*`, so `Fkkt3 d γ_h ξ_h` tends to `d⁵/(d-1)²`. -/
theorem continuousAt_Fkkt3 (d : ℕ) {γ z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    ContinuousAt (fun q : ℝ × ℝ => Fkkt3 d q.1 q.2) (γ, z) := by
  have hJ : ContinuousAt (fun q : ℝ × ℝ => Jp4 q.2) (γ, z) :=
    (continuousAt_Jp4 hz0 hz1).comp' continuousAt_snd
  have hpow : ContinuousAt (fun q : ℝ × ℝ =>
      q.1 * ((d : ℝ) - 1) * ((d : ℝ) - 2) * ((d - 3 : ℕ) : ℝ) * q.2 ^ (d - 4)) (γ, z) := by
    fun_prop
  exact hJ.sub hpow

end SingularEndpoint

end UpperTailOptimizers
