import UpperTailOptimizers.SingularEndpoint.RankOneStationaryFamily.Defs

/-!
# The `3 × 3` family Jacobian (Section 5, `paper/sections/singular.tex`)

The linear-algebraic input to the implicit function theorem behind
`lem:rank-one-kkt-family`.

The desingularized family system `(E₁, E₂, E₃)` used for that lemma
(`SingularEndpoint/RankOneStationaryFamily/FamilySystem.lean`; the paper works with `B(u,h)` instead) has, at the base point
`(u_*, ℓ_*, γ_*, 0)`, the `(u, ℓ, γ)`-Jacobian

```
[ 0   1   a ]
[ 0   0   b ]
[ c   0   e ]
```

with `b = -4u_*(d-1)r_*^{d-2}` and `c = 8u_*³ · Γ_d^{(4)}(r_*)` both nonzero (the latter by
`Lstar3_rStar`), so that the determinant `-bc` is nonzero.  Nothing else about the entries
matters, so the equivalence is built here purely abstractly, from the four real parameters
`a, b, c, e` and the two nonvanishing hypotheses; the explicit inverse is

  `(P, Q, R) ↦ ((R - eQ/b)/c, P - aQ/b, Q/b)`.

Feeding `jac3` to `LZBoundary/AnalyticIFT.lean`'s `analytic_implicit` is what turns the
strict differentiability of `(E₁, E₂, E₃)` into the analytic family.

## Contents

* `jac3` — the continuous linear equivalence of `ℝ × ℝ × ℝ` given by the matrix above
  (`lem:rank-one-kkt-family`);
* `jac3_apply`, `jac3_symm_apply` — its forward and inverse formulas;
* `jac3_coe` — the underlying continuous linear map, in the shape a `HasStrictFDerivAt`
  statement wants.
-/

namespace UpperTailOptimizers

namespace SingularEndpoint

/-- The forward continuous linear map `(x, y, z) ↦ (y + az, bz, cx + ez)` underlying
`jac3`. -/
private noncomputable def jac3Fwd (a b c e : ℝ) : (ℝ × ℝ × ℝ) →L[ℝ] (ℝ × ℝ × ℝ) where
  toFun v := (v.2.1 + a * v.2.2, b * v.2.2, c * v.1 + e * v.2.2)
  map_add' v w := by
    simp only [Prod.fst_add, Prod.snd_add, Prod.mk_add_mk, Prod.mk.injEq]
    refine ⟨by ring, by ring, by ring⟩
  map_smul' m v := by
    simp only [Prod.smul_fst, Prod.smul_snd, Prod.smul_mk, RingHom.id_apply, smul_eq_mul,
      Prod.mk.injEq]
    refine ⟨by ring, by ring, by ring⟩
  cont := by fun_prop

/-- The inverse continuous linear map `(P, Q, R) ↦ ((R - eQ/b)/c, P - aQ/b, Q/b)`
underlying `jac3`. -/
private noncomputable def jac3Inv (a b c e : ℝ) : (ℝ × ℝ × ℝ) →L[ℝ] (ℝ × ℝ × ℝ) where
  toFun w := ((w.2.2 - e * w.2.1 / b) / c, w.1 - a * w.2.1 / b, w.2.1 / b)
  map_add' v w := by
    simp only [Prod.fst_add, Prod.snd_add, Prod.mk_add_mk, Prod.mk.injEq]
    refine ⟨by ring, by ring, by ring⟩
  map_smul' m v := by
    simp only [Prod.smul_fst, Prod.smul_snd, Prod.smul_mk, RingHom.id_apply, smul_eq_mul,
      Prod.mk.injEq]
    refine ⟨by ring, by ring, by ring⟩
  cont := by fun_prop

/-- The `3 × 3` Jacobian of `lem:rank-one-kkt-family` at the base point, as a
continuous linear equivalence of `ℝ × ℝ × ℝ`:

  `(x, y, z) ↦ (y + az, bz, cx + ez)`,

invertible exactly because its determinant `-bc` is nonzero.  Its inverse is
`(P, Q, R) ↦ ((R - eQ/b)/c, P - aQ/b, Q/b)`. -/
noncomputable def jac3 (a b c e : ℝ) (hb : b ≠ 0) (hc : c ≠ 0) :
    (ℝ × ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ × ℝ) :=
  ContinuousLinearEquiv.equivOfInverse (jac3Fwd a b c e) (jac3Inv a b c e)
    (by
      rintro ⟨x, y, z⟩
      show ((c * x + e * z - e * (b * z) / b) / c, y + a * z - a * (b * z) / b, b * z / b)
        = (x, y, z)
      simp only [Prod.mk.injEq]
      refine ⟨?_, ?_, ?_⟩ <;> field_simp <;> ring)
    (by
      rintro ⟨P, Q, R⟩
      show (P - a * Q / b + a * (Q / b), b * (Q / b),
          c * ((R - e * Q / b) / c) + e * (Q / b)) = (P, Q, R)
      simp only [Prod.mk.injEq]
      refine ⟨by ring, ?_, ?_⟩ <;> field_simp
      ring)

/-- Forward formula for `jac3` (`lem:rank-one-kkt-family`). -/
theorem jac3_apply (a b c e : ℝ) (hb : b ≠ 0) (hc : c ≠ 0) (v : ℝ × ℝ × ℝ) :
    jac3 a b c e hb hc v = (v.2.1 + a * v.2.2, b * v.2.2, c * v.1 + e * v.2.2) :=
  rfl

/-- Inverse formula for `jac3` (`lem:rank-one-kkt-family`). -/
theorem jac3_symm_apply (a b c e : ℝ) (hb : b ≠ 0) (hc : c ≠ 0) (w : ℝ × ℝ × ℝ) :
    (jac3 a b c e hb hc).symm w
      = ((w.2.2 - e * w.2.1 / b) / c, w.1 - a * w.2.1 / b, w.2.1 / b) :=
  rfl

/-- The continuous linear map underlying `jac3`, in the shape a `HasStrictFDerivAt`
statement for the family system of `lem:rank-one-kkt-family` produces. -/
theorem jac3_coe (a b c e : ℝ) (hb : b ≠ 0) (hc : c ≠ 0) :
    ((jac3 a b c e hb hc : (ℝ × ℝ × ℝ) →L[ℝ] (ℝ × ℝ × ℝ)) : (ℝ × ℝ × ℝ) → (ℝ × ℝ × ℝ))
      = fun v => (v.2.1 + a * v.2.2, b * v.2.2, c * v.1 + e * v.2.2) :=
  rfl

end SingularEndpoint

end UpperTailOptimizers
