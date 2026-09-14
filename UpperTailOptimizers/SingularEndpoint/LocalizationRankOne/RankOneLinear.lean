import UpperTailOptimizers.SingularEndpoint.RankOneStationaryFamily.Defs

/-!
# The linearised nonlinear Factor map (Section 5, `paper/sections/singular.tex`)

The nonlinear Factor map `𝓕(W, f) = T_W(f^{d-1}) - (∫ f^d) · f`, whose zeros are the
solutions of the first identity `T_W(f^{d-1}) = q(f) f` of `eq:rank-one-orthogonality`, has
derivative in the second variable at the constant solution `(r_*, u_*)`

`D_f 𝓕(r_*, u_*)[v] = -u_*^d · (v + ∫ v)`.

This operator is invertible: it is multiplication by `-u_*^d` on the mean-zero subspace and
by `-2u_*^d` on the constants.  That invertibility is the only property of the derivative an
implicit-function-theorem construction of the factor near `u_*` would consume.  The proof of
`lem:localization-rank-one` does not linearise `𝓕`: it obtains the factor from a maximiser
of `Q_W` on the unit ball of `L^{d/(d-1)}`, and the Lean construction uses the normalised
contraction of `SingularEndpoint/LocalizationRankOne/FactorContraction.lean` instead.  No other file of the
development uses the results below.

This file isolates the invertibility as what it is: an abstract fact about a **rank-one
perturbation of the identity** on a real normed space.  Nothing here mentions `[0,1]`, `L^p`,
or the degree `d`.  Taking `E` to be a function space, `phi` to be `v ↦ ∫ v` and `e` to be
the constant function `1` — so that `phi e = 1` and the mean-zero subspace is `ker phi` —
turns `smulAddRankOne (-u_*^d) _ phi e _` into the displayed derivative and
`addRankOne_symm_apply_of_map_one` into the inverse.

## Contents

* `addRankOne` — the rank-one perturbation `v ↦ v + (φ v) • e` of the identity, as a
  `ContinuousLinearEquiv`, under the (sharp) invertibility hypothesis `1 + φ e ≠ 0`;
* `addRankOne_apply`, `addRankOne_symm_apply` — its forward map and its inverse
  `w ↦ w - (φ w / (1 + φ e)) • e`;
* `smulAddRankOne`, `smulAddRankOne_apply` — the scaled form `v ↦ c • (v + (φ v) • e)`
  with `c ≠ 0`, the shape of the derivative displayed above;
* `addRankOne_symm_apply_of_map_one` — the specialisation `φ e = 1` relevant to that
  derivative, where the inverse is `w ↦ w - (φ w / 2) • e`.
-/

namespace UpperTailOptimizers

namespace SingularEndpoint

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ## Rank-one perturbations of the identity -/

/-- The forward map `v ↦ v + (φ v) • e` of `addRankOne`, as a continuous linear map. -/
private noncomputable def addRankOneMap (phi : E →L[ℝ] ℝ) (e : E) : E →L[ℝ] E :=
  ContinuousLinearMap.id ℝ E + ContinuousLinearMap.smulRight phi e

private theorem addRankOneMap_apply (phi : E →L[ℝ] ℝ) (e : E) (v : E) :
    addRankOneMap phi e v = v + (phi v) • e := rfl

/-- The **rank-one perturbation of the identity** `v ↦ v + (φ v) • e`, as a continuous
linear equivalence.  The hypothesis `1 + φ e ≠ 0` is exactly the invertibility condition:
the map acts as the identity on `ker φ` and by the factor `1 + φ e` on `e`.

This is the abstract content of the invertibility of the linearised Factor map described in
the module docstring, which is multiplication by `-u_*^d` on the mean-zero subspace and by
`-2u_*^d` on the constants. -/
noncomputable def addRankOne (phi : E →L[ℝ] ℝ) (e : E) (h : 1 + phi e ≠ 0) : E ≃L[ℝ] E :=
  ContinuousLinearEquiv.equivOfInverse (addRankOneMap phi e)
    (addRankOneMap (-(1 + phi e)⁻¹ • phi) e)
    (fun v => by
      simp only [addRankOneMap_apply, FunLike.coe_smul, Pi.smul_apply,
        smul_eq_mul, map_add, map_smul]
      match_scalars <;> (field_simp; try ring))
    (fun w => by
      simp only [addRankOneMap_apply, FunLike.coe_smul, Pi.smul_apply,
        smul_eq_mul, map_add, map_smul]
      match_scalars <;> (field_simp; try ring))

/-- The forward map of `addRankOne`. -/
@[simp]
theorem addRankOne_apply (phi : E →L[ℝ] ℝ) (e : E) (h : 1 + phi e ≠ 0) (v : E) :
    addRankOne phi e h v = v + (phi v) • e := rfl

/-- The inverse of `addRankOne`: `w ↦ w - (φ w / (1 + φ e)) • e`. -/
theorem addRankOne_symm_apply (phi : E →L[ℝ] ℝ) (e : E) (h : 1 + phi e ≠ 0) (w : E) :
    (addRankOne phi e h).symm w = w - (phi w / (1 + phi e)) • e := by
  show addRankOneMap (-(1 + phi e)⁻¹ • phi) e w = _
  simp only [addRankOneMap_apply, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
  rw [sub_eq_add_neg, ← neg_smul]
  congr 1
  field_simp

/-! ## The scaled form -/

/-- Scaling by a nonzero real `c`, as a continuous linear equivalence. -/
private noncomputable def scaleEquiv (c : ℝ) (hc : c ≠ 0) : E ≃L[ℝ] E :=
  ContinuousLinearEquiv.equivOfInverse (c • ContinuousLinearMap.id ℝ E)
    (c⁻¹ • ContinuousLinearMap.id ℝ E)
    (fun _ => by simp only [FunLike.coe_smul, Pi.smul_apply,
      ContinuousLinearMap.coe_id', id_eq, smul_smul, inv_mul_cancel₀ hc, one_smul])
    (fun _ => by simp only [FunLike.coe_smul, Pi.smul_apply,
      ContinuousLinearMap.coe_id', id_eq, smul_smul, mul_inv_cancel₀ hc, one_smul])

/-- The **scaled rank-one perturbation** `v ↦ c • (v + (φ v) • e)`, `c ≠ 0`.

This is the exact shape of the derivative `D_f 𝓕(r_*, u_*)[v] = -u_*^d · (v + ∫ v)` of the
Factor map in the module docstring: take `c = -u_*^d`, `φ = ∫ ·` and `e = 1`. -/
noncomputable def smulAddRankOne (c : ℝ) (hc : c ≠ 0) (phi : E →L[ℝ] ℝ) (e : E)
    (h : 1 + phi e ≠ 0) : E ≃L[ℝ] E :=
  (addRankOne phi e h).trans (scaleEquiv c hc)

/-- The forward map of `smulAddRankOne`. -/
@[simp]
theorem smulAddRankOne_apply (c : ℝ) (hc : c ≠ 0) (phi : E →L[ℝ] ℝ) (e : E)
    (h : 1 + phi e ≠ 0) (v : E) :
    smulAddRankOne c hc phi e h v = c • (v + (phi v) • e) := rfl

/-! ## The case `φ e = 1` -/

/-- The specialisation relevant to the Factor map: when `φ` is integration
against a probability measure and `e` is the constant function `1`, one has `φ e = 1`, and
the inverse of `addRankOne` is `w ↦ w - (φ w / 2) • e`.  The factor `2` is the eigenvalue
`1 + φ e` on the constants, which is what makes the derivative act by `-2u_*^d` there. -/
theorem addRankOne_symm_apply_of_map_one (phi : E →L[ℝ] ℝ) (e : E) (he : phi e = 1)
    (h : 1 + phi e ≠ 0) (w : E) :
    (addRankOne phi e h).symm w = w - (phi w / 2) • e := by
  rw [addRankOne_symm_apply, he]
  norm_num

end SingularEndpoint

end UpperTailOptimizers
