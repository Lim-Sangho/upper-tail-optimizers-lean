import UpperTailOptimizers.SingularEndpoint.Defs

/-!
# The linearised nonlinear Factor map (Section 7, `paper/singular_endpoint.tex`)

The proof of `lem:localization-rank-one` runs the Banach-space implicit-function
theorem on the nonlinear Factor map
`𝓕(W, f) = T_W(f^{d-1}) - (∫ f^d) · f`.  Its derivative in the second variable at the
constant solution `(r_*, u_*)` is computed there to be

`D_f 𝓕(r_*, u_*)[v] = -u_*^d · (v + ∫ v)`,

and the lemma then observes that this operator is invertible, "it is multiplication by
`-u_*^d` on the mean-zero subspace and by `-2u_*^d` on the constants".  That invertibility
is the only property of the derivative the implicit-function theorem consumes.

This file isolates it as what it is: an abstract fact about a **rank-one perturbation of
the identity** on a real normed space.  Nothing here mentions `[0,1]`, `L^p`, or the
degree `d`, so the statements are available whichever function space the existence
argument is eventually carried out in.  Taking `E` to be that function space, `phi` to be
`v ↦ ∫ v` and `e` to be the constant function `1` — so that `phi e = 1` and the mean-zero
subspace is `ker phi` — turns `smulAddRankOne (-u_*^d) _ phi e _` into the displayed
derivative and `addRankOne_symm_apply_of_map_one` into the inverse.

## Contents

* `addRankOne` — the rank-one perturbation `v ↦ v + (φ v) • e` of the identity, as a
  `ContinuousLinearEquiv`, under the (sharp) invertibility hypothesis `1 + φ e ≠ 0`;
* `addRankOne_apply`, `addRankOne_symm_apply` — its forward map and its inverse
  `w ↦ w - (φ w / (1 + φ e)) • e`;
* `smulAddRankOne`, `smulAddRankOne_apply` — the scaled form `v ↦ c • (v + (φ v) • e)`
  with `c ≠ 0`, the shape in which the derivative appears in
  `lem:localization-rank-one`;
* `addRankOne_symm_apply_of_map_one` — the specialisation `φ e = 1` used by that lemma,
  where the inverse is `w ↦ w - (φ w / 2) • e`.
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

This is the abstract content of the invertibility assertion in the proof of
`lem:localization-rank-one`, "it is multiplication by `-u_*^d` on the mean-zero
subspace and by `-2u_*^d` on the constants". -/
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

/-- The forward map of `addRankOne` (`lem:localization-rank-one`). -/
@[simp]
theorem addRankOne_apply (phi : E →L[ℝ] ℝ) (e : E) (h : 1 + phi e ≠ 0) (v : E) :
    addRankOne phi e h v = v + (phi v) • e := rfl

/-- The inverse of `addRankOne`: `w ↦ w - (φ w / (1 + φ e)) • e`
(`lem:localization-rank-one`). -/
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

This is the exact shape of the derivative computed in the proof of
`lem:localization-rank-one`, `D_f 𝓕(r_*, u_*)[v] = -u_*^d · (v + ∫ v)`: take
`c = -u_*^d`, `φ = ∫ ·` and `e = 1`. -/
noncomputable def smulAddRankOne (c : ℝ) (hc : c ≠ 0) (phi : E →L[ℝ] ℝ) (e : E)
    (h : 1 + phi e ≠ 0) : E ≃L[ℝ] E :=
  (addRankOne phi e h).trans (scaleEquiv c hc)

/-- The forward map of `smulAddRankOne` (`lem:localization-rank-one`). -/
@[simp]
theorem smulAddRankOne_apply (c : ℝ) (hc : c ≠ 0) (phi : E →L[ℝ] ℝ) (e : E)
    (h : 1 + phi e ≠ 0) (v : E) :
    smulAddRankOne c hc phi e h v = c • (v + (phi v) • e) := rfl

/-! ## The case `φ e = 1` -/

/-- The specialisation used by `lem:localization-rank-one`: when `φ` is integration
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
