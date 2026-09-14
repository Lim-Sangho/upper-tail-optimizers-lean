import UpperTailOptimizers.SingularEndpoint.RankOneStationaryFamily.Contact

/-!
# Inverting the log-odds (Section 5, `paper/sections/singular.tex`)

The scalar family of `lem:rank-one-kkt-family` is produced by the analytic
implicit function theorem in the coordinates `(u_h, ℓ_h, γ_h)`, where `ℓ_h` plays the role
of the log-odds `ℓ(p_h)` of the ambient density.  Recovering `p_h` itself is purely
explicit: the log-odds `ℓ(z) = log((1-z)/z)` of `SingularEndpoint/RankOneStationaryFamily/Defs.lean` is inverted on the
open unit interval by

```
p = 1 / (1 + e^ℓ),
```

which is analytic on all of `ℝ` because `1 + e^L` never vanishes.  So `p_h` is an analytic
function of `h` as soon as `ℓ_h` is, which is the first of the four steps that turn
`exists_scalar_family` into a constructed `KKTFamily`.

## Contents

* `pOf` — the inverse log-odds `L ↦ 1/(1 + e^L)`;
* `pOf_pos`, `pOf_lt_one` — its values lie in the open unit interval;
* `ell_pOf`, `pOf_ell` — the two inversion identities, `ℓ ∘ pOf = id` on `ℝ` and
  `pOf ∘ ℓ = id` on `(0,1)`;
* `pOf_ellStar` — `pOf(ℓ_*) = p_*`, the base point of the family
  (`lem:rank-one-kkt-family`);
* `analyticAt_pOf` — `pOf` is real-analytic at every point.
-/

namespace UpperTailOptimizers

namespace SingularEndpoint

open Real

variable {d : ℕ}

/-- The inverse log-odds `pOf L = 1/(1 + e^L)`.  Solving `ℓ(p) = log((1-p)/p) = L` for `p`
gives exactly this, so `pOf` inverts `ell` on the open unit interval (`ell_pOf`,
`pOf_ell`).  It is the explicit analytic map that recovers the ambient density `p_h` from
the family coordinate `ℓ_h` of `lem:rank-one-kkt-family`. -/
noncomputable def pOf (L : ℝ) : ℝ := 1 / (1 + Real.exp L)

/-- The denominator `1 + e^L` of `pOf` is strictly positive; in particular it never
vanishes, which is what makes `pOf` analytic on all of `ℝ`. -/
theorem one_add_exp_pos (L : ℝ) : (0 : ℝ) < 1 + Real.exp L := by
  have := Real.exp_pos L
  linarith

/-- `pOf L > 0`: the inverse log-odds is a genuine density. -/
theorem pOf_pos (L : ℝ) : 0 < pOf L :=
  div_pos one_pos (one_add_exp_pos L)

/-- `pOf L < 1`: the inverse log-odds is a genuine density. -/
theorem pOf_lt_one (L : ℝ) : pOf L < 1 := by
  rw [pOf, div_lt_one (one_add_exp_pos L)]
  have := Real.exp_pos L
  linarith

/-- **`ℓ ∘ pOf = id`.**  Since `1 - pOf L = e^L/(1 + e^L)`, the ratio
`(1 - pOf L)/pOf L` is exactly `e^L`, and `Real.log_exp` finishes. -/
theorem ell_pOf (L : ℝ) : ell (pOf L) = L := by
  have hden : (1 + Real.exp L) ≠ 0 := ne_of_gt (one_add_exp_pos L)
  have hratio : (1 - pOf L) / pOf L = Real.exp L := by
    rw [pOf]
    field_simp
    ring
  rw [ell, hratio, Real.log_exp]

/-- **`pOf ∘ ℓ = id` on `(0,1)`.**  For `p ∈ (0,1)` the ratio `(1-p)/p` is positive, so
`e^{ℓ(p)} = (1-p)/p` and `1/(1 + (1-p)/p) = p`. -/
theorem pOf_ell {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) : pOf (ell p) = p := by
  have hpos : (0 : ℝ) < (1 - p) / p := div_pos (by linarith) hp0
  rw [pOf, ell, Real.exp_log hpos]
  field_simp
  ring

/-- `pOf(ℓ_*) = p_*`: the base point of the scalar family of
`lem:rank-one-kkt-family` in the coordinate `ℓ` corresponds to the singular endpoint
density `p_*`.  Immediate from `ell_pStar` and `pOf_ell`. -/
theorem pOf_ellStar (hd : 2 ≤ d) : pOf (ellStar d) = pStar d := by
  rw [← ell_pStar hd, pOf_ell (pStar_pos hd) (pStar_lt_one hd)]

/-- **`pOf` is real-analytic at every point.**  `Real.exp` is analytic and `1 + e^L > 0`,
so the quotient `1/(1 + e^L)` is analytic; hence `p_h = pOf ℓ_h` is analytic in `h`
whenever `ℓ_h` is, which is what `lem:rank-one-kkt-family` needs. -/
theorem analyticAt_pOf (L : ℝ) : AnalyticAt ℝ pOf L := by
  have hexp : AnalyticAt ℝ (fun x : ℝ => 1 + Real.exp x) L :=
    analyticAt_const.add analyticAt_rexp
  exact analyticAt_const.div hexp (ne_of_gt (one_add_exp_pos L))

end SingularEndpoint

end UpperTailOptimizers
