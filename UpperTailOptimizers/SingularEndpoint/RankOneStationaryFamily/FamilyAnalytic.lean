import UpperTailOptimizers.SingularEndpoint.RankOneStationaryFamily.FamilySystem
import UpperTailOptimizers.SingularEndpoint.RankOneStationaryFamily.Contact

/-!
# Joint analyticity of the desingularized family system (Section 5, `paper/sections/singular.tex`)

The formal construction of the family of `lem:rank-one-kkt-family` applies the
**analytic** implicit function theorem to the desingularized system

  `F(u, ℓ, γ, h) = (E₁, E₂, E₃)`

of `SingularEndpoint/RankOneStationaryFamily/FamilySystem.lean`, at the base point
`(u, ℓ, γ, h) = (u_*, ℓ_*, γ_*, 0)` (the paper applies the theorem to `B(u,h)` in the single
unknown `u`).  Two hypotheses feed that theorem: invertibility of the
`(u, ℓ, γ)`-Jacobian, and joint analyticity of `F` near the base point.  **This file supplies
the second one.**

There is no hard analysis left in it.  Every ingredient of `E₁, E₂, E₃` is

* a polynomial in the four coordinates (in particular each of the three geometric sums of
  `eq:three-value-kkt` is a *finite* sum of monomials);
* a quotient whose denominator is nonzero at the base point — `1 - s²` and `(1 - st)²` take
  the value `1 - r_*` and `(1 - r_*)²` there, and `t` takes the value `u_* > 0`;
* the log-odds `ℓ(z) = log((1-z)/z)`, analytic on the open unit interval, composed with
  `st`, whose value at the base point is `u_*² = r_* ∈ (0,1)`;
* `logSlope`, analytic at the origin by `analyticAt_logSlope`, composed with an argument that
  **vanishes at `h = 0`** — this is exactly the removable singularity that the divisions by
  `h` and `h²` created, and `AnalyticAt.logSlope_comp` absorbs it.

## Contents

* `wBase` — the base point `((u_*, ℓ_*, γ_*), 0)` of `lem:rank-one-kkt-family`;
* `analyticAt_ell` — the log-odds `ℓ` is analytic on `(0,1)`;
* `analyticAt_Esys1`, `analyticAt_Esys2`, `analyticAt_Esys3` — each component of the
  desingularized system of `eq:three-value-kkt` is jointly analytic at `wBase`;
* `analyticAt_Fsys` — the packaged hypothesis `hF` of the analytic implicit function
  theorem for `lem:rank-one-kkt-family`.
-/

namespace UpperTailOptimizers

open Real

variable {d : ℕ}

/-! ## The base point

The parameter space is `W = (ℝ × ℝ × ℝ) × ℝ` with coordinates `w.1.1 = u`, `w.1.2.1 = ℓ`,
`w.1.2.2 = γ`, `w.2 = h`: the first factor carries the three unknowns that the implicit
function theorem solves for, the second the family parameter. -/

/-- The base point `(u, ℓ, γ, h) = (u_*, ℓ_*, γ_*, 0)` of the implicit function theorem in
`lem:rank-one-kkt-family`, as a point of `(ℝ × ℝ × ℝ) × ℝ`. -/
noncomputable def wBase (d : ℕ) : (ℝ × ℝ × ℝ) × ℝ := ((uStar d, ellStar d, gammaStar d), 0)

/-! ## The four coordinate functions

Each coordinate of `(ℝ × ℝ × ℝ) × ℝ` is a composite of the continuous linear projections
`Prod.fst` and `Prod.snd`, hence analytic everywhere. -/

/-- The coordinate `u = w.1.1` is analytic. -/
private theorem analyticAt_coord_u (w : (ℝ × ℝ × ℝ) × ℝ) :
    AnalyticAt ℝ (fun z : (ℝ × ℝ × ℝ) × ℝ => z.1.1) w :=
  analyticAt_fst.fun_comp_of_eq analyticAt_fst rfl

/-- The coordinate `ℓ = w.1.2.1` is analytic. -/
private theorem analyticAt_coord_lv (w : (ℝ × ℝ × ℝ) × ℝ) :
    AnalyticAt ℝ (fun z : (ℝ × ℝ × ℝ) × ℝ => z.1.2.1) w :=
  analyticAt_fst.fun_comp_of_eq (analyticAt_snd.fun_comp_of_eq analyticAt_fst rfl) rfl

/-- The coordinate `γ = w.1.2.2` is analytic. -/
private theorem analyticAt_coord_g (w : (ℝ × ℝ × ℝ) × ℝ) :
    AnalyticAt ℝ (fun z : (ℝ × ℝ × ℝ) × ℝ => z.1.2.2) w :=
  analyticAt_snd.fun_comp_of_eq (analyticAt_snd.fun_comp_of_eq analyticAt_fst rfl) rfl

/-- The coordinate `h = w.2` is analytic. -/
private theorem analyticAt_coord_h (w : (ℝ × ℝ × ℝ) × ℝ) :
    AnalyticAt ℝ (fun z : (ℝ × ℝ × ℝ) × ℝ => z.2) w :=
  analyticAt_snd

/-- `s = u - h` is analytic. -/
private theorem analyticAt_sVal (w : (ℝ × ℝ × ℝ) × ℝ) :
    AnalyticAt ℝ (fun z : (ℝ × ℝ × ℝ) × ℝ => z.1.1 - z.2) w :=
  (analyticAt_coord_u w).sub (analyticAt_coord_h w)

/-- `t = u + h` is analytic. -/
private theorem analyticAt_tVal (w : (ℝ × ℝ × ℝ) × ℝ) :
    AnalyticAt ℝ (fun z : (ℝ × ℝ × ℝ) × ℝ => z.1.1 + z.2) w :=
  (analyticAt_coord_u w).add (analyticAt_coord_h w)

/-! ## The log-odds -/

/-- The log-odds `ℓ(z) = log((1-z)/z)` of `SingularEndpoint/RankOneStationaryFamily/Defs.lean` is analytic at every point of
the open unit interval: the quotient `(1-z)/z` is analytic there (the denominator does not
vanish) and positive, so `Real.log` composes. -/
theorem analyticAt_ell {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) : AnalyticAt ℝ ell z := by
  have hinner : AnalyticAt ℝ (fun y : ℝ => (1 - y) / y) z :=
    (analyticAt_const.sub analyticAt_id).div analyticAt_id (ne_of_gt hz0)
  have hpos : (0 : ℝ) < (1 - z) / z := div_pos (by linarith) hz0
  exact hinner.log hpos

/-! ## The three components

Throughout, the base-point values are `u = u_*`, `h = 0`, so `s = t = u_*`, `st = u_*² = r_*`,
`1 - s² = 1 - r_* > 0`, `t = u_* > 0`, and every `logSlope` argument carries a factor `h` and
therefore vanishes. -/

/-- **`E₁` is jointly analytic at the base point.**  `E₁ = 𝓛(st)` is the middle equation of
`eq:three-value-kkt`; the only non-polynomial ingredient is `ℓ` evaluated at `st`,
whose base-point value is `u_*² = r_* ∈ (0,1)`. -/
theorem analyticAt_Esys1 (hd : 2 ≤ d) :
    AnalyticAt ℝ (fun w : (ℝ × ℝ × ℝ) × ℝ => Esys1 d w.1.2.1 w.1.2.2 w.1.1 w.2) (wBase d) := by
  have hP : AnalyticAt ℝ
      (fun z : (ℝ × ℝ × ℝ) × ℝ => (z.1.1 - z.2) * (z.1.1 + z.2)) (wBase d) :=
    (analyticAt_sVal _).mul (analyticAt_tVal _)
  have hPval : ((wBase d).1.1 - (wBase d).2) * ((wBase d).1.1 + (wBase d).2) = rStar d := by
    show (uStar d - 0) * (uStar d + 0) = rStar d
    rw [sub_zero, add_zero, ← uStar_sq hd]; ring
  have hell : AnalyticAt ℝ
      (fun z : (ℝ × ℝ × ℝ) × ℝ => ell ((z.1.1 - z.2) * (z.1.1 + z.2))) (wBase d) :=
    (analyticAt_ell (rStar_pos hd) (rStar_lt_one hd)).fun_comp_of_eq hP hPval
  simp only [Esys1, Lell]
  exact ((analyticAt_coord_lv _).sub hell).sub ((analyticAt_coord_g _).mul (hP.pow (d - 1)))

/-- **`E₂` is jointly analytic at the base point.**  `E₂ = (𝓛(t²) - 𝓛(s²))/h` in the closed
form of `SingularEndpoint/RankOneStationaryFamily/FamilySystem.lean`: the denominators `1 - s²` and `t` take the nonzero
values `1 - r_*` and `u_*`, both `logSlope` arguments carry a factor `h` and so vanish at the
base point, and the geometric sum is a finite sum of monomials. -/
theorem analyticAt_Esys2 (hd : 2 ≤ d) :
    AnalyticAt ℝ (fun w : (ℝ × ℝ × ℝ) × ℝ => Esys2 d w.1.2.2 w.1.1 w.2) (wBase d) := by
  have hr1 : rStar d < 1 := rStar_lt_one hd
  -- the two denominators are nonzero at the base point
  have hden1 : (1 : ℝ) - ((wBase d).1.1 - (wBase d).2) ^ 2 ≠ 0 := by
    have h : (1 : ℝ) - ((wBase d).1.1 - (wBase d).2) ^ 2 = 1 - rStar d := by
      show (1 : ℝ) - (uStar d - 0) ^ 2 = 1 - rStar d
      rw [sub_zero, uStar_sq hd]
    rw [h]; exact ne_of_gt (by linarith)
  have hden2 : (wBase d).1.1 + (wBase d).2 ≠ 0 := by
    show uStar d + 0 ≠ 0
    rw [add_zero]; exact uStar_ne_zero hd
  -- the two denominators are analytic
  have hD1 : AnalyticAt ℝ (fun z : (ℝ × ℝ × ℝ) × ℝ => 1 - (z.1.1 - z.2) ^ 2) (wBase d) :=
    analyticAt_const.sub ((analyticAt_sVal _).pow 2)
  have hD2 : AnalyticAt ℝ (fun z : (ℝ × ℝ × ℝ) × ℝ => z.1.1 + z.2) (wBase d) :=
    analyticAt_tVal _
  -- the two `logSlope` arguments are analytic and vanish at the base point
  have harg1 : AnalyticAt ℝ
      (fun z : (ℝ × ℝ × ℝ) × ℝ => 4 * z.1.1 * z.2 / (1 - (z.1.1 - z.2) ^ 2)) (wBase d) :=
    ((analyticAt_const.mul (analyticAt_coord_u _)).mul (analyticAt_coord_h _)).div hD1 hden1
  have harg1z :
      4 * (wBase d).1.1 * (wBase d).2 / (1 - ((wBase d).1.1 - (wBase d).2) ^ 2) = 0 := by
    show 4 * uStar d * 0 / (1 - (uStar d - 0) ^ 2) = 0
    rw [mul_zero, zero_div]
  have harg2 : AnalyticAt ℝ
      (fun z : (ℝ × ℝ × ℝ) × ℝ => 2 * z.2 / (z.1.1 + z.2)) (wBase d) :=
    (analyticAt_const.mul (analyticAt_coord_h _)).div hD2 hden2
  have harg2z : 2 * (wBase d).2 / ((wBase d).1.1 + (wBase d).2) = 0 := by
    show 2 * (0 : ℝ) / (uStar d + 0) = 0
    rw [mul_zero, zero_div]
  have hL1 : AnalyticAt ℝ
      (fun z : (ℝ × ℝ × ℝ) × ℝ =>
        logSlope (4 * z.1.1 * z.2 / (1 - (z.1.1 - z.2) ^ 2))) (wBase d) :=
    AnalyticAt.logSlope_comp harg1 harg1z
  have hL2 : AnalyticAt ℝ
      (fun z : (ℝ × ℝ × ℝ) × ℝ => logSlope (2 * z.2 / (z.1.1 + z.2))) (wBase d) :=
    AnalyticAt.logSlope_comp harg2 harg2z
  -- the geometric sum
  have hsum : AnalyticAt ℝ
      (fun z : (ℝ × ℝ × ℝ) × ℝ =>
        ∑ i ∈ Finset.range (d - 1),
          ((z.1.1 + z.2) ^ 2) ^ i * ((z.1.1 - z.2) ^ 2) ^ (d - 1 - 1 - i)) (wBase d) :=
    Finset.analyticAt_fun_sum _ fun i _ =>
      (((analyticAt_tVal _).pow 2).pow i).mul (((analyticAt_sVal _).pow 2).pow (d - 1 - 1 - i))
  simp only [Esys2]
  refine ((((analyticAt_const.mul (analyticAt_coord_u _)).div hD1 hden1).mul hL1).add
    ((analyticAt_const.div hD2 hden2).mul hL2)).sub ?_
  exact (((analyticAt_const.mul (analyticAt_coord_g _)).mul (analyticAt_coord_u _))).mul hsum

/-- **`E₃` is jointly analytic at the base point.**  `E₃ = (𝓛(t²) + 𝓛(s²) - 2𝓛(st))/h²` in
the closed form of `SingularEndpoint/RankOneStationaryFamily/FamilySystem.lean`: the single denominator `(1 - st)²` takes the
nonzero value `(1 - r_*)²`, the `logSlope` argument carries a factor `h²` and so vanishes at
the base point, and the three geometric sums are finite sums of monomials. -/
theorem analyticAt_Esys3 (hd : 2 ≤ d) :
    AnalyticAt ℝ (fun w : (ℝ × ℝ × ℝ) × ℝ => Esys3 d w.1.2.2 w.1.1 w.2) (wBase d) := by
  have hr1 : rStar d < 1 := rStar_lt_one hd
  have hden : (1 - ((wBase d).1.1 - (wBase d).2) * ((wBase d).1.1 + (wBase d).2)) ^ 2 ≠ 0 := by
    have h : (1 - ((wBase d).1.1 - (wBase d).2) * ((wBase d).1.1 + (wBase d).2)) ^ 2
        = (1 - rStar d) ^ 2 := by
      show (1 - (uStar d - 0) * (uStar d + 0)) ^ 2 = (1 - rStar d) ^ 2
      rw [sub_zero, add_zero, ← uStar_sq hd]; ring
    rw [h]
    exact pow_ne_zero 2 (ne_of_gt (by linarith))
  have hD : AnalyticAt ℝ
      (fun z : (ℝ × ℝ × ℝ) × ℝ => (1 - (z.1.1 - z.2) * (z.1.1 + z.2)) ^ 2) (wBase d) :=
    (analyticAt_const.sub ((analyticAt_sVal _).mul (analyticAt_tVal _))).pow 2
  have harg : AnalyticAt ℝ
      (fun z : (ℝ × ℝ × ℝ) × ℝ =>
        4 * z.2 ^ 2 / (1 - (z.1.1 - z.2) * (z.1.1 + z.2)) ^ 2) (wBase d) :=
    (analyticAt_const.mul ((analyticAt_coord_h _).pow 2)).div hD hden
  have hargz : 4 * (wBase d).2 ^ 2
      / (1 - ((wBase d).1.1 - (wBase d).2) * ((wBase d).1.1 + (wBase d).2)) ^ 2 = 0 := by
    show 4 * (0 : ℝ) ^ 2 / (1 - (uStar d - 0) * (uStar d + 0)) ^ 2 = 0
    norm_num
  have hL : AnalyticAt ℝ
      (fun z : (ℝ × ℝ × ℝ) × ℝ =>
        logSlope (4 * z.2 ^ 2 / (1 - (z.1.1 - z.2) * (z.1.1 + z.2)) ^ 2)) (wBase d) :=
    AnalyticAt.logSlope_comp harg hargz
  have hsum1 : AnalyticAt ℝ
      (fun z : (ℝ × ℝ × ℝ) × ℝ =>
        ∑ i ∈ Finset.range (d - 1),
          ((z.1.1 + z.2) ^ 2) ^ i
            * ((z.1.1 - z.2) * (z.1.1 + z.2)) ^ (d - 1 - 1 - i)) (wBase d) :=
    Finset.analyticAt_fun_sum _ fun i _ =>
      (((analyticAt_tVal _).pow 2).pow i).mul
        (((analyticAt_sVal _).mul (analyticAt_tVal _)).pow (d - 1 - 1 - i))
  have hsum2 : AnalyticAt ℝ
      (fun z : (ℝ × ℝ × ℝ) × ℝ =>
        ∑ i ∈ Finset.range (d - 1),
          (z.1.1 - z.2) ^ (d - 1 - 1 - i) * (z.1.1 + z.2) ^ i) (wBase d) :=
    Finset.analyticAt_fun_sum _ fun i _ =>
      ((analyticAt_sVal _).pow (d - 1 - 1 - i)).mul ((analyticAt_tVal _).pow i)
  have hsum3 : AnalyticAt ℝ
      (fun z : (ℝ × ℝ × ℝ) × ℝ =>
        ∑ j ∈ Finset.range (d - 2),
          (z.1.1 + z.2) ^ j * (z.1.1 - z.2) ^ (d - 2 - 1 - j)) (wBase d) :=
    Finset.analyticAt_fun_sum _ fun j _ =>
      ((analyticAt_tVal _).pow j).mul ((analyticAt_sVal _).pow (d - 2 - 1 - j))
  simp only [Esys3]
  refine ((analyticAt_const.div hD hden).mul hL).sub ?_
  exact (analyticAt_const.mul (analyticAt_coord_g _)).mul
    (hsum1.add (((analyticAt_sVal _).mul hsum2).mul hsum3))

/-! ## The packaged hypothesis -/

/-- **The hypothesis `hF` of the analytic implicit function theorem** for
`lem:rank-one-kkt-family`: the desingularized system
`F = (E₁, E₂, E₃) : (ℝ × ℝ × ℝ) × ℝ → ℝ × ℝ × ℝ` of `eq:three-value-kkt` is jointly
analytic at the base point `(u_*, ℓ_*, γ_*, 0)`. -/
theorem analyticAt_Fsys (hd : 2 ≤ d) :
    AnalyticAt ℝ (fun w : (ℝ × ℝ × ℝ) × ℝ =>
        ((Esys1 d w.1.2.1 w.1.2.2 w.1.1 w.2, Esys2 d w.1.2.2 w.1.1 w.2,
          Esys3 d w.1.2.2 w.1.1 w.2) : ℝ × ℝ × ℝ)) (wBase d) :=
  (analyticAt_Esys1 hd).prod ((analyticAt_Esys2 hd).prod (analyticAt_Esys3 hd))

end UpperTailOptimizers
