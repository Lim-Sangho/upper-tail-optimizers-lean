import UpperTailOptimizers.LZBoundary.Merge.Critical
import UpperTailOptimizers.LZBoundary.AnalyticImplicitUnique

/-!
# The merged contact is nondegenerate, and the analytic solution branch

At the exceptional density the normalised critical-point function `What` of `Merge/Critical.lean`
vanishes (`What_rStar_zero`) with a **negative** `u`-derivative (`deriv_What_rStar_neg`).  The
analytic implicit function theorem of `LZBoundary/AnalyticImplicitUnique.lean` then produces an
analytic branch `u(ε)` of solutions through `(r_*, 0)`, unique among continuous branches
(`exists_merge_solution`).

The two values that drive the computation are
`What d ε 0 = ⅙(ε^{-2} - (1-ε)^{-2})·C(d,2)ε^{d-2} + (2ε(1-ε))^{-1}·C(d,3)ε^{d-3}`, which vanishes
exactly at `ε = r_*`, and
`∂_u What d ε 0 = -⅙(ε^{-3} + (1-ε)^{-3})·C(d,2)ε^{d-2} + (ε(1-ε))^{-1}·C(d,4)ε^{d-4}`, which at
`ε = r_*` equals `-d⁴(d-1)r_*^{d-4}/24 < 0`: the fourth-order degeneracy of the merged contact is
exactly what makes this derivative nonzero.
-/

namespace UpperTailOptimizers

open Filter Topology

/-! ### Binomial coefficients as real polynomials in `d` -/

/-- `2·C(d,2) = d(d-1)` in `ℝ`. -/
private theorem cast_choose_two {d : ℕ} (hd : 2 ≤ d) :
    ((d.choose 2 : ℕ) : ℝ) * 2 = (d : ℝ) * ((d : ℝ) - 1) := by
  have h1 : (1 : ℕ) ≤ d := le_trans (by norm_num) hd
  have hnat : (d - 1) * d = 2 * d.choose 2 := by
    have h := Nat.descFactorial_eq_factorial_mul_choose d 2
    simpa [Nat.descFactorial, Nat.factorial] using h
  have hcast : (((d - 1) * d : ℕ) : ℝ) = ((2 * d.choose 2 : ℕ) : ℝ) := by rw [hnat]
  push_cast [Nat.cast_sub h1] at hcast
  linarith

/-- `6·C(d,3) = d(d-1)(d-2)` in `ℝ`. -/
private theorem cast_choose_three {d : ℕ} (hd : 3 ≤ d) :
    ((d.choose 3 : ℕ) : ℝ) * 6 = (d : ℝ) * ((d : ℝ) - 1) * ((d : ℝ) - 2) := by
  have h1 : (1 : ℕ) ≤ d := le_trans (by norm_num) hd
  have h2 : (2 : ℕ) ≤ d := le_trans (by norm_num) hd
  have hnat : (d - 2) * ((d - 1) * d) = 6 * d.choose 3 := by
    have h := Nat.descFactorial_eq_factorial_mul_choose d 3
    simpa [Nat.descFactorial, Nat.factorial] using h
  have hcast : (((d - 2) * ((d - 1) * d) : ℕ) : ℝ) = ((6 * d.choose 3 : ℕ) : ℝ) := by rw [hnat]
  push_cast [Nat.cast_sub h1, Nat.cast_sub h2] at hcast
  nlinarith [hcast]

/-- `24·C(d,4) = d(d-1)(d-2)(d-3)` in `ℝ`. -/
private theorem cast_choose_four {d : ℕ} (hd : 4 ≤ d) :
    ((d.choose 4 : ℕ) : ℝ) * 24 = (d : ℝ) * ((d : ℝ) - 1) * ((d : ℝ) - 2) * ((d : ℝ) - 3) := by
  have h1 : (1 : ℕ) ≤ d := le_trans (by norm_num) hd
  have h2 : (2 : ℕ) ≤ d := le_trans (by norm_num) hd
  have h3 : (3 : ℕ) ≤ d := le_trans (by norm_num) hd
  have hnat : (d - 3) * ((d - 2) * ((d - 1) * d)) = 24 * d.choose 4 := by
    have h := Nat.descFactorial_eq_factorial_mul_choose d 4
    simpa [Nat.descFactorial, Nat.factorial] using h
  have hcast : (((d - 3) * ((d - 2) * ((d - 1) * d)) : ℕ) : ℝ) = ((24 * d.choose 4 : ℕ) : ℝ) := by
    rw [hnat]
  push_cast [Nat.cast_sub h1, Nat.cast_sub h2, Nat.cast_sub h3] at hcast
  nlinarith [hcast]

/-- `1 - r_* = 1/d`. -/
private theorem one_sub_rStar_eq {d : ℕ} (hd : 2 ≤ d) : 1 - rStar d = 1 / (d : ℝ) := by
  have hD : (0 : ℝ) < (d : ℝ) := dpos hd
  unfold rStar
  field_simp
  ring

/-! ### The two values at the exceptional density -/

/-- **The normalised equation holds at the merged contact**: `What d r_* 0 = 0`. -/
theorem What_rStar_zero {d : ℕ} (hd : 2 ≤ d) : What d (rStar d) 0 = 0 := by
  have hD1 : (1 : ℝ) < (d : ℝ) := one_lt_d hd
  have hD0 : (0 : ℝ) < (d : ℝ) := dpos hd
  have he0 : 0 < rStar d := rStar_pos hd
  have he1 : rStar d < 1 := rStar_lt_one hd
  have hsub : 1 - rStar d = 1 / (d : ℝ) := one_sub_rStar_eq hd
  have hdef : rStar d = ((d : ℝ) - 1) / (d : ℝ) := rfl
  unfold What
  rw [Qfun1_zero he0 he1, Qfun_zero he0 he1, polyP_zero hd, polyP1_zero hd]
  rcases eq_or_lt_of_le hd with h2 | h3
  · -- `d = 2`: both binomial factors conspire to vanish
    have hd2 : d = 2 := h2.symm
    subst hd2
    norm_num [rStar]
  · -- `d ≥ 3`
    have h3' : 3 ≤ d := h3
    have hpow : rStar d ^ (d - 2) = rStar d ^ (d - 3) * rStar d := by
      rw [← pow_succ]
      congr 1
      omega
    have hC2 := cast_choose_two hd
    have hC3 := cast_choose_three h3'
    have hne : rStar d ≠ 0 := ne_of_gt he0
    have h1sne : (1 : ℝ) - rStar d ≠ 0 := ne_of_gt (by linarith)
    have hDne : (d : ℝ) ≠ 0 := ne_of_gt hD0
    have hD1ne : (d : ℝ) - 1 ≠ 0 := by linarith
    have hC2' : ((d.choose 2 : ℕ) : ℝ) = (d : ℝ) * ((d : ℝ) - 1) / 2 := by linarith [hC2]
    have hC3' : ((d.choose 3 : ℕ) : ℝ)
        = (d : ℝ) * ((d : ℝ) - 1) * ((d : ℝ) - 2) / 6 := by linarith [hC3]
    rw [hpow, hsub, hdef, hC2', hC3']
    field_simp
    ring

/-- **The nondegeneracy at the merged contact**: the `u`-derivative of `What` at `(r_*, 0)` is
negative, hence nonzero. -/
theorem deriv_What_rStar_neg {d : ℕ} (hd : 2 ≤ d) :
    deriv (fun u : ℝ => What d (rStar d) u) 0 < 0 := by
  have hD1 : (1 : ℝ) < (d : ℝ) := one_lt_d hd
  have hD0 : (0 : ℝ) < (d : ℝ) := dpos hd
  have he0 : 0 < rStar d := rStar_pos hd
  have he1 : rStar d < 1 := rStar_lt_one hd
  have hsub : 1 - rStar d = 1 / (d : ℝ) := one_sub_rStar_eq hd
  have hdef : rStar d = ((d : ℝ) - 1) / (d : ℝ) := rfl
  have hne : rStar d ≠ 0 := ne_of_gt he0
  have h1s : (0 : ℝ) < 1 - rStar d := by linarith
  have h1sne : (1 : ℝ) - rStar d ≠ 0 := ne_of_gt h1s
  have hDne : (d : ℝ) ≠ 0 := ne_of_gt hD0
  have hD1ne : (d : ℝ) - 1 ≠ 0 := by linarith
  rw [(hasDerivAt_What d he0 he1).deriv, Qfun2_zero he0 he1, Qfun_zero he0 he1,
    polyP_zero hd, deriv_polyP1_zero hd]
  have hC2 := cast_choose_two hd
  have hpos : 0 < rStar d ^ (d - 2) := pow_pos he0 _
  rcases lt_or_ge d 4 with hlt4 | hge4
  · -- `d = 2` or `d = 3`: the `C(d,4)` term vanishes and the first term is negative
    have hC4 : ((d.choose 4 : ℕ) : ℝ) = 0 := by
      have : d.choose 4 = 0 := Nat.choose_eq_zero_of_lt hlt4
      rw [this]; norm_num
    rw [hC4]
    have hC2pos : (0 : ℝ) < ((d.choose 2 : ℕ) : ℝ) := by nlinarith [hC2]
    have hcube : 0 < 1 / rStar d ^ 3 + 1 / (1 - rStar d) ^ 3 := by positivity
    nlinarith [mul_pos hcube (mul_pos hC2pos hpos)]
  · -- `d ≥ 4`: the exact value is `-d⁴(d-1)r_*^{d-4}/24`
    have hC4 := cast_choose_four hge4
    have hpow2 : rStar d ^ (d - 2) = rStar d ^ (d - 4) * rStar d ^ 2 := by
      rw [← pow_add]
      congr 1
      omega
    have hpos4 : 0 < rStar d ^ (d - 4) := pow_pos he0 _
    have hval : -(1 / 6 * (1 / rStar d ^ 3 + 1 / (1 - rStar d) ^ 3))
          * (((d.choose 2 : ℕ) : ℝ) * rStar d ^ (d - 2))
        - -(1 / (2 * rStar d * (1 - rStar d)))
          * (2 * ((d.choose 4 : ℕ) : ℝ) * rStar d ^ (d - 4))
        = -((d : ℝ) ^ 4 * ((d : ℝ) - 1) / 24) * rStar d ^ (d - 4) := by
      have hC2' : ((d.choose 2 : ℕ) : ℝ) = (d : ℝ) * ((d : ℝ) - 1) / 2 := by linarith [hC2]
      have hC4' : ((d.choose 4 : ℕ) : ℝ)
          = (d : ℝ) * ((d : ℝ) - 1) * ((d : ℝ) - 2) * ((d : ℝ) - 3) / 24 := by linarith [hC4]
      rw [hpow2, hsub, hdef, hC2', hC4']
      field_simp
      ring
    rw [hval]
    have : 0 < (d : ℝ) ^ 4 * ((d : ℝ) - 1) := by positivity
    nlinarith [mul_pos this hpos4]

/-! ### The analytic solution branch -/

/-- **The analytic branch of merged-contact solutions.**  There is an analytic `u` with
`u(r_*) = 0` solving `What d ε (u ε) = 0` near `r_*`, and it is the only continuous branch
through `(r_*, 0)`. -/
theorem exists_merge_solution {d : ℕ} (hd : 2 ≤ d) :
    ∃ u : ℝ → ℝ, u (rStar d) = 0 ∧ AnalyticAt ℝ u (rStar d) ∧
      (∀ᶠ ε in 𝓝 (rStar d), What d ε (u ε) = 0) ∧
      (∀ v : ℝ → ℝ, ContinuousAt v (rStar d) → v (rStar d) = 0 →
        (∀ᶠ ε in 𝓝 (rStar d), What d ε (v ε) = 0) →
        ∀ᶠ ε in 𝓝 (rStar d), v ε = u ε) := by
  have he0 : 0 < rStar d := rStar_pos hd
  have he1 : rStar d < 1 := rStar_lt_one hd
  -- the derivative in the unknown, and its nonvanishing
  obtain ⟨c, hderiv⟩ : ∃ c : ℝ, HasDerivAt (fun u : ℝ => What d (rStar d) u) c 0 :=
    ⟨_, hasDerivAt_What d he0 he1⟩
  have hcne : c ≠ 0 := by
    have hcv : c = deriv (fun u : ℝ => What d (rStar d) u) 0 := hderiv.deriv.symm
    rw [hcv]
    exact ne_of_lt (deriv_What_rStar_neg hd)
  have hcd : ContDiffAt ℝ 1 (fun u : ℝ => What d (rStar d) u) 0 :=
    (analyticAt_What_snd d he0 he1).contDiffAt
  have hstrict : HasStrictDerivAt (fun u : ℝ => What d (rStar d) u) c 0 :=
    hcd.hasStrictDerivAt' hderiv (by norm_num)
  -- joint analyticity in the order `(unknown, parameter)`
  have hswap : AnalyticAt ℝ (fun w : ℝ × ℝ => ((w.2, w.1) : ℝ × ℝ)) ((0 : ℝ), rStar d) :=
    AnalyticAt.prod analyticAt_snd analyticAt_fst
  have hF : AnalyticAt ℝ (fun w : ℝ × ℝ => What d w.2 w.1) ((0 : ℝ), rStar d) := by
    have hg : AnalyticAt ℝ (fun w : ℝ × ℝ => What d w.1 w.2)
        ((fun w : ℝ × ℝ => ((w.2, w.1) : ℝ × ℝ)) ((0 : ℝ), rStar d)) :=
      analyticAt_What d he0 he1
    have h := AnalyticAt.comp (g := fun w : ℝ × ℝ => What d w.1 w.2)
      (f := fun w : ℝ × ℝ => ((w.2, w.1) : ℝ × ℝ)) (x := (((0 : ℝ), rStar d) : ℝ × ℝ)) hg hswap
    simpa [Function.comp_def] using h
  have hL : HasStrictFDerivAt (fun z : ℝ => What d (rStar d) z)
      ((mulCLE hcne : ℝ →L[ℝ] ℝ)) 0 := by
    rw [mulCLE_coe hcne]
    exact hstrict.hasStrictFDerivAt
  obtain ⟨u, hu0, husol, huan, huniq⟩ :=
    analytic_implicit_locally_unique (F := fun (z : ℝ) (p : ℝ) => What d p z) hF
      (What_rStar_zero hd) (mulCLE hcne) hL
  exact ⟨u, hu0, huan, husol, huniq⟩

end UpperTailOptimizers
