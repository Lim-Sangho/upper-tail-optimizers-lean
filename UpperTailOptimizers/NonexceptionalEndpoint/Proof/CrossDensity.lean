import UpperTailOptimizers.Preliminaries.KRRSBipodality.GapQuadratic
import UpperTailOptimizers.LZBoundary.Curve

/-!
# The limiting cross density is the second contact density

`rmk:bipodal-parameter-expansions` of `paper/paper.tex` observes that the KRR–S limiting cross
density `ζ_d(r)` of `thm:krrs-cross-density` and the second contact density `sm(r)` of the
Lubetzky–Zhao supporting line of Theorem 3.1 coincide, and that `ζ_2(r) = 1 - r`.

* `zetaFun_eq_smGlobal` — `ζ_d(r) = sm(r)` for every `r ∈ (0,1)`.  The paper states it for
  `r ≠ r_*`; at `r = r_*` both sides equal `r_*` (`zetaFun_rStar`, `smGlobal_rStar`).
* `zetaFun_two` — `ζ_2(r) = 1 - r` for every `r ∈ (0,1)`.

The proof of the first identity follows the remark.  With `β = J'_{pc(r)}(r)/(d r^{d-1})`, the
supporting cost gap is `g_r(z) = -𝒟_r(z)(ψ_d(r,z) + β)` for `z ≠ r`, because `J_{pc(r)} + 2S₀` is
affine.  Since `g_r ≥ 0` and `𝒟_r(z) > 0`, `ψ_d(r,z) ≤ -β`, with equality at `z = sm(r)`; the
maximizer of `ψ_d(r,·)` off the diagonal is unique (`psiD_lt_psiStar`), so `sm(r) = ζ_d(r)`.
-/

namespace UpperTailOptimizers

open Real Set

/-- **`J_p + 2S₀` is affine.**  On `(0,1)`, the first-order Taylor remainder of `J_p` at `r` is
minus the entropy remainder: `J_p(z) - J_p(r) - J_p'(r)(z-r) = -𝒩_r(z)`. -/
theorem Jp_sub_tangent_eq_neg_Nfun {p r z : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hr0 : 0 < r) (hr1 : r < 1) (hz0 : 0 < z) (hz1 : z < 1) :
    Jp p z - Jp p r - Jp' p r * (z - r) = -Nfun r z := by
  have hp1' : (1:ℝ) - p ≠ 0 := by linarith
  have hr1' : (1:ℝ) - r ≠ 0 := by linarith
  have hz1' : (1:ℝ) - z ≠ 0 := by linarith
  unfold Jp Jp' Nfun S0 dS0
  rw [shannonH_eq, shannonH_eq, Real.log_div hz0.ne' hp0.ne', Real.log_div hz1' hp1',
    Real.log_div hr0.ne' hp0.ne', Real.log_div hr1' hp1',
    Real.log_div (mul_ne_zero hr0.ne' hp1') (mul_ne_zero hr1' hp0.ne'),
    Real.log_mul hr0.ne' hp1', Real.log_mul hr1' hp0.ne']
  ring

/-- **`ζ_d(r) = sm(r)`** (`rmk:bipodal-parameter-expansions`): the KRR–S limiting cross density
is the second contact density of the Lubetzky–Zhao supporting line. -/
theorem zetaFun_eq_smGlobal {d : ℕ} (hd : 2 ≤ d) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    zetaFun d r = smGlobal d r := by
  by_cases hrs : r = rStar d
  · subst hrs
    rw [zetaFun_rStar hd, smGlobal_rStar hd]
  obtain ⟨M, hrU, -⟩ := lz_boundary_arcs hd hr0 hr1 hrs
  rw [smGlobal_eq_sm hd M hrU]
  obtain ⟨hpc0, hpcr, -, hsmne, hsm0, hsm1⟩ := M.ordering r hrU
  have hpc1 : M.pc r < 1 := lt_trans hpcr hr1
  have hden : (d : ℝ) * r ^ (d - 1) ≠ 0 := (mul_pos (dpos hd) (pow_pos hr0 _)).ne'
  -- the supporting slope `β`, with `J_p'(r) = β d r^{d-1}`
  have hJ' : Jp' (M.pc r) r = slope d M.pc r * ((d : ℝ) * r ^ (d - 1)) := by
    unfold slope
    field_simp
  -- the supporting cost gap is `-(𝒩_r(z) + β 𝒟_r(z))`
  have hgap : ∀ z ∈ Ioo (0:ℝ) 1,
      Jp (M.pc r) z - (Jp (M.pc r) r + slope d M.pc r * (z ^ d - r ^ d))
        = -(Nfun r z + slope d M.pc r * Dfun d r z) := by
    intro z hz
    have h := Jp_sub_tangent_eq_neg_Nfun hpc0 hpc1 hr0 hr1 hz.1 hz.2
    rw [hJ'] at h
    unfold Dfun
    linear_combination h
  -- hence `ψ_d(r,z) ≤ -β` off the diagonal
  have hle : ∀ z ∈ Ioo (0:ℝ) 1, z ≠ r → psiD d r z ≤ -slope d M.pc r := by
    intro z hz hzr
    have hD := Dfun_pos hd hr0 hz.1.le hzr
    have hs := M.supporting r hrU z ⟨hz.1.le, hz.2.le⟩
    have hg := hgap z hz
    unfold psiD
    rw [div_le_iff₀ hD]
    linarith
  -- with equality at the second contact
  have heq : psiD d r (M.sm r) = -slope d M.pc r := by
    have hD := Dfun_pos hd hr0 hsm0.le hsmne
    have hs := M.secondContact r hrU
    have hg := hgap (M.sm r) ⟨hsm0, hsm1⟩
    unfold psiD
    rw [div_eq_iff hD.ne']
    linarith
  -- uniqueness of the off-diagonal maximizer
  by_contra hne
  have hrI : r ∈ Ioo (0:ℝ) 1 := ⟨hr0, hr1⟩
  have hlt := psiD_lt_psiStar hd hrI ⟨hsm0, hsm1⟩ hsmne (Ne.symm hne)
  have hz := hle (zetaFun d r) (zetaFun_mem hd hrI) (zetaFun_ne_self hd hrI hrs)
  unfold psiStar at hlt
  linarith

/-- **`ζ_2(r) = 1 - r`** (`rmk:bipodal-parameter-expansions`), from `S₀(1-r) = S₀(r)` and
`S₀'(1-r) = -S₀'(r)`. -/
theorem zetaFun_two {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) : zetaFun 2 r = 1 - r := by
  have hrs2 : rStar 2 = 1 / 2 := by unfold rStar; norm_num
  by_cases hh : r = 1 / 2
  · subst hh
    rw [← hrs2, zetaFun_rStar le_rfl, hrs2]
    norm_num
  refine (zetaFun_eq_of_crit le_rfl ⟨hr0, hr1⟩ ⟨by linarith, by linarith⟩
    (fun h => hh (by linarith)) ?_).symm
  have hH : shannonH (1 - r) = shannonH r := by
    rw [shannonH_eq, shannonH_eq, sub_sub_cancel]
    ring
  simp only [Wr, dN, Dfun, Nfun, dD, S0, dS0, hH, sub_sub_cancel]
  norm_num
  ring

end UpperTailOptimizers
