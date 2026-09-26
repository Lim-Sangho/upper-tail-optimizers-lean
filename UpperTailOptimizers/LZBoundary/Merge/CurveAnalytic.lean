import UpperTailOptimizers.LZBoundary.Merge.ZetaAnalytic
import UpperTailOptimizers.LZBoundary.DensityGap
import UpperTailOptimizers.NonexceptionalEndpoint.Proof.CrossDensity

/-!
# (M1) at the exceptional density: `pc` and `sc` are analytic through `r_*`

This file completes condition (M1) of `thm:lz-boundary`: the boundary curve `pc` and the second
contact density `sc` are real-analytic on **all** of `(0,1)`, the exceptional density included.

Two steps.

* `analyticAt_scGlobal_rStar`.  The second contact is the Kenyon–Radin–Ren–Sadun selector
  (`zetaFun_eq_scGlobal`), i.e. a critical point of `ψ_d(ε,·)`, so `ε ↦ scGlobal d ε - ε` is a
  continuous branch of solutions of the normalised equation `What d ε u = 0` through `(r_*, 0)`.
  By the uniqueness clause of `exists_merge_solution` it coincides with the analytic branch.
* `analyticAt_pcGlobal_rStar`.  Tangency at the second contact (`gapD1_contact`) is the
  equal-slope identity `J_p'(s)r^{d-1} = J_p'(r)s^{d-1}`.  Writing `s = r + w` and splitting off
  the common factor `w` — with `logQuot` for the logarithmic difference quotient and `polyR` for
  the polynomial one — turns it into an equation `G(p, r) = 0` that is nondegenerate in `p` at
  `(p_*, r_*)`; the analytic implicit function theorem then gives the analyticity of `pc`.

The nondegeneracy inputs are `deriv_What_rStar_neg` for `sc` and `polyR_zero` (i.e.
`(d-1)r_*^{d-2} ≠ 0`) for `pc`.
-/

namespace UpperTailOptimizers

open Filter Topology

/-! ### The second contact -/

/-- **The analytic branch through the merged contact, identified with `sc`.**  Near `r_*`,
`s_c(ε) = ε + u ε` for an analytic `u` vanishing at `r_*`. -/
theorem exists_scGlobal_branch {d : ℕ} (hd : 2 ≤ d) :
    ∃ u : ℝ → ℝ, u (rStar d) = 0 ∧ AnalyticAt ℝ u (rStar d) ∧
      (∀ᶠ ε in 𝓝 (rStar d), scGlobal d ε = ε + u ε) := by
  obtain ⟨u, hu0, huan, husol, huniq⟩ := exists_merge_solution hd
  have hrmem : rStar d ∈ Set.Ioo (0 : ℝ) 1 := rStar_mem_Ioo hd
  have hscc : ContinuousAt (scGlobal d) (rStar d) := continuousAt_scGlobal_rStar hd
  have hvc : ContinuousAt (fun ε => scGlobal d ε - ε) (rStar d) := hscc.sub continuousAt_id
  have hv0 : (fun ε => scGlobal d ε - ε) (rStar d) = 0 := by
    simp [scGlobal_rStar hd]
  have hvsol : ∀ᶠ ε in 𝓝 (rStar d), What d ε (scGlobal d ε - ε) = 0 := by
    have hIoo : ∀ᶠ ε in 𝓝 (rStar d), ε ∈ Set.Ioo (0 : ℝ) 1 :=
      Ioo_mem_nhds hrmem.1 hrmem.2
    filter_upwards [hIoo] with ε hε
    by_cases hexc : ε = rStar d
    · subst hexc
      simpa [scGlobal_rStar hd] using What_rStar_zero hd
    · have hsc := scGlobal_mem_Ioo hd hε.1 hε.2
      have hne : scGlobal d ε ≠ ε := by
        rw [← zetaFun_eq_scGlobal hd hε.1 hε.2]
        exact zetaFun_ne_self hd hε hexc
      have hw : scGlobal d ε - ε ≠ 0 := sub_ne_zero_of_ne hne
      have hzero : Wr d ε (scGlobal d ε) = 0 := by
        rw [← zetaFun_eq_scGlobal hd hε.1 hε.2]
        exact zetaFun_Wr_eq_zero hd hε
      have hshift := Wr_shift hd hε.1 hε.2
        (show 0 < ε + (scGlobal d ε - ε) by simpa using hsc.1)
        (show ε + (scGlobal d ε - ε) < 1 by simpa using hsc.2)
      rw [show ε + (scGlobal d ε - ε) = scGlobal d ε by ring, hzero] at hshift
      rcases mul_eq_zero.mp hshift.symm with h | h
      · exact absurd (pow_eq_zero_iff (n := 4) (by norm_num) |>.mp h) hw
      · exact h
  have heq := huniq (fun ε => scGlobal d ε - ε) hvc hv0 hvsol
  refine ⟨u, hu0, huan, ?_⟩
  filter_upwards [heq] with ε hε
  have hval : scGlobal d ε - ε = u ε := hε
  linarith

/-- **`sc` is analytic at the exceptional density.** -/
theorem analyticAt_scGlobal_rStar {d : ℕ} (hd : 2 ≤ d) :
    AnalyticAt ℝ (scGlobal d) (rStar d) := by
  obtain ⟨u, -, huan, hsc⟩ := exists_scGlobal_branch hd
  have hsc' : (fun ε : ℝ => ε + u ε) =ᶠ[𝓝 (rStar d)] scGlobal d := by
    filter_upwards [hsc] with ε hε
    exact hε.symm
  exact ((analyticAt_id).add huan).congr hsc'

/-! ### The polynomial difference quotient -/

/-- `((r+w)^{d-1} - r^{d-1})/w`, as a polynomial. -/
noncomputable def polyR (d : ℕ) (r w : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (d - 1), (r + w) ^ i * r ^ (d - 1 - 1 - i)

/-- `(r+w)^{d-1} - r^{d-1} = w · polyR d r w`. -/
theorem polyR_spec (d : ℕ) (r w : ℝ) :
    (r + w) ^ (d - 1) - r ^ (d - 1) = w * polyR d r w := by
  have h := (Commute.all (r + w) r).geom_sum₂_mul (d - 1)
  unfold polyR
  rw [show r + w - r = w by ring] at h
  rw [mul_comm]
  exact h.symm

/-- `polyR d r 0 = (d-1) r^{d-2}`. -/
theorem polyR_zero {d : ℕ} (hd : 2 ≤ d) (r : ℝ) :
    polyR d r 0 = ((d : ℝ) - 1) * r ^ (d - 2) := by
  have hcast : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
    have h1 : (1 : ℕ) ≤ d := le_trans (by norm_num) hd
    push_cast [Nat.cast_sub h1]
    ring
  have hterm : ∀ i ∈ Finset.range (d - 1),
      (r + 0) ^ i * r ^ (d - 1 - 1 - i) = r ^ (d - 2) := by
    intro i hi
    have hi' : i < d - 1 := Finset.mem_range.mp hi
    have hexp : i + (d - 1 - 1 - i) = d - 2 := by omega
    rw [add_zero, ← pow_add, hexp]
  unfold polyR
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul, hcast]

/-- `polyR` is jointly analytic. -/
theorem analyticAt_polyR (d : ℕ) (q : ℝ × ℝ) :
    AnalyticAt ℝ (fun v : ℝ × ℝ => polyR d v.1 v.2) q := by
  unfold polyR
  refine Finset.analyticAt_fun_sum _ fun i _ => ?_
  exact ((analyticAt_fst.add analyticAt_snd).pow i).mul (analyticAt_fst.pow _)

/-! ### The logarithmic difference quotient -/

/-- The scalar log-odds of a density, `lamD z = log z - log (1 - z)`. -/
noncomputable def lamD (z : ℝ) : ℝ := Real.log z - Real.log (1 - z)

/-- `(lamD (r + w) - lamD r)/w`, filled analytically by `logQuot`. -/
noncomputable def lamQ (r w : ℝ) : ℝ :=
  logQuot (w / r) / r + logQuot (-(w / (1 - r))) / (1 - r)

/-- `lamD (r + w) - lamD r = w · lamQ r w`. -/
theorem lamQ_spec {r w : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (h0 : 0 < r + w) (h1 : r + w < 1) :
    lamD (r + w) - lamD r = w * lamQ r w := by
  have hrne : r ≠ 0 := ne_of_gt hr0
  have h1r : (0 : ℝ) < 1 - r := by linarith
  have h1rne : (1 : ℝ) - r ≠ 0 := ne_of_gt h1r
  have hx1 : (-1 : ℝ) < w / r := by rw [lt_div_iff₀ hr0]; linarith
  have hx2 : (-1 : ℝ) < -(w / (1 - r)) := by
    rw [neg_lt_neg_iff, div_lt_one h1r]; linarith
  have hpos1 : (0 : ℝ) < 1 + w / r := by linarith
  have hpos2 : (0 : ℝ) < 1 + -(w / (1 - r)) := by linarith
  have hlog1 : Real.log (r + w) - Real.log r = w / r * logQuot (w / r) := by
    have hA : r + w = r * (1 + w / r) := by field_simp
    rw [hA, Real.log_mul hrne (ne_of_gt hpos1), log_one_add_eq_mul_logQuot hx1]
    ring
  have hlog2 : Real.log (1 - (r + w)) - Real.log (1 - r)
      = -(w / (1 - r)) * logQuot (-(w / (1 - r))) := by
    have hB : 1 - (r + w) = (1 - r) * (1 + -(w / (1 - r))) := by field_simp; ring
    rw [hB, Real.log_mul h1rne (ne_of_gt hpos2), log_one_add_eq_mul_logQuot hx2]
    ring
  unfold lamD lamQ
  rw [show Real.log (r + w) - Real.log (1 - (r + w)) - (Real.log r - Real.log (1 - r))
      = (Real.log (r + w) - Real.log r) - (Real.log (1 - (r + w)) - Real.log (1 - r)) by ring,
    hlog1, hlog2]
  field_simp
  ring

/-- `lamQ` is jointly analytic at `(r, 0)` for `0 < r < 1`. -/
theorem analyticAt_lamQ {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    AnalyticAt ℝ (fun v : ℝ × ℝ => lamQ v.1 v.2) (r, 0) := by
  have hrne : r ≠ 0 := ne_of_gt hr0
  have h1rne : (1 : ℝ) - r ≠ 0 := ne_of_gt (by linarith)
  have hfst : AnalyticAt ℝ (fun v : ℝ × ℝ => v.1) (r, 0) := analyticAt_fst
  have hsnd : AnalyticAt ℝ (fun v : ℝ × ℝ => v.2) (r, 0) := analyticAt_snd
  have hinner1 : AnalyticAt ℝ (fun v : ℝ × ℝ => v.2 / v.1) (r, 0) := hsnd.div hfst hrne
  have hinner2 : AnalyticAt ℝ (fun v : ℝ × ℝ => -(v.2 / (1 - v.1))) (r, 0) :=
    (hsnd.div (analyticAt_const.sub hfst) h1rne).neg
  have hcomp1 : AnalyticAt ℝ (fun v : ℝ × ℝ => logQuot (v.2 / v.1)) (r, 0) := by
    have hg : AnalyticAt ℝ logQuot ((fun v : ℝ × ℝ => v.2 / v.1) (r, 0)) := by
      simpa using analyticAt_logQuot
    have h := AnalyticAt.comp (g := logQuot) (f := fun v : ℝ × ℝ => v.2 / v.1)
      (x := ((r, 0) : ℝ × ℝ)) hg hinner1
    simpa [Function.comp_def] using h
  have hcomp2 : AnalyticAt ℝ (fun v : ℝ × ℝ => logQuot (-(v.2 / (1 - v.1)))) (r, 0) := by
    have hg : AnalyticAt ℝ logQuot ((fun v : ℝ × ℝ => -(v.2 / (1 - v.1))) (r, 0)) := by
      simpa using analyticAt_logQuot
    have h := AnalyticAt.comp (g := logQuot) (f := fun v : ℝ × ℝ => -(v.2 / (1 - v.1)))
      (x := ((r, 0) : ℝ × ℝ)) hg hinner2
    simpa [Function.comp_def] using h
  exact (hcomp1.div hfst hrne).add (hcomp2.div (analyticAt_const.sub hfst) h1rne)

/-- `lamQ r 0 = 1/(r(1-r))`. -/
theorem lamQ_zero {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) : lamQ r 0 = 1 / (r * (1 - r)) := by
  have hrne : r ≠ 0 := ne_of_gt hr0
  have h1rne : (1 : ℝ) - r ≠ 0 := ne_of_gt (by linarith)
  unfold lamQ
  simp only [zero_div, neg_zero, logQuot_zero]
  field_simp
  ring

/-- `J_p'` splits into a density part and a log-odds part. -/
theorem Jp'_eq_lamD_add {p z : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hz0 : 0 < z) (hz1 : z < 1) :
    Jp' p z = lamD z + (Real.log (1 - p) - Real.log p) := by
  have h1z : (0 : ℝ) < 1 - z := by linarith
  have h1p : (0 : ℝ) < 1 - p := by linarith
  unfold Jp' lamD
  rw [Real.log_div (by positivity) (by positivity), Real.log_mul (ne_of_gt hz0) (ne_of_gt h1p),
    Real.log_mul (ne_of_gt h1z) (ne_of_gt hp0)]
  ring

/-! ### The boundary curve -/

/-- `log(1 - p_*) - log p_* = d/(d-1) - log(d-1)`. -/
private theorem log_odds_pStar {d : ℕ} (hd : 2 ≤ d) :
    Real.log (1 - pStar d) - Real.log (pStar d)
      = (d : ℝ) / ((d : ℝ) - 1) - Real.log ((d : ℝ) - 1) := by
  have hd1 : (1 : ℝ) < (d : ℝ) := one_lt_d hd
  have hE : (0 : ℝ) < Real.exp ((d : ℝ) / ((d : ℝ) - 1)) := Real.exp_pos _
  have hS : (0 : ℝ) < ((d : ℝ) - 1) + Real.exp ((d : ℝ) / ((d : ℝ) - 1)) := by linarith
  have hp : pStar d = ((d : ℝ) - 1) / (((d : ℝ) - 1) + Real.exp ((d : ℝ) / ((d : ℝ) - 1))) := rfl
  have h1p : 1 - pStar d
      = Real.exp ((d : ℝ) / ((d : ℝ) - 1))
        / (((d : ℝ) - 1) + Real.exp ((d : ℝ) / ((d : ℝ) - 1))) := by
    rw [hp]; field_simp; ring
  rw [h1p, hp, Real.log_div (ne_of_gt hE) (ne_of_gt hS),
    Real.log_div (by linarith) (ne_of_gt hS), Real.log_exp]
  ring

/-- `lamD r_* = log (d-1)`. -/
private theorem lamD_rStar {d : ℕ} (hd : 2 ≤ d) : lamD (rStar d) = Real.log ((d : ℝ) - 1) := by
  have hd0 : (0 : ℝ) < (d : ℝ) := dpos hd
  have hd1 : (1 : ℝ) < (d : ℝ) := one_lt_d hd
  have hr : rStar d = ((d : ℝ) - 1) / (d : ℝ) := rfl
  have h1r : (1 : ℝ) - rStar d = 1 / (d : ℝ) := by rw [hr]; field_simp; ring
  unfold lamD
  rw [h1r, hr, Real.log_div (by linarith) (ne_of_gt hd0),
    Real.log_div one_ne_zero (ne_of_gt hd0), Real.log_one]
  ring

/-- **`pc` is analytic at the exceptional density.** -/
theorem analyticAt_pcGlobal_rStar {d : ℕ} (hd : 2 ≤ d) :
    AnalyticAt ℝ (pcGlobal d) (rStar d) := by
  obtain ⟨u, hu0, huan, hsc⟩ := exists_scGlobal_branch hd
  have hrmem : rStar d ∈ Set.Ioo (0 : ℝ) 1 := rStar_mem_Ioo hd
  have hd0 : (0 : ℝ) < (d : ℝ) := dpos hd
  have hd1 : (1 : ℝ) < (d : ℝ) := one_lt_d hd
  have hr0 : 0 < rStar d := rStar_pos hd
  have hr1 : rStar d < 1 := rStar_lt_one hd
  have hp0 : 0 < pStar d := pStar_pos hd
  have hp1 : pStar d < 1 := pStar_lt_one hd
  -- the normalised equal-slope equation
  set F : ℝ → ℝ → ℝ := fun p r =>
    lamQ r (u r) * r ^ (d - 1)
      - (lamD r + (Real.log (1 - p) - Real.log p)) * polyR d r (u r) with hFdef
  -- the base point
  have hCpos : 0 < polyR d (rStar d) (u (rStar d)) := by
    rw [hu0, polyR_zero hd]
    have : (0 : ℝ) < (d : ℝ) - 1 := by linarith
    positivity
  have hF0 : F (pStar d) (rStar d) = 0 := by
    rw [hFdef]
    simp only
    rw [hu0, lamQ_zero hr0 hr1, polyR_zero hd, lamD_rStar hd, log_odds_pStar hd]
    have hpow : rStar d ^ (d - 1) = rStar d ^ (d - 2) * rStar d := by
      rw [← pow_succ]
      congr 1
      omega
    have hsub : (1 : ℝ) - rStar d = 1 / (d : ℝ) := by
      rw [show rStar d = ((d : ℝ) - 1) / (d : ℝ) from rfl]; field_simp; ring
    have hlogcancel : Real.log ((d : ℝ) - 1)
        + ((d : ℝ) / ((d : ℝ) - 1) - Real.log ((d : ℝ) - 1)) = (d : ℝ) / ((d : ℝ) - 1) := by
      ring
    have hene : rStar d ≠ 0 := ne_of_gt hr0
    have hDne : (d : ℝ) ≠ 0 := ne_of_gt hd0
    have hD1ne : (d : ℝ) - 1 ≠ 0 := by linarith
    rw [hpow, hsub, hlogcancel]
    field_simp
    ring
  -- the derivative in the unknown `p`
  have hlog : HasDerivAt (fun p : ℝ => Real.log (1 - p) - Real.log p)
      (-(1 - pStar d)⁻¹ - (pStar d)⁻¹) (pStar d) := by
    have h1 : HasDerivAt (fun p : ℝ => Real.log (1 - p)) (-(1 - pStar d)⁻¹) (pStar d) := by
      have hinner : HasDerivAt (fun p : ℝ => 1 - p) (-1) (pStar d) := by
        simpa using (hasDerivAt_id (pStar d)).const_sub 1
      have hout : HasDerivAt Real.log ((1 - pStar d)⁻¹) (1 - pStar d) :=
        Real.hasDerivAt_log (by linarith)
      have h := hout.comp (pStar d) hinner
      simpa [Function.comp_def] using h
    exact h1.sub (Real.hasDerivAt_log (ne_of_gt hp0))
  set c : ℝ := -(-(1 - pStar d)⁻¹ - (pStar d)⁻¹) * polyR d (rStar d) (u (rStar d)) with hcdef
  have hFderiv : HasDerivAt (fun p : ℝ => F p (rStar d)) c (pStar d) := by
    rw [hFdef, hcdef]
    simp only
    have hmul := ((hasDerivAt_const (pStar d) (lamD (rStar d))).add hlog).mul_const
      (polyR d (rStar d) (u (rStar d)))
    have hconst : HasDerivAt
        (fun _ : ℝ => lamQ (rStar d) (u (rStar d)) * rStar d ^ (d - 1)) 0 (pStar d) :=
      hasDerivAt_const _ _
    exact (hconst.sub hmul).congr_deriv (by ring)
  have hcne : c ≠ 0 := by
    rw [hcdef]
    have h1 : (0 : ℝ) < (1 - pStar d)⁻¹ := by
      have : (0 : ℝ) < 1 - pStar d := by linarith
      positivity
    have h2 : (0 : ℝ) < (pStar d)⁻¹ := by positivity
    have : 0 < -(-(1 - pStar d)⁻¹ - (pStar d)⁻¹) := by linarith
    exact ne_of_gt (mul_pos this hCpos)
  -- joint analyticity
  have hsndc : ∀ {g : ℝ → ℝ}, AnalyticAt ℝ g (rStar d) →
      AnalyticAt ℝ (fun w : ℝ × ℝ => g w.2) (((pStar d : ℝ), rStar d) : ℝ × ℝ) := by
    intro g hg
    have h := AnalyticAt.comp (g := g) (f := fun w : ℝ × ℝ => w.2)
      (x := (((pStar d : ℝ), rStar d) : ℝ × ℝ)) (by simpa using hg) analyticAt_snd
    simpa [Function.comp_def] using h
  have hupair : AnalyticAt ℝ (fun r : ℝ => ((r, u r) : ℝ × ℝ)) (rStar d) :=
    AnalyticAt.prod analyticAt_id huan
  have hLQ : AnalyticAt ℝ (fun r : ℝ => lamQ r (u r)) (rStar d) := by
    have hg : AnalyticAt ℝ (fun v : ℝ × ℝ => lamQ v.1 v.2)
        ((fun r : ℝ => ((r, u r) : ℝ × ℝ)) (rStar d)) := by
      rw [show ((fun r : ℝ => ((r, u r) : ℝ × ℝ)) (rStar d)) = ((rStar d, (0 : ℝ)) : ℝ × ℝ) by
        simp [hu0]]
      exact analyticAt_lamQ hr0 hr1
    have h := AnalyticAt.comp (g := fun v : ℝ × ℝ => lamQ v.1 v.2)
      (f := fun r : ℝ => ((r, u r) : ℝ × ℝ)) (x := rStar d) hg hupair
    simpa [Function.comp_def] using h
  have hPR : AnalyticAt ℝ (fun r : ℝ => polyR d r (u r)) (rStar d) := by
    have h := AnalyticAt.comp (g := fun v : ℝ × ℝ => polyR d v.1 v.2)
      (f := fun r : ℝ => ((r, u r) : ℝ × ℝ)) (x := rStar d) (analyticAt_polyR d _) hupair
    simpa [Function.comp_def] using h
  have hlamDan : AnalyticAt ℝ lamD (rStar d) := by
    unfold lamD
    exact (analyticAt_log hr0).sub
      (analyticAt_log_comp (analyticAt_const.sub analyticAt_id) (by linarith))
  have hFan : AnalyticAt ℝ (fun w : ℝ × ℝ => F w.1 w.2) (((pStar d : ℝ), rStar d) : ℝ × ℝ) := by
    rw [hFdef]
    simp only
    have hlogp : AnalyticAt ℝ (fun w : ℝ × ℝ => Real.log (1 - w.1) - Real.log w.1)
        (((pStar d : ℝ), rStar d) : ℝ × ℝ) := by
      refine (analyticAt_log_comp (analyticAt_const.sub analyticAt_fst)
          (by show (0 : ℝ) < 1 - pStar d; linarith)).sub
        (analyticAt_log_comp analyticAt_fst (by show (0 : ℝ) < pStar d; exact hp0))
    exact ((hsndc hLQ).mul (analyticAt_snd.pow _)).sub
      (((hsndc hlamDan).add hlogp).mul (hsndc hPR))
  have hL : HasStrictFDerivAt (fun p : ℝ => F p (rStar d)) ((mulCLE hcne : ℝ →L[ℝ] ℝ))
      (pStar d) := by
    rw [mulCLE_coe hcne]
    have hcd : ContDiffAt ℝ 1 (fun p : ℝ => F p (rStar d)) (pStar d) := by
      have hpair : AnalyticAt ℝ (fun p : ℝ => ((p, rStar d) : ℝ × ℝ)) (pStar d) :=
        AnalyticAt.prod analyticAt_id analyticAt_const
      have h := AnalyticAt.comp (g := fun w : ℝ × ℝ => F w.1 w.2)
        (f := fun p : ℝ => ((p, rStar d) : ℝ × ℝ)) (x := pStar d) (by simpa using hFan) hpair
      exact (by simpa [Function.comp_def] using h : AnalyticAt ℝ _ _).contDiffAt
    exact (hcd.hasStrictDerivAt' hFderiv (by norm_num)).hasStrictFDerivAt
  obtain ⟨P, hP0, hPsol, hPan, hPuniq⟩ :=
    analytic_implicit_locally_unique (F := F) hFan hF0 (mulCLE hcne) hL
  -- `pcGlobal` is a continuous branch through the same base point
  have hpcsol : ∀ᶠ r in 𝓝 (rStar d), F (pcGlobal d r) r = 0 := by
    have hIoo : ∀ᶠ r in 𝓝 (rStar d), r ∈ Set.Ioo (0 : ℝ) 1 := Ioo_mem_nhds hrmem.1 hrmem.2
    filter_upwards [hIoo, hsc] with r hr hscr
    by_cases hexc : r = rStar d
    · subst hexc
      rw [pcGlobal_rStar hd]
      exact hF0
    · have hs := scGlobal_mem_Ioo hd hr.1 hr.2
      have hne : scGlobal d r ≠ r := by
        rw [← zetaFun_eq_scGlobal hd hr.1 hr.2]
        exact zetaFun_ne_self hd hr hexc
      have hw : u r ≠ 0 := by
        intro h
        rw [h, add_zero] at hscr
        exact hne hscr
      obtain ⟨hpc0', hple⟩ := pcGlobal_pos_le hd hr.1 hr.2
      have hpc1 : pcGlobal d r < 1 := lt_of_le_of_lt hple (pStar_lt_one hd)
      -- tangency at the second contact
      have htan : gapD1 d r (scGlobal d r) = 0 :=
        gapD1_contact hd hr.1 hr.2 hexc (Or.inr rfl)
      have hrpow : (0 : ℝ) < (d : ℝ) * r ^ (d - 1) := by
        have : (0 : ℝ) < r ^ (d - 1) := pow_pos hr.1 _
        positivity
      -- the equal-slope identity
      have heqs : Jp' (pcGlobal d r) (scGlobal d r) * r ^ (d - 1)
          = Jp' (pcGlobal d r) r * scGlobal d r ^ (d - 1) := by
        have hne1 : r ^ (d - 1) ≠ 0 := ne_of_gt (pow_pos hr.1 _)
        have hdne : (d : ℝ) ≠ 0 := ne_of_gt hd0
        unfold gapD1 slope at htan
        have h1 : Jp' (pcGlobal d r) (scGlobal d r)
            = Jp' (pcGlobal d r) r / ((d : ℝ) * r ^ (d - 1))
              * ((d : ℝ) * scGlobal d r ^ (d - 1)) := by linarith [htan]
        rw [h1]
        field_simp
      -- rewrite with the two difference quotients
      have hJs := Jp'_eq_lamD_add hpc0' hpc1 hs.1 hs.2
      have hJr := Jp'_eq_lamD_add hpc0' hpc1 hr.1 hr.2
      have hlamq := lamQ_spec hr.1 hr.2 (by rw [← hscr]; exact hs.1) (by rw [← hscr]; exact hs.2)
      have hpolyr := polyR_spec d r (u r)
      rw [hFdef]
      simp only
      rw [hscr] at heqs hJs
      rw [hJs, hJr] at heqs
      have hlam : lamD (r + u r) = lamD r + u r * lamQ r (u r) := by linarith [hlamq]
      have hpw : (r + u r) ^ (d - 1) = r ^ (d - 1) + u r * polyR d r (u r) := by linarith [hpolyr]
      rw [hlam, hpw] at heqs
      have hkey : u r * (lamQ r (u r) * r ^ (d - 1)
          - (lamD r + (Real.log (1 - pcGlobal d r) - Real.log (pcGlobal d r)))
            * polyR d r (u r)) = 0 := by nlinarith [heqs]
      rcases mul_eq_zero.mp hkey with h | h
      · exact absurd h hw
      · exact h
  have heq := hPuniq (pcGlobal d) (continuousAt_pcGlobal_rStar hd) (pcGlobal_rStar hd) hpcsol
  have hform : P =ᶠ[𝓝 (rStar d)] pcGlobal d := by
    filter_upwards [heq] with r hr
    exact hr.symm
  exact hPan.congr hform

/-! ### (M1) in paper form -/

/-- **`pc` is analytic on all of `(0,1)`.** -/
theorem analyticOnNhd_pcGlobal {d : ℕ} (hd : 2 ≤ d) :
    AnalyticOnNhd ℝ (pcGlobal d) (Set.Ioo 0 1) := by
  intro r hr
  by_cases hexc : r = rStar d
  · subst hexc
    exact analyticAt_pcGlobal_rStar hd
  · exact analyticAt_pcGlobal hd hr.1 hr.2 hexc

/-- **`sc` is analytic on all of `(0,1)`.** -/
theorem analyticOnNhd_scGlobal {d : ℕ} (hd : 2 ≤ d) :
    AnalyticOnNhd ℝ (scGlobal d) (Set.Ioo 0 1) := by
  intro r hr
  by_cases hexc : r = rStar d
  · subst hexc
    exact analyticAt_scGlobal_rStar hd
  · exact analyticAt_scGlobal hd hr.1 hr.2 hexc

/-- **The analyticity clause of (M1) of Theorem 3.1.**  The two boundary maps are real-analytic
on the whole of `(0,1)` — the exceptional density included — map it into `(0,1)`, and take the
values `p_c(r_*) = p_*`, `s_c(r_*) = r_*` there. -/
theorem lz_boundary_analytic {d : ℕ} (hd : 2 ≤ d) :
    AnalyticOnNhd ℝ (pcGlobal d) (Set.Ioo 0 1) ∧
      AnalyticOnNhd ℝ (scGlobal d) (Set.Ioo 0 1) ∧
      Set.MapsTo (pcGlobal d) (Set.Ioo 0 1) (Set.Ioo 0 1) ∧
      Set.MapsTo (scGlobal d) (Set.Ioo 0 1) (Set.Ioo 0 1) ∧
      pcGlobal d (rStar d) = pStar d ∧ scGlobal d (rStar d) = rStar d := by
  refine ⟨analyticOnNhd_pcGlobal hd, analyticOnNhd_scGlobal hd, ?_, ?_,
    pcGlobal_rStar hd, scGlobal_rStar hd⟩
  · intro r hr
    obtain ⟨h0, hle⟩ := pcGlobal_pos_le hd hr.1 hr.2
    exact ⟨h0, lt_of_le_of_lt hle (pStar_lt_one hd)⟩
  · intro r hr
    exact scGlobal_mem_Ioo hd hr.1 hr.2

end UpperTailOptimizers
