import UpperTailOptimizers.LZBoundary.Merge.Bennett
import UpperTailOptimizers.Preliminaries.KRRSAnalyticExtension.Reduced

/-!
# The entropy remainder at a merged contact: the `u²` factor

The analyticity of the boundary maps `pc` and `sc` **through** the exceptional density `r_*`
(condition (M1) of `thm:lz-boundary`) is proved by normalising the contact equations so that they
survive the coalescence of the two contacts.  In the density variable, the relevant equation is the
critical-point equation of the Kenyon–Radin–Ren–Sadun selector `ψ_d(ε,·) = 𝒩_ε/𝒟_ε`, whose
numerator and denominator both vanish to second order at `z = ε`.

Writing `z = ε + u`, this file splits off the double zero from the entropy remainder:

`𝒩_ε(ε + u) = u² · Qfun ε u`,   `Qfun ε u = -(bennett(u/ε)/ε + bennett(-u/(1-ε))/(1-ε))`,

where `bennett` is the filled quotient `((1+x)log(1+x) - x)/x²` of `Merge/Bennett.lean`.  Since
`bennett` is analytic at `0`, `Qfun` is **jointly analytic** in `(ε, u)` at every `(ε, 0)` with
`0 < ε < 1` — the whole point of the normalisation.  `Qfun1` and `Qfun2` are its first two
`u`-derivatives, and `Nfun_shift`, `dN_shift` record the two identities that the critical-point
equation needs.

The companion file `Merge/PolyPart.lean` does the same for the moment remainder `𝒟`, where the
cofactor is a polynomial.
-/

namespace UpperTailOptimizers

open Filter Topology

/-- `𝒩_ε(z) = -J_ε(z)`: the entropy remainder is minus the relative entropy. -/
theorem Nfun_eq_neg_Jp {ε z : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    Nfun ε z = -Jp ε z := by
  have hJ := Jp_eq_entIntegrand hε0 hε1 hz0 hz1
  unfold Nfun S0 dS0 shannonH
  rw [hJ]
  unfold entIntegrand
  ring

/-- The cofactor of the double zero of the entropy remainder at a merged contact. -/
noncomputable def Qfun (ε u : ℝ) : ℝ :=
  -(bennett (u / ε) / ε + bennett (-(u / (1 - ε))) / (1 - ε))

/-- The first `u`-derivative of `Qfun`. -/
noncomputable def Qfun1 (ε u : ℝ) : ℝ :=
  -(deriv bennett (u / ε) / ε ^ 2 - deriv bennett (-(u / (1 - ε))) / (1 - ε) ^ 2)

/-- The second `u`-derivative of `Qfun`. -/
noncomputable def Qfun2 (ε u : ℝ) : ℝ :=
  -(deriv (deriv bennett) (u / ε) / ε ^ 3
    + deriv (deriv bennett) (-(u / (1 - ε))) / (1 - ε) ^ 3)

/-- **The shift identity for the entropy remainder**: `𝒩_ε(ε + u) = u² Qfun ε u`. -/
theorem Nfun_shift {ε u : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (h0 : 0 < ε + u) (h1 : ε + u < 1) :
    Nfun ε (ε + u) = u ^ 2 * Qfun ε u := by
  have hεne : ε ≠ 0 := ne_of_gt hε0
  have h1ε : (0 : ℝ) < 1 - ε := by linarith
  have h1εne : (1 : ℝ) - ε ≠ 0 := ne_of_gt h1ε
  have hx : (-1 : ℝ) < u / ε := by rw [lt_div_iff₀ hε0]; linarith
  have hy : (-1 : ℝ) < -(u / (1 - ε)) := by rw [neg_lt_neg_iff, div_lt_one h1ε]; linarith
  have hxid := one_add_mul_log_eq hx
  have hyid := one_add_mul_log_eq hy
  have hterm1 : (ε + u) * Real.log ((ε + u) / ε) = u + u ^ 2 / ε * bennett (u / ε) := by
    have hA : (ε + u) / ε = 1 + u / ε := by field_simp
    have hεu : ε + u = ε * (1 + u / ε) := by field_simp
    rw [hA, hεu, show ε * (1 + u / ε) * Real.log (1 + u / ε)
        = ε * ((1 + u / ε) * Real.log (1 + u / ε)) by ring,
      show (1 + u / ε) * Real.log (1 + u / ε)
        = u / ε + (u / ε) ^ 2 * bennett (u / ε) by linarith]
    field_simp
  have hterm2 : (1 - (ε + u)) * Real.log ((1 - (ε + u)) / (1 - ε))
      = -u + u ^ 2 / (1 - ε) * bennett (-(u / (1 - ε))) := by
    have hB : (1 - (ε + u)) / (1 - ε) = 1 + -(u / (1 - ε)) := by field_simp; ring
    have h1εu : 1 - (ε + u) = (1 - ε) * (1 + -(u / (1 - ε))) := by field_simp; ring
    rw [hB, h1εu, show (1 - ε) * (1 + -(u / (1 - ε))) * Real.log (1 + -(u / (1 - ε)))
        = (1 - ε) * ((1 + -(u / (1 - ε))) * Real.log (1 + -(u / (1 - ε)))) by ring,
      show (1 + -(u / (1 - ε))) * Real.log (1 + -(u / (1 - ε)))
        = -(u / (1 - ε)) + (-(u / (1 - ε))) ^ 2 * bennett (-(u / (1 - ε))) by linarith]
    field_simp
  rw [Nfun_eq_neg_Jp hε0 hε1 h0.le h1.le]
  unfold Jp Qfun
  rw [hterm1, hterm2]
  field_simp
  ring

/-! ### `bennett` away from the origin -/

/-- `bennett` is analytic at **every** `x > -1`: at `0` by `analyticAt_bennett`, elsewhere because
the closed form is a quotient of analytic functions with nonvanishing denominator. -/
theorem analyticAt_bennett_of_gt {x : ℝ} (hx : -1 < x) : AnalyticAt ℝ bennett x := by
  rcases eq_or_ne x 0 with rfl | hne
  · exact analyticAt_bennett
  · have hlog : AnalyticAt ℝ (fun y : ℝ => Real.log (1 + y)) x :=
      analyticAt_log_comp (analyticAt_const.add analyticAt_id) (by linarith)
    have hnum : AnalyticAt ℝ (fun y : ℝ => (1 + y) * Real.log (1 + y) - y) x :=
      ((analyticAt_const.add analyticAt_id).mul hlog).sub analyticAt_id
    have hq : AnalyticAt ℝ (fun y : ℝ => ((1 + y) * Real.log (1 + y) - y) / y ^ 2) x :=
      hnum.div (analyticAt_id.pow 2) (pow_ne_zero 2 hne)
    refine hq.congr ?_
    filter_upwards [eventually_ne_nhds hne] with y hy
    unfold bennett
    rw [if_neg hy]

/-- `deriv bennett` is analytic at every `x > -1`. -/
theorem analyticAt_deriv_bennett_of_gt {x : ℝ} (hx : -1 < x) :
    AnalyticAt ℝ (deriv bennett) x :=
  (analyticAt_bennett_of_gt hx).deriv

/-! ### Joint analyticity -/

/-- `Qfun` is jointly analytic at every `(ε, 0)` with `0 < ε < 1`. -/
theorem analyticAt_Qfun {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    AnalyticAt ℝ (fun w : ℝ × ℝ => Qfun w.1 w.2) (ε, 0) := by
  have hεne : ε ≠ 0 := ne_of_gt hε0
  have h1ε : (0 : ℝ) < 1 - ε := by linarith
  have h1εne : (1 : ℝ) - ε ≠ 0 := ne_of_gt h1ε
  have hfst : AnalyticAt ℝ (fun w : ℝ × ℝ => w.1) (ε, 0) := analyticAt_fst
  have hsnd : AnalyticAt ℝ (fun w : ℝ × ℝ => w.2) (ε, 0) := analyticAt_snd
  -- the first inner map `w ↦ w.2 / w.1`
  have hinner1 : AnalyticAt ℝ (fun w : ℝ × ℝ => w.2 / w.1) (ε, 0) := hsnd.div hfst hεne
  have hcomp1 : AnalyticAt ℝ (fun w : ℝ × ℝ => bennett (w.2 / w.1)) (ε, 0) := by
    have h := AnalyticAt.comp (g := bennett) (f := fun w : ℝ × ℝ => w.2 / w.1)
      (x := ((ε, 0) : ℝ × ℝ)) (by simpa using analyticAt_bennett) hinner1
    simpa [Function.comp_def] using h
  -- the second inner map `w ↦ -(w.2 / (1 - w.1))`
  have hinner2 : AnalyticAt ℝ (fun w : ℝ × ℝ => -(w.2 / (1 - w.1))) (ε, 0) :=
    (hsnd.div (analyticAt_const.sub hfst) h1εne).neg
  have hcomp2 : AnalyticAt ℝ (fun w : ℝ × ℝ => bennett (-(w.2 / (1 - w.1)))) (ε, 0) := by
    have h := AnalyticAt.comp (g := bennett) (f := fun w : ℝ × ℝ => -(w.2 / (1 - w.1)))
      (x := ((ε, 0) : ℝ × ℝ)) (by simpa using analyticAt_bennett) hinner2
    simpa [Function.comp_def] using h
  exact ((hcomp1.div hfst hεne).add (hcomp2.div (analyticAt_const.sub hfst) h1εne)).neg

/-- `Qfun1` is jointly analytic at every `(ε, 0)` with `0 < ε < 1`. -/
theorem analyticAt_Qfun1 {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    AnalyticAt ℝ (fun w : ℝ × ℝ => Qfun1 w.1 w.2) (ε, 0) := by
  have hεne : ε ≠ 0 := ne_of_gt hε0
  have h1ε : (0 : ℝ) < 1 - ε := by linarith
  have h1εne : (1 : ℝ) - ε ≠ 0 := ne_of_gt h1ε
  have hfst : AnalyticAt ℝ (fun w : ℝ × ℝ => w.1) (ε, 0) := analyticAt_fst
  have hsnd : AnalyticAt ℝ (fun w : ℝ × ℝ => w.2) (ε, 0) := analyticAt_snd
  have hinner1 : AnalyticAt ℝ (fun w : ℝ × ℝ => w.2 / w.1) (ε, 0) := hsnd.div hfst hεne
  have hcomp1 : AnalyticAt ℝ (fun w : ℝ × ℝ => deriv bennett (w.2 / w.1)) (ε, 0) := by
    have h := AnalyticAt.comp (g := deriv bennett) (f := fun w : ℝ × ℝ => w.2 / w.1)
      (x := ((ε, 0) : ℝ × ℝ)) (by simpa using analyticAt_deriv_bennett) hinner1
    simpa [Function.comp_def] using h
  have hinner2 : AnalyticAt ℝ (fun w : ℝ × ℝ => -(w.2 / (1 - w.1))) (ε, 0) :=
    (hsnd.div (analyticAt_const.sub hfst) h1εne).neg
  have hcomp2 : AnalyticAt ℝ (fun w : ℝ × ℝ => deriv bennett (-(w.2 / (1 - w.1)))) (ε, 0) := by
    have h := AnalyticAt.comp (g := deriv bennett) (f := fun w : ℝ × ℝ => -(w.2 / (1 - w.1)))
      (x := ((ε, 0) : ℝ × ℝ)) (by simpa using analyticAt_deriv_bennett) hinner2
    simpa [Function.comp_def] using h
  exact ((hcomp1.div (hfst.pow 2) (pow_ne_zero 2 hεne)).sub
    (hcomp2.div ((analyticAt_const.sub hfst).pow 2) (pow_ne_zero 2 h1εne))).neg

/-! ### Values and derivatives at `u = 0` -/

/-- `Qfun ε 0 = -1/(2ε(1-ε))`. -/
theorem Qfun_zero {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    Qfun ε 0 = -(1 / (2 * ε * (1 - ε))) := by
  have hεne : ε ≠ 0 := ne_of_gt hε0
  have h1εne : (1 : ℝ) - ε ≠ 0 := ne_of_gt (by linarith)
  unfold Qfun
  simp only [zero_div, neg_zero, bennett_zero]
  field_simp
  ring

/-- `Qfun1 ε 0 = (1/6)(1/ε² - 1/(1-ε)²)`. -/
theorem Qfun1_zero {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    Qfun1 ε 0 = 1 / 6 * (1 / ε ^ 2 - 1 / (1 - ε) ^ 2) := by
  have hεne : ε ≠ 0 := ne_of_gt hε0
  have h1εne : (1 : ℝ) - ε ≠ 0 := ne_of_gt (by linarith)
  unfold Qfun1
  simp only [zero_div, neg_zero, deriv_bennett_zero]
  field_simp
  ring

/-- `Qfun2 ε 0 = -(1/6)(1/ε³ + 1/(1-ε)³)`. -/
theorem Qfun2_zero {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    Qfun2 ε 0 = -(1 / 6 * (1 / ε ^ 3 + 1 / (1 - ε) ^ 3)) := by
  have hεne : ε ≠ 0 := ne_of_gt hε0
  have h1εne : (1 : ℝ) - ε ≠ 0 := ne_of_gt (by linarith)
  unfold Qfun2
  simp only [zero_div, neg_zero, deriv2_bennett_zero]
  field_simp

/-! ### The derivative identities -/

/-- The two arguments of `bennett` stay above `-1` on the admissible range. -/
private theorem bennett_args {ε u : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (h0 : 0 < ε + u)
    (h1 : ε + u < 1) : (-1 : ℝ) < u / ε ∧ (-1 : ℝ) < -(u / (1 - ε)) := by
  have h1ε : (0 : ℝ) < 1 - ε := by linarith
  refine ⟨?_, ?_⟩
  · rw [lt_div_iff₀ hε0]; linarith
  · rw [neg_lt_neg_iff, div_lt_one h1ε]; linarith

/-- `Qfun1` is the `u`-derivative of `Qfun` on the admissible range. -/
theorem hasDerivAt_Qfun {ε u : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (h0 : 0 < ε + u)
    (h1 : ε + u < 1) : HasDerivAt (fun y : ℝ => Qfun ε y) (Qfun1 ε u) u := by
  have hεne : ε ≠ 0 := ne_of_gt hε0
  have h1ε : (0 : ℝ) < 1 - ε := by linarith
  have h1εne : (1 : ℝ) - ε ≠ 0 := ne_of_gt h1ε
  obtain ⟨ha1, ha2⟩ := bennett_args hε0 hε1 h0 h1
  have hd1 : HasDerivAt bennett (deriv bennett (u / ε)) (u / ε) :=
    (analyticAt_bennett_of_gt ha1).differentiableAt.hasDerivAt
  have hd2 : HasDerivAt bennett (deriv bennett (-(u / (1 - ε)))) (-(u / (1 - ε))) :=
    (analyticAt_bennett_of_gt ha2).differentiableAt.hasDerivAt
  have hi1 : HasDerivAt (fun y : ℝ => y / ε) (1 / ε) u := by
    have h : HasDerivAt (fun y : ℝ => 1 / ε * y) (1 / ε * 1) u := (hasDerivAt_id u).const_mul _
    have heq : (fun y : ℝ => 1 / ε * y) = fun y : ℝ => y / ε := by
      funext y; field_simp
    rw [heq] at h
    simpa using h
  have hi2 : HasDerivAt (fun y : ℝ => -(y / (1 - ε))) (-(1 / (1 - ε))) u := by
    have h : HasDerivAt (fun y : ℝ => -(1 / (1 - ε)) * y) (-(1 / (1 - ε)) * 1) u :=
      (hasDerivAt_id u).const_mul _
    have heq : (fun y : ℝ => -(1 / (1 - ε)) * y) = fun y : ℝ => -(y / (1 - ε)) := by
      funext y; field_simp
    rw [heq] at h
    simpa using h
  have h1' : HasDerivAt (fun y : ℝ => bennett (y / ε))
      (deriv bennett (u / ε) * (1 / ε)) u := by
    simpa [Function.comp_def] using hd1.comp u hi1
  have h2' : HasDerivAt (fun y : ℝ => bennett (-(y / (1 - ε))))
      (deriv bennett (-(u / (1 - ε))) * -(1 / (1 - ε))) u := by
    simpa [Function.comp_def] using hd2.comp u hi2
  have hsum := ((h1'.div_const ε).add (h2'.div_const (1 - ε))).neg
  have hval : -(deriv bennett (u / ε) * (1 / ε) / ε
      + deriv bennett (-(u / (1 - ε))) * -(1 / (1 - ε)) / (1 - ε)) = Qfun1 ε u := by
    unfold Qfun1
    field_simp
    ring
  rw [← hval]
  exact hsum

/-- `Qfun2` is the `u`-derivative of `Qfun1` on the admissible range. -/
theorem hasDerivAt_Qfun1 {ε u : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (h0 : 0 < ε + u)
    (h1 : ε + u < 1) : HasDerivAt (fun y : ℝ => Qfun1 ε y) (Qfun2 ε u) u := by
  have hεne : ε ≠ 0 := ne_of_gt hε0
  have h1ε : (0 : ℝ) < 1 - ε := by linarith
  have h1εne : (1 : ℝ) - ε ≠ 0 := ne_of_gt h1ε
  obtain ⟨ha1, ha2⟩ := bennett_args hε0 hε1 h0 h1
  have hd1 : HasDerivAt (deriv bennett) (deriv (deriv bennett) (u / ε)) (u / ε) :=
    (analyticAt_deriv_bennett_of_gt ha1).differentiableAt.hasDerivAt
  have hd2 : HasDerivAt (deriv bennett)
      (deriv (deriv bennett) (-(u / (1 - ε)))) (-(u / (1 - ε))) :=
    (analyticAt_deriv_bennett_of_gt ha2).differentiableAt.hasDerivAt
  have hi1 : HasDerivAt (fun y : ℝ => y / ε) (1 / ε) u := by
    have h : HasDerivAt (fun y : ℝ => 1 / ε * y) (1 / ε * 1) u := (hasDerivAt_id u).const_mul _
    have heq : (fun y : ℝ => 1 / ε * y) = fun y : ℝ => y / ε := by
      funext y; field_simp
    rw [heq] at h
    simpa using h
  have hi2 : HasDerivAt (fun y : ℝ => -(y / (1 - ε))) (-(1 / (1 - ε))) u := by
    have h : HasDerivAt (fun y : ℝ => -(1 / (1 - ε)) * y) (-(1 / (1 - ε)) * 1) u :=
      (hasDerivAt_id u).const_mul _
    have heq : (fun y : ℝ => -(1 / (1 - ε)) * y) = fun y : ℝ => -(y / (1 - ε)) := by
      funext y; field_simp
    rw [heq] at h
    simpa using h
  have h1' : HasDerivAt (fun y : ℝ => deriv bennett (y / ε))
      (deriv (deriv bennett) (u / ε) * (1 / ε)) u := by
    simpa [Function.comp_def] using hd1.comp u hi1
  have h2' : HasDerivAt (fun y : ℝ => deriv bennett (-(y / (1 - ε))))
      (deriv (deriv bennett) (-(u / (1 - ε))) * -(1 / (1 - ε))) u := by
    simpa [Function.comp_def] using hd2.comp u hi2
  have hsum := ((h1'.div_const (ε ^ 2)).sub (h2'.div_const ((1 - ε) ^ 2))).neg
  have hval : -(deriv (deriv bennett) (u / ε) * (1 / ε) / ε ^ 2
      - deriv (deriv bennett) (-(u / (1 - ε))) * -(1 / (1 - ε)) / (1 - ε) ^ 2)
      = Qfun2 ε u := by
    unfold Qfun2
    field_simp
    ring
  rw [← hval]
  exact hsum

/-- **The shift identity for the derivative of the entropy remainder**. -/
theorem dN_shift {ε u : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (h0 : 0 < ε + u) (h1 : ε + u < 1) :
    dN ε (ε + u) = 2 * u * Qfun ε u + u ^ 2 * Qfun1 ε u := by
  have hL : HasDerivAt (fun y : ℝ => Nfun ε (ε + y)) (dN ε (ε + u)) u := by
    have hz0 : ε + u ≠ 0 := ne_of_gt h0
    have hz1 : ε + u ≠ 1 := ne_of_lt h1
    have hinner : HasDerivAt (fun y : ℝ => ε + y) 1 u := by
      simpa using (hasDerivAt_id u).const_add ε
    simpa [Function.comp_def] using (hasDerivAt_Nfun ε hz0 hz1).comp u hinner
  have hR : HasDerivAt (fun y : ℝ => y ^ 2 * Qfun ε y)
      (2 * u * Qfun ε u + u ^ 2 * Qfun1 ε u) u := by
    have hp : HasDerivAt (fun y : ℝ => y ^ 2) (2 * u) u := by
      simpa using hasDerivAt_pow 2 u
    exact (hp.mul (hasDerivAt_Qfun hε0 hε1 h0 h1)).congr_deriv (by ring)
  have hopen : IsOpen {y : ℝ | 0 < ε + y ∧ ε + y < 1} := by
    have hset : {y : ℝ | 0 < ε + y ∧ ε + y < 1} = (fun y : ℝ => ε + y) ⁻¹' Set.Ioo 0 1 := by
      ext y; simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Ioo]
    rw [hset]
    exact isOpen_Ioo.preimage (continuous_const.add continuous_id)
  have hmem : u ∈ {y : ℝ | 0 < ε + y ∧ ε + y < 1} := ⟨h0, h1⟩
  have heq : (fun y : ℝ => y ^ 2 * Qfun ε y) =ᶠ[nhds u] fun y : ℝ => Nfun ε (ε + y) := by
    filter_upwards [hopen.mem_nhds hmem] with y hy
    exact (Nfun_shift hε0 hε1 hy.1 hy.2).symm
  exact (hL.congr_of_eventuallyEq heq).unique hR

end UpperTailOptimizers
