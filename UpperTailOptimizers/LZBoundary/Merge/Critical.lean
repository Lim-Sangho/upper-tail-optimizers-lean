import UpperTailOptimizers.LZBoundary.Merge.Shift
import UpperTailOptimizers.LZBoundary.Merge.PolyPart
import UpperTailOptimizers.Preliminaries.KRRSAnalyticExtension.PsiExists

/-!
# The normalised critical-point equation at the merged contact

The critical points of the Kenyon–Radin–Ren–Sadun selector `ψ_d(ε,·) = 𝒩_ε/𝒟_ε` are the zeros of
the Wronskian-type numerator `Wr d ε z = 𝒩'_ε(z)𝒟_ε(z) - 𝒩_ε(z)𝒟'_ε(z)`.  Both `𝒩_ε` and `𝒟_ε`
vanish to second order at `z = ε`, so `Wr` vanishes to fourth order there and the equation
`Wr = 0` carries no information at a merged contact.  Writing `z = ε + u` and dividing by `u⁴`
removes the degeneracy:

`Wr d ε (ε + u) = u⁴ · What d ε u`,
`What d ε u = Qfun1 ε u · polyP d ε u - Qfun ε u · polyP1 d ε u`.

`What` is jointly analytic at `(ε, 0)` (`analyticAt_What`), vanishes at the exceptional density
(`What_rStar_zero`) and has there a **nonzero** `u`-derivative (`deriv_What_rStar_ne_zero`,
indeed negative).  That is exactly the input of the analytic implicit function theorem used in
`Merge/ZetaAnalytic.lean`.
-/

namespace UpperTailOptimizers

open Filter Topology

/-- The `u⁴`-cofactor of `Wr` after the shift `z = ε + u`. -/
noncomputable def What (d : ℕ) (ε u : ℝ) : ℝ :=
  Qfun1 ε u * polyP d ε u - Qfun ε u * polyP1 d ε u

/-- The shift identity for the derivative of the moment remainder. -/
theorem dD_shift {d : ℕ} (hd : 2 ≤ d) (ε u : ℝ) :
    dD d ε (ε + u) = 2 * u * polyP d ε u + u ^ 2 * polyP1 d ε u := by
  have hL : HasDerivAt (fun y : ℝ => Dfun d ε (ε + y)) (dD d ε (ε + u)) u := by
    have hinner : HasDerivAt (fun y : ℝ => ε + y) 1 u := by
      simpa using (hasDerivAt_id u).const_add ε
    simpa [Function.comp_def] using (hasDerivAt_Dfun d ε (ε + u)).comp u hinner
  have hR : HasDerivAt (fun y : ℝ => y ^ 2 * polyP d ε y)
      (2 * u * polyP d ε u + u ^ 2 * polyP1 d ε u) u := by
    have hp : HasDerivAt (fun y : ℝ => y ^ 2) (2 * u) u := by
      simpa using hasDerivAt_pow 2 u
    exact (hp.mul (hasDerivAt_polyP (d := d) ε u)).congr_deriv (by ring)
  have heq : (fun y : ℝ => Dfun d ε (ε + y)) = fun y : ℝ => y ^ 2 * polyP d ε y := by
    funext y
    exact Dfun_shift hd ε y
  rw [heq] at hL
  exact hL.unique hR

/-- **The normalisation identity** `Wr d ε (ε + u) = u⁴ · What d ε u`. -/
theorem Wr_shift {d : ℕ} (hd : 2 ≤ d) {ε u : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (h0 : 0 < ε + u) (h1 : ε + u < 1) : Wr d ε (ε + u) = u ^ 4 * What d ε u := by
  have hN := Nfun_shift hε0 hε1 h0 h1
  have hD := Dfun_shift hd ε u
  have hdN := dN_shift hε0 hε1 h0 h1
  have hdD := dD_shift hd ε u
  unfold Wr What
  rw [hdN, hN, hD, hdD]
  ring

/-- `What` is jointly analytic at `(ε, 0)` for `0 < ε < 1`. -/
theorem analyticAt_What (d : ℕ) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    AnalyticAt ℝ (fun w : ℝ × ℝ => What d w.1 w.2) (ε, 0) :=
  ((analyticAt_Qfun1 hε0 hε1).mul (analyticAt_polyP d (ε, 0))).sub
    ((analyticAt_Qfun hε0 hε1).mul (analyticAt_polyP1 d (ε, 0)))

/-- `What` is analytic in `u` alone at `0`. -/
theorem analyticAt_What_snd (d : ℕ) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    AnalyticAt ℝ (fun u : ℝ => What d ε u) 0 := by
  have hpair : AnalyticAt ℝ (fun u : ℝ => ((ε, u) : ℝ × ℝ)) 0 :=
    AnalyticAt.prod (analyticAt_const : AnalyticAt ℝ (fun _ : ℝ => ε) 0) analyticAt_id
  have := (analyticAt_What d hε0 hε1).comp hpair
  simpa [Function.comp_def] using this

/-- The `u`-derivative of `What` at `u = 0`. -/
theorem hasDerivAt_What (d : ℕ) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    HasDerivAt (fun u : ℝ => What d ε u)
      (Qfun2 ε 0 * polyP d ε 0 - Qfun ε 0 * deriv (fun y : ℝ => polyP1 d ε y) 0) 0 := by
  have hQ : HasDerivAt (fun y : ℝ => Qfun ε y) (Qfun1 ε 0) 0 :=
    hasDerivAt_Qfun hε0 hε1 (by simpa using hε0) (by simpa using hε1)
  have hQ1 : HasDerivAt (fun y : ℝ => Qfun1 ε y) (Qfun2 ε 0) 0 :=
    hasDerivAt_Qfun1 hε0 hε1 (by simpa using hε0) (by simpa using hε1)
  have hP : HasDerivAt (fun y : ℝ => polyP d ε y) (polyP1 d ε 0) 0 :=
    hasDerivAt_polyP ε 0
  have hP1 : HasDerivAt (fun y : ℝ => polyP1 d ε y)
      (deriv (fun y : ℝ => polyP1 d ε y) 0) 0 := by
    have hpair : AnalyticAt ℝ (fun u : ℝ => ((ε, u) : ℝ × ℝ)) 0 :=
      AnalyticAt.prod (analyticAt_const : AnalyticAt ℝ (fun _ : ℝ => ε) 0) analyticAt_id
    have han : AnalyticAt ℝ (fun y : ℝ => polyP1 d ε y) 0 := by
      have := (analyticAt_polyP1 d (ε, 0)).comp hpair
      simpa [Function.comp_def] using this
    exact han.differentiableAt.hasDerivAt
  unfold What
  exact ((hQ1.mul hP).sub (hQ.mul hP1)).congr_deriv (by ring)

end UpperTailOptimizers
