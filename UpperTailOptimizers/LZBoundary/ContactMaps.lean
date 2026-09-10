import UpperTailOptimizers.LZBoundary.AnalyticIFT
import UpperTailOptimizers.LZBoundary.Phi

/-!
# Layers 2–3 of `thm:scalar-lz-boundary` of `paper/bipodal_optimizer.tex`: analyticity of the
Lubetzky–Zhao contact maps

The two Lubetzky–Zhao contacts `u_a(p), u_b(p)` solve, in the `u`-coordinate, the
two-equation system `contactF`:
* equal slope:  `s(a) = s(b)` where `s(u) = J_p'(u)/(d u^{d-1}) = φ'_{p,d}(u^d)`;
* chord:        `J_p(b) - J_p(a) = s(a)·(b^d - a^d)`.

`contacts_analytic` shows that near any base solution `(a₀, b₀, p₀)` with
`0 < a₀ < b₀ < 1`, `0 < p₀ < 1`, and the convexity-defect non-degeneracy
`h_{p₀,d}(a₀) ≠ 0`, `h_{p₀,d}(b₀) ≠ 0`, the contacts extend to real-analytic
functions of `p`.  This is the local, functional form of `lem:contact-points`
(`lem:contact-points`) needed for `thm:scalar-lz-boundary`; it is a direct
application of the analytic implicit function theorem `analytic_implicit_two`
(`LZBoundary/AnalyticIFT.lean`), via:

* `contactF_analyticAt` — `contactF` is jointly analytic at `((a₀,b₀), p₀)`;
* `contactF_partial_isCLE` — the partial `z = (a,b)` Jacobian of `contactF(·, p₀)`
  at `(a₀,b₀)` is a continuous linear *equiv*.  Its determinant at a solution is
  `-s'(a₀)·s'(b₀)·(b₀^d - a₀^d)` with `s'(u) = h_{p,d}(u)/(d u^d)`, nonzero
  precisely under the `h ≠ 0` hypotheses.

The `h ≠ 0` hypotheses are faithful (the genuine contacts lie strictly outside the
concave interval `(u_-, u_+)`, where `h_{p,d}` has its zeros); they are discharged
for the genuine contacts in `LZBoundary/Existence.lean` (`exists_contactF_zero`, feeding
the keystone `exists_globalContacts`).  Layer 3, the analytic local inverse used for
the boundary curve `p_c`, is `contact_localInverse_analytic` at the end of the file.
-/

open Filter Topology

namespace UpperTailOptimizers

/-- Contact slope `s(u) = J_p'(u)/(d u^{d-1})` (which equals `φ'_{p,d}(u^d)`). -/
noncomputable def sCM (d : ℕ) (p u : ℝ) : ℝ := Jp' p u / ((d : ℝ) * u ^ (d - 1))

/-- The two-equation contact system in `u`-coordinates (equal-slope, then chord). -/
noncomputable def contactF (d : ℕ) (z : ℝ × ℝ) (p : ℝ) : ℝ × ℝ :=
  (sCM d p z.1 - sCM d p z.2,
   Jp p z.2 - Jp p z.1 - sCM d p z.1 * (z.2 ^ d - z.1 ^ d))

/-- `Real.log ∘ g` is analytic where `g` is analytic and positive. -/
theorem analyticAt_log_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : E → ℝ} {x : E} (hg : AnalyticAt ℝ g x) (hpos : 0 < g x) :
    AnalyticAt ℝ (fun z => Real.log (g z)) x :=
  (analyticAt_log hpos).fun_comp hg

/-- **Helper (joint analyticity).**  `contactF` is real-analytic in `((a,b), p)` at
any interior base point. -/
theorem contactF_analyticAt {d : ℕ} (hd : 2 ≤ d) {a₀ b₀ p₀ : ℝ}
    (ha0 : 0 < a₀) (ha1 : a₀ < 1) (hb0 : 0 < b₀) (hb1 : b₀ < 1)
    (hp0 : 0 < p₀) (hp1 : p₀ < 1) :
    AnalyticAt ℝ (fun w : (ℝ × ℝ) × ℝ => contactF d w.1 w.2) (((a₀, b₀) : ℝ × ℝ), p₀) := by
  have hdpos : (0 : ℝ) < (d : ℝ) := dpos hd
  have hd1 : (d : ℝ) ≠ 0 := ne_of_gt hdpos
  have hA : AnalyticAt ℝ (fun w : (ℝ × ℝ) × ℝ => w.1.1) (((a₀, b₀) : ℝ × ℝ), p₀) :=
    analyticAt_fst.comp analyticAt_fst
  have hB : AnalyticAt ℝ (fun w : (ℝ × ℝ) × ℝ => w.1.2) (((a₀, b₀) : ℝ × ℝ), p₀) :=
    analyticAt_snd.comp analyticAt_fst
  have hP : AnalyticAt ℝ (fun w : (ℝ × ℝ) × ℝ => w.2) (((a₀, b₀) : ℝ × ℝ), p₀) :=
    analyticAt_snd
  have hone : AnalyticAt ℝ (fun _ : (ℝ × ℝ) × ℝ => (1 : ℝ)) (((a₀, b₀) : ℝ × ℝ), p₀) :=
    analyticAt_const
  have h1mA : AnalyticAt ℝ (fun w : (ℝ × ℝ) × ℝ => 1 - w.1.1) (((a₀, b₀) : ℝ × ℝ), p₀) := hone.sub hA
  have h1mB : AnalyticAt ℝ (fun w : (ℝ × ℝ) × ℝ => 1 - w.1.2) (((a₀, b₀) : ℝ × ℝ), p₀) := hone.sub hB
  have h1mP : AnalyticAt ℝ (fun w : (ℝ × ℝ) × ℝ => 1 - w.2) (((a₀, b₀) : ℝ × ℝ), p₀) := hone.sub hP
  have hlogAP : AnalyticAt ℝ (fun w : (ℝ × ℝ) × ℝ => Real.log (w.1.1 / w.2)) (((a₀, b₀) : ℝ × ℝ), p₀) :=
    analyticAt_log_comp (hA.div hP (ne_of_gt hp0)) (by show 0 < a₀ / p₀; positivity)
  have hlog1mAP : AnalyticAt ℝ (fun w : (ℝ × ℝ) × ℝ => Real.log ((1 - w.1.1) / (1 - w.2))) (((a₀, b₀) : ℝ × ℝ), p₀) :=
    analyticAt_log_comp (h1mA.div h1mP (by show (1:ℝ) - p₀ ≠ 0; linarith))
      (by show 0 < (1 - a₀) / (1 - p₀); apply div_pos <;> linarith)
  have hlogBP : AnalyticAt ℝ (fun w : (ℝ × ℝ) × ℝ => Real.log (w.1.2 / w.2)) (((a₀, b₀) : ℝ × ℝ), p₀) :=
    analyticAt_log_comp (hB.div hP (ne_of_gt hp0)) (by show 0 < b₀ / p₀; positivity)
  have hlog1mBP : AnalyticAt ℝ (fun w : (ℝ × ℝ) × ℝ => Real.log ((1 - w.1.2) / (1 - w.2))) (((a₀, b₀) : ℝ × ℝ), p₀) :=
    analyticAt_log_comp (h1mB.div h1mP (by show (1:ℝ) - p₀ ≠ 0; linarith))
      (by show 0 < (1 - b₀) / (1 - p₀); apply div_pos <;> linarith)
  have hJpA : AnalyticAt ℝ (fun w : (ℝ × ℝ) × ℝ => Jp w.2 w.1.1) (((a₀, b₀) : ℝ × ℝ), p₀) := by
    simp only [Jp]; exact (hA.mul hlogAP).add (h1mA.mul hlog1mAP)
  have hJpB : AnalyticAt ℝ (fun w : (ℝ × ℝ) × ℝ => Jp w.2 w.1.2) (((a₀, b₀) : ℝ × ℝ), p₀) := by
    simp only [Jp]; exact (hB.mul hlogBP).add (h1mB.mul hlog1mBP)
  have hJp'A : AnalyticAt ℝ (fun w : (ℝ × ℝ) × ℝ => Jp' w.2 w.1.1) (((a₀, b₀) : ℝ × ℝ), p₀) := by
    simp only [Jp']
    refine analyticAt_log_comp ((hA.mul h1mP).div (h1mA.mul hP) ?_) ?_
    · show (1 - a₀) * p₀ ≠ 0; exact mul_ne_zero (by linarith) (ne_of_gt hp0)
    · show 0 < a₀ * (1 - p₀) / ((1 - a₀) * p₀)
      apply div_pos
      · apply mul_pos ha0; linarith
      · apply mul_pos _ hp0; linarith
  have hJp'B : AnalyticAt ℝ (fun w : (ℝ × ℝ) × ℝ => Jp' w.2 w.1.2) (((a₀, b₀) : ℝ × ℝ), p₀) := by
    simp only [Jp']
    refine analyticAt_log_comp ((hB.mul h1mP).div (h1mB.mul hP) ?_) ?_
    · show (1 - b₀) * p₀ ≠ 0; exact mul_ne_zero (by linarith) (ne_of_gt hp0)
    · show 0 < b₀ * (1 - p₀) / ((1 - b₀) * p₀)
      apply div_pos
      · apply mul_pos hb0; linarith
      · apply mul_pos _ hp0; linarith
  have hdenA : AnalyticAt ℝ (fun w : (ℝ × ℝ) × ℝ => (d : ℝ) * w.1.1 ^ (d - 1)) (((a₀, b₀) : ℝ × ℝ), p₀) :=
    analyticAt_const.mul (hA.pow (d - 1))
  have hdenB : AnalyticAt ℝ (fun w : (ℝ × ℝ) × ℝ => (d : ℝ) * w.1.2 ^ (d - 1)) (((a₀, b₀) : ℝ × ℝ), p₀) :=
    analyticAt_const.mul (hB.pow (d - 1))
  have hdenA0 : (fun w : (ℝ × ℝ) × ℝ => (d : ℝ) * w.1.1 ^ (d - 1)) (((a₀, b₀) : ℝ × ℝ), p₀) ≠ 0 := by
    show (d : ℝ) * a₀ ^ (d - 1) ≠ 0; exact mul_ne_zero hd1 (by positivity)
  have hdenB0 : (fun w : (ℝ × ℝ) × ℝ => (d : ℝ) * w.1.2 ^ (d - 1)) (((a₀, b₀) : ℝ × ℝ), p₀) ≠ 0 := by
    show (d : ℝ) * b₀ ^ (d - 1) ≠ 0; exact mul_ne_zero hd1 (by positivity)
  have hsA : AnalyticAt ℝ (fun w : (ℝ × ℝ) × ℝ => sCM d w.2 w.1.1) (((a₀, b₀) : ℝ × ℝ), p₀) := by
    simp only [sCM]; exact hJp'A.div hdenA hdenA0
  have hsB : AnalyticAt ℝ (fun w : (ℝ × ℝ) × ℝ => sCM d w.2 w.1.2) (((a₀, b₀) : ℝ × ℝ), p₀) := by
    simp only [sCM]; exact hJp'B.div hdenB hdenB0
  have hAd : AnalyticAt ℝ (fun w : (ℝ × ℝ) × ℝ => w.1.1 ^ d) (((a₀, b₀) : ℝ × ℝ), p₀) := hA.pow d
  have hBd : AnalyticAt ℝ (fun w : (ℝ × ℝ) × ℝ => w.1.2 ^ d) (((a₀, b₀) : ℝ × ℝ), p₀) := hB.pow d
  unfold contactF
  apply AnalyticAt.prod
  · exact hsA.sub hsB
  · exact (hJpB.sub hJpA).sub (hsA.mul (hBd.sub hAd))

/-- Strict version of `hasDerivAt_Jp'`. -/
theorem hasStrictDerivAt_Jp' {p u : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hu0 : 0 < u) (hu1 : u < 1) :
    HasStrictDerivAt (Jp' p) (Jp'' u) u := by
  have hune : u ≠ 0 := ne_of_gt hu0
  have h1une : (1 - u) ≠ 0 := ne_of_gt (by linarith)
  have hpne : p ≠ 0 := ne_of_gt hp0
  have h1pne : (1 - p) ≠ 0 := ne_of_gt (by linarith)
  have hlogA : HasStrictDerivAt (fun y : ℝ => Real.log (y / p)) (1 / u) u := by
    have hd : HasStrictDerivAt (fun y : ℝ => y / p) (1 / p) u := by
      simpa using (hasStrictDerivAt_id u).div_const p
    have := hd.log (by positivity)
    convert this using 1
    field_simp
  have hlogB : HasStrictDerivAt (fun y : ℝ => Real.log ((1 - y) / (1 - p))) (-(1 / (1 - u))) u := by
    have hsub : HasStrictDerivAt (fun y : ℝ => 1 - y) (-1) u := by
      simpa using (hasStrictDerivAt_id u).const_sub 1
    have hd : HasStrictDerivAt (fun y : ℝ => (1 - y) / (1 - p)) (-1 / (1 - p)) u := by
      simpa using hsub.div_const (1 - p)
    have := hd.log (div_ne_zero h1une h1pne)
    convert this using 1
    field_simp
  have hdiff := hlogA.sub hlogB
  have hagree : (fun y : ℝ => Real.log (y / p) - Real.log ((1 - y) / (1 - p))) =ᶠ[nhds u] Jp' p := by
    filter_upwards [Ioo_mem_nhds hu0 hu1] with y hy
    exact (Jp'_eq_sub hp0 hp1 hy.1 hy.2).symm
  have hres := hdiff.congr_of_eventuallyEq hagree
  have hval : (1 / u - -(1 / (1 - u))) = Jp'' u := by
    unfold Jp''
    field_simp
    ring
  rw [hval] at hres
  exact hres

/-- Strict version of `hasDerivAt_Jp`. -/
theorem hasStrictDerivAt_Jp {p u : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hu0 : 0 < u) (hu1 : u < 1) :
    HasStrictDerivAt (Jp p) (Jp' p u) u := by
  have hune : u ≠ 0 := ne_of_gt hu0
  have h1une : (1 - u) ≠ 0 := ne_of_gt (by linarith)
  have hpne : p ≠ 0 := ne_of_gt hp0
  have h1pne : (1 - p) ≠ 0 := ne_of_gt (by linarith)
  have hlogA : HasStrictDerivAt (fun y : ℝ => Real.log (y / p)) (1 / u) u := by
    have hd : HasStrictDerivAt (fun y : ℝ => y / p) (1 / p) u := by
      simpa using (hasStrictDerivAt_id u).div_const p
    have := hd.log (by positivity)
    convert this using 1
    field_simp
  have hlogB : HasStrictDerivAt (fun y : ℝ => Real.log ((1 - y) / (1 - p))) (-(1 / (1 - u))) u := by
    have hsub : HasStrictDerivAt (fun y : ℝ => 1 - y) (-1) u := by
      simpa using (hasStrictDerivAt_id u).const_sub 1
    have hd : HasStrictDerivAt (fun y : ℝ => (1 - y) / (1 - p)) (-1 / (1 - p)) u := by
      simpa using hsub.div_const (1 - p)
    have := hd.log (div_ne_zero h1une h1pne)
    convert this using 1
    field_simp
  have hA : HasStrictDerivAt (fun y : ℝ => y * Real.log (y / p))
      (Real.log (u / p) + u * (1 / u)) u := by
    have h := (hasStrictDerivAt_id u).mul hlogA
    simp only [id_eq, one_mul] at h
    exact h
  have hB : HasStrictDerivAt (fun y : ℝ => (1 - y) * Real.log ((1 - y) / (1 - p)))
      ((-1) * Real.log ((1 - u) / (1 - p)) + (1 - u) * (-(1 / (1 - u)))) u := by
    have hsub : HasStrictDerivAt (fun y : ℝ => 1 - y) (-1) u := by
      simpa using (hasStrictDerivAt_id u).const_sub 1
    exact hsub.mul hlogB
  have hsum := hA.add hB
  have hfun : ((fun y : ℝ => y * Real.log (y / p)) +
      fun y : ℝ => (1 - y) * Real.log ((1 - y) / (1 - p))) = Jp p := by
    funext y; rfl
  rw [hfun] at hsum
  have hval : Real.log (u / p) + u * (1 / u) +
      ((-1) * Real.log ((1 - u) / (1 - p)) + (1 - u) * (-(1 / (1 - u)))) = Jp' p u := by
    have e1 : u * (1 / u) = 1 := by field_simp
    have e2 : (1 - u) * (-(1 / (1 - u))) = -1 := by field_simp
    rw [e1, e2, Jp'_eq_sub hp0 hp1 hu0 hu1]; ring
  rw [← hval]
  exact hsum

/-- Derivative of `sCM`: `s'(u) = h_{p,d}(u) / (d u^d)`. -/
theorem hasStrictDerivAt_sCM {d : ℕ} (hd : 2 ≤ d) {p u : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) (hu0 : 0 < u) (hu1 : u < 1) :
    HasStrictDerivAt (sCM d p) (hpd p d u / ((d : ℝ) * u ^ d)) u := by
  have hune : u ≠ 0 := ne_of_gt hu0
  have h1une : (1 - u) ≠ 0 := ne_of_gt (by linarith)
  have hdpos : (0 : ℝ) < (d : ℝ) := dpos hd
  have hdne : (d : ℝ) ≠ 0 := ne_of_gt hdpos
  have hupowne : u ^ (d - 1) ≠ 0 := pow_ne_zero _ hune
  have hnum : HasStrictDerivAt (Jp' p) (Jp'' u) u := hasStrictDerivAt_Jp' hp0 hp1 hu0 hu1
  have hden : HasStrictDerivAt (fun y : ℝ => (d : ℝ) * y ^ (d - 1))
      ((d : ℝ) * ((↑(d - 1) : ℝ) * u ^ (d - 1 - 1))) u :=
    (hasStrictDerivAt_pow (d - 1) u).const_mul (d : ℝ)
  have hdenval : (d : ℝ) * u ^ (d - 1) ≠ 0 := by positivity
  have hquot := hnum.div hden hdenval
  have hfun : (Jp' p / fun y : ℝ => (d : ℝ) * y ^ (d - 1)) = sCM d p := by
    funext y; rfl
  rw [hfun] at hquot
  have key : (Jp'' u * ((d : ℝ) * u ^ (d - 1)) -
      Jp' p u * ((d : ℝ) * ((↑(d - 1) : ℝ) * u ^ (d - 1 - 1)))) / ((d : ℝ) * u ^ (d - 1)) ^ 2
      = hpd p d u / ((d : ℝ) * u ^ d) := by
    have hd1 : d - 1 = (d - 1 - 1) + 1 := by omega
    have hd0 : d = (d - 1 - 1) + 2 := by omega
    rw [hpd_eq hu0 hu1]
    have hcast : (↑(d - 1) : ℝ) = (d : ℝ) - 1 := by
      have : 1 ≤ d := by omega
      push_cast [Nat.cast_sub this]; ring
    rw [hcast]
    set m := u ^ (d - 1 - 1) with hm
    have e1 : u ^ (d - 1) = u * m := by rw [hd1, pow_succ]; ring
    have e2 : u ^ d = u * u * m := by rw [hd0, pow_succ, pow_succ]; ring
    rw [e1, e2]
    have hmne : m ≠ 0 := by rw [hm]; exact pow_ne_zero _ hune
    unfold Jp''
    field_simp
  rw [key] at hquot
  exact hquot

/-- At the contact, `s(u)·(d u^{d-1}) = J_p'(u)` (the slope identity). -/
theorem sCM_mul_dpow {d : ℕ} (hd : 2 ≤ d) {p u : ℝ} (hu0 : 0 < u) :
    sCM d p u * ((d : ℝ) * u ^ (d - 1)) = Jp' p u := by
  have hdne : (d : ℝ) ≠ 0 := ne_of_gt (dpos hd)
  have hune : u ≠ 0 := ne_of_gt hu0
  have hupowne : u ^ (d - 1) ≠ 0 := pow_ne_zero _ hune
  unfold sCM
  field_simp

open ContinuousLinearMap in
/-- **Helper (Jacobian is a linear equiv).**  At a solution of the slope equation,
the partial `(a,b)`-derivative of `contactF(·, p₀)` is invertible, because its
determinant is `-s'(a₀)·s'(b₀)·(b₀^d - a₀^d)` with `s'(u) = h_{p,d}(u)/(d u^d)`. -/
theorem contactF_partial_isCLE {d : ℕ} (hd : 2 ≤ d) {a₀ b₀ p₀ : ℝ}
    (ha0 : 0 < a₀) (hab : a₀ < b₀) (hb1 : b₀ < 1) (hp0 : 0 < p₀) (hp1 : p₀ < 1)
    (hslope : sCM d p₀ a₀ = sCM d p₀ b₀)
    (hha : hpd p₀ d a₀ ≠ 0) (hhb : hpd p₀ d b₀ ≠ 0) :
    ∃ L : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ),
      HasStrictFDerivAt (fun z : ℝ × ℝ => contactF d z p₀)
        (L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) (a₀, b₀) := by
  have ha1 : a₀ < 1 := lt_trans hab hb1
  have hb0 : 0 < b₀ := lt_trans ha0 hab
  have hdpos : (0 : ℝ) < (d : ℝ) := dpos hd
  have hdne : (d : ℝ) ≠ 0 := ne_of_gt hdpos
  have hane : a₀ ≠ 0 := ne_of_gt ha0
  have hbne : b₀ ≠ 0 := ne_of_gt hb0
  have hapd : (0 : ℝ) < (d : ℝ) * a₀ ^ d := by positivity
  have hbpd : (0 : ℝ) < (d : ℝ) * b₀ ^ d := by positivity
  set α : ℝ := hpd p₀ d a₀ / ((d : ℝ) * a₀ ^ d) with hα
  set sb : ℝ := hpd p₀ d b₀ / ((d : ℝ) * b₀ ^ d) with hsb
  set powdiff : ℝ := b₀ ^ d - a₀ ^ d with hpowdiff
  set β : ℝ := -sb with hβ
  set γ : ℝ := -α * powdiff with hγ
  set Δ : ℝ := -β * γ with hΔ
  have hαne : α ≠ 0 := div_ne_zero hha (ne_of_gt hapd)
  have hsbne : sb ≠ 0 := div_ne_zero hhb (ne_of_gt hbpd)
  have hβne : β ≠ 0 := by rw [hβ]; exact neg_ne_zero.mpr hsbne
  have hpowlt : a₀ ^ d < b₀ ^ d := pow_lt_pow_left₀ hab (le_of_lt ha0) (by omega : d ≠ 0)
  have hpowdiffne : powdiff ≠ 0 := by
    rw [hpowdiff]; exact sub_ne_zero.mpr (ne_of_gt hpowlt)
  have hγne : γ ≠ 0 := by
    rw [hγ]; exact mul_ne_zero (neg_ne_zero.mpr hαne) hpowdiffne
  have hΔne : Δ ≠ 0 := by rw [hΔ]; exact mul_ne_zero (neg_ne_zero.mpr hβne) hγne
  set P1 : (ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ ℝ with hP1
  set P2 : (ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ ℝ ℝ with hP2
  have hfst : HasStrictFDerivAt (Prod.fst : ℝ × ℝ → ℝ) P1 (a₀, b₀) := hasStrictFDerivAt_fst
  have hsnd : HasStrictFDerivAt (Prod.snd : ℝ × ℝ → ℝ) P2 (a₀, b₀) := hasStrictFDerivAt_snd
  set M₁ : (ℝ × ℝ) →L[ℝ] ℝ := (α • P1) + (β • P2) with hM₁
  set M₂ : (ℝ × ℝ) →L[ℝ] ℝ := γ • P1 with hM₂
  have hg1 : HasStrictFDerivAt (fun z : ℝ × ℝ => sCM d p₀ z.1 - sCM d p₀ z.2) M₁ (a₀, b₀) := by
    have h1 := (hasStrictDerivAt_sCM hd hp0 hp1 ha0 ha1).comp_hasStrictFDerivAt (a₀, b₀) hfst
    have h2 := (hasStrictDerivAt_sCM hd hp0 hp1 hb0 hb1).comp_hasStrictFDerivAt (a₀, b₀) hsnd
    have hraw := h1.sub h2
    have heq : (α • P1 - sb • P2) = M₁ := by
      rw [hM₁, hβ]; module
    rw [heq] at hraw
    exact hraw
  have hg2 : HasStrictFDerivAt
      (fun z : ℝ × ℝ => Jp p₀ z.2 - Jp p₀ z.1 - sCM d p₀ z.1 * (z.2 ^ d - z.1 ^ d)) M₂ (a₀, b₀) := by
    have hJpb := (hasStrictDerivAt_Jp hp0 hp1 hb0 hb1).comp_hasStrictFDerivAt (a₀, b₀) hsnd
    have hJpa := (hasStrictDerivAt_Jp hp0 hp1 ha0 ha1).comp_hasStrictFDerivAt (a₀, b₀) hfst
    have hsa := (hasStrictDerivAt_sCM hd hp0 hp1 ha0 ha1).comp_hasStrictFDerivAt (a₀, b₀) hfst
    have hpowb : HasStrictFDerivAt (fun z : ℝ × ℝ => z.2 ^ d) _ (a₀, b₀) := hsnd.pow d
    have hpowa : HasStrictFDerivAt (fun z : ℝ × ℝ => z.1 ^ d) _ (a₀, b₀) := hfst.pow d
    have hpd := hpowb.sub hpowa
    have hprod := hsa.mul hpd
    have hraw := (hJpb.sub hJpa).sub hprod
    have hia : sCM d p₀ a₀ * ((d : ℝ) * a₀ ^ (d - 1)) = Jp' p₀ a₀ := sCM_mul_dpow hd ha0
    have hib : sCM d p₀ b₀ * ((d : ℝ) * b₀ ^ (d - 1)) = Jp' p₀ b₀ := sCM_mul_dpow hd hb0
    have hib' : sCM d p₀ a₀ * ((d : ℝ) * b₀ ^ (d - 1)) = Jp' p₀ b₀ := by rw [hslope]; exact hib
    convert hraw using 1
    all_goals try rfl
    apply ContinuousLinearMap.ext
    intro w
    obtain ⟨w1, w2⟩ := w
    simp only [hM₂, hP1, hP2, add_apply, sub_apply,
      smul_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd', Function.comp_apply, Pi.sub_apply, smul_eq_mul, nsmul_eq_mul]
    rw [hγ, hα, hpowdiff]
    linear_combination (-(w1 : ℝ)) * hia + (w2 : ℝ) * hib'
  set M : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) := M₁.prod M₂ with hM
  have hgM : HasStrictFDerivAt (fun z : ℝ × ℝ => contactF d z p₀) M (a₀, b₀) := by
    have := hg1.prodMk hg2
    convert this using 1
    all_goals try rfl
  set N : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
    (((-β / Δ) • P2)).prod (((-γ / Δ) • P1) + ((α / Δ) • P2)) with hN
  have hMN : Function.RightInverse N M := by
    intro w
    obtain ⟨y1, y2⟩ := w
    simp only [hM, hN, hM₁, hM₂, hP1, hP2, ContinuousLinearMap.prod_apply,
      add_apply, smul_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul, Prod.mk.injEq]
    rw [hΔ]
    constructor <;> · field_simp; try ring
  have hNM : Function.LeftInverse N M := by
    intro w
    obtain ⟨w1, w2⟩ := w
    simp only [hM, hN, hM₁, hM₂, hP1, hP2, ContinuousLinearMap.prod_apply,
      add_apply, smul_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul, Prod.mk.injEq]
    rw [hΔ]
    constructor <;> · field_simp; try ring
  refine ⟨ContinuousLinearEquiv.equivOfInverse M N hNM hMN, ?_⟩
  have hcoe : ((ContinuousLinearEquiv.equivOfInverse M N hNM hMN :
      (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) = M := by
    apply ContinuousLinearMap.ext
    intro w
    rw [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.equivOfInverse_apply]
  rw [hcoe]
  exact hgM

/-- **Layer 2 (functional `lem:contact-points`, local form).**  Near a non-degenerate base
solution of the contact system, the two Lubetzky–Zhao contacts extend to real-analytic
functions `u_a(p), u_b(p)`. -/
theorem contacts_analytic {d : ℕ} (hd : 2 ≤ d) {a₀ b₀ p₀ : ℝ}
    (ha0 : 0 < a₀) (hab : a₀ < b₀) (hb1 : b₀ < 1) (hp0 : 0 < p₀) (hp1 : p₀ < 1)
    (hF0 : contactF d (a₀, b₀) p₀ = 0)
    (hslope : sCM d p₀ a₀ = sCM d p₀ b₀)
    (hha : hpd p₀ d a₀ ≠ 0) (hhb : hpd p₀ d b₀ ≠ 0) :
    ∃ ua ub : ℝ → ℝ, ua p₀ = a₀ ∧ ub p₀ = b₀ ∧
      (∀ᶠ p in 𝓝 p₀, contactF d (ua p, ub p) p = 0) ∧
      AnalyticAt ℝ ua p₀ ∧ AnalyticAt ℝ ub p₀ := by
  have ha1 : a₀ < 1 := lt_trans hab hb1
  have hb0 : 0 < b₀ := lt_trans ha0 hab
  have hanalytic := contactF_analyticAt hd ha0 ha1 hb0 hb1 hp0 hp1
  obtain ⟨L, hL⟩ := contactF_partial_isCLE hd ha0 hab hb1 hp0 hp1 hslope hha hhb
  exact analytic_implicit_two hanalytic hF0 L hL

/-- **Layer 3 (inversion).**  An analytic contact map `f = u_a` (resp. `u_b`) with
non-zero derivative at `p₀` has a real-analytic local inverse `g` at `f p₀`
(a genuine two-sided inverse near `p₀`: `g ∘ f = id` near `p₀` **and** `f ∘ g = id`
near `f p₀`).  This is the analytic boundary curve `p_c` (`g`) on its family; via
Mathlib's 1-D analytic inverse function theorem.  The non-vanishing of the
derivative is the contact-map monotonicity (`dx_a/dp > 0`, `dx_b/dp < 0`).  The
right-inverse half is what lets us identify `g` with the global choice-defined `p_c`. -/
theorem contact_localInverse_analytic {f : ℝ → ℝ} {p₀ : ℝ}
    (hf : AnalyticAt ℝ f p₀) (hf' : deriv f p₀ ≠ 0) :
    ∃ g : ℝ → ℝ, AnalyticAt ℝ g (f p₀) ∧ g (f p₀) = p₀ ∧
      (∀ᶠ p in 𝓝 p₀, g (f p) = p) ∧ (∀ᶠ s in 𝓝 (f p₀), f (g s) = s) := by
  have hev := hf.hasStrictDerivAt.eventually_left_inverse hf'
  have hev' := hf.hasStrictDerivAt.eventually_right_inverse hf'
  exact ⟨hf.hasStrictDerivAt.localInverse _ _ _ hf', hf.analyticAt_localInverse hf',
    hev.self_of_nhds, hev, hev'⟩

end UpperTailOptimizers
