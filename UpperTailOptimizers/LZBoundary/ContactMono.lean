import UpperTailOptimizers.LZBoundary.ContactMaps

/-!
# Monotonicity of the Lubetzky–Zhao contact maps (Layer 4 of Theorem 3.1 of
`paper/paper.tex`)

`contact_deriv_ua_pos`: the left contact map `u_a(p)` is strictly increasing
(`dx_a/dp > 0`).  Differentiating the chord equation `(contactF …).2 = 0` and using
that its `b`-partial vanishes at a solution (the equal-slope condition), the `u_b'`
term drops out, leaving `γ · u_a' + ∂_p F₂ = 0` with `γ < 0` and `∂_p F₂ > 0`
(strict convexity of `x ↦ x^d`, `pow_tangent_lt`), hence `u_a' > 0`.

`contact_deriv_ub_neg`: symmetrically, the right contact map is strictly
decreasing (`dx_b/dp < 0`), via the slope-equation derivative system and the
right-endpoint tangent bound `pow_tangent_lt_right`.

Provides the joint 2-variable Fréchet derivatives of `Jp`, `Jp'`, `sCM`
(`hasFDerivAt_Jp_joint` etc.) and the chain-rule helper `hasDerivAt_comp_pair`.
Together with `contacts_analytic` and `contact_localInverse_analytic` this
completes the *local* functional `lem:contact-points` of `paper/paper.tex`.
-/

open UpperTailOptimizers Real Filter Topology
open ContinuousLinearMap

namespace UpperTailOptimizers

/-! ### Joint (two-variable) Fréchet derivatives -/

/-- A neighbourhood of `(p₀,u₀)` (both coords in `(0,1)`) on which both coords of
`w` lie in `(0,1)`. -/
theorem eventually_box {p₀ u₀ : ℝ} (hp0 : 0 < p₀) (hp1 : p₀ < 1) (hu0 : 0 < u₀) (hu1 : u₀ < 1) :
    ∀ᶠ w : ℝ × ℝ in 𝓝 (p₀, u₀), 0 < w.1 ∧ w.1 < 1 ∧ 0 < w.2 ∧ w.2 < 1 := by
  have hmem : (Set.Ioo (0:ℝ) 1) ×ˢ (Set.Ioo (0:ℝ) 1) ∈ 𝓝 (p₀, u₀) :=
    prod_mem_nhds (Ioo_mem_nhds hp0 hp1) (Ioo_mem_nhds hu0 hu1)
  filter_upwards [hmem] with w hw
  obtain ⟨⟨hw1a, hw1b⟩, ⟨hw2a, hw2b⟩⟩ := hw
  exact ⟨hw1a, hw1b, hw2a, hw2b⟩

/-- Joint FDeriv of `Jp` at `(p₀,u₀)`: gradient `(∂_p Jp)•fst + (Jp' p₀ u₀)•snd`. -/
theorem hasFDerivAt_Jp_joint {p₀ u₀ : ℝ} (hp0 : 0 < p₀) (hp1 : p₀ < 1) (hu0 : 0 < u₀) (hu1 : u₀ < 1) :
    HasFDerivAt (fun w : ℝ × ℝ => Jp w.1 w.2)
      ((-u₀ / p₀ + (1 - u₀) / (1 - p₀)) • (ContinuousLinearMap.fst ℝ ℝ ℝ)
        + (Jp' p₀ u₀) • (ContinuousLinearMap.snd ℝ ℝ ℝ)) (p₀, u₀) := by
  have hp0ne : p₀ ≠ 0 := ne_of_gt hp0
  have h1p0ne : (1 - p₀) ≠ 0 := ne_of_gt (by linarith)
  have hu0ne : u₀ ≠ 0 := ne_of_gt hu0
  have h1u0ne : (1 - u₀) ≠ 0 := ne_of_gt (by linarith)
  have hP : HasFDerivAt (fun w : ℝ × ℝ => w.1) (ContinuousLinearMap.fst ℝ ℝ ℝ) (p₀, u₀) :=
    hasFDerivAt_fst
  have hU : HasFDerivAt (fun w : ℝ × ℝ => w.2) (ContinuousLinearMap.snd ℝ ℝ ℝ) (p₀, u₀) :=
    hasFDerivAt_snd
  have h1mP : HasFDerivAt (fun w : ℝ × ℝ => 1 - w.1) (-ContinuousLinearMap.fst ℝ ℝ ℝ) (p₀, u₀) := by
    simpa using (hasFDerivAt_const (1:ℝ) (p₀,u₀)).fun_sub hP
  have h1mU : HasFDerivAt (fun w : ℝ × ℝ => 1 - w.2) (-ContinuousLinearMap.snd ℝ ℝ ℝ) (p₀, u₀) := by
    simpa using (hasFDerivAt_const (1:ℝ) (p₀,u₀)).fun_sub hU
  have hlogP := (Real.hasDerivAt_log hp0ne).comp_hasFDerivAt (p₀, u₀) hP
  have hlogU := (Real.hasDerivAt_log hu0ne).comp_hasFDerivAt (p₀, u₀) hU
  have hlog1mP := (Real.hasDerivAt_log h1p0ne).comp_hasFDerivAt (p₀, u₀) h1mP
  have hlog1mU := (Real.hasDerivAt_log h1u0ne).comp_hasFDerivAt (p₀, u₀) h1mU
  have hA : HasFDerivAt (fun w : ℝ × ℝ => w.2 * (Real.log w.2 - Real.log w.1)) _ (p₀, u₀) :=
    hU.mul (hlogU.sub hlogP)
  have hB : HasFDerivAt (fun w : ℝ × ℝ => (1 - w.2) * (Real.log (1 - w.2) - Real.log (1 - w.1))) _ (p₀, u₀) :=
    h1mU.mul (hlog1mU.sub hlog1mP)
  have hsum := hA.add hB
  have hbox := eventually_box hp0 hp1 hu0 hu1
  have hagree : (fun w : ℝ × ℝ => Jp w.1 w.2) =ᶠ[𝓝 (p₀, u₀)]
      (fun w : ℝ × ℝ => w.2 * (Real.log w.2 - Real.log w.1)
        + (1 - w.2) * (Real.log (1 - w.2) - Real.log (1 - w.1))) := by
    filter_upwards [hbox] with w hw
    obtain ⟨hw1a, hw1b, hw2a, hw2b⟩ := hw
    unfold Jp
    rw [Real.log_div hw2a.ne' hw1a.ne',
      Real.log_div (by linarith : (1 - w.2) ≠ 0) (by linarith : (1 - w.1) ≠ 0)]
  have hres := hsum.congr_of_eventuallyEq hagree
  convert hres using 1
  all_goals try rfl
  apply ContinuousLinearMap.ext
  intro dw
  obtain ⟨d1, d2⟩ := dw
  simp only [add_apply, sub_apply,
    smul_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    smul_eq_mul, neg_apply]
  rw [Jp'_eq_sub hp0 hp1 hu0 hu1, Real.log_div hu0ne hp0ne,
    Real.log_div h1u0ne h1p0ne]
  field_simp
  ring

/-- Joint FDeriv of `Jp'` at `(p₀,u₀)`: gradient `(-1/(p(1-p)))•fst + (Jp'' u₀)•snd`. -/
theorem hasFDerivAt_Jp'_joint {p₀ u₀ : ℝ} (hp0 : 0 < p₀) (hp1 : p₀ < 1) (hu0 : 0 < u₀) (hu1 : u₀ < 1) :
    HasFDerivAt (fun w : ℝ × ℝ => Jp' w.1 w.2)
      ((-1 / (p₀ * (1 - p₀))) • (ContinuousLinearMap.fst ℝ ℝ ℝ)
        + (Jp'' u₀) • (ContinuousLinearMap.snd ℝ ℝ ℝ)) (p₀, u₀) := by
  have hp0ne : p₀ ≠ 0 := ne_of_gt hp0
  have h1p0ne : (1 - p₀) ≠ 0 := ne_of_gt (by linarith)
  have hu0ne : u₀ ≠ 0 := ne_of_gt hu0
  have h1u0ne : (1 - u₀) ≠ 0 := ne_of_gt (by linarith)
  have hP : HasFDerivAt (fun w : ℝ × ℝ => w.1) (ContinuousLinearMap.fst ℝ ℝ ℝ) (p₀, u₀) :=
    hasFDerivAt_fst
  have hU : HasFDerivAt (fun w : ℝ × ℝ => w.2) (ContinuousLinearMap.snd ℝ ℝ ℝ) (p₀, u₀) :=
    hasFDerivAt_snd
  have h1mP : HasFDerivAt (fun w : ℝ × ℝ => 1 - w.1) (-ContinuousLinearMap.fst ℝ ℝ ℝ) (p₀, u₀) := by
    simpa using (hasFDerivAt_const (1:ℝ) (p₀,u₀)).fun_sub hP
  have h1mU : HasFDerivAt (fun w : ℝ × ℝ => 1 - w.2) (-ContinuousLinearMap.snd ℝ ℝ ℝ) (p₀, u₀) := by
    simpa using (hasFDerivAt_const (1:ℝ) (p₀,u₀)).fun_sub hU
  have hlogP := (Real.hasDerivAt_log hp0ne).comp_hasFDerivAt (p₀, u₀) hP
  have hlogU := (Real.hasDerivAt_log hu0ne).comp_hasFDerivAt (p₀, u₀) hU
  have hlog1mP := (Real.hasDerivAt_log h1p0ne).comp_hasFDerivAt (p₀, u₀) h1mP
  have hlog1mU := (Real.hasDerivAt_log h1u0ne).comp_hasFDerivAt (p₀, u₀) h1mU
  have hsum := (hlogU.sub hlogP).sub (hlog1mU.sub hlog1mP)
  have hbox := eventually_box hp0 hp1 hu0 hu1
  have hagree : (fun w : ℝ × ℝ => Jp' w.1 w.2) =ᶠ[𝓝 (p₀, u₀)]
      (fun w : ℝ × ℝ => (Real.log w.2 - Real.log w.1)
        - (Real.log (1 - w.2) - Real.log (1 - w.1))) := by
    filter_upwards [hbox] with w hw
    obtain ⟨hw1a, hw1b, hw2a, hw2b⟩ := hw
    rw [Jp'_eq_sub hw1a hw1b hw2a hw2b, Real.log_div hw2a.ne' hw1a.ne',
      Real.log_div (by linarith : (1 - w.2) ≠ 0) (by linarith : (1 - w.1) ≠ 0)]
  have hres := hsum.congr_of_eventuallyEq hagree
  convert hres using 1
  all_goals try rfl
  apply ContinuousLinearMap.ext
  intro dw
  obtain ⟨d1, d2⟩ := dw
  simp only [add_apply, sub_apply,
    smul_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    smul_eq_mul, neg_apply]
  unfold Jp''
  field_simp
  ring

/-- 1D deriv of `(d·u^{d-1})⁻¹` in `u`. -/
theorem hasDerivAt_invpow {d : ℕ} (hd : 2 ≤ d) {u₀ : ℝ} (hu0 : 0 < u₀) :
    HasDerivAt (fun u : ℝ => ((d : ℝ) * u ^ (d - 1))⁻¹)
      (-((d : ℝ) * ((↑(d-1) : ℝ) * u₀ ^ (d - 1 - 1))) / ((d : ℝ) * u₀ ^ (d - 1)) ^ 2) u₀ := by
  have hden : HasDerivAt (fun u : ℝ => (d : ℝ) * u ^ (d - 1))
      ((d : ℝ) * ((↑(d - 1) : ℝ) * u₀ ^ (d - 1 - 1))) u₀ :=
    (hasDerivAt_pow (d - 1) u₀).const_mul (d : ℝ)
  have hdenne : (d : ℝ) * u₀ ^ (d - 1) ≠ 0 := by
    have := dpos hd; positivity
  exact hden.fun_inv hdenne

/-- Joint FDeriv of `sCM` at `(p₀,u₀)`: gradient
`(-1/(p(1-p)·d·u^{d-1}))•fst + (hpd p d u/(d·u^d))•snd`. -/
theorem hasFDerivAt_sCM_joint {d : ℕ} (hd : 2 ≤ d) {p₀ u₀ : ℝ}
    (hp0 : 0 < p₀) (hp1 : p₀ < 1) (hu0 : 0 < u₀) (hu1 : u₀ < 1) :
    HasFDerivAt (fun w : ℝ × ℝ => sCM d w.1 w.2)
      ((-1 / (p₀ * (1 - p₀) * ((d : ℝ) * u₀ ^ (d - 1)))) • (ContinuousLinearMap.fst ℝ ℝ ℝ)
        + (hpd p₀ d u₀ / ((d : ℝ) * u₀ ^ d)) • (ContinuousLinearMap.snd ℝ ℝ ℝ)) (p₀, u₀) := by
  have hp0ne : p₀ ≠ 0 := ne_of_gt hp0
  have h1p0ne : (1 - p₀) ≠ 0 := ne_of_gt (by linarith)
  have hu0ne : u₀ ≠ 0 := ne_of_gt hu0
  have hdne : (d : ℝ) ≠ 0 := ne_of_gt (dpos hd)
  have hupowne : u₀ ^ (d - 1) ≠ 0 := pow_ne_zero _ hu0ne
  have hdenne : (d : ℝ) * u₀ ^ (d - 1) ≠ 0 := mul_ne_zero hdne hupowne
  have hU : HasFDerivAt (fun w : ℝ × ℝ => w.2) (ContinuousLinearMap.snd ℝ ℝ ℝ) (p₀, u₀) :=
    hasFDerivAt_snd
  have hJp' := hasFDerivAt_Jp'_joint hp0 hp1 hu0 hu1
  have hinv := (hasDerivAt_invpow hd hu0).comp_hasFDerivAt (p₀, u₀) hU
  have hmul := hJp'.mul hinv
  have hfun : ((fun w : ℝ × ℝ => Jp' w.1 w.2) *
      (fun u : ℝ => ((d : ℝ) * u ^ (d - 1))⁻¹) ∘ (fun w : ℝ × ℝ => w.2))
      = (fun w : ℝ × ℝ => sCM d w.1 w.2) := by
    funext w
    simp only [Pi.mul_apply, Function.comp_apply]
    rw [sCM, div_eq_mul_inv]
  rw [hfun] at hmul
  convert hmul using 1
  all_goals try rfl
  apply ContinuousLinearMap.ext
  intro dw
  obtain ⟨d1, d2⟩ := dw
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul,
    Function.comp_apply]
  have hd1eq : d - 1 = (d - 1 - 1) + 1 := by omega
  have hd0eq : d = (d - 1 - 1) + 2 := by omega
  have hcast : (↑(d - 1) : ℝ) = (d : ℝ) - 1 := by
    have : 1 ≤ d := by omega
    push_cast [Nat.cast_sub this]; ring
  set m := u₀ ^ (d - 1 - 1) with hm
  have hmne : m ≠ 0 := pow_ne_zero _ hu0ne
  have e1 : u₀ ^ (d - 1) = u₀ * m := by rw [hd1eq, pow_succ]; ring
  have e2 : u₀ ^ d = u₀ * u₀ * m := by rw [hd0eq, pow_succ, pow_succ]; ring
  rw [hpd_eq hu0 hu1, hcast, e1, e2]
  unfold Jp''
  field_simp
  ring

/-! ### Composition helper -/

/-- If `F` has joint gradient `Dp•fst + Du•snd` at `(p₀, u p₀)` and `u` has derivative
`va` at `p₀`, then `p ↦ F p (u p)` has derivative `Dp + Du·va` at `p₀`. -/
theorem hasDerivAt_comp_pair {F : ℝ → ℝ → ℝ} {Dp Du : ℝ} {p₀ u₀ : ℝ} {ua : ℝ → ℝ} {va : ℝ}
    (hF : HasFDerivAt (fun w : ℝ × ℝ => F w.1 w.2)
      (Dp • (ContinuousLinearMap.fst ℝ ℝ ℝ) + Du • (ContinuousLinearMap.snd ℝ ℝ ℝ)) (p₀, u₀))
    (hua : HasDerivAt ua va p₀) (hu0 : ua p₀ = u₀) :
    HasDerivAt (fun p => F p (ua p)) (Dp + Du * va) p₀ := by
  have hcurve : HasDerivAt (fun p => (p, ua p)) ((1 : ℝ), va) p₀ :=
    (hasDerivAt_id p₀).prodMk hua
  have hcurve0 : (fun p => (p, ua p)) p₀ = (p₀, u₀) := by simp [hu0]
  rw [← hcurve0] at hF
  have hcomp := hF.comp_hasDerivAt p₀ hcurve
  have hval : (Dp • (ContinuousLinearMap.fst ℝ ℝ ℝ)
      + Du • (ContinuousLinearMap.snd ℝ ℝ ℝ)) ((1 : ℝ), va) = Dp + Du * va := by
    simp only [add_apply, smul_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul]
    ring
  rw [hval] at hcomp
  exact hcomp

/-! ### Strict convexity bound -/

open Finset in
/-- Strict convexity (tangent-line underestimate) for `x ↦ x^d` on `(0,∞)`:
for `0 < a < b` and `d ≥ 2`, `d·a^{d-1}·(b-a) < b^d - a^d`. -/
theorem pow_tangent_lt {d : ℕ} (hd : 2 ≤ d) {a b : ℝ} (ha0 : 0 < a) (hab : a < b) :
    (d : ℝ) * a ^ (d - 1) * (b - a) < b ^ d - a ^ d := by
  have hb0 : 0 < b := lt_trans ha0 hab
  have hbma : 0 < b - a := by linarith
  have hfact : (∑ i ∈ range d, b ^ i * a ^ (d - 1 - i)) * (b - a) = b ^ d - a ^ d :=
    geom_sum₂_mul b a d
  have hconst : (∑ _i ∈ range d, a ^ (d - 1)) = (d : ℝ) * a ^ (d - 1) := by
    rw [Finset.sum_const, Finset.card_range]
    simp [nsmul_eq_mul]
  have hle : ∀ i ∈ range d, a ^ (d - 1) ≤ b ^ i * a ^ (d - 1 - i) := by
    intro i hi
    rw [Finset.mem_range] at hi
    have hsplit : a ^ (d - 1) = a ^ i * a ^ (d - 1 - i) := by
      rw [← pow_add]; congr 1; omega
    rw [hsplit]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact pow_le_pow_left₀ (le_of_lt ha0) (le_of_lt hab) i
  have hlt : ∃ i ∈ range d, a ^ (d - 1) < b ^ i * a ^ (d - 1 - i) := by
    refine ⟨1, ?_, ?_⟩
    · rw [Finset.mem_range]; omega
    · have hsplit : a ^ (d - 1) = a ^ 1 * a ^ (d - 1 - 1) := by
        rw [← pow_add]; congr 1; omega
      rw [hsplit, pow_one, pow_one]
      apply mul_lt_mul_of_pos_right hab (by positivity)
  have hsum_lt : (∑ _i ∈ range d, a ^ (d - 1)) < ∑ i ∈ range d, b ^ i * a ^ (d - 1 - i) :=
    Finset.sum_lt_sum hle hlt
  rw [hconst] at hsum_lt
  calc (d : ℝ) * a ^ (d - 1) * (b - a)
      < (∑ i ∈ range d, b ^ i * a ^ (d - 1 - i)) * (b - a) := by
        apply mul_lt_mul_of_pos_right hsum_lt hbma
    _ = b ^ d - a ^ d := hfact

/-! ### Main theorem -/

/-- **Layer 4 (left contact monotonicity).**  At a non-degenerate solution of the
contact system, differentiating the chord equation in `p` gives
`deriv ua p₀ > 0` (`dx_a/dp > 0`). -/
theorem contact_deriv_ua_pos {d : ℕ} (hd : 2 ≤ d) {a₀ b₀ p₀ : ℝ}
    (ha0 : 0 < a₀) (hab : a₀ < b₀) (hb1 : b₀ < 1) (hp0 : 0 < p₀) (hp1 : p₀ < 1)
    {ua ub : ℝ → ℝ}
    (hua : DifferentiableAt ℝ ua p₀) (hub : DifferentiableAt ℝ ub p₀)
    (hua0 : ua p₀ = a₀) (hub0 : ub p₀ = b₀)
    (hsol : ∀ᶠ p in 𝓝 p₀, contactF d (ua p, ub p) p = (0, 0))
    (hslope : sCM d p₀ a₀ = sCM d p₀ b₀)
    (hha : 0 < hpd p₀ d a₀) (_hhb : 0 < hpd p₀ d b₀) :
    0 < deriv ua p₀ := by
  have hb0 : 0 < b₀ := lt_trans ha0 hab
  have ha1 : a₀ < 1 := lt_trans hab hb1
  set va := deriv ua p₀ with hva
  set vb := deriv ub p₀ with hvb
  have huaD : HasDerivAt ua va p₀ := hua.hasDerivAt
  have hubD : HasDerivAt ub vb p₀ := hub.hasDerivAt
  -- The second component G of contactF is eventually 0.
  set G : ℝ → ℝ := fun p => Jp p (ub p) - Jp p (ua p)
    - sCM d p (ua p) * ((ub p) ^ d - (ua p) ^ d) with hG
  have hGzero : G =ᶠ[𝓝 p₀] (fun _ => (0 : ℝ)) := by
    filter_upwards [hsol] with p hp
    have : (contactF d (ua p, ub p) p).2 = 0 := by rw [hp]
    simpa [contactF, hG] using this
  -- Term derivatives via composition helper.
  have hT1 : HasDerivAt (fun p => Jp p (ub p))
      ((-b₀ / p₀ + (1 - b₀) / (1 - p₀)) + Jp' p₀ b₀ * vb) p₀ :=
    hasDerivAt_comp_pair (hasFDerivAt_Jp_joint hp0 hp1 hb0 hb1) hubD hub0
  have hT2 : HasDerivAt (fun p => Jp p (ua p))
      ((-a₀ / p₀ + (1 - a₀) / (1 - p₀)) + Jp' p₀ a₀ * va) p₀ :=
    hasDerivAt_comp_pair (hasFDerivAt_Jp_joint hp0 hp1 ha0 ha1) huaD hua0
  have hT3 : HasDerivAt (fun p => sCM d p (ua p))
      ((-1 / (p₀ * (1 - p₀) * ((d : ℝ) * a₀ ^ (d - 1))))
        + (hpd p₀ d a₀ / ((d : ℝ) * a₀ ^ d)) * va) p₀ :=
    hasDerivAt_comp_pair (hasFDerivAt_sCM_joint hd hp0 hp1 ha0 ha1) huaD hua0
  -- T4 = (ub p)^d - (ua p)^d
  have hub_pow : HasDerivAt (fun p => (ub p) ^ d) ((d : ℝ) * (ub p₀) ^ (d - 1) * vb) p₀ :=
    hubD.fun_pow d
  have hua_pow : HasDerivAt (fun p => (ua p) ^ d) ((d : ℝ) * (ua p₀) ^ (d - 1) * va) p₀ :=
    huaD.fun_pow d
  have hT4 : HasDerivAt (fun p => (ub p) ^ d - (ua p) ^ d)
      ((d : ℝ) * (ub p₀) ^ (d - 1) * vb - (d : ℝ) * (ua p₀) ^ (d - 1) * va) p₀ :=
    hub_pow.sub hua_pow
  -- product rule for sCM·(pow diff)
  have hT34 := hT3.mul hT4
  -- assemble G
  have hGderiv : HasDerivAt G _ p₀ := (hT1.sub hT2).sub hT34
  -- G is eventually constant 0, so its derivative is 0
  have hGderiv0 : HasDerivAt G 0 p₀ :=
    (hasDerivAt_const p₀ (0:ℝ)).congr_of_eventuallyEq hGzero
  have hkey := hGderiv.unique hGderiv0
  -- rewrite the point values ua p₀ = a₀, ub p₀ = b₀
  rw [hua0, hub0] at hkey
  -- abbreviations and basic positivity
  have hane : a₀ ≠ 0 := ne_of_gt ha0
  have hbne : b₀ ≠ 0 := ne_of_gt hb0
  have hp0ne : p₀ ≠ 0 := ne_of_gt hp0
  have h1p0ne : (1 - p₀) ≠ 0 := ne_of_gt (by linarith)
  have hdpos : (0 : ℝ) < (d : ℝ) := dpos hd
  have hdne : (d : ℝ) ≠ 0 := ne_of_gt hdpos
  have hapd : (0 : ℝ) < (d : ℝ) * a₀ ^ d := by positivity
  have hapd1 : (0 : ℝ) < (d : ℝ) * a₀ ^ (d - 1) := by positivity
  have hpowlt : a₀ ^ d < b₀ ^ d := pow_lt_pow_left₀ hab (le_of_lt ha0) (by omega : d ≠ 0)
  -- slope identities at the contact
  have hSa : sCM d p₀ a₀ * ((d : ℝ) * a₀ ^ (d - 1)) = Jp' p₀ a₀ := sCM_mul_dpow hd ha0
  have hSb : sCM d p₀ a₀ * ((d : ℝ) * b₀ ^ (d - 1)) = Jp' p₀ b₀ := by
    rw [hslope]; exact sCM_mul_dpow hd hb0
  -- definitions of the va-coefficient γ and the ∂_p part Dp
  set γ : ℝ := -(hpd p₀ d a₀ / ((d : ℝ) * a₀ ^ d)) * (b₀ ^ d - a₀ ^ d) with hγdef
  set Dp : ℝ := (1 / (p₀ * (1 - p₀))) * (-(b₀ - a₀) + (b₀ ^ d - a₀ ^ d) / ((d : ℝ) * a₀ ^ (d - 1)))
    with hDpdef
  -- eliminate Jp' from hkey using the slope identities
  rw [← hSa, ← hSb] at hkey
  -- reduce hkey to γ * va + Dp = 0
  have hreduced : γ * va + Dp = 0 := by
    rw [hγdef, hDpdef]
    field_simp
    field_simp at hkey
    linear_combination hkey
  -- sign of γ : negative
  have hγneg : γ < 0 := by
    rw [hγdef]
    have h1 : 0 < hpd p₀ d a₀ / ((d : ℝ) * a₀ ^ d) := div_pos hha hapd
    have h2 : 0 < b₀ ^ d - a₀ ^ d := by linarith
    nlinarith [mul_pos h1 h2]
  -- sign of Dp : positive (strict convexity)
  have hDppos : 0 < Dp := by
    rw [hDpdef]
    have hconv := pow_tangent_lt hd ha0 hab
    have hfrac : b₀ - a₀ < (b₀ ^ d - a₀ ^ d) / ((d : ℝ) * a₀ ^ (d - 1)) := by
      rw [lt_div_iff₀ hapd1]; nlinarith [hconv]
    have hbracket : 0 < -(b₀ - a₀) + (b₀ ^ d - a₀ ^ d) / ((d : ℝ) * a₀ ^ (d - 1)) := by linarith
    have hp1p : 0 < p₀ * (1 - p₀) := mul_pos hp0 (by linarith)
    have hpre : 0 < 1 / (p₀ * (1 - p₀)) := by positivity
    exact mul_pos hpre hbracket
  -- conclude: γ * va = -Dp < 0 with γ < 0 ⟹ va > 0
  have hva_eq : γ * va = -Dp := by linarith [hreduced]
  nlinarith [hva_eq, hγneg, hDppos]

open Finset in
/-- Strict convexity (tangent-line at the RIGHT endpoint overestimate) for `x ↦ x^d`
on `(0,∞)`: for `0 < a < b` and `d ≥ 2`, `b^d - a^d < d·b^{d-1}·(b-a)`. -/
private theorem pow_tangent_lt_right {d : ℕ} (hd : 2 ≤ d) {a b : ℝ} (ha0 : 0 < a) (hab : a < b) :
    b ^ d - a ^ d < (d : ℝ) * b ^ (d - 1) * (b - a) := by
  have hb0 : 0 < b := lt_trans ha0 hab
  have hbma : 0 < b - a := by linarith
  have hfact : (∑ i ∈ range d, b ^ i * a ^ (d - 1 - i)) * (b - a) = b ^ d - a ^ d :=
    geom_sum₂_mul b a d
  have hconst : (∑ _i ∈ range d, b ^ (d - 1)) = (d : ℝ) * b ^ (d - 1) := by
    rw [Finset.sum_const, Finset.card_range]
    simp [nsmul_eq_mul]
  have hle : ∀ i ∈ range d, b ^ i * a ^ (d - 1 - i) ≤ b ^ (d - 1) := by
    intro i hi
    rw [Finset.mem_range] at hi
    have hsplit : b ^ (d - 1) = b ^ i * b ^ (d - 1 - i) := by
      rw [← pow_add]; congr 1; omega
    rw [hsplit]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact pow_le_pow_left₀ (le_of_lt ha0) (le_of_lt hab) (d - 1 - i)
  have hlt : ∃ i ∈ range d, b ^ i * a ^ (d - 1 - i) < b ^ (d - 1) := by
    refine ⟨0, ?_, ?_⟩
    · rw [Finset.mem_range]; omega
    · rw [pow_zero, one_mul, Nat.sub_zero]
      exact pow_lt_pow_left₀ hab (le_of_lt ha0) (by omega)
  have hsum_lt : (∑ i ∈ range d, b ^ i * a ^ (d - 1 - i)) < ∑ _i ∈ range d, b ^ (d - 1) :=
    Finset.sum_lt_sum hle hlt
  rw [hconst] at hsum_lt
  calc b ^ d - a ^ d
      = (∑ i ∈ range d, b ^ i * a ^ (d - 1 - i)) * (b - a) := hfact.symm
    _ < ((d : ℝ) * b ^ (d - 1)) * (b - a) := by
        apply mul_lt_mul_of_pos_right hsum_lt hbma
    _ = (d : ℝ) * b ^ (d - 1) * (b - a) := by ring

-- The proof subsumes the full chord-equation reduction of `contact_deriv_ua_pos`
-- (re-derived here) plus the slope-equation derivative system, so it needs a higher
-- heartbeat budget than the default.
set_option maxHeartbeats 800000 in
/-- **Layer 4 (right contact monotonicity).**  Under the same hypotheses,
`deriv ub p₀ < 0` (`dx_b/dp < 0`). -/
theorem contact_deriv_ub_neg {d : ℕ} (hd : 2 ≤ d) {a₀ b₀ p₀ : ℝ}
    (ha0 : 0 < a₀) (hab : a₀ < b₀) (hb1 : b₀ < 1) (hp0 : 0 < p₀) (hp1 : p₀ < 1)
    {ua ub : ℝ → ℝ}
    (hua : DifferentiableAt ℝ ua p₀) (hub : DifferentiableAt ℝ ub p₀)
    (hua0 : ua p₀ = a₀) (hub0 : ub p₀ = b₀)
    (hsol : ∀ᶠ p in 𝓝 p₀, contactF d (ua p, ub p) p = (0, 0))
    (hslope : sCM d p₀ a₀ = sCM d p₀ b₀)
    (hha : 0 < hpd p₀ d a₀) (hhb : 0 < hpd p₀ d b₀) :
    deriv ub p₀ < 0 := by
  have hb0 : 0 < b₀ := lt_trans ha0 hab
  have ha1 : a₀ < 1 := lt_trans hab hb1
  -- (1) From `contact_deriv_ua_pos`, the left contact map is strictly increasing.
  have hvapos : 0 < deriv ua p₀ :=
    contact_deriv_ua_pos hd ha0 hab hb1 hp0 hp1 hua hub hua0 hub0 hsol hslope hha hhb
  set va := deriv ua p₀ with hva
  set vb := deriv ub p₀ with hvb
  have huaD : HasDerivAt ua va p₀ := hua.hasDerivAt
  have hubD : HasDerivAt ub vb p₀ := hub.hasDerivAt
  -- basic positivity / nonvanishing facts
  have hane : a₀ ≠ 0 := ne_of_gt ha0
  have hbne : b₀ ≠ 0 := ne_of_gt hb0
  have hp0ne : p₀ ≠ 0 := ne_of_gt hp0
  have h1p0ne : (1 - p₀) ≠ 0 := ne_of_gt (by linarith)
  have hdpos : (0 : ℝ) < (d : ℝ) := dpos hd
  have hdne : (d : ℝ) ≠ 0 := ne_of_gt hdpos
  have hapd : (0 : ℝ) < (d : ℝ) * a₀ ^ d := by positivity
  have hbpd : (0 : ℝ) < (d : ℝ) * b₀ ^ d := by positivity
  have hapd1 : (0 : ℝ) < (d : ℝ) * a₀ ^ (d - 1) := by positivity
  have hbpd1 : (0 : ℝ) < (d : ℝ) * b₀ ^ (d - 1) := by positivity
  have hapd1ne : (d : ℝ) * a₀ ^ (d - 1) ≠ 0 := ne_of_gt hapd1
  have hbpd1ne : (d : ℝ) * b₀ ^ (d - 1) ≠ 0 := ne_of_gt hbpd1
  have hapdne : (d : ℝ) * a₀ ^ d ≠ 0 := ne_of_gt hapd
  have hbpdne : (d : ℝ) * b₀ ^ d ≠ 0 := ne_of_gt hbpd
  have hpowlt : a₀ ^ d < b₀ ^ d := pow_lt_pow_left₀ hab (le_of_lt ha0) (by omega : d ≠ 0)
  have hΔx : 0 < b₀ ^ d - a₀ ^ d := by linarith
  have hΔxne : b₀ ^ d - a₀ ^ d ≠ 0 := ne_of_gt hΔx
  -- the positive slope-derivatives sa', sb'
  set sa' : ℝ := hpd p₀ d a₀ / ((d : ℝ) * a₀ ^ d) with hsa'def
  set sb' : ℝ := hpd p₀ d b₀ / ((d : ℝ) * b₀ ^ d) with hsb'def
  have hsa'pos : 0 < sa' := div_pos hha hapd
  have hsb'pos : 0 < sb' := div_pos hhb hbpd
  -- slope identities at the contact (as in `contact_deriv_ua_pos`)
  have hSa : sCM d p₀ a₀ * ((d : ℝ) * a₀ ^ (d - 1)) = Jp' p₀ a₀ := sCM_mul_dpow hd ha0
  have hSb : sCM d p₀ a₀ * ((d : ℝ) * b₀ ^ (d - 1)) = Jp' p₀ b₀ := by
    rw [hslope]; exact sCM_mul_dpow hd hb0
  -- ===================================================================
  -- (3) Reduced chord equation: γ * va + Dp = 0  (replicated verbatim).
  -- ===================================================================
  set G : ℝ → ℝ := fun p => Jp p (ub p) - Jp p (ua p)
    - sCM d p (ua p) * ((ub p) ^ d - (ua p) ^ d) with hG
  have hGzero : G =ᶠ[𝓝 p₀] (fun _ => (0 : ℝ)) := by
    filter_upwards [hsol] with p hp
    have : (contactF d (ua p, ub p) p).2 = 0 := by rw [hp]
    simpa [contactF, hG] using this
  have hT1 : HasDerivAt (fun p => Jp p (ub p))
      ((-b₀ / p₀ + (1 - b₀) / (1 - p₀)) + Jp' p₀ b₀ * vb) p₀ :=
    hasDerivAt_comp_pair (hasFDerivAt_Jp_joint hp0 hp1 hb0 hb1) hubD hub0
  have hT2 : HasDerivAt (fun p => Jp p (ua p))
      ((-a₀ / p₀ + (1 - a₀) / (1 - p₀)) + Jp' p₀ a₀ * va) p₀ :=
    hasDerivAt_comp_pair (hasFDerivAt_Jp_joint hp0 hp1 ha0 ha1) huaD hua0
  have hT3 : HasDerivAt (fun p => sCM d p (ua p))
      ((-1 / (p₀ * (1 - p₀) * ((d : ℝ) * a₀ ^ (d - 1))))
        + (hpd p₀ d a₀ / ((d : ℝ) * a₀ ^ d)) * va) p₀ :=
    hasDerivAt_comp_pair (hasFDerivAt_sCM_joint hd hp0 hp1 ha0 ha1) huaD hua0
  have hub_pow : HasDerivAt (fun p => (ub p) ^ d) ((d : ℝ) * (ub p₀) ^ (d - 1) * vb) p₀ :=
    hubD.fun_pow d
  have hua_pow : HasDerivAt (fun p => (ua p) ^ d) ((d : ℝ) * (ua p₀) ^ (d - 1) * va) p₀ :=
    huaD.fun_pow d
  have hT4 : HasDerivAt (fun p => (ub p) ^ d - (ua p) ^ d)
      ((d : ℝ) * (ub p₀) ^ (d - 1) * vb - (d : ℝ) * (ua p₀) ^ (d - 1) * va) p₀ :=
    hub_pow.sub hua_pow
  have hT34 := hT3.mul hT4
  have hGderiv : HasDerivAt G _ p₀ := (hT1.sub hT2).sub hT34
  have hGderiv0 : HasDerivAt G 0 p₀ :=
    (hasDerivAt_const p₀ (0:ℝ)).congr_of_eventuallyEq hGzero
  have hkey := hGderiv.unique hGderiv0
  rw [hua0, hub0] at hkey
  set γ : ℝ := -(hpd p₀ d a₀ / ((d : ℝ) * a₀ ^ d)) * (b₀ ^ d - a₀ ^ d) with hγdef
  set Dp : ℝ := (1 / (p₀ * (1 - p₀))) * (-(b₀ - a₀) + (b₀ ^ d - a₀ ^ d) / ((d : ℝ) * a₀ ^ (d - 1)))
    with hDpdef
  rw [← hSa, ← hSb] at hkey
  have hreduced : γ * va + Dp = 0 := by
    rw [hγdef, hDpdef]
    field_simp
    field_simp at hkey
    linear_combination hkey
  -- From γ * va + Dp = 0 with γ = -sa'·Δx: solve for sa'·va = Dp / Δx.
  have hγeq : γ = -sa' * (b₀ ^ d - a₀ ^ d) := by rw [hγdef, hsa'def]
  have hsava : sa' * va = Dp / (b₀ ^ d - a₀ ^ d) := by
    rw [eq_div_iff hΔxne]
    have hr : -sa' * (b₀ ^ d - a₀ ^ d) * va + Dp = 0 := by rw [← hγeq]; exact hreduced
    linear_combination -hr
  -- ===================================================================
  -- (2) First component F1 = sCM(·,ua) - sCM(·,ub) is eventually 0  ⇒  Eq. I.
  -- ===================================================================
  set F1 : ℝ → ℝ := fun p => sCM d p (ua p) - sCM d p (ub p) with hF1
  have hF1zero : F1 =ᶠ[𝓝 p₀] (fun _ => (0 : ℝ)) := by
    filter_upwards [hsol] with p hp
    have : (contactF d (ua p, ub p) p).1 = 0 := by rw [hp]
    simpa [contactF, hF1] using this
  -- derivative of sCM(·, ub) at p₀
  have hS3b : HasDerivAt (fun p => sCM d p (ub p))
      ((-1 / (p₀ * (1 - p₀) * ((d : ℝ) * b₀ ^ (d - 1))))
        + (hpd p₀ d b₀ / ((d : ℝ) * b₀ ^ d)) * vb) p₀ :=
    hasDerivAt_comp_pair (hasFDerivAt_sCM_joint hd hp0 hp1 hb0 hb1) hubD hub0
  have hF1deriv : HasDerivAt F1 _ p₀ := hT3.sub hS3b
  have hF1deriv0 : HasDerivAt F1 0 p₀ :=
    (hasDerivAt_const p₀ (0:ℝ)).congr_of_eventuallyEq hF1zero
  have hI := hF1deriv.unique hF1deriv0
  -- hI : (∂ₚsCM(a₀) + sa'·va) - (∂ₚsCM(b₀) + sb'·vb) = 0
  -- rewrite to fold in sa', sb'
  rw [← hsa'def, ← hsb'def] at hI
  -- ===================================================================
  -- (4) Solve for sb'·vb and show it is negative.
  -- ===================================================================
  -- abbreviate the two ∂ₚsCM values (folds the literal expressions in `hI` too)
  set dpa : ℝ := -1 / (p₀ * (1 - p₀) * ((d : ℝ) * a₀ ^ (d - 1))) with hdpa
  set dpb : ℝ := -1 / (p₀ * (1 - p₀) * ((d : ℝ) * b₀ ^ (d - 1))) with hdpb
  -- from hI: sb'·vb = dpa + sa'·va - dpb
  have hsbvb_eq : sb' * vb = dpa + sa' * va - dpb := by linarith [hI]
  -- substitute sa'·va = Dp/Δx
  rw [hsava] at hsbvb_eq
  -- collapse the RHS algebraically to the right-secant defect form.
  have hp1p : 0 < p₀ * (1 - p₀) := mul_pos hp0 (by linarith)
  have hp1pne : p₀ * (1 - p₀) ≠ 0 := ne_of_gt hp1p
  have hRHS : dpa + Dp / (b₀ ^ d - a₀ ^ d) - dpb
      = (1 / (p₀ * (1 - p₀)))
        * (1 / ((d : ℝ) * b₀ ^ (d - 1)) - (b₀ - a₀) / (b₀ ^ d - a₀ ^ d)) := by
    rw [hdpa, hdpb, hDpdef]
    field_simp
    ring
  rw [hRHS] at hsbvb_eq
  -- The bracket is negative by the right-tangent strict convexity bound.
  have hbracket_neg :
      1 / ((d : ℝ) * b₀ ^ (d - 1)) - (b₀ - a₀) / (b₀ ^ d - a₀ ^ d) < 0 := by
    have hconv := pow_tangent_lt_right hd ha0 hab
    -- 1/(d b^{d-1}) < (b-a)/Δx  ⟺  Δx < d b^{d-1} (b-a)
    have hlt : 1 / ((d : ℝ) * b₀ ^ (d - 1)) < (b₀ - a₀) / (b₀ ^ d - a₀ ^ d) := by
      rw [div_lt_div_iff₀ hbpd1 hΔx, one_mul]
      nlinarith [hconv]
    linarith
  have hpre : 0 < 1 / (p₀ * (1 - p₀)) := by positivity
  have hRHSneg : (1 / (p₀ * (1 - p₀)))
      * (1 / ((d : ℝ) * b₀ ^ (d - 1)) - (b₀ - a₀) / (b₀ ^ d - a₀ ^ d)) < 0 :=
    mul_neg_of_pos_of_neg hpre hbracket_neg
  -- sb'·vb < 0 and sb' > 0 ⟹ vb < 0
  have hsbvb_neg : sb' * vb < 0 := by rw [hsbvb_eq]; exact hRHSneg
  nlinarith [hsbvb_neg, hsb'pos]

end UpperTailOptimizers
