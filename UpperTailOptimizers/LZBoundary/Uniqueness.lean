import UpperTailOptimizers.LZBoundary.Arc
import UpperTailOptimizers.Graphon.ExternalInputs

/-!
# Boundary uniqueness at `p = pc(r)` (the boundary case of `thm:local-optimizer-structure`(a))

At a boundary point `p₀ = pc(r)` of an oriented regular Lubetzky–Zhao boundary arc, the constant
graphon `W ≡ r` is the unique minimizer of
`inf { I_{p₀}(W) : t(H,W) ≥ r^m }`.

`paper/bipodal_optimizer.tex` has no separate lemma for this: the proof of `thm:local-optimizer-structure`(a)
(`thm:local-optimizer-structure`) covers the closed side `p ≥ pc(r)` in one step, using condition (M2)
of `thm:scalar-lz-boundary` — an equivalence valid for every `p ∈ (0,1)` — together with the uniqueness
clause of `thm:lz-criterion`.  The Lean development instead
*derives* uniqueness from the Lubetzky–Zhao-arc fields, so it needs the boundary case as a
standalone lemma.

The proof integrates the supporting-line inequality (M3) against any feasible
graphon, uses the generalized-Hölder moment bound `r^d ≤ ∫ W^d`, and the
quadratic separation (M5) for the equality/uniqueness case.
-/

namespace UpperTailOptimizers

open MeasureTheory Real

variable {d : ℕ}

/-- `I_{p}(W ≡ r) = J_p(r)`. -/
theorem Ip_constGraphon {r : ℝ} (hr : r ∈ Set.Icc (0:ℝ) 1) (p : ℝ) :
    (constGraphon r hr).Ip p = Jp p r := by
  unfold Graphon.Ip
  simp only [constGraphon_apply]
  rw [integral_const]
  simp

/-- **Boundary uniqueness.**  At `p₀ = pc(r)`, the constant graphon
`W ≡ r` attains the value `J_{p₀}(r)`, is optimal among all feasible graphons, and
is the unique optimizer (almost everywhere). -/
theorem boundary_uniqueness (hd : 2 ≤ d) (M : LZBoundaryArc d) {r : ℝ} (hr : r ∈ M.U)
    {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (hreg : ∀ v, H.degree v = d) (hm : 1 ≤ H.edgeFinset.card) :
    -- the constant graphon attains `J_{p₀}(r)`
    (∀ hr' : r ∈ Set.Icc (0:ℝ) 1, (constGraphon r hr').Ip (M.pc r) = Jp (M.pc r) r) ∧
    -- optimality: every feasible graphon costs at least `J_{p₀}(r)`
    (∀ W : Graphon, Feasible H r W → Jp (M.pc r) r ≤ W.Ip (M.pc r)) ∧
    -- uniqueness: equality forces `W = r` almost everywhere
    (∀ W : Graphon, Feasible H r W → W.Ip (M.pc r) = Jp (M.pc r) r →
      ∀ᵐ z ∂gμ, W.toFun z.1 z.2 = r) := by
  obtain ⟨hpc0, hpcr, hr1, hsmr, hsm0, hsm1⟩ := M.ordering r hr
  set p₀ := M.pc r with hp₀
  have hr0 : 0 < r := lt_trans hpc0 hpcr
  have hp1 : p₀ < 1 := lt_trans hpcr hr1
  have hd1 : 1 ≤ d := le_trans (by norm_num) hd
  have hslope : 0 < slope d M.pc r := slope_pos hd1 hpc0 hpcr hr1
  have hdne : d ≠ 0 := by omega
  -- injectivity of `· ^ d` on the nonnegatives
  have pow_inj : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a ^ d = b ^ d → a = b := by
    intro a b ha hb hab
    rcases lt_trichotomy a b with h | h | h
    · exact absurd hab (ne_of_lt (pow_lt_pow_left₀ h ha hdne))
    · exact h
    · exact absurd hab.symm (ne_of_lt (pow_lt_pow_left₀ h hb hdne))
  -- integrability shorthands
  have hWd_int : ∀ W : Graphon, Integrable (fun z => (W.toFun z.1 z.2) ^ d) gμ := fun W =>
    W.integrable_comp (continuous_pow d).measurable (continuous_pow d).continuousOn
  have hJpW_int : ∀ W : Graphon, Integrable (fun z => Jp p₀ (W.toFun z.1 z.2)) gμ := fun W =>
    W.integrable_comp (measurable_Jp p₀) (continuousOn_Jp_Icc hpc0 hp1)
  have hL_int : ∀ W : Graphon, Integrable
      (fun z => Jp p₀ r + slope d M.pc r * ((W.toFun z.1 z.2) ^ d - r ^ d)) gμ := fun W =>
    (integrable_const _).add (((hWd_int W).sub (integrable_const _)).const_mul _)
  -- the lower-bound integral `∫ (J_p(r) + slope (W^d - r^d)) = J_p(r) + slope (∫W^d - r^d)`
  have hintL : ∀ W : Graphon,
      ∫ z, (Jp p₀ r + slope d M.pc r * ((W.toFun z.1 z.2) ^ d - r ^ d)) ∂gμ
        = Jp p₀ r + slope d M.pc r * (W.Wmoment d - r ^ d) := by
    intro W
    have ha : ∫ z, (Jp p₀ r + slope d M.pc r * ((W.toFun z.1 z.2) ^ d - r ^ d)) ∂gμ
        = (∫ _ : ℝ × ℝ, Jp p₀ r ∂gμ)
          + ∫ z, slope d M.pc r * ((W.toFun z.1 z.2) ^ d - r ^ d) ∂gμ :=
      integral_add (integrable_const _) (((hWd_int W).sub (integrable_const _)).const_mul _)
    have hb : ∫ z, slope d M.pc r * ((W.toFun z.1 z.2) ^ d - r ^ d) ∂gμ
        = slope d M.pc r * ∫ z, ((W.toFun z.1 z.2) ^ d - r ^ d) ∂gμ := integral_const_mul _ _
    have hc : ∫ z, ((W.toFun z.1 z.2) ^ d - r ^ d) ∂gμ = W.Wmoment d - r ^ d := by
      unfold Graphon.Wmoment
      rw [integral_sub (hWd_int W) (integrable_const _),
        show (∫ _ : ℝ × ℝ, r ^ d ∂gμ) = r ^ d from by rw [integral_const]; simp]
    rw [ha, hb, hc]
    have : ∫ _ : ℝ × ℝ, Jp p₀ r ∂gμ = Jp p₀ r := by rw [integral_const]; simp
    rw [this]
  -- pointwise supporting-line bound for any graphon
  have hsupp : ∀ W : Graphon, ∀ z : ℝ × ℝ,
      Jp p₀ r + slope d M.pc r * ((W.toFun z.1 z.2) ^ d - r ^ d) ≤ Jp p₀ (W.toFun z.1 z.2) :=
    fun W z => M.supporting r hr (W.toFun z.1 z.2) (W.mem_Icc z.1 z.2)
  -- the key lower bound: `I_{p₀}(W) ≥ J_{p₀}(r) + slope (∫W^d - r^d)`
  have hlower : ∀ W : Graphon,
      Jp p₀ r + slope d M.pc r * (W.Wmoment d - r ^ d) ≤ W.Ip p₀ := by
    intro W
    have hmono := integral_mono (hL_int W) (hJpW_int W) (fun z => hsupp W z)
    rw [hintL W] at hmono
    exact hmono
  refine ⟨fun hr' => Ip_constGraphon hr' p₀, ?_, ?_⟩
  · -- optimality
    intro W hWfeas
    have hmom : r ^ d ≤ W.Wmoment d :=
      holder_moment H hreg hd W (le_of_lt hr0) hm hWfeas
    have hnn : 0 ≤ slope d M.pc r * (W.Wmoment d - r ^ d) :=
      mul_nonneg (le_of_lt hslope) (by linarith)
    have := hlower W
    linarith
  · -- uniqueness
    intro W hWfeas hWeq
    have hmom : r ^ d ≤ W.Wmoment d :=
      holder_moment H hreg hd W (le_of_lt hr0) hm hWfeas
    -- from equality, the moment is exactly `r^d`
    have hWmom_eq : W.Wmoment d = r ^ d := by
      by_contra hne
      have hlt : r ^ d < W.Wmoment d := lt_of_le_of_ne hmom (Ne.symm hne)
      have hpos : 0 < slope d M.pc r * (W.Wmoment d - r ^ d) := mul_pos hslope (by linarith)
      have hh := hlower W
      rw [hWeq] at hh; linarith
    -- the gap function is `≥ 0` and integrates to `0`, hence is `0` a.e.
    have hgap_nonneg : ∀ᵐ z ∂gμ, (0:ℝ) ≤
        Jp p₀ (W.toFun z.1 z.2)
          - (Jp p₀ r + slope d M.pc r * ((W.toFun z.1 z.2) ^ d - r ^ d)) := by
      filter_upwards with z; linarith [hsupp W z]
    have hgap_int : Integrable (fun z =>
        Jp p₀ (W.toFun z.1 z.2)
          - (Jp p₀ r + slope d M.pc r * ((W.toFun z.1 z.2) ^ d - r ^ d))) gμ :=
      (hJpW_int W).sub (hL_int W)
    have hgap_intzero : ∫ z, (Jp p₀ (W.toFun z.1 z.2)
        - (Jp p₀ r + slope d M.pc r * ((W.toFun z.1 z.2) ^ d - r ^ d))) ∂gμ = 0 := by
      rw [integral_sub (hJpW_int W) (hL_int W), hintL W, hWmom_eq]
      have hIp : W.Ip p₀ = ∫ z, Jp p₀ (W.toFun z.1 z.2) ∂gμ := rfl
      rw [← hIp, hWeq]; ring
    have hgap_zero : (fun z => Jp p₀ (W.toFun z.1 z.2)
        - (Jp p₀ r + slope d M.pc r * ((W.toFun z.1 z.2) ^ d - r ^ d))) =ᵐ[gμ] 0 :=
      (integral_eq_zero_iff_of_nonneg_ae hgap_nonneg hgap_int).mp hgap_intzero
    -- quadratic separation at the single point `r`
    obtain ⟨γ, hγ, hquad⟩ := M.quadSep {r} (by simpa using hr) isCompact_singleton
    -- a.e., `W z ∈ {r, sm r}`
    have htwo : ∀ᵐ z ∂gμ, W.toFun z.1 z.2 = r ∨ W.toFun z.1 z.2 = M.sm r := by
      filter_upwards [hgap_zero] with z hz
      have hzgap : Jp p₀ (W.toFun z.1 z.2)
          - (Jp p₀ r + slope d M.pc r * ((W.toFun z.1 z.2) ^ d - r ^ d)) = 0 := by
        simpa using hz
      have hbound := hquad r rfl (W.toFun z.1 z.2) (W.mem_Icc z.1 z.2)
      have hmin0 : min |(W.toFun z.1 z.2) ^ d - r ^ d|
          |(W.toFun z.1 z.2) ^ d - (M.sm r) ^ d| = 0 := by
        by_contra hmne
        have hmn : 0 ≤ min |(W.toFun z.1 z.2) ^ d - r ^ d|
            |(W.toFun z.1 z.2) ^ d - (M.sm r) ^ d| := le_min (abs_nonneg _) (abs_nonneg _)
        have hpos : 0 < (min |(W.toFun z.1 z.2) ^ d - r ^ d|
            |(W.toFun z.1 z.2) ^ d - (M.sm r) ^ d|) ^ 2 := by
          have : 0 < min |(W.toFun z.1 z.2) ^ d - r ^ d|
              |(W.toFun z.1 z.2) ^ d - (M.sm r) ^ d| := lt_of_le_of_ne hmn (Ne.symm hmne)
          positivity
        nlinarith [hbound, hzgap, mul_pos hγ hpos]
      rcases min_choice |(W.toFun z.1 z.2) ^ d - r ^ d|
        |(W.toFun z.1 z.2) ^ d - (M.sm r) ^ d| with hch | hch
      · left
        have hA0 : |(W.toFun z.1 z.2) ^ d - r ^ d| = 0 := by rw [← hch]; exact hmin0
        have : (W.toFun z.1 z.2) ^ d = r ^ d := by
          have := abs_eq_zero.mp hA0; linarith
        exact pow_inj _ _ (W.mem_Icc z.1 z.2).1 hr0.le this
      · right
        have hB0 : |(W.toFun z.1 z.2) ^ d - (M.sm r) ^ d| = 0 := by rw [← hch]; exact hmin0
        have : (W.toFun z.1 z.2) ^ d = (M.sm r) ^ d := by
          have := abs_eq_zero.mp hB0; linarith
        exact pow_inj _ _ (W.mem_Icc z.1 z.2).1 hsm0.le this
    -- `(W z)^d - r^d` has a fixed sign a.e. and integrates to 0, so `W = r` a.e.
    rcases lt_or_gt_of_ne hsmr with hslt | hsgt
    · -- `sm r < r`: then `(W z)^d ≤ r^d` a.e.
      have hle : ∀ᵐ z ∂gμ, (0:ℝ) ≤ r ^ d - (W.toFun z.1 z.2) ^ d := by
        filter_upwards [htwo] with z hz
        rcases hz with h | h
        · rw [h]; simp
        · rw [h]; have := pow_le_pow_left₀ hsm0.le (le_of_lt hslt) d; linarith
      have hint0 : ∫ z, (r ^ d - (W.toFun z.1 z.2) ^ d) ∂gμ = 0 := by
        rw [integral_sub (integrable_const _) (hWd_int W)]
        have h1 : ∫ _ : ℝ × ℝ, r ^ d ∂gμ = r ^ d := by rw [integral_const]; simp
        have h2 : ∫ z, (W.toFun z.1 z.2) ^ d ∂gμ = r ^ d := hWmom_eq
        rw [h1, h2]; ring
      have hzero : (fun z => r ^ d - (W.toFun z.1 z.2) ^ d) =ᵐ[gμ] 0 :=
        (integral_eq_zero_iff_of_nonneg_ae hle
          ((integrable_const _).sub (hWd_int W))).mp hint0
      filter_upwards [hzero] with z hz
      have : (W.toFun z.1 z.2) ^ d = r ^ d := by
        have : r ^ d - (W.toFun z.1 z.2) ^ d = 0 := by simpa using hz
        linarith
      exact pow_inj _ _ (W.mem_Icc z.1 z.2).1 hr0.le this
    · -- `sm r > r`: then `(W z)^d ≥ r^d` a.e.
      have hge : ∀ᵐ z ∂gμ, (0:ℝ) ≤ (W.toFun z.1 z.2) ^ d - r ^ d := by
        filter_upwards [htwo] with z hz
        rcases hz with h | h
        · rw [h]; simp
        · rw [h]; have := pow_le_pow_left₀ hr0.le (le_of_lt hsgt) d; linarith
      have hint0 : ∫ z, ((W.toFun z.1 z.2) ^ d - r ^ d) ∂gμ = 0 := by
        rw [integral_sub (hWd_int W) (integrable_const _)]
        have h1 : ∫ _ : ℝ × ℝ, r ^ d ∂gμ = r ^ d := by rw [integral_const]; simp
        have h2 : ∫ z, (W.toFun z.1 z.2) ^ d ∂gμ = r ^ d := hWmom_eq
        rw [h1, h2]; ring
      have hzero : (fun z => (W.toFun z.1 z.2) ^ d - r ^ d) =ᵐ[gμ] 0 :=
        (integral_eq_zero_iff_of_nonneg_ae hge
          ((hWd_int W).sub (integrable_const _))).mp hint0
      filter_upwards [hzero] with z hz
      have : (W.toFun z.1 z.2) ^ d = r ^ d := by
        have : (W.toFun z.1 z.2) ^ d - r ^ d = 0 := by simpa using hz
        linarith
      exact pow_inj _ _ (W.mem_Icc z.1 z.2).1 hr0.le this

end UpperTailOptimizers
