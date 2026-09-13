import UpperTailOptimizers.Bipodality.SliceBounds
import UpperTailOptimizers.Bipodality.GapQuadratic
import UpperTailOptimizers.KRRS.FamilyCore

/-!
# Entropy of the analytic bipodal family to second order

`kb:eq:family-entropy` of the bipodality draft, in the form it is used:

  `2(S₀(ε) - s(Ŵ_{ε,ϑ})) ≤ |ψ_*|·h_ε(ϑ) + Kϑ²`,   `h_ε(ϑ) = (ε^m + ϑ)^{d/m} - ε^d`,

uniformly for `ε` near `ε₀`.  The first-order coefficient is read off without differentiating
the family: the analytic function
`Φ_S(ε,a,b,c) = 𝒜(ε,b)(Ŝ(ε,a,b,c) - S₀(ε)) - 𝒩_ε(b)(𝒯̂(ε,a,b,c) - ε^m)`
vanishes to second order on `c = 0`, and along the family `𝒯̂ = ε^m + ϑ`.
-/

namespace UpperTailOptimizers

open Real Set Filter Topology

variable {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]

/-- `Φ_S(ε,a,b,c)`. -/
noncomputable def entQuot (d : ℕ) (p : ℝ × ℝ × ℝ × ℝ) : ℝ :=
  Afun H d p.1 p.2.2.1 * (Shat p.1 p.2.1 p.2.2.1 p.2.2.2 - S0 p.1)
    - Nfun p.1 p.2.2.1 * (That H p.1 p.2.1 p.2.2.1 p.2.2.2 - p.1 ^ H.edgeFinset.card)

theorem analyticAt_entQuot (d : ℕ) {p : ℝ × ℝ × ℝ × ℝ} (hc : p.2.2.2 ≠ 1)
    (hε0 : 0 < p.1) (hε1 : p.1 < 1) (ha0 : 0 < p.2.1) (ha1 : p.2.1 < 1)
    (hb0 : 0 < p.2.2.1) (hb1 : p.2.2.1 < 1)
    (hQ0 : 0 < Qmap p.1 p.2.1 p.2.2.1 p.2.2.2) (hQ1 : Qmap p.1 p.2.1 p.2.2.1 p.2.2.2 < 1) :
    AnalyticAt ℝ (entQuot H d) p := by
  have hfst := analyticAt_fst4 p
  have hthd := analyticAt_thd4 p
  have hA : AnalyticAt ℝ (fun w : ℝ × ℝ × ℝ × ℝ => Afun H d w.1 w.2.2.1) p := by
    unfold Afun Dfun
    exact (analyticAt_const.mul (hfst.pow _)).mul (((hthd.pow d).sub (hfst.pow d)).sub
      ((analyticAt_const.mul (hfst.pow _)).mul (hthd.sub hfst)))
  have hS0ε : AnalyticAt ℝ (fun w : ℝ × ℝ × ℝ × ℝ => S0 w.1) p :=
    (analyticAt_S0 hε0 hε1).comp_of_eq hfst rfl
  have hN : AnalyticAt ℝ (fun w : ℝ × ℝ × ℝ × ℝ => Nfun w.1 w.2.2.1) p := by
    unfold Nfun
    exact analyticAt_const.mul ((((analyticAt_S0 hb0 hb1).comp_of_eq hthd rfl).sub hS0ε).sub
      (((analyticAt_dS0 hε0 hε1).comp_of_eq hfst rfl).mul (hthd.sub hfst)))
  exact (hA.mul ((analyticAt_Shat hc ha0 ha1 hb0 hb1 hQ0 hQ1).sub hS0ε)).sub
    (hN.mul ((analyticAt_That H hc).sub (hfst.pow _)))

theorem entQuot_zero (d : ℕ) (ε a b : ℝ) : entQuot H d (ε, a, b, 0) = 0 := by
  unfold entQuot
  simp only [That_zero, sub_self, mul_zero]
  have : Shat ε a b 0 = S0 ε := by unfold Shat; simp [Qmap_zero]
  rw [this, sub_self, mul_zero, sub_zero]

theorem partialC_entQuot_zero {d : ℕ} (hd : 2 ≤ d) (hreg : ∀ v, H.degree v = d)
    (hm : 2 ≤ H.edgeFinset.card) {ε a b : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (ha0 : 0 < a) (ha1 : a < 1) (hb0 : 0 < b) (hb1 : b < 1) :
    partialC (entQuot H d) (ε, a, b, 0) = 0 := by
  have hQ : Qmap ε a b 0 = ε := Qmap_zero ε a b
  have hQ0 : 0 < Qmap ε a b 0 := by rw [hQ]; exact hε0
  have hQ1 : Qmap ε a b 0 < 1 := by rw [hQ]; exact hε1
  have hana : AnalyticAt ℝ (entQuot H d) (ε, a, b, 0) :=
    analyticAt_entQuot H d (p := (ε, a, b, 0)) (by norm_num) hε0 hε1 ha0 ha1 hb0 hb1 hQ0 hQ1
  have h1 : HasDerivAt (fun c => entQuot H d (ε, a, b, c))
      (partialC (entQuot H d) (ε, a, b, 0)) 0 :=
    hasDerivAt_partialSlot hana ((hasDerivAt_const 0 ε).prodMk ((hasDerivAt_const 0 a).prodMk
      ((hasDerivAt_const 0 b).prodMk (hasDerivAt_id 0)))) rfl
  have h2 : HasDerivAt (fun c => entQuot H d (ε, a, b, c))
      (Afun H d ε b * Nfun ε b - Nfun ε b * Afun H d ε b) 0 := by
    have hS := ((hasDerivAt_Shat_c_zero hε0 hε1 a b).sub_const (S0 ε)).const_mul (Afun H d ε b)
    have hT := ((hasDerivAt_That_c_zero H hd hreg hm ε a b).sub_const
      (ε ^ H.edgeFinset.card)).const_mul (Nfun ε b)
    exact hS.sub hT
  rw [h1.unique h2]
  ring

/-! ### The Hölder profile `h_ε(ϑ) = (ε^m + ϑ)^{d/m} - ε^d` -/

/-- Second-order lower bound for a concave power: for `0 < x`, `0 ≤ α ≤ 1` and `0 ≤ t`,
`(x + t)^α ≥ x^α + α x^{α-1} t - (α(1-α)/2) x^{α-2} t²`. -/
theorem rpow_add_ge_taylor {x α t : ℝ} (hx : 0 < x) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (ht : 0 ≤ t) :
    x ^ α + α * x ^ (α - 1) * t - α * (1 - α) / 2 * x ^ (α - 2) * t ^ 2 ≤ (x + t) ^ α := by
  set F : ℝ → ℝ := fun s => (x + s) ^ α - x ^ α - α * x ^ (α - 1) * s with hF
  set F' : ℝ → ℝ := fun s => α * (x + s) ^ (α - 1) - α * x ^ (α - 1) with hF'
  set F'' : ℝ → ℝ := fun s => α * (α - 1) * (x + s) ^ (α - 2) with hF''
  have hpos : ∀ s ∈ Icc (0:ℝ) t, 0 < x + s := fun s hs => by linarith [hs.1]
  have hd1 : ∀ s ∈ Icc (0:ℝ) t, HasDerivAt F (F' s) s := by
    intro s hs
    have h1 : HasDerivAt (fun y => (x + y) ^ α) (1 * α * (x + s) ^ (α - 1)) s :=
      ((hasDerivAt_id s).const_add x).rpow_const (Or.inl (ne_of_gt (hpos s hs)))
    have h2 : HasDerivAt (fun y => α * x ^ (α - 1) * y) (α * x ^ (α - 1)) s := by
      simpa using (hasDerivAt_id s).const_mul (α * x ^ (α - 1))
    have h3 := (h1.sub_const (x ^ α)).sub h2
    have e : 1 * α * (x + s) ^ (α - 1) - α * x ^ (α - 1) = F' s := by simp only [hF']; ring
    rw [e] at h3
    exact h3
  have hd2 : ∀ s ∈ Icc (0:ℝ) t, HasDerivAt F' (F'' s) s := by
    intro s hs
    have h1 : HasDerivAt (fun y => (x + y) ^ (α - 1)) (1 * (α - 1) * (x + s) ^ (α - 1 - 1)) s :=
      ((hasDerivAt_id s).const_add x).rpow_const (Or.inl (ne_of_gt (hpos s hs)))
    have h3 := (h1.const_mul α).sub_const (α * x ^ (α - 1))
    have e : α * (1 * (α - 1) * (x + s) ^ (α - 1 - 1)) = F'' s := by
      simp only [hF'']; rw [show α - 1 - 1 = α - 2 by ring]; ring
    rw [e] at h3
    exact h3
  have hlow : ∀ s ∈ Icc (0:ℝ) t, -(α * (1 - α)) * x ^ (α - 2) ≤ F'' s := by
    intro s hs
    have hle : (x + s) ^ (α - 2) ≤ x ^ (α - 2) :=
      Real.rpow_le_rpow_of_nonpos hx (by linarith [hs.1]) (by linarith)
    have hc : 0 ≤ α * (1 - α) := mul_nonneg hα0 (by linarith)
    simp only [hF'']
    nlinarith [hle, hc]
  have hq := quadratic_lower_of_deriv2_ge (f := F) (f' := F') (f'' := F'') (c := 0)
    (a := 0) (b := t) le_rfl ht hd1 hd2 hlow (by simp [hF]) (by simp [hF']) t ⟨ht, le_rfl⟩
  simp only [hF, sub_zero] at hq
  nlinarith [hq]

/-! ### Along the family -/

namespace KRRSFamily

variable {H} {d : ℕ} {ε₀ : ℝ}

theorem graphon_entropy (F : KRRSFamily H d ε₀) {ε ϑ : ℝ} (hε : ε ∈ F.U) (hϑ0 : 0 < ϑ)
    (hϑΔ : ϑ < F.Δ) :
    (F.graphon ε ϑ).entropy = Shat ε (F.q11 ε ϑ) (F.q12 ε ϑ) (F.c ε ϑ) := by
  obtain ⟨h11, h12, h22, hc, hval, -, -⟩ := F.graphon_spec hε hϑ0 hϑΔ
  have hae : ∀ᵐ z ∂gμ, (F.graphon ε ϑ).toFun z.1 z.2
      = bipodalValue (Set.Icc 0
          ((F.q11 ε ϑ, F.q12 ε ϑ, Qmap ε (F.q11 ε ϑ) (F.q12 ε ϑ) (F.c ε ϑ), F.c ε ϑ) : Theta).2.2.2)
          ((F.q11 ε ϑ, F.q12 ε ϑ, Qmap ε (F.q11 ε ϑ) (F.q12 ε ϑ) (F.c ε ϑ), F.c ε ϑ) : Theta).1
          ((F.q11 ε ϑ, F.q12 ε ϑ, Qmap ε (F.q11 ε ϑ) (F.q12 ε ϑ) (F.c ε ϑ), F.c ε ϑ) : Theta).2.1
          ((F.q11 ε ϑ, F.q12 ε ϑ, Qmap ε (F.q11 ε ϑ) (F.q12 ε ϑ) (F.c ε ϑ), F.c ε ϑ) : Theta).2.2.1
          (id z.1, id z.2) :=
    Filter.Eventually.of_forall (fun z => by simpa using hval z)
  have htr := bipodal_transfer H
    (θ := ((F.q11 ε ϑ, F.q12 ε ϑ, Qmap ε (F.q11 ε ϑ) (F.q12 ε ϑ) (F.c ε ϑ), F.c ε ϑ) : Theta))
    ⟨h11.1.le, h11.2.le⟩ ⟨h12.1.le, h12.2.le⟩ ⟨h22.1.le, h22.2.le⟩ ⟨hc.1.le, hc.2.le⟩
    isRelabelling_id hae
  rw [htr.2.2, Shat_eq_bipEnt]

/-- An open window `|ε - ε₀| < w`, `|ϑ| ≤ ρ` inside the analytic strip of the family. -/
theorem exists_box (F : KRRSFamily H d ε₀) :
    ∃ w ρ : ℝ, 0 < w ∧ 0 < ρ ∧ ∀ ε ϑ : ℝ, |ε - ε₀| < w → |ϑ| ≤ ρ → ε ∈ F.U ∧ |ϑ| < F.Δ := by
  obtain ⟨w, hw, hball⟩ := Metric.isOpen_iff.mp F.isOpen_U ε₀ F.mem_U
  refine ⟨w, F.Δ / 2, hw, by linarith [F.Δ_pos], fun ε ϑ hε hϑ => ⟨hball ?_, by
    linarith [F.Δ_pos]⟩⟩
  rw [Metric.mem_ball, Real.dist_eq]; exact hε

/-- `c = O(ϑ)` along the family, uniformly near `ε₀`. -/
theorem exists_c_le (F : KRRSFamily H d ε₀) :
    ∃ w ρ L : ℝ, 0 < w ∧ 0 < ρ ∧ 0 ≤ L ∧
      ∀ ε ϑ : ℝ, |ε - ε₀| ≤ w → |ϑ| ≤ ρ → ε ∈ F.U ∧ |ϑ| < F.Δ ∧ |F.c ε ϑ| ≤ L * |ϑ| := by
  obtain ⟨w, ρ, hw, hρ, hbox⟩ := F.exists_box
  obtain ⟨L, hL0, hL⟩ := exists_lipschitz_bound_of_boundary_zero (F := fun p : ℝ × ℝ => F.c p.1 p.2)
    hw hρ (fun r δ hr hδ => (F.analytic r (hbox r δ hr hδ).1 δ (hbox r δ hr hδ).2).2.2.2)
    (fun r hr => (F.boundary r (hbox r 0 hr (by simp [hρ.le])).1).1)
  refine ⟨w / 2, ρ / 2, L, by linarith, by linarith, hL0, fun ε ϑ hε hϑ => ?_⟩
  obtain ⟨h1, h2⟩ := hbox ε ϑ (by linarith) (by linarith)
  exact ⟨h1, h2, hL ε ϑ hε hϑ⟩

/-- `q₁₂ - ζ_d(ε) = O(ϑ)` along the family, uniformly near `ε₀`. -/
theorem exists_q12_sub_le (F : KRRSFamily H d ε₀) :
    ∃ w ρ L : ℝ, 0 < w ∧ 0 < ρ ∧ 0 ≤ L ∧
      ∀ ε ϑ : ℝ, |ε - ε₀| ≤ w → |ϑ| ≤ ρ →
        |F.q12 ε ϑ - zetaFun d ε| ≤ L * |ϑ| := by
  obtain ⟨w, ρ, hw, hρ, hbox⟩ := F.exists_box
  have hana : ∀ r δ : ℝ, |r - ε₀| < w → |δ| ≤ ρ →
      AnalyticAt ℝ (fun p : ℝ × ℝ => F.q12 p.1 p.2 - F.q12 p.1 0) (r, δ) := by
    intro r δ hr hδ
    obtain ⟨hU, hΔ⟩ := hbox r δ hr hδ
    have h1 := (F.analytic r hU δ hΔ).2.1
    have h0 : AnalyticAt ℝ (fun p : ℝ × ℝ => F.q12 p.1 p.2) (r, 0) :=
      (F.analytic r hU 0 (by simpa using F.Δ_pos)).2.1
    have h2 : AnalyticAt ℝ (fun p : ℝ × ℝ => F.q12 p.1 0) (r, δ) :=
      h0.comp_of_eq (analyticAt_fst.prod analyticAt_const) rfl
    exact h1.sub h2
  obtain ⟨L, hL0, hL⟩ := exists_lipschitz_bound_of_boundary_zero hw hρ hana
    (fun r _ => by simp)
  refine ⟨w / 2, ρ / 2, L, by linarith, by linarith, hL0, fun ε ϑ hε hϑ => ?_⟩
  have h := hL ε ϑ hε hϑ
  obtain ⟨hU, -⟩ := hbox ε ϑ (by linarith) (by linarith)
  simpa [(F.boundary ε hU).2.2] using h

end KRRSFamily

/-! ### The Hölder profile, and `ψ_d` near `ζ_d(ε₀)` -/

theorem holder_profile_ge {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] {d : ℕ} (hd : 2 ≤ d) (hreg : ∀ v, H.degree v = d)
    (hm : 1 ≤ H.edgeFinset.card) {ε₁ : ℝ} (hε₁ : 0 < ε₁) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ ε ϑ : ℝ, ε₁ ≤ ε → 0 ≤ ϑ →
      2 * ϑ / ((Fintype.card V : ℝ) * ε ^ (H.edgeFinset.card - d)) - K * ϑ ^ 2
        ≤ Real.rpow (ε ^ H.edgeFinset.card + ϑ) ((d : ℝ) / (H.edgeFinset.card : ℝ)) - ε ^ d := by
  set m := H.edgeFinset.card with hmdef
  have hdm : d ≤ m := degree_le_card_edges H hreg (by omega)
  have hmR : (0:ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hdR : (0:ℝ) < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
  set α : ℝ := (d : ℝ) / (m : ℝ) with hα
  have hα0 : 0 ≤ α := div_nonneg hdR.le hmR.le
  have hα1 : α ≤ 1 := by rw [hα, div_le_one hmR]; exact_mod_cast hdm
  have hnd : (Fintype.card V : ℝ) * (d : ℝ) = 2 * (m : ℝ) := by
    exact_mod_cast regular_handshake H hreg
  have hV : (0:ℝ) < (Fintype.card V : ℝ) := by
    have : Nonempty V := nonempty_of_edge H hm
    exact_mod_cast Fintype.card_pos
  refine ⟨α * (1 - α) / 2 * (ε₁ ^ m) ^ (α - 2), by
    have := Real.rpow_nonneg (pow_nonneg hε₁.le m) (α - 2)
    have hc : 0 ≤ α * (1 - α) := mul_nonneg hα0 (by linarith)
    positivity, fun ε ϑ hε hϑ => ?_⟩
  have hε0 : 0 < ε := lt_of_lt_of_le hε₁ hε
  have hx : 0 < ε ^ m := pow_pos hε0 m
  have htay := rpow_add_ge_taylor hx hα0 hα1 hϑ
  -- the three coefficients
  have hxα : (ε ^ m) ^ α = ε ^ d := by
    rw [← Real.rpow_natCast ε m, ← Real.rpow_mul hε0.le, hα,
      mul_div_cancel₀ _ (ne_of_gt hmR), Real.rpow_natCast]
  have hcoef : α * (ε ^ m) ^ (α - 1)
      = 2 / ((Fintype.card V : ℝ) * ε ^ (m - d)) := by
    have hpow : ε ^ (m - d) * ε ^ d = ε ^ m := by rw [← pow_add, Nat.sub_add_cancel hdm]
    rw [← Real.rpow_natCast ε m, ← Real.rpow_mul hε0.le,
      show (m : ℝ) * (α - 1) = (d : ℝ) - (m : ℝ) by rw [hα]; field_simp,
      Real.rpow_sub hε0, Real.rpow_natCast, Real.rpow_natCast, hα]
    have hεm : ε ^ (m - d) ≠ 0 := pow_ne_zero _ (ne_of_gt hε0)
    rw [← hpow]
    field_simp
    nlinarith [hnd]
  have hK : (ε ^ m) ^ (α - 2) ≤ (ε₁ ^ m) ^ (α - 2) :=
    Real.rpow_le_rpow_of_nonpos (pow_pos hε₁ m) (pow_le_pow_left₀ hε₁.le hε m) (by linarith)
  have hc : 0 ≤ α * (1 - α) / 2 := by
    have := mul_nonneg hα0 (show 0 ≤ 1 - α by linarith); linarith
  rw [hxα, hcoef] at htay
  show 2 * ϑ / ((Fintype.card V : ℝ) * ε ^ (m - d)) - α * (1 - α) / 2 * (ε₁ ^ m) ^ (α - 2) * ϑ ^ 2
    ≤ (ε ^ m + ϑ) ^ α - ε ^ d
  have hsq : α * (1 - α) / 2 * (ε ^ m) ^ (α - 2) * ϑ ^ 2
      ≤ α * (1 - α) / 2 * (ε₁ ^ m) ^ (α - 2) * ϑ ^ 2 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hK hc) (sq_nonneg _)
  have hdiv : 2 * ϑ / ((Fintype.card V : ℝ) * ε ^ (m - d))
      = 2 / ((Fintype.card V : ℝ) * ε ^ (m - d)) * ϑ := by ring
  rw [hdiv]
  linarith

theorem analyticAt_psiD_prod {d : ℕ} (hd : 2 ≤ d) {ε b : ℝ} (hε : ε ∈ Ioo (0:ℝ) 1)
    (hb : b ∈ Ioo (0:ℝ) 1) (hne : b ≠ ε) :
    AnalyticAt ℝ (fun p : ℝ × ℝ => psiD d p.1 p.2) (ε, b) := by
  have hfst : AnalyticAt ℝ (fun p : ℝ × ℝ => p.1) (ε, b) := analyticAt_fst
  have hsnd : AnalyticAt ℝ (fun p : ℝ × ℝ => p.2) (ε, b) := analyticAt_snd
  have hN : AnalyticAt ℝ (fun p : ℝ × ℝ => Nfun p.1 p.2) (ε, b) := by
    unfold Nfun
    exact analyticAt_const.mul ((((analyticAt_S0 hb.1 hb.2).comp_of_eq hsnd rfl).sub
      ((analyticAt_S0 hε.1 hε.2).comp_of_eq hfst rfl)).sub
      (((analyticAt_dS0 hε.1 hε.2).comp_of_eq hfst rfl).mul (hsnd.sub hfst)))
  have hD : AnalyticAt ℝ (fun p : ℝ × ℝ => Dfun d p.1 p.2) (ε, b) := by
    unfold Dfun
    exact ((hsnd.pow d).sub (hfst.pow d)).sub
      ((analyticAt_const.mul (hfst.pow _)).mul (hsnd.sub hfst))
  exact hN.div hD (ne_of_gt (Dfun_pos hd hε.1 hb.1.le hne))

theorem exists_psiD_lipschitz {d : ℕ} (hd : 2 ≤ d) {ε₀ b₀ : ℝ} (hε₀ : ε₀ ∈ Ioo (0:ℝ) 1)
    (hb₀ : b₀ ∈ Ioo (0:ℝ) 1) (hne : b₀ ≠ ε₀) :
    ∃ r L : ℝ, 0 < r ∧ 0 ≤ L ∧ ∀ ε b b' : ℝ, |ε - ε₀| ≤ r → |b - b₀| ≤ r → |b' - b₀| ≤ r →
      |psiD d ε b - psiD d ε b'| ≤ L * |b - b'| := by
  set r : ℝ := min (min ε₀ (1 - ε₀)) (min (min b₀ (1 - b₀)) |b₀ - ε₀|) / 4 with hr
  have hsep : 0 < |b₀ - ε₀| := abs_pos.mpr (sub_ne_zero.mpr hne)
  have hr0 : 0 < r := by
    have h1' : (0:ℝ) < 1 - ε₀ := by linarith [hε₀.2]
    have h2' : (0:ℝ) < 1 - b₀ := by linarith [hb₀.2]
    have := lt_min (lt_min hε₀.1 h1') (lt_min (lt_min hb₀.1 h2') hsep)
    rw [hr]; linarith
  have h1 : r ≤ ε₀ / 4 := by
    rw [hr]; have := min_le_left (min ε₀ (1 - ε₀)) (min (min b₀ (1 - b₀)) |b₀ - ε₀|)
    have := min_le_left ε₀ (1 - ε₀); linarith
  have h2 : r ≤ (1 - ε₀) / 4 := by
    rw [hr]; have := min_le_left (min ε₀ (1 - ε₀)) (min (min b₀ (1 - b₀)) |b₀ - ε₀|)
    have := min_le_right ε₀ (1 - ε₀); linarith
  have h3 : r ≤ b₀ / 4 := by
    rw [hr]; have := min_le_right (min ε₀ (1 - ε₀)) (min (min b₀ (1 - b₀)) |b₀ - ε₀|)
    have := min_le_left (min b₀ (1 - b₀)) |b₀ - ε₀|; have := min_le_left b₀ (1 - b₀); linarith
  have h4 : r ≤ (1 - b₀) / 4 := by
    rw [hr]; have := min_le_right (min ε₀ (1 - ε₀)) (min (min b₀ (1 - b₀)) |b₀ - ε₀|)
    have := min_le_left (min b₀ (1 - b₀)) |b₀ - ε₀|; have := min_le_right b₀ (1 - b₀); linarith
  have h5 : r ≤ |b₀ - ε₀| / 4 := by
    rw [hr]; have := min_le_right (min ε₀ (1 - ε₀)) (min (min b₀ (1 - b₀)) |b₀ - ε₀|)
    have := min_le_right (min b₀ (1 - b₀)) |b₀ - ε₀|; linarith
  obtain ⟨L, hL0, hL⟩ := exists_lipschitz_snd (Ψ := fun p : ℝ × ℝ => psiD d p.1 p.2)
    (x₀ := ε₀) (y₀ := b₀) (w := r) (ρ := r) (fun x y hx hy => by
      have hx' := abs_le.mp hx
      have hy' := abs_le.mp hy
      refine analyticAt_psiD_prod hd ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ ?_
      intro heq
      have : |b₀ - ε₀| ≤ 2 * r := by
        rw [abs_le]; constructor <;> linarith
      linarith)
  exact ⟨r, L, hr0, hL0, fun ε b b' hε hb hb' => hL ε b b' hε hb hb'⟩

/-! ### The entropy of the family to second order -/

private theorem ball_of_continuousAt₄ {f : ℝ × ℝ × ℝ × ℝ → ℝ} {p₀ : ℝ × ℝ × ℝ × ℝ}
    (hf : ContinuousAt f p₀) {U : Set ℝ} (hU : IsOpen U) (hmem : f p₀ ∈ U) :
    ∃ r : ℝ, 0 < r ∧ ∀ p, dist p p₀ < r → f p ∈ U := by
  obtain ⟨r, hr, h⟩ := Metric.eventually_nhds_iff.mp (hf.eventually (hU.mem_nhds hmem))
  exact ⟨r, hr, h⟩

theorem entQuot_bound_box {d : ℕ} (hd : 2 ≤ d) (hreg : ∀ v, H.degree v = d)
    (hm : 2 ≤ H.edgeFinset.card) {ε₀ a₀ b₀ : ℝ} (hε₀ : ε₀ ∈ Ioo (0:ℝ) 1)
    (ha₀ : a₀ ∈ Ioo (0:ℝ) 1) (hb₀ : b₀ ∈ Ioo (0:ℝ) 1) :
    ∃ r L : ℝ, 0 < r ∧ 0 ≤ L ∧ ∀ ε a b c : ℝ, |ε - ε₀| ≤ r → |a - a₀| ≤ r → |b - b₀| ≤ r →
      |c| ≤ r → |entQuot H d (ε, a, b, c)| ≤ L * c ^ 2 := by
  have hQc : ContinuousAt (fun w : ℝ × ℝ × ℝ × ℝ => Qmap w.1 w.2.1 w.2.2.1 w.2.2.2)
      (ε₀, a₀, b₀, 0) := (analyticAt_Qmap (p := (ε₀, a₀, b₀, 0)) (by norm_num)).continuousAt
  obtain ⟨rQ, hrQ, hQball⟩ := ball_of_continuousAt₄ hQc isOpen_Ioo
    (show Qmap ε₀ a₀ b₀ 0 ∈ Ioo (0:ℝ) 1 by rw [Qmap_zero]; exact hε₀)
  set r : ℝ := min (min (min ε₀ (1 - ε₀)) (min a₀ (1 - a₀))) (min (min b₀ (1 - b₀)) rQ) / 2
    with hr
  have hr0 : 0 < r := by
    have e1 : (0:ℝ) < 1 - ε₀ := by linarith [hε₀.2]
    have e2 : (0:ℝ) < 1 - a₀ := by linarith [ha₀.2]
    have e3 : (0:ℝ) < 1 - b₀ := by linarith [hb₀.2]
    have := lt_min (lt_min (lt_min hε₀.1 e1) (lt_min ha₀.1 e2)) (lt_min (lt_min hb₀.1 e3) hrQ)
    rw [hr]; linarith
  have hm1 : 2 * r ≤ min (min ε₀ (1 - ε₀)) (min a₀ (1 - a₀)) := by
    rw [hr]; have := min_le_left (min (min ε₀ (1 - ε₀)) (min a₀ (1 - a₀)))
      (min (min b₀ (1 - b₀)) rQ); linarith
  have hm2 : 2 * r ≤ min (min b₀ (1 - b₀)) rQ := by
    rw [hr]; have := min_le_right (min (min ε₀ (1 - ε₀)) (min a₀ (1 - a₀)))
      (min (min b₀ (1 - b₀)) rQ); linarith
  have hε₀r : 2 * r ≤ ε₀ :=
    le_trans hm1 (le_trans (min_le_left _ _) (min_le_left _ _))
  have hε₀r' : 2 * r ≤ 1 - ε₀ :=
    le_trans hm1 (le_trans (min_le_left _ _) (min_le_right _ _))
  have ha₀r : 2 * r ≤ a₀ :=
    le_trans hm1 (le_trans (min_le_right _ _) (min_le_left _ _))
  have ha₀r' : 2 * r ≤ 1 - a₀ :=
    le_trans hm1 (le_trans (min_le_right _ _) (min_le_right _ _))
  have hb₀r : 2 * r ≤ b₀ :=
    le_trans hm2 (le_trans (min_le_left _ _) (min_le_left _ _))
  have hb₀r' : 2 * r ≤ 1 - b₀ :=
    le_trans hm2 (le_trans (min_le_left _ _) (min_le_right _ _))
  have hrQr : 2 * r ≤ rQ := le_trans hm2 (min_le_right _ _)
  set K₃ : Set (ℝ × ℝ × ℝ) := Icc (ε₀ - r) (ε₀ + r) ×ˢ Icc (a₀ - r) (a₀ + r) ×ˢ
    Icc (b₀ - r) (b₀ + r) with hK₃
  have hK₃c : IsCompact K₃ := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hana : ∀ x ∈ K₃, ∀ c ∈ Icc (-r) r, AnalyticAt ℝ (entQuot H d) (x.1, x.2.1, x.2.2, c) := by
    intro x hx c hc
    obtain ⟨hx1, hx2, hx3⟩ := hx
    have hdist : dist ((x.1, x.2.1, x.2.2, c) : ℝ × ℝ × ℝ × ℝ) (ε₀, a₀, b₀, 0) < rQ := by
      simp only [Prod.dist_eq, Real.dist_eq, sub_zero]
      refine max_lt ?_ (max_lt ?_ (max_lt ?_ ?_)) <;> rw [abs_lt] <;> constructor <;>
        linarith [hx1.1, hx1.2, hx2.1, hx2.2, hx3.1, hx3.2, hc.1, hc.2]
    have hQ := hQball _ hdist
    exact analyticAt_entQuot H d (by show c ≠ 1; intro h; rw [h] at hc; linarith [hc.2])
      (by show 0 < x.1; linarith [hx1.1]) (by show x.1 < 1; linarith [hx1.2])
      (by show 0 < x.2.1; linarith [hx2.1]) (by show x.2.1 < 1; linarith [hx2.2])
      (by show 0 < x.2.2; linarith [hx3.1]) (by show x.2.2 < 1; linarith [hx3.2]) hQ.1 hQ.2
  obtain ⟨L, hL0, hL⟩ := exists_sq_bound_slice_zero hK₃c hana
    (fun x _ => entQuot_zero H d x.1 x.2.1 x.2.2)
    (fun x hx => by
      obtain ⟨hx1, hx2, hx3⟩ := hx
      exact partialC_entQuot_zero H hd hreg hm (by linarith [hx1.1]) (by linarith [hx1.2])
        (by linarith [hx2.1]) (by linarith [hx2.2]) (by linarith [hx3.1]) (by linarith [hx3.2]))
  refine ⟨r, L, hr0, hL0, fun ε a b c hε ha hb hc => ?_⟩
  have hx : ((ε, a, b) : ℝ × ℝ × ℝ) ∈ K₃ :=
    ⟨⟨by linarith [(abs_le.mp hε).1], by linarith [(abs_le.mp hε).2]⟩,
      ⟨by linarith [(abs_le.mp ha).1], by linarith [(abs_le.mp ha).2]⟩,
      ⟨by linarith [(abs_le.mp hb).1], by linarith [(abs_le.mp hb).2]⟩⟩
  exact hL _ hx c ⟨(abs_le.mp hc).1, (abs_le.mp hc).2⟩

/-- **`kb:eq:family-entropy`.**  Along the family,
`2(S₀(ε) - s(Ŵ_{ε,ϑ})) ≤ |ψ_*|·h_ε(ϑ) + Kϑ²`, uniformly near `ε₀`. -/
theorem KRRSFamily.exists_entropy_gap_le {d : ℕ} {ε₀ : ℝ} (F : KRRSFamily H d ε₀)
    (hd : 2 ≤ d) (hreg : ∀ v, H.degree v = d) (hm : 2 ≤ H.edgeFinset.card)
    (hε₀ : ε₀ ∈ Ioo (0:ℝ) 1) (hε₀r : ε₀ ≠ rStar d) :
    ∃ η Δ₁ K : ℝ, 0 < η ∧ 0 < Δ₁ ∧ 0 ≤ K ∧ ∀ ε ϑ : ℝ, |ε - ε₀| < η → 0 < ϑ → ϑ < Δ₁ →
      ε ∈ F.U ∧ ϑ < F.Δ ∧
      2 * (S0 ε - (F.graphon ε ϑ).entropy)
        ≤ -psiStar d ε * (Real.rpow (ε ^ H.edgeFinset.card + ϑ)
            ((d : ℝ) / (H.edgeFinset.card : ℝ)) - ε ^ d) + K * ϑ ^ 2 := by
  classical
  set m := H.edgeFinset.card with hmdef
  obtain ⟨hζ₀m, hζ₀ne, -⟩ := zetaFun_crit hd hε₀.1 hε₀.2 hε₀r
  obtain ⟨hc00, ha00, hb00⟩ := F.boundary ε₀ F.mem_U
  set a₀ := F.q11 ε₀ 0 with ha₀
  set b₀ := F.q12 ε₀ 0 with hb₀
  have ha₀I : a₀ ∈ Ioo (0:ℝ) 1 := by rw [ha00]; exact baseA_mem H d _ _
  have hb₀I : b₀ ∈ Ioo (0:ℝ) 1 := by rw [hb00]; exact hζ₀m
  -- the ingredients
  obtain ⟨rE, LE, hrE, hLE0, hE⟩ := entQuot_bound_box H hd hreg hm hε₀ ha₀I hb₀I
  obtain ⟨w₁, ρ₁, L₁, hw₁, hρ₁, hL₁0, hc⟩ := F.exists_c_le
  obtain ⟨w₂, ρ₂, L₂, hw₂, hρ₂, hL₂0, hq⟩ := F.exists_q12_sub_le
  obtain ⟨r₃, L₃, hr₃, hL₃0, hψ⟩ := exists_psiD_lipschitz hd hε₀ hζ₀m hζ₀ne
  obtain ⟨K₄, hK₄0, hK₄⟩ := holder_profile_ge H hd hreg (by omega) (ε₁ := ε₀ / 2) (by linarith [hε₀.1])
  -- continuity: the family near `(ε₀, 0)`
  have hfam : ContinuousAt (fun p : ℝ × ℝ => ((p.1, F.q11 p.1 p.2, F.q12 p.1 p.2, F.c p.1 p.2) :
      ℝ × ℝ × ℝ × ℝ)) (ε₀, 0) := by
    obtain ⟨h1, h2, -, h4⟩ := F.analytic ε₀ F.mem_U 0 (by simpa using F.Δ_pos)
    exact continuous_fst.continuousAt.prodMk (h1.continuousAt.prodMk
      (h2.continuousAt.prodMk h4.continuousAt))
  have hAc : ContinuousAt (fun p : ℝ × ℝ => Afun H d p.1 p.2) (ε₀, b₀) := by
    unfold Afun Dfun; fun_prop
  have hA0 : 0 < Afun H d ε₀ b₀ :=
    Afun_pos H hd (by omega) hε₀.1 hb₀I.1.le (by rw [hb00]; exact hζ₀ne)
  obtain ⟨r₈, hr₈, hAball⟩ := Metric.eventually_nhds_iff.mp
    (hAc.eventually (lt_mem_nhds (show Afun H d ε₀ b₀ / 2 < Afun H d ε₀ b₀ by linarith)))
  set rmin : ℝ := min rE (min r₃ r₈) with hrmin
  have hrmin0 : 0 < rmin := lt_min hrE (lt_min hr₃ hr₈)
  obtain ⟨r₅, hr₅, hfamball⟩ := Metric.eventually_nhds_iff.mp
    (hfam.eventually (Metric.ball_mem_nhds _ hrmin0))
  -- `ζ_d` near `ε₀`
  obtain ⟨r₆, hr₆, hζball⟩ := Metric.eventually_nhds_iff.mp
    ((continuousAt_zetaFun hd hε₀).eventually (Metric.ball_mem_nhds _ hr₃))
  -- bounds on `ψ_*` and on `𝒜`
  obtain ⟨r₇, hr₇, hψball⟩ := Metric.eventually_nhds_iff.mp
    ((continuousAt_psiStar hd hε₀ hε₀r).eventually (Metric.ball_mem_nhds _ one_pos))
  set B₁ : ℝ := |psiStar d ε₀| + 1 with hB₁
  have hV : (0:ℝ) < (Fintype.card V : ℝ) := by
    have : Nonempty V := nonempty_of_edge H (by omega)
    exact_mod_cast Fintype.card_pos
  set B₂ : ℝ := 1 / ((Fintype.card V : ℝ) * (ε₀ / 2) ^ (m - d)) with hB₂
  set A₁ : ℝ := Afun H d ε₀ b₀ / 2 with hA₁
  set K : ℝ := B₁ * K₄ + 2 * L₃ * L₂ * B₂ + 2 * LE * L₁ ^ 2 / A₁ with hK
  set η : ℝ := min (min (min w₁ w₂) (min r₆ r₇)) (min (min r₅ r₈) (ε₀ / 2)) with hη
  set Δ₁ : ℝ := min (min ρ₁ ρ₂) (min r₅ (min r₈ 1)) with hΔ₁
  have hη0 : 0 < η := lt_min (lt_min (lt_min hw₁ hw₂) (lt_min hr₆ hr₇))
    (lt_min (lt_min hr₅ hr₈) (by linarith [hε₀.1]))
  have hΔ₁0 : 0 < Δ₁ := lt_min (lt_min hρ₁ hρ₂) (lt_min hr₅ (lt_min hr₈ one_pos))
  have hK0 : 0 ≤ K := by
    have hB₁0 : 0 ≤ B₁ := by rw [hB₁]; positivity
    have hB₂0 : 0 ≤ B₂ := by
      rw [hB₂]; have : (0:ℝ) < ε₀ / 2 := by linarith [hε₀.1]
      positivity
    have hA₁0 : 0 < A₁ := by rw [hA₁]; linarith
    rw [hK]
    exact add_nonneg (add_nonneg (mul_nonneg hB₁0 hK₄0)
      (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hL₃0) hL₂0) hB₂0))
      (div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hLE0) (sq_nonneg _)) hA₁0.le)
  refine ⟨η, Δ₁, K, hη0, hΔ₁0, hK0, fun ε ϑ hε hϑ0 hϑΔ => ?_⟩
  -- unpack the smallness of `ε - ε₀` and `ϑ`
  have hη1 : η ≤ min w₁ w₂ := le_trans (min_le_left _ _) (min_le_left _ _)
  have hη2 : η ≤ min r₆ r₇ := le_trans (min_le_left _ _) (min_le_right _ _)
  have hη3 : η ≤ min r₅ r₈ := le_trans (min_le_right _ _) (min_le_left _ _)
  have hη4 : η ≤ ε₀ / 2 := le_trans (min_le_right _ _) (min_le_right _ _)
  have hΔa : Δ₁ ≤ min ρ₁ ρ₂ := min_le_left _ _
  have hΔb : Δ₁ ≤ r₅ := le_trans (min_le_right _ _) (min_le_left _ _)
  have hΔc : Δ₁ ≤ 1 := le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  have hεabs := abs_lt.mp hε
  have hϑabs : |ϑ| = ϑ := abs_of_pos hϑ0
  obtain ⟨hεU, hϑF, hcle⟩ := hc ε ϑ (by linarith [min_le_left w₁ w₂])
    (by rw [hϑabs]; linarith [min_le_left ρ₁ ρ₂])
  have hqle := hq ε ϑ (by linarith [min_le_right w₁ w₂]) (by rw [hϑabs]; linarith [min_le_right ρ₁ ρ₂])
  have hϑF' : ϑ < F.Δ := by rw [← hϑabs]; exact hϑF
  obtain ⟨hεI, hεr, h11, h12, -, -, h12ne⟩ := F.interior ε hεU ϑ hϑF
  -- the family point is close to the base point
  have hdist5 : dist ((ε, ϑ) : ℝ × ℝ) (ε₀, 0) < r₅ := by
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, sub_zero, hϑabs]
    exact max_lt (by rw [abs_lt]; constructor <;> linarith [min_le_left r₅ r₈])
      (by linarith)
  have hfb := hfamball hdist5
  change dist ((ε, F.q11 ε ϑ, F.q12 ε ϑ, F.c ε ϑ) : ℝ × ℝ × ℝ × ℝ)
    (ε₀, F.q11 ε₀ 0, F.q12 ε₀ 0, F.c ε₀ 0) < rmin at hfb
  rw [hc00, Prod.dist_eq, Prod.dist_eq, Prod.dist_eq] at hfb
  simp only [Real.dist_eq, sub_zero] at hfb
  have hfb1 : |ε - ε₀| < rmin := lt_of_le_of_lt (le_max_left _ _) hfb
  have hfb2 : |F.q11 ε ϑ - a₀| < rmin :=
    lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hfb
  have hfb3 : |F.q12 ε ϑ - b₀| < rmin :=
    lt_of_le_of_lt (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hfb
  have hfb4 : |F.c ε ϑ| < rmin :=
    lt_of_le_of_lt (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hfb
  have hrE' : rmin ≤ rE := min_le_left _ _
  have hr₃' : rmin ≤ r₃ := le_trans (min_le_right _ _) (min_le_left _ _)
  have hr₈' : rmin ≤ r₈ := le_trans (min_le_right _ _) (min_le_right _ _)
  -- the four estimates
  have hEb := hE ε (F.q11 ε ϑ) (F.q12 ε ϑ) (F.c ε ϑ) (by linarith) (by linarith) (by linarith)
    (by linarith)
  have hζε : |zetaFun d ε - b₀| < r₃ := by
    have := hζball (show dist ε ε₀ < r₆ by rw [Real.dist_eq]; linarith [min_le_left r₆ r₇])
    rw [Real.dist_eq, ← hb00] at this
    exact this
  have hψb := hψ ε (F.q12 ε ϑ) (zetaFun d ε) (by linarith) (by rw [← hb00]; linarith)
    (by rw [← hb00]; linarith)
  have hψs : |psiStar d ε - psiStar d ε₀| < 1 := by
    have := hψball (show dist ε ε₀ < r₇ by rw [Real.dist_eq]; linarith [min_le_right r₆ r₇])
    rwa [Real.dist_eq] at this
  have hAb : A₁ < Afun H d ε (F.q12 ε ϑ) := by
    have := hAball (show dist ((ε, F.q12 ε ϑ) : ℝ × ℝ) (ε₀, b₀) < r₈ by
      rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
      exact max_lt (by linarith) (by linarith))
    exact this
  have hK₄b := hK₄ ε ϑ (by linarith) hϑ0.le
  refine ⟨hεU, hϑF', ?_⟩
  -- name the quantities
  set a := F.q11 ε ϑ with ha
  set b := F.q12 ε ϑ with hb
  set c := F.c ε ϑ with hcdef
  set Nb := Nfun ε b with hNb
  set Db := Dfun d ε b with hDb
  set A := Afun H d ε b with hA
  set Sh := Shat ε a b c with hSh
  set h := Real.rpow (ε ^ m + ϑ) ((d : ℝ) / (m : ℝ)) - ε ^ d with hh
  set X := 2 * ϑ / ((Fintype.card V : ℝ) * ε ^ (m - d)) with hX
  have hent : (F.graphon ε ϑ).entropy = Sh := F.graphon_entropy hεU hϑ0 hϑF'
  have hdens : That H ε a b c = ε ^ m + ϑ := F.density ε hεU ϑ hϑF
  have hEq : entQuot H d (ε, a, b, c) = A * (Sh - S0 ε) - Nb * ϑ := by
    show Afun H d ε b * (Shat ε a b c - S0 ε) - Nfun ε b * (That H ε a b c - ε ^ m) = _
    rw [hdens]; ring
  set E := entQuot H d (ε, a, b, c) with hEdef
  have hDpos : 0 < Db := Dfun_pos hd hεI.1 h12.1.le h12ne
  have hεpow : 0 < ε ^ (m - d) := pow_pos hεI.1 _
  have hvε : 0 < (Fintype.card V : ℝ) * ε ^ (m - d) := mul_pos hV hεpow
  have hAeq : A = (Fintype.card V : ℝ) * ε ^ (m - d) * Db := rfl
  have hApos : 0 < A := by linarith [hAb, show (0:ℝ) < A₁ by rw [hA₁]; linarith]
  have hψdef : psiD d ε b = Nb / Db := rfl
  -- (1) the entropy in terms of `E`
  have h1 : 2 * (S0 ε - Sh) = -(psiD d ε b) * X - 2 * E / A := by
    have hSh : Sh - S0 ε = (Nb * ϑ + E) / A := by
      rw [eq_div_iff (ne_of_gt hApos)]; linarith [hEq]
    have : 2 * (S0 ε - Sh) = -2 * (Nb * ϑ + E) / A := by
      rw [show S0 ε - Sh = -(Sh - S0 ε) by ring, hSh]; ring
    rw [this, hψdef, hX, hAeq]
    field_simp
    ring
  -- (2) `ψ_d(ε,b) ≥ ψ_* - L₃L₂ϑ`
  have h2 : psiStar d ε - L₃ * L₂ * ϑ ≤ psiD d ε b := by
    have hlip : |psiD d ε b - psiD d ε (zetaFun d ε)| ≤ L₃ * (L₂ * ϑ) := by
      refine le_trans hψb (mul_le_mul_of_nonneg_left ?_ hL₃0)
      rw [← hϑabs]; exact hqle
    have h' := (abs_le.mp hlip).1
    have hps : psiStar d ε = psiD d ε (zetaFun d ε) := rfl
    have hmul : L₃ * (L₂ * ϑ) = L₃ * L₂ * ϑ := by ring
    rw [hps]
    linarith [h', hmul]
  -- (3) bounds on the coefficients
  have hXnn : 0 ≤ X := by rw [hX]; positivity
  have hXle : X ≤ 2 * ϑ * B₂ := by
    rw [hX, hB₂, div_eq_mul_one_div]
    refine mul_le_mul_of_nonneg_left ?_ (by linarith)
    have hpow : (ε₀ / 2) ^ (m - d) ≤ ε ^ (m - d) :=
      pow_le_pow_left₀ (by linarith [hε₀.1]) (by linarith) _
    exact one_div_le_one_div_of_le (mul_pos hV (pow_pos (by linarith [hε₀.1]) _))
      (mul_le_mul_of_nonneg_left hpow hV.le)
  have hneg : psiStar d ε < 0 := psiStar_neg hd hεI hεr
  have hB₁b : -psiStar d ε ≤ B₁ := by
    rw [hB₁]; have := abs_lt.mp hψs; have := neg_abs_le (psiStar d ε₀); linarith
  have hcsq : c ^ 2 ≤ L₁ ^ 2 * ϑ ^ 2 := by
    have h' : |c| ≤ L₁ * ϑ := by rw [← hϑabs]; exact hcle
    have h0 : 0 ≤ |c| := abs_nonneg c
    calc c ^ 2 = |c| ^ 2 := (sq_abs c).symm
      _ ≤ (L₁ * ϑ) ^ 2 := pow_le_pow_left₀ h0 h' 2
      _ = L₁ ^ 2 * ϑ ^ 2 := by ring
  have hEb' : |E| ≤ LE * (L₁ ^ 2 * ϑ ^ 2) := le_trans hEb (mul_le_mul_of_nonneg_left hcsq hLE0)
  have hA₁pos : 0 < A₁ := by rw [hA₁]; linarith
  have h3 : -(2 * E / A) ≤ 2 * LE * L₁ ^ 2 / A₁ * ϑ ^ 2 := by
    have hE' : -E ≤ LE * (L₁ ^ 2 * ϑ ^ 2) := le_trans (neg_le_abs E) hEb'
    have hnum : 0 ≤ LE * (L₁ ^ 2 * ϑ ^ 2) := by positivity
    calc -(2 * E / A) = 2 * (-E) / A := by ring
      _ ≤ 2 * (LE * (L₁ ^ 2 * ϑ ^ 2)) / A := by
          apply div_le_div_of_nonneg_right _ hApos.le; linarith
      _ ≤ 2 * (LE * (L₁ ^ 2 * ϑ ^ 2)) / A₁ :=
          div_le_div_of_nonneg_left (by positivity) hA₁pos hAb.le
      _ = 2 * LE * L₁ ^ 2 / A₁ * ϑ ^ 2 := by ring
  -- (4) combine
  have h4 : -(psiD d ε b) * X ≤ -psiStar d ε * X + L₃ * L₂ * ϑ * X := by
    have hm := mul_le_mul_of_nonneg_right h2 hXnn
    linarith [hm]
  have h5 : L₃ * L₂ * ϑ * X ≤ 2 * L₃ * L₂ * B₂ * ϑ ^ 2 := by
    have hc0 : 0 ≤ L₃ * L₂ * ϑ := by positivity
    have hm := mul_le_mul_of_nonneg_left hXle hc0
    have e : L₃ * L₂ * ϑ * (2 * ϑ * B₂) = 2 * L₃ * L₂ * B₂ * ϑ ^ 2 := by ring
    linarith [hm, e]
  have h6 : -psiStar d ε * X ≤ -psiStar d ε * h + B₁ * K₄ * ϑ ^ 2 := by
    have hpos : 0 ≤ -psiStar d ε := by linarith
    have hXh : X ≤ h + K₄ * ϑ ^ 2 := by linarith [hK₄b]
    have hm1 := mul_le_mul_of_nonneg_left hXh hpos
    have hK₄sq : 0 ≤ K₄ * ϑ ^ 2 := by positivity
    have hm2 := mul_le_mul_of_nonneg_right hB₁b hK₄sq
    have e1 : -psiStar d ε * (h + K₄ * ϑ ^ 2) = -psiStar d ε * h + (-psiStar d ε) * (K₄ * ϑ ^ 2) :=
      by ring
    have e2 : B₁ * (K₄ * ϑ ^ 2) = B₁ * K₄ * ϑ ^ 2 := by ring
    linarith [hm1, hm2, e1, e2]
  rw [hent, hK]
  have e3 : (B₁ * K₄ + 2 * L₃ * L₂ * B₂ + 2 * LE * L₁ ^ 2 / A₁) * ϑ ^ 2
      = B₁ * K₄ * ϑ ^ 2 + 2 * L₃ * L₂ * B₂ * ϑ ^ 2 + 2 * LE * L₁ ^ 2 / A₁ * ϑ ^ 2 := by ring
  linarith [h1, h3, h4, h5, h6, e3]

end UpperTailOptimizers
