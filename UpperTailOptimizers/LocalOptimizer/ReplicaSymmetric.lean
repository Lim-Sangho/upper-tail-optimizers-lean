import UpperTailOptimizers.LocalOptimizer.Basic

/-!
# Section 6 of `paper/bipodal_optimizer.tex`, part (a): the replica-symmetric side `p ≥ pc(r)`

Part (a) of the paper's `thm:local-optimizer-structure`: for `p` on the replica-symmetric side
of a regular Lubetzky–Zhao boundary arc and close enough to the boundary, the **unique** optimizer of the
upper-tail problem is the constant graphon `W ≡ r`.

The paper obtains this by quoting the uniqueness clause of Lubetzky–Zhao
(`thm:lz-criterion`) at a point where condition (M2) supplies a supporting line.
Here uniqueness is instead *derived*, so no new axiom is needed:

* at the boundary value `p = pc(r)` it is exactly `boundary_uniqueness`;
* for `pc(r) < p < p_*` the arc's `orientation` field (the replica-symmetric half of (M2))
  supplies a supporting line whose integral against the law `μ` of `W^d` already gives the
  **value** `Φ_H(p,r) = J_p(r)` — so the `lubetzkyZhao` axiom is not needed here either —
  and uniqueness follows from the arc's `noFlatTie` field applied to that same law: the
  supporting line forces the `d`-th moment `∫W^d` down to `r^d`, the generalized Hölder bound
  forces it up to `r^d`, and then `noFlatTie` turns the equality `∫φ_{p,d} dμ = J_p(r)` into
  `μ = δ_{r^d}`, i.e. `W ≡ r` a.e.

The auxiliary object is `powDistribution W d`, the pushforward of the graphon measure `gμ` along
`z ↦ W(z)^d`; the lemmas around it are the dictionary between graphon integrals and the
scalar measure statements of `noFlatTie`.
-/

namespace UpperTailOptimizers

open MeasureTheory Real Set Filter

/-! ### The law of `W^d` -/

/-- The Lubetzky–Zhao one-variable function `φ_{p,d}` is measurable. -/
theorem measurable_phi (p : ℝ) (d : ℕ) : Measurable (phi p d) :=
  (measurable_Jp p).comp (Real.continuous_rpow_const (by positivity)).measurable

/-- `z ↦ W(z)^d` is measurable. -/
theorem measurable_powFun (W : Graphon) (d : ℕ) :
    Measurable (fun z : ℝ × ℝ => (W.toFun z.1 z.2) ^ d) :=
  W.measurable_uncurry.pow_const d

/-- **The law of `W^d`**: the pushforward of the graphon measure along `z ↦ W(z)^d`.  It is the
`[0,1]`-valued probability law that the `noFlatTie` field is stated about. -/
noncomputable def powDistribution (W : Graphon) (d : ℕ) : Measure ℝ :=
  Measure.map (fun z : ℝ × ℝ => (W.toFun z.1 z.2) ^ d) gμ

instance instIsProbabilityMeasurePowLaw (W : Graphon) (d : ℕ) :
    IsProbabilityMeasure (powDistribution W d) :=
  Measure.isProbabilityMeasure_map (measurable_powFun W d).aemeasurable

/-- The law of `W^d` is carried by `[0,1]`. -/
theorem powLaw_compl_Icc (W : Graphon) (d : ℕ) : powDistribution W d (Set.Icc (0:ℝ) 1)ᶜ = 0 := by
  have hpre : (fun z : ℝ × ℝ => (W.toFun z.1 z.2) ^ d) ⁻¹' (Set.Icc (0:ℝ) 1)ᶜ = ∅ := by
    ext z
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_Icc, Set.mem_empty_iff_false,
      iff_false, not_not]
    exact ⟨pow_nonneg (W.nonneg' _ _) d, pow_le_one₀ (W.nonneg' _ _) (W.le_one' _ _)⟩
  rw [powDistribution, Measure.map_apply (measurable_powFun W d) measurableSet_Icc.compl, hpre,
    measure_empty]

/-- The mean of the law of `W^d` is the `d`-th moment `∫∫ W^d`. -/
theorem powLaw_integral_id (W : Graphon) (d : ℕ) : ∫ x, x ∂(powDistribution W d) = W.Wmoment d := by
  rw [powDistribution, integral_map (measurable_powFun W d).aemeasurable
    (f := fun x : ℝ => x) measurable_id'.aestronglyMeasurable]
  rfl

/-- Integrating `φ_{p,d}` against the law of `W^d` returns `I_p(W)` (because
`φ_{p,d}(W^d) = J_p(W)`). -/
theorem powLaw_integral_phi {p : ℝ} {d : ℕ} (hd : 2 ≤ d) (W : Graphon) :
    ∫ x, phi p d x ∂(powDistribution W d) = W.Ip p := by
  rw [powDistribution, integral_map (measurable_powFun W d).aemeasurable
    (measurable_phi p d).aestronglyMeasurable]
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  exact (Jp_eq_phi_pow hd (W.nonneg' z.1 z.2)).symm

/-- If the law of `W^d` is a Dirac mass at `c`, then `W^d = c` almost everywhere. -/
theorem ae_pow_eq_of_powLaw_dirac {W : Graphon} {d : ℕ} {c : ℝ}
    (h : powDistribution W d = Measure.dirac c) : ∀ᵐ z ∂gμ, (W.toFun z.1 z.2) ^ d = c := by
  have hset : MeasurableSet {x : ℝ | x = c} := measurableSet_eq
  have h1 : ∀ᵐ x ∂(powDistribution W d), x = c := by
    rw [h]
    exact (ae_dirac_iff hset).mpr rfl
  rw [powDistribution, ae_map_iff (measurable_powFun W d).aemeasurable hset] at h1
  exact h1

/-! ### The supporting-line bound on the replica-symmetric side -/

/-- **Integrating the `orientation` supporting line against the law of `W^d`.**  If the affine function
`x ↦ J_p(r) + a(x - r^d)` lies below `φ_{p,d}` on `[0,1]`, then its slope is positive (test at
`x = p^d`, where `φ_{p,d}` vanishes) and

`J_p(r) + a(∫∫W^d - r^d) ≤ I_p(W)`

for every graphon `W`.  Both halves of Section 6, part (a) — the value `Φ_H = J_p(r)` and the
uniqueness — are read off from this. -/
private theorem rs_supporting_bound {d : ℕ} (hd : 2 ≤ d) {p r a : ℝ}
    (hp0 : 0 < p) (hpr : p < r) (hr1 : r < 1)
    (ha : ∀ x ∈ Set.Icc (0:ℝ) 1, Jp p r + a * (x - r ^ d) ≤ phi p d x) (W : Graphon) :
    0 < a ∧ Jp p r + a * (W.Wmoment d - r ^ d) ≤ W.Ip p := by
  have hp1 : p < 1 := lt_trans hpr hr1
  have hdne : d ≠ 0 := by omega
  -- `a > 0`: test the supporting line at `x = p^d`, where `φ_{p,d}` vanishes
  have hapos : 0 < a := by
    have hpd_mem : p ^ d ∈ Set.Icc (0:ℝ) 1 := ⟨pow_nonneg hp0.le d, pow_le_one₀ hp0.le hp1.le⟩
    have h1 := ha _ hpd_mem
    rw [← Jp_eq_phi_pow hd hp0.le, Jp_self hp0 hp1] at h1
    have h2 : p ^ d < r ^ d := pow_lt_pow_left₀ hpr hp0.le hdne
    have h3 : 0 < Jp p r := Jp_pos_of_gt hp0 hp1 hpr hr1
    nlinarith [h1, h2, h3]
  refine ⟨hapos, ?_⟩
  set μ := powDistribution W d with hμdef
  have hμcompl : μ (Set.Icc (0:ℝ) 1)ᶜ = 0 := powLaw_compl_Icc W d
  have hμae : ∀ᵐ x ∂μ, x ∈ Set.Icc (0:ℝ) 1 := by rw [ae_iff]; exact hμcompl
  have hrestrict : μ.restrict (Set.Icc (0:ℝ) 1) = μ := Measure.restrict_eq_self_of_ae_mem hμae
  have hint_phi : Integrable (phi p d) μ := by
    rw [← hrestrict]; exact (phi_continuousOn_Icc hd hp0 hp1).integrableOn_Icc
  have hint_id : Integrable (fun x : ℝ => x) μ := by
    rw [← hrestrict]; exact continuous_id.continuousOn.integrableOn_Icc
  have hint_aff : Integrable (fun x : ℝ => a * (x - r ^ d)) μ :=
    (hint_id.sub (integrable_const _)).const_mul a
  have hint_L : Integrable (fun x : ℝ => Jp p r + a * (x - r ^ d)) μ :=
    (integrable_const _).add hint_aff
  -- `∫ (J_p(r) + a(x - r^d)) dμ = J_p(r) + a(∫∫W^d - r^d)`
  have hsplit : ∫ x, (Jp p r + a * (x - r ^ d)) ∂μ
      = (∫ _ : ℝ, Jp p r ∂μ) + ∫ x, a * (x - r ^ d) ∂μ :=
    integral_add (integrable_const _) hint_aff
  have hmul : ∫ x, a * (x - r ^ d) ∂μ = a * ∫ x, (x - r ^ d) ∂μ := integral_const_mul _ _
  have hsub : ∫ x, (x - r ^ d) ∂μ = W.Wmoment d - r ^ d := by
    rw [integral_sub hint_id (integrable_const _), powLaw_integral_id W d]
    simp
  have hconst : (∫ _ : ℝ, Jp p r ∂μ) = Jp p r := by simp
  have hLint : ∫ x, (Jp p r + a * (x - r ^ d)) ∂μ = Jp p r + a * (W.Wmoment d - r ^ d) := by
    rw [hsplit, hmul, hsub, hconst]
  have hLle_ae : ∀ᵐ x ∂μ, Jp p r + a * (x - r ^ d) ≤ phi p d x := by
    filter_upwards [hμae] with x hx; exact ha x hx
  have hmono := integral_mono_ae hint_L hint_phi hLle_ae
  rw [hLint, powLaw_integral_phi hd W] at hmono
  exact hmono

/-! ### Part (a) -/

/-- **`thm:local-optimizer-structure`(a): the replica-symmetric side.**  On a regular Lubetzky–Zhao boundary arc, for every `p`
with `pc(r) ≤ p < p_*` and `p < r`:

* the upper-tail value is the constant-graphon value, `Φ_H(p,r) = J_p(r)`;
* the constant graphon `W ≡ r` attains it;
* it is the **unique** optimizer: every optimizer equals `r` almost everywhere.

At `p = pc(r)` this is `boundary_uniqueness`; for `p > pc(r)` both the value and the
uniqueness come from the arc's `orientation` and `noFlatTie` fields applied to
`powDistribution W d`, so the whole statement rests on `generalized_holder` alone — in particular it does
*not* consume `lubetzkyZhao`, which is where the paper takes its uniqueness clause from.  The window is the *global* replica-symmetric window
`(pc r, p_*)` of the arc, so nothing here depends on `r` through an unspecified radius; that
is what lets `thm:local-optimizer-structure` take one window width `η` for all `r` near `r₀`. -/
theorem replica_symmetric_unique {d : ℕ} (hd : 2 ≤ d) (M : LZBoundaryArc d) {r : ℝ} (hr : r ∈ M.U)
    {p : ℝ} (hp_ge : M.pc r ≤ p) (hp_ps : p < pStar d) (hpr : p < r)
    {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (hreg : ∀ v, H.degree v = d) (hm : 1 ≤ H.edgeFinset.card) :
    phiVar H p r = Jp p r ∧
    (∀ hr' : r ∈ Set.Icc (0:ℝ) 1, (constGraphon r hr').Ip p = phiVar H p r) ∧
    (∀ W : Graphon, Feasible H r W → W.Ip p = phiVar H p r →
      ∀ᵐ z ∂gμ, W.toFun z.1 z.2 = r) := by
  classical
  obtain ⟨hpc0, hpcr, hr1, -⟩ := M.ordering r hr
  have hr0 : 0 < r := lt_trans hpc0 hpcr
  have hr_mem : r ∈ Set.Icc (0:ℝ) 1 := ⟨hr0.le, hr1.le⟩
  have hd1 : 1 ≤ d := le_trans (by norm_num) hd
  have hdne : d ≠ 0 := by omega
  -- injectivity of `· ^ d` on the nonnegatives
  have pow_inj : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → x ^ d = y ^ d → x = y := by
    intro x y hx hy hxy
    rcases lt_trichotomy x y with h | h | h
    · exact absurd hxy (ne_of_lt (pow_lt_pow_left₀ h hx hdne))
    · exact h
    · exact absurd hxy.symm (ne_of_lt (pow_lt_pow_left₀ h hy hdne))
  have hRS := M.orientation r hr
  have hNFT := M.noFlatTie r hr
  have hp0 : 0 < p := lt_of_lt_of_le hpc0 hp_ge
  have hp1 : p < 1 := lt_trans hpr hr1
  -- optimality of the constant graphon, in both cases
  have hlower : ∀ W : Graphon, Feasible H r W → Jp p r ≤ W.Ip p := by
    rcases eq_or_lt_of_le hp_ge with hpeq | hpgt
    · -- boundary value: `boundary_uniqueness`
      intro W hW
      have h := (boundary_uniqueness hd M hr H hreg hm).2.1 W hW
      rwa [hpeq] at h
    · -- replica-symmetric side: the `orientation` supporting line + generalized Hölder
      intro W hW
      obtain ⟨a, ha⟩ := hRS p hpgt hp_ps
      obtain ⟨hapos, hbound⟩ := rs_supporting_bound hd hp0 hpr hr1 ha W
      have hmom : r ^ d ≤ W.Wmoment d := holder_moment H hreg hd W hr0.le hm hW
      have : 0 ≤ a * (W.Wmoment d - r ^ d) := mul_nonneg hapos.le (by linarith)
      linarith
  have hattain : ∀ hr' : r ∈ Set.Icc (0:ℝ) 1, (constGraphon r hr').Ip p = Jp p r :=
    fun hr' => Ip_constGraphon hr' p
  have hphi : phiVar H p r = Jp p r := by
    refine le_antisymm (phiVar_le_Jp H hp0 hp1 hr_mem) ?_
    refine le_csInf ⟨Jp p r, ⟨constGraphon r hr_mem, feasible_constGraphon H hr_mem,
      hattain hr_mem⟩⟩ ?_
    rintro y ⟨W, hWfeas, rfl⟩
    exact hlower W hWfeas
  refine ⟨hphi, fun hr' => by rw [hattain hr', hphi], ?_⟩
  -- uniqueness
  intro W hWfeas hWopt
  rw [hphi] at hWopt
  rcases eq_or_lt_of_le hp_ge with hpeq | hpgt
  · -- boundary: `boundary_uniqueness`
    refine (boundary_uniqueness hd M hr H hreg hm).2.2 W hWfeas ?_
    rw [hpeq]; exact hWopt
  · -- replica-symmetric side: `noFlatTie` applied to the law of `W^d`
    obtain ⟨a, ha⟩ := hRS p hpgt hp_ps
    obtain ⟨hapos, hbound⟩ := rs_supporting_bound hd hp0 hpr hr1 ha W
    have hmom : r ^ d ≤ W.Wmoment d := holder_moment H hreg hd W hr0.le hm hWfeas
    rw [hWopt] at hbound
    have hmom_eq : ∫ x, x ∂(powDistribution W d) = r ^ d := by
      rw [powLaw_integral_id W d]
      nlinarith [hbound, hmom, hapos]
    have hphi_int : ∫ x, phi p d x ∂(powDistribution W d) = Jp p r := by
      rw [powLaw_integral_phi hd W, hWopt]
    have hdirac : powDistribution W d = Measure.dirac (r ^ d) :=
      (hNFT p hpgt hp_ps (powDistribution W d) inferInstance (powLaw_compl_Icc W d) hmom_eq).2 hphi_int
    filter_upwards [ae_pow_eq_of_powLaw_dirac (W := W) (d := d) (c := r ^ d) hdirac] with z hz
    exact pow_inj _ _ (W.nonneg' z.1 z.2) hr0.le hz

end UpperTailOptimizers
