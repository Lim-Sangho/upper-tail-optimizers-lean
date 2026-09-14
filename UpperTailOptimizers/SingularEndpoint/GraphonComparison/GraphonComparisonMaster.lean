import UpperTailOptimizers.SingularEndpoint.AuxiliaryLagrangian.LagrangeBridge
import UpperTailOptimizers.SingularEndpoint.LocalizationRankOne.LocalizationMain
import UpperTailOptimizers.SingularEndpoint.GraphonComparison.GraphonComparisonMain
import UpperTailOptimizers.SingularEndpoint.AuxiliaryLagrangian.DistributionFinal
import UpperTailOptimizers.SingularEndpoint.GraphonComparison.RowJensen

/-!
# The assembly of `lem:graphon-lagrangian-bound` (Section 5, `paper/sections/singular.tex`)

`eq:graphon-lagrangian-bound` is the assembly of three estimates at a **common** window
radius, as in the paper's proof, which combines the auxiliary Lagrangian bound with the
central, mixed and tail–tail parts of the remaining double integral.  The paper's proof has
no numbered steps; the step numbers here and below are the Lean's:

* **Step 1**, the rank-one law: the refined form of `eq:auxiliary-lagrangian-bound`
  (`KKTFamily.exists_distributionGap_refined_window_forall`), together with the tail bound
  `Ψ_h ≥ b_ρ` of `lem:first-variation-bound`
  (`KKTFamily.exists_firstVariation_upperGap`, integrated by `setIntegral_PsiT_ge`).  **This is
  the only source of a positive coefficient of the tail mass `ε = ν(T_ρ)`** (Lean notation,
  closed window; the paper's `ν(𝒯_ρ)`); Steps 2 and 3 only spend it;
* **Step 2**, the central square (`comparisonMain_exists_central_bound`);
* **Step 3**, the complement of the central square (`rowJensen_exists_mixed`,
  `rowJensen_exists_tailSq`), whose two rectangles cost at most `b_ρ/4` each.

The first two are stated against a general probability measure `ν` and against the `χ` weights
of `SingularEndpoint/GraphonComparison/GraphonComparisonMain.lean` respectively, the third with iterated set-restricted
integrals.  This file puts all three in the same language — `ν` is the law of `f`
(`comparison_distribution_window`, `_tail`, `_diff`, `_moment`), and the `χ`-weighted integrals are
converted by `comparisonMain_integral_mixed_eq`, `comparisonMain_integral_tailSqRect_eq` and the three-way
split `comparisonMain_split_three` — and adds them.

Below, "under `eq:graphon-comparison-estimates`" refers to the Lean hypothesis bundle
`ε, |Δ|, A_ρ ≤ Kh⁴` and `‖E‖₂ ≤ Kh²`, the rates supplied by `singular_endpoint_localization`.
They are sharper than the rates `|Δ_h(ν)| ≤ C_dh²` and `‖E‖₂ ≤ C_dh` listed in the paper's
display.  `graphon_lagrangian_bound_of_close` (`SingularEndpoint/GraphonComparison/GraphonLagrangianBound.lean`)
assumes only `‖f - u_*‖₄, ‖E‖₂ ≤ K₀h`.

## Contents

* `exists_comparisonDistribution_refined` — the refined form of `eq:auxiliary-lagrangian-bound` read at the law of
  `f`, i.e. entirely in the `x`-coordinate of the graphon;
* `comparisonMasterErr` — the error aggregate `𝔈` of Steps 3–4;
* `exists_comparison_premaster` — Step 5's algebra: `eq:graphon-lagrangian-bound` with the
  bracket multiplying `ε` still carrying the Lean loss terms `ζ(h)` (`zeta`) and `C_err·𝔈`,
  which have no counterpart in the paper;
* `comparisonMasterMaj`, `comparisonMaster_tendsto_maj`, `comparisonMaster_exists_maj_le`,
  `comparisonMaster_err_le_maj` — the majorant of `𝔈` under `eq:graphon-comparison-estimates` and its
  vanishing;
* **`exists_comparison_master`** — `eq:graphon-lagrangian-bound`;
* `Qh_eq_sq_sub`, `sq_Qh_le`, **`family_Ah_le`** — the a-priori bound
  `A_ρ ≤ 16‖f - u_*‖₄⁴ + 16(u_h - u_*)⁴ + 2h⁴` that `exists_comparison_master` consumes (not a
  clause of the paper's `eq:graphon-comparison-estimates`, but a consequence of its clause
  `‖f - u_*‖₄ ≤ C_d h`), which `singular_endpoint_localization` does not supply;
* `exists_abs_u_sub_le`, **`exists_singular_endpoint_comparison`** — the master estimate for an
  actual near-optimal feasible competitor, with no a-priori hypothesis left;
* `exists_abs_muVal_le`, **`exists_singular_endpoint_comparison_graph`** — the same with the
  graph-carrying Lagrangian `μ_h{t(H,W) - r_h^m}` in place of the layer's `η_hΔ`, which is
  the form `terminal_optimality_of_master` consumes.
-/

namespace UpperTailOptimizers

namespace SingularEndpoint

open MeasureTheory

variable {d : ℕ}

/-! ## The refined law bound at the law of `f` -/

/-- **The refined form of `eq:auxiliary-lagrangian-bound`, read at `ν = law(f)`.**

`KKTFamily.exists_distributionGap_refined_window_forall` is stated for an arbitrary
probability measure carried by `[0,2]`; every consumer downstream wants it at the law of the
Factor factor, where `A_ρ`, `ν(T_ρ)`, `∫_{T_ρ}Ψ_h dν` and `m_d(ν)` become integrals over
`G_ρ`, `G_ρ^c` and `[0,1]` in the graphon's own coordinate.  The four translations are
`comparison_distribution_window`, `comparison_distribution_tail`, `comparison_distribution_diff` and
`comparison_distribution_moment`; nothing else changes, and the radius stays universally quantified
below `ρ₀` so that the Step-5 join can meet the residual half. -/
theorem exists_comparisonDistribution_refined (hd : 2 ≤ d) (B : KKTFamily d) :
    ∃ ρ₀ > 0, ∀ K : ℝ, 1 ≤ K → ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ →
      ∃ Cz : ℝ, 0 < Cz ∧ ∃ M : ℝ, 0 < M ∧ ∃ δ₀ > 0,
        ∀ h : ℝ, 0 < h → h < δ₀ → h ≤ 1 → |h| < B.h₀ →
        ∀ f : ℝ → ℝ, Measurable f → (∀ x, 0 ≤ f x) → (∀ x, f x ≤ 2) →
          (unitμ {x | f x ∉ centralWindow d ρ}).toReal ≤ K * h ^ 4 →
          |(∫ x, f x ^ d ∂unitμ) - B.qVal h| ≤ K * h ^ 4 →
            (d : ℝ) ^ 3 / 48
                  * (∫ x in {x | f x ∈ centralWindow d ρ}, B.Qh h (f x) ^ 2 ∂unitμ)
                + (∫ x in {x | f x ∉ centralWindow d ρ}, B.PsiT h (f x) ∂unitμ)
                - zeta Cz K h * (unitμ {x | f x ∉ centralWindow d ρ}).toReal
                - M * ((∫ x, f x ^ d ∂unitμ) - B.qVal h) ^ 2
              ≤ B.distributionJ h (comparisonDistribution f) - B.distributionJ h (B.distributionMeasure h)
                  - B.etaVal h * ((∫ x, f x ^ d ∂unitμ) - B.qVal h) := by
  obtain ⟨ρ₀, hρ₀0, hgapall⟩ := KKTFamily.exists_distributionGap_refined_window_forall hd B
  refine ⟨ρ₀, hρ₀0, ?_⟩
  intro K hK ρ hρ0 hρle
  obtain ⟨Cz, hCz, M, hM, δ₀, hδ₀, hgap⟩ := hgapall K hK ρ hρ0 hρle
  refine ⟨Cz, hCz, M, hM, δ₀, hδ₀, ?_⟩
  intro h hh0 hhδ hh1 hhb f hf hnn hbd htail hmom
  have htail' : (comparisonDistribution f (Set.Icc (0 : ℝ) 2 \ centralWindow d ρ)).toReal ≤ K * h ^ 4 := by
    rw [comparison_distribution_diff hf hnn hbd (measurableSet_centralWindow d ρ)]
    exact htail
  have hmom' : |(∫ x, x ^ d ∂(comparisonDistribution f)) - B.qVal h| ≤ K * h ^ 4 := by
    rw [comparison_distribution_moment hf d]
    exact hmom
  have key := hgap h hh0 hhδ hh1 hhb (comparisonDistribution f) (comparison_isProbabilityMeasure hf)
    (comparison_distribution_compl_Icc hf hnn hbd) htail' hmom'
  rw [comparison_distribution_window hf B h ρ, comparison_distribution_tail hf hnn hbd B h ρ,
    comparison_distribution_diff hf hnn hbd (measurableSet_centralWindow d ρ),
    comparison_distribution_moment hf d] at key
  exact key

/-! ## `eq:graphon-lagrangian-bound`, before the a-priori bounds are spent -/

/-- **The error aggregate of Steps 3–4**,

`𝔈 = A_ρ^{1/4} + A_ρ^{1/2} + ε + |Δ| + L_h(ε + |Δ| + A_ρ^{3/16}) + ‖E‖₂ + ε`,

with `L_h = 1 + log(1/h)`.  Every loss that `exists_comparison_premaster` pays on the `ε`
term is a constant multiple of this.  Under `eq:graphon-comparison-estimates` each summand is
`O(L_h h^{3/4})`, so `𝔈 → 0` as `h ↓ 0`; that is the only thing the passage from the
pre-master estimate to `eq:graphon-lagrangian-bound` needs of it. -/
noncomputable def comparisonMasterErr (B : KKTFamily d) (h ρ : ℝ) {W : Graphon}
    (P : FactorDecomp d W) : ℝ :=
  Real.sqrt (Real.sqrt (∫ y in centralSet d ρ P.f, B.Qh h (P.f y) ^ 2 ∂unitμ))
    + Real.sqrt (∫ y in centralSet d ρ P.f, B.Qh h (P.f y) ^ 2 ∂unitμ)
    + tailMass d ρ P.f
    + |(∫ y, P.f y ^ d ∂unitμ) - B.qVal h|
    + (1 + Real.log (1 / h))
        * (tailMass d ρ P.f + |(∫ y, P.f y ^ d ∂unitμ) - B.qVal h|
          + (∫ y in centralSet d ρ P.f, B.Qh h (P.f y) ^ 2 ∂unitμ) ^ (3 / 16 : ℝ))
    + P.residL2
    + tailMass d ρ P.f

/-- **The algebra of the assembly of `lem:graphon-lagrangian-bound`** (the Lean's Step 5).

For small `h` in the family window, every graphon `W` and every nonlinear Factor
decomposition `W = f ⊗ f + E` satisfying the tail and moment clauses of
`eq:graphon-comparison-estimates` and the pinning smallness of Step 4,

`I_{p_h}(W) - I_{p_h}(W_h) ≥ η_hΔ + a{A_ρ + ‖E‖₂²} + {c - ζ(h) - C_err·𝔈}ε - MΔ²`.

This is `eq:graphon-lagrangian-bound` except that the bracket multiplying `ε` is not yet
known to be positive; making it so is the separate asymptotic step that spends the rest of
`eq:graphon-comparison-estimates` (`ζ(h) → 0` and `𝔈 → 0`).

It is the sum of `exists_comparisonDistribution_refined`, `setIntegral_PsiT_ge`,
`comparisonMain_exists_central_bound` and `rowJensen_exists_mixed` / `_corner`, joined by
`comparison_splitting`, `comparisonMain_entropy_split` and `comparisonMain_residSq_split`, all at a common
`ρ`.

**The `ε` budget.**  Step 1 contributes `+b_ρ ε`.  Against it: `b_ρ/4` for the mixed
rectangles (`rowJensen_exists_mixed` at `β = b_ρ/4`), and `b_ρ/4` for the mixed *residual*
`2a‖E‖²_{2,Ω^c×Ω} ≤ 50a ε` (`mixed_resid_le`), which is why the coercivity constant is
capped at `a ≤ b_ρ/200` — the Lean's counterpart of the paper's choice of `C_{d,ρ} ≥ 1` with
`50C_{d,ρ}^{-1} ≤ b_ρ/16`.  What
is left is `c = b_ρ/2`.  The remaining losses — the corner entropy `C ε²`, the corner residual
`25ε²` and the central bound's `C ε‖E‖₂` — are all bounded by `𝔈·ε` and go into `C_err`.

**The order in which the constants are chosen is forced.**  The KKT smallness
`θ_K = min(d³/96, 1)` depends on `d` alone, so the radius the central bound admits does too;
`ρ` is fixed next; only then does the tail gap `b_ρ` appear, and the coercivity constant is
`a = min(θ_K, b_ρ/200)`.  Choosing `a` first would be circular, since `b_ρ` depends on `ρ` and
the admissible radius depends on the smallness demanded of the KKT error.  This is also why
`comparisonMain_abs_kkt_error_le` has to be stated against the central norm `‖E‖²_{2,G_ρ²}`: the
mixed and corner parts of `‖E‖₂²` are charged to the `ε` budget instead, at the cost of the
`a ≤ b_ρ/200` cap. -/
theorem exists_comparison_premaster (hd : 2 ≤ d) (B : KKTFamily d) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧ ∀ K : ℝ, 1 ≤ K →
      ∃ a : ℝ, 0 < a ∧ ∃ c : ℝ, 0 < c ∧
      ∃ Cz : ℝ, 0 < Cz ∧ ∃ M : ℝ, 0 < M ∧ ∃ Cerr : ℝ, 0 < Cerr ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧
      ∀ (h : ℝ) (hb : |h| < B.h₀), 0 < h → h < δ₀ → h ≤ 1 →
      ∀ (W : Graphon) (P : FactorDecomp d W),
        tailMass d ρ P.f ≤ K * h ^ 4 →
        |(∫ x, P.f x ^ d ∂unitμ) - B.qVal h| ≤ K * h ^ 4 →
        (∫ x, (P.f x - uStar d) ^ 4 ∂unitμ) ≤ K * h ^ 4 →
          B.etaVal h * ((∫ x, P.f x ^ d ∂unitμ) - B.qVal h)
              + a * ((∫ x in centralSet d ρ P.f, B.Qh h (P.f x) ^ 2 ∂unitμ)
                  + P.residSq)
              + (c - zeta Cz K h - Cerr * comparisonMasterErr B h ρ P) * tailMass d ρ P.f
              - M * ((∫ x, P.f x ^ d ∂unitμ) - B.qVal h) ^ 2
            ≤ W.Ip (B.p h) - (B.graphon hb).Ip (B.p h) := by
  have hdp : (0 : ℝ) < (d : ℝ) := dpos hd
  obtain ⟨θK, hθK⟩ : ∃ t : ℝ, t = min ((d : ℝ) ^ 3 / 96) 1 := ⟨_, rfl⟩
  have hθK0 : 0 < θK := by rw [hθK]; exact lt_min (by positivity) one_pos
  have hθK1 : θK ≤ 1 := by rw [hθK]; exact min_le_right _ _
  have hθKd : θK ≤ (d : ℝ) ^ 3 / 96 := by rw [hθK]; exact min_le_left _ _
  obtain ⟨ρP, hρP0, hprofall⟩ := exists_comparisonDistribution_refined hd B
  obtain ⟨ρC, hρC0, -, -, hcentall⟩ := comparisonMain_exists_central_bound hd B hθK0
  obtain ⟨ρ, hρ0, hρ1, hρP, hρC⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧ ρ ≤ ρP ∧ ρ ≤ ρC :=
    ⟨min (min ρP ρC) 1, lt_min (lt_min hρP0 hρC0) one_pos, min_le_right _ _,
      le_trans (min_le_left _ _) (min_le_left _ _),
      le_trans (min_le_left _ _) (min_le_right _ _)⟩
  refine ⟨ρ, hρ0, hρ1, ?_⟩
  intro K hK
  have hK0 : (0 : ℝ) ≤ K := by linarith
  -- the tail gap `b_ρ` of `lem:first-variation-bound`: the ONLY source of a
  -- positive `ε`-coefficient in the proof
  obtain ⟨b, hb0, δb, hδb, hbtail⟩ := KKTFamily.exists_firstVariation_upperGap hd B hρ0
  obtain ⟨δR, hδR, hmix⟩ := rowJensen_exists_mixed hd B ρ (β := b / 4) (by linarith) hK0
  obtain ⟨CK, hCK, δK, hδK, hcorner⟩ := rowJensen_exists_tailSq hd B ρ
  obtain ⟨Cz, hCz, MP, hMP, δP, hδP, hprof⟩ := hprofall K hK ρ hρ0 hρP
  obtain ⟨CC, hCC, δC, hδC, hcent⟩ := hcentall ρ hρ0 hρC
  obtain ⟨a, ha⟩ : ∃ t : ℝ, t = min θK (b / 200) := ⟨_, rfl⟩
  have ha0 : 0 < a := by rw [ha]; exact lt_min hθK0 (by linarith)
  have haK : a ≤ θK := by rw [ha]; exact min_le_left _ _
  have hab : a ≤ b / 200 := by rw [ha]; exact min_le_right _ _
  have ha1 : a ≤ 1 := le_trans haK hθK1
  refine ⟨a, ha0, b / 2, by linarith, Cz, hCz, MP, hMP, CC + CK + 25 + 1,
    by linarith, min (min δR δK) (min (min δP δC) δb),
    lt_min (lt_min hδR hδK) (lt_min (lt_min hδP hδC) hδb), ?_⟩
  intro h hhb hh0 hhδ hh1 W P htail hmom hquart
  have hhR : h < δR := lt_of_lt_of_le hhδ (le_trans (min_le_left _ _) (min_le_left _ _))
  have hhK : |h| < δK := by
    rw [abs_of_pos hh0]
    exact lt_of_lt_of_le hhδ (le_trans (min_le_left _ _) (min_le_right _ _))
  have hhP : h < δP :=
    lt_of_lt_of_le hhδ (le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_left _ _)))
  have hhC : h < δC :=
    lt_of_lt_of_le hhδ (le_trans (min_le_right _ _)
      (le_trans (min_le_left _ _) (min_le_right _ _)))
  have hhb' : |h| < δb := by
    rw [abs_of_pos hh0]
    exact lt_of_lt_of_le hhδ (le_trans (min_le_right _ _) (min_le_right _ _))
  have hsplit := comparison_splitting hd B hhb W P.meas_f P.f_nonneg P.f_bdd
  have hent := comparisonMain_entropy_split hd B hhb P ρ
  have hres := comparisonMain_residSq_split P ρ
  have hcor25 := comparisonMain_tailSq_resid_le P ρ
  have hp := hprof h hh0 hhP hh1 hhb P.f P.meas_f P.f_nonneg P.f_bdd htail hmom
  have hc := hcent h hh0 hhC hhb W P
  have hr := hmix h hh0 hhR hhb W P htail hquart
  have hk := hcorner h hhK W P
  have hΨ := setIntegral_PsiT_ge hd B hρ0 hhb (hbtail h hhb' hhb) P.meas_f P.f_nonneg P.f_bdd
  have hmixres := mixed_resid_le (ρ := ρ) P
  -- the imported estimates speak of `{x | f x ∈ 𝓝_ρ}` and `(unitμ {x | f x ∉ 𝓝_ρ}).toReal`;
  -- `SingularEndpoint/GraphonComparison/RowWindow.lean` names the same terms `centralSet` and `tailMass`.
  have hset : centralSet d ρ P.f = {x | P.f x ∈ centralWindow d ρ} := rfl
  have hsetc : (centralSet d ρ P.f)ᶜ = {x | P.f x ∉ centralWindow d ρ} := rfl
  have hepsdef : (unitμ (centralSet d ρ P.f)ᶜ).toReal = tailMass d ρ P.f := rfl
  simp only [← hset, ← hsetc, hepsdef] at hp hc hent hres hcor25
  -- nonnegativity
  have hGm : MeasurableSet (centralSet d ρ P.f) := measurableSet_centralSet P.meas_f d ρ
  have hGc : MeasurableSet (centralSet d ρ P.f)ᶜ := hGm.compl
  have hA0 : (0 : ℝ) ≤ ∫ x in centralSet d ρ P.f, B.Qh h (P.f x) ^ 2 ∂unitμ :=
    setIntegral_nonneg hGm fun x _ => sq_nonneg _
  have hEmix0 : (0 : ℝ) ≤ ∫ x in (centralSet d ρ P.f)ᶜ,
      (∫ y in centralSet d ρ P.f, P.resid x y ^ 2 ∂unitμ) ∂unitμ :=
    setIntegral_nonneg hGc fun x _ => setIntegral_nonneg hGm fun y _ => sq_nonneg _
  have hEcor0 : (0 : ℝ) ≤ ∫ x in (centralSet d ρ P.f)ᶜ,
      (∫ y in (centralSet d ρ P.f)ᶜ, P.resid x y ^ 2 ∂unitμ) ∂unitμ :=
    setIntegral_nonneg hGc fun x _ => setIntegral_nonneg hGc fun y _ => sq_nonneg _
  have hEcc0 : (0 : ℝ) ≤ ∫ z : ℝ × ℝ, comparisonMainChi d ρ P.f z.1 * comparisonMainChi d ρ P.f z.2
      * P.resid z.1 z.2 ^ 2 ∂gμ :=
    integral_nonneg fun z => by
      have h1 := comparisonMainChi_nonneg d ρ P.f z.1
      have h2 := comparisonMainChi_nonneg d ρ P.f z.2
      positivity
  have hep0 : (0 : ℝ) ≤ tailMass d ρ P.f := ENNReal.toReal_nonneg
  have hL0 : (0 : ℝ) ≤ P.residL2 := P.residL2_nonneg
  have hDl0 : (0 : ℝ) ≤ |(∫ y, P.f y ^ d ∂unitμ) - B.qVal h| := abs_nonneg _
  have hlog : 0 ≤ Real.log (1 / h) := Real.log_nonneg (by rw [le_div_iff₀ hh0]; linarith)
  have hIe0 : (0 : ℝ)
      ≤ (∫ y in centralSet d ρ P.f, B.Qh h (P.f y) ^ 2 ∂unitμ) ^ (3 / 16 : ℝ) :=
    Real.rpow_nonneg hA0 _
  have hErr0 : 0 ≤ comparisonMasterErr B h ρ P := by
    rw [comparisonMasterErr]
    have h1 := Real.sqrt_nonneg (Real.sqrt
      (∫ y in centralSet d ρ P.f, B.Qh h (P.f y) ^ 2 ∂unitμ))
    have h2 := Real.sqrt_nonneg (∫ y in centralSet d ρ P.f, B.Qh h (P.f y) ^ 2 ∂unitμ)
    have h3 : 0 ≤ (1 + Real.log (1 / h))
        * (tailMass d ρ P.f + |(∫ y, P.f y ^ d ∂unitμ) - B.qVal h|
          + (∫ y in centralSet d ρ P.f, B.Qh h (P.f y) ^ 2 ∂unitμ) ^ (3 / 16 : ℝ)) :=
      mul_nonneg (by linarith) (by linarith)
    linarith
  have hεErr : tailMass d ρ P.f ≤ comparisonMasterErr B h ρ P := by
    rw [comparisonMasterErr]
    have h1 := Real.sqrt_nonneg (Real.sqrt
      (∫ y in centralSet d ρ P.f, B.Qh h (P.f y) ^ 2 ∂unitμ))
    have h2 := Real.sqrt_nonneg (∫ y in centralSet d ρ P.f, B.Qh h (P.f y) ^ 2 ∂unitμ)
    have h3 : 0 ≤ (1 + Real.log (1 / h))
        * (tailMass d ρ P.f + |(∫ y, P.f y ^ d ∂unitμ) - B.qVal h|
          + (∫ y in centralSet d ρ P.f, B.Qh h (P.f y) ^ 2 ∂unitμ) ^ (3 / 16 : ℝ)) :=
      mul_nonneg (by linarith) (by linarith)
    linarith
  -- the four coefficient comparisons
  have cA : a * (∫ x in centralSet d ρ P.f, B.Qh h (P.f x) ^ 2 ∂unitμ)
      ≤ ((d : ℝ) ^ 3 / 48 - θK)
        * (∫ x in centralSet d ρ P.f, B.Qh h (P.f x) ^ 2 ∂unitμ) :=
    mul_le_mul_of_nonneg_right (by linarith) hA0
  have cE : a * (∫ z : ℝ × ℝ, comparisonMainChi d ρ P.f z.1 * comparisonMainChi d ρ P.f z.2
        * P.resid z.1 z.2 ^ 2 ∂gμ)
      ≤ (2 - θK) * (∫ z : ℝ × ℝ, comparisonMainChi d ρ P.f z.1 * comparisonMainChi d ρ P.f z.2
        * P.resid z.1 z.2 ^ 2 ∂gμ) :=
    mul_le_mul_of_nonneg_right (by linarith) hEcc0
  -- the mixed residual is now a loss, not a gain: `2a‖E‖²_{2,mixed} ≤ 50aε ≤ (b/4)ε`
  have cM : 2 * a * (∫ x in (centralSet d ρ P.f)ᶜ,
        (∫ y in centralSet d ρ P.f, P.resid x y ^ 2 ∂unitμ) ∂unitμ)
      ≤ b / 4 * tailMass d ρ P.f := by
    have h1 : 2 * a * (∫ x in (centralSet d ρ P.f)ᶜ,
          (∫ y in centralSet d ρ P.f, P.resid x y ^ 2 ∂unitμ) ∂unitμ)
        ≤ 2 * a * (25 * tailMass d ρ P.f) :=
      mul_le_mul_of_nonneg_left hmixres (by linarith)
    have hstep := mul_le_mul_of_nonneg_right hab hep0
    have h2 : 2 * a * (25 * tailMass d ρ P.f) ≤ b / 4 * tailMass d ρ P.f := by
      calc 2 * a * (25 * tailMass d ρ P.f) = 50 * (a * tailMass d ρ P.f) := by ring
        _ ≤ 50 * (b / 200 * tailMass d ρ P.f) := by linarith
        _ = b / 4 * tailMass d ρ P.f := by ring
    linarith
  have cC : a * (∫ x in (centralSet d ρ P.f)ᶜ,
        (∫ y in (centralSet d ρ P.f)ᶜ, P.resid x y ^ 2 ∂unitμ) ∂unitμ)
      ≤ 25 * (tailMass d ρ P.f * tailMass d ρ P.f) := by
    have h1 : a * (∫ x in (centralSet d ρ P.f)ᶜ,
          (∫ y in (centralSet d ρ P.f)ᶜ, P.resid x y ^ 2 ∂unitμ) ∂unitμ)
        ≤ 1 * (∫ x in (centralSet d ρ P.f)ᶜ,
          (∫ y in (centralSet d ρ P.f)ᶜ, P.resid x y ^ 2 ∂unitμ) ∂unitμ) :=
      mul_le_mul_of_nonneg_right ha1 hEcor0
    have h2 : 25 * tailMass d ρ P.f ^ 2
        = 25 * (tailMass d ρ P.f * tailMass d ρ P.f) := by ring
    linarith [h1, hcor25, h2.ge, h2.le]
  -- the `ε²` losses and the central `ε‖E‖₂` loss are constant multiples of `𝔈·ε`
  have hCKε : CK * tailMass d ρ P.f ^ 2 ≤ CK * comparisonMasterErr B h ρ P * tailMass d ρ P.f := by
    have hstep : CK * tailMass d ρ P.f * tailMass d ρ P.f
        ≤ CK * comparisonMasterErr B h ρ P * tailMass d ρ P.f :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hεErr hCK.le) hep0
    calc CK * tailMass d ρ P.f ^ 2 = CK * tailMass d ρ P.f * tailMass d ρ P.f := by ring
      _ ≤ _ := hstep
  have h25ε : 25 * (tailMass d ρ P.f * tailMass d ρ P.f)
      ≤ 25 * comparisonMasterErr B h ρ P * tailMass d ρ P.f := by
    have hstep : 25 * tailMass d ρ P.f * tailMass d ρ P.f
        ≤ 25 * comparisonMasterErr B h ρ P * tailMass d ρ P.f :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hεErr (by norm_num : (0 : ℝ) ≤ 25)) hep0
    calc 25 * (tailMass d ρ P.f * tailMass d ρ P.f)
        = 25 * tailMass d ρ P.f * tailMass d ρ P.f := by ring
      _ ≤ _ := hstep
  have hCCε : CC * (tailMass d ρ P.f * P.residL2)
      ≤ CC * comparisonMasterErr B h ρ P * tailMass d ρ P.f := by
    have hLE : P.residL2 ≤ comparisonMasterErr B h ρ P := by
      rw [comparisonMasterErr]
      have h1 := Real.sqrt_nonneg (Real.sqrt
        (∫ y in centralSet d ρ P.f, B.Qh h (P.f y) ^ 2 ∂unitμ))
      have h2 := Real.sqrt_nonneg (∫ y in centralSet d ρ P.f, B.Qh h (P.f y) ^ 2 ∂unitμ)
      have h3 : 0 ≤ (1 + Real.log (1 / h))
          * (tailMass d ρ P.f + |(∫ y, P.f y ^ d ∂unitμ) - B.qVal h|
            + (∫ y in centralSet d ρ P.f, B.Qh h (P.f y) ^ 2 ∂unitμ) ^ (3 / 16 : ℝ)) :=
        mul_nonneg (by linarith) (by linarith)
      linarith
    have hstep : CC * P.residL2 * tailMass d ρ P.f
        ≤ CC * comparisonMasterErr B h ρ P * tailMass d ρ P.f :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hLE hCC.le) hep0
    calc CC * (tailMass d ρ P.f * P.residL2)
        = CC * P.residL2 * tailMass d ρ P.f := by ring
      _ ≤ _ := hstep
  have hεdistr : (CC + CK + 25 + 1) * comparisonMasterErr B h ρ P * tailMass d ρ P.f
      = CC * comparisonMasterErr B h ρ P * tailMass d ρ P.f
        + CK * comparisonMasterErr B h ρ P * tailMass d ρ P.f
        + 25 * comparisonMasterErr B h ρ P * tailMass d ρ P.f
        + 1 * comparisonMasterErr B h ρ P * tailMass d ρ P.f := by ring
  have hslack : (0 : ℝ) ≤ 1 * comparisonMasterErr B h ρ P * tailMass d ρ P.f := by
    have := mul_nonneg hErr0 hep0; linarith
  -- the positive `ε` term, from the rank-one tail
  have hbε : b * tailMass d ρ P.f ≤ ∫ x in (centralSet d ρ P.f)ᶜ, B.PsiT h (P.f x) ∂unitμ := hΨ
  -- assemble
  rw [hres, hsplit, hent]
  linarith only [hp, hc, hr, hk, hbε, cA, cE, cM, cC, hCKε, h25ε, hCCε, hεdistr.ge,
    hεdistr.le, hslack]

/-! ## The asymptotic step

Everything below turns `exists_comparison_premaster` into `eq:graphon-lagrangian-bound` by
showing that the bracket multiplying `ε` is eventually at least `c/2`.  Under
`eq:graphon-comparison-estimates` every summand of `comparisonMasterErr` is dominated by an explicit
function of `h` alone, and that function tends to `0`. -/

/-- **The majorant of `comparisonMasterErr`** under `eq:graphon-comparison-estimates`: a function of
`h` and `K` alone.  Each summand majorises the corresponding summand of `𝔈` once
`ε, |Δ|, A_ρ ≤ Kh⁴` and `‖E‖₂ ≤ Kh²`. -/
noncomputable def comparisonMasterMaj (K h : ℝ) : ℝ :=
  Real.sqrt (Real.sqrt (K * h ^ 4)) + Real.sqrt (K * h ^ 4) + 3 * (K * h ^ 4)
    + (1 + Real.log (1 / h)) * (2 * (K * h ^ 4) + (K * h ^ 4) ^ (3 / 16 : ℝ))
    + K * h ^ 2

/-- `comparisonMasterMaj K h → 0` as `h ↓ 0`.  The two `L_h`-weighted summands are
`tendsto_logInv_mul_rpow` at `r = 4` and `r = 3/4`, after
`(Kh⁴)^{3/16} = K^{3/16}h^{3/4}`; the rest is continuity. -/
theorem comparisonMaster_tendsto_maj {K : ℝ} (hK : 0 ≤ K) :
    Filter.Tendsto (comparisonMasterMaj K) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hpoly : Filter.Tendsto (fun h : ℝ => K * h ^ 4) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have : Filter.Tendsto (fun h : ℝ => K * h ^ 4) (nhds 0) (nhds (K * (0:ℝ) ^ 4)) :=
      (continuous_const.mul (continuous_pow 4)).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  have hsq : Filter.Tendsto (fun h : ℝ => Real.sqrt (K * h ^ 4))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have := (Real.continuous_sqrt.tendsto (0:ℝ)).comp hpoly
    simpa [Function.comp_def] using this
  have hsqsq : Filter.Tendsto (fun h : ℝ => Real.sqrt (Real.sqrt (K * h ^ 4)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have := (Real.continuous_sqrt.tendsto (0:ℝ)).comp hsq
    simpa [Function.comp_def] using this
  have hsq2 : Filter.Tendsto (fun h : ℝ => K * h ^ 2) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have : Filter.Tendsto (fun h : ℝ => K * h ^ 2) (nhds 0) (nhds (K * (0:ℝ) ^ 2)) :=
      (continuous_const.mul (continuous_pow 2)).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  -- the two `L_h`-weighted summands
  have hL4 : Filter.Tendsto (fun h : ℝ => (1 + Real.log (1 / h)) * (2 * (K * h ^ 4)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have h4 := tendsto_logInv_mul_rpow (r := 4) (by norm_num)
    have := (h4.const_mul (2 * K))
    rw [mul_zero] at this
    refine Filter.Tendsto.congr (fun x => ?_) this
    show 2 * K * ((1 + Real.log (1 / x)) * x ^ (4:ℝ))
      = (1 + Real.log (1 / x)) * (2 * (K * x ^ 4))
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    ring
  have hL3 : Filter.Tendsto
      (fun h : ℝ => (1 + Real.log (1 / h)) * (K * h ^ 4) ^ (3 / 16 : ℝ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have h34 := tendsto_logInv_mul_rpow (r := 3 / 4) (by norm_num)
    have hmul := h34.const_mul (K ^ (3 / 16 : ℝ))
    rw [mul_zero] at hmul
    refine Filter.Tendsto.congr' ?_ hmul
    refine Filter.eventuallyEq_of_mem self_mem_nhdsWithin fun x hx => ?_
    have hx0 : (0 : ℝ) < x := hx
    show K ^ (3 / 16 : ℝ) * ((1 + Real.log (1 / x)) * x ^ (3 / 4 : ℝ))
      = (1 + Real.log (1 / x)) * (K * x ^ 4) ^ (3 / 16 : ℝ)
    have hx4 : (0 : ℝ) ≤ x ^ 4 := by positivity
    rw [Real.mul_rpow hK hx4]
    have hpow : (x ^ 4 : ℝ) ^ (3 / 16 : ℝ) = x ^ (3 / 4 : ℝ) := by
      rw [show (x ^ 4 : ℝ) = x ^ ((4 : ℕ) : ℝ) by rw [Real.rpow_natCast],
        ← Real.rpow_mul hx0.le]
      norm_num
    rw [hpow]
    ring
  have := ((((hsqsq.add hsq).add (hpoly.const_mul 3)).add (hL4.add hL3)).add hsq2)
  simp only [mul_zero, add_zero] at this
  refine Filter.Tendsto.congr (fun x => ?_) this
  show Real.sqrt (Real.sqrt (K * x ^ 4)) + Real.sqrt (K * x ^ 4) + 3 * (K * x ^ 4)
      + ((1 + Real.log (1 / x)) * (2 * (K * x ^ 4))
        + (1 + Real.log (1 / x)) * (K * x ^ 4) ^ (3 / 16 : ℝ)) + K * x ^ 2
    = comparisonMasterMaj K x
  rw [comparisonMasterMaj]
  ring

/-- **The `ε`-form of `comparisonMaster_tendsto_maj`**, in the shape the assembly consumes. -/
theorem comparisonMaster_exists_maj_le {K : ℝ} (hK : 0 ≤ K) {b : ℝ} (hb : 0 < b) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 < h → h < δ → comparisonMasterMaj K h ≤ b := by
  obtain ⟨δ, hδ, hprop⟩ :=
    Metric.tendsto_nhdsWithin_nhds.mp (comparisonMaster_tendsto_maj hK) b hb
  refine ⟨δ, hδ, fun h hh0 hhδ => ?_⟩
  have hmem : h ∈ Set.Ioi (0 : ℝ) := hh0
  have hdist : dist h (0 : ℝ) < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hh0]
    exact hhδ
  have hval := hprop hmem hdist
  rw [Real.dist_eq, sub_zero] at hval
  exact le_trans (le_abs_self _) hval.le

/-- **`comparisonMasterErr` is dominated by `comparisonMasterMaj`** under `eq:graphon-comparison-estimates`.
Termwise: `√·` and `·^{3/16}` are monotone, `2ε + |Δ| ≤ 3Kh⁴`, and `L_h ≥ 0` for `h ≤ 1`. -/
theorem comparisonMaster_err_le_maj (B : KKTFamily d) {h ρ : ℝ} (hh0 : 0 < h) (hh1 : h ≤ 1)
    {W : Graphon} (P : FactorDecomp d W) {K : ℝ}
    (htail : tailMass d ρ P.f ≤ K * h ^ 4)
    (hmom : |(∫ x, P.f x ^ d ∂unitμ) - B.qVal h| ≤ K * h ^ 4)
    (hA : (∫ x in centralSet d ρ P.f, B.Qh h (P.f x) ^ 2 ∂unitμ) ≤ K * h ^ 4)
    (hL : P.residL2 ≤ K * h ^ 2) :
    comparisonMasterErr B h ρ P ≤ comparisonMasterMaj K h := by
  have hA0 : (0 : ℝ) ≤ ∫ x in centralSet d ρ P.f, B.Qh h (P.f x) ^ 2 ∂unitμ :=
    setIntegral_nonneg (measurableSet_centralSet P.meas_f d ρ) fun x _ => sq_nonneg _
  have hlog : 0 ≤ Real.log (1 / h) := Real.log_nonneg (by rw [le_div_iff₀ hh0]; linarith)
  have hLh : (0 : ℝ) ≤ 1 + Real.log (1 / h) := by linarith
  have hep0 : (0 : ℝ) ≤ tailMass d ρ P.f := ENNReal.toReal_nonneg
  have hDl0 : (0 : ℝ) ≤ |(∫ x, P.f x ^ d ∂unitμ) - B.qVal h| := abs_nonneg _
  have h1 : Real.sqrt (Real.sqrt
        (∫ x in centralSet d ρ P.f, B.Qh h (P.f x) ^ 2 ∂unitμ))
      ≤ Real.sqrt (Real.sqrt (K * h ^ 4)) :=
    Real.sqrt_le_sqrt (Real.sqrt_le_sqrt hA)
  have h2 : Real.sqrt (∫ x in centralSet d ρ P.f, B.Qh h (P.f x) ^ 2 ∂unitμ)
      ≤ Real.sqrt (K * h ^ 4) := Real.sqrt_le_sqrt hA
  have h3 : (∫ x in centralSet d ρ P.f, B.Qh h (P.f x) ^ 2 ∂unitμ) ^ (3 / 16 : ℝ)
      ≤ (K * h ^ 4) ^ (3 / 16 : ℝ) := Real.rpow_le_rpow hA0 hA (by norm_num)
  have h4 : (1 + Real.log (1 / h))
        * (tailMass d ρ P.f + |(∫ x, P.f x ^ d ∂unitμ) - B.qVal h|
          + (∫ x in centralSet d ρ P.f, B.Qh h (P.f x) ^ 2 ∂unitμ) ^ (3 / 16 : ℝ))
      ≤ (1 + Real.log (1 / h)) * (2 * (K * h ^ 4) + (K * h ^ 4) ^ (3 / 16 : ℝ)) :=
    mul_le_mul_of_nonneg_left (by linarith) hLh
  rw [comparisonMasterErr, comparisonMasterMaj]
  linarith

/-- **`eq:graphon-lagrangian-bound`**, in the layer's
graph-free form.

For each `K ≥ 1` there are a window radius `ρ > 0`, a constant `M ≥ 1` and a threshold
`δ₀ > 0` such that, for every `0 < h < δ₀` inside the family window, every graphon `W` and
every nonlinear Factor decomposition `W = f ⊗ f + E` satisfying
`eq:graphon-comparison-estimates`,

`I_{p_h}(W) - I_{p_h}(W_h) ≥ η_hΔ + M⁻¹{‖E‖₂² + A_ρ + ε} - MΔ²`.

Comparing with the paper's display: its `C_{d,ρ}^{-1}[A_{h,ρ}(ν) + ν(𝒯_ρ) + ‖E‖₂²]` and
`-C_{d,m}Δ_h(ν)²` appear here as `M⁻¹{‖E‖₂² + A_ρ + ε}` (closed window) and `-MΔ²`, and the
Lagrangian term is the layer's graph-free `η_hΔ_h(ν)` where the paper writes
`μ_h{t(H,W) - r_h^m}`.  The paper reconciles the two using the display following
`eq:first-variation` and the homomorphism-density bound of `eq:rank-one-reduction-bounds`; that
reconciliation is not part of this theorem, and is `muVal_tDensity_le_etaVal`
(`SingularEndpoint/AuxiliaryLagrangian/LagrangeBridge.lean`), used in `exists_singular_endpoint_comparison_graph` below.

This is `exists_comparison_premaster` with the bracket multiplying `ε` made positive:
`ζ(h) ≤ c/4` is `KKTFamily.exists_zeta_le`, `C_err·𝔈 ≤ c/4` is
`comparisonMaster_err_le_maj` fed into `comparisonMaster_exists_maj_le`.  The constant is
`M⁻¹ = min(a, c/2)`. -/
theorem exists_comparison_master (hd : 2 ≤ d) (B : KKTFamily d) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ K : ℝ, 1 ≤ K → ∃ M : ℝ, 0 < M ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧
      ∀ (h : ℝ) (hb : |h| < B.h₀), 0 < h → h < δ₀ → h ≤ 1 →
      ∀ (W : Graphon) (P : FactorDecomp d W),
        tailMass d ρ P.f ≤ K * h ^ 4 →
        |(∫ x, P.f x ^ d ∂unitμ) - B.qVal h| ≤ K * h ^ 4 →
        (∫ x in centralSet d ρ P.f, B.Qh h (P.f x) ^ 2 ∂unitμ) ≤ K * h ^ 4 →
        P.residL2 ≤ K * h ^ 2 →
        (∫ x, (P.f x - uStar d) ^ 4 ∂unitμ) ≤ K * h ^ 4 →
          B.etaVal h * ((∫ x, P.f x ^ d ∂unitμ) - B.qVal h)
              + M⁻¹ * (P.residSq
                  + (∫ x in centralSet d ρ P.f, B.Qh h (P.f x) ^ 2 ∂unitμ)
                  + tailMass d ρ P.f)
              - M * ((∫ x, P.f x ^ d ∂unitμ) - B.qVal h) ^ 2
            ≤ W.Ip (B.p h) - (B.graphon hb).Ip (B.p h) := by
  obtain ⟨ρ, hρ0, hρ1, hpreall⟩ := exists_comparison_premaster hd B
  refine ⟨ρ, hρ0, ?_⟩
  intro K hK
  obtain ⟨a, ha0, c, hc0, Cz, hCz, MP, hMP, Cerr, hCerr, δ₀, hδ₀, hpre⟩ := hpreall K hK
  have hK0 : (0 : ℝ) ≤ K := by linarith
  obtain ⟨δz, hδz, hzeta⟩ := exists_zeta_le Cz hK0 (b := c / 4) (by linarith)
  obtain ⟨δe, hδe, herr⟩ := comparisonMaster_exists_maj_le hK0 (b := c / 4 / Cerr) (by positivity)
  obtain ⟨Minv, hMinv⟩ : ∃ t : ℝ, t = min a (c / 2) := ⟨_, rfl⟩
  have hMinv0 : 0 < Minv := by rw [hMinv]; exact lt_min ha0 (by linarith)
  have hMinva : Minv ≤ a := by rw [hMinv]; exact min_le_left _ _
  have hMinvc : Minv ≤ c / 2 := by rw [hMinv]; exact min_le_right _ _
  refine ⟨max MP Minv⁻¹, lt_of_lt_of_le hMP (le_max_left _ _),
    min (min δ₀ δz) δe, lt_min (lt_min hδ₀ hδz) hδe, ?_⟩
  intro h hhb hh0 hhδ hh1 W P htail hmom hA hL hquart
  have hh₀ : h < δ₀ := lt_of_lt_of_le hhδ (le_trans (min_le_left _ _) (min_le_left _ _))
  have hhz : h < δz := lt_of_lt_of_le hhδ (le_trans (min_le_left _ _) (min_le_right _ _))
  have hhe : h < δe := lt_of_lt_of_le hhδ (min_le_right _ _)
  have hp := hpre h hhb hh0 hh₀ hh1 W P htail hmom hquart
  -- the bracket multiplying `ε` is at least `c/2`
  have hz := hzeta h hh0 hhz
  have hmaj := comparisonMaster_err_le_maj B hh0 hh1 P htail hmom hA hL
  have hmb := herr h hh0 hhe
  have hCerrE : Cerr * comparisonMasterErr B h ρ P ≤ c / 4 := by
    have h1 : Cerr * comparisonMasterErr B h ρ P ≤ Cerr * comparisonMasterMaj K h :=
      mul_le_mul_of_nonneg_left hmaj hCerr.le
    have h2 : Cerr * comparisonMasterMaj K h ≤ Cerr * (c / 4 / Cerr) :=
      mul_le_mul_of_nonneg_left hmb hCerr.le
    rw [mul_div_cancel₀ _ (ne_of_gt hCerr)] at h2
    linarith
  have hbracket : c / 2 ≤ c - zeta Cz K h - Cerr * comparisonMasterErr B h ρ P := by linarith
  -- nonnegativity
  have hA0 : (0 : ℝ) ≤ ∫ x in centralSet d ρ P.f, B.Qh h (P.f x) ^ 2 ∂unitμ :=
    setIntegral_nonneg (measurableSet_centralSet P.meas_f d ρ) fun x _ => sq_nonneg _
  have hR0 : (0 : ℝ) ≤ P.residSq := P.residSq_nonneg
  have hep0 : (0 : ℝ) ≤ tailMass d ρ P.f := ENNReal.toReal_nonneg
  have hDl0 : (0 : ℝ) ≤ ((∫ x, P.f x ^ d ∂unitμ) - B.qVal h) ^ 2 := sq_nonneg _
  -- `M⁻¹ ≤ Minv` and `M ≥ MP`
  have hMle : (max MP Minv⁻¹)⁻¹ ≤ Minv := by
    have h1 : Minv⁻¹ ≤ max MP Minv⁻¹ := le_max_right _ _
    have h2 : (max MP Minv⁻¹)⁻¹ ≤ (Minv⁻¹)⁻¹ :=
      one_div_le_one_div_of_le (by positivity) h1 |>.trans_eq (by rw [one_div])
        |>.trans_eq' (by rw [one_div])
    rwa [inv_inv] at h2
  have hMinv0' : (0 : ℝ) ≤ (max MP Minv⁻¹)⁻¹ := by positivity
  -- the three comparisons
  have cQ : (max MP Minv⁻¹)⁻¹
        * ((∫ x in centralSet d ρ P.f, B.Qh h (P.f x) ^ 2 ∂unitμ) + P.residSq)
      ≤ a * ((∫ x in centralSet d ρ P.f, B.Qh h (P.f x) ^ 2 ∂unitμ) + P.residSq) :=
    mul_le_mul_of_nonneg_right (le_trans hMle hMinva) (by linarith)
  have cE : (max MP Minv⁻¹)⁻¹ * tailMass d ρ P.f
      ≤ (c - zeta Cz K h - Cerr * comparisonMasterErr B h ρ P) * tailMass d ρ P.f :=
    mul_le_mul_of_nonneg_right (le_trans (le_trans hMle hMinvc) (by linarith)) hep0
  have cD : MP * ((∫ x, P.f x ^ d ∂unitμ) - B.qVal h) ^ 2
      ≤ max MP Minv⁻¹ * ((∫ x, P.f x ^ d ∂unitμ) - B.qVal h) ^ 2 :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) hDl0
  have hdistr : (max MP Minv⁻¹)⁻¹ * (P.residSq
        + (∫ x in centralSet d ρ P.f, B.Qh h (P.f x) ^ 2 ∂unitμ)
        + tailMass d ρ P.f)
      = (max MP Minv⁻¹)⁻¹
          * ((∫ x in centralSet d ρ P.f, B.Qh h (P.f x) ^ 2 ∂unitμ) + P.residSq)
        + (max MP Minv⁻¹)⁻¹ * tailMass d ρ P.f := by ring
  rw [hdistr]
  linarith only [hp, cQ, cE, cD]

/-! ## The a-priori bound on `A_ρ`

`singular_endpoint_localization` already supplies three of the four a-priori bounds that
`exists_comparison_master` consumes — the tail mass `ε ≤ Mh⁴`, the moment displacement
`|Δ| ≤ Mh⁴` and `‖E‖₂ ≤ Mh²`.  The fourth, `A_ρ ≤ Ch⁴`, follows from
`|Q_h(f)| ≤ (|f - u_*| + Ch)²` pointwise and `‖f - u_*‖₄ = O(h)` (a clause of the paper's
`eq:graphon-comparison-estimates`); the paper's proof does not need it, and it is proved here. -/

/-- `Q_h(x) = (x - u_h)² - h²`: the first-variation quadratic in centred form. -/
theorem Qh_eq_sq_sub (B : KKTFamily d) (h x : ℝ) :
    B.Qh h x = (x - B.u h) ^ 2 - h ^ 2 := by
  show (x - B.sVal h) * (x - B.tVal h) = (x - B.u h) ^ 2 - h ^ 2
  rw [KKTFamily.sVal, KKTFamily.tVal]
  ring

/-- `(p - q)⁴ ≤ 8p⁴ + 8q⁴`. -/
private theorem comparisonMaster_sub_pow_four_le (p q : ℝ) : (p - q) ^ 4 ≤ 8 * p ^ 4 + 8 * q ^ 4 := by
  have h1 : (p - q) ^ 2 ≤ 2 * p ^ 2 + 2 * q ^ 2 := by nlinarith [sq_nonneg (p + q)]
  have h2 : (0 : ℝ) ≤ (p - q) ^ 2 := sq_nonneg _
  have h3 : ((p - q) ^ 2) ^ 2 ≤ (2 * p ^ 2 + 2 * q ^ 2) ^ 2 := by nlinarith
  have h4 : (2 * p ^ 2 + 2 * q ^ 2) ^ 2 ≤ 8 * p ^ 4 + 8 * q ^ 4 := by
    nlinarith [sq_nonneg (p ^ 2 - q ^ 2)]
  calc (p - q) ^ 4 = ((p - q) ^ 2) ^ 2 := by ring
    _ ≤ (2 * p ^ 2 + 2 * q ^ 2) ^ 2 := h3
    _ ≤ 8 * p ^ 4 + 8 * q ^ 4 := h4

/-- The pointwise form: `Q_h(x)² ≤ 16(x - u_*)⁴ + 16(u_h - u_*)⁴ + 2h⁴`. -/
theorem sq_Qh_le (B : KKTFamily d) (h x : ℝ) :
    B.Qh h x ^ 2 ≤ 16 * (x - uStar d) ^ 4 + 16 * (B.u h - uStar d) ^ 4 + 2 * h ^ 4 := by
  rw [Qh_eq_sq_sub]
  have hA : (0 : ℝ) ≤ (x - B.u h) ^ 2 := sq_nonneg _
  have hB : (0 : ℝ) ≤ h ^ 2 := sq_nonneg _
  have h1 : ((x - B.u h) ^ 2 - h ^ 2) ^ 2
      ≤ 2 * ((x - B.u h) ^ 2) ^ 2 + 2 * (h ^ 2) ^ 2 := by
    nlinarith [sq_nonneg ((x - B.u h) ^ 2 + h ^ 2)]
  have h2 : ((x - B.u h) ^ 2) ^ 2 = (x - B.u h) ^ 4 := by ring
  have h3 : (x - B.u h) ^ 4 ≤ 8 * (x - uStar d) ^ 4 + 8 * (B.u h - uStar d) ^ 4 := by
    have he : x - B.u h = (x - uStar d) - (B.u h - uStar d) := by ring
    rw [he]
    exact comparisonMaster_sub_pow_four_le _ _
  have h4 : (h ^ 2) ^ 2 = h ^ 4 := by ring
  linarith

/-- `|a| ≤ 3 → a⁴ ≤ 81`, hoisted so the two call sites do not carry the ambient context. -/
private theorem comparisonMaster_pow_four_le_of_abs_le {a : ℝ} (h : |a| ≤ 3) : a ^ 4 ≤ 81 := by
  have hb := abs_le.mp h
  have h2 : a ^ 2 ≤ 9 := by nlinarith [hb.1, hb.2]
  have h0 : (0 : ℝ) ≤ a ^ 2 := sq_nonneg _
  calc a ^ 4 = (a ^ 2) ^ 2 := by ring
    _ ≤ 9 ^ 2 := by nlinarith
    _ = 81 := by norm_num

/-- **`A_ρ` is controlled by `‖f - u_*‖₄`, the family drift and `h`**:

`A_ρ = ∫_{G_ρ}Q_h(f)² ≤ 16‖f - u_*‖₄⁴ + 16(u_h - u_*)⁴ + 2h⁴`.

The integral over `G_ρ` is at most the integral over all of `[0,1]` because the integrand is
nonnegative, and `sq_Qh_le` is applied under it.  Along the family `‖f - u_*‖₄ = O(h)`
(`eq:rank-one-reduction-bounds` fed by `family_localization`) and `(u_h - u_*)/h → 0`
(`KKTFamily.tendsto_u_slope`), so the right-hand side is `O(h⁴)`, the bound on `A_ρ` that
`exists_comparison_master` consumes. -/
theorem family_Ah_le (hd : 2 ≤ d) (B : KKTFamily d) (h : ℝ) {f : ℝ → ℝ}
    (hf : Measurable f) (hnn : ∀ x, 0 ≤ f x) (hbd : ∀ x, f x ≤ 2) (ρ : ℝ) {c : ℝ}
    (_hc : 0 ≤ c) (hclose : Lnorm unitμ 4 (fun x => f x - uStar d) ≤ c) :
    (∫ x in centralSet d ρ f, B.Qh h (f x) ^ 2 ∂unitμ)
      ≤ 16 * c ^ 4 + 16 * (B.u h - uStar d) ^ 4 + 2 * h ^ 4 := by
  have hGm : MeasurableSet (centralSet d ρ f) := measurableSet_centralSet hf d ρ
  have hfb : ∀ x, |f x - uStar d| ≤ 3 := by
    intro x
    have h1 : (0 : ℝ) ≤ uStar d := uStar_nonneg hd
    have h2 : uStar d ≤ 1 := (uStar_lt_one hd).le
    rw [abs_le]
    exact ⟨by linarith [hnn x], by linarith [hbd x]⟩
  have hmQ : Measurable fun x : ℝ => B.Qh h (f x) ^ 2 :=
    (((measurable_id.sub measurable_const).mul
      (measurable_id.sub measurable_const)).comp hf).pow_const 2
  have hmR : Measurable fun x : ℝ =>
      16 * (f x - uStar d) ^ 4 + 16 * (B.u h - uStar d) ^ 4 + 2 * h ^ 4 :=
    ((((hf.sub measurable_const).pow_const 4).const_mul _).add measurable_const).add
      measurable_const
  have hRb : ∀ x : ℝ, |16 * (f x - uStar d) ^ 4 + 16 * (B.u h - uStar d) ^ 4 + 2 * h ^ 4|
      ≤ 16 * 81 + 16 * (B.u h - uStar d) ^ 4 + 2 * h ^ 4 := by
    intro x
    have h1 : (f x - uStar d) ^ 4 ≤ 81 := comparisonMaster_pow_four_le_of_abs_le (hfb x)
    rw [abs_of_nonneg (by positivity)]
    linarith
  have hRi : Integrable (fun x : ℝ =>
      16 * (f x - uStar d) ^ 4 + 16 * (B.u h - uStar d) ^ 4 + 2 * h ^ 4) unitμ :=
    Integrable.of_bound hmR.aestronglyMeasurable _
      (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hRb x)
  have hQi : Integrable (fun x : ℝ => B.Qh h (f x) ^ 2) unitμ := by
    refine Integrable.mono hRi hmQ.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact le_trans (sq_Qh_le B h (f x)) (le_trans (le_abs_self _) (le_refl _))
  -- pass from `G_ρ` to `[0,1]`, then apply the pointwise bound
  have hstep1 : (∫ x in centralSet d ρ f, B.Qh h (f x) ^ 2 ∂unitμ)
      ≤ ∫ x, B.Qh h (f x) ^ 2 ∂unitμ :=
    setIntegral_le_integral hQi (Filter.Eventually.of_forall fun x => sq_nonneg _)
  have hstep2 : (∫ x, B.Qh h (f x) ^ 2 ∂unitμ)
      ≤ ∫ x, (16 * (f x - uStar d) ^ 4 + 16 * (B.u h - uStar d) ^ 4 + 2 * h ^ 4) ∂unitμ :=
    integral_mono hQi hRi fun x => sq_Qh_le B h (f x)
  -- evaluate the majorant
  have hFi : Integrable (fun x : ℝ => (f x - uStar d) ^ 4) unitμ :=
    Integrable.of_bound ((hf.sub measurable_const).pow_const 4).aestronglyMeasurable 81
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact comparisonMaster_pow_four_le_of_abs_le (hfb x))
  have hci : Integrable (fun _ : ℝ => 16 * (B.u h - uStar d) ^ 4 + 2 * h ^ 4) unitμ :=
    Integrable.of_bound measurable_const.aestronglyMeasurable
      |16 * (B.u h - uStar d) ^ 4 + 2 * h ^ 4|
      (Filter.Eventually.of_forall fun _ => by simp [Real.norm_eq_abs])
  have hstep3 : (∫ x, (16 * (f x - uStar d) ^ 4 + 16 * (B.u h - uStar d) ^ 4 + 2 * h ^ 4) ∂unitμ)
      = 16 * (∫ x, (f x - uStar d) ^ 4 ∂unitμ)
        + (16 * (B.u h - uStar d) ^ 4 + 2 * h ^ 4) := by
    have he : ∀ x : ℝ, 16 * (f x - uStar d) ^ 4 + 16 * (B.u h - uStar d) ^ 4 + 2 * h ^ 4
        = 16 * (f x - uStar d) ^ 4 + (16 * (B.u h - uStar d) ^ 4 + 2 * h ^ 4) :=
      fun x => by ring
    rw [integral_congr_ae (Filter.Eventually.of_forall he),
      integral_add (hFi.const_mul 16) hci, integral_const_mul, integral_const]
    simp [measureReal_def]
  -- `∫(f - u_*)⁴ = ‖f - u_*‖₄⁴ ≤ c⁴`
  have hLn : (∫ x, (f x - uStar d) ^ 4 ∂unitμ) ≤ c ^ 4 := by
    have hpow := Lnorm_rpow (μ := unitμ) (p := 4) (by norm_num) (fun x => f x - uStar d)
    have hcast : ∀ x : ℝ, |f x - uStar d| ^ (4 : ℝ) = (f x - uStar d) ^ 4 := by
      intro x
      rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, ← abs_pow,
        abs_of_nonneg (by positivity)]
    rw [integral_congr_ae (Filter.Eventually.of_forall hcast)] at hpow
    have hnat : Lnorm unitμ 4 (fun x => f x - uStar d) ^ (4 : ℝ)
        = Lnorm unitμ 4 (fun x => f x - uStar d) ^ (4 : ℕ) := by
      rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [hnat] at hpow
    rw [← hpow]
    exact pow_le_pow_left₀ (Lnorm_nonneg _ _ _) hclose 4
  linarith

/-! ## Localization feeds the master estimate

`exists_comparison_master` quantifies over Factor decompositions satisfying
`eq:graphon-comparison-estimates`.  `singular_endpoint_localization` produces one for every near-optimal
feasible competitor, together with three of the four clauses; `family_Ah_le` supplies the
fourth.  Composing them removes the hypothesis. -/

/-- `|u_h - u_*| ≤ h` for small `h`, from `(u_h - u_*)/h → 0`
(`KKTFamily.tendsto_u_slope`, which holds because `u` is even and analytic). -/
theorem exists_abs_u_sub_le (B : KKTFamily d) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 < h → h < δ → |B.u h - uStar d| ≤ h := by
  obtain ⟨δ, hδ, hprop⟩ :=
    Metric.tendsto_nhdsWithin_nhds.mp (tendsto_u_slope B) 1 one_pos
  refine ⟨δ, hδ, fun h hh0 hhδ => ?_⟩
  have hmem : h ∈ ({(0 : ℝ)}ᶜ : Set ℝ) := ne_of_gt hh0
  have hdist : dist h (0 : ℝ) < δ := by rw [Real.dist_eq, sub_zero, abs_of_pos hh0]; exact hhδ
  have hval := hprop hmem hdist
  have h1 : |(B.u h - uStar d) / h| < 1 := by
    have := hval
    rwa [Real.dist_eq, sub_zero] at this
  have h2 : |B.u h - uStar d| / h < 1 := by
    rwa [abs_div, abs_of_pos hh0] at h1
  have h3 : |B.u h - uStar d| < h := by rwa [div_lt_one hh0] at h2
  exact h3.le

/-- **`eq:graphon-lagrangian-bound` for an actual competitor.**

There are a window radius `ρ > 0`, a constant `M > 0` and a threshold `δ > 0` such that, for
every `0 < h < δ` inside the family window, every graphon `W` that is feasible
(`t(H,W) ≥ r_h^m`) and no more costly than `W_h` carries a nonlinear Factor decomposition
`W = f ⊗ f + E` with

`I_{p_h}(W) - I_{p_h}(W_h) ≥ η_hΔ + M⁻¹{‖E‖₂² + A_ρ + ε} - MΔ²`.

The decomposition and three of the four a-priori clauses are `singular_endpoint_localization`; the
fourth, `A_ρ ≤ Kh⁴`, is `family_Ah_le` fed the exported `‖f - u_*‖₄ ≤ M_loc h` and
`|u_h - u_*| ≤ h` (`exists_abs_u_sub_le`).

The radius has to be quantified before the a-priori constant `K`, and it is: the law
window `exists_distribution_window_forall` sees no `K`.  Otherwise this composition would be
circular, `K` having to dominate a localization constant that itself depends on `ρ`. -/
theorem exists_singular_endpoint_comparison (hd : 2 ≤ d) {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (hreg : ∀ v, H.degree v = d)
    (hcard : 1 ≤ H.edgeFinset.card) (B : KKTFamily d) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ M : ℝ, 0 < M ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ (h : ℝ) (hh : |h| < B.h₀), 0 < h → h < δ → h ≤ 1 →
        ∀ W : Graphon, B.rVal h ^ H.edgeFinset.card ≤ W.tDensity H →
          W.Ip (B.p h) ≤ (B.graphon hh).Ip (B.p h) →
          ∃ P : FactorDecomp d W, P.residL2 ≤ M * h ^ 2 ∧
            |P.qVal - B.qVal h| ≤ M * h ^ 4 ∧
            B.etaVal h * (P.qVal - B.qVal h)
                + M⁻¹ * (P.residSq
                    + (∫ x in centralSet d ρ P.f, B.Qh h (P.f x) ^ 2 ∂unitμ)
                    + tailMass d ρ P.f)
                - M * (P.qVal - B.qVal h) ^ 2
              ≤ W.Ip (B.p h) - (B.graphon hh).Ip (B.p h) := by
  obtain ⟨ρ, hρ0, hmasterall⟩ := exists_comparison_master hd B
  obtain ⟨Mloc, hMloc, δloc, hδloc, hloc⟩ := singular_endpoint_localization hd H hreg hcard B hρ0
  obtain ⟨δu, hδu, hu⟩ := exists_abs_u_sub_le B
  -- the a-priori constant
  obtain ⟨K, hKdef⟩ : ∃ t : ℝ, t = 1 + Mloc + (16 * Mloc ^ 4 + 18) := ⟨_, rfl⟩
  have hK1 : 1 ≤ K := by rw [hKdef]; nlinarith [hMloc, pow_pos hMloc 4]
  have hKloc : Mloc ≤ K := by rw [hKdef]; nlinarith [hMloc, pow_pos hMloc 4]
  have hKA : 16 * Mloc ^ 4 + 18 ≤ K := by rw [hKdef]; linarith
  obtain ⟨Mm, hMm, δm, hδm, hmaster⟩ := hmasterall K hK1
  refine ⟨ρ, hρ0, max Mm K, lt_of_lt_of_le hMm (le_max_left _ _),
    min (min δloc δu) δm, lt_min (lt_min hδloc hδu) hδm, ?_⟩
  intro h hhb hh0 hhδ hh1 W hfeas hcost
  have hhl : h < δloc := lt_of_lt_of_le hhδ (le_trans (min_le_left _ _) (min_le_left _ _))
  have hhu : h < δu := lt_of_lt_of_le hhδ (le_trans (min_le_left _ _) (min_le_right _ _))
  have hhm : h < δm := lt_of_lt_of_le hhδ (min_le_right _ _)
  obtain ⟨-, -, P, hres, hmom, htail, hclose⟩ := hloc h hhb hh0 hhl W hfeas hcost
  -- the four a-priori clauses at the constant `K`
  have hh4 : (0 : ℝ) ≤ h ^ 4 := by positivity
  have hh2 : (0 : ℝ) ≤ h ^ 2 := by positivity
  have htail' : tailMass d ρ P.f ≤ K * h ^ 4 :=
    le_trans htail (mul_le_mul_of_nonneg_right hKloc hh4)
  have hmom' : |(∫ x, P.f x ^ d ∂unitμ) - B.qVal h| ≤ K * h ^ 4 :=
    le_trans hmom (mul_le_mul_of_nonneg_right hKloc hh4)
  have hres' : P.residL2 ≤ K * h ^ 2 := by
    rw [FactorDecomp.residL2_eq_residNorm]
    exact le_trans hres (mul_le_mul_of_nonneg_right hKloc hh2)
  have hA : (∫ x in centralSet d ρ P.f, B.Qh h (P.f x) ^ 2 ∂unitμ) ≤ K * h ^ 4 := by
    have hAw := family_Ah_le hd B h P.meas_f P.f_nonneg P.f_bdd ρ
      (by positivity : (0 : ℝ) ≤ Mloc * h) hclose
    have hu4 : (B.u h - uStar d) ^ 4 ≤ h ^ 4 := by
      have hb := hu h hh0 hhu
      have h0 : (0 : ℝ) ≤ |B.u h - uStar d| := abs_nonneg _
      calc (B.u h - uStar d) ^ 4 = |B.u h - uStar d| ^ 4 := by
            rw [← abs_pow, abs_of_nonneg (by positivity)]
        _ ≤ h ^ 4 := pow_le_pow_left₀ h0 hb 4
    have hMh : (Mloc * h) ^ 4 = Mloc ^ 4 * h ^ 4 := by ring
    have hstep : 16 * (Mloc * h) ^ 4 + 16 * (B.u h - uStar d) ^ 4 + 2 * h ^ 4
        ≤ (16 * Mloc ^ 4 + 18) * h ^ 4 := by rw [hMh]; nlinarith [hu4, hh4]
    have hfin : (16 * Mloc ^ 4 + 18) * h ^ 4 ≤ K * h ^ 4 :=
      mul_le_mul_of_nonneg_right hKA hh4
    linarith
  have hquart' : (∫ x, (P.f x - uStar d) ^ 4 ∂unitμ) ≤ K * h ^ 4 := by
    have h1 := integral_pow_four_le_of_Lnorm hclose
    have h2 : (Mloc * h) ^ 4 = Mloc ^ 4 * h ^ 4 := by ring
    have h3 : Mloc ^ 4 * h ^ 4 ≤ K * h ^ 4 :=
      mul_le_mul_of_nonneg_right (by nlinarith [hKA, pow_pos hMloc 4]) hh4
    rw [h2] at h1
    linarith
  refine ⟨P, ?_, ?_, ?_⟩
  · exact le_trans hres' (mul_le_mul_of_nonneg_right (le_max_right _ _) hh2)
  · exact le_trans hmom' (mul_le_mul_of_nonneg_right (le_max_right _ _) hh4)
  · have hmain := hmaster h hhb hh0 hhm hh1 W P htail' hmom' hA hres' hquart'
    have hqdef : P.qVal = ∫ x, P.f x ^ d ∂unitμ := rfl
    rw [hqdef]
    have hMle : (max Mm K)⁻¹ ≤ Mm⁻¹ := by
      have h1 : Mm ≤ max Mm K := le_max_left _ _
      have h2 : (max Mm K)⁻¹ ≤ Mm⁻¹ :=
        one_div_le_one_div_of_le hMm h1 |>.trans_eq (by rw [one_div])
          |>.trans_eq' (by rw [one_div])
      exact h2
    have hAnn : (0 : ℝ) ≤ ∫ x in centralSet d ρ P.f, B.Qh h (P.f x) ^ 2 ∂unitμ :=
      setIntegral_nonneg (measurableSet_centralSet P.meas_f d ρ) fun x _ => sq_nonneg _
    have hnn : (0 : ℝ) ≤ P.residSq
        + (∫ x in centralSet d ρ P.f, B.Qh h (P.f x) ^ 2 ∂unitμ)
        + tailMass d ρ P.f := by
      have h1 : (0 : ℝ) ≤ P.residSq := P.residSq_nonneg
      have h2 : (0 : ℝ) ≤ tailMass d ρ P.f := ENNReal.toReal_nonneg
      linarith
    have c1 : (max Mm K)⁻¹ * (P.residSq
          + (∫ x in centralSet d ρ P.f, B.Qh h (P.f x) ^ 2 ∂unitμ)
          + tailMass d ρ P.f)
        ≤ Mm⁻¹ * (P.residSq
          + (∫ x in centralSet d ρ P.f, B.Qh h (P.f x) ^ 2 ∂unitμ)
          + tailMass d ρ P.f) := mul_le_mul_of_nonneg_right hMle hnn
    have c2 : Mm * ((∫ x, P.f x ^ d ∂unitμ) - B.qVal h) ^ 2
        ≤ max Mm K * ((∫ x, P.f x ^ d ∂unitμ) - B.qVal h) ^ 2 :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)
    linarith [hmain, c1, c2]

/-! ## The master estimate with the graph-carrying Lagrangian -/

/-- **`|μ_h| ≤ C` for small `h`.**  `μ_h = γ_h/(m q_h^{v-2})` with `v - 2 ≥ 0` when `m ≥ d`
(equivalently `n ≥ 2`), so `q_h^{v-2} ≥ c^{v-2}` once `q_h ≥ c > 0`
(`centralSet_exists_qVal_lower`), and `|γ_h| ≤ Γ` (`centralSet_exists_gam_bound`). -/
theorem exists_abs_muVal_le (hd : 2 ≤ d) (B : KKTFamily d) {m : ℝ} (hm : 0 < m)
    (hmd : (d : ℝ) ≤ m) :
    ∃ C : ℝ, 0 < C ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, |h| < δ → |h| < B.h₀ →
      |B.muVal m h| ≤ C := by
  have hd0 : (0 : ℝ) < (d : ℝ) := dpos hd
  obtain ⟨Γ, hΓ0, δg, hδg0, hgam⟩ := centralSet_exists_gam_bound B
  obtain ⟨c, hc0, δq, hδq0, hqlow⟩ := centralSet_exists_qVal_lower hd B
  have he0 : (0 : ℝ) ≤ 2 * m / (d : ℝ) - 2 := by
    rw [sub_nonneg, le_div_iff₀ hd0]
    linarith
  have hce : (0 : ℝ) < c ^ (2 * m / (d : ℝ) - 2) := Real.rpow_pos_of_pos hc0 _
  have hden : (0 : ℝ) < m * c ^ (2 * m / (d : ℝ) - 2) := mul_pos hm hce
  refine ⟨Γ / (m * c ^ (2 * m / (d : ℝ) - 2)) + 1,
    by have h0 : (0 : ℝ) ≤ Γ / (m * c ^ (2 * m / (d : ℝ) - 2)) := div_nonneg hΓ0 hden.le
       linarith,
    min δg δq, lt_min hδg0 hδq0, ?_⟩
  intro h hhδ hhb
  have hhg : |h| < δg := lt_of_lt_of_le hhδ (min_le_left _ _)
  have hhq : |h| < δq := lt_of_lt_of_le hhδ (min_le_right _ _)
  have hq := hqlow h hhq
  have hqpos := KKTFamily.qVal_pos hhb
  have hqe : c ^ (2 * m / (d : ℝ) - 2) ≤ B.qVal h ^ (2 * m / (d : ℝ) - 2) :=
    Real.rpow_le_rpow hc0.le hq he0
  have hqepos : (0 : ℝ) < B.qVal h ^ (2 * m / (d : ℝ) - 2) := Real.rpow_pos_of_pos hqpos _
  have habs : |B.muVal m h| = |B.gam h| / (m * B.qVal h ^ (2 * m / (d : ℝ) - 2)) := by
    rw [KKTFamily.muVal, abs_div, abs_of_pos (mul_pos hm hqepos)]
  rw [habs]
  have hstep : |B.gam h| / (m * B.qVal h ^ (2 * m / (d : ℝ) - 2))
      ≤ Γ / (m * c ^ (2 * m / (d : ℝ) - 2)) := by
    refine div_le_div₀ hΓ0 (hgam h hhg) (by positivity) ?_
    exact mul_le_mul_of_nonneg_left hqe hm.le
  linarith

/-- **`eq:graphon-lagrangian-bound` with the graph-carrying Lagrangian.**

For every `0 < h < δ` inside the family window, every graphon `W` that is feasible and no more
costly than `W_h` carries a nonlinear Factor decomposition `W = f ⊗ f + E` with

`I_{p_h}(W) - I_{p_h}(W_h) ≥ μ_h{t(H,W) - r_h^m} + M⁻¹{‖E‖₂² + A_ρ + ε} - MΔ²`.

This is `exists_singular_endpoint_comparison` with `muVal_tDensity_le_etaVal` substituted for the
graph-free Lagrangian.  The `O(Δ²)` it costs is absorbed into the retained `MΔ²`; the
`|μ_h|40^m‖E‖₂³` is absorbed into the retained `M⁻¹‖E‖₂²`, because `‖E‖₂³ = ‖E‖₂·‖E‖₂²` and
`‖E‖₂ ≤ M₀h²`, so the threshold is decreased once more to make `C_μ40^mM₀h² ≤ M₀⁻¹/2`.

This is the form `terminal_optimality_of_master` (`SingularEndpoint/Proof/Terminal.lean`) consumes. -/
theorem exists_singular_endpoint_comparison_graph (hd : 2 ≤ d) {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (hreg : ∀ v, H.degree v = d)
    (hcard : 1 ≤ H.edgeFinset.card) (hv : 2 ≤ Fintype.card V) (B : KKTFamily d) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ M : ℝ, 0 < M ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ (h : ℝ) (hh : |h| < B.h₀), 0 < h → h < δ → h ≤ 1 →
        ∀ W : Graphon, B.rVal h ^ H.edgeFinset.card ≤ W.tDensity H →
          W.Ip (B.p h) ≤ (B.graphon hh).Ip (B.p h) →
          ∃ P : FactorDecomp d W, |P.qVal - B.qVal h| ≤ M * h ^ 4 ∧
            B.muVal (H.edgeFinset.card : ℝ) h
                  * (W.tDensity H - B.rVal h ^ H.edgeFinset.card)
              + M⁻¹ * (P.residSq
                  + (∫ x in centralSet d ρ P.f, B.Qh h (P.f x) ^ 2 ∂unitμ)
                  + tailMass d ρ P.f)
              - M * (P.qVal - B.qVal h) ^ 2
            ≤ W.Ip (B.p h) - (B.graphon hh).Ip (B.p h) := by
  have hd0 : (0 : ℝ) < (d : ℝ) := dpos hd
  have hmpos : (0 : ℝ) < (H.edgeFinset.card : ℝ) := by exact_mod_cast hcard
  have hnR : 2 * (H.edgeFinset.card : ℝ) = (Fintype.card V : ℝ) * (d : ℝ) := by
    have := factorMain_two_mul_card_edgeFinset H hreg
    exact_mod_cast congrArg (fun k : ℕ => (k : ℝ)) this
  have hvR : (2 : ℝ) ≤ (Fintype.card V : ℝ) := by exact_mod_cast hv
  have hmd : (d : ℝ) ≤ (H.edgeFinset.card : ℝ) := by nlinarith [hnR, hvR, hd0]
  obtain ⟨ρ, hρ0, M₀, hM₀, δ₀, hδ₀, hmod⟩ := exists_singular_endpoint_comparison hd H hreg hcard B
  obtain ⟨Cμ, hCμ, δμ, hδμ, hmu⟩ := exists_abs_muVal_le hd B hmpos hmd
  -- the threshold that makes the cubic residual fit inside the quadratic one
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = 1 / (2 * M₀ ^ 2 * Cμ * (40 : ℝ) ^ H.edgeFinset.card) :=
    ⟨_, rfl⟩
  have ht0 : 0 < t := by rw [ht]; positivity
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ,
      Q = Cμ * ((Fintype.card V : ℝ) ^ 2 * (2 ^ d : ℝ) ^ (2 * Fintype.card V)) := ⟨_, rfl⟩
  have hQ0 : 0 ≤ Q := by rw [hQ]; positivity
  refine ⟨ρ, hρ0, max (2 * M₀) (M₀ + Q), lt_of_lt_of_le (by linarith) (le_max_left _ _),
    min (min δ₀ δμ) (Real.sqrt t), lt_min (lt_min hδ₀ hδμ) (Real.sqrt_pos.mpr ht0), ?_⟩
  intro h hhb hh0 hhδ hh1 W hfeas hcost
  have hh₀ : h < δ₀ := lt_of_lt_of_le hhδ (le_trans (min_le_left _ _) (min_le_left _ _))
  have hhμ : |h| < δμ := by
    rw [abs_of_pos hh0]
    exact lt_of_lt_of_le hhδ (le_trans (min_le_left _ _) (min_le_right _ _))
  have hht : h < Real.sqrt t := lt_of_lt_of_le hhδ (min_le_right _ _)
  have hh2t : h ^ 2 ≤ t := by
    have hs0 : (0 : ℝ) ≤ Real.sqrt t := Real.sqrt_nonneg t
    have h1 : h ^ 2 ≤ Real.sqrt t ^ 2 := by nlinarith [hh0.le, hht.le, hs0]
    rwa [Real.sq_sqrt ht0.le] at h1
  obtain ⟨P, hres, hmom, hmain⟩ := hmod h hhb hh0 hh₀ hh1 W hfeas hcost
  refine ⟨P, ?_, ?_⟩
  · refine le_trans hmom (mul_le_mul_of_nonneg_right ?_ (by positivity))
    have h1 : M₀ ≤ 2 * M₀ := by linarith
    exact le_trans h1 (le_max_left _ _)
  -- the Lagrangian conversion
  have hlag := muVal_tDensity_le_etaVal hd H hreg hv hcard B hhb P
  have hmub := hmu h hhμ hhb
  have hR0 : (0 : ℝ) ≤ P.residSq := P.residSq_nonneg
  have hL0 : (0 : ℝ) ≤ P.residL2 := P.residL2_nonneg
  have hΔ0 : (0 : ℝ) ≤ (P.qVal - B.qVal h) ^ 2 := sq_nonneg _
  have hA0 : (0 : ℝ) ≤ ∫ x in centralSet d ρ P.f, B.Qh h (P.f x) ^ 2 ∂unitμ :=
    setIntegral_nonneg (measurableSet_centralSet P.meas_f d ρ) fun x _ => sq_nonneg _
  have hep0 : (0 : ℝ) ≤ tailMass d ρ P.f := ENNReal.toReal_nonneg
  -- `|μ_h|·{…} ≤ C_μ·{…}`
  have herrnn : (0 : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 * (2 ^ d : ℝ) ^ (2 * Fintype.card V)
        * (P.qVal - B.qVal h) ^ 2 + (40 : ℝ) ^ H.edgeFinset.card * P.residL2 ^ 3 := by
    have h1 : (0 : ℝ) ≤ P.residL2 ^ 3 := by positivity
    have h2 : (0 : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 * (2 ^ d : ℝ) ^ (2 * Fintype.card V)
        * (P.qVal - B.qVal h) ^ 2 := by positivity
    have h3 : (0 : ℝ) ≤ (40 : ℝ) ^ H.edgeFinset.card * P.residL2 ^ 3 := by positivity
    linarith
  have hlag' : B.muVal (H.edgeFinset.card : ℝ) h
        * (W.tDensity H - B.rVal h ^ H.edgeFinset.card)
      ≤ B.etaVal h * (P.qVal - B.qVal h)
        + Cμ * ((Fintype.card V : ℝ) ^ 2 * (2 ^ d : ℝ) ^ (2 * Fintype.card V)
            * (P.qVal - B.qVal h) ^ 2
          + (40 : ℝ) ^ H.edgeFinset.card * P.residL2 ^ 3) := by
    have := mul_le_mul_of_nonneg_right hmub herrnn
    linarith [hlag]
  -- the cubic residual fits inside the quadratic one
  have hcube : P.residL2 ^ 3 = P.residL2 * P.residSq := by
    rw [← P.residL2_sq]; ring
  have hLh : P.residL2 * P.residSq ≤ M₀ * h ^ 2 * P.residSq :=
    mul_le_mul_of_nonneg_right hres hR0
  have hcoef : Cμ * (40 : ℝ) ^ H.edgeFinset.card * (M₀ * h ^ 2) ≤ M₀⁻¹ / 2 := by
    have h1 : Cμ * (40 : ℝ) ^ H.edgeFinset.card * (M₀ * h ^ 2)
        ≤ Cμ * (40 : ℝ) ^ H.edgeFinset.card * (M₀ * t) := by
      have : M₀ * h ^ 2 ≤ M₀ * t := mul_le_mul_of_nonneg_left hh2t hM₀.le
      exact mul_le_mul_of_nonneg_left this (by positivity)
    have h2 : Cμ * (40 : ℝ) ^ H.edgeFinset.card * (M₀ * t) = M₀⁻¹ / 2 := by
      rw [ht]
      field_simp
    linarith
  have hcubefit : Cμ * ((40 : ℝ) ^ H.edgeFinset.card * P.residL2 ^ 3)
      ≤ M₀⁻¹ / 2 * P.residSq := by
    rw [hcube]
    have h1 : Cμ * ((40 : ℝ) ^ H.edgeFinset.card * (P.residL2 * P.residSq))
        ≤ Cμ * ((40 : ℝ) ^ H.edgeFinset.card * (M₀ * h ^ 2 * P.residSq)) := by
      refine mul_le_mul_of_nonneg_left ?_ hCμ.le
      exact mul_le_mul_of_nonneg_left hLh (by positivity)
    have h2 : Cμ * ((40 : ℝ) ^ H.edgeFinset.card * (M₀ * h ^ 2 * P.residSq))
        = (Cμ * (40 : ℝ) ^ H.edgeFinset.card * (M₀ * h ^ 2)) * P.residSq := by ring
    have h3 : (Cμ * (40 : ℝ) ^ H.edgeFinset.card * (M₀ * h ^ 2)) * P.residSq
        ≤ M₀⁻¹ / 2 * P.residSq := mul_le_mul_of_nonneg_right hcoef hR0
    linarith
  -- the constants
  have hMle : (max (2 * M₀) (M₀ + Q))⁻¹ ≤ M₀⁻¹ / 2 := by
    have h1 : 2 * M₀ ≤ max (2 * M₀) (M₀ + Q) := le_max_left _ _
    have h2 : (max (2 * M₀) (M₀ + Q))⁻¹ ≤ (2 * M₀)⁻¹ :=
      one_div_le_one_div_of_le (by linarith) h1 |>.trans_eq (by rw [one_div])
        |>.trans_eq' (by rw [one_div])
    have h3 : (2 * M₀)⁻¹ = M₀⁻¹ / 2 := by field_simp
    linarith
  have hMge : M₀ + Q ≤ max (2 * M₀) (M₀ + Q) := le_max_right _ _
  have cQ : (max (2 * M₀) (M₀ + Q))⁻¹ * (P.residSq
        + (∫ x in centralSet d ρ P.f, B.Qh h (P.f x) ^ 2 ∂unitμ)
        + tailMass d ρ P.f)
      ≤ M₀⁻¹ / 2 * (P.residSq
        + (∫ x in centralSet d ρ P.f, B.Qh h (P.f x) ^ 2 ∂unitμ)
        + tailMass d ρ P.f) := mul_le_mul_of_nonneg_right hMle (by linarith)
  have cD : (M₀ + Q) * (P.qVal - B.qVal h) ^ 2
      ≤ max (2 * M₀) (M₀ + Q) * (P.qVal - B.qVal h) ^ 2 :=
    mul_le_mul_of_nonneg_right hMge hΔ0
  have hQexp : Cμ * ((Fintype.card V : ℝ) ^ 2 * (2 ^ d : ℝ) ^ (2 * Fintype.card V)
      * (P.qVal - B.qVal h) ^ 2) = Q * (P.qVal - B.qVal h) ^ 2 := by rw [hQ]; ring
  have hhalf : M₀⁻¹ / 2 * (P.residSq
        + (∫ x in centralSet d ρ P.f, B.Qh h (P.f x) ^ 2 ∂unitμ)
        + tailMass d ρ P.f) + M₀⁻¹ / 2 * P.residSq
      ≤ M₀⁻¹ * (P.residSq
        + (∫ x in centralSet d ρ P.f, B.Qh h (P.f x) ^ 2 ∂unitμ)
        + tailMass d ρ P.f) := by
    have hAE : (0 : ℝ) ≤ M₀⁻¹ / 2
        * ((∫ x in centralSet d ρ P.f, B.Qh h (P.f x) ^ 2 ∂unitμ)
          + tailMass d ρ P.f) :=
      mul_nonneg (div_nonneg (inv_nonneg.mpr hM₀.le) (by norm_num)) (by linarith)
    linarith
  have hstep1 : B.muVal (H.edgeFinset.card : ℝ) h
        * (W.tDensity H - B.rVal h ^ H.edgeFinset.card)
      ≤ B.etaVal h * (P.qVal - B.qVal h) + Q * (P.qVal - B.qVal h) ^ 2
        + M₀⁻¹ / 2 * P.residSq := by
    linarith only [hlag', hcubefit, hQexp.ge, hQexp.le]
  linarith only [hmain, hstep1, cQ, cD, hhalf]

end SingularEndpoint

end UpperTailOptimizers
