import UpperTailOptimizers.SingularEndpoint.GraphonComparison.GraphonComparison
import UpperTailOptimizers.SingularEndpoint.LocalizationRankOne.FactorHDensity

/-!
# The central set `Ω_ρ(f)` and the tail mass `|Ω_ρ(f)^c|` (Section 5, `paper/sections/singular.tex`)

Two objects of the proof of `lem:graphon-lagrangian-bound` (`sec:graphon-comparison`), together
with the elementary facts every later step uses.

* `centralSet d ρ f = {y : f(y) ∈ 𝓝_ρ}` is the set of coordinates at which the Factor factor
  lies in the closed coalescence window `𝓝_ρ = [u_* - ρ, u_* + ρ]`: the closed-window
  counterpart of the paper's `Ω_ρ = {x : f(x) ∈ 𝒩_ρ}`, whose window `𝒩_ρ` is open;
* `tailMass d ρ f = |Ω_ρ(f)^c|` is likewise the counterpart of the paper's
  `λ(Ω_ρ^c) = ν(𝒯_ρ)`, the mass that `lem:auxiliary-lagrangian-bound` charges at rate `b_ρ/2`
  and `eq:graphon-comparison-estimates` bounds by `C_{d,ρ}h⁴`.

The rest of the file is plumbing: the two set-integral estimates `abs_setIntegral_le_measure`
and `measurable_setIntegral_row` that the mixed-rectangle and corner bounds of
`SingularEndpoint/GraphonComparison/RowJensen.lean` both need, and the two uniform family-scalar bounds
`centralSet_exists_qVal_lower` and `centralSet_exists_gam_bound` that the assembly in
`SingularEndpoint/GraphonComparison/GraphonComparisonMaster.lean` needs.

## Contents

* `centralSet`, `measurableSet_centralSet`;
* `tailMass`, `tailMass_nonneg`, `measure_centralSet_add_tailMass`,
  `half_le_measure_centralSet` — `|Ω_ρ(f)| ≥ 1/2` once `|Ω_ρ(f)^c| ≤ 1/2`, the sixth clause of
  `eq:graphon-comparison-estimates`;
* `abs_setIntegral_le_measure`, `measurable_setIntegral_row`;
* `centralSet_exists_qVal_lower`, `centralSet_exists_gam_bound`.
-/

namespace UpperTailOptimizers

namespace SingularEndpoint

open MeasureTheory

variable {d : ℕ}

/-! ## The central set and the tail mass -/

/-- **The central set `Ω_ρ(f) = {y : f(y) ∈ 𝓝_ρ}`** of the proof of `lem:graphon-lagrangian-bound`. -/
def centralSet (d : ℕ) (ρ : ℝ) (f : ℝ → ℝ) : Set ℝ := {y | f y ∈ centralWindow d ρ}

/-- `Ω_ρ(f)` is measurable. -/
theorem measurableSet_centralSet {f : ℝ → ℝ} (hf : Measurable f) (d : ℕ) (ρ : ℝ) :
    MeasurableSet (centralSet d ρ f) := hf (measurableSet_centralWindow d ρ)

/-- **The tail mass `|Ω_ρ(f)^c|`** (closed window; the paper's counterpart is
`λ(Ω_ρ^c) = ν(𝒯_ρ)`). -/
noncomputable def tailMass (d : ℕ) (ρ : ℝ) (f : ℝ → ℝ) : ℝ :=
  (unitμ (centralSet d ρ f)ᶜ).toReal

theorem tailMass_nonneg (d : ℕ) (ρ : ℝ) (f : ℝ → ℝ) : 0 ≤ tailMass d ρ f :=
  ENNReal.toReal_nonneg

/-- `|Ω_ρ(f)| + |Ω_ρ(f)^c| = 1`. -/
theorem measure_centralSet_add_tailMass {f : ℝ → ℝ} (hf : Measurable f) (d : ℕ) (ρ : ℝ) :
    (unitμ (centralSet d ρ f)).toReal + tailMass d ρ f = 1 := by
  have hm := measurableSet_centralSet hf d ρ
  have h := measure_add_measure_compl (μ := unitμ) hm
  have hfin : unitμ (centralSet d ρ f) ≠ ⊤ := measure_ne_top _ _
  have hfin' : unitμ (centralSet d ρ f)ᶜ ≠ ⊤ := measure_ne_top _ _
  rw [tailMass, ← ENNReal.toReal_add hfin hfin', h]
  simp [unitμ]

/-- **`|Ω_ρ(f)| ≥ 1/2`**, the sixth clause of `eq:graphon-comparison-estimates`: it holds
as soon as the tail mass is at most `1/2`, which the localisation supplies. -/
theorem half_le_measure_centralSet {f : ℝ → ℝ} (hf : Measurable f) {d : ℕ} {ρ : ℝ}
    (hε : tailMass d ρ f ≤ 1 / 2) : (1 : ℝ) / 2 ≤ (unitμ (centralSet d ρ f)).toReal := by
  have h := measure_centralSet_add_tailMass hf d ρ
  linarith

/-! ## Two set-integral estimates -/

/-- `|∫_G g| ≤ C|G|` for a measurable `g` bounded by `C`. -/
theorem abs_setIntegral_le_measure {G : Set ℝ} (hG : MeasurableSet G) {g : ℝ → ℝ}
    (hgm : Measurable g) {C : ℝ} (hgb : ∀ x, |g x| ≤ C) :
    |∫ x in G, g x ∂unitμ| ≤ C * (unitμ G).toReal := by
  have hgi : IntegrableOn g G unitμ :=
    Integrable.of_bound hgm.aestronglyMeasurable C
      (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hgb x)
  have hci : IntegrableOn (fun _ : ℝ => C) G unitμ :=
    Integrable.of_bound measurable_const.aestronglyMeasurable |C|
      (Filter.Eventually.of_forall fun _ => by simp [Real.norm_eq_abs])
  have h1 : |∫ x in G, g x ∂unitμ| ≤ ∫ x in G, |g x| ∂unitμ := by
    simpa [Real.norm_eq_abs] using (norm_integral_le_integral_norm (μ := unitμ.restrict G) g)
  have h2 : ∫ x in G, |g x| ∂unitμ ≤ ∫ _x in G, C ∂unitμ :=
    setIntegral_mono_on hgi.abs hci hG fun x _ => hgb x
  have h3 : ∫ _x in G, (C : ℝ) ∂unitμ = C * (unitμ G).toReal := by
    rw [setIntegral_const, measureReal_def, smul_eq_mul, mul_comm]
  linarith

/-- **The row map of a bounded jointly measurable kernel is measurable.**  This is
`StronglyMeasurable.integral_prod_right'` at the finite measure `unitμ|_G`; over `ℝ`,
strong measurability and measurability coincide. -/
theorem measurable_setIntegral_row {F : ℝ → ℝ → ℝ}
    (hF : Measurable fun z : ℝ × ℝ => F z.1 z.2) (G : Set ℝ) :
    Measurable fun x => ∫ y in G, F x y ∂unitμ :=
  (hF.stronglyMeasurable.integral_prod_right' (ν := unitμ.restrict G)).measurable

/-- The row map of a kernel bounded by `C` is bounded by `C`, `unitμ` being a probability
measure. -/
theorem abs_setIntegral_row_le {F : ℝ → ℝ → ℝ}
    (hF : Measurable fun z : ℝ × ℝ => F z.1 z.2) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ x y, |F x y| ≤ C) {G : Set ℝ} (hG : MeasurableSet G) (x : ℝ) :
    |∫ y in G, F x y ∂unitμ| ≤ C := by
  have h := abs_setIntegral_le_measure (g := fun y => F x y) hG
    (hF.comp (measurable_const.prodMk measurable_id)) (C := C) (hb x)
  have h4 : (unitμ G).toReal ≤ 1 := by
    have hle : unitμ G ≤ 1 := prob_le_one
    calc (unitμ G).toReal ≤ (1 : ENNReal).toReal := ENNReal.toReal_mono (by simp) hle
      _ = 1 := ENNReal.toReal_one
  have h5 : C * (unitμ G).toReal ≤ C := by
    calc C * (unitμ G).toReal ≤ C * 1 := mul_le_mul_of_nonneg_left h4 hC
      _ = C := mul_one C
  linarith

/-! ## Uniform family-scalar bounds

`q_h` is bounded above by `1` outright (`qVal_lt_one`); the *lower* bound needs continuity at
the singular endpoint, `q_0 = u_*^d > 0`. -/

/-- **`q_h` is bounded away from `0` for small `h`**, since `q_h → q_0 = u_*^d > 0`
(`qVal_zero`, `hasDerivAt_qVal_zero`).  The bound is `q_0/2`, which is all any consumer
needs. -/
theorem centralSet_exists_qVal_lower (hd : 2 ≤ d) (B : KKTFamily d) :
    ∃ c : ℝ, 0 < c ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, |h| < δ → c ≤ B.qVal h := by
  have hq0 : 0 < B.qVal 0 := by
    rw [KKTFamily.qVal_zero]
    exact pow_pos (uStar_pos hd) d
  have hqc : ContinuousAt B.qVal 0 := (hasDerivAt_qVal_zero B).continuousAt
  obtain ⟨δ, hδ0, hδ⟩ := Metric.eventually_nhds_iff.mp
    (Metric.tendsto_nhds.mp hqc (B.qVal 0 / 2) (by linarith))
  refine ⟨B.qVal 0 / 2, by linarith, δ, hδ0, fun h hh => ?_⟩
  have hdist : dist h (0 : ℝ) < δ := by rwa [Real.dist_eq, sub_zero]
  have hlt := hδ hdist
  rw [Real.dist_eq] at hlt
  have := abs_lt.mp hlt
  linarith [this.1]

/-- A uniform bound on `γ_h` for small `h`, from continuity of the family multiplier.
`SingularEndpoint/GraphonComparison/GraphonComparisonMain.lean` has the same statement as a `private` declaration; this copy
is public, being wanted by `SingularEndpoint/GraphonComparison/GraphonComparisonMaster.lean` as well. -/
theorem centralSet_exists_gam_bound (B : KKTFamily d) :
    ∃ Γ : ℝ, 0 ≤ Γ ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, |h| < δ → |B.gam h| ≤ Γ := by
  have hgc : ContinuousAt B.gam 0 := B.gam_continuousAt
  obtain ⟨δ, hδ0, hδ⟩ := Metric.eventually_nhds_iff.mp
    (Metric.tendsto_nhds.mp hgc (1 : ℝ) one_pos)
  refine ⟨|gammaStar d| + 1, by positivity, δ, hδ0, fun h hh => ?_⟩
  have hdist : dist h (0 : ℝ) < δ := by rwa [Real.dist_eq, sub_zero]
  have hlt := hδ hdist
  rw [Real.dist_eq, B.gam_zero] at hlt
  have h1 : |B.gam h| - |gammaStar d| ≤ |B.gam h - gammaStar d| := abs_sub_abs_le_abs_sub _ _
  linarith

end SingularEndpoint

end UpperTailOptimizers
