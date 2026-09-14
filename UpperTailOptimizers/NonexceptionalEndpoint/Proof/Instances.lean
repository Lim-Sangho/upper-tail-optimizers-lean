import UpperTailOptimizers.SingularEndpoint.Proof.IntroSingularEndpointOptimizers
import UpperTailOptimizers.NonexceptionalEndpoint.Proof.Global

/-!
# Worked instances: the capstones are not vacuous

Every headline theorem here is stated for an abstract `d`-regular `H` under the hypotheses
`2 ≤ d`, `∀ v, H.degree v = d`, `1 ≤ |E(H)|` — and, for `singular_endpoint_optimizers`, `2 ≤ |V(H)|`.
A reader is entitled to ask
whether those hypotheses can all hold at once — a theorem whose hypotheses are contradictory is
true and says nothing.  This file answers by exhibiting them: it discharges every hypothesis at
two concrete graphs and runs the capstones there.

* `K3 = ⊤ : SimpleGraph (Fin 3)` is `2`-regular with `3` edges;
* `K4 = ⊤ : SimpleGraph (Fin 4)` is `3`-regular with `6` edges.

Both regularity facts are `decide`d, so nothing here is taken on trust.

The two substantive outputs are `K3_has_nonconstant_optimizer` and
`K4_has_nonconstant_optimizer`: at each graph the singular-endpoint theory produces an actual
pair `(p, r)` with `0 < p < 1` and `0 < r < 1`, strictly inside the symmetry-breaking phase,
and an actual graphon at that pair which is feasible, **not** almost everywhere constant, and
minimises `I_p` among all feasible graphons.  So the singular endpoint layer proves something about real
objects, not merely something unfalsifiable.

`K3_main_bipodal_optimizer` does the same for `thm:nonexceptional-optimizers`, at the non-exceptional density
`r₀ = 1/4` (the exceptional density for `d = 2` is `r_* = 1/2`).

## Contents

* `K3`, `K3_reg`, `K3_card`, `K3_verts` and the `K4` analogues — the discharged hypotheses;
* **`K3_has_nonconstant_optimizer`**, **`K4_has_nonconstant_optimizer`** — `thm:endpoint-optimizers` made
  concrete;
* **`K3_main_bipodal_optimizer`** — `thm:nonexceptional-optimizers` made concrete.
-/

namespace UpperTailOptimizers

namespace Instances

open MeasureTheory SingularEndpoint

/-! ## The two graphs -/

/-- The triangle, as the complete graph on three vertices. -/
abbrev K3 : SimpleGraph (Fin 3) := ⊤

theorem K3_reg : ∀ v : Fin 3, K3.degree v = 2 := by decide

theorem K3_card : K3.edgeFinset.card = 3 := by decide

theorem K3_card_ge : 1 ≤ K3.edgeFinset.card := by rw [K3_card]; norm_num

theorem K3_verts : 2 ≤ Fintype.card (Fin 3) := by simp

/-- `K₄`, the smallest cubic graph. -/
abbrev K4 : SimpleGraph (Fin 4) := ⊤

theorem K4_reg : ∀ v : Fin 4, K4.degree v = 3 := by decide

theorem K4_card : K4.edgeFinset.card = 6 := by decide

theorem K4_card_ge : 1 ≤ K4.edgeFinset.card := by rw [K4_card]; norm_num

theorem K4_verts : 2 ≤ Fintype.card (Fin 4) := by simp

/-! ## The singular endpoint, made concrete

The abstract statement is `SingularEndpoint.singular_endpoint_optimizers`
(`thm:endpoint-optimizers`).  What follows picks a parameter `h` inside both the family
window and the optimality window, and reads off the resulting graphon. -/

/-- **The singular endpoint theory is not vacuous at `K₃`.**  There are `p, r ∈ (0,1)` with
`p < p_c(r)` — strictly inside the symmetry-breaking phase — and a graphon that is feasible for
`t(K₃,·) ≥ r³`, is not almost everywhere constant, and minimises `I_p` among all feasible
graphons. -/
theorem K3_has_nonconstant_optimizer :
    ∃ (p r : ℝ) (W : Graphon), 0 < p ∧ p < 1 ∧ 0 < r ∧ r < 1 ∧
      Feasible K3 r W ∧ (¬ ∃ c : ℝ, ∀ᵐ z ∂gμ, W.toFun z.1 z.2 = c) ∧
      p < pcGlobal 2 r ∧
      ∀ W' : Graphon, Feasible K3 r W' → W.Ip p ≤ W'.Ip p := by
  obtain ⟨B, C, -, hall⟩ := singular_endpoint_optimizers (d := 2) (by norm_num)
  obtain ⟨δ, hresult⟩ := hall K3 K3_reg K3_card_ge K3_verts
  have hδ : 0 < δ := hresult.delta_pos
  have hδh₀ : δ ≤ B.h₀ := hresult.delta_le
  obtain ⟨h, hpos, hwin, hlt⟩ : ∃ h : ℝ, 0 < h ∧ |h| < B.h₀ ∧ h < δ :=
    ⟨δ / 2, half_pos hδ, by rw [abs_of_pos (half_pos hδ)]; linarith, by linarith⟩
  obtain ⟨-, -, hnc, htd, hopt⟩ := hresult.optimizers h hwin hpos hlt
  have hsym := hresult.below_boundary h hpos hlt
  exact ⟨B.p h, B.rVal h, B.graphon hwin, (B.p_mem h hwin).1, (B.p_mem h hwin).2,
    KKTFamily.rVal_pos (by norm_num) hwin, KKTFamily.rVal_lt_one (by norm_num) hwin,
    le_of_eq htd.symm, hnc, hsym, fun W' hW' => (hopt W' hW').1⟩

/-- **The singular endpoint theory is not vacuous at `K₄`** either, so the construction is not an
accident of `d = 2`. -/
theorem K4_has_nonconstant_optimizer :
    ∃ (p r : ℝ) (W : Graphon), 0 < p ∧ p < 1 ∧ 0 < r ∧ r < 1 ∧
      Feasible K4 r W ∧ (¬ ∃ c : ℝ, ∀ᵐ z ∂gμ, W.toFun z.1 z.2 = c) ∧
      p < pcGlobal 3 r ∧
      ∀ W' : Graphon, Feasible K4 r W' → W.Ip p ≤ W'.Ip p := by
  obtain ⟨B, C, -, hall⟩ := singular_endpoint_optimizers (d := 3) (by norm_num)
  obtain ⟨δ, hresult⟩ := hall K4 K4_reg K4_card_ge K4_verts
  have hδ : 0 < δ := hresult.delta_pos
  have hδh₀ : δ ≤ B.h₀ := hresult.delta_le
  obtain ⟨h, hpos, hwin, hlt⟩ : ∃ h : ℝ, 0 < h ∧ |h| < B.h₀ ∧ h < δ :=
    ⟨δ / 2, half_pos hδ, by rw [abs_of_pos (half_pos hδ)]; linarith, by linarith⟩
  obtain ⟨-, -, hnc, htd, hopt⟩ := hresult.optimizers h hwin hpos hlt
  have hsym := hresult.below_boundary h hpos hlt
  exact ⟨B.p h, B.rVal h, B.graphon hwin, (B.p_mem h hwin).1, (B.p_mem h hwin).2,
    KKTFamily.rVal_pos (by norm_num) hwin, KKTFamily.rVal_lt_one (by norm_num) hwin,
    le_of_eq htd.symm, hnc, hsym, fun W' hW' => (hopt W' hW').1⟩

/-! ## `thm:nonexceptional-optimizers`, made concrete -/

/-- **`thm:nonexceptional-optimizers` is not vacuous.**  Its hypotheses hold at `H = K₃` and `r₀ = 1/4`, which is
non-exceptional because the exceptional density at `d = 2` is `r_* = 1/2`. -/
theorem K3_main_bipodal_optimizer :
    ∃ ρ η C : ℝ, 0 < ρ ∧ 0 < η ∧ 0 ≤ C ∧
      ∀ r : ℝ, |r - 1/4| < ρ → ∀ p : ℝ, |p - pcGlobal 2 r| < η →
        0 < p ∧ p < r ∧
        (pcGlobal 2 r ≤ p →
          phiVar K3 p r = Jp p r ∧
          (∀ hr' : r ∈ Set.Icc (0:ℝ) 1, (constGraphon r hr').Ip p = phiVar K3 p r) ∧
          (∀ W : Graphon, Feasible K3 r W → W.Ip p = phiVar K3 p r →
            ∀ᵐ z ∂gμ, W.toFun z.1 z.2 = r)) ∧
        (p < pcGlobal 2 r →
          0 < AHGlobal K3 2 r ∧
          ∃ Wstar : Graphon, Feasible K3 r Wstar ∧ Wstar.Ip p = phiVar K3 p r ∧
            IsBipodal Wstar ∧
            (¬ ∃ c : ℝ, ∀ᵐ z ∂gμ, Wstar.toFun z.1 z.2 = c) ∧
            (∀ W : Graphon, Feasible K3 r W → W.Ip p = phiVar K3 p r →
              ∃ σ : ℝ → ℝ, IsRelabelling σ ∧
                ∀ᵐ z ∂gμ, W.toFun z.1 z.2 = Wstar.toFun (σ z.1) (σ z.2)) ∧
            |Wstar.edgeDensity - (r - lambdaGlobal 2 p r / AHGlobal K3 2 r)|
              ≤ C * lambdaGlobal 2 p r ^ 2 ∧
            |phiVar K3 p r - (Jp p r - lambdaGlobal 2 p r ^ 2 / (2 * AHGlobal K3 2 r))|
              ≤ C * lambdaGlobal 2 p r ^ 3) :=
  (main_bipodal_optimizer (d := 2) (by norm_num) K3 K3_reg K3_card_ge
    (r₀ := 1/4) (by norm_num) (by norm_num) (by rw [rStar]; norm_num)).window

end Instances

end UpperTailOptimizers
