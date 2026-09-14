import UpperTailOptimizers.SingularEndpoint.AuxiliaryLagrangian.FirstVariation
import UpperTailOptimizers.Preliminaries.Graphons.ExternalInputs

/-!
# Terminal optimality at the singular endpoint (Section 5, `paper/sections/singular.tex`)

The closing subsection `sec:singular-proof` of `paper/sections/singular.tex` combines the
localization lemma with the full graphon calibration estimate `eq:graphon-lagrangian-bound`
to prove `thm:singular-endpoint`.  Once the calibration estimate is available, the rest of
that argument is *pure arithmetic*, and that is what this file proves:

* `singular_endpoint_endgame` — the scalar endgame.  If a competitor's cost gap `g` obeys the
  master estimate `g ≥ μ·c + M⁻¹·R - M·Δ²` with a nonnegative residual `R`, a constraint
  slack `c ≥ κΔ` bounded below linearly in the moment displacement,
  and `Δ` is nonnegative and small, then `g ≤ 0` forces `g = 0`, `Δ = 0` and `R = 0`.
* `terminal_optimality_of_master` — the graphon form: with the master estimate as a
  hypothesis, every feasible competitor costs at least `I_{p_h}(W_h)`, and one attaining
  that cost has vanishing residual and moment displacement.  This is `eq:graphon-lagrangian-bound`
  through the display that closes the proof.
* `graphon_not_ae_const` — `W_h` is nonconstant for `h ≠ 0`, the nonconstancy clause of
  `thm:singular-endpoint`.  Proved outright: the `d`-th moment `q_h²` exceeds
  `e(W_h)^d` by strict Jensen, whereas an a.e.-constant graphon has `∫W^d = e(W)^d`.

The hypothesis `hmaster` carried here is discharged in `SingularEndpoint/GraphonComparison/GraphonComparisonMaster.lean`
(`exists_comparison_master`, `exists_singular_endpoint_comparison_graph`). In
`SingularEndpoint/Proof/TerminalUnique.lean`, `exists_singular_endpoint_full` adds feasibility and
uniqueness for a given family. `singular_endpoint_full` constructs that family and collects
the other proved clauses of Theorem 5.1, with the documented qualifications.

## Contents

* `singular_endpoint_endgame`;
* `KKTFamily.graphon_not_ae_const`;
* `terminal_optimality_of_master`.
-/

namespace UpperTailOptimizers

namespace SingularEndpoint

open MeasureTheory Real

variable {d : ℕ}

/-! ## The scalar endgame -/

/-- **`sec:singular-proof`, the closing display.**

`g` is the cost gap `I_{p_h}(W) - I_{p_h}(W_h)`, `c` the constraint slack
`t(H,W) - r_h^m`, `R` the residual `‖E‖₂² + A_{h,ρ}(ν) + ν(T_ρ)` with
`A_{h,ρ}(ν) = ∫_{𝓝_ρ} Q_h² dν`, and `Δ` the moment displacement `Δ_h(ν) = ∫f^d - q_h`.
The master estimate `eq:graphon-lagrangian-bound` is `hmaster`, and the linear lower bound
`κΔ ≤ c` on the constraint slack is `hslack`.  The smallness hypothesis `hsmall` lets the
negative quadratic term `-MΔ²` be absorbed by the linear term `μκΔ`; in the paper, `h_ρ` is
decreased so that `C_{d,m,ρ}Δ_h(ν) ≤ (1/4)v q_h^{v-1}` and
`C_{d,m,ρ}Δ_h(ν) ≤ (1/4)μ_h v q_h^{v-1}`, which yields
`μ_h{t(H,W) - r_h^m} - C_{d,m,ρ}Δ_h(ν)² ≥ (1/2)μ_h v q_h^{v-1}Δ_h(ν)`.

The conclusion is the paper's "equality holds throughout". -/
theorem singular_endpoint_endgame {g c Δ R μ κ M D : ℝ}
    (hμ : 0 < μ) (hκ : 0 < κ) (hM : 0 < M) (hR : 0 ≤ R)
    (hΔ0 : 0 ≤ Δ) (hΔD : Δ ≤ D)
    (hsmall : M * D ≤ 3 / 4 * (μ * κ))
    (hmaster : μ * c + M⁻¹ * R - M * Δ ^ 2 ≤ g)
    (hslack : κ * Δ ≤ c)
    (hg : g ≤ 0) : Δ = 0 ∧ R = 0 ∧ g = 0 := by
  have hMinv : 0 < M⁻¹ := inv_pos.mpr hM
  have hRterm : 0 ≤ M⁻¹ * R := mul_nonneg hMinv.le hR
  -- `M Δ² ≤ M D Δ ≤ (3/4) μ κ Δ`
  have hquad : M * Δ ^ 2 ≤ 3 / 4 * (μ * κ) * Δ := by
    have h1 : M * Δ ^ 2 = (M * Δ) * Δ := by ring
    have h2 : M * Δ ≤ M * D := mul_le_mul_of_nonneg_left hΔD hM.le
    calc M * Δ ^ 2 = (M * Δ) * Δ := h1
      _ ≤ (M * D) * Δ := mul_le_mul_of_nonneg_right h2 hΔ0
      _ ≤ 3 / 4 * (μ * κ) * Δ := mul_le_mul_of_nonneg_right hsmall hΔ0
  -- `μ c ≥ μ κ Δ`
  have hmc : μ * (κ * Δ) ≤ μ * c := mul_le_mul_of_nonneg_left hslack hμ.le
  -- hence `g ≥ (1/4) μ κ Δ + M⁻¹ R ≥ 0`
  have hlow : 1 / 4 * (μ * κ) * Δ + M⁻¹ * R ≤ g := by nlinarith
  have hpos : 0 ≤ 1 / 4 * (μ * κ) * Δ := by positivity
  have hgz : g = 0 := le_antisymm hg (by linarith)
  have hzero : 1 / 4 * (μ * κ) * Δ + M⁻¹ * R ≤ 0 := by linarith
  have hΔz : Δ = 0 := by
    by_contra hne
    have : 0 < Δ := lt_of_le_of_ne hΔ0 (Ne.symm hne)
    have : 0 < 1 / 4 * (μ * κ) * Δ := by positivity
    linarith
  have hRz : R = 0 := by
    by_contra hne
    have hRpos : 0 < R := lt_of_le_of_ne hR (Ne.symm hne)
    have : 0 < M⁻¹ * R := mul_pos hMinv hRpos
    rw [hΔz] at hzero
    simp only [mul_zero, zero_add] at hzero
    linarith
  exact ⟨hΔz, hRz, hgz⟩

/-! ## The candidate is nonconstant -/

namespace KKTFamily

variable {B : KKTFamily d}

/-- An a.e.-constant graphon has `∫∫W^k = e(W)^k`. -/
private theorem moment_of_ae_const {W : Graphon} {ρ : ℝ} (hae : ∀ᵐ z ∂gμ, W.toFun z.1 z.2 = ρ)
    (k : ℕ) : W.Wmoment k = W.edgeDensity ^ k := by
  have he : W.edgeDensity = ρ := by
    show ∫ z, W.toFun z.1 z.2 ∂gμ = ρ
    rw [integral_congr_ae (g := fun _ : ℝ × ℝ => ρ) hae, integral_const]
    simp
  have hm : W.Wmoment k = ρ ^ k := by
    show ∫ z, (W.toFun z.1 z.2) ^ k ∂gμ = ρ ^ k
    rw [integral_congr_ae (g := fun _ : ℝ × ℝ => ρ ^ k)
      (hae.mono fun z hz => by rw [hz]), integral_const]
    simp
  rw [hm, he]

/-- **`W_h` is nonconstant for `h ≠ 0`** — the nonconstancy clause of `thm:singular-endpoint`.

Strict Jensen for `u ↦ u^d` gives `q_h = α s^d + (1-α) t^d > (α s + (1-α) t)^d`, i.e.
`∫∫W_h^d = q_h² > e(W_h)^d`, whereas an a.e.-constant graphon has `∫∫W^d = e(W)^d`. -/
theorem graphon_not_ae_const (hd : 2 ≤ d) {h : ℝ} (hh : |h| < B.h₀) (hne : h ≠ 0) :
    ¬ ∃ ρ : ℝ, ∀ᵐ z ∂gμ, (B.graphon hh).toFun z.1 z.2 = ρ := by
  rintro ⟨ρ, hae⟩
  have ha := B.alph_mem h hh
  have hs := sVal_pos hh
  have ht := tVal_pos hh
  -- `s_h ≠ t_h`
  have hst : B.sVal h ≠ B.tVal h := by
    intro hcon
    have : (2 : ℝ) * h = 0 := by
      have : B.u h - h = B.u h + h := hcon
      linarith
    exact hne (by linarith)
  -- strict Jensen for `u ↦ u^d`
  have hcvx : StrictConvexOn ℝ (Set.Ici (0 : ℝ)) fun x : ℝ => x ^ d := strictConvexOn_pow hd
  have hjensen : (B.alph h * B.sVal h + (1 - B.alph h) * B.tVal h) ^ d < B.qVal h := by
    have := hcvx.2 (Set.mem_Ici.mpr hs.le) (Set.mem_Ici.mpr ht.le) hst ha.1
      (by linarith [ha.2]) (by ring : B.alph h + (1 - B.alph h) = 1)
    simpa [qVal, smul_eq_mul] using this
  -- the two moment computations
  have hmom := moment_of_ae_const hae d
  rw [graphon_Wmoment hh, graphon_edgeDensity hh] at hmom
  set P : ℝ := B.alph h * B.sVal h + (1 - B.alph h) * B.tVal h with hP
  have hPpos : 0 < P := by
    have : 0 < 1 - B.alph h := by linarith [ha.2]
    have := mul_pos ha.1 hs
    nlinarith
  -- `q² = (P²)^d = (P^d)²` contradicts `P^d < q` and `0 < P^d`
  have hPd : 0 < P ^ d := pow_pos hPpos d
  have hsq : (P ^ 2) ^ d = (P ^ d) ^ 2 := by rw [← pow_mul, ← pow_mul, mul_comm]
  rw [hsq] at hmom
  nlinarith [qVal_pos hh]

end KKTFamily

/-! ## Terminal optimality from the calibration estimate -/

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **`sec:singular-proof`, the argument after `eq:graphon-lagrangian-bound`.**  Take the
calibration estimate `eq:graphon-lagrangian-bound` and the linear lower bound on the
constraint slack as given, for a fixed `h`, with a residual functional `R` (the paper's
`‖E‖₂² + A_{h,ρ}(ν) + ν(T_ρ)`) and a moment displacement `Δ`.  Then `W_h` is
optimal among feasible graphons, and any competitor attaining its cost has vanishing
residual and moment displacement — which the paper turns into "`ν` is supported on
`{s_h,t_h}`, and `Δ_h(ν)=0` implies `ν=α_hδ_{s_h}+(1-α_h)δ_{t_h}`". -/
theorem terminal_optimality_of_master (H : SimpleGraph V) [DecidableRel H.Adj]
    {B : KKTFamily d} {h : ℝ} (hh : |h| < B.h₀)
    {μ κ M D : ℝ} (hμ : 0 < μ) (hκ : 0 < κ) (hM : 0 < M)
    (hsmall : M * D ≤ 3 / 4 * (μ * κ))
    (R Δ : Graphon → ℝ) (hR : ∀ W, 0 ≤ R W)
    (hΔ0 : ∀ W : Graphon, Feasible H (B.rVal h) W →
      W.Ip (B.p h) ≤ (B.graphon hh).Ip (B.p h) → 0 ≤ Δ W)
    (hΔD : ∀ W : Graphon, Feasible H (B.rVal h) W →
      W.Ip (B.p h) ≤ (B.graphon hh).Ip (B.p h) → Δ W ≤ D)
    (hslack : ∀ W : Graphon, Feasible H (B.rVal h) W →
      W.Ip (B.p h) ≤ (B.graphon hh).Ip (B.p h) →
      κ * Δ W ≤ W.tDensity H - B.rVal h ^ H.edgeFinset.card)
    (hmaster : ∀ W : Graphon, Feasible H (B.rVal h) W →
      W.Ip (B.p h) ≤ (B.graphon hh).Ip (B.p h) →
      μ * (W.tDensity H - B.rVal h ^ H.edgeFinset.card) + M⁻¹ * R W - M * (Δ W) ^ 2
        ≤ W.Ip (B.p h) - (B.graphon hh).Ip (B.p h)) :
    ∀ W : Graphon, Feasible H (B.rVal h) W →
      (B.graphon hh).Ip (B.p h) ≤ W.Ip (B.p h)
        ∧ (W.Ip (B.p h) = (B.graphon hh).Ip (B.p h) → Δ W = 0 ∧ R W = 0) := by
  intro W hfeas
  by_cases hle : W.Ip (B.p h) ≤ (B.graphon hh).Ip (B.p h)
  · obtain ⟨hΔz, hRz, hgz⟩ :=
      singular_endpoint_endgame hμ hκ hM (hR W) (hΔ0 W hfeas hle) (hΔD W hfeas hle) hsmall
        (hmaster W hfeas hle) (hslack W hfeas hle) (by linarith)
    exact ⟨by linarith, fun _ => ⟨hΔz, hRz⟩⟩
  · push Not at hle
    exact ⟨hle.le, fun heq => absurd heq (by linarith)⟩

end SingularEndpoint

end UpperTailOptimizers
