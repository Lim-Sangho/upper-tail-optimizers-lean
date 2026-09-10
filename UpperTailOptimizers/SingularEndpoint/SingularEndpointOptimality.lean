import UpperTailOptimizers.SingularEndpoint.GraphonComparisonMaster
import UpperTailOptimizers.SingularEndpoint.Terminal

/-!
# `thm:endpoint-optimality`, the optimality clause (Section 7)

`sec:endpoint-optimality-proof` closes by feeding `eq:graphon-lagrangian-bound` and the
linearised constraint the linear constraint control into the scalar endgame
`singular_endpoint_endgame`.  Both inputs are now available:

* the calibration estimate in its graph-carrying form is
  `exists_singular_endpoint_comparison_graph` (`SingularEndpoint/GraphonComparisonMaster.lean`);
* the linearised constraint is derived here, from the *same* three ingredients as the
  Lagrangian conversion — `r_h^m = q_h^n`, the rank-one splitting `t(H,W) = q^n + 𝓡_H`, and
  the polynomial expansion `q^n - q_h^n = n q_h^{n-1}Δ + O(Δ²)` — together with
  the residual bound `‖E‖₂ ≤ M|Δ|` (in the paper an unlabelled display in the proof of
  `thm:endpoint-optimality`, with constant `C_{d,m,ρ}`), which the master estimate itself
  supplies once the competitor is feasible and no more costly than `W_h`.

What this file stops short of is the uniqueness half of `thm:endpoint-optimality`.
`singular_endpoint_endgame` returns `Δ = 0` and `R = 0`, i.e. `E = 0`, `ν(T_ρ) = 0` and `Q_h = 0`
`ν`-a.e.; turning that into a measure-preserving relabelling of `W_h` is the paper's
"`ν = βδ_{s_h} + (1-β)δ_{t_h}` and the moment equation pins `β = α_h`".  That step is
`SingularEndpoint/TerminalTwoValued.lean` and `SingularEndpoint/CdfTransport.lean`, and
`SingularEndpoint/TerminalUnique.lean` assembles it with `exists_singular_endpoint_optimality` below into
`exists_singular_endpoint_full` for a supplied family; `singular_endpoint_full` constructs the
family and adds the other proved clauses, with the qualifications in `FORMALISATION.md`.

## Contents

* `KKTFamily.exists_gam_lower`, `exists_muVal_lower` — `γ_h` and `μ_h` bounded away
  from `0` for small `h`;
* `exists_singular_endpoint_rigidity` — the scalar endgame's own conclusion: a
  competitor no more costly than `W_h` has `Δ = 0` and `R = 0`, i.e. zero residual, zero
  rare-row mass, `Q_h = 0` on the central rows and equal cost;
* **`exists_singular_endpoint_optimality`** — `W_h` minimises `I_{p_h}` among feasible graphons, for
  every small `h > 0`.
-/

namespace UpperTailOptimizers

namespace SingularEndpoint

open MeasureTheory

variable {d : ℕ}

/-! ## The multiplier is bounded away from zero -/

namespace KKTFamily

/-- `γ_h ≥ γ_*/2 > 0` for small `h`, from `γ_0 = γ_*` and continuity. -/
theorem exists_gam_lower (hd : 2 ≤ d) (B : KKTFamily d) :
    ∃ c : ℝ, 0 < c ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, |h| < δ → c ≤ B.gam h := by
  have hg0 : 0 < gammaStar d := gammaStar_pos hd
  have hgc : ContinuousAt B.gam 0 := B.gam_continuousAt
  obtain ⟨δ, hδ0, hδ⟩ := Metric.eventually_nhds_iff.mp
    (Metric.tendsto_nhds.mp hgc (gammaStar d / 2) (by linarith))
  refine ⟨gammaStar d / 2, by linarith, δ, hδ0, fun h hh => ?_⟩
  have hdist : dist h (0 : ℝ) < δ := by rwa [Real.dist_eq, sub_zero]
  have hlt := hδ hdist
  rw [Real.dist_eq, B.gam_zero] at hlt
  have := abs_lt.mp hlt
  linarith [this.1]

end KKTFamily

/-- `μ_h ≥ γ_*/(2m) > 0` for small `h`: `μ_h = γ_h/(m q_h^{v-2})` with `q_h ≤ 1` and
`v - 2 ≥ 0`, so the denominator is at most `m`. -/
theorem exists_muVal_lower (hd : 2 ≤ d) (B : KKTFamily d) {m : ℝ} (hm : 0 < m)
    (hmd : (d : ℝ) ≤ m) :
    ∃ c : ℝ, 0 < c ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, |h| < δ → |h| < B.h₀ →
      c ≤ B.muVal m h := by
  have hd0 : (0 : ℝ) < (d : ℝ) := dpos hd
  obtain ⟨cg, hcg, δg, hδg, hgam⟩ := KKTFamily.exists_gam_lower hd B
  have he0 : (0 : ℝ) ≤ 2 * m / (d : ℝ) - 2 := by
    rw [sub_nonneg, le_div_iff₀ hd0]; linarith
  refine ⟨cg / m, by positivity, δg, hδg, ?_⟩
  intro h hhδ hhb
  have hqpos := KKTFamily.qVal_pos hhb
  have hq1 := KKTFamily.qVal_lt_one hd hhb
  have hqe : B.qVal h ^ (2 * m / (d : ℝ) - 2) ≤ 1 := by
    have h1 : B.qVal h ^ (2 * m / (d : ℝ) - 2) ≤ (1 : ℝ) ^ (2 * m / (d : ℝ) - 2) :=
      Real.rpow_le_rpow hqpos.le hq1.le he0
    rwa [Real.one_rpow] at h1
  have hqepos : (0 : ℝ) < B.qVal h ^ (2 * m / (d : ℝ) - 2) := Real.rpow_pos_of_pos hqpos _
  have hden : m * B.qVal h ^ (2 * m / (d : ℝ) - 2) ≤ m * 1 :=
    mul_le_mul_of_nonneg_left hqe hm.le
  rw [KKTFamily.muVal, le_div_iff₀ (mul_pos hm hqepos)]
  calc cg / m * (m * B.qVal h ^ (2 * m / (d : ℝ) - 2))
      = cg * B.qVal h ^ (2 * m / (d : ℝ) - 2) := by field_simp
    _ ≤ cg * 1 := mul_le_mul_of_nonneg_left hqe hcg.le
    _ = cg := mul_one cg
    _ ≤ B.gam h := hgam h hhδ

/-! ## The linearised constraint, as pure arithmetic

Both steps are hoisted out of `exists_singular_endpoint_optimality`: in that proof's context they
exhaust the heartbeat budget. -/

/-- `C·(M·(κ/(CM))) = κ`, hoisted so `field_simp` runs in a small context. -/
private theorem singularEndpointOpt_cancel {C M κ : ℝ} (hC : C ≠ 0) (hM : M ≠ 0) :
    C * (M * (κ / (C * M))) = κ := by field_simp

/-- `M·(M·(3A/(4M²))) = (3/4)A`, hoisted for the same reason. -/
private theorem singularEndpointOpt_cancel₂ {M A : ℝ} (hM : M ≠ 0) :
    M * (M * (3 * A / (4 * (M * M)))) = 3 / 4 * A := by field_simp

/-- The error of the linearised constraint, abstractly: `|A| ≤ PΔ²`, `|B| ≤ QL³` and
`L ≤ M|Δ| ≤ M²` give `|A + B| ≤ (P + QM⁴)Δ²`.  Hoisted because in the ambient context the
same chain exhausts the heartbeat budget. -/
private theorem singularEndpointOpt_err_le {A B Δ L M P Q : ℝ} (hL0 : 0 ≤ L) (hM0 : 0 ≤ M)
    (hQ0 : 0 ≤ Q) (hA : |A| ≤ P * Δ ^ 2) (hB : |B| ≤ Q * L ^ 3)
    (hL : L ≤ M * |Δ|) (hΔM : |Δ| ≤ M) :
    |A + B| ≤ (P + Q * M ^ 3 * M) * Δ ^ 2 := by
  have hsq : |Δ| ^ 2 = Δ ^ 2 := sq_abs Δ
  have h1 : L ^ 3 ≤ (M * |Δ|) ^ 3 := pow_le_pow_left₀ hL0 hL 3
  have h3 : |Δ| * |Δ| ^ 2 ≤ M * |Δ| ^ 2 := mul_le_mul_of_nonneg_right hΔM (sq_nonneg _)
  have h4 : Q * L ^ 3 ≤ Q * (M ^ 3 * (M * |Δ| ^ 2)) := by
    refine mul_le_mul_of_nonneg_left ?_ hQ0
    calc L ^ 3 ≤ (M * |Δ|) ^ 3 := h1
      _ = M ^ 3 * (|Δ| * |Δ| ^ 2) := by ring
      _ ≤ M ^ 3 * (M * |Δ| ^ 2) := mul_le_mul_of_nonneg_left h3 (by positivity)
  have h5 : Q * (M ^ 3 * (M * |Δ| ^ 2)) = Q * M ^ 3 * M * Δ ^ 2 := by rw [hsq]; ring
  have h6 : (P + Q * M ^ 3 * M) * Δ ^ 2 = P * Δ ^ 2 + Q * M ^ 3 * M * Δ ^ 2 := by ring
  have hab := abs_add_le A B
  linarith

/-- **Feasibility forces `Δ ≥ 0`.**  If `sl ≥ 0`, `sl ≤ aΔ + C₁Δ²`, `2κ ≤ a` and
`C₁|Δ| ≤ κ` with `κ > 0`, then `Δ ≥ 0`: for `Δ < 0` the right-hand side is at most
`-κ|Δ| < 0`. -/
private theorem singularEndpointOpt_delta_nonneg {sl a Δ C₁ κ : ℝ} (hsl : 0 ≤ sl)
    (hup : sl - a * Δ ≤ C₁ * Δ ^ 2) (hκa : 2 * κ ≤ a) (hκ : 0 < κ)
    (hC : C₁ * |Δ| ≤ κ) : 0 ≤ Δ := by
  by_contra hneg
  push Not at hneg
  have hD : Δ = -|Δ| := by rw [abs_of_neg hneg]; ring
  have hpos : 0 < |Δ| := abs_pos.mpr (ne_of_lt hneg)
  have h1 : C₁ * |Δ| * |Δ| ≤ κ * |Δ| := mul_le_mul_of_nonneg_right hC (abs_nonneg Δ)
  have h2 : 2 * κ * |Δ| ≤ a * |Δ| := mul_le_mul_of_nonneg_right hκa (abs_nonneg Δ)
  have haΔ : a * Δ = -(a * |Δ|) := by rw [abs_of_neg hneg]; ring
  have hC1sq : C₁ * Δ ^ 2 = C₁ * |Δ| * |Δ| := by rw [abs_of_neg hneg]; ring
  rw [haΔ, hC1sq] at hup
  have hκpos : 0 < κ * |Δ| := mul_pos hκ hpos
  linarith

/-- **the linear constraint control.**  If `sl ≥ aΔ - C₁Δ²`, `2κ ≤ a`, `Δ ≥ 0` and
`C₁Δ ≤ κ`, then `κΔ ≤ sl`. -/
private theorem singularEndpointOpt_slack {sl a Δ C₁ κ : ℝ} (hlow : -(C₁ * Δ ^ 2) ≤ sl - a * Δ)
    (hκa : 2 * κ ≤ a) (hΔ : 0 ≤ Δ) (hC : C₁ * Δ ≤ κ) : κ * Δ ≤ sl := by
  have h1 : C₁ * Δ ^ 2 ≤ κ * Δ := by
    have : C₁ * Δ * Δ ≤ κ * Δ := mul_le_mul_of_nonneg_right hC hΔ
    nlinarith [this]
  have h2 : 2 * κ * Δ ≤ a * Δ := mul_le_mul_of_nonneg_right hκa hΔ
  linarith

/-! ## The endgame -/

/-- **`thm:endpoint-optimality`, optimality clause.**

There is a threshold `δ > 0` such that, for every `0 < h < δ` inside the family window, the
family graphon `W_h` minimises `I_{p_h}` among all graphons feasible for
`t(H,·) ≥ r_h^m`.

The proof is `sec:endpoint-optimality-proof`.  If the competitor costs more there is nothing to
prove; otherwise `exists_singular_endpoint_comparison_graph` gives

`0 ≥ I_{p_h}(W) - I_{p_h}(W_h) ≥ μ_h{t(H,W) - r_h^m} + M⁻¹R - MΔ²`,

and feasibility with `μ_h > 0` forces `R ≤ M²Δ²`, hence the residual bound `‖E‖₂ ≤ M|Δ|`
(an unlabelled display in the paper's proof).  Substituting that into the same expansion
that produced the Lagrangian — `t(H,W) - r_h^m = n q_h^{n-1}Δ + O(Δ²)` — gives `Δ ≥ 0` and
then `t(H,W) - r_h^m ≥ κΔ` with `κ = n c^{n-1}/2`; the paper's
the linear constraint control states this linearised constraint with the quadratic
defect already absorbed, as `μ_h{t(H,W) - r_h^m} - CΔ² ≥ (1/4)μ_h v q_h^{v-1}Δ`.  The
scalar endgame `singular_endpoint_endgame` closes it: the negative `MΔ²` is absorbed by the positive
`μ_hκΔ` because `Δ = O(h⁴)` while `μ_h` and `κ` are bounded away from `0`.

What `singular_endpoint_endgame` returns is stronger than optimality: alongside `g = 0` it gives
`Δ = 0` and `R = 0`, i.e. `E = 0`, `|G_ρᶜ| = 0` and `Q_h(f) = 0` a.e.  This theorem therefore
states the full **rigidity**, from which optimality is the immediate corollary
`exists_singular_endpoint_optimality` and the uniqueness clause of `thm:endpoint-optimality` follows
in `SingularEndpoint/TerminalUnique.lean`. -/
theorem exists_singular_endpoint_rigidity (hd : 2 ≤ d) {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (hreg : ∀ v, H.degree v = d)
    (hcard : 1 ≤ H.edgeFinset.card) (hv : 2 ≤ Fintype.card V) (B : KKTFamily d) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ (h : ℝ) (hh : |h| < B.h₀), 0 < h → h < δ → h ≤ 1 →
      ∀ W : Graphon, Feasible H (B.rVal h) W → W.Ip (B.p h) ≤ (B.graphon hh).Ip (B.p h) →
        ∃ P : FactorDecomp d W,
          P.qVal = B.qVal h ∧ P.residSq = 0 ∧
          (∫ x in centralSet d ρ P.f, B.Qh h (P.f x) ^ 2 ∂unitμ) = 0 ∧
          tailMass d ρ P.f = 0 ∧
          W.Ip (B.p h) = (B.graphon hh).Ip (B.p h) := by
  classical
  have hd0 : (0 : ℝ) < (d : ℝ) := dpos hd
  have hmpos : (0 : ℝ) < (H.edgeFinset.card : ℝ) := by exact_mod_cast hcard
  have hnR : 2 * (H.edgeFinset.card : ℝ) = (Fintype.card V : ℝ) * (d : ℝ) := by
    have := factorMain_two_mul_card_edgeFinset H hreg
    exact_mod_cast congrArg (fun k : ℕ => (k : ℝ)) this
  have hvR : (2 : ℝ) ≤ (Fintype.card V : ℝ) := by exact_mod_cast hv
  have hmd : (d : ℝ) ≤ (H.edgeFinset.card : ℝ) := by nlinarith [hnR, hvR, hd0]
  obtain ⟨ρ, hρ0, M, hM, δ₀, hδ₀, hmod⟩ :=
    exists_singular_endpoint_comparison_graph hd H hreg hcard hv B
  obtain ⟨μc, hμc, δμ, hδμ, hmulow⟩ := exists_muVal_lower hd B hmpos hmd
  obtain ⟨Cμ, hCμ, δu, hδu, hmuup⟩ := exists_abs_muVal_le hd B hmpos hmd
  obtain ⟨cq, hcq, δq, hδq, hqlow⟩ := centralSet_exists_qVal_lower hd B
  -- the constants of the linearised constraint
  obtain ⟨κ, hκdef⟩ : ∃ t : ℝ,
      t = (Fintype.card V : ℝ) * cq ^ (Fintype.card V - 1) / 2 := ⟨_, rfl⟩
  have hκ0 : 0 < κ := by
    rw [hκdef]
    have : (0 : ℝ) < cq ^ (Fintype.card V - 1) := pow_pos hcq _
    have hn0 : (0 : ℝ) < (Fintype.card V : ℝ) := by linarith
    positivity
  obtain ⟨C₁, hC₁def⟩ : ∃ t : ℝ,
      t = (Fintype.card V : ℝ) ^ 2 * (2 ^ d : ℝ) ^ (2 * Fintype.card V)
        + (40 : ℝ) ^ H.edgeFinset.card * M ^ 3 * M := ⟨_, rfl⟩
  have hC₁0 : 0 < C₁ := by
    rw [hC₁def]
    have h1 : (0 : ℝ) < (Fintype.card V : ℝ) ^ 2 * (2 ^ d : ℝ) ^ (2 * Fintype.card V) := by
      have : (0 : ℝ) < (Fintype.card V : ℝ) := by linarith
      positivity
    have h2 : (0 : ℝ) < (40 : ℝ) ^ H.edgeFinset.card * M ^ 3 * M := by positivity
    linarith
  -- the two smallness cuts on `h`
  obtain ⟨t₁, ht₁⟩ : ∃ t : ℝ, t = κ / (C₁ * M) := ⟨_, rfl⟩
  have ht₁0 : 0 < t₁ := by rw [ht₁]; positivity
  obtain ⟨t₂, ht₂⟩ : ∃ t : ℝ, t = 3 * (μc * κ) / (4 * (M * M)) := ⟨_, rfl⟩
  have ht₂0 : 0 < t₂ := by rw [ht₂]; positivity
  refine ⟨ρ, hρ0, min (min δ₀ δμ) (min (min δu δq) (min (min t₁ t₂) 1)),
    lt_min (lt_min hδ₀ hδμ) (lt_min (lt_min hδu hδq) (lt_min (lt_min ht₁0 ht₂0) one_pos)),
    ?_⟩
  intro h hhb hh0 hhδ hh1 W hfeas hcost
  -- the thresholds
  have hh₀ : h < δ₀ := lt_of_lt_of_le hhδ (le_trans (min_le_left _ _) (min_le_left _ _))
  have hhμ : |h| < δμ := by
    rw [abs_of_pos hh0]
    exact lt_of_lt_of_le hhδ (le_trans (min_le_left _ _) (min_le_right _ _))
  have hhu : |h| < δu := by
    rw [abs_of_pos hh0]
    exact lt_of_lt_of_le hhδ
      (le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_left _ _)))
  have hhq : |h| < δq := by
    rw [abs_of_pos hh0]
    exact lt_of_lt_of_le hhδ
      (le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_right _ _)))
  have hht₁ : h < t₁ := lt_of_lt_of_le hhδ
    (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_left _ _) (min_le_left _ _))))
  have hht₂ : h < t₂ := lt_of_lt_of_le hhδ
    (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_left _ _) (min_le_right _ _))))
  -- the master estimate
  obtain ⟨P, hmom, hmain⟩ := hmod h hhb hh0 hh₀ hh1 W hfeas hcost
  obtain ⟨mu, hmudef⟩ : ∃ t : ℝ, t = B.muVal (H.edgeFinset.card : ℝ) h := ⟨_, rfl⟩
  have hmulow' : μc ≤ mu := by rw [hmudef]; exact hmulow h hhμ hhb
  have hmu0 : 0 < mu := lt_of_lt_of_le hμc hmulow'
  have hmuC : |mu| ≤ Cμ := by rw [hmudef]; exact hmuup h hhu hhb
  obtain ⟨Δ, hΔdef⟩ : ∃ t : ℝ, t = P.qVal - B.qVal h := ⟨_, rfl⟩
  obtain ⟨R, hRdef⟩ : ∃ t : ℝ, t = P.residSq
      + (∫ x in centralSet d ρ P.f, B.Qh h (P.f x) ^ 2 ∂unitμ)
      + tailMass d ρ P.f := ⟨_, rfl⟩
  obtain ⟨sl, hsldef⟩ : ∃ t : ℝ,
      t = W.tDensity H - B.rVal h ^ H.edgeFinset.card := ⟨_, rfl⟩
  obtain ⟨G, hGdef⟩ : ∃ t : ℝ,
      t = W.Ip (B.p h) - (B.graphon hhb).Ip (B.p h) := ⟨_, rfl⟩
  have hmain' : mu * sl + M⁻¹ * R - M * Δ ^ 2 ≤ G := by
    rw [hmudef, hsldef, hRdef, hΔdef, hGdef]; exact hmain
  have hG0 : G ≤ 0 := by rw [hGdef]; linarith
  have hfeas' : B.rVal h ^ H.edgeFinset.card ≤ W.tDensity H := hfeas
  have hsl0 : 0 ≤ sl := by rw [hsldef]; linarith
  have hR0 : 0 ≤ R := by
    rw [hRdef]
    have h1 : (0 : ℝ) ≤ P.residSq := P.residSq_nonneg
    have h2 : (0 : ℝ) ≤ ∫ x in centralSet d ρ P.f, B.Qh h (P.f x) ^ 2 ∂unitμ :=
      setIntegral_nonneg (measurableSet_centralSet P.meas_f d ρ) fun x _ => sq_nonneg _
    have h3 : (0 : ℝ) ≤ tailMass d ρ P.f := ENNReal.toReal_nonneg
    linarith
  have hΔabs : |Δ| ≤ M * h ^ 4 := by rw [hΔdef]; exact hmom
  -- the residual bound in the proof of `thm:endpoint-optimality`: `‖E‖₂ ≤ M|Δ|`
  have hmuslsl : 0 ≤ mu * sl := mul_nonneg hmu0.le hsl0
  have hMinv : (0 : ℝ) < M⁻¹ := inv_pos.mpr hM
  have hRq : M⁻¹ * R ≤ M * Δ ^ 2 := by linarith
  have hEsq : P.residSq ≤ M * (M * Δ ^ 2) := by
    have h1 : P.residSq ≤ R := by
      rw [hRdef]
      have h2 : (0 : ℝ) ≤ ∫ x in centralSet d ρ P.f, B.Qh h (P.f x) ^ 2 ∂unitμ :=
        setIntegral_nonneg (measurableSet_centralSet P.meas_f d ρ) fun x _ => sq_nonneg _
      have h3 : (0 : ℝ) ≤ tailMass d ρ P.f := ENNReal.toReal_nonneg
      linarith
    have h4 : R ≤ M * (M * Δ ^ 2) := by
      have := mul_le_mul_of_nonneg_left hRq hM.le
      rwa [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hM), one_mul] at this
    linarith
  have hL : P.residL2 ≤ M * |Δ| := by
    have hsq : P.residL2 ^ 2 = P.residSq := P.residL2_sq
    have h1 : P.residL2 ^ 2 ≤ (M * |Δ|) ^ 2 := by
      rw [hsq]
      have : (M * |Δ|) ^ 2 = M * (M * Δ ^ 2) := by
        rw [mul_pow, sq_abs]; ring
      rw [this]; exact hEsq
    have h2 : (0 : ℝ) ≤ M * |Δ| := by positivity
    exact le_of_sq_le_sq h1 h2
  -- the second-order expansion of the constraint slack
  have hTay := abs_pow_sub_taylor_le (M := (2 : ℝ) ^ d) (one_le_pow₀ (by norm_num))
    P.qVal_mem_Icc.1 P.qVal_mem_Icc.2 (KKTFamily.qVal_pos hhb).le
    (le_trans (KKTFamily.qVal_lt_one hd hhb).le (one_le_pow₀ (by norm_num)))
    (Fintype.card V)
  have hT := P.abs_tDensity_sub_qVal_pow_le H hreg
  have hr := KKTFamily.rVal_pow_card_edges H hd hreg hhb
  have hqe : cq ^ (Fintype.card V - 1) ≤ B.qVal h ^ (Fintype.card V - 1) :=
    pow_le_pow_left₀ hcq.le (hqlow h hhq) _
  have hslid : sl = (P.qVal ^ Fintype.card V - B.qVal h ^ Fintype.card V
        - (Fintype.card V : ℝ) * B.qVal h ^ (Fintype.card V - 1) * Δ)
      + (W.tDensity H - P.qVal ^ Fintype.card V)
      + (Fintype.card V : ℝ) * B.qVal h ^ (Fintype.card V - 1) * Δ := by
    rw [hsldef, hr, hΔdef]; ring
  have hcube : P.residL2 ^ 3 ≤ M ^ 3 * |Δ| ^ 3 := by
    have h1 : P.residL2 ^ 3 ≤ (M * |Δ|) ^ 3 :=
      pow_le_pow_left₀ P.residL2_nonneg hL 3
    calc P.residL2 ^ 3 ≤ (M * |Δ|) ^ 3 := h1
      _ = M ^ 3 * |Δ| ^ 3 := by ring
  have hΔ1 : |Δ| ≤ M := by
    have hh4le : h ^ 4 ≤ 1 := pow_le_one₀ hh0.le hh1
    have h1 : M * h ^ 4 ≤ M * 1 := mul_le_mul_of_nonneg_left hh4le hM.le
    linarith
  have hid : sl - (Fintype.card V : ℝ) * B.qVal h ^ (Fintype.card V - 1) * Δ
      = (P.qVal ^ Fintype.card V - B.qVal h ^ Fintype.card V
          - (Fintype.card V : ℝ) * B.qVal h ^ (Fintype.card V - 1) * Δ)
        + (W.tDensity H - P.qVal ^ Fintype.card V) := by rw [hslid]; ring
  have hTay' : |P.qVal ^ Fintype.card V - B.qVal h ^ Fintype.card V
        - (Fintype.card V : ℝ) * B.qVal h ^ (Fintype.card V - 1) * Δ|
      ≤ (Fintype.card V : ℝ) ^ 2 * (2 ^ d : ℝ) ^ (2 * Fintype.card V) * Δ ^ 2 := by
    rw [hΔdef]; exact hTay
  have herr : |sl - (Fintype.card V : ℝ) * B.qVal h ^ (Fintype.card V - 1) * Δ|
      ≤ C₁ * Δ ^ 2 := by
    rw [hid, hC₁def]
    exact singularEndpointOpt_err_le P.residL2_nonneg hM.le (by positivity) hTay' hT hL hΔ1
  -- `Δ ≥ 0` and the linearised constraint
  have hnq : κ ≤ (Fintype.card V : ℝ) * B.qVal h ^ (Fintype.card V - 1) / 2 := by
    rw [hκdef]
    have hn0 : (0 : ℝ) ≤ (Fintype.card V : ℝ) := by linarith
    have := mul_le_mul_of_nonneg_left hqe hn0
    linarith
  have hC₁h : C₁ * (M * h ^ 4) ≤ κ := by
    have h1 : h ^ 4 ≤ h := by
      have := pow_le_pow_of_le_one hh0.le hh1 (by omega : 1 ≤ 4)
      rwa [pow_one] at this
    have h2 : C₁ * (M * h ^ 4) ≤ C₁ * (M * h) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 hM.le) hC₁0.le
    have h3 : C₁ * (M * h) ≤ C₁ * (M * t₁) := by
      refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hht₁.le hM.le) hC₁0.le
    have h4 : C₁ * (M * t₁) = κ := by
      rw [ht₁]; exact singularEndpointOpt_cancel (ne_of_gt hC₁0) (ne_of_gt hM)
    linarith
  have hC₁Δ : C₁ * |Δ| ≤ κ := le_trans (mul_le_mul_of_nonneg_left hΔabs hC₁0.le) hC₁h
  have hκa : 2 * κ ≤ (Fintype.card V : ℝ) * B.qVal h ^ (Fintype.card V - 1) := by
    linarith [hnq]
  have hΔ0 : 0 ≤ Δ :=
    singularEndpointOpt_delta_nonneg hsl0 (abs_le.mp herr).2 hκa hκ0 hC₁Δ
  have hslack : κ * Δ ≤ sl := by
    have hΔabs' : |Δ| = Δ := abs_of_nonneg hΔ0
    have hC₁Δ' : C₁ * Δ ≤ κ := by rwa [hΔabs'] at hC₁Δ
    exact singularEndpointOpt_slack (abs_le.mp herr).1 hκa hΔ0 hC₁Δ'
  -- the endgame
  have hΔD : Δ ≤ M * h ^ 4 := le_trans (le_abs_self Δ) hΔabs
  have hsmall : M * (M * h ^ 4) ≤ 3 / 4 * (mu * κ) := by
    have h1 : h ^ 4 ≤ h := by
      have := pow_le_pow_of_le_one hh0.le hh1 (by omega : 1 ≤ 4)
      rwa [pow_one] at this
    have h2 : M * (M * h ^ 4) ≤ M * (M * t₂) := by
      refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hM.le) hM.le
      linarith [hht₁, hht₂, h1]
    have h3 : M * (M * t₂) = 3 / 4 * (μc * κ) := by
      rw [ht₂]; exact singularEndpointOpt_cancel₂ (ne_of_gt hM)
    have h4 : 3 / 4 * (μc * κ) ≤ 3 / 4 * (mu * κ) := by
      have : μc * κ ≤ mu * κ := mul_le_mul_of_nonneg_right (by linarith) hκ0.le
      linarith
    linarith
  obtain ⟨hΔz, hRz, hgz⟩ :=
    singular_endpoint_endgame hmu0 hκ0 hM hR0 hΔ0 hΔD hsmall hmain' hslack hG0
  -- `R = 0` splits into its three nonnegative summands
  have hr1 : (0 : ℝ) ≤ P.residSq := P.residSq_nonneg
  have hr2 : (0 : ℝ) ≤ ∫ x in centralSet d ρ P.f, B.Qh h (P.f x) ^ 2 ∂unitμ :=
    setIntegral_nonneg (measurableSet_centralSet P.meas_f d ρ) fun x _ => sq_nonneg _
  have hr3 : (0 : ℝ) ≤ tailMass d ρ P.f := ENNReal.toReal_nonneg
  rw [hRdef] at hRz
  rw [hΔdef] at hΔz
  rw [hGdef] at hgz
  exact ⟨P, by linarith, by linarith, by linarith, by linarith, by linarith⟩

/-- **`thm:endpoint-optimality`, optimality clause.**  The immediate corollary of
`exists_singular_endpoint_rigidity`: if the competitor costs no more than `W_h` then in fact it costs
exactly the same, and if it costs more there is nothing to prove. -/
theorem exists_singular_endpoint_optimality (hd : 2 ≤ d) {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (hreg : ∀ v, H.degree v = d)
    (hcard : 1 ≤ H.edgeFinset.card) (hv : 2 ≤ Fintype.card V) (B : KKTFamily d) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (h : ℝ) (hh : |h| < B.h₀), 0 < h → h < δ → h ≤ 1 →
      ∀ W : Graphon, Feasible H (B.rVal h) W →
        (B.graphon hh).Ip (B.p h) ≤ W.Ip (B.p h) := by
  obtain ⟨_, -, δ, hδ, hrig⟩ := exists_singular_endpoint_rigidity hd H hreg hcard hv B
  refine ⟨δ, hδ, fun h hhb hh0 hhδ hh1 W hfeas => ?_⟩
  by_cases hcost : W.Ip (B.p h) ≤ (B.graphon hhb).Ip (B.p h)
  · obtain ⟨-, -, -, -, -, hEq⟩ := hrig h hhb hh0 hhδ hh1 W hfeas hcost
    exact hEq.ge
  · push Not at hcost
    exact hcost.le

end SingularEndpoint

end UpperTailOptimizers
