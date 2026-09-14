import UpperTailOptimizers.NonexceptionalEndpoint.Proof.ScalarCritical
import UpperTailOptimizers.NonexceptionalEndpoint.Proof.ReplicaSymmetric
import UpperTailOptimizers.NonexceptionalEndpoint.QuadraticGrowth.AnalyticExcess

/-!
# The symmetry-breaking side `p < pc(r)` of `thm:nonexceptional-endpoint`

The heart of the paper's `thm:nonexceptional-endpoint` (Theorem 4.1 of `paper/paper.tex`, proved
in Section 4.3).  Near a non-exceptional `r₀` of a
regular Lubetzky–Zhao boundary arc there are `ρ, η > 0` such that for every `r` with `|r - r₀| < ρ` and every
`p` with `pc(r) - η < p < pc(r)`:

* the optimizer of the upper-tail problem is unique up to relabelling, non-constant
  and bipodal;
* its edge density and the optimal value have the expansions

  `e(W_{p,r}) = r - λ(p,r)/A_H(r) + O(λ(p,r)²)`,
  `Φ_H(p,r)  = J_p(r) - λ(p,r)²/(2 A_H(r)) + O(λ(p,r)³)`,

  with constants uniform over the whole range of `r`.

The assembly follows the paper.  The shift identity of `NonexceptionalEndpoint/Proof/Basic.lean` turns the
reduction of Section 4.1 into the tilted scalar problem
`Φ_H(p,r) = J_p(r) + min_{0<δ<δ₀} (G_r(δ) - λ(p,r)δ)` (eq. `eq:edge-deficit-minimization`); the
chart `boundaryExcess_chart` of `thm:positive-second-variation` provides
`G_r'' = A_H(r) + O(|δ|) ≥ A_H(r)/2 > 0`; and
`tilted_critical_point` produces the unique minimiser `δ_*` together with its expansion.  Since
distinct `δ` give distinct edge densities, *every* graphon optimizer has edge density exactly
`r - δ_*`, hence is a relabelling of the single KRR-S maximizer `B_{r-δ_*, r}`.

One difference from the paper's proof: the critical point is located by the intermediate value
theorem against the strictly increasing `G_r'` rather than by the analytic implicit function
theorem; its analytic dependence on `(p,r)` is added in `NonexceptionalEndpoint/Proof/Analytic.lean`.  As in
the paper, the whole argument runs inside **one** chart, since `thm:nonexceptional-endpoint` is
local at `r₀`.
-/

namespace UpperTailOptimizers

open MeasureTheory Real Set Filter

/-! ### Two scalar estimates -/

/-- A bound for the log-odds displacement `λ(p,r)` in terms of the distance to the boundary,
uniform as long as `pc(r)` stays a margin `m` away from `0` and `1`. -/
private theorem lambdaDisp_le {d : ℕ} (M : LZBoundaryArc d) {r p m ζ : ℝ}
    (hm0 : 0 < m) (hpcm : m ≤ M.pc r) (hpc1m : m ≤ 1 - M.pc r)
    (hζm : ζ ≤ m / 2) (hlo : M.pc r - ζ < p) (hhi : p < M.pc r) :
    lambdaDisp M p r < 3 * ζ / m := by
  have hp0 : 0 < p := by linarith
  have hpc0 : 0 < M.pc r := by linarith
  have hpc1 : M.pc r < 1 := by linarith
  have hp1 : p < 1 := by linarith
  have hpm : m / 2 < p := by linarith
  have hne : (1:ℝ) - M.pc r ≠ 0 := ne_of_gt (by linarith)
  -- `log(pc r) - log p ≤ (pc r - p)/p < 2ζ/m`
  have h1 : Real.log (M.pc r) - Real.log p ≤ (M.pc r - p) / p := by
    have hlog : Real.log (M.pc r / p) ≤ M.pc r / p - 1 :=
      Real.log_le_sub_one_of_pos (div_pos hpc0 hp0)
    rw [Real.log_div (ne_of_gt hpc0) (ne_of_gt hp0)] at hlog
    have hfrac : M.pc r / p - 1 = (M.pc r - p) / p := by field_simp
    linarith [hfrac ▸ hlog]
  -- `log(1-p) - log(1-pc r) ≤ (pc r - p)/(1 - pc r) < ζ/m`
  have h2 : Real.log (1 - p) - Real.log (1 - M.pc r) ≤ (M.pc r - p) / (1 - M.pc r) := by
    have hlog : Real.log ((1 - p) / (1 - M.pc r)) ≤ (1 - p) / (1 - M.pc r) - 1 :=
      Real.log_le_sub_one_of_pos (div_pos (by linarith) (by linarith))
    rw [Real.log_div (by linarith : (1:ℝ) - p ≠ 0) hne] at hlog
    have hfrac : (1 - p) / (1 - M.pc r) - 1 = (M.pc r - p) / (1 - M.pc r) := by
      field_simp; ring
    linarith [hfrac ▸ hlog]
  have hb1 : (M.pc r - p) / p < 2 * ζ / m := by
    rw [div_lt_div_iff₀ hp0 hm0]
    nlinarith [hpm, hlo]
  have hb2 : (M.pc r - p) / (1 - M.pc r) < ζ / m := by
    rw [div_lt_div_iff₀ (by linarith) hm0]
    nlinarith [hlo, hpc1m]
  have hexp : lambdaDisp M p r
      = (Real.log (1 - p) - Real.log (1 - M.pc r)) + (Real.log (M.pc r) - Real.log p) := by
    rw [lambdaDisp, logOdds_eq_sub hp0 hp1, logOdds_eq_sub hpc0 hpc1]; ring
  have hsum : (2 * ζ / m) + (ζ / m) = 3 * ζ / m := by ring
  rw [hexp]
  linarith [h1, h2, hb1, hb2]

/-- The admissibility bound `λ < (CA/2) δ₀` for the tilted problem, from the choice of the
window width `η ≤ ηK·CA·δ₀/12`. -/
private theorem lam_small {ηK CA δ₀ η lam : ℝ}
    (hηK0 : 0 < ηK) (hCA0 : 0 < CA) (hδ₀0 : 0 < δ₀)
    (hηlam : η ≤ ηK * CA * δ₀ / 12) (hb : lam < 3 * η / ηK) :
    lam < CA / 2 * δ₀ := by
  have h12 : 12 * η ≤ ηK * CA * δ₀ := by linarith
  have h3 : 3 * η / ηK ≤ CA * δ₀ / 4 := by
    rw [div_le_div_iff₀ hηK0 (by norm_num : (0:ℝ) < 4)]
    nlinarith [h12, hηK0]
  have h4 : CA * δ₀ / 4 < CA / 2 * δ₀ := by nlinarith [mul_pos hCA0 hδ₀0]
  linarith

/-- **The edge-density expansion, scalar form.**  From `|λ - A δ_*| ≤ Mc δ_*²` and
`δ_* ≤ 2λ/CA` with `CA ≤ A`: `|λ/A - δ_*| ≤ (4 Mc / CA³) λ²`. -/
private theorem edge_expansion_bound {A CA Mch lam ds C : ℝ}
    (hCA0 : 0 < CA) (hA : CA ≤ A) (hMch0 : 0 ≤ Mch)
    (hds0 : 0 < ds) (hdsb : ds ≤ 2 * lam / CA)
    (hexp : |lam - A * ds| ≤ Mch * ds ^ 2)
    (hC : 4 * Mch / CA ^ 3 ≤ C) :
    |lam / A - ds| ≤ C * lam ^ 2 := by
  have hA0 : 0 < A := lt_of_lt_of_le hCA0 hA
  have hfac : lam / A - ds = (lam - A * ds) / A := by field_simp
  rw [hfac, abs_div, abs_of_pos hA0, div_le_iff₀ hA0]
  have h1 : ds ^ 2 ≤ (2 * lam / CA) ^ 2 := pow_le_pow_left₀ hds0.le hdsb 2
  have h2 : (2 * lam / CA) ^ 2 = 4 * lam ^ 2 / CA ^ 2 := by field_simp; ring
  have h3 : Mch * ds ^ 2 ≤ Mch * (4 * lam ^ 2 / CA ^ 2) := by
    rw [← h2]; exact mul_le_mul_of_nonneg_left h1 hMch0
  have h4 : Mch * (4 * lam ^ 2 / CA ^ 2) = 4 * Mch / CA ^ 3 * lam ^ 2 * CA := by
    field_simp
  have hnn : (0:ℝ) ≤ 4 * Mch / CA ^ 3 * lam ^ 2 := by positivity
  have hle : 4 * Mch / CA ^ 3 * lam ^ 2 ≤ C * lam ^ 2 :=
    mul_le_mul_of_nonneg_right hC (sq_nonneg lam)
  have h5 : 4 * Mch / CA ^ 3 * lam ^ 2 * CA ≤ C * lam ^ 2 * A := by
    calc 4 * Mch / CA ^ 3 * lam ^ 2 * CA ≤ C * lam ^ 2 * CA :=
          mul_le_mul_of_nonneg_right hle hCA0.le
      _ ≤ C * lam ^ 2 * A := mul_le_mul_of_nonneg_left hA (le_trans hnn hle)
  linarith [hexp, h4 ▸ h3, h5]

/-- **The value expansion, scalar form.**  From `|G - A δ_*²/2| ≤ Mc δ_*³`,
`|A δ_* - λ| ≤ Mc δ_*²`, `δ_* ≤ min(δ₀, 2λ/CA)` and `CA ≤ A`, the tilted value
`G - λ δ_*` equals `-λ²/(2A)` up to `(8 Mc/CA³ + 4 Mc² δ₀/CA⁴) λ³`.  The algebraic core is
the identity `A δ²/2 - λ δ + λ²/(2A) = (A δ - λ)²/(2A)`. -/
private theorem value_expansion_bound {A CA Mch lam ds δ₀ G C : ℝ}
    (hCA0 : 0 < CA) (hA : CA ≤ A) (hMch0 : 0 ≤ Mch) (hlam0 : 0 < lam)
    (hds0 : 0 < ds) (hdsδ₀ : ds ≤ δ₀) (hdsb : ds ≤ 2 * lam / CA)
    (hR : |G - A * ds ^ 2 / 2| ≤ Mch * ds ^ 3)
    (hY : |A * ds - lam| ≤ Mch * ds ^ 2)
    (hC : 8 * Mch / CA ^ 3 + 4 * Mch ^ 2 * δ₀ / CA ^ 4 ≤ C) :
    |G - lam * ds + lam ^ 2 / (2 * A)| ≤ C * lam ^ 3 := by
  have hA0 : 0 < A := lt_of_lt_of_le hCA0 hA
  have hid : G - lam * ds + lam ^ 2 / (2 * A)
      = (G - A * ds ^ 2 / 2) + (A * ds - lam) ^ 2 / (2 * A) := by
    field_simp; ring
  rw [hid]
  refine le_trans (abs_add_le _ _) ?_
  -- the quadratic term
  have hsq : (A * ds - lam) ^ 2 ≤ (Mch * ds ^ 2) ^ 2 := by
    have h0 : (0:ℝ) ≤ Mch * ds ^ 2 := by positivity
    nlinarith [hY, abs_nonneg (A * ds - lam), sq_abs (A * ds - lam)]
  have hq : |(A * ds - lam) ^ 2 / (2 * A)| ≤ (Mch * ds ^ 2) ^ 2 / (2 * CA) := by
    rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < 2 * A), abs_of_nonneg (sq_nonneg _),
      div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hsq, hCA0, hA, sq_nonneg (A * ds - lam), sq_nonneg (Mch * ds ^ 2)]
  -- convert the `δ_*`-powers into `λ`-powers
  have hds3 : ds ^ 3 ≤ 8 * lam ^ 3 / CA ^ 3 := by
    have h := pow_le_pow_left₀ hds0.le hdsb 3
    have h2 : (2 * lam / CA) ^ 3 = 8 * lam ^ 3 / CA ^ 3 := by field_simp; ring
    linarith [h2 ▸ h]
  have hds4 : ds ^ 4 ≤ 8 * lam ^ 3 / CA ^ 3 * δ₀ := by
    have hpow : ds ^ 4 = ds ^ 3 * ds := by ring
    rw [hpow]
    exact mul_le_mul hds3 hdsδ₀ hds0.le (by positivity)
  have hA1 : Mch * ds ^ 3 ≤ 8 * Mch / CA ^ 3 * lam ^ 3 := by
    have h := mul_le_mul_of_nonneg_left hds3 hMch0
    have heq : Mch * (8 * lam ^ 3 / CA ^ 3) = 8 * Mch / CA ^ 3 * lam ^ 3 := by
      field_simp
    linarith [heq ▸ h]
  have hB1 : (Mch * ds ^ 2) ^ 2 / (2 * CA) ≤ 4 * Mch ^ 2 * δ₀ / CA ^ 4 * lam ^ 3 := by
    have h1 : (Mch * ds ^ 2) ^ 2 = Mch ^ 2 * ds ^ 4 := by ring
    have h2 : Mch ^ 2 * ds ^ 4 ≤ Mch ^ 2 * (8 * lam ^ 3 / CA ^ 3 * δ₀) :=
      mul_le_mul_of_nonneg_left hds4 (by positivity)
    have h3 : Mch ^ 2 * (8 * lam ^ 3 / CA ^ 3 * δ₀) / (2 * CA)
        = 4 * Mch ^ 2 * δ₀ / CA ^ 4 * lam ^ 3 := by field_simp; ring
    rw [h1, ← h3]
    exact div_le_div_of_nonneg_right h2 (by positivity)
  have hCle : (8 * Mch / CA ^ 3 + 4 * Mch ^ 2 * δ₀ / CA ^ 4) * lam ^ 3 ≤ C * lam ^ 3 :=
    mul_le_mul_of_nonneg_right hC (by positivity)
  nlinarith [hR, hq, hA1, hB1, hCle]

/-! ### The symmetry-breaking side of `thm:nonexceptional-endpoint` -/

/-- **`thm:nonexceptional-endpoint`, symmetry-breaking side, chart-relative core.**  The whole
symmetry-breaking analysis, with
the analytic chart of `thm:positive-second-variation` supplied as *hypotheses* rather than
obtained internally, so that
one caller can feed the **same** chart both here and to the implicit-function step of
`NonexceptionalEndpoint/Proof/Analytic.lean`.  (Two independent calls to `boundaryExcess_chart` produce
different opaque witnesses `Gc`, and nothing can be concluded from the pair.)

Besides everything `symmetry_breaking_side` states, the conclusion exports the internal data
that the "Furthermore" clause of `thm:nonexceptional-endpoint` needs: the critical point `δ_*` itself, the fact
that it is the **unique root** of `∂_δ Gc(r,·) = λ(p,r)` on `[-δ₀, δ₀]`, the **exact** edge
identity `e(W) = r - δ_*` for every optimizer, the two value identities
`Φ = I_{p,r}(r - δ_*) = J_p(r) + Gc(r, δ_*) - λ δ_*`, the raw first-order bound
`|λ - A_H δ_*| ≤ Mch δ_*²` and the size bound `δ_* ≤ C λ`, together with the window
bookkeeping `δ₀ ≤ ρc`, `2ρ ≤ w` and `η ≤ pc(r)`. -/
theorem symmetry_breaking_core {d : ℕ} (hd : 2 ≤ d) (M : LZBoundaryArc d)
    {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (hreg : ∀ v, H.degree v = d) (hm : 1 ≤ H.edgeFinset.card)
    {r₀ w ρc Mch : ℝ} (hw0 : 0 < w) (hρc0 : 0 < ρc) (hMch0 : 0 ≤ Mch)
    (hr₀U : r₀ ∈ M.U) (hr₀ex : r₀ ≠ rStar d)
    {Gc : ℝ × ℝ → ℝ}
    (hGcA : ∀ r δ : ℝ, |r - r₀| < w → |δ| ≤ ρc → AnalyticAt ℝ Gc (r, δ))
    (hG1A : ∀ r δ : ℝ, |r - r₀| < w → |δ| ≤ ρc → AnalyticAt ℝ (dDelta Gc) (r, δ))
    (heqG : ∀ r δ : ℝ, |r - r₀| < w → 0 < δ → δ < ρc → boundaryExcess H M r δ = Gc (r, δ))
    (hG10 : ∀ r : ℝ, |r - r₀| < w → dDelta Gc (r, 0) = 0)
    (hlipG : ∀ r δ : ℝ, |r - r₀| < w → |δ| ≤ ρc →
      |dDelta (dDelta Gc) (r, δ) - AH H M r| ≤ Mch * |δ|)
    (htayG : ∀ r δ : ℝ, |r - r₀| < w → 0 < δ → δ < ρc →
      |boundaryExcess H M r δ - AH H M r * δ ^ 2 / 2| ≤ Mch * δ ^ 3) :
    ∃ ρ η δ₀ C : ℝ, 0 < ρ ∧ 0 < η ∧ 0 < δ₀ ∧ 0 ≤ C ∧ δ₀ ≤ ρc ∧ 2 * ρ ≤ w ∧
      (∀ r : ℝ, |r - r₀| < ρ → r ∈ M.U ∧ r ≠ rStar d ∧ η ≤ M.pc r) ∧
      ∀ r : ℝ, |r - r₀| < ρ → ∀ p : ℝ, M.pc r - η < p → p < M.pc r →
        0 < AH H M r ∧ 0 < lambdaDisp M p r ∧
        ∃ ds : ℝ, ds ∈ Set.Ioo (0:ℝ) δ₀ ∧
          dDelta Gc (r, ds) = lambdaDisp M p r ∧
          (∀ t ∈ Set.Icc (-δ₀) δ₀, dDelta Gc (r, t) = lambdaDisp M p r → t = ds) ∧
          phiVar H p r = reducedObjectiveReal H p (r - ds) (r ^ H.edgeFinset.card) ∧
          phiVar H p r = Jp p r + Gc (r, ds) - lambdaDisp M p r * ds ∧
          (∀ W : Graphon, Feasible H r W → W.Ip p = phiVar H p r →
            W.edgeDensity = r - ds) ∧
          |lambdaDisp M p r - AH H M r * ds| ≤ Mch * ds ^ 2 ∧
          ds ≤ C * lambdaDisp M p r ∧
          (∃ Wstar : Graphon, Feasible H r Wstar ∧ Wstar.Ip p = phiVar H p r ∧
            Wstar.edgeDensity = r - ds ∧ IsBipodal Wstar ∧
            (¬ ∃ c : ℝ, ∀ᵐ z ∂gμ, Wstar.toFun z.1 z.2 = c) ∧
            (∀ W : Graphon, Feasible H r W → W.Ip p = phiVar H p r →
              ∃ σ : ℝ → ℝ, IsRelabelling σ ∧
                ∀ᵐ z ∂gμ, W.toFun z.1 z.2 = Wstar.toFun (σ z.1) (σ z.2)) ∧
            |Wstar.edgeDensity - (r - lambdaDisp M p r / AH H M r)| ≤ C * lambdaDisp M p r ^ 2 ∧
            |phiVar H p r - (Jp p r - lambdaDisp M p r ^ 2 / (2 * AH H M r))|
              ≤ C * lambdaDisp M p r ^ 3) := by
  classical
  have hmne : H.edgeFinset.card ≠ 0 := by omega
  -- ### A compact interval `K` around `r₀`: inside the arc, inside the chart, non-exceptional
  obtain ⟨εU, hεU0, hεUsub⟩ := Metric.isOpen_iff.mp M.isOpen_U r₀ hr₀U
  have hexc0 : 0 < |r₀ - rStar d| := abs_pos.mpr (sub_ne_zero.mpr hr₀ex)
  obtain ⟨ρ, hρ_def⟩ : ∃ x : ℝ, x = min (min (w / 2) (εU / 2)) (|r₀ - rStar d| / 2) := ⟨_, rfl⟩
  have hρ0 : 0 < ρ := by
    rw [hρ_def]; exact lt_min (lt_min (by linarith) (by linarith)) (by linarith)
  have hρw : ρ ≤ w / 2 := by rw [hρ_def]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hρεU : ρ ≤ εU / 2 := by rw [hρ_def]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hρexc : ρ ≤ |r₀ - rStar d| / 2 := by rw [hρ_def]; exact min_le_right _ _
  obtain ⟨K, hK_def⟩ : ∃ S : Set ℝ, S = Set.Icc (r₀ - ρ) (r₀ + ρ) := ⟨_, rfl⟩
  have hKmem : ∀ r : ℝ, |r - r₀| ≤ ρ → r ∈ K := by
    intro r hr
    rw [hK_def]
    have h := abs_le.mp hr
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  have hKabs : ∀ r ∈ K, |r - r₀| ≤ ρ := by
    intro r hr
    rw [hK_def] at hr
    exact abs_le.mpr ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have hKsub : K ⊆ M.U := by
    intro r hr
    refine hεUsub ?_
    rw [Metric.mem_ball, Real.dist_eq]
    linarith [hKabs r hr]
  have hKc : IsCompact K := by rw [hK_def]; exact isCompact_Icc
  have hKne : K.Nonempty := ⟨r₀, hKmem r₀ (by simp; linarith)⟩
  have hKex : ∀ r ∈ K, r ≠ rStar d := by
    intro r hr hcon
    have h1 := hKabs r hr
    have h2 : |r₀ - rStar d| ≤ |r₀ - r| + |r - rStar d| := abs_sub_le _ _ _
    rw [hcon, sub_self, abs_zero, add_zero, abs_sub_comm] at h2
    rw [hcon] at h1
    rw [abs_sub_comm] at h1
    linarith
  have hKw : ∀ r ∈ K, |r - r₀| < w := fun r hr => by linarith [hKabs r hr]
  -- ### Uniform second-variation and reduction data on `K`
  obtain ⟨CA, -, -, hCA0, -, -, -, hAHlow, -⟩ :=
    boundaryExcess_taylor hd M hKsub hKc hKne hKex H hreg hm
  obtain ⟨ρ₀, hρ₀0, What, hfam, hcore⟩ :=
    reduction_core_uniform hd M hKsub hKc hKne hKex H hreg hm
  obtain ⟨ηK, hηK0, -, hηK⟩ := arc_uniform_bounds M hKsub hKc hKne
  -- ### The confinement radius `δ₀`
  obtain ⟨δ₀, hδ₀_def⟩ : ∃ x : ℝ, x = min (min ρc ρ₀) (CA / (2 * (Mch + 1))) := ⟨_, rfl⟩
  have hδ₀0 : 0 < δ₀ := by
    rw [hδ₀_def]; exact lt_min (lt_min hρc0 hρ₀0) (by positivity)
  have hδ₀ρc : δ₀ ≤ ρc := by rw [hδ₀_def]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hδ₀ρ₀ : δ₀ ≤ ρ₀ := by rw [hδ₀_def]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hδ₀Mc : Mch * δ₀ ≤ CA / 2 := by
    have h1 : δ₀ ≤ CA / (2 * (Mch + 1)) := by rw [hδ₀_def]; exact min_le_right _ _
    have hden : (0:ℝ) < 2 * (Mch + 1) := by linarith
    have h2 : Mch * δ₀ ≤ Mch * (CA / (2 * (Mch + 1))) := mul_le_mul_of_nonneg_left h1 hMch0
    have h3 : Mch * (CA / (2 * (Mch + 1))) ≤ CA / 2 := by
      rw [mul_comm, div_mul_eq_mul_div, div_le_div_iff₀ hden (by norm_num : (0:ℝ) < 2)]
      nlinarith [hCA0, hMch0]
    linarith
  -- ### The window width `η`
  obtain ⟨ηred, hηred0, -, hcore'⟩ := hcore δ₀ hδ₀0 hδ₀ρ₀
  obtain ⟨η, hη_def⟩ : ∃ x : ℝ, x = min (min ηred (ηK / 2)) (ηK * CA * δ₀ / 12) := ⟨_, rfl⟩
  have hη0 : 0 < η := by
    rw [hη_def]; exact lt_min (lt_min hηred0 (by linarith)) (by positivity)
  have hηred : η ≤ ηred := by rw [hη_def]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hηηK : η ≤ ηK / 2 := by rw [hη_def]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hηlam : η ≤ ηK * CA * δ₀ / 12 := by rw [hη_def]; exact min_le_right _ _
  -- ### The expansion constant
  obtain ⟨C, hC_def⟩ : ∃ x : ℝ,
      x = 4 * Mch / CA ^ 3 + (8 * Mch / CA ^ 3 + 4 * Mch ^ 2 * δ₀ / CA ^ 4)
        + 2 / CA := ⟨_, rfl⟩
  have hC0 : 0 ≤ C := by rw [hC_def]; positivity
  have hCedge : 4 * Mch / CA ^ 3 ≤ C := by
    rw [hC_def]
    have h1 : (0:ℝ) ≤ 8 * Mch / CA ^ 3 + 4 * Mch ^ 2 * δ₀ / CA ^ 4 := by positivity
    have h2 : (0:ℝ) ≤ 2 / CA := by positivity
    linarith
  have hCval : 8 * Mch / CA ^ 3 + 4 * Mch ^ 2 * δ₀ / CA ^ 4 ≤ C := by
    rw [hC_def]
    have h1 : (0:ℝ) ≤ 4 * Mch / CA ^ 3 := by positivity
    have h2 : (0:ℝ) ≤ 2 / CA := by positivity
    linarith
  have hCds : 2 / CA ≤ C := by
    rw [hC_def]
    have h1 : (0:ℝ) ≤ 4 * Mch / CA ^ 3 := by positivity
    have h2 : (0:ℝ) ≤ 8 * Mch / CA ^ 3 + 4 * Mch ^ 2 * δ₀ / CA ^ 4 := by positivity
    linarith
  refine ⟨ρ, η, δ₀, C, hρ0, hη0, hδ₀0, hC0, hδ₀ρc, by linarith [hρw], ?_, ?_⟩
  · -- the window bookkeeping
    intro r hrρ
    have hrK : r ∈ K := hKmem r hrρ.le
    obtain ⟨-, -, -, -, hηKpc, -⟩ := hηK r hrK
    exact ⟨hKsub hrK, hKex r hrK, by linarith [hηηK]⟩
  intro r hrρ p hp_lo hp_hi
  have hrK : r ∈ K := hKmem r hrρ.le
  have hrU : r ∈ M.U := hKsub hrK
  have hrw : |r - r₀| < w := hKw r hrK
  obtain ⟨hpc0, hpcr, hr1, -⟩ := M.ordering r hrU
  have hr0 : 0 < r := lt_trans hpc0 hpcr
  obtain ⟨hηKr, hr1ηK, -, -, hηKpc, -⟩ := hηK r hrK
  have hp0 : 0 < p := by linarith
  have hp1 : p < 1 := by linarith
  have hpr : p < r := lt_trans hp_hi hpcr
  -- opaque names for `λ(p,r)` and `A_H(r)`, so that the arithmetic tactics below never
  -- unfold them (the definitions expand to logarithms and a `limUnder`)
  obtain ⟨lam, hlam_def⟩ : ∃ x : ℝ, x = lambdaDisp M p r := ⟨_, rfl⟩
  obtain ⟨AHr, hAHr_def⟩ : ∃ x : ℝ, x = AH H M r := ⟨_, rfl⟩
  rw [← hlam_def, ← hAHr_def]
  have hAHr : CA ≤ AHr := by rw [hAHr_def]; exact hAHlow r hrK
  have hAH0 : 0 < AHr := lt_of_lt_of_le hCA0 hAHr
  -- ### The tilt `λ` and its size
  have hlam0 : 0 < lam := by rw [hlam_def]; exact lambdaDisp_pos M hrU hp0 hp_hi
  have hlamlt : lam < CA / 2 * δ₀ := by
    rw [hlam_def]
    exact lam_small hηK0 hCA0 hδ₀0 hηlam
      (lambdaDisp_le M hηK0 hηKpc (by linarith : ηK ≤ 1 - M.pc r) hηηK hp_lo hp_hi)
  -- ### The scalar critical point
  have hmemδ : ∀ t : ℝ, t ∈ Set.Icc (-δ₀) δ₀ → |t| ≤ ρc :=
    fun t ht => le_trans (abs_le.mpr ⟨ht.1, ht.2⟩) hδ₀ρc
  have hd1 : ∀ t ∈ Set.Icc (-δ₀) δ₀, HasDerivAt (fun s => Gc (r, s)) (dDelta Gc (r, t)) t :=
    fun t ht => hasDerivAt_dDelta (hGcA r t hrw (hmemδ t ht)).differentiableAt
  have hd2 : ∀ t ∈ Set.Icc (-δ₀) δ₀,
      HasDerivAt (fun s => dDelta Gc (r, s)) (dDelta (dDelta Gc) (r, t)) t :=
    fun t ht => hasDerivAt_dDelta (hG1A r t hrw (hmemδ t ht)).differentiableAt
  have hg2A : ∀ t ∈ Set.Icc (-δ₀) δ₀,
      |dDelta (dDelta Gc) (r, t) - AHr| ≤ Mch * |t| := by
    intro t ht
    rw [hAHr_def]
    exact hlipG r t hrw (hmemδ t ht)
  have hg2 : ∀ t ∈ Set.Icc (-δ₀) δ₀, CA / 2 ≤ dDelta (dDelta Gc) (r, t) := by
    intro t ht
    have habs : |t| ≤ δ₀ := abs_le.mpr ⟨ht.1, ht.2⟩
    have hb : Mch * |t| ≤ CA / 2 := le_trans (mul_le_mul_of_nonneg_left habs hMch0) hδ₀Mc
    have h2 := abs_le.mp (le_trans (hg2A t ht) hb)
    linarith [h2.1]
  obtain ⟨ds, hds, hdseq, hdsle, hdsmin, hdsexp, hdsroot⟩ :=
    tilted_critical_point hδ₀0 (by linarith : (0:ℝ) < CA / 2) hd1 hd2 (hG10 r hrw) hg2 hg2A
      hlam0 hlamlt
  have hds0 : 0 < ds := hds.1
  have hdsδ₀ : ds < δ₀ := hds.2
  have hdsρc : ds < ρc := lt_of_lt_of_le hdsδ₀ hδ₀ρc
  have hdsbound : ds ≤ 2 * lam / CA := by
    have heq : lam / (CA / 2) = 2 * lam / CA := by field_simp
    linarith [heq ▸ hdsle]
  -- ### The reduction, tilted by `λ`
  obtain ⟨hF_lb, ⟨W0, hW0feas, hW0opt⟩, huniv⟩ :=
    hcore' r hrK p (by linarith [hηred]) hp_hi
  have hFshift : ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      reducedObjectiveReal H p (r - δ) (r ^ H.edgeFinset.card) - Jp p r
        = Gc (r, δ) - lam * δ := by
    intro δ hδ0 hδlt
    rw [hlam_def, reducedObjective_sub_Jp_eq_boundaryExcess H M hrU hp0 hp1,
      heqG r δ hrw hδ0 (lt_of_lt_of_le hδlt hδ₀ρc)]
  -- every optimizer has edge density exactly `r - δ_*`
  have hedge : ∀ W : Graphon, Feasible H r W → W.Ip p = phiVar H p r →
      W.edgeDensity = r - ds := by
    intro W hWfeas hWopt
    obtain ⟨hWmem, hWF, -, -, -⟩ := huniv W hWfeas hWopt
    have hδW0 : 0 < r - W.edgeDensity := by linarith [hWmem.2]
    have hδWlt : r - W.edgeDensity < δ₀ := by linarith [hWmem.1]
    have hWe : W.edgeDensity = r - (r - W.edgeDensity) := by ring
    have hmin : ∀ δ ∈ Set.Ioo (0:ℝ) δ₀,
        Gc (r, r - W.edgeDensity) - lam * (r - W.edgeDensity)
          ≤ Gc (r, δ) - lam * δ := by
      intro δ hδ
      have h1 : phiVar H p r ≤ reducedObjectiveReal H p (r - δ) (r ^ H.edgeFinset.card) :=
        hF_lb (r - δ) ⟨by linarith [hδ.2], by linarith [hδ.1]⟩
      rw [← hFshift δ hδ.1 hδ.2, ← hFshift (r - W.edgeDensity) hδW0 hδWlt, ← hWe, ← hWF]
      linarith
    have hEq : r - W.edgeDensity = ds := by
      by_contra hne
      have h1 := hdsmin (r - W.edgeDensity) ⟨hδW0, hδWlt⟩ hne
      have h2 := hmin ds hds
      linarith
    linarith [hEq]
  -- ### The optimizer `W_*`
  have hmemIoo : r - ds ∈ Set.Ioo (r - ρ₀) r := ⟨by linarith [hδ₀ρ₀], by linarith⟩
  obtain ⟨hWse, hWsfeas, hWsbip, hWst, -⟩ := hfam r hrK (r - ds) hmemIoo
  obtain ⟨-, -, -, hW0star, -⟩ := huniv W0 hW0feas hW0opt
  have hW0e : W0.edgeDensity = r - ds := hedge W0 hW0feas hW0opt
  have hWsopt : (What (r - ds) r).Ip p = phiVar H p r := by rw [← hW0e]; exact hW0star
  -- the two value identities
  have hPhiF : phiVar H p r = reducedObjectiveReal H p (r - ds) (r ^ H.edgeFinset.card) := by
    obtain ⟨-, hWF, -, -, -⟩ := huniv W0 hW0feas hW0opt
    rw [hW0e] at hWF
    exact hWF
  have hPhi : phiVar H p r - Jp p r = Gc (r, ds) - lam * ds := by
    rw [hPhiF, hFshift ds hds0 hdsδ₀]
  refine ⟨hAH0, hlam0, ds, hds, hdseq, hdsroot, hPhiF, by linarith [hPhi], hedge, hdsexp,
    ?_, What (r - ds) r, hWsfeas, hWsopt, hWse, hWsbip, ?_, ?_, ?_, ?_⟩
  · -- `δ_* ≤ C λ`
    have h1 : 2 * lam / CA = 2 / CA * lam := by ring
    have h2 : 2 / CA * lam ≤ C * lam := mul_le_mul_of_nonneg_right hCds hlam0.le
    linarith [h1 ▸ hdsbound]
  · -- non-constant: edge density `r - δ_* < r` but `H`-density `r^m`
    rintro ⟨c, hc⟩
    have he : (What (r - ds) r).edgeDensity = c := edgeDensity_ae_const _ hc
    have ht : (What (r - ds) r).tDensity H = c ^ H.edgeFinset.card :=
      tDensity_ae_const _ H hc
    rw [hWse] at he
    rw [hWst, ← he] at ht
    have hc0 : (0:ℝ) ≤ r - ds := by
      rw [← hWse]; exact edgeDensity_nonneg _
    have hcontra : r = r - ds := by
      rcases lt_trichotomy (r - ds) r with h | h | h
      · exact absurd ht.symm (ne_of_lt (pow_lt_pow_left₀ h hc0 hmne))
      · exact h.symm
      · exact absurd ht (ne_of_lt (pow_lt_pow_left₀ h hr0.le hmne))
    linarith
  · -- uniqueness up to relabelling
    intro W hWfeas hWopt
    obtain ⟨-, -, -, -, σ, hσ, hrel⟩ := huniv W hWfeas hWopt
    rw [hedge W hWfeas hWopt] at hrel
    exact ⟨σ, hσ, hrel⟩
  · -- the edge-density expansion
    rw [hWse]
    have hkey : |r - ds - (r - lam / AHr)| = |lam / AHr - ds| := by
      congr 1; ring
    rw [hkey]
    exact edge_expansion_bound hCA0 hAHr hMch0 hds0 hdsbound hdsexp hCedge
  · -- the value expansion
    have hR : |Gc (r, ds) - AHr * ds ^ 2 / 2| ≤ Mch * ds ^ 3 := by
      have h := htayG r ds hrw hds0 hdsρc
      rw [heqG r ds hrw hds0 hdsρc, ← hAHr_def] at h
      exact h
    have hY : |AHr * ds - lam| ≤ Mch * ds ^ 2 := by
      rw [abs_sub_comm]; exact hdsexp
    have hgoal := value_expansion_bound hCA0 hAHr hMch0 hlam0 hds0 hdsδ₀.le hdsbound hR hY hCval
    have hrewrite : phiVar H p r - (Jp p r - lam ^ 2 / (2 * AHr))
        = Gc (r, ds) - lam * ds + lam ^ 2 / (2 * AHr) := by
      linarith [hPhi]
    rw [hrewrite]
    exact hgoal

/-- **`thm:nonexceptional-endpoint`: the symmetry-breaking side.**  Near a non-exceptional `r₀` of a
regular Lubetzky–Zhao boundary arc there are `ρ, η > 0` and a constant `C` such that for every `r` with
`|r - r₀| < ρ` and every `p ∈ (pc(r) - η, pc(r))` there is a graphon `W_*` which is

* an optimizer of the upper-tail problem, **bipodal** and **non-constant**;
* the optimizer **up to relabelling**: every optimizer is `W_*` relabelled;

and, writing `λ = λ(p,r)` for the log-odds displacement,

* `|e(W) - (r - λ/A_H(r))| ≤ C λ²` for every optimizer `W`;
* `|Φ_H(p,r) - (J_p(r) - λ²/(2 A_H(r)))| ≤ C λ³`,

these last two together with `A_H(r) > 0`, so that the divisions are not the degenerate
`x / 0 = 0` reading.  The constants `ρ, η, C` do not depend on `r` or `p` in the stated
range.  This is `symmetry_breaking_core` with the second-variation chart supplied by
`boundaryExcess_chart` and the chart-relative data projected away. -/
theorem symmetry_breaking_side {d : ℕ} (hd : 2 ≤ d) (M : LZBoundaryArc d)
    {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (hreg : ∀ v, H.degree v = d) (hm : 1 ≤ H.edgeFinset.card)
    {r₀ : ℝ} (hr₀U : r₀ ∈ M.U) (hr₀ex : r₀ ≠ rStar d) :
    ∃ ρ η C : ℝ, 0 < ρ ∧ 0 < η ∧ 0 ≤ C ∧
      ∀ r : ℝ, |r - r₀| < ρ → ∀ p : ℝ, M.pc r - η < p → p < M.pc r →
        0 < AH H M r ∧
        ∃ Wstar : Graphon, Feasible H r Wstar ∧ Wstar.Ip p = phiVar H p r ∧
          IsBipodal Wstar ∧
          (¬ ∃ c : ℝ, ∀ᵐ z ∂gμ, Wstar.toFun z.1 z.2 = c) ∧
          (∀ W : Graphon, Feasible H r W → W.Ip p = phiVar H p r →
            ∃ σ : ℝ → ℝ, IsRelabelling σ ∧
              ∀ᵐ z ∂gμ, W.toFun z.1 z.2 = Wstar.toFun (σ z.1) (σ z.2)) ∧
          |Wstar.edgeDensity - (r - lambdaDisp M p r / AH H M r)| ≤ C * lambdaDisp M p r ^ 2 ∧
          |phiVar H p r - (Jp p r - lambdaDisp M p r ^ 2 / (2 * AH H M r))|
            ≤ C * lambdaDisp M p r ^ 3 := by
  classical
  obtain ⟨w, ρc, Mch, hw0, hρc0, hMch0, Gc, hGcA, hG1A, heqG, -, hG10, -, hlipG, htayG⟩ :=
    boundaryExcess_chart hd M H hreg hm hr₀U hr₀ex
  obtain ⟨ρ, η, δ₀, C, hρ0, hη0, -, hC0, -, -, -, hmain⟩ :=
    symmetry_breaking_core hd M H hreg hm hw0 hρc0 hMch0 hr₀U hr₀ex
      hGcA hG1A heqG hG10 hlipG htayG
  refine ⟨ρ, η, C, hρ0, hη0, hC0, ?_⟩
  intro r hrρ p hp_lo hp_hi
  obtain ⟨hAH0, -, ds, -, -, -, -, -, -, -, -, Wstar, hWfeas, hWopt, -, hWbip, hWnc,
    hWrel, hWedge, hWval⟩ := hmain r hrρ p hp_lo hp_hi
  exact ⟨hAH0, Wstar, hWfeas, hWopt, hWbip, hWnc, hWrel, hWedge, hWval⟩

end UpperTailOptimizers
