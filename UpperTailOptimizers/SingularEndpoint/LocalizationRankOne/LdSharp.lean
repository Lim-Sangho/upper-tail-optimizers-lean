import UpperTailOptimizers.SingularEndpoint.LocalizationRankOne.FactorMain
import UpperTailOptimizers.SingularEndpoint.LocalizationRankOne.FactorTail

/-!
# The sharp moment bound in the proof of `lem:localization-rank-one` (Section 5)

`SingularEndpoint/LocalizationRankOne/FamilyLocalization.lean` instantiates the coercive step `gamInt_localized` along the
singular endpoint family for `eq:graphon-quartic-localization` only: it drops the
nonnegative moment term `b₀(∫W^d - r_h^d)` before feeding the quartic bound
`eq:endpoint-gap-quartic-bound` in.  This file keeps that term instead and drops
`𝒢_Γ/2 ≥ 0` (Lean notation, `𝒢_Γ = ∫Γ_d(W)`), which gives the moment half of
`eq:moment-and-cost-gap-bounds` in the proof of the lemma,

`0 ≤ ∫W^d - r_h^d ≤ Mh⁴`   (the sharp `∫W^d` bound),

and then draws the two consequences the Lean uses downstream.

## What is proved

* `family_ld_sharp` — **the sharp `∫W^d` bound** along the family.  The lower bound is
  generalized Hölder at feasibility (`holder_moment`); the upper bound is `gamInt_localized`
  at `b₀ = β_d/2` with the same three family rates that
  `family_localization` uses (`tendsto_gamInt_graphon`, `tendsto_ell_coeff`, and
  `𝒱_{R,h} = ∫R_d(W_h) = O(h²)` through `edge_eq_moment_sub_rdInt`).
* `family_holder_deficit` — the **Hölder deficit** `(∫W^d)^{m/d} - t(H,W) ≤ Kh⁴`, from
  feasibility `t(H,W) ≥ r_h^m` and the display above.
* `family_factor_clause` — a sharpened **Factor clause** along the family, not in the paper
  (whose `eq:rank-one-reduction-bounds` has `‖E‖₂ ≤ C_d h` and `|q(f) - q_h| ≤ C_d h²`): the
  decomposition produced by `localization_rankOne` satisfies `‖E‖₂ ≤ Mh²` and
  `|∫f^d - q_h| ≤ Mh⁴`.  This is `exists_factorTail_factor_clause` with all three of its
  `O(h⁴)` hypotheses discharged.

Together with `family_localization`, `family_localization_sq` and `family_factor_tail_mass`
this gives a family-level form of `lem:localization-rank-one` with these sharper rates; the
statement in the paper's form is `localization_rank_one_reduction`
(`SingularEndpoint/LocalizationRankOne/LocalizationRankOne.lean`).

## The mean-value step

The one genuinely new analytic ingredient is `ldSharp_rpow_increment`:

`B^a - A^a ≤ a(B - A)`   for `0 ≤ A ≤ B ≤ 1` and `a ≥ 1`.

It is Bernoulli's inequality `1 + a s ≤ (1+s)^a` (`Real.one_add_mul_self_le_rpow_one_add`) at
`s = A/B - 1`, which is the tangent-line bound at the **right** endpoint `B` — the correct end
for a convex increment.  No lower bound on the base point is needed, because the base point
`B = ∫W^d` of a graphon is at most `1`, so `B^{a-1} ≤ 1` and the derivative factor is bounded by
`a` outright.  The paper has no counterpart of this step: its proof of
`lem:localization-rank-one` does not pass through the Hölder deficit.

## Paper results realised

* the moment half of `eq:moment-and-cost-gap-bounds` along the family — `family_ld_sharp`;
* `eq:generalized-holder` at the family, turned into the Hölder deficit bound consumed by the
  Lean's combined stability inequality (no counterpart in the paper) —
  `family_holder_deficit`;
* the sharpened Factor clause (beyond the paper) — `family_factor_clause`.

## Axiom footprint

Every theorem here carries `generalized_holder` in addition to
`[propext, Classical.choice, Quot.sound]`, inherited from `holder_moment` exactly as
`family_localization` does.  No new axiom is introduced.

## Contents

* `family_ld_sharp`, `family_holder_deficit`, `family_factor_clause`.

That is the whole interface.
-/

namespace UpperTailOptimizers

open Filter MeasureTheory Topology

variable {d : ℕ}

/-! ## The right-hand side of `eq:graphon-cost-decomposition` along the family -/

/-- **The `O(h⁴)` input from the family expansions, packaged once.**

There is a Cauchy–Schwarz constant `C_d` for `R_d² ≤ C_dΓ_d` and a width `δ` such
that on `0 < h < δ` both

* the coefficient `β_d + Λ_h/(d r_*^{d-1})` of `eq:graphon-cost-decomposition` exceeds
  `β_d/2` (because `Λ_h → 0`), and
* the whole right-hand side of `gamInt_localized` at the candidate `W_h`,
  `𝒢_{Γ,h} + |Λ_h||𝒱_{R,h}| + C_dΛ_h²/2` (Lean notation: `𝒢_{Γ,h} = ∫Γ_d(W_h)`,
  `𝒱_{R,h} = ∫R_d(W_h)`), is at most `Nh⁴`.

The three rates fed in are `tendsto_gamInt_graphon` (`𝒢_{Γ,h}/h⁴ → d³/3`),
`tendsto_ell_coeff` (`Λ_h → 0` and `Λ_h/h² → L₂`) and, through `edge_eq_moment_sub_rdInt` at
the saturated moment `∫∫W_h^d = r_h^d`, the composite `𝒱_{R,h}/h²` of `tendsto_rVal_coeff`
and `graphon_edge_gap`.  This is exactly the block that `family_localization` performs inline;
it is isolated here because the moment bound needs the *same* block with a different final
step. -/
theorem ldSharp_family_rhs (hd : 2 ≤ d) (B : KKTFamily d) :
    ∃ Cc : ℝ, 0 < Cc ∧ (∀ X : Graphon, RdInt d X ^ 2 ≤ Cc * GamInt d X) ∧
      ∃ N : ℝ, 0 < N ∧ ∃ δ : ℝ, 0 < δ ∧
        ∀ (h : ℝ) (hh : |h| < B.h₀), 0 < h → h < δ →
          (betaD d / 2 ≤ betaD d
              + (ell (B.p h) - ell (pStar d)) / ((d : ℝ) * rStar d ^ (d - 1))) ∧
            GamInt d (B.graphon hh)
                + |ell (B.p h) - ell (pStar d)| * |RdInt d (B.graphon hh)|
                + Cc * (ell (B.p h) - ell (pStar d)) ^ 2 / 2
              ≤ N * h ^ 4 := by
  classical
  obtain ⟨Cc, hCc0, hVG⟩ := RdInt_sq_le_gamInt (d := d) hd
  refine ⟨Cc, hCc0, hVG, ?_⟩
  -- Arbitrary representatives of the three `h`-dependent family quantities.
  obtain ⟨F, hF⟩ : ∃ F : ℝ → ℝ, ∀ (h : ℝ) (hh : |h| < B.h₀), F h = GamInt d (B.graphon hh) :=
    ⟨fun h => if hh : |h| < B.h₀ then GamInt d (B.graphon hh) else 0, fun _ hh => dif_pos hh⟩
  obtain ⟨G, hG⟩ : ∃ G : ℝ → ℝ,
      ∀ (h : ℝ) (hh : |h| < B.h₀), G h = (B.graphon hh).edgeDensity :=
    ⟨fun h => if hh : |h| < B.h₀ then (B.graphon hh).edgeDensity else 0, fun _ hh => dif_pos hh⟩
  obtain ⟨R, hR⟩ : ∃ R : ℝ → ℝ, ∀ (h : ℝ) (hh : |h| < B.h₀), R h = RdInt d (B.graphon hh) :=
    ⟨fun h => if hh : |h| < B.h₀ then RdInt d (B.graphon hh) else 0, fun _ hh => dif_pos hh⟩
  -- `𝒢_{Γ,h}/h⁴ → d³/3`.
  have hFlim : Tendsto (fun h : ℝ => F h / h ^ 4) (𝓝[≠] (0 : ℝ)) (𝓝 ((d : ℝ) ^ 3 / 3)) :=
    tendsto_gamInt_graphon hd B hF
  -- `(r_h^d - r_*^d)/h²` converges, by the geometric-sum factorisation.
  have hrpow : Tendsto (fun h : ℝ => (B.rVal h ^ d - rStar d ^ d) / h ^ 2) (𝓝[≠] (0 : ℝ))
      (𝓝 (-(2 * (4 * (d : ℝ) - 1) / 3) * ((d : ℝ) * rStar d ^ (d - 1)))) := by
    have hcof := tendsto_geom_sum₂ (f := B.rVal) (g := fun _ : ℝ => rStar d) d
      (tendsto_rVal hd B) tendsto_const_nhds
    refine ((tendsto_rVal_coeff B hd).mul hcof).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with h hmem
    have hne : h ≠ 0 := hmem
    rw [pow_sub_pow_eq (B.rVal h) (rStar d) d]
    field_simp
  -- `(e(W_h) - r_*)/h²` converges.
  have hedge : Tendsto (fun h : ℝ => (G h - rStar d) / h ^ 2) (𝓝[≠] (0 : ℝ))
      (𝓝 (-((d : ℝ) - 1) + -(2 * (4 * (d : ℝ) - 1) / 3))) := by
    refine ((graphon_edge_gap B hd hG).add (tendsto_rVal_coeff B hd)).congr'
      (Filter.Eventually.of_forall fun h => ?_)
    rw [← add_div]
    congr 1
    ring
  -- Hence `𝒱_{R,h}/h²` converges, by the edge/moment identity at the saturated moment.
  have hRlim : Tendsto (fun h : ℝ => R h / h ^ 2) (𝓝[≠] (0 : ℝ))
      (𝓝 (-(2 * (4 * (d : ℝ) - 1) / 3) * ((d : ℝ) * rStar d ^ (d - 1))
            / ((d : ℝ) * rStar d ^ (d - 1))
          - (-((d : ℝ) - 1) + -(2 * (4 * (d : ℝ) - 1) / 3)))) := by
    refine ((hrpow.div_const ((d : ℝ) * rStar d ^ (d - 1))).sub hedge).congr' ?_
    filter_upwards [eventually_window B] with h hw
    rw [hR h hw, hG h hw]
    have he := edge_eq_moment_sub_rdInt hd (B.graphon hw)
    rw [KKTFamily.graphon_Wmoment_eq_rVal_pow hd hw] at he
    rw [he, div_right_comm, div_sub_div_same, sub_sub_cancel]
  -- The three eventual bounds.
  obtain ⟨M₁, hM₁0, hM₁⟩ :=
    exists_eventual_bound (fun _ hne => Even.pow_pos (by norm_num) hne) hFlim
  obtain ⟨M₂, hM₂0, hM₂⟩ :=
    exists_eventual_bound (f := fun h : ℝ => ell (B.p h) - ell (pStar d)) (n := 2)
      (fun _ hne => Even.pow_pos (by norm_num) hne) ((tendsto_ell_coeff B hd).2)
  obtain ⟨M₃, hM₃0, hM₃⟩ :=
    exists_eventual_bound (fun _ hne => Even.pow_pos (by norm_num) hne) hRlim
  -- The coefficient of `eq:graphon-cost-decomposition` stays above `β_d/2`.
  have hbpos : 0 < betaD d := betaD_pos hd
  have hb0ev : ∀ᶠ h in 𝓝[≠] (0 : ℝ), betaD d / 2 ≤ betaD d
      + (ell (B.p h) - ell (pStar d)) / ((d : ℝ) * rStar d ^ (d - 1)) := by
    have h0 : Tendsto
        (fun h : ℝ => |(ell (B.p h) - ell (pStar d)) / ((d : ℝ) * rStar d ^ (d - 1))|)
        (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
      have h1 := ((tendsto_ell_coeff B hd).1.div_const ((d : ℝ) * rStar d ^ (d - 1))).abs
      simpa using h1
    filter_upwards [h0.eventually_lt_const (show (0 : ℝ) < betaD d / 2 by linarith)] with h hlt
    linarith [(abs_lt.mp hlt).1]
  -- Merge the four eventual statements into one punctured ball.
  have hev : ∀ᶠ h in 𝓝[≠] (0 : ℝ),
      |F h| ≤ M₁ * h ^ 4 ∧ |ell (B.p h) - ell (pStar d)| ≤ M₂ * h ^ 2 ∧
        |R h| ≤ M₃ * h ^ 2 ∧ betaD d / 2 ≤ betaD d
          + (ell (B.p h) - ell (pStar d)) / ((d : ℝ) * rStar d ^ (d - 1)) := by
    filter_upwards [hM₁, hM₂, hM₃, hb0ev] with h a1 a2 a3 a4
    exact ⟨a1, a2, a3, a4⟩
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
  obtain ⟨δ, hδ, hmem⟩ := hev
  have hnum : 0 < M₁ + M₂ * M₃ + Cc * M₂ ^ 2 / 2 := by
    have h1 : 0 < M₂ * M₃ := mul_pos hM₂0 hM₃0
    have h2 : 0 < Cc * M₂ ^ 2 := mul_pos hCc0 (pow_pos hM₂0 2)
    linarith
  refine ⟨M₁ + M₂ * M₃ + Cc * M₂ ^ 2 / 2, hnum, δ, hδ, ?_⟩
  intro h hh hpos hlt
  have hdist : dist h (0 : ℝ) < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hpos]
    exact hlt
  obtain ⟨hb1, hb2, hb3, hb4⟩ := hmem hdist (ne_of_gt hpos)
  refine ⟨hb4, ?_⟩
  have h2 : (0 : ℝ) < h ^ 2 := pow_pos hpos 2
  have hM2h : (0 : ℝ) ≤ M₂ * h ^ 2 := (mul_pos hM₂0 h2).le
  have hGam : F h ≤ M₁ * h ^ 4 := le_trans (le_abs_self _) hb1
  have hprod : |ell (B.p h) - ell (pStar d)| * |R h| ≤ M₂ * h ^ 2 * (M₃ * h ^ 2) :=
    mul_le_mul hb2 hb3 (abs_nonneg _) hM2h
  have hsq : (ell (B.p h) - ell (pStar d)) ^ 2 ≤ (M₂ * h ^ 2) ^ 2 := by
    have habs := sq_abs (ell (B.p h) - ell (pStar d))
    nlinarith [abs_nonneg (ell (B.p h) - ell (pStar d)), hb2, hM2h]
  have hCcs : Cc * (ell (B.p h) - ell (pStar d)) ^ 2 / 2 ≤ Cc * (M₂ * h ^ 2) ^ 2 / 2 := by
    linarith [mul_le_mul_of_nonneg_left hsq hCc0.le]
  rw [← hF h hh, ← hR h hh]
  nlinarith [hGam, hprod, hCcs]

/-! ## the sharp `∫W^d` bound -/

/-- **the sharp `∫W^d` bound along the singular endpoint family.**

There are `M > 0` and `δ > 0` such that for every `0 < h < δ` in the family window, every
graphon `W` feasible at `(p_h, r_h)` and no more expensive than the candidate `W_h` satisfies

`0 ≤ ∫W^d - r_h^d ≤ Mh⁴`.

The lower bound is generalized Hölder at feasibility (`holder_moment`).  The upper bound is
`gamInt_localized` at `b₀ = β_d/2`, keeping the moment term and discarding `𝒢_Γ/2 ≥ 0` — the
mirror image of `family_localization`, which discards the moment term and keeps `𝒢_Γ/2`.  The
constant is `M = 2N/β_d` with `N` the `O(h⁴)` bound of `ldSharp_family_rhs`. -/
theorem family_ld_sharp (hd : 2 ≤ d) {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (hreg : ∀ v, H.degree v = d)
    (hm : 1 ≤ H.edgeFinset.card) (B : KKTFamily d) :
    ∃ M : ℝ, 0 < M ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ (h : ℝ) (hh : |h| < B.h₀), 0 < h → h < δ →
        ∀ W : Graphon, B.rVal h ^ H.edgeFinset.card ≤ W.tDensity H →
          W.Ip (B.p h) ≤ (B.graphon hh).Ip (B.p h) →
          0 ≤ W.Wmoment d - B.rVal h ^ d ∧ W.Wmoment d - B.rVal h ^ d ≤ M * h ^ 4 := by
  obtain ⟨Cc, hCc0, hVG, N, hN0, δ, hδ, hrhs⟩ := ldSharp_family_rhs hd B
  have hbpos : 0 < betaD d := betaD_pos hd
  refine ⟨2 * N / betaD d, div_pos (by linarith) hbpos, δ, hδ, ?_⟩
  intro h hh hpos hlt W hfeas hcost
  have hlow : B.rVal h ^ d ≤ W.Wmoment d :=
    holder_moment H hreg hd W (KKTFamily.rVal_pos hd hh).le hm hfeas
  obtain ⟨hb4, hbnd⟩ := hrhs h hh hpos hlt
  have hkey := gamInt_localized hd H hreg hm (B.p_mem h hh).1 (B.p_mem h hh).2
    (KKTFamily.rVal_pos hd hh).le hfeas
    (KKTFamily.graphon_Wmoment_eq_rVal_pow hd hh) hcost
    (show (0 : ℝ) < betaD d / 2 by linarith) hCc0 hVG hb4
  have hGam : 0 ≤ GamInt d W := gamInt_nonneg hd W
  refine ⟨by linarith, ?_⟩
  rw [div_mul_eq_mul_div, le_div_iff₀ hbpos]
  nlinarith [hkey, hGam, hbnd]

/-! ## The Hölder deficit -/

/-- `∫W^d ≤ 1` for a graphon: the integrand `W^d` is at most `1` and `gμ` is a probability
measure.  This is what makes the derivative factor of the mean-value step below harmless. -/
private theorem ldSharp_Wmoment_le_one (W : Graphon) (d : ℕ) : W.Wmoment d ≤ 1 := by
  have hI : Integrable (fun z : ℝ × ℝ => (W.toFun z.1 z.2) ^ d) gμ :=
    W.integrable_comp (continuous_pow d).measurable (continuous_pow d).continuousOn
  have h : ∫ z, (W.toFun z.1 z.2) ^ d ∂gμ ≤ ∫ _z : ℝ × ℝ, (1 : ℝ) ∂gμ :=
    integral_mono hI (integrable_const _) fun z =>
      pow_le_one₀ (W.nonneg' z.1 z.2) (W.le_one' z.1 z.2)
  simpa [Graphon.Wmoment] using h

/-- **The mean-value bound at the right endpoint.**  For `0 ≤ A ≤ B ≤ 1` and `a ≥ 1`,

`B^a - A^a ≤ a(B - A)`.

Bernoulli's inequality `1 + as ≤ (1+s)^a` at `s = A/B - 1` is the tangent-line bound for the
convex function `x ↦ x^a` at the right endpoint `B`, and gives
`B^a - A^a ≤ aB^{a-1}(B - A)`; the factor `B^{a-1} = B^a/B` is at most `1` because `B ≤ 1`.
Nothing is assumed about how close `A` is to `B`. -/
private theorem ldSharp_rpow_increment {A Bv a : ℝ} (hA : 0 ≤ A) (hB0 : 0 < Bv)
    (hAB : A ≤ Bv) (hB1 : Bv ≤ 1) (ha : 1 ≤ a) :
    Bv ^ a - A ^ a ≤ a * (Bv - A) := by
  have hBa : 0 < Bv ^ a := Real.rpow_pos_of_pos hB0 a
  have hs : (-1 : ℝ) ≤ A / Bv - 1 := by
    have h0 : 0 ≤ A / Bv := div_nonneg hA hB0.le
    linarith
  have hbern := one_add_mul_self_le_rpow_one_add hs ha
  rw [show (1 : ℝ) + (A / Bv - 1) = A / Bv by ring, Real.div_rpow hA hB0.le] at hbern
  have hkey : Bv ^ a * (1 + a * (A / Bv - 1)) ≤ Bv ^ a * (A ^ a / Bv ^ a) :=
    mul_le_mul_of_nonneg_left hbern hBa.le
  rw [show Bv ^ a * (A ^ a / Bv ^ a) = A ^ a by field_simp,
    show Bv ^ a * (1 + a * (A / Bv - 1)) = Bv ^ a + a * (Bv ^ a / Bv) * (A - Bv) by
      field_simp] at hkey
  have hBaB : Bv ^ a ≤ Bv := by
    have h1 : Bv ^ a ≤ Bv ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_ge hB0 hB1 ha
    rwa [Real.rpow_one] at h1
  have ht1 : Bv ^ a / Bv ≤ 1 := (div_le_one hB0).mpr hBaB
  have ha0 : (0 : ℝ) ≤ a := by linarith
  have hBA : 0 ≤ Bv - A := by linarith
  have hstep : a * (Bv ^ a / Bv) * (Bv - A) ≤ a * (Bv - A) := by
    calc a * (Bv ^ a / Bv) * (Bv - A) = Bv ^ a / Bv * (a * (Bv - A)) := by ring
      _ ≤ 1 * (a * (Bv - A)) := mul_le_mul_of_nonneg_right ht1 (mul_nonneg ha0 hBA)
      _ = a * (Bv - A) := by ring
  linarith

/-- **The Hölder deficit is `O(h⁴)` along the singular endpoint family.**

There are `K > 0` and `δ > 0` such that for `0 < h < δ` and every competitor `W` at
`(p_h, r_h)` no more expensive than `W_h`,

`(∫W^d)^{m/d} - t(H,W) ≤ Kh⁴`.

Feasibility gives `t(H,W) ≥ r_h^m = (r_h^d)^{m/d}`, so the deficit is at most the increment of
`x ↦ x^{m/d}` between `r_h^d` and `∫W^d`; `family_ld_sharp` bounds that gap by `Mh⁴` and
`ldSharp_rpow_increment` converts it with the factor `m/d = v/2 ≥ 1`.  The constant is
`K = (m/d)M`. -/
theorem family_holder_deficit (hd : 2 ≤ d) {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (hreg : ∀ v, H.degree v = d)
    (hm : 1 ≤ H.edgeFinset.card) (B : KKTFamily d) :
    ∃ K : ℝ, 0 < K ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ (h : ℝ) (hh : |h| < B.h₀), 0 < h → h < δ →
        ∀ W : Graphon, B.rVal h ^ H.edgeFinset.card ≤ W.tDensity H →
          W.Ip (B.p h) ≤ (B.graphon hh).Ip (B.p h) →
          W.Wmoment d ^ ((H.edgeFinset.card : ℝ) / (d : ℝ)) - W.tDensity H ≤ K * h ^ 4 := by
  obtain ⟨M, hM0, δ, hδ, hbnd⟩ := family_ld_sharp hd H hreg hm B
  have hdR : (0 : ℝ) < (d : ℝ) := dpos hd
  have hdm : d ≤ H.edgeFinset.card := degree_le_card_edges H hreg hm
  have hage : (1 : ℝ) ≤ (H.edgeFinset.card : ℝ) / (d : ℝ) := by
    rw [le_div_iff₀ hdR, one_mul]
    exact_mod_cast hdm
  refine ⟨(H.edgeFinset.card : ℝ) / (d : ℝ) * M, by positivity, δ, hδ, ?_⟩
  intro h hh hpos hlt W hfeas hcost
  obtain ⟨hge, hle⟩ := hbnd h hh hpos hlt W hfeas hcost
  have hr0 : 0 < B.rVal h := KKTFamily.rVal_pos hd hh
  have hAd : (0 : ℝ) < B.rVal h ^ d := pow_pos hr0 d
  have hB0 : (0 : ℝ) < W.Wmoment d := lt_of_lt_of_le hAd (by linarith)
  -- `(r_h^d)^{m/d} = r_h^m`
  have hpow : (B.rVal h ^ d) ^ ((H.edgeFinset.card : ℝ) / (d : ℝ))
      = B.rVal h ^ H.edgeFinset.card := by
    rw [← Real.rpow_natCast (B.rVal h) d, ← Real.rpow_mul hr0.le,
      show (d : ℝ) * ((H.edgeFinset.card : ℝ) / (d : ℝ)) = (H.edgeFinset.card : ℝ) by
        field_simp,
      Real.rpow_natCast]
  have hinc := ldSharp_rpow_increment (A := B.rVal h ^ d) (Bv := W.Wmoment d)
    (a := (H.edgeFinset.card : ℝ) / (d : ℝ)) hAd.le hB0 (by linarith)
    (ldSharp_Wmoment_le_one W d) hage
  rw [hpow] at hinc
  have hfinal : (H.edgeFinset.card : ℝ) / (d : ℝ) * (W.Wmoment d - B.rVal h ^ d)
      ≤ (H.edgeFinset.card : ℝ) / (d : ℝ) * M * h ^ 4 := by
    have := mul_le_mul_of_nonneg_left hle (by positivity :
      (0 : ℝ) ≤ (H.edgeFinset.card : ℝ) / (d : ℝ))
    linarith [this]
  linarith [hinc, hfeas]

/-! ## The Factor clause -/

/-- `2 ≤ |V(H)|` for a `d`-regular `H` with `d ≥ 2` and at least one edge: the handshake
identity `2m = vd` together with `d ≤ m` forces `2m ≤ vm`, and `m ≥ 1`. -/
private theorem ldSharp_two_le_card {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (hd : 2 ≤ d) (hreg : ∀ v, H.degree v = d)
    (hm : 1 ≤ H.edgeFinset.card) : 2 ≤ Fintype.card V := by
  have hhand : 2 * H.edgeFinset.card = Fintype.card V * d :=
    factorMain_two_mul_card_edgeFinset H hreg
  have hdm : d ≤ H.edgeFinset.card := degree_le_card_edges H hreg hm
  nlinarith [hhand, hdm, hm, hd]

/-- **A sharpened Factor clause for `lem:localization-rank-one` along the singular endpoint
family** (the paper's rates are only `‖E‖₂ ≤ C_d h` and `|q(f) - q_h| ≤ C_d h²`).

There are `M > 0` and `δ > 0` such that for every `0 < h < δ` in the family window and every
graphon `W` feasible at `(p_h, r_h)` and no more expensive than `W_h`, the nonlinear Factor
decomposition `W = f ⊗ f + E` of `localization_rankOne` — whose `ortho` field is
`T_E(f^{d-1}) = 0` and whose `f` is nonnegative — satisfies

`‖E‖₂ ≤ Mh²`   and   `|∫f^d - q_h| ≤ Mh⁴`.

The three `O(h⁴)` hypotheses of `exists_factorTail_factor_clause` are discharged by
`family_localization` (`ε⁴ ≤ Kh⁴`, which also puts `W` below the existence threshold
`ε₂(d)` of `localization_rankOne` once `h` is small), `family_holder_deficit`, and
`family_ld_sharp` read through `q_h² = r_h^d` (`KKTFamily.rVal_pow_d`).  The closeness
clause `eq:rank-one-reduction-bounds` is carried along so that the tail-mass estimate
`family_factor_tail_mass` applies to the *same* decomposition. -/
theorem family_factor_clause (hd : 2 ≤ d) {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (hreg : ∀ v, H.degree v = d)
    (hm : 1 ≤ H.edgeFinset.card) (B : KKTFamily d) :
    ∃ M : ℝ, 0 < M ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ (h : ℝ) (hh : |h| < B.h₀), 0 < h → h < δ →
        ∀ W : Graphon, B.rVal h ^ H.edgeFinset.card ≤ W.tDensity H →
          W.Ip (B.p h) ≤ (B.graphon hh).Ip (B.p h) →
            ∃ P : FactorDecomp d W, (1 : ℝ) / 2 ^ d ≤ P.qVal ∧
              Lnorm unitμ 4 (fun x => P.f x - uStar d)
                  + Lnorm gμ 4 (fun z : ℝ × ℝ => P.resid z.1 z.2)
                ≤ factorSolutionCloseConst d * contractionEps W d ∧
              P.residNorm ≤ M * h ^ 2 ∧ |P.qVal - B.qVal h| ≤ M * h ^ 4 := by
  classical
  have hv : 2 ≤ Fintype.card V := ldSharp_two_le_card H hd hreg hm
  have hvm : 2 * H.edgeFinset.card = Fintype.card V * d :=
    factorMain_two_mul_card_edgeFinset H hreg
  -- the three `O(h⁴)` inputs
  obtain ⟨K₁, hK₁0, δ₁, hδ₁, hloc⟩ := family_localization hd H hreg hm B
  obtain ⟨K₂, hK₂0, δ₂, hδ₂, hdefc⟩ := family_holder_deficit hd H hreg hm B
  obtain ⟨K₃, hK₃0, δ₃, hδ₃, hmomb⟩ := family_ld_sharp hd H hreg hm B
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = K₁ + K₂ + K₃ := ⟨_, rfl⟩
  have hK0 : 0 < K := by rw [hKdef]; linarith
  -- the abstract Factor clause at these constants
  obtain ⟨M, hM0, h₀, hh₀, hclause⟩ := exists_factorTail_factor_clause (d := d)
    (v := Fintype.card V) (m := H.edgeFinset.card) hd hv hvm
    (factorMainC1_nonneg (d := d) hd) (factorMainC2_nonneg (d := d) hd)
    (by positivity : (0 : ℝ) ≤ (40 : ℝ) ^ H.edgeFinset.card)
    (by positivity : (0 : ℝ) < (1 : ℝ) / 2 ^ d) hK0.le
  -- the existence threshold of `localization_rankOne`
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = Real.sqrt (Real.sqrt K) := ⟨_, rfl⟩
  have hA0 : (0 : ℝ) ≤ A := by rw [hAdef]; exact Real.sqrt_nonneg _
  have hApow : A ^ 4 = K := by
    rw [hAdef, show Real.sqrt (Real.sqrt K) ^ 4 = (Real.sqrt (Real.sqrt K) ^ 2) ^ 2 by ring,
      Real.sq_sqrt (Real.sqrt_nonneg _), Real.sq_sqrt hK0.le]
  have hden : (0 : ℝ) < A + 1 := by linarith
  refine ⟨M, hM0, min (min δ₁ δ₂) (min δ₃ (min h₀ (factorEps2 d / (A + 1)))),
    lt_min (lt_min hδ₁ hδ₂) (lt_min hδ₃ (lt_min hh₀ (div_pos (factorEps2_pos hd) hden))), ?_⟩
  intro h hh hpos hlt W hfeas hcost
  have hlt₁ : h < δ₁ := lt_of_lt_of_le hlt (le_trans (min_le_left _ _) (min_le_left _ _))
  have hlt₂ : h < δ₂ := lt_of_lt_of_le hlt (le_trans (min_le_left _ _) (min_le_right _ _))
  have hlt₃ : h < δ₃ := lt_of_lt_of_le hlt (le_trans (min_le_right _ _) (min_le_left _ _))
  have hlt₀ : h < h₀ :=
    lt_of_lt_of_le hlt (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hltε : h < factorEps2 d / (A + 1) :=
    lt_of_lt_of_le hlt (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (min_le_right _ _)))
  have hh4 : (0 : ℝ) < h ^ 4 := by positivity
  -- `ε⁴ = ∫∫(W - r_*)⁴ ≤ K₁h⁴`
  have hcong : defectQuart d W = ∫ z, |W.toFun z.1 z.2 - rStar d| ^ 4 ∂gμ := by
    unfold defectQuart
    exact integral_congr_ae (Filter.Eventually.of_forall fun z => (Even.pow_abs (n := 4) (by norm_num) _).symm)
  have hdq : defectQuart d W ≤ K₁ * h ^ 4 := by
    rw [hcong]
    exact hloc h hh hpos hlt₁ W hfeas hcost
  have hdqK : defectQuart d W ≤ K * h ^ 4 := by
    have hpad : (0 : ℝ) ≤ (K₂ + K₃) * h ^ 4 := mul_nonneg (by linarith) hh4.le
    rw [hKdef]
    linarith
  -- hence `ε ≤ A·h < ε₂(d)`, so `localization_rankOne` applies
  have hepsA : contractionEps W d ≤ A * h := by
    refine factorTail_le_of_pow_four_le (contractionEps_nonneg W d) (by positivity) ?_
    rw [factorMain_contractionEps_pow_four, mul_pow, hApow]
    exact hdqK
  have heps : contractionEps W d ≤ factorEps2 d := by
    have h1 : h * (A + 1) < factorEps2 d := (lt_div_iff₀ hden).mp hltε
    linarith [hepsA, hpos.le]
  obtain ⟨P, _hqpos, hqlow, _hptw, hclose, hT, _hstab⟩ :=
    localization_rankOne hd H hreg hv W heps
  have hEnn : (0 : ℝ) ≤ Lnorm unitμ 4 (fun x => P.f x - uStar d) := Lnorm_nonneg _ _ _
  have hE : Lnorm gμ 4 (fun z : ℝ × ℝ => P.resid z.1 z.2)
      ≤ factorSolutionCloseConst d * contractionEps W d := by linarith
  -- the deficit and moment inputs
  have hdefh : W.Wmoment d ^ ((H.edgeFinset.card : ℝ) / (d : ℝ)) - W.tDensity H ≤ K * h ^ 4 := by
    have h1 := hdefc h hh hpos hlt₂ W hfeas hcost
    have hpad : (0 : ℝ) ≤ (K₁ + K₃) * h ^ 4 := mul_nonneg (by linarith) hh4.le
    rw [hKdef]
    linarith
  obtain ⟨hge, hle⟩ := hmomb h hh hpos hlt₃ W hfeas hcost
  have hmomh : |W.Wmoment d - B.qVal h ^ 2| ≤ K * h ^ 4 := by
    have hpad : (0 : ℝ) ≤ (K₁ + K₂) * h ^ 4 := mul_nonneg (by linarith) hh4.le
    rw [← KKTFamily.rVal_pow_d hd hh, abs_of_nonneg hge, hKdef]
    linarith
  -- the two closeness inputs, in the vocabulary of `exists_factorTail_factor_clause`
  have hA4 : P.rankOneQuart ≤ factorMainC1 d * defectQuart d W :=
    factorMain_rankOneQuart_le hd hE
  have hE4 : P.residQuart ≤ factorMainC2 d * defectQuart d W := factorMain_residQuart_le hE
  -- feed the abstract clause
  have hmain := hclause h hpos hlt₀ W P (W.tDensity H) (B.qVal h) hqlow
    (KKTFamily.qVal_pos hh).le hA4 hE4 hT hdqK hdefh hmomh
  exact ⟨P, hqlow, by linarith [hclose], hmain.1, hmain.2⟩

end UpperTailOptimizers
