import UpperTailOptimizers.SingularEndpoint.ConstantGraphonComparison.StrictImprovement
import UpperTailOptimizers.SingularEndpoint.ConstantGraphonComparison.ParameterRemainders
import UpperTailOptimizers.SingularEndpoint.RankOneStationaryFamily.MfunAnalytic

/-!
# `lem:constant-graphon-comparison` with the paper's `O_d(h⁴)` and `O_d(h⁶)` remainders

`lem:constant-graphon-comparison` states, for all small `h`,

  `e(W_h) = r_h - (d-1)h² + O_d(h⁴)`,   `I_{p_h}(W_h) = J_{p_h}(r_h) - d³h⁴/3 + O_d(h⁶)`.

The two rates are already proved: `tendsto_edge_gap` (`SingularEndpoint/ConstantGraphonComparison/EdgeGap.lean`) gives
`(e(W_h) - r_h)/h² → -(d-1)` and `tendsto_cost_gap` (`SingularEndpoint/ConstantGraphonComparison/StrictImprovement.lean`)
gives `(I_{p_h}(W_h) - J_{p_h}(r_h))/h⁴ → -d³/3`.  The remainders are upgraded from `o` to the
paper's orders by parity (`SingularEndpoint/ConstantGraphonComparison/ParityOrder.lean`): an even function analytic at `0`
has only even Taylor terms, so the next remainder is two orders higher.

**Edge clause.**  `e(W_h) - r_h = (α_h s_h + (1-α_h)t_h)² - r_h` (`graphon_edgeDensity`) is a
function of `h` alone, analytic at `0` (`u_h, α_h, r_h` are), even (reflection turns `α_h` into
`1-α_h` and exchanges `s_h, t_h`, fixing the mean `α_h s_h + (1-α_h)t_h`; `r_h` is even) and
zero at `h = 0` (`u_*² = r_*`); `exists_pow_bound_sub_quadratic` gives the `O(h⁴)` remainder.

**Cost clause.**  The cost gap itself is exhibited as an even analytic function of `h`.  Both
halves are already available:

* the gap is the scalar `I_{p_h}(W_h) = α_h²J_{p_h}(s_h²) + 2α_h(1-α_h)J_{p_h}(s_ht_h) +
  (1-α_h)²J_{p_h}(t_h²)` (`graphon_Ip_eq_IpScalar`) minus `J_{p_h}(r_h)`, so it is a function of
  `h` alone — no dependence on the window proof — and it is analytic at `0` because `α_h, p_h,
  u_h, r_h` are and `J` is jointly analytic on `(0,1)²` (`analyticAt_Jp_comp`);
* it is **even** because reflection exchanges the two blocks: `alph_reflect` turns `α_h` into
  `1-α_h` while `sVal_neg`/`tVal_neg` exchange `s_h` and `t_h`, which permutes the three terms of
  `IpScalar` among themselves, and `p_h, r_h` are even outright.

## Contents

* `KKTFamily.costScalar` — the cost gap as a function of `h`, with `costScalar_eq`;
* `KKTFamily.IpScalar_even`, `KKTFamily.costScalar_even`, `analyticAt_IpScalar`,
  `analyticAt_costScalar` — the parity and analyticity inputs;
* `constant_graphon_comparison` — `lem:constant-graphon-comparison`:
  `|e(W_h) - (r_h - (d-1)h²)| ≤ C|h|⁴` and `|I_{p_h}(W_h) - (J_{p_h}(r_h) - d³h⁴/3)| ≤ C|h|⁶`
  for `|h| < δ`, with one pair `C, δ` depending only on the family `B`.
-/

namespace UpperTailOptimizers

open Filter Topology MeasureTheory

variable {d : ℕ}

namespace KKTFamily

variable {B : KKTFamily d}

/-- **The cost gap as a function of `h`.**  `I_{p_h}(W_h) - J_{p_h}(r_h)`, written through the
scalar form `IpScalar` so that it does not mention the window proof. -/
noncomputable def costScalar (B : KKTFamily d) (h : ℝ) : ℝ :=
  B.IpScalar h - Jp (B.p h) (B.rVal h)

theorem costScalar_eq {h : ℝ} (hh : |h| < B.h₀) :
    B.costScalar h = (B.graphon hh).Ip (B.p h) - Jp (B.p h) (B.rVal h) := by
  rw [costScalar, graphon_Ip_eq_IpScalar hh]

/-- **`I_{p_h}(W_h)` is even in `h`.**  Reflection exchanges the two blocks: `α_h ↦ 1-α_h` and
`s_h ↔ t_h`, which permutes the three terms of `IpScalar` among themselves. -/
theorem IpScalar_even (B : KKTFamily d) (h : ℝ) : B.IpScalar (-h) = B.IpScalar h := by
  simp only [IpScalar, B.p_even, B.alph_reflect, sVal_neg, tVal_neg]
  rw [show B.tVal h * B.sVal h = B.sVal h * B.tVal h from mul_comm _ _]
  ring

/-- **The cost gap is even in `h`**: `IpScalar_even` for the first term, `p_even` and `rVal_even`
for the second. -/
theorem costScalar_even (B : KKTFamily d) (h : ℝ) : B.costScalar (-h) = B.costScalar h := by
  simp only [costScalar, IpScalar_even, B.p_even, rVal_even]

end KKTFamily

/-! ## Analyticity at the endpoint -/

/-- `I_{p_h}(W_h)` is analytic at `h = 0`.  The three entropies are `J` composed with the
analytic parameters `p_h` and the three edge values, all of which lie in `(0,1)` at `h = 0`
(where they are `p_*` and `r_* = u_*²`). -/
theorem analyticAt_IpScalar (hd : 2 ≤ d) (B : KKTFamily d) :
    AnalyticAt ℝ B.IpScalar 0 := by
  have hw := KKTFamily.zero_mem_window B
  have hp := B.analyticAt_p 0 hw
  have ha := B.analyticAt_alph 0 hw
  have hu := B.analyticAt_u 0 hw
  have hs : AnalyticAt ℝ B.sVal 0 := hu.sub analyticAt_id
  have ht : AnalyticAt ℝ B.tVal 0 := hu.add analyticAt_id
  have hp0 : 0 < B.p 0 := by rw [B.p_zero]; exact pStar_pos hd
  have hp1 : B.p 0 < 1 := by rw [B.p_zero]; exact pStar_lt_one hd
  have hs0 : 0 < B.sVal 0 := KKTFamily.sVal_pos hw
  have hs1 : B.sVal 0 < 1 := KKTFamily.sVal_lt_one hw
  have ht0 : 0 < B.tVal 0 := KKTFamily.tVal_pos hw
  have ht1 : B.tVal 0 < 1 := KKTFamily.tVal_lt_one hw
  have hss1 : B.sVal 0 ^ 2 < 1 := pow_lt_one₀ hs0.le hs1 (n := 2) (by norm_num)
  have htt1 : B.tVal 0 ^ 2 < 1 := pow_lt_one₀ ht0.le ht1 (n := 2) (by norm_num)
  have hJss : AnalyticAt ℝ (fun h : ℝ => Jp (B.p h) (B.sVal h ^ 2)) 0 :=
    analyticAt_Jp_comp hp (hs.pow 2) hp0 hp1 (by positivity) (by simpa using hss1)
  have hJst : AnalyticAt ℝ (fun h : ℝ => Jp (B.p h) (B.sVal h * B.tVal h)) 0 :=
    analyticAt_Jp_comp hp (hs.mul ht) hp0 hp1 (by positivity)
      (by simpa using mul_lt_one_of_nonneg_of_lt_one_left hs0.le hs1 ht1.le)
  have hJtt : AnalyticAt ℝ (fun h : ℝ => Jp (B.p h) (B.tVal h ^ 2)) 0 :=
    analyticAt_Jp_comp hp (ht.pow 2) hp0 hp1 (by positivity) (by simpa using htt1)
  exact (((ha.pow 2).mul hJss).add
    (((analyticAt_const.mul ha).mul (analyticAt_const.sub ha)).mul hJst)).add
    (((analyticAt_const.sub ha).pow 2).mul hJtt)

/-- The cost gap is analytic at `h = 0`. -/
theorem analyticAt_costScalar (hd : 2 ≤ d) (B : KKTFamily d) :
    AnalyticAt ℝ B.costScalar 0 := by
  have hw := KKTFamily.zero_mem_window B
  have hr0 : 0 < B.rVal 0 := KKTFamily.rVal_pos hd hw
  have hr1 : B.rVal 0 < 1 := KKTFamily.rVal_lt_one hd hw
  have hp0 : 0 < B.p 0 := by rw [B.p_zero]; exact pStar_pos hd
  have hp1 : B.p 0 < 1 := by rw [B.p_zero]; exact pStar_lt_one hd
  exact (analyticAt_IpScalar hd B).sub
    (analyticAt_Jp_comp (B.analyticAt_p 0 hw) (KKTFamily.analyticAt_rVal hw) hp0 hp1 hr0 hr1)

/-! ## `lem:constant-graphon-comparison` -/

/-- **`lem:constant-graphon-comparison`.**  For all small `h`,

  `e(W_h) = r_h - (d-1)h² + O_d(h⁴)`,   `I_{p_h}(W_h) = J_{p_h}(r_h) - \frac{d³}{3}h⁴ + O_d(h⁶)`.

The constants depend only on the family `B`, which depends only on `d`. -/
theorem constant_graphon_comparison (hd : 2 ≤ d) (B : KKTFamily d) :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∀ (h : ℝ) (hh : |h| < B.h₀), |h| < δ →
      |(B.graphon hh).edgeDensity - (B.rVal h - ((d : ℝ) - 1) * h ^ 2)| ≤ C * |h| ^ 4 ∧
      |(B.graphon hh).Ip (B.p h) - (Jp (B.p h) (B.rVal h) - (d : ℝ) ^ 3 / 3 * h ^ 4)|
        ≤ C * |h| ^ 6 := by
  have hw := KKTFamily.zero_mem_window B
  -- the edge clause: `v h = e(W_h) - r_h` is even, analytic, vanishes at `0`, and has rate `-(d-1)`
  set v : ℝ → ℝ := fun h =>
    (B.alph h * B.sVal h + (1 - B.alph h) * B.tVal h) ^ 2 - B.rVal h with hvdef
  have ha := B.analyticAt_alph 0 hw
  have hu := B.analyticAt_u 0 hw
  have hs : AnalyticAt ℝ B.sVal 0 := hu.sub analyticAt_id
  have ht : AnalyticAt ℝ B.tVal 0 := hu.add analyticAt_id
  have hva : AnalyticAt ℝ v 0 :=
    (((ha.mul hs).add ((analyticAt_const.sub ha).mul ht)).pow 2).sub
      (KKTFamily.analyticAt_rVal hw)
  have hve : ∀ h : ℝ, v (-h) = v h := by
    intro h
    simp only [hvdef, B.alph_reflect, KKTFamily.sVal_neg, KKTFamily.tVal_neg,
      KKTFamily.rVal_even]
    ring
  have hv0 : v 0 = 0 := by
    have hs0 : B.sVal 0 = uStar d := by simp [KKTFamily.sVal, B.u_zero]
    have ht0 : B.tVal 0 = uStar d := by simp [KKTFamily.tVal, B.u_zero]
    simp only [hvdef, hs0, ht0, B.alph_zero, KKTFamily.rVal_zero hd B]
    rw [← uStar_sq hd]
    ring
  have hvlim : Tendsto (fun h : ℝ => (v h - v 0) / h ^ 2) (𝓝[≠] (0 : ℝ))
      (𝓝 (-((d : ℝ) - 1))) := by
    simp only [hv0, sub_zero]
    exact tendsto_edge_gap B hd
  obtain ⟨C₁, δ₁, hC₁, hδ₁, hb₁⟩ := exists_pow_bound_sub_quadratic hva hve hvlim
  -- the cost clause
  have hlim := tendsto_cost_gap hd B (K := B.costScalar)
    (fun h hh => KKTFamily.costScalar_eq hh)
  obtain ⟨C₂, δ₂, hC₂, hδ₂, hb₂⟩ := exists_pow_bound_sub_quartic (analyticAt_costScalar hd B)
    (KKTFamily.costScalar_even B) hlim
  refine ⟨max C₁ C₂, min δ₁ δ₂, lt_max_of_lt_left hC₁, lt_min hδ₁ hδ₂, fun h hh hhδ => ?_⟩
  constructor
  · have h1 := hb₁ h (lt_of_lt_of_le hhδ (min_le_left _ _))
    rw [hv0] at h1
    rw [KKTFamily.graphon_edgeDensity hh]
    calc |(B.alph h * B.sVal h + (1 - B.alph h) * B.tVal h) ^ 2
          - (B.rVal h - ((d : ℝ) - 1) * h ^ 2)|
        = |v h - 0 - -((d : ℝ) - 1) * h ^ 2| := by
          congr 1; simp only [hvdef]; ring
      _ ≤ C₁ * |h| ^ 4 := h1
      _ ≤ max C₁ C₂ * |h| ^ 4 :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  · have h2 := hb₂ h (lt_of_lt_of_le hhδ (min_le_right _ _))
    calc |(B.graphon hh).Ip (B.p h) - (Jp (B.p h) (B.rVal h) - (d : ℝ) ^ 3 / 3 * h ^ 4)|
        = |B.costScalar h - -((d : ℝ) ^ 3 / 3) * h ^ 4| := by
          rw [KKTFamily.costScalar_eq hh]; congr 1; ring
      _ ≤ C₂ * |h| ^ 6 := h2
      _ ≤ max C₁ C₂ * |h| ^ 6 :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

end UpperTailOptimizers
