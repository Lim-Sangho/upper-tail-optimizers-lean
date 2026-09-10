import UpperTailOptimizers.SingularEndpoint.DistributionFinal

/-!
# The uniqueness clause of `sec:endpoint-optimality-proof` (Section 7)

`SingularEndpoint/DistributionFinal.lean` closes the quantitative half of `sec:endpoint-optimality-proof`: `eq:auxiliary-lagrangian-bound` and its refined companion
the refined form of `eq:auxiliary-lagrangian-bound` holds with every deferred hypothesis discharged.  This file
realises the closing paragraph of the proof, `paper/singular_endpoint.tex`, which is what
turns that gap bound into the *uniqueness* statement of the lemma:

> For an exact minimizer with `m_d(ν) = q_h`, the left-hand side of `eq:auxiliary-lagrangian-bound` is
> non-positive because `ν_h` is admissible, whereas the right-hand side is nonnegative.  Hence
> `ν(T_ρ) = 0` and `Q_h = 0` almost surely.  Therefore `ν = βδ_{s_h} + (1-β)δ_{t_h}` for some
> `β ∈ [0,1]`.  The equation `βs_h^d + (1-β)t_h^d = q_h` has the unique solution `β = α_h`.
> Thus `ν = ν_h`.

## The four steps

1. `Δ_h(ν) = 0` makes the moment clause of `eq:graphon-comparison-estimates` trivial, and the tail
   clause is `KKTFamily.exists_tail_mass_le` (`SingularEndpoint/DistributionLocal.lean`), which holds
  for exactly the competitors considered here.  `eq:auxiliary-lagrangian-bound` then reads
   `M⁻¹(A_ρ + ε_ρ) ≤ 𝒥_h(ν) - 𝒥_h(ν_h) ≤ 0`, and both `A_ρ = ∫_{𝓝_ρ}Q_h²dν` and
   `ε_ρ = ν(T_ρ)` are nonnegative, so both vanish.
2. `ε_ρ = 0` together with `ν([0,2]ᶜ) = 0` says `ν(𝓝_ρᶜ) = 0`, so the window integral `A_ρ` is
   the full integral; `A_ρ = 0` with a nonnegative integrand then gives `Q_h = 0` `ν`-a.e.
3. `Q_h(x) = (x - s_h)(x - t_h)` vanishes exactly on `{s_h, t_h}`, so `ν({s_h,t_h}ᶜ) = 0`.
   That is `KKTFamily.distribution_carried_by_atoms`, stated separately because it is already
   the substance of the argument.
4. A measure carried by a two-point set is the matching combination of Dirac masses
   (`eq_two_atoms`), and its `d`-th moment is the two-point average (`integral_two_atoms`).
   Since `0 ≤ s_h < t_h` gives `s_h^d < t_h^d`, the linear equation `βs_h^d + (1-β)t_h^d = q_h`
   has at most one solution, and `α_h` is one by the definition of `q_h`.  Hence `ν = ν_h`.

## Quantifier order

`exists_distributionGap` fixes the constant `K` of `eq:graphon-comparison-estimates` *before* the window
radius `ρ`, while `exists_tail_mass_le` produces its `K` *from* `ρ`.  The composition in
`SingularEndpoint/DistributionFinal.lean` therefore cannot be used as a black box here; instead the same
three ingredients are recombined in the order `ρ` (from `exists_distribution_window`), then `K`
(from `exists_tail_mass_le` at that `ρ`), then `exists_distributionGap` at `max 1 K`.  This is the
only reason the file calls `exists_distribution_window` and `exists_distributionGap` directly rather
than `exists_distributionGap_window`.

## Contents

* `eq_two_atoms` — a measure on `ℝ` carried by `{s,t}` with `s ≠ t` is `ν{s}δ_s + ν{t}δ_t`;
* `integral_two_atoms` — integration against `aδ_s + bδ_t`;
* **`KKTFamily.distribution_carried_by_atoms`** — steps 1–3: an exact minimiser at the pinned
  moment is carried by `{s_h, t_h}`;
* **`KKTFamily.distribution_unique`** — the uniqueness clause of `sec:endpoint-optimality-proof`;
* **`KKTFamily.distributionMeasure_isMinimizer`** — the lemma as the paper states it: `ν_h`
  minimises `𝒥_h` at the pinned moment, and no other competitor attains that value.

`ν_h` is itself admissible — `isProbabilityMeasure_distributionMeasure`,
`distributionMeasure_Icc_compl` and `integral_pow_distributionMeasure` (`SingularEndpoint/DistributionMeasure.lean`,
`SingularEndpoint/DistributionLocal.lean`) — so the statement is not vacuous.
-/

namespace UpperTailOptimizers

namespace SingularEndpoint

open MeasureTheory

variable {d : ℕ}

/-! ## Measures carried by a two-point set -/

/-- **A measure carried by `{s,t}` is a combination of two Dirac masses.**  This is the
"`ν = βδ_{s_h} + (1-β)δ_{t_h}` for some `β`" step of `paper/singular_endpoint.tex`, in the
form that also identifies the two weights.

The proof is `Measure.restrict_eq_self_of_ae_mem` followed by `Measure.restrict_union` on
`{s,t} = {s} ∪ {t}` and `Measure.restrict_singleton`; the hypothesis `s ≠ t` is what makes the
two singletons disjoint, and without it the right-hand side would double-count. -/
private theorem eq_two_atoms {ν : Measure ℝ} {s t : ℝ} (hst : s ≠ t)
    (hν : ν ({s, t} : Set ℝ)ᶜ = 0) :
    ν = ν {s} • Measure.dirac s + ν {t} • Measure.dirac t := by
  have hae : ∀ᵐ x ∂ν, x ∈ ({s, t} : Set ℝ) := by
    rw [ae_iff]
    exact hν
  have hpair : ({s, t} : Set ℝ) = {s} ∪ {t} := by rw [Set.singleton_union]
  calc ν = ν.restrict ({s, t} : Set ℝ) := (Measure.restrict_eq_self_of_ae_mem hae).symm
    _ = ν.restrict ({s} : Set ℝ) + ν.restrict ({t} : Set ℝ) := by
        rw [hpair, Measure.restrict_union (Set.disjoint_singleton.mpr hst)
          (measurableSet_singleton t)]
    _ = ν {s} • Measure.dirac s + ν {t} • Measure.dirac t := by
        rw [Measure.restrict_singleton, Measure.restrict_singleton]

/-- **Integration against `aδ_s + bδ_t`** is the two-point average `a f(s) + b f(t)`.  No
measurability of `f` is needed, exactly as in `KKTFamily.integral_distributionMeasure`:
`MeasureTheory.integral_dirac` holds for arbitrary `f` on a space with measurable singletons,
and the two finite weights let `MeasureTheory.integral_add_measure` apply. -/
private theorem integral_two_atoms {a b : ENNReal} (ha : a ≠ ⊤) (hb : b ≠ ⊤) (s t : ℝ)
    (f : ℝ → ℝ) :
    ∫ x, f x ∂(a • Measure.dirac s + b • Measure.dirac t)
      = a.toReal * f s + b.toReal * f t := by
  have hi1 : Integrable f (a • Measure.dirac s) := (integrable_dirac (by simp)).smul_measure ha
  have hi2 : Integrable f (b • Measure.dirac t) := (integrable_dirac (by simp)).smul_measure hb
  rw [integral_add_measure hi1 hi2, integral_smul_measure, integral_smul_measure,
    integral_dirac, integral_dirac, smul_eq_mul, smul_eq_mul]

namespace KKTFamily

/-! ## Steps 1–3: the minimiser is carried by the two atoms -/

/-- **Every exact minimiser at the pinned moment is carried by `{s_h, t_h}`**.

If `ν` is a probability measure on `[0,2]` with `m_d(ν) = q_h` and `𝒥_h(ν) ≤ 𝒥_h(ν_h)`, then
`ν({s_h,t_h}ᶜ) = 0`.

The moment clause of `eq:graphon-comparison-estimates` is trivial because `Δ_h(ν) = 0`, and its tail
clause is `exists_tail_mass_le`; `eq:auxiliary-lagrangian-bound` then bounds
`M⁻¹(∫_{𝓝_ρ}Q_h²dν + ν(T_ρ))` by `𝒥_h(ν) - 𝒥_h(ν_h) ≤ 0`.  Both bracketed terms are
nonnegative, so both vanish.  The vanishing tail mass upgrades the window integral to the full
integral, and `∫Q_h²dν = 0` with `Q_h² ≥ 0` forces `Q_h = 0` `ν`-a.e.; the zero set of
`Q_h(x) = (x - s_h)(x - t_h)` is `{s_h, t_h}`. -/
theorem distribution_carried_by_atoms (hd : 2 ≤ d) (B : KKTFamily d) :
    ∃ hρ > 0, ∀ h : ℝ, 0 < h → h < hρ → h ≤ 1 → |h| < B.h₀ →
      ∀ ν : Measure ℝ, IsProbabilityMeasure ν → ν (Set.Icc (0 : ℝ) 2)ᶜ = 0 →
        (∫ x, x ^ d ∂ν) = B.qVal h →
        B.distributionJ h ν ≤ B.distributionJ h (B.distributionMeasure h) →
          ν ({B.sVal h, B.tVal h} : Set ℝ)ᶜ = 0 := by
  obtain ⟨ρ, hρ0, Cu, hCu, Cp, hCp, C, _hC, hw, hw0, hρu, hρ1, hwin⟩ :=
    exists_distribution_window hd B
  obtain ⟨K, _hK, δT, hδT, htailb⟩ := exists_tail_mass_le hd B hρ0
  obtain ⟨M, hM, δ₁, hδ₁, hgap⟩ :=
    exists_distributionGap hd B hρ0 hρu hρ1 hCu.le hCp.le (le_max_left 1 K)
  refine ⟨min (min hw δT) δ₁, lt_min (lt_min hw0 hδT) hδ₁, ?_⟩
  intro h hh0 hhδ hh1 hhb ν hν hνc hmom hcost
  have hhw : h < hw := lt_of_lt_of_le hhδ (le_trans (min_le_left _ _) (min_le_left _ _))
  have hhT : h < δT := lt_of_lt_of_le hhδ (le_trans (min_le_left _ _) (min_le_right _ _))
  have hhδ₁ : h < δ₁ := lt_of_lt_of_le hhδ (min_le_right _ _)
  obtain ⟨hs, ht, hk00, hkd0, hk0d, hkdd, hu0, hud, hcor, htw, _⟩ := hwin h hh0 hhw hhb
  have hpow4 : (0 : ℝ) ≤ h ^ 4 := by positivity
  have hKpos : (0 : ℝ) < max 1 K := lt_of_lt_of_le one_pos (le_max_left 1 K)
  have htail : (ν (Set.Icc (0 : ℝ) 2 \ centralWindow d ρ)).toReal ≤ max 1 K * h ^ 4 :=
    le_trans (htailb h hhb hh0 hhT ν hν hνc hmom hcost)
      (mul_le_mul_of_nonneg_right (le_max_right 1 K) hpow4)
  have hmomb : |(∫ x, x ^ d ∂ν) - B.qVal h| ≤ max 1 K * h ^ 4 := by
    rw [hmom, sub_self, abs_zero]
    exact mul_nonneg hKpos.le hpow4
  have hg := hgap h hh0 hhδ₁ hh1 hhb ((d : ℝ) ^ 3 / 192) (by positivity) le_rfl
    hk00 hkd0 hk0d hkdd hu0 hud hcor htw hs ht ν hν hνc htail hmomb
  rw [hmom, sub_self] at hg
  have hz1 : M * (0 : ℝ) ^ 2 = 0 := by ring
  have hz2 : B.etaVal h * (0 : ℝ) = 0 := by ring
  rw [hz1, hz2, sub_zero, sub_zero] at hg
  -- Both bracketed terms are nonnegative and their `M⁻¹`-multiple is nonpositive.
  have hAnn : 0 ≤ ∫ x in centralWindow d ρ, B.Qh h x ^ 2 ∂ν :=
    integral_nonneg fun _ => sq_nonneg _
  have henn : 0 ≤ (ν (Set.Icc (0 : ℝ) 2 \ centralWindow d ρ)).toReal := ENNReal.toReal_nonneg
  have hMinv : (0 : ℝ) < M⁻¹ := inv_pos.mpr hM
  have hsum : (∫ x in centralWindow d ρ, B.Qh h x ^ 2 ∂ν)
      + (ν (Set.Icc (0 : ℝ) 2 \ centralWindow d ρ)).toReal ≤ 0 := by
    by_contra hc
    push Not at hc
    have := mul_pos hMinv hc
    linarith
  have hA0 : (∫ x in centralWindow d ρ, B.Qh h x ^ 2 ∂ν) = 0 := by linarith
  have hε0 : (ν (Set.Icc (0 : ℝ) 2 \ centralWindow d ρ)).toReal = 0 := by linarith
  -- Step 2: no mass outside the window, so the window integral is the full integral.
  have hνtail : ν (Set.Icc (0 : ℝ) 2 \ centralWindow d ρ) = 0 := by
    rcases (ENNReal.toReal_eq_zero_iff _).mp hε0 with hcase | hcase
    · exact hcase
    · exact absurd hcase (measure_ne_top ν _)
  have hνN : ν (centralWindow d ρ)ᶜ = 0 := by
    refine measure_mono_null (fun x hx => ?_) (measure_union_null hνtail hνc)
    by_cases hxI : x ∈ Set.Icc (0 : ℝ) 2
    · exact Or.inl ⟨hxI, hx⟩
    · exact Or.inr hxI
  have hres : ν.restrict (centralWindow d ρ) = ν :=
    Measure.restrict_eq_self_of_ae_mem (by rw [ae_iff]; exact hνN)
  rw [hres] at hA0
  -- Step 3: `Q_h² = 0` almost everywhere, and `Q_h` vanishes only at the two atoms.
  have hcont : Continuous fun x : ℝ => B.Qh h x ^ 2 := by
    have heq : (fun x : ℝ => B.Qh h x ^ 2)
        = fun x : ℝ => ((x - B.sVal h) * (x - B.tVal h)) ^ 2 := rfl
    rw [heq]
    fun_prop
  have hint : Integrable (fun x : ℝ => B.Qh h x ^ 2) ν :=
    integrable_of_continuousOn hνc hcont.continuousOn
  have hae : (fun x : ℝ => B.Qh h x ^ 2) =ᵐ[ν] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun _ => sq_nonneg _) hint).mp hA0
  have hmem : ∀ᵐ x ∂ν, x ∈ ({B.sVal h, B.tVal h} : Set ℝ) := by
    filter_upwards [hae] with x hx
    simp only [Pi.zero_apply] at hx
    have hQ : (x - B.sVal h) * (x - B.tVal h) = 0 := sq_eq_zero_iff.mp hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases mul_eq_zero.mp hQ with hcase | hcase
    · exact Or.inl (sub_eq_zero.mp hcase)
    · exact Or.inr (sub_eq_zero.mp hcase)
  exact ae_iff.mp hmem

/-! ## Steps 4–5: the two-point measure with the right moment is `ν_h` -/

/-- **The uniqueness clause of `sec:endpoint-optimality-proof`**.

There is `h_ρ > 0` such that for every `0 < h < h_ρ` inside the family window, the candidate
law `ν_h = α_hδ_{s_h} + (1-α_h)δ_{t_h}` is the *only* probability measure on `[0,2]` with
`m_d(ν) = q_h` and `𝒥_h(ν) ≤ 𝒥_h(ν_h)`.  Since `ν_h` itself is such a measure
(`integral_pow_distributionMeasure`), this says exactly that `ν_h` is the unique minimiser of `𝒥_h`
at the pinned moment.

`distribution_carried_by_atoms` gives `ν = aδ_{s_h} + bδ_{t_h}` through `eq_two_atoms`, with
`a + b = 1` from `ν(ℝ) = 1`.  The moment condition reads `a s_h^d + b t_h^d = q_h`, and
`q_h = α_h s_h^d + (1-α_h)t_h^d` by the definition of `qVal`; subtracting gives
`(a - α_h)(s_h^d - t_h^d) = 0`.  For `h > 0` one has `0 < s_h < t_h` (`sVal_pos`, and
`s_h = u_h - h < u_h + h = t_h`), hence `s_h^d < t_h^d` for `d ≥ 2`, so `a = α_h`. -/
theorem distribution_unique (hd : 2 ≤ d) (B : KKTFamily d) :
    ∃ hρ > 0, ∀ h : ℝ, 0 < h → h < hρ → h ≤ 1 → |h| < B.h₀ →
      ∀ ν : Measure ℝ, IsProbabilityMeasure ν → ν (Set.Icc (0 : ℝ) 2)ᶜ = 0 →
        (∫ x, x ^ d ∂ν) = B.qVal h →
        B.distributionJ h ν ≤ B.distributionJ h (B.distributionMeasure h) →
          ν = B.distributionMeasure h := by
  obtain ⟨hρ, hρ0, hcar⟩ := distribution_carried_by_atoms hd B
  refine ⟨hρ, hρ0, ?_⟩
  intro h hh0 hhρ hh1 hhb ν hν hνc hmom hcost
  have hatoms := hcar h hh0 hhρ hh1 hhb ν hν hνc hmom hcost
  have hst : B.sVal h < B.tVal h := B.sVal_lt_tVal hh0
  -- Name the two weights before rewriting, so that `ν` no longer occurs in them.
  obtain ⟨a, hadef⟩ : ∃ a : ENNReal, ν {B.sVal h} = a := ⟨_, rfl⟩
  obtain ⟨b, hbdef⟩ : ∃ b : ENNReal, ν {B.tVal h} = b := ⟨_, rfl⟩
  have hrep : ν = a • Measure.dirac (B.sVal h) + b • Measure.dirac (B.tVal h) := by
    rw [← hadef, ← hbdef]
    exact eq_two_atoms (ne_of_lt hst) hatoms
  have hatop : a ≠ ⊤ := by rw [← hadef]; exact measure_ne_top ν _
  have hbtop : b ≠ ⊤ := by rw [← hbdef]; exact measure_ne_top ν _
  -- The two weights sum to one.
  have hsum : a + b = 1 := by
    have huniv : ν Set.univ = 1 := measure_univ
    rw [hrep] at huniv
    simpa only [Measure.coe_add, Pi.add_apply, Measure.smul_apply, smul_eq_mul,
      Measure.dirac_apply_of_mem (Set.mem_univ _), mul_one] using huniv
  have hsumR : a.toReal + b.toReal = 1 := by
    rw [← ENNReal.toReal_add hatop hbtop, hsum, ENNReal.toReal_one]
  -- The moment equation.
  have hI : (∫ x, x ^ d ∂ν) = a.toReal * B.sVal h ^ d + b.toReal * B.tVal h ^ d := by
    rw [hrep]
    exact integral_two_atoms hatop hbtop _ _ _
  have hmomA : a.toReal * B.sVal h ^ d + b.toReal * B.tVal h ^ d
      = B.alph h * B.sVal h ^ d + (1 - B.alph h) * B.tVal h ^ d := by
    rw [← hI, hmom]
    rfl
  -- `s_h^d < t_h^d`, so the linear moment equation pins the weight.
  have hpowlt : B.sVal h ^ d < B.tVal h ^ d :=
    pow_lt_pow_left₀ hst (sVal_pos hhb).le (by omega)
  have hkey : (a.toReal - B.alph h) * (B.sVal h ^ d - B.tVal h ^ d) = 0 := by
    have hb : b.toReal = 1 - a.toReal := by linarith
    rw [hb] at hmomA
    linear_combination hmomA
  have halph : a.toReal = B.alph h := by
    have hne : B.sVal h ^ d - B.tVal h ^ d ≠ 0 := sub_ne_zero_of_ne (ne_of_lt hpowlt)
    exact sub_eq_zero.mp ((mul_eq_zero.mp hkey).resolve_right hne)
  have hbeta : b.toReal = 1 - B.alph h := by rw [← halph]; linarith
  have haval : a = ENNReal.ofReal (B.alph h) := by
    rw [← halph, ENNReal.ofReal_toReal hatop]
  have hbval : b = ENNReal.ofReal (1 - B.alph h) := by
    rw [← hbeta, ENNReal.ofReal_toReal hbtop]
  calc ν = a • Measure.dirac (B.sVal h) + b • Measure.dirac (B.tVal h) := hrep
    _ = ENNReal.ofReal (B.alph h) • Measure.dirac (B.sVal h)
        + ENNReal.ofReal (1 - B.alph h) • Measure.dirac (B.tVal h) := by rw [haval, hbval]
    _ = B.distributionMeasure h := rfl

/-- **`sec:endpoint-optimality-proof` as the paper states it**:
for every small `h > 0` the candidate law `ν_h` is *the* minimiser of `𝒥_h` among
probability measures on `[0,2]` with `m_d(ν) = q_h`.

Minimality is a formal consequence of `distribution_unique`: a competitor with
`𝒥_h(ν) < 𝒥_h(ν_h)` would in particular satisfy `𝒥_h(ν) ≤ 𝒥_h(ν_h)`, hence equal `ν_h`, hence
contradict the strict inequality.  The paper instead argues minimality first, from weak
compactness of the moment-constrained set; that
attainment step is therefore not needed here and is not formalised. -/
theorem distributionMeasure_isMinimizer (hd : 2 ≤ d) (B : KKTFamily d) :
    ∃ hρ > 0, ∀ h : ℝ, 0 < h → h < hρ → h ≤ 1 → |h| < B.h₀ →
      ∀ ν : Measure ℝ, IsProbabilityMeasure ν → ν (Set.Icc (0 : ℝ) 2)ᶜ = 0 →
        (∫ x, x ^ d ∂ν) = B.qVal h →
          B.distributionJ h (B.distributionMeasure h) ≤ B.distributionJ h ν
            ∧ (B.distributionJ h ν ≤ B.distributionJ h (B.distributionMeasure h) →
                ν = B.distributionMeasure h) := by
  obtain ⟨hρ, hρ0, huniq⟩ := distribution_unique hd B
  refine ⟨hρ, hρ0, ?_⟩
  intro h hh0 hhρ hh1 hhb ν hν hνc hmom
  refine ⟨?_, fun hcost => huniq h hh0 hhρ hh1 hhb ν hν hνc hmom hcost⟩
  by_contra hc
  push Not at hc
  have heq := huniq h hh0 hhρ hh1 hhb ν hν hνc hmom hc.le
  rw [heq] at hc
  exact lt_irrefl _ hc

end KKTFamily

end SingularEndpoint

end UpperTailOptimizers
