import UpperTailOptimizers.SingularEndpoint.MfunSandwich
import UpperTailOptimizers.SingularEndpoint.FamilySymm
import UpperTailOptimizers.SingularEndpoint.Order4

/-!
# The `h⁴` order along the coalescing family, right increment (Section 7)

This is the companion of `SingularEndpoint/Order4.lean`: the same statement
the paper's expansion for the *other* of the two increments of
`eq:block-proportion-formula`,

    𝓜_h(t_h²) - 𝓜_h(s_h t_h) = -2d³h⁴/3 + o(h⁴).

Together with `exists_family_left_increment_asymptotics` — which gives
`A_h = 𝓜_h(s_h²) - 𝓜_h(s_h t_h) = -2d³h⁴/3 + o(h⁴)` — this is everything the block weight
`α_h = B/(A+B)` needs in order to converge to `1/2`.

The proof is a transcription of `SingularEndpoint/Order4.lean`, and reuses its uniform bound
`eventually_Fkkt3_near` verbatim.  There is exactly one difference.  On the right
subinterval the node cubic is *negative*, so `Mfun_sandwich_right` has `m` and `M`
exchanged and the cubic factor carries a minus sign: writing `Δ` for the increment and
`X = h⁴ C_h` with `C_h = 4 t_h³(t_h + 2s_h)/3` for the (positive) cubic factor supplied by
`cubic_factor_right`, the sandwich reads

    M/6 · (-X)  ≤  Δ  ≤  m/6 · (-X).

Setting `R = -6Δ/X`, so that `Δ = -R X/6`, turns this into `m ≤ R ≤ M`, exactly as on the
left; the ε-argument then gives `R → K = d⁵/(d-1)²` unchanged.  The extra minus survives
into the conclusion:

    Δ/h⁴ = -R·C_h/6  →  -K·4r_*²/6 = -(2d³/3),

whereas the left increment `𝓜(s t) - 𝓜(s²)` tends to `+2d³/3`.  The two limits differ in
sign only because the two increments are taken in opposite directions: `A_h` and `B_h`
themselves are both `-2d³h⁴/3 + o(h⁴)`.

**Why `h > 0`.**  As in `SingularEndpoint/Order4.lean`: the nodes are ordered `s² < st < t²` exactly
when `h > 0`, and the family is even in `h`, so nothing is lost.

## Contents

* `family_right_increment_asymptotics` — the `h⁴` limit, with constant `-2d³/3`, for a
  family supplied as hypotheses; this hypothesis-taking form exists so that this increment
  and the left increment `family_left_increment_asymptotics` can be taken against one and
  the same family, which is what the block weight `α_h = B_h/(A_h + B_h)` needs;
* `exists_family_right_increment_asymptotics` — the same limit packaged existentially.
-/

namespace UpperTailOptimizers

namespace SingularEndpoint

open Filter Topology

variable {d : ℕ}

/-- **The right-increment expansion, along a prescribed family.**

The hypotheses are exactly the data that `exists_scalar_family_density` produces, taken as
arguments instead of opened from an existential.  Paired with
`family_left_increment_asymptotics`, this lets both increments be evaluated along *the same*
`(u, lv, g, p)`, which is what computing the block weight `α_h = B_h/(A_h + B_h)` requires.
The functions `lv` and `p` are carried in the binder even though `lv` occurs only in the
KKT hypotheses, so that a caller can pass a family through unchanged.

The conclusion is

    (𝓜_h(t_h²) - 𝓜_h(s_h t_h)) / h⁴  →  -2d³/3   as `h ↓ 0`. -/
theorem family_right_increment_asymptotics (hd : 2 ≤ d) {h0 : ℝ} {u lv g p : ℝ → ℝ}
    (hh0 : 0 < h0) (hu0 : u 0 = uStar d) (hg0 : g 0 = gammaStar d)
    (hua : ∀ h : ℝ, |h| < h0 → AnalyticAt ℝ u h)
    (hga : ∀ h : ℝ, |h| < h0 → AnalyticAt ℝ g h)
    (hadm : ∀ h : ℝ, |h| < h0 → 0 < u h - |h| ∧ u h + |h| < 1)
    (hp01 : ∀ h : ℝ, |h| < h0 → 0 < p h ∧ p h < 1)
    (hellp : ∀ h : ℝ, |h| < h0 → ell (p h) = lv h)
    (hkkt : ∀ h : ℝ, |h| < h0 → h ≠ 0 →
        Lell d (lv h) (g h) ((u h - h) ^ 2) = 0 ∧
          Lell d (lv h) (g h) ((u h - h) * (u h + h)) = 0 ∧
          Lell d (lv h) (g h) ((u h + h) ^ 2) = 0) :
    Tendsto (fun h : ℝ => (Mfun d (p h) (g h) ((u h + h) ^ 2)
          - Mfun d (p h) (g h) ((u h - h) * (u h + h))) / h ^ 4)
      (𝓝[>] (0 : ℝ)) (𝓝 (-(2 * (d : ℝ) ^ 3 / 3))) := by
  set K : ℝ := (d : ℝ) ^ 5 / ((d : ℝ) - 1) ^ 2 with hKdef
  set s : ℝ → ℝ := fun h => u h - h with hs
  set t : ℝ → ℝ := fun h => u h + h with ht
  set C : ℝ → ℝ := fun h => 4 * t h ^ 3 * (t h + 2 * s h) / 3 with hC
  set D : ℝ → ℝ := fun h => Mfun d (p h) (g h) (t h ^ 2) - Mfun d (p h) (g h) (s h * t h)
    with hD
  -- continuity of the family at `0`
  have h0mem : |(0 : ℝ)| < h0 := by simpa using hh0
  have huT : Tendsto u (𝓝 (0 : ℝ)) (𝓝 (uStar d)) := by
    have := (hua 0 h0mem).continuousAt.tendsto
    rwa [hu0] at this
  have hgT : Tendsto g (𝓝 (0 : ℝ)) (𝓝 (gammaStar d)) := by
    have := (hga 0 h0mem).continuousAt.tendsto
    rwa [hg0] at this
  have hsT : Tendsto s (𝓝 (0 : ℝ)) (𝓝 (uStar d)) := by
    simpa [hs] using huT.sub (continuous_id.continuousAt (x := (0 : ℝ))).tendsto
  have htT : Tendsto t (𝓝 (0 : ℝ)) (𝓝 (uStar d)) := by
    simpa [ht] using huT.add (continuous_id.continuousAt (x := (0 : ℝ))).tendsto
  have hsqT : Tendsto (fun h => s h ^ 2) (𝓝 (0 : ℝ)) (𝓝 (rStar d)) := by
    simpa [uStar_sq hd] using hsT.pow 2
  have htqT : Tendsto (fun h => t h ^ 2) (𝓝 (0 : ℝ)) (𝓝 (rStar d)) := by
    simpa [uStar_sq hd] using htT.pow 2
  -- the limit of the shape factor `C`
  have hu4 : uStar d ^ 4 = rStar d ^ 2 := by
    have : uStar d ^ 4 = (uStar d ^ 2) ^ 2 := by ring
    rw [this, uStar_sq hd]
  have hCT : Tendsto C (𝓝 (0 : ℝ)) (𝓝 (4 * rStar d ^ 2)) := by
    have := ((htT.pow 3).mul (htT.add (hsT.const_mul 2)))
    have h2 : Tendsto (fun h => 4 * (t h ^ 3 * (t h + 2 * s h)) / 3) (𝓝 (0 : ℝ))
        (𝓝 (4 * (uStar d ^ 3 * (uStar d + 2 * uStar d)) / 3)) :=
      (this.const_mul 4).div_const 3
    have hval : 4 * (uStar d ^ 3 * (uStar d + 2 * uStar d)) / 3 = 4 * rStar d ^ 2 := by
      rw [← hu4]; ring
    rw [hval] at h2
    simpa [hC, mul_assoc] using h2
  -- admissibility and the KKT equations, on the positive side
  have hpos : ∀ᶠ h in 𝓝[>] (0 : ℝ), 0 < h ∧ |h| < h0 := by
    refine (eventually_nhdsWithin_iff.mpr ?_).and ?_
    · filter_upwards with x hx using hx
    · exact (Metric.eventually_nhds_iff.mpr ⟨h0, hh0, fun {y} hy => by
        simpa [Real.dist_eq] using hy⟩).filter_mono nhdsWithin_le_nhds
  -- the pinched quotient converges to `K`
  have hR : Tendsto (fun h => -6 * D h / (h ^ 4 * C h)) (𝓝[>] (0 : ℝ)) (𝓝 K) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hnear := eventually_Fkkt3_near hd (g := g) (z₁ := fun h => s h ^ 2)
      (z₃ := fun h => t h ^ 2) hgT hsqT htqT (half_pos hε)
    filter_upwards [hpos, hnear.filter_mono nhdsWithin_le_nhds] with h ⟨hh, hhlt⟩ hbnd
    -- the three nodes, in order, inside `(0,1)`
    obtain ⟨hs0, ht1⟩ := hadm h hhlt
    have habs : |h| = h := abs_of_pos hh
    rw [habs] at hs0 ht1
    have hspos : 0 < s h := hs0
    have hst : s h < t h := by simp only [hs, ht]; linarith
    have ht1' : t h < 1 := by simpa [ht] using ht1
    have htpos : 0 < t h := hspos.trans hst
    have hz₁ : (0 : ℝ) < s h ^ 2 := by positivity
    have hz₁₂ : s h ^ 2 < s h * t h := by nlinarith
    have hz₂₃ : s h * t h < t h ^ 2 := by nlinarith
    have hz₃ : t h ^ 2 < 1 := by nlinarith
    -- the KKT equations, transported from `Lell` to `Fkkt`
    obtain ⟨hp0, hp1⟩ := hp01 h hhlt
    obtain ⟨e₁, e₂, e₃⟩ := hkkt h hhlt (ne_of_gt hh)
    rw [← hellp h hhlt] at e₁ e₂ e₃
    rw [Lell_eq_Fkkt hp0 hp1 hz₁ (hz₁₂.trans (hz₂₃.trans hz₃))] at e₁
    rw [Lell_eq_Fkkt hp0 hp1 (hz₁.trans hz₁₂) (hz₂₃.trans hz₃)] at e₂
    rw [Lell_eq_Fkkt hp0 hp1 ((hz₁.trans hz₁₂).trans hz₂₃) hz₃] at e₃
    -- the sandwich, with `m = K - ε/2` and `M = K + ε/2`
    have hm : ∀ x ∈ Set.Icc (s h ^ 2) (t h ^ 2), K - ε / 2 ≤ Fkkt3 d (g h) x := by
      intro x hx
      have := hbnd x hx
      rw [abs_sub_lt_iff] at this
      linarith [this.2]
    have hM : ∀ x ∈ Set.Icc (s h ^ 2) (t h ^ 2), Fkkt3 d (g h) x ≤ K + ε / 2 := by
      intro x hx
      have := hbnd x hx
      rw [abs_sub_lt_iff] at this
      linarith [this.1]
    obtain ⟨hlow, hhigh⟩ :=
      Mfun_sandwich_right hd hp0 hp1 hz₁ hz₁₂ hz₂₃ hz₃ e₁ e₂ e₃ hm hM
    -- rewrite the cubic factor as `h⁴ · C h`
    have hcf : (t h ^ 2 - s h * t h) ^ 3 *
        ((t h ^ 2 - s h * t h) + 2 * (s h * t h - s h ^ 2)) / 12 = h ^ 4 * C h := by
      simp only [hs, ht, hC]
      rw [cubic_factor_right]
      ring
    rw [hcf] at hlow hhigh
    -- divide by the positive quantity `h⁴ · C h`
    have hCpos : 0 < C h := by
      simp only [hC]
      have : 0 < t h + 2 * s h := by linarith
      positivity
    have hXpos : 0 < h ^ 4 * C h := by positivity
    have hXne : h ^ 4 * C h ≠ 0 := ne_of_gt hXpos
    set R : ℝ := -6 * D h / (h ^ 4 * C h) with hRdef
    have hDR : D h = -R * (h ^ 4 * C h) / 6 := by
      rw [hRdef]; field_simp
    rw [show Mfun d (p h) (g h) (t h ^ 2) - Mfun d (p h) (g h) (s h * t h) = D h from rfl,
      hDR] at hlow hhigh
    have hlow' : (K - ε / 2) * (h ^ 4 * C h) ≤ R * (h ^ 4 * C h) := by linarith
    have hhigh' : R * (h ^ 4 * C h) ≤ (K + ε / 2) * (h ^ 4 * C h) := by linarith
    have hb1 : K - ε / 2 ≤ R := le_of_mul_le_mul_right hlow' hXpos
    have hb2 : R ≤ K + ε / 2 := le_of_mul_le_mul_right hhigh' hXpos
    rw [Real.dist_eq, abs_sub_lt_iff]
    constructor <;> linarith
  -- assemble
  have hCT6 : Tendsto (fun h => -(C h / 6)) (𝓝[>] (0 : ℝ)) (𝓝 (-(4 * rStar d ^ 2 / 6))) :=
    ((hCT.div_const 6).neg).mono_left nhdsWithin_le_nhds
  have hfin : Tendsto (fun h => -6 * D h / (h ^ 4 * C h) * -(C h / 6)) (𝓝[>] (0 : ℝ))
      (𝓝 (K * -(4 * rStar d ^ 2 / 6))) := hR.mul hCT6
  have hconst : K * -(4 * rStar d ^ 2 / 6) = -(2 * (d : ℝ) ^ 3 / 3) := by
    have hd2 : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    have hdne : (d : ℝ) ≠ 0 := ne_of_gt (by linarith)
    have hd1ne : (d : ℝ) - 1 ≠ 0 := ne_of_gt (by linarith)
    rw [hKdef, rStar_eq, div_pow]
    field_simp
    ring
  rw [hconst] at hfin
  refine hfin.congr' ?_
  filter_upwards [hpos] with h ⟨hh, hhlt⟩
  obtain ⟨hs0, ht1⟩ := hadm h hhlt
  have habs : |h| = h := abs_of_pos hh
  rw [habs] at hs0 ht1
  have hspos : 0 < s h := hs0
  have hst : s h < t h := by simp only [hs, ht]; linarith
  have htpos : 0 < t h := hspos.trans hst
  have hCpos : 0 < C h := by
    simp only [hC]
    have : 0 < t h + 2 * s h := by linarith
    positivity
  have hCne : C h ≠ 0 := ne_of_gt hCpos
  have hhne : h ≠ 0 := ne_of_gt hh
  -- the two sides agree pointwise, once `D h` is recognised inside the target
  rw [show Mfun d (p h) (g h) ((u h + h) ^ 2)
      - Mfun d (p h) (g h) ((u h - h) * (u h + h)) = D h from rfl]
  field_simp

/-- **The right-increment expansion.**

Along the coalescing family of `lem:rank-one-kkt-family`,

    (𝓜_h(t_h²) - 𝓜_h(s_h t_h)) / h⁴  →  -2d³/3   as `h ↓ 0`,

i.e. `B_h = 𝓜_h(t_h²) - 𝓜_h(s_h t_h) = -2d³h⁴/3 + o(h⁴)`.  `SingularEndpoint/RowSign.lean` already
gives `B_h < 0`; this gives its size. -/
theorem exists_family_right_increment_asymptotics (hd : 2 ≤ d) :
    ∃ (h0 : ℝ) (u g p : ℝ → ℝ),
      0 < h0 ∧ u 0 = uStar d ∧ g 0 = gammaStar d ∧ p 0 = pStar d ∧
      Tendsto (fun h : ℝ => (Mfun d (p h) (g h) ((u h + h) ^ 2)
            - Mfun d (p h) (g h) ((u h - h) * (u h + h))) / h ^ 4)
        (𝓝[>] (0 : ℝ)) (𝓝 (-(2 * (d : ℝ) ^ 3 / 3))) := by
  obtain ⟨h0, u, lv, g, p, hh0, hu0, _hlv0, hg0, hp00, hua, _hlva, hga, _hpa,
    hadm, hp01, hellp, _hsym, hkkt⟩ := exists_scalar_family_density hd
  exact ⟨h0, u, g, p, hh0, hu0, hg0, hp00,
    family_right_increment_asymptotics hd hh0 hu0 hg0 hua hga hadm hp01 hellp hkkt⟩

end SingularEndpoint

end UpperTailOptimizers
