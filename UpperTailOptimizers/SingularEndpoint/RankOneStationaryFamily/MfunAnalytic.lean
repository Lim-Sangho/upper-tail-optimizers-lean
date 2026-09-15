import UpperTailOptimizers.SingularEndpoint.RankOneStationaryFamily.Family
import UpperTailOptimizers.NonexceptionalEndpoint.Proof.Analytic

/-!
# Analyticity of `𝓜` along the coalescing family (Section 5, `paper/sections/singular.tex`)

The block weight of `lem:rank-one-kkt-family` is the ratio

`α_h = B_h / (A_h + B_h)`,  `A_h = 𝓜_h(s_h²) - 𝓜_h(s_h t_h)`,
`B_h = 𝓜_h(t_h²) - 𝓜_h(s_h t_h)`,

with `s_h = u_h - h`, `t_h = u_h + h` and `𝓜 = Mfun` of `SingularEndpoint/RankOneStationaryFamily/Family.lean`.  Both
increments vanish to order exactly `4` in `h`, so `α` is a `0/0` at `h = 0`; the way that
indeterminacy is resolved is `exists_analytic_factor_of_tendsto`
(`SingularEndpoint/RankOneStationaryFamily/OrderFactor.lean`), which cancels the common factor `h⁴` and reads off the
value `1/2`.  That factorisation lemma applies only to functions **analytic at `0`**, and
this file supplies exactly that hypothesis for the two increments.

Nothing here is specific to the singular endpoint: the substance is the chain rule for real-analytic
maps applied to `𝓜_{p,γ}(z) = J_p(z) - (γ/d)z^d`, whose only non-elementary ingredient is
the joint analyticity of `J` on `(0,1)²`.  That is already proved, as `analyticAt_Jp_prod`
(`NonexceptionalEndpoint/Proof/Analytic.lean`), and is reused verbatim rather than restated.

The hypotheses of the last three theorems are deliberately spelled with the names and the
shapes that `exists_scalar_family_density` (`SingularEndpoint/RankOneStationaryFamily/FamilySymm.lean`) binds — the analytic
window `h0`, the pointwise analyticity of `u, g, p` on `|h| < h0`, the admissibility pair
`0 < u h - |h| ∧ u h + |h| < 1` and the density bounds `0 < p h ∧ p h < 1` — so that a caller
holding that family can pass them straight through.  Only their values at `h = 0` are used,
where admissibility degenerates to `0 < u 0` and `u 0 < 1`; the window hypothesis `0 < h0`
is what makes `h = 0` a member of it.

## Contents

* `analyticAt_Jp_comp` — `k ↦ J_{P k}(Z k)` is analytic wherever `P` and `Z` are, provided
  both take values in `(0,1)` at the point;
* `analyticAt_Mfun_comp` — the same for `k ↦ 𝓜_d(P k, G k, Z k)` (no `2 ≤ d` needed);
* `analyticAt_left_increment` — analyticity at `0` of `h ↦ 𝓜_h(s_h t_h) - 𝓜_h(s_h²)`,
  i.e. of `-A_h`;
* `analyticAt_right_increment` — analyticity at `0` of `h ↦ 𝓜_h(t_h²) - 𝓜_h(s_h t_h)`,
  i.e. of `B_h`;
* `analyticAt_increment_sum` — analyticity at `0` of the denominator `A_h + B_h`, written in
  the arrangement `(𝓜_h(t_h²) - 𝓜_h(s_h t_h)) + (𝓜_h(s_h²) - 𝓜_h(s_h t_h))`, i.e. `B_h + A_h`
  with each increment in its own `𝓜(·) - 𝓜(s t)` form.
-/

namespace UpperTailOptimizers

/-! ## The chain rule for `J` and `𝓜` -/

/-- **`J` composed with analytic parameters.**  If `P` and `Z` are analytic at `x` and both
land in `(0,1)` there, then `k ↦ J_{P k}(Z k)` is analytic at `x`.

This is `analyticAt_Jp_prod` — the joint analyticity of `J` on `(0,1)²`, proved in
`NonexceptionalEndpoint/Proof/Analytic.lean` — precomposed with `k ↦ (P k, Z k)` via `AnalyticAt.comp₂`. -/
theorem analyticAt_Jp_comp {P Z : ℝ → ℝ} {x : ℝ}
    (hP : AnalyticAt ℝ P x) (hZ : AnalyticAt ℝ Z x)
    (hp0 : 0 < P x) (hp1 : P x < 1) (hz0 : 0 < Z x) (hz1 : Z x < 1) :
    AnalyticAt ℝ (fun k => Jp (P k) (Z k)) x :=
  AnalyticAt.comp₂ (analyticAt_Jp_prod hp0 hp1 hz0 hz1) hP hZ

/-- **`𝓜` composed with analytic parameters.**  `𝓜_{p,γ}(z) = J_p(z) - (γ/d)z^d` is
built from `J` by subtracting a polynomial in `z` with coefficient linear in `γ`, so
`k ↦ 𝓜_d(P k, G k, Z k)` is analytic at `x` as soon as `P, G, Z` are and `P x, Z x ∈ (0,1)`.

No hypothesis `2 ≤ d` is needed: the monomial `z ↦ z^d` is analytic for every `d`, and the
degenerate case `d = 0` merely makes the subtracted term the constant `γ/0 = 0`. -/
theorem analyticAt_Mfun_comp {d : ℕ} {P G Z : ℝ → ℝ} {x : ℝ}
    (hP : AnalyticAt ℝ P x) (hG : AnalyticAt ℝ G x) (hZ : AnalyticAt ℝ Z x)
    (hp0 : 0 < P x) (hp1 : P x < 1) (hz0 : 0 < Z x) (hz1 : Z x < 1) :
    AnalyticAt ℝ (fun k => Mfun d (P k) (G k) (Z k)) x :=
  (analyticAt_Jp_comp hP hZ hp0 hp1 hz0 hz1).sub
    ((hG.div_const (c := (d : ℝ))).mul (hZ.pow d))

/-! ## The two increments of the block weight -/

/-- **The left increment is analytic at `0`.**  Along the coalescing family
`(u_h, g_h, p_h)` of `exists_scalar_family_density`, the function
`h ↦ 𝓜_{p_h,g_h}(s_h t_h) - 𝓜_{p_h,g_h}(s_h²)` — the negative of `A_h` — is analytic at
`h = 0`.

Both arguments `s_h t_h = (u_h - h)(u_h + h)` and `s_h² = (u_h - h)²` are analytic in `h`,
being polynomials in `u_h` and `h`, and at `h = 0` both collapse to `u_0²`, which lies in
`(0,1)` because admissibility at `h = 0` reads `0 < u_0` and `u_0 < 1`. -/
theorem analyticAt_left_increment {d : ℕ} {h0 : ℝ} {u g p : ℝ → ℝ}
    (hh0 : 0 < h0)
    (hua : ∀ h : ℝ, |h| < h0 → AnalyticAt ℝ u h)
    (hga : ∀ h : ℝ, |h| < h0 → AnalyticAt ℝ g h)
    (hpa : ∀ h : ℝ, |h| < h0 → AnalyticAt ℝ p h)
    (hadm : ∀ h : ℝ, |h| < h0 → 0 < u h - |h| ∧ u h + |h| < 1)
    (hpm : ∀ h : ℝ, |h| < h0 → 0 < p h ∧ p h < 1) :
    AnalyticAt ℝ (fun h => Mfun d (p h) (g h) ((u h - h) * (u h + h))
      - Mfun d (p h) (g h) ((u h - h) ^ 2)) 0 := by
  have h00 : |(0 : ℝ)| < h0 := by simpa using hh0
  have hu : AnalyticAt ℝ u 0 := hua 0 h00
  have hg : AnalyticAt ℝ g 0 := hga 0 h00
  have hp : AnalyticAt ℝ p 0 := hpa 0 h00
  have hp1 : 0 < p 0 := (hpm 0 h00).1
  have hp2 : p 0 < 1 := (hpm 0 h00).2
  have hu1 : 0 < u 0 := by simpa using (hadm 0 h00).1
  have hu2 : u 0 < 1 := by simpa using (hadm 0 h00).2
  have hs : AnalyticAt ℝ (fun h : ℝ => u h - h) 0 := hu.sub analyticAt_id
  have ht : AnalyticAt ℝ (fun h : ℝ => u h + h) 0 := hu.add analyticAt_id
  have hst : AnalyticAt ℝ (fun h : ℝ => (u h - h) * (u h + h)) 0 := hs.mul ht
  have hss : AnalyticAt ℝ (fun h : ℝ => (u h - h) ^ 2) 0 := hs.pow 2
  refine (analyticAt_Mfun_comp hp hg hst hp1 hp2 ?_ ?_).sub
    (analyticAt_Mfun_comp hp hg hss hp1 hp2 ?_ ?_)
  · show 0 < (u 0 - 0) * (u 0 + 0)
    nlinarith
  · show (u 0 - 0) * (u 0 + 0) < 1
    nlinarith
  · show 0 < (u 0 - 0) ^ 2
    nlinarith
  · show (u 0 - 0) ^ 2 < 1
    nlinarith

/-- **The right increment is analytic at `0`.**  The mirror image of
`analyticAt_left_increment`: along the same family,
`h ↦ 𝓜_{p_h,g_h}(t_h²) - 𝓜_{p_h,g_h}(s_h t_h)` — the increment `B_h` — is analytic at
`h = 0`.  The proof is identical with `t_h² = (u_h + h)²` in place of `s_h²`. -/
theorem analyticAt_right_increment {d : ℕ} {h0 : ℝ} {u g p : ℝ → ℝ}
    (hh0 : 0 < h0)
    (hua : ∀ h : ℝ, |h| < h0 → AnalyticAt ℝ u h)
    (hga : ∀ h : ℝ, |h| < h0 → AnalyticAt ℝ g h)
    (hpa : ∀ h : ℝ, |h| < h0 → AnalyticAt ℝ p h)
    (hadm : ∀ h : ℝ, |h| < h0 → 0 < u h - |h| ∧ u h + |h| < 1)
    (hpm : ∀ h : ℝ, |h| < h0 → 0 < p h ∧ p h < 1) :
    AnalyticAt ℝ (fun h => Mfun d (p h) (g h) ((u h + h) ^ 2)
      - Mfun d (p h) (g h) ((u h - h) * (u h + h))) 0 := by
  have h00 : |(0 : ℝ)| < h0 := by simpa using hh0
  have hu : AnalyticAt ℝ u 0 := hua 0 h00
  have hg : AnalyticAt ℝ g 0 := hga 0 h00
  have hp : AnalyticAt ℝ p 0 := hpa 0 h00
  have hp1 : 0 < p 0 := (hpm 0 h00).1
  have hp2 : p 0 < 1 := (hpm 0 h00).2
  have hu1 : 0 < u 0 := by simpa using (hadm 0 h00).1
  have hu2 : u 0 < 1 := by simpa using (hadm 0 h00).2
  have hs : AnalyticAt ℝ (fun h : ℝ => u h - h) 0 := hu.sub analyticAt_id
  have ht : AnalyticAt ℝ (fun h : ℝ => u h + h) 0 := hu.add analyticAt_id
  have hst : AnalyticAt ℝ (fun h : ℝ => (u h - h) * (u h + h)) 0 := hs.mul ht
  have htt : AnalyticAt ℝ (fun h : ℝ => (u h + h) ^ 2) 0 := ht.pow 2
  refine (analyticAt_Mfun_comp hp hg htt hp1 hp2 ?_ ?_).sub
    (analyticAt_Mfun_comp hp hg hst hp1 hp2 ?_ ?_)
  · show 0 < (u 0 + 0) ^ 2
    nlinarith
  · show (u 0 + 0) ^ 2 < 1
    nlinarith
  · show 0 < (u 0 - 0) * (u 0 + 0)
    nlinarith
  · show (u 0 - 0) * (u 0 + 0) < 1
    nlinarith

/-- **The denominator of the block weight is analytic at `0`.**  The sum `A_h + B_h` of the
two increments, written in the arrangement

`(𝓜_h(t_h²) - 𝓜_h(s_h t_h)) + (𝓜_h(s_h²) - 𝓜_h(s_h t_h))`,

that is, `B_h + A_h` with each summand kept in its own `𝓜(·) - 𝓜(s_h t_h)` form, is analytic
at `h = 0`.  This is the shape the block-weight quotient `α_h = B_h / (A_h + B_h)` needs.

It is *not* the sum of the two theorems above as stated, because
`analyticAt_left_increment` produces `-A_h`; the rearrangement is by `ring` on the
underlying functions, after which the statement is `B_h - (-A_h)`. -/
theorem analyticAt_increment_sum {d : ℕ} {h0 : ℝ} {u g p : ℝ → ℝ}
    (hh0 : 0 < h0)
    (hua : ∀ h : ℝ, |h| < h0 → AnalyticAt ℝ u h)
    (hga : ∀ h : ℝ, |h| < h0 → AnalyticAt ℝ g h)
    (hpa : ∀ h : ℝ, |h| < h0 → AnalyticAt ℝ p h)
    (hadm : ∀ h : ℝ, |h| < h0 → 0 < u h - |h| ∧ u h + |h| < 1)
    (hpm : ∀ h : ℝ, |h| < h0 → 0 < p h ∧ p h < 1) :
    AnalyticAt ℝ (fun h => (Mfun d (p h) (g h) ((u h + h) ^ 2)
        - Mfun d (p h) (g h) ((u h - h) * (u h + h)))
      + (Mfun d (p h) (g h) ((u h - h) ^ 2)
        - Mfun d (p h) (g h) ((u h - h) * (u h + h)))) 0 := by
  have hfun : (fun h : ℝ => (Mfun d (p h) (g h) ((u h + h) ^ 2)
        - Mfun d (p h) (g h) ((u h - h) * (u h + h)))
      + (Mfun d (p h) (g h) ((u h - h) ^ 2)
        - Mfun d (p h) (g h) ((u h - h) * (u h + h))))
      = fun h : ℝ => (Mfun d (p h) (g h) ((u h + h) ^ 2)
          - Mfun d (p h) (g h) ((u h - h) * (u h + h)))
        - (Mfun d (p h) (g h) ((u h - h) * (u h + h))
          - Mfun d (p h) (g h) ((u h - h) ^ 2)) := by
    funext h; ring
  rw [hfun]
  exact (analyticAt_right_increment hh0 hua hga hpa hadm hpm).sub
    (analyticAt_left_increment hh0 hua hga hpa hadm hpm)

end UpperTailOptimizers
