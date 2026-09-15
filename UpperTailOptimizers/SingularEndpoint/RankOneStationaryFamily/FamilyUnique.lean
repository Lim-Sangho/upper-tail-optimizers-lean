import UpperTailOptimizers.SingularEndpoint.RankOneStationaryFamily.FamilySymm
import UpperTailOptimizers.LZBoundary.AnalyticImplicitUnique

/-!
# Local uniqueness of the coalescing scalar family (Section 5, `paper/sections/singular.tex`)

`SingularEndpoint/RankOneStationaryFamily/FamilyExists.lean` builds the analytic family `h ↦ (u_h, ℓ_h, γ_h)` of
`lem:rank-one-kkt-family` and `SingularEndpoint/RankOneStationaryFamily/FamilySymm.lean` establishes its
`h ↦ -h` symmetry.  **This file proves the remaining clause of that lemma: its local
uniqueness.**

The paper's formulation is the lemma's converse assertion: "let `W = f ⊗ f` be a nearby
nonconstant rank-one graphon whose factor `f` is bounded away from `0` and `1`. If `W`
satisfies the KKT conditions with multiplier `μ` and `eq:block-stationarity` holds, then `W`
agrees, up to measure-preserving relabeling, with a unique member `W_h` indexed by
`h ∈ (0, h₀)`, and `μ = μ_h`" — made precise after the statement: once
`lem:stationary-rank-one-bipodality` has put the factor in the form `f_{α,s,t}`, if
`(s, t, p, r, μ, α)` is sufficiently close to `(u_*, u_*, p_*, r_*, 1/(m r_*^m), 1/2)`, then
`h := (t - s)/2` lies in `(0, h₀)` and `(s, t, p, r, μ, α) = (s_h, t_h, p_h, r_h, μ_h, α_h)`.
Its scalar content — the part proved here — is that a nearby triple `(u', ℓ', γ')` solving the
three rank-one KKT equations `eq:three-value-kkt` at a prescribed small half-gap
`h ≠ 0` is *the* family point at `h`.  The paper houses this local uniqueness in
`lem:rank-one-kkt-family` itself; `thm:singular-endpoint` asserts instead
that `W_h` is the unique *minimizer* up to relabelling, and the discussion following the
family lemma refers to the clause as its "local uniqueness assertion".

The proof is the uniqueness half of the implicit function theorem.  `analytic_implicit`
(`LZBoundary/AnalyticIFT.lean`) is replaced by `analytic_implicit_unique`
(`LZBoundary/AnalyticImplicitUnique.lean`), whose statement carries the two neighbourhoods
`S ∋ z₀` and `T ∋ h₀ = 0` together with the clause that `z p` is the *only* zero of `F · p`
in `S`.  The hypotheses fed to it are the same three as in `SingularEndpoint/RankOneStationaryFamily/FamilyExists.lean`:
`analyticAt_Fsys`, `Fsys_base` and `exists_hasStrictFDerivAt_Fsys`.

Two pieces of bookkeeping turn the abstract neighbourhoods into the explicit radii `h₀` and
`ε` of the statement.  For the parameter, `Metric.isOpen_iff` at `0 ∈ T` gives `h₀ > 0` and
`dist h 0 = |h|`.  For the unknown, `Metric.isOpen_iff` at `zBase d ∈ S` gives `ε > 0`, and
the metric on `ℝ × ℝ × ℝ` is the sup metric (`Prod.dist_eq`), so the three coordinate
bounds `|u' - u_*| < ε`, `|ℓ' - ℓ_*| < ε`, `|γ' - γ_*| < ε` are exactly `dist · < ε`.
Finally `lell_three_eq_iff` converts the three original equations into `Fsys = 0`, which is
legitimate precisely because `h ≠ 0`.

## Contents

* `exists_scalar_family_locally_unique` — the local-uniqueness clause of
  `lem:rank-one-kkt-family` in scalar form, with explicit radii `h₀`, `ε`;
* `exists_scalar_family_locally_unique'` — the same with the neighbourhoods left abstract,
  the shape in which `analytic_implicit_unique` delivers it.
-/

namespace UpperTailOptimizers

open Filter Topology

variable {d : ℕ}

/-! ## The sup metric on the triple of unknowns

`Metric.isOpen_iff` produces a ball in `ℝ × ℝ × ℝ`; the statements below quantify instead
over the three coordinates separately.  On a product the distance is the maximum of the
coordinate distances, so the two forms match with the *same* radius. -/

/-- Coordinatewise bounds give membership in a metric ball of `ℝ × ℝ × ℝ` around
`zBase d = (u_*, ℓ_*, γ_*)`: the product metric is the sup metric. -/
private theorem dist_zBase_lt {u' lv' g' ε : ℝ} (hu : |u' - uStar d| < ε)
    (hl : |lv' - ellStar d| < ε) (hg : |g' - gammaStar d| < ε) :
    dist ((u', lv', g') : ℝ × ℝ × ℝ) (zBase d) < ε := by
  have h1 : dist u' (uStar d) < ε := by rw [Real.dist_eq]; exact hu
  have h2 : dist lv' (ellStar d) < ε := by rw [Real.dist_eq]; exact hl
  have h3 : dist g' (gammaStar d) < ε := by rw [Real.dist_eq]; exact hg
  show dist ((u', lv', g') : ℝ × ℝ × ℝ) ((uStar d, ellStar d, gammaStar d) : ℝ × ℝ × ℝ) < ε
  rw [Prod.dist_eq, Prod.dist_eq]
  exact max_lt h1 (max_lt h2 h3)

/-! ## Local uniqueness -/

/-- **Local uniqueness of the coalescing scalar family, with abstract neighbourhoods**
(`lem:rank-one-kkt-family`).

`analytic_implicit_unique` applied to the desingularized system `Fsys`, with the three
equations of `eq:three-value-kkt` substituted for `Fsys = 0` by `lell_three_eq_iff`.
There are an open `S ∋ (u_*, ℓ_*, γ_*)` and an open `T ∋ 0` and an analytic family `z` on
`T` through `zBase d` such that for `h ∈ T` with `h ≠ 0`, every admissible triple in `S`
solving the three rank-one KKT equations at half-gap `h` equals `z h`. -/
theorem exists_scalar_family_locally_unique' (hd : 2 ≤ d) :
    ∃ (S : Set (ℝ × ℝ × ℝ)) (T : Set ℝ) (z : ℝ → ℝ × ℝ × ℝ),
      IsOpen S ∧ zBase d ∈ S ∧ IsOpen T ∧ (0 : ℝ) ∈ T ∧
      z 0 = zBase d ∧ AnalyticAt ℝ z 0 ∧
      (∀ h ∈ T, Fsys d (z h) h = 0) ∧
      (∀ h ∈ T, h ≠ 0 → ∀ w ∈ S,
        0 < w.1 - h → 0 < w.1 + h → (w.1 - h) ^ 2 < 1 → (w.1 + h) ^ 2 < 1 →
        (w.1 - h) * (w.1 + h) < 1 →
        Lell d w.2.1 w.2.2 ((w.1 - h) ^ 2) = 0 →
        Lell d w.2.1 w.2.2 ((w.1 - h) * (w.1 + h)) = 0 →
        Lell d w.2.1 w.2.2 ((w.1 + h) ^ 2) = 0 →
        w = z h) := by
  obtain ⟨a, b, c, e, hb, hc, hL⟩ := exists_hasStrictFDerivAt_Fsys hd
  obtain ⟨S, T, z, hSopen, hzS, hTopen, h0T, hz0, hzan, _hmaps, hzsol, huniq⟩ :=
    analytic_implicit_unique (analyticAt_Fsys hd) (Fsys_base hd) (jac3 a b c e hb hc) hL
  refine ⟨S, T, z, hSopen, hzS, hTopen, h0T, hz0, hzan, hzsol, ?_⟩
  intro h hT hne w hwS hs ht hs1 ht1 hst e1 e2 e3
  refine huniq h hT w hwS ?_
  obtain ⟨q1, q2, q3⟩ := (lell_three_eq_iff hd hne hs ht hs1 ht1 hst).mp ⟨e1, e2, e3⟩
  show (Esys1 d w.2.1 w.2.2 w.1 h, Esys2 d w.2.2 w.1 h, Esys3 d w.2.2 w.1 h) = 0
  rw [q1, q2, q3]
  rfl

/-- **Local uniqueness of the coalescing scalar family**
(`lem:rank-one-kkt-family`).

The scalar form of the lemma's converse assertion, that a nearby nonconstant rank-one
graphon with factor bounded away from `0` and `1`, satisfying the KKT conditions and
`eq:block-stationarity`, "agrees, up to measure-preserving relabeling, with a unique member
`W_h` indexed by `h ∈ (0, h₀)`": there
are radii `h₀ > 0`, `ε > 0` and the analytic family `z` through `(u_*, ℓ_*, γ_*)` solving
the desingularized system on `|h| < h₀`, such that for `0 < |h| < h₀` *every* triple
`(u', ℓ', γ')` within `ε` of the base point, coordinatewise, which is admissible and solves
the three rank-one KKT equations `eq:three-value-kkt` at half-gap `h`, is the family
point `z h`.

This is the scalar content of the local-uniqueness clause of
`lem:rank-one-kkt-family`; `thm:singular-endpoint` states minimizer
uniqueness instead and does not restate it.

The radii come from `Metric.isOpen_iff` applied to the two neighbourhoods produced by
`exists_scalar_family_locally_unique'`; the coordinatewise form of the `ε`-bound is the
sup-metric description `Prod.dist_eq` of the metric on `ℝ × ℝ × ℝ`. -/
theorem exists_scalar_family_locally_unique (hd : 2 ≤ d) :
    ∃ (h0 ε : ℝ) (z : ℝ → ℝ × ℝ × ℝ),
      0 < h0 ∧ 0 < ε ∧ z 0 = zBase d ∧ AnalyticAt ℝ z 0 ∧
      (∀ h : ℝ, |h| < h0 → Fsys d (z h) h = 0) ∧
      (∀ h : ℝ, |h| < h0 → h ≠ 0 →
        ∀ u' lv' g' : ℝ,
          |u' - uStar d| < ε → |lv' - ellStar d| < ε → |g' - gammaStar d| < ε →
          0 < u' - h → 0 < u' + h → (u' - h) ^ 2 < 1 → (u' + h) ^ 2 < 1 →
          (u' - h) * (u' + h) < 1 →
          Lell d lv' g' ((u' - h) ^ 2) = 0 →
          Lell d lv' g' ((u' - h) * (u' + h)) = 0 →
          Lell d lv' g' ((u' + h) ^ 2) = 0 →
          (u', lv', g') = z h) := by
  obtain ⟨S, T, z, hSopen, hzS, hTopen, h0T, hz0, hzan, hzsol, huniq⟩ :=
    exists_scalar_family_locally_unique' hd
  obtain ⟨ε, hε, hballS⟩ := Metric.isOpen_iff.mp hSopen _ hzS
  obtain ⟨h0, hh0, hballT⟩ := Metric.isOpen_iff.mp hTopen _ h0T
  -- `|h| < h₀` is membership in the parameter ball, since `dist h 0 = |h|`
  have hmemT : ∀ h : ℝ, |h| < h0 → h ∈ T := by
    intro h hh
    refine hballT ?_
    rw [Metric.mem_ball, Real.dist_eq, sub_zero]
    exact hh
  refine ⟨h0, ε, z, hh0, hε, hz0, hzan, fun h hh => hzsol h (hmemT h hh), ?_⟩
  intro h hh hne u' lv' g' hu hl hg hs ht hs1 ht1 hst e1 e2 e3
  have hwS : ((u', lv', g') : ℝ × ℝ × ℝ) ∈ S :=
    hballS (Metric.mem_ball.mpr (dist_zBase_lt hu hl hg))
  exact huniq h (hmemT h hh) hne _ hwS hs ht hs1 ht1 hst e1 e2 e3

end UpperTailOptimizers
