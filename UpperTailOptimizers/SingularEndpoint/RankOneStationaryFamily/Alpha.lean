import UpperTailOptimizers.SingularEndpoint.RankOneStationaryFamily.Order4
import UpperTailOptimizers.SingularEndpoint.RankOneStationaryFamily.Order4Right
import UpperTailOptimizers.SingularEndpoint.RankOneStationaryFamily.OrderFactor
import UpperTailOptimizers.SingularEndpoint.RankOneStationaryFamily.MfunAnalytic
import UpperTailOptimizers.SingularEndpoint.RankOneStationaryFamily.RowSign
import UpperTailOptimizers.SingularEndpoint.RankOneStationaryFamily.Contact

/-!
# The block weight `α_h` of the coalescing family (Section 5, `paper/sections/singular.tex`)

`lem:rank-one-kkt-family` closes the rank-one KKT family by adjoining the
block weight `eq:block-proportion-formula`

`α_h = B_h / (A_h + B_h)`,  `A_h = 𝓜_h(s_h²) - 𝓜_h(s_h t_h)`,
`B_h = 𝓜_h(t_h²) - 𝓜_h(s_h t_h)`,

with `s_h = u_h - h`, `t_h = u_h + h`.  Both increments vanish to order exactly `4` at
`h = 0` — the family expansions give
`A_h, B_h = -2d³h⁴/3 + o(h⁴)` — so the displayed quotient is a `0/0` there and the value
`α_0 = 1/2` has to be produced by cancelling the common factor `h⁴`.

This file performs that cancellation and assembles the result into the exact field list of
`KKTFamily` (`SingularEndpoint/RankOneStationaryFamily/Family.lean`).

**The two difficulties, and how they are met.**

*The `0/0`.*  `exists_analytic_factor_of_tendsto` (`SingularEndpoint/RankOneStationaryFamily/OrderFactor.lean`) turns each of
the two one-sided asymptotics of `SingularEndpoint/RankOneStationaryFamily/Order4.lean` and `SingularEndpoint/RankOneStationaryFamily/Order4Right.lean` into
a genuine factorisation `A_h + B_h = h⁴ G_h`, `B_h = h⁴ G^B_h` with `G, G^B` analytic at `0`
and `G_0 = -4d³/3 ≠ 0`, `G^B_0 = -2d³/3`.  The quotient `G^B/G` is then analytic near `0`,
and away from `h = 0` it *is* `B_h/(A_h + B_h)`.

*Global antisymmetry.*  The structure demands `α_{-h} = 1 - α_h` for **every** real `h`, not
merely on the analytic window.  A quotient defined only near `0` can never satisfy a globally
quantified identity, so the weight actually produced here is the antisymmetrisation

`α_h = (f_h + 1 - f_{-h}) / 2`,  `f = G^B / G`,

which satisfies `α_{-h} = 1 - α_h` and `α_0 = 1/2` identically, by algebra alone, and which
coincides with `f_h = B_h/(A_h + B_h)` for `0 < |h|` small because `f_{-h} = 1 - f_h` there
(the family is even, so reflecting `h` exchanges `A_h` and `B_h`).  The same device is applied
to `u, γ, p` through `evenPart`: `exists_scalar_family_density` only gives their evenness on
its window, and `evenPart` upgrades that to an identity valid on all of `ℝ` without changing
the functions where it matters.

## Contents

* `evenPart` — the even part `(v h + v (-h))/2` of a function, with `evenPart_neg`,
  `evenPart_eq` and `analyticAt_evenPart`;
* `exists_symmetrised_block_weight` — the abstract cancellation: from the two order-`4`
  factorisations and the reflection `A_{-h} = B_h`, a globally antisymmetric analytic `α`
  agreeing with `B/(A+B)` off the origin;
* `exists_scalar_family_even` — `exists_scalar_family_density` with `u, γ, p` replaced by
  their even parts, so that the symmetries hold on all of `ℝ`;
* `family_kkt_of_family` — the three KKT equations on the whole window, the coalescing
  parameter `h = 0` included;
* `exists_family_with_block_weight` — the coalescing family together with its block weight,
  field for field the data of `KKTFamily d`.
-/

namespace UpperTailOptimizers

open Filter Topology

variable {d : ℕ}

/-! ## Even parts

`exists_scalar_family_density` proves `u_{-h} = u_h` only for `|h| < h₀`, while
`KKTFamily` asks for it on all of `ℝ`.  Replacing a function by its even part costs
nothing where the local symmetry already holds and buys the global identity. -/

/-- The **even part** `(v h + v (-h))/2` of a real function. -/
noncomputable def evenPart (v : ℝ → ℝ) : ℝ → ℝ := fun h => (v h + v (-h)) / 2

/-- The even part is even, for every real `h` and with no hypothesis on `v`. -/
theorem evenPart_neg (v : ℝ → ℝ) (h : ℝ) : evenPart v (-h) = evenPart v h := by
  simp only [evenPart, neg_neg]
  ring

/-- Where `v` is already symmetric, its even part agrees with it. -/
theorem evenPart_eq {v : ℝ → ℝ} {h : ℝ} (hv : v (-h) = v h) : evenPart v h = v h := by
  simp only [evenPart, hv]
  ring

/-- The even part is analytic at `h` as soon as `v` is analytic at both `h` and `-h`. -/
theorem analyticAt_evenPart {v : ℝ → ℝ} {h : ℝ} (h1 : AnalyticAt ℝ v h)
    (h2 : AnalyticAt ℝ v (-h)) : AnalyticAt ℝ (evenPart v) h := by
  have hneg : AnalyticAt ℝ (fun k : ℝ => v (-k)) h :=
    AnalyticAt.fun_comp_of_eq h2 analyticAt_id.neg rfl
  exact (h1.add hneg).div_const

/-! ## The abstract cancellation

Everything about the block weight that does not mention the graphon problem: two functions
`A, B` vanishing to order `4` at `0`, exchanged by `h ↦ -h`, produce a globally antisymmetric
analytic weight. -/

/-- **The block weight, abstractly.**

Let `A, B : ℝ → ℝ` be exchanged by reflection, `A_{-h} = B_h`, let `B` and `A + B` be analytic
at `0`, and let both vanish to order exactly `4` there in the one-sided sense
`B_h/h⁴ → c_B ≠ 0` and `(B_h + A_h)/h⁴ → c_D ≠ 0`.  Then there is a radius `h₁ > 0` and a
function `α` with

* `α_0 = 1/2` and `α_{-h} = 1 - α_h` for **every** real `h`;
* `α` analytic on `|h| < h₁`;
* `A_h + B_h ≠ 0` and `α_h = B_h/(A_h + B_h)` for `0 < |h| < h₁`.

`α` is the antisymmetrisation `(f_h + 1 - f_{-h})/2` of `f = G^B/G`, where
`B_h = h⁴ G^B_h` and `A_h + B_h = h⁴ G_h` are the factorisations supplied by
`exists_analytic_factor_of_tendsto`.  Off the origin the common factor `h⁴` cancels, so
`f_h = B_h/(A_h+B_h)`; the reflection hypothesis turns `f_{-h}` into `A_h/(A_h+B_h)`, and the
two combine to `α_h = f_h`.  At the origin the antisymmetrisation returns `1/2` whatever `f`
does, which is why no information about `G^B_0/G_0` is needed. -/
theorem exists_symmetrised_block_weight {A B : ℝ → ℝ} {cD cB : ℝ}
    (hsum : AnalyticAt ℝ (fun h => B h + A h) 0) (hBan : AnalyticAt ℝ B 0)
    (hcD : cD ≠ 0) (hcB : cB ≠ 0)
    (hlimD : Tendsto (fun h : ℝ => (B h + A h) / h ^ 4) (𝓝[>] (0 : ℝ)) (𝓝 cD))
    (hlimB : Tendsto (fun h : ℝ => B h / h ^ 4) (𝓝[>] (0 : ℝ)) (𝓝 cB))
    (hrefl : ∀ h : ℝ, A (-h) = B h) :
    ∃ (h1 : ℝ) (alph : ℝ → ℝ),
      0 < h1 ∧ alph 0 = 1 / 2 ∧
      (∀ h : ℝ, alph (-h) = 1 - alph h) ∧
      (∀ h : ℝ, |h| < h1 → AnalyticAt ℝ alph h) ∧
      (∀ h : ℝ, |h| < h1 → h ≠ 0 → A h + B h ≠ 0 ∧ alph h = B h / (A h + B h)) := by
  obtain ⟨G, hGan, hG0, hGeq⟩ := exists_analytic_factor_of_tendsto (k := 4) hsum hcD hlimD
  obtain ⟨GB, hGBan, _hGB0, hGBeq⟩ := exists_analytic_factor_of_tendsto (k := 4) hBan hcB hlimB
  have hGne0 : G 0 ≠ 0 := by rw [hG0]; exact hcD
  have hall : ∀ᶠ h in 𝓝 (0 : ℝ),
      B h + A h = h ^ 4 * G h ∧ B h = h ^ 4 * GB h ∧ G h ≠ 0 ∧
        AnalyticAt ℝ G h ∧ AnalyticAt ℝ GB h := by
    filter_upwards [hGeq, hGBeq, hGan.continuousAt.eventually_ne hGne0,
      hGan.eventually_analyticAt, hGBan.eventually_analyticAt] with h e1 e2 e3 e4 e5
    exact ⟨e1, e2, e3, e4, e5⟩
  rw [Metric.eventually_nhds_iff] at hall
  obtain ⟨ε, hε, hball⟩ := hall
  have hkey : ∀ h : ℝ, |h| < ε →
      B h + A h = h ^ 4 * G h ∧ B h = h ^ 4 * GB h ∧ G h ≠ 0 ∧
        AnalyticAt ℝ G h ∧ AnalyticAt ℝ GB h := by
    intro h hh
    exact hball (by rw [Real.dist_eq, sub_zero]; exact hh)
  refine ⟨ε, fun h => (GB h / G h + 1 - GB (-h) / G (-h)) / 2, hε, ?_, ?_, ?_, ?_⟩
  · show (GB 0 / G 0 + 1 - GB (-0) / G (-0)) / 2 = 1 / 2
    rw [neg_zero]; ring
  · intro h
    show (GB (-h) / G (-h) + 1 - GB (- -h) / G (- -h)) / 2
      = 1 - (GB h / G h + 1 - GB (-h) / G (-h)) / 2
    rw [neg_neg]; ring
  · intro h hh
    have k1 := hkey h hh
    have k2 := hkey (-h) (by rwa [abs_neg])
    have hf : AnalyticAt ℝ (fun k : ℝ => GB k / G k) h :=
      k1.2.2.2.2.div k1.2.2.2.1 k1.2.2.1
    have hq : AnalyticAt ℝ (fun k : ℝ => GB k / G k) (-h) :=
      k2.2.2.2.2.div k2.2.2.2.1 k2.2.2.1
    have hfneg : AnalyticAt ℝ (fun k : ℝ => GB (-k) / G (-k)) h :=
      AnalyticAt.fun_comp_of_eq hq analyticAt_id.neg rfl
    exact ((hf.add analyticAt_const).sub hfneg).div_const
  · intro h hh hne
    have k1 := hkey h hh
    have k2 := hkey (-h) (by rwa [abs_neg])
    have h4 : (h : ℝ) ^ 4 ≠ 0 := pow_ne_zero 4 hne
    have hn4 : ((-h : ℝ)) ^ 4 ≠ 0 := pow_ne_zero 4 (neg_ne_zero.mpr hne)
    have e1 : A h = B (-h) := by
      have := hrefl (-h); rwa [neg_neg] at this
    have e2 : A (-h) = B h := hrefl h
    have hAB : A h + B h = h ^ 4 * G h := by
      rw [add_comm (A h) (B h)]; exact k1.1
    have hABne : A h + B h ≠ 0 := by rw [hAB]; exact mul_ne_zero h4 k1.2.2.1
    have hAB2 : A h + B h = (-h) ^ 4 * G (-h) := by
      rw [show A h + B h = B (-h) + A (-h) by rw [← e1, e2]]
      exact k2.1
    refine ⟨hABne, ?_⟩
    have r1 : GB h / G h = B h / (A h + B h) := by
      rw [hAB, k1.2.1, mul_div_mul_left _ _ h4]
    have r2 : GB (-h) / G (-h) = A h / (A h + B h) := by
      rw [hAB2, e1, k2.2.1, mul_div_mul_left _ _ hn4]
    show (GB h / G h + 1 - GB (-h) / G (-h)) / 2 = B h / (A h + B h)
    rw [r1, r2]
    field_simp
    ring

/-! ## The symmetrised family

`exists_scalar_family_density` proves the symmetries `u_{-h} = u_h`, `γ_{-h} = γ_h`,
`p_{-h} = p_h` only on its window, whereas `KKTFamily` demands them on all of `ℝ`.
Replacing the three functions by their even parts repairs this without disturbing anything
else: on the window the even part *is* the original function, so every hypothesis of
`SingularEndpoint/RankOneStationaryFamily/Order4.lean`, `SingularEndpoint/RankOneStationaryFamily/Order4Right.lean` and `SingularEndpoint/RankOneStationaryFamily/MfunAnalytic.lean`
transports verbatim. -/

/-- **The coalescing scalar family with globally even data**
(`lem:rank-one-kkt-family`).

`exists_scalar_family_density` with `u, γ, p` replaced by their even parts, so that the
symmetries hold for every real `h` and not merely on `|h| < h₀`.  The remaining clauses are
those of `exists_scalar_family_density`, minus its analyticity clause for `ℓ_h`, which
nothing downstream consumes: what is kept is exactly the hypothesis block that
`family_left_increment_asymptotics`, `family_right_increment_asymptotics` and the
analyticity lemmas of `SingularEndpoint/RankOneStationaryFamily/MfunAnalytic.lean` require. -/
theorem exists_scalar_family_even (hd : 2 ≤ d) :
    ∃ (h0 : ℝ) (u lv g p : ℝ → ℝ),
      0 < h0 ∧
      u 0 = uStar d ∧ lv 0 = ellStar d ∧ g 0 = gammaStar d ∧ p 0 = pStar d ∧
      (∀ h : ℝ, |h| < h0 → AnalyticAt ℝ u h) ∧
      (∀ h : ℝ, |h| < h0 → AnalyticAt ℝ g h) ∧
      (∀ h : ℝ, |h| < h0 → AnalyticAt ℝ p h) ∧
      (∀ h : ℝ, u (-h) = u h) ∧ (∀ h : ℝ, g (-h) = g h) ∧ (∀ h : ℝ, p (-h) = p h) ∧
      (∀ h : ℝ, |h| < h0 → 0 < u h - |h| ∧ u h + |h| < 1) ∧
      (∀ h : ℝ, |h| < h0 → 0 < p h ∧ p h < 1) ∧
      (∀ h : ℝ, |h| < h0 → ell (p h) = lv h) ∧
      (∀ h : ℝ, |h| < h0 → h ≠ 0 →
        Lell d (lv h) (g h) ((u h - h) ^ 2) = 0 ∧
          Lell d (lv h) (g h) ((u h - h) * (u h + h)) = 0 ∧
          Lell d (lv h) (g h) ((u h + h) ^ 2) = 0) := by
  obtain ⟨h0, u, lv, g, p, hh0, hu0, hlv0, hg0, hp00, hua, _hlva, hga, hpa,
    hadm, hp01, hellp, hsym, hkkt⟩ := exists_scalar_family_density hd
  have h0mem : |(0 : ℝ)| < h0 := by simpa using hh0
  have hnegwin : ∀ h : ℝ, |h| < h0 → |(-h)| < h0 := by
    intro h hh; rwa [abs_neg]
  have huS : ∀ h : ℝ, |h| < h0 → evenPart u h = u h :=
    fun h hh => evenPart_eq (hsym h hh).1
  have hgS : ∀ h : ℝ, |h| < h0 → evenPart g h = g h :=
    fun h hh => evenPart_eq (hsym h hh).2.2.1
  have hpS : ∀ h : ℝ, |h| < h0 → evenPart p h = p h :=
    fun h hh => evenPart_eq (hsym h hh).2.2.2
  refine ⟨h0, evenPart u, lv, evenPart g, evenPart p, hh0, ?_, hlv0, ?_, ?_, ?_, ?_, ?_,
    evenPart_neg u, evenPart_neg g, evenPart_neg p, ?_, ?_, ?_, ?_⟩
  · rw [huS 0 h0mem, hu0]
  · rw [hgS 0 h0mem, hg0]
  · rw [hpS 0 h0mem, hp00]
  · exact fun h hh => analyticAt_evenPart (hua h hh) (hua (-h) (hnegwin h hh))
  · exact fun h hh => analyticAt_evenPart (hga h hh) (hga (-h) (hnegwin h hh))
  · exact fun h hh => analyticAt_evenPart (hpa h hh) (hpa (-h) (hnegwin h hh))
  · intro h hh; rw [huS h hh]; exact hadm h hh
  · intro h hh; rw [hpS h hh]; exact hp01 h hh
  · intro h hh; rw [hpS h hh]; exact hellp h hh
  · intro h hh hne; rw [huS h hh, hgS h hh]; exact hkkt h hh hne

/-! ## The KKT equations at the degenerate parameter

Along the family the three equations are only available for `h ≠ 0`, because the
desingularized system of `SingularEndpoint/RankOneStationaryFamily/FamilySystem.lean` divides by `h` and `h²`.  At `h = 0`
the three nodes coalesce at `u_*² = r_*` and the single equation that remains is the
base-point contact identity `Lstar_rStar` of `SingularEndpoint/RankOneStationaryFamily/Contact.lean`. -/

/-- **The three rank-one KKT equations on the whole window**, the degenerate parameter
included `eq:three-value-kkt`.

For `h ≠ 0` this is the family's own conclusion in log-odds form, transported by
`Lell_eq_Fkkt`; for `h = 0` all three nodes equal `u_0² = u_*² = r_*` and the assertion is
`F_{p_*,γ_*}(r_*) = 𝓛_*(r_*) = 0`.

The hypotheses are exactly the clauses of `exists_scalar_family_even` that the proof uses. -/
theorem family_kkt_of_family (hd : 2 ≤ d) {h0 : ℝ} {u lv g p : ℝ → ℝ}
    (hu0 : u 0 = uStar d) (hg0 : g 0 = gammaStar d) (hp0 : p 0 = pStar d)
    (hadm : ∀ h : ℝ, |h| < h0 → 0 < u h - |h| ∧ u h + |h| < 1)
    (hp01 : ∀ h : ℝ, |h| < h0 → 0 < p h ∧ p h < 1)
    (hellp : ∀ h : ℝ, |h| < h0 → ell (p h) = lv h)
    (hkkt : ∀ h : ℝ, |h| < h0 → h ≠ 0 →
      Lell d (lv h) (g h) ((u h - h) ^ 2) = 0 ∧
        Lell d (lv h) (g h) ((u h - h) * (u h + h)) = 0 ∧
        Lell d (lv h) (g h) ((u h + h) ^ 2) = 0) :
    ∀ h : ℝ, |h| < h0 →
      Fkkt d (p h) (g h) ((u h - h) ^ 2) = 0 ∧
        Fkkt d (p h) (g h) ((u h - h) * (u h + h)) = 0 ∧
        Fkkt d (p h) (g h) ((u h + h) ^ 2) = 0 := by
  intro h hh
  rcases eq_or_ne h 0 with rfl | hne
  · have e1 : (u 0 - 0) ^ 2 = rStar d := by rw [sub_zero, hu0, uStar_sq hd]
    have e2 : (u 0 - 0) * (u 0 + 0) = rStar d := by
      rw [show (u 0 - 0) * (u 0 + 0) = (u 0 - 0) ^ 2 by ring, e1]
    have e3 : (u 0 + 0) ^ 2 = rStar d := by
      rw [show (u 0 + 0) ^ 2 = (u 0 - 0) ^ 2 by ring, e1]
    refine ⟨?_, ?_, ?_⟩
    · rw [hp0, hg0, e1]; exact Lstar_rStar hd
    · rw [hp0, hg0, e2]; exact Lstar_rStar hd
    · rw [hp0, hg0, e3]; exact Lstar_rStar hd
  · obtain ⟨hp1, hp2⟩ := hp01 h hh
    obtain ⟨ha1, ha2⟩ := hadm h hh
    have hle := le_abs_self h
    have hle' := neg_abs_le h
    have hs0 : 0 < u h - h := by linarith
    have ht0 : 0 < u h + h := by linarith
    have hs1 : u h - h < 1 := by linarith
    have ht1 : u h + h < 1 := by linarith
    have hz1 : 0 < (u h - h) ^ 2 := pow_pos hs0 2
    have hz1' : (u h - h) ^ 2 < 1 := by nlinarith
    have hz2 : 0 < (u h - h) * (u h + h) := mul_pos hs0 ht0
    have hz2' : (u h - h) * (u h + h) < 1 := by nlinarith
    have hz3 : 0 < (u h + h) ^ 2 := pow_pos ht0 2
    have hz3' : (u h + h) ^ 2 < 1 := by nlinarith
    obtain ⟨k1, k2, k3⟩ := hkkt h hh hne
    have hell := hellp h hh
    refine ⟨?_, ?_, ?_⟩
    · rw [← Lell_eq_Fkkt hp1 hp2 hz1 hz1' (g h), hell]; exact k1
    · rw [← Lell_eq_Fkkt hp1 hp2 hz2 hz2' (g h), hell]; exact k2
    · rw [← Lell_eq_Fkkt hp1 hp2 hz3 hz3' (g h), hell]; exact k3

/-! ## The family with its block weight -/

/-- **The rank-one KKT family, complete with its block weight**
(`lem:rank-one-kkt-family`).

The conclusion is field for field the data of the structure `KKTFamily d`
(`SingularEndpoint/RankOneStationaryFamily/Family.lean`): a family `h ↦ (u_h, γ_h, p_h, α_h)`, analytic on `|h| < h₀` and
passing through `(u_*, γ_*, p_*, 1/2)`, even in `h` except for `α_{-h} = 1 - α_h`,
admissible, satisfying the three rank-one KKT equations `eq:three-value-kkt` at the
nodes `s_h², s_h t_h, t_h²` and the block-weight stationarity `eq:block-proportion-balance`.

The log-odds value `ℓ_h` is carried along only so that its base value `ℓ_*` is recorded;
unlike `u, γ, p, α` it is given **no** analyticity clause here and is not tied to `p_h`,
because `KKTFamily` has no `ℓ` field and nothing downstream needs either fact.

Three points deserve notice.

* The symmetries and `α_{-h} = 1 - α_h` hold for **every** real `h`, not just on the window;
  this is what `exists_scalar_family_even` and the antisymmetrisation inside
  `exists_symmetrised_block_weight` are for.
* The KKT equations and the row balance hold on **all** of `|h| < h₀`, the degenerate
  parameter `h = 0` included; see `family_kkt_of_family`.  At `h = 0` both sides of the row
  balance are `0` outright, the three nodes having coalesced.
* `0 < α_h < 1` comes from `rowBalance_alpha_mem` (`SingularEndpoint/RankOneStationaryFamily/RowSign.lean`) for `h > 0`,
  from the reflection `α_{-h} = 1 - α_h` for `h < 0`, and from `α_0 = 1/2` at the origin. -/
theorem exists_family_with_block_weight (hd : 2 ≤ d) :
    ∃ (h0 : ℝ) (u lv g p alph : ℝ → ℝ),
      0 < h0 ∧
      u 0 = uStar d ∧ lv 0 = ellStar d ∧ g 0 = gammaStar d ∧ p 0 = pStar d ∧
      alph 0 = 1 / 2 ∧
      (∀ h : ℝ, |h| < h0 → AnalyticAt ℝ u h) ∧
      (∀ h : ℝ, |h| < h0 → AnalyticAt ℝ g h) ∧
      (∀ h : ℝ, |h| < h0 → AnalyticAt ℝ p h) ∧
      (∀ h : ℝ, |h| < h0 → AnalyticAt ℝ alph h) ∧
      (∀ h : ℝ, u (-h) = u h) ∧ (∀ h : ℝ, g (-h) = g h) ∧ (∀ h : ℝ, p (-h) = p h) ∧
      (∀ h : ℝ, alph (-h) = 1 - alph h) ∧
      (∀ h : ℝ, |h| < h0 → 0 < p h ∧ p h < 1) ∧
      (∀ h : ℝ, |h| < h0 → 0 < u h - |h| ∧ u h + |h| < 1) ∧
      (∀ h : ℝ, |h| < h0 → 0 < alph h ∧ alph h < 1) ∧
      (∀ h : ℝ, |h| < h0 → Fkkt d (p h) (g h) ((u h - h) ^ 2) = 0) ∧
      (∀ h : ℝ, |h| < h0 → Fkkt d (p h) (g h) ((u h - h) * (u h + h)) = 0) ∧
      (∀ h : ℝ, |h| < h0 → Fkkt d (p h) (g h) ((u h + h) ^ 2) = 0) ∧
      (∀ h : ℝ, |h| < h0 →
        alph h * (Mfun d (p h) (g h) ((u h - h) ^ 2)
            - Mfun d (p h) (g h) ((u h - h) * (u h + h)))
          = (1 - alph h) * (Mfun d (p h) (g h) ((u h + h) ^ 2)
            - Mfun d (p h) (g h) ((u h - h) * (u h + h)))) := by
  obtain ⟨h0, u, lv, g, p, hh0, hu0, hlv0, hg0, hp00, hua, hga, hpa, hueven, hgeven,
    hpeven, hadm, hp01, hellp, hkkt⟩ := exists_scalar_family_even hd
  have hFk := family_kkt_of_family hd hu0 hg0 hp00 hadm hp01 hellp hkkt
  -- the two increments along the family
  obtain ⟨Afn, hAfn⟩ : ∃ Afn : ℝ → ℝ, Afn = fun h =>
      Mfun d (p h) (g h) ((u h - h) ^ 2)
        - Mfun d (p h) (g h) ((u h - h) * (u h + h)) := ⟨_, rfl⟩
  obtain ⟨Bfn, hBfn⟩ : ∃ Bfn : ℝ → ℝ, Bfn = fun h =>
      Mfun d (p h) (g h) ((u h + h) ^ 2)
        - Mfun d (p h) (g h) ((u h - h) * (u h + h)) := ⟨_, rfl⟩
  have hsumAn : AnalyticAt ℝ (fun h => Bfn h + Afn h) 0 := by
    simp only [hAfn, hBfn]
    exact analyticAt_increment_sum hh0 hua hga hpa hadm hp01
  have hBan : AnalyticAt ℝ Bfn 0 := by
    simp only [hBfn]
    exact analyticAt_right_increment hh0 hua hga hpa hadm hp01
  have hlimB : Tendsto (fun h : ℝ => Bfn h / h ^ 4) (𝓝[>] (0 : ℝ))
      (𝓝 (-(2 * (d : ℝ) ^ 3 / 3))) := by
    simp only [hBfn]
    exact family_right_increment_asymptotics hd hh0 hu0 hg0 hua hga hadm hp01 hellp hkkt
  have hlimA : Tendsto (fun h : ℝ => Afn h / h ^ 4) (𝓝[>] (0 : ℝ))
      (𝓝 (-(2 * (d : ℝ) ^ 3 / 3))) := by
    have hl := family_left_increment_asymptotics hd hh0 hu0 hg0 hua hga hadm hp01 hellp hkkt
    refine hl.neg.congr ?_
    intro x
    simp only [hAfn]
    ring
  have hlimD : Tendsto (fun h : ℝ => (Bfn h + Afn h) / h ^ 4) (𝓝[>] (0 : ℝ))
      (𝓝 (-(4 * (d : ℝ) ^ 3 / 3))) := by
    have hs := hlimB.add hlimA
    rw [show -(2 * (d : ℝ) ^ 3 / 3) + -(2 * (d : ℝ) ^ 3 / 3) = -(4 * (d : ℝ) ^ 3 / 3) by ring]
      at hs
    exact hs.congr fun x => (add_div _ _ _).symm
  have hd2 : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hd3 : (0 : ℝ) < (d : ℝ) ^ 3 := pow_pos (by linarith) 3
  have hcD : -(4 * (d : ℝ) ^ 3 / 3) ≠ 0 := by intro hcon; linarith
  have hcB : -(2 * (d : ℝ) ^ 3 / 3) ≠ 0 := by intro hcon; linarith
  have hrefl : ∀ h : ℝ, Afn (-h) = Bfn h := by
    intro h
    simp only [hAfn, hBfn, hueven, hgeven, hpeven]
    rw [show u h - -h = u h + h by ring, show u h + -h = u h - h by ring,
      mul_comm (u h + h) (u h - h)]
  obtain ⟨h1, alph, hh1, halph0, halphrefl, halphan, halphkey⟩ :=
    exists_symmetrised_block_weight hsumAn hBan hcD hcB hlimD hlimB hrefl
  -- one radius for the family and for the weight
  obtain ⟨h2, hh2, hh2a, hh2b⟩ : ∃ h2 : ℝ, 0 < h2 ∧ h2 ≤ h0 ∧ h2 ≤ h1 :=
    ⟨min h0 h1, lt_min hh0 hh1, min_le_left _ _, min_le_right _ _⟩
  have hwin0 : ∀ h : ℝ, |h| < h2 → |h| < h0 := fun h hh => lt_of_lt_of_le hh hh2a
  have hwin1 : ∀ h : ℝ, |h| < h2 → |h| < h1 := fun h hh => lt_of_lt_of_le hh hh2b
  -- the block weight is a genuine convex weight
  have halphpos : ∀ h : ℝ, 0 < h → |h| < h2 → 0 < alph h ∧ alph h < 1 := by
    intro h hpos hh
    have hh' : |h| < h0 := hwin0 h hh
    obtain ⟨hp1, hp2⟩ := hp01 h hh'
    obtain ⟨ha1, ha2⟩ := hadm h hh'
    have hle := le_abs_self h
    have hle' := neg_abs_le h
    have hs0 : 0 < u h - h := by linarith
    have ht0 : 0 < u h + h := by linarith
    have ht1 : u h + h < 1 := by linarith
    have hst : u h - h < u h + h := by linarith
    have hz1 : 0 < (u h - h) ^ 2 := pow_pos hs0 2
    have hz12 : (u h - h) ^ 2 < (u h - h) * (u h + h) := by nlinarith
    have hz23 : (u h - h) * (u h + h) < (u h + h) ^ 2 := by nlinarith
    have hz3 : (u h + h) ^ 2 < 1 := by nlinarith
    obtain ⟨_, heq⟩ := halphkey h (hwin1 h hh) (ne_of_gt hpos)
    obtain ⟨f1, f2, f3⟩ := hFk h hh'
    rw [heq]
    simp only [hAfn, hBfn]
    exact rowBalance_alpha_mem hd hp1 hp2 hz1 hz12 hz23 hz3 f1 f2 f3
  have halphmem : ∀ h : ℝ, |h| < h2 → 0 < alph h ∧ alph h < 1 := by
    intro h hh
    rcases lt_trichotomy h 0 with hlt | rfl | hgt
    · have hnh : 0 < -h := by linarith
      have hb := halphpos (-h) hnh (by rwa [abs_neg])
      rw [halphrefl h] at hb
      exact ⟨by linarith [hb.2], by linarith [hb.1]⟩
    · rw [halph0]; norm_num
    · exact halphpos h hgt hh
  -- block-weight stationarity, degenerate parameter included
  have hrow : ∀ h : ℝ, |h| < h2 →
      alph h * (Mfun d (p h) (g h) ((u h - h) ^ 2)
          - Mfun d (p h) (g h) ((u h - h) * (u h + h)))
        = (1 - alph h) * (Mfun d (p h) (g h) ((u h + h) ^ 2)
          - Mfun d (p h) (g h) ((u h - h) * (u h + h))) := by
    intro h hh
    rcases eq_or_ne h 0 with rfl | hne
    · rw [show (u 0 - 0) * (u 0 + 0) = (u 0 - 0) ^ 2 by ring,
        show (u 0 + 0) ^ 2 = (u 0 - 0) ^ 2 by ring, sub_self, mul_zero, mul_zero]
    · obtain ⟨hden, heq⟩ := halphkey h (hwin1 h hh) hne
      have hA : Afn h = Mfun d (p h) (g h) ((u h - h) ^ 2)
          - Mfun d (p h) (g h) ((u h - h) * (u h + h)) := by rw [hAfn]
      have hB : Bfn h = Mfun d (p h) (g h) ((u h + h) ^ 2)
          - Mfun d (p h) (g h) ((u h - h) * (u h + h)) := by rw [hBfn]
      rw [← hA, ← hB, heq]
      field_simp
      ring
  exact ⟨h2, u, lv, g, p, alph, hh2, hu0, hlv0, hg0, hp00, halph0,
    fun h hh => hua h (hwin0 h hh), fun h hh => hga h (hwin0 h hh),
    fun h hh => hpa h (hwin0 h hh), fun h hh => halphan h (hwin1 h hh),
    hueven, hgeven, hpeven, halphrefl,
    fun h hh => hp01 h (hwin0 h hh), fun h hh => hadm h (hwin0 h hh), halphmem,
    fun h hh => (hFk h (hwin0 h hh)).1, fun h hh => (hFk h (hwin0 h hh)).2.1,
    fun h hh => (hFk h (hwin0 h hh)).2.2, hrow⟩

end UpperTailOptimizers
