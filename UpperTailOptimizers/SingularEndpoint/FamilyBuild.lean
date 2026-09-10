import UpperTailOptimizers.SingularEndpoint.Alpha

/-!
# The coalescing family exists (Section 7, `paper/singular_endpoint.tex`)

`SingularEndpoint/Family.lean` transcribes `lem:rank-one-kkt-family` as a structure,
`KKTFamily d`, and derives from it the candidate graphon `W_h` together with its edge
density, moment, cost and `H`-density.  Everything downstream of that file is therefore
*conditional* on such a family existing.

This file discharges that hypothesis.  All the analytic work is already done:
`exists_family_with_block_weight` (`SingularEndpoint/Alpha.lean`) produces the family
`(h₀, u, ℓ, γ, p, α)` with the exact list of properties the structure asks for — the analytic
window, the values at the coalescing parameter `h = 0`, the symmetries `u_{-h} = u_h`,
`γ_{-h} = γ_h`, `p_{-h} = p_h`, `α_{-h} = 1 - α_h`, admissibility of the two factor values
and of `p_h`, the convexity `0 < α_h < 1` of the block weight, the three KKT equations
`eq:endpoint-entropy-derivatives` at `s_h², s_h t_h, t_h²`, and the block-weight
stationarity `eq:block-proportion-balance`.  What remains is to read that existential statement
into the fields of the structure, which is what happens here.

The auxiliary function `ℓ` of the existential — the value `ell (p_h)` of the log-odds
along the family — is not a field of `KKTFamily` and is discarded.

## Contents

* `exists_kktFamily` — `Nonempty (KKTFamily d)` for `2 ≤ d`;
* `kktFamily` — a choice-selected term of `KKTFamily d`.
-/

namespace UpperTailOptimizers

namespace SingularEndpoint

variable {d : ℕ}

/-- **The rank-one KKT family exists**
(`lem:rank-one-kkt-family`).

For every `d ≥ 2` the data assembled by `exists_family_with_block_weight` populates every
field of `KKTFamily d`, so the structure is inhabited and all results derived from an
arbitrary `KKTFamily d` are unconditional. -/
theorem exists_kktFamily (hd : 2 ≤ d) : Nonempty (KKTFamily d) := by
  obtain ⟨h0, u, _lv, g, p, alph, hh0, hu0, _hlv0, hg0, hp0, halph0,
    hua, hga, hpa, halpha, hueven, hgeven, hpeven, halphrefl,
    hp01, hadm, halphmem, hkss, hkst, hktt, hrow⟩ :=
    exists_family_with_block_weight hd
  exact
    ⟨{ h₀ := h0
       h₀_pos := hh0
       u := u
       p := p
       gam := g
       alph := alph
       u_zero := hu0
       p_zero := hp0
       gam_zero := hg0
       alph_zero := halph0
       analyticAt_u := hua
       analyticAt_p := hpa
       analyticAt_gam := hga
       analyticAt_alph := halpha
       u_even := hueven
       p_even := hpeven
       gam_even := hgeven
       alph_reflect := halphrefl
       p_mem := hp01
       factor_mem := hadm
       alph_mem := halphmem
       kkt_ss := hkss
       kkt_st := hkst
       kkt_tt := hktt
       rowBalance := hrow }⟩

/-- **A rank-one KKT family**, selected from `exists_kktFamily`.

This is `noncomputable` and choice-based: it is `Classical.choice` applied to the
`Nonempty (KKTFamily d)` witness, so nothing about the family can be extracted from it
beyond the fields of the structure.  It exists to let statements about the family be phrased
as properties of a term rather than under an existential quantifier. -/
noncomputable def kktFamily (hd : 2 ≤ d) : KKTFamily d :=
  Classical.choice (exists_kktFamily hd)

end SingularEndpoint

end UpperTailOptimizers
