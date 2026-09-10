import UpperTailOptimizers.Nondegeneracy.ScalarLower
import UpperTailOptimizers.Graphon.ExternalInputs

/-!
# The quadratic lower bound for graphons (`prop:graphon-quadratic-bound` of `paper/bipodal_optimizer.tex`)

**`prop:graphon-quadratic-bound` (quadratic lower bound for graphons).**  Uniformly for `r` in a
compact subarc `K` of a Lubetzky–Zhao boundary arc: if `e(W) = r - δ` and `t(H,W) ≥ r^m`, then
`I_{pc(r)}(W) ≥ J_{pc(r)}(r) + C δ²`.

The proof applies the scalar quadratic lower bound (`lem:scalar-quadratic-bound`,
`expectation_quadratic_lower`) to the random variable `X = W(U,V)` with `(U,V)`
uniform on `[0,1]²`: the mean of `X` is the edge density, and the generalized
Hölder inequality (`holder_moment`) turns the `H`-density constraint into the
`d`-th moment constraint `E X^d ≥ r^d`.

Unlike the paper's statement, no smallness `δ < δ₀` is required: the bound holds
for every `δ ≥ 0`.
-/

namespace UpperTailOptimizers

open MeasureTheory Real Set

/-- **`prop:graphon-quadratic-bound`.**  There is `C > 0`,
uniform over the compact subarc `K`, such that every graphon `W` with edge density
`r - δ` (`δ ≥ 0`) and `H`-density `≥ r^m` satisfies
`J_{pc(r)}(r) + C δ² ≤ I_{pc(r)}(W)`. -/
theorem quadratic_lower_graphon {d : ℕ} (hd : 2 ≤ d) (M : LZBoundaryArc d)
    {K : Set ℝ} (hK : K ⊆ M.U) (hKc : IsCompact K) (hKne : K.Nonempty)
    {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (hreg : ∀ v, H.degree v = d) (hm : 1 ≤ H.edgeFinset.card) :
    ∃ C : ℝ, 0 < C ∧ ∀ r ∈ K, ∀ δ : ℝ, 0 ≤ δ → ∀ W : Graphon,
      W.edgeDensity = r - δ → r ^ H.edgeFinset.card ≤ W.tDensity H →
      Jp (M.pc r) r + C * δ ^ 2 ≤ W.Ip (M.pc r) := by
  obtain ⟨γ, hγ, hsep⟩ := quadSep_dist hd M hK hKc hKne
  obtain ⟨η, hη0, hη12, hηbd⟩ := arc_uniform_bounds M hK hKc hKne
  have hd1 : 1 ≤ d := le_trans one_le_two hd
  -- the moment gap `η_d ≤ r^d - (sm r)^d` on the family `sm r < r`
  set ηd : ℝ := η ^ (d - 1) * η with hηddef
  have hηd0 : 0 < ηd := by positivity
  refine ⟨γ / (1 + d / ηd) ^ 2, by positivity, ?_⟩
  intro r hr δ hδ W hWe hWt
  obtain ⟨hpc0, hpcr, hr1, hsmne, hsm0, hsm1⟩ := M.ordering r (hK hr)
  have hr0 : 0 < r := lt_trans hpc0 hpcr
  obtain ⟨hηr, hr1', hηs, hs1', hηpc, hηdist⟩ := hηbd r hr
  have hpc1 : M.pc r < 1 := lt_trans hpcr hr1
  have hL : 0 < slope d M.pc r := slope_pos hd1 hpc0 hpcr hr1
  -- case dichotomy at the second contact, with the uniform moment gap on the lower side
  have hcase : r < M.sm r ∨ (M.sm r < r ∧ ηd ≤ r ^ d - (M.sm r) ^ d) := by
    rcases lt_or_gt_of_ne hsmne with hlt | hgt
    · right
      refine ⟨hlt, ?_⟩
      have hkey := pow_sub_pow_ge (x := r) (y := M.sm r) hr0.le hsm0.le hd1
      have habs1 : |r - M.sm r| = r - M.sm r := abs_of_pos (by linarith)
      have hpow_le : (M.sm r) ^ d ≤ r ^ d := pow_le_pow_left₀ hsm0.le hlt.le d
      have habs2 : |r ^ d - (M.sm r) ^ d| = r ^ d - (M.sm r) ^ d :=
        abs_of_nonneg (by linarith)
      rw [habs1, habs2] at hkey
      have h2 : η ≤ r - M.sm r := by
        have habs : |M.sm r - r| = r - M.sm r := by
          rw [abs_of_neg (by linarith : M.sm r - r < 0)]; ring
        linarith [habs]
      have hstep : ηd ≤ (M.sm r) ^ (d - 1) * (r - M.sm r) := by
        rw [hηddef]
        exact mul_le_mul (pow_le_pow_left₀ hη0.le hηs _) h2 hη0.le (pow_nonneg hsm0.le _)
      linarith
    · left; exact hgt
  -- apply the scalar `lem:scalar-quadratic-bound` to `X = W(U,V)` on `([0,1]², gμ)`
  have hmean : ∫ z : ℝ × ℝ, W.toFun z.1 z.2 ∂gμ = r - δ := hWe
  have hmom : r ^ d ≤ ∫ z : ℝ × ℝ, (W.toFun z.1 z.2) ^ d ∂gμ :=
    holder_moment H hreg hd W hr0.le hm hWt
  exact expectation_quadratic_lower (μ := gμ) W.measurable_uncurry
    (fun z => W.mem_Icc z.1 z.2) hd1 hpc0 hpc1 hr0 hr1 hsm0 hsm1 hδ hL hγ hηd0
    (hsep r hr) hcase hmean hmom

end UpperTailOptimizers
