import E374.Inputs

/-!
# From the (coarse) Weil bound to a square-or-zero residue count

For an odd prime `p`, `c ≠ 0`, and a nonempty `U ⊆ 𝔽_p`,
  `#{z : c ∏_{u∈U}(z-u) is a square (zero included)} ≤ (p + |U| + 5|U|√p) / 2`.
The zero residues are included explicitly, as the draft requires.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.style.longLine false
set_option maxHeartbeats 1600000

noncomputable section
open scoped BigOperators
open Finset

namespace Erdos374.D35

open Classical in
theorem square_count_le (hW : CoarseWeilBound) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (c : ZMod p) (hc : c ≠ 0) (U : Finset (ZMod p)) (hU : U.Nonempty) :
    letI : Fact p.Prime := ⟨hp⟩
    ((Finset.univ.filter (fun z : ZMod p => IsSquare (c * ∏ u ∈ U, (z - u)))).card : ℝ) ≤
      ((p : ℝ) + U.card + 5 * U.card * Real.sqrt p) / 2 := by
  letI : Fact p.Prime := ⟨hp⟩
  set χ := quadraticChar (ZMod p) with hχ
  set f : ZMod p → ZMod p := fun z => ∏ u ∈ U, (z - u) with hf
  -- pointwise identity: 2·[square] = 1 + χ(c f z) + [c f z = 0]
  have hpt : ∀ z : ZMod p,
      2 * (if IsSquare (c * f z) then (1 : ℝ) else 0) =
        1 + ((χ (c * f z) : ℤ) : ℝ) + (if c * f z = 0 then (1 : ℝ) else 0) := by
    intro z
    by_cases h0 : c * f z = 0
    · have hsq : IsSquare (c * f z) := by rw [h0]; exact ⟨0, by ring⟩
      rw [if_pos hsq, if_pos h0, h0, quadraticChar_zero]
      norm_num
    · rw [if_neg h0]
      by_cases hsq : IsSquare (c * f z)
      · rw [if_pos hsq, (quadraticChar_one_iff_isSquare h0).mpr hsq]
        norm_num
      · rw [if_neg hsq, quadraticChar_neg_one_iff_not_isSquare.mpr hsq]
        norm_num
  have hsum := Finset.sum_congr rfl (fun z (_ : z ∈ (Finset.univ : Finset (ZMod p))) => hpt z)
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum
  simp only [Finset.sum_boole, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul,
    mul_one] at hsum
  -- zeros of `c f` lie in `U`
  have hZ : ((Finset.univ.filter (fun z : ZMod p => c * f z = 0)).card : ℝ) ≤ U.card := by
    have hsub : Finset.univ.filter (fun z : ZMod p => c * f z = 0) ⊆ U := by
      intro z hz
      rw [Finset.mem_filter] at hz
      have h2 : f z = 0 := (mul_eq_zero.mp hz.2).resolve_left hc
      rw [hf, Finset.prod_eq_zero_iff] at h2
      obtain ⟨u, hu, hzu⟩ := h2
      rw [sub_eq_zero.mp hzu]; exact hu
    exact_mod_cast Finset.card_le_card hsub
  -- the character sum
  have hchar : ((∑ z : ZMod p, ((χ (c * f z) : ℤ) : ℝ))) ≤ 5 * U.card * Real.sqrt p := by
    have hmul : ∀ z, ((χ (c * f z) : ℤ) : ℝ) = ((χ c : ℤ) : ℝ) * ((χ (f z) : ℤ) : ℝ) := by
      intro z; rw [map_mul]; push_cast; ring
    simp_rw [hmul]
    rw [← Finset.mul_sum]
    have hb := hW p hp hp2 U hU
    have hc1 : |((χ c : ℤ) : ℝ)| = 1 := by
      rcases quadraticChar_dichotomy hc with h | h <;> rw [hχ, h] <;> norm_num
    calc ((χ c : ℤ) : ℝ) * ∑ z : ZMod p, ((χ (f z) : ℤ) : ℝ)
        ≤ |((χ c : ℤ) : ℝ) * ∑ z : ZMod p, ((χ (f z) : ℤ) : ℝ)| := le_abs_self _
      _ = |∑ z : ZMod p, ((χ (f z) : ℤ) : ℝ)| := by rw [abs_mul, hc1, one_mul]
      _ ≤ 5 * U.card * Real.sqrt p := hb
  have : 2 * ((Finset.univ.filter (fun z : ZMod p => IsSquare (c * f z))).card : ℝ) ≤
      (p : ℝ) + 5 * U.card * Real.sqrt p + U.card := by
    rw [hsum]; linarith
  show ((Finset.univ.filter (fun z : ZMod p => IsSquare (c * f z))).card : ℝ) ≤ _
  linarith

end Erdos374.D35

end
