import UpperProfileGridArithmetic
import UpperProfileGridStorage

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000
noncomputable section
namespace UpperProfileGridSoundness
open UpperProfileGridArithmetic UpperProfileGridStorage

def rowPoint (i : ℕ) : ℝ := 2+(i : ℝ)/40
def cut (j : ℕ) : ℝ := 2+((j : ℝ)+1)/40
def edge (k : ℕ) : ℝ := 1+(k : ℝ)/400
def kernel (c s : ℝ) : ℝ := max 0 ((c+1-max 3 s)/s)
def cumulativeRectangles (i j : ℕ) : ℝ :=
  (1/400 : ℝ)*∑ k ∈ Finset.range (outerCount i j), kernel (cut j) (rowPoint i*edge k-1)
def forcingRectangles (i : ℕ) : ℝ :=
  (1/400 : ℝ)*∑ k ∈ Finset.range (forcingCount i), (3/(rowPoint i*edge k-1)-1)

theorem parameter_eq (i k : ℕ) :
    rowPoint i*edge k-1 = (denominator i k : ℝ)/16000 := by
  simp only [rowPoint, edge, denominator, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  ring

theorem parameter_pos (i k : ℕ) : 0 < rowPoint i*edge k-1 := by
  rw [parameter_eq]
  exact div_pos (by exact_mod_cast denominator_pos i k) (by norm_num)

theorem inverse_bound (i k : ℕ) :
    1/(rowPoint i*edge k-1) ≤ (roundedInverse i k : ℝ)/scale := by
  have hd : (0 : ℝ)<denominator i k := by exact_mod_cast denominator_pos i k
  have hs : (0 : ℝ)<scale := by norm_num [scale]
  have h := ceilDiv_bound (16000*scale) (denominator i k) (denominator_pos i k)
  rw [parameter_eq]
  have he : (1 : ℝ)/((denominator i k : ℝ)/16000) = 16000/(denominator i k : ℝ) := by
    field_simp
  rw [he]
  apply (div_le_div_iff₀ hd hs).mpr
  exact_mod_cast h

theorem cumulative_term_le (i j k : ℕ) (hk : k < outerCount i j) :
    (1/400 : ℝ)*kernel (cut j) (rowPoint i*edge k-1) ≤
      (if k<forcingCount i then ((j : ℝ)+1)*(roundedInverse i k : ℝ)
       else ((j : ℝ)+121)*(roundedInverse i k : ℝ)-40*(scale : ℝ))/(16000*(scale : ℝ)) := by
  have ht := parameter_pos i k
  have hi := inverse_bound i k
  have hact : rowPoint i*edge k-1 ≤ cut j+1 := by
    have h := outer_active i j k hk
    have h' : (denominator i k : ℝ)<400*(121+(j : ℝ)) := by exact_mod_cast h
    rw [parameter_eq]
    unfold cut
    linarith
  unfold kernel
  split_ifs with hsmall
  · have hs3 : rowPoint i*edge k-1 ≤ 3 := by
      have h := (forcing_split i k).mpr hsmall
      have h' : (denominator i k : ℝ)<48000 := by exact_mod_cast h
      rw [parameter_eq]
      linarith
    rw [max_eq_left hs3]
    have hn : 0 ≤ (cut j+1-3)/(rowPoint i*edge k-1) := by
      apply div_nonneg
      · unfold cut
        have := Nat.cast_nonneg (α := ℝ) j
        linarith
      · exact ht.le
    rw [max_eq_right hn]
    have h := mul_le_mul_of_nonneg_left hi (show (0 : ℝ) ≤ ((j : ℝ)+1)/16000 by positivity)
    convert h using 1 <;> simp only [cut, scale, Nat.cast_ofNat] <;> ring
  · have hs3 : 3 ≤ rowPoint i*edge k-1 := by
      have h : 48000 ≤ denominator i k := by
        exact Nat.le_of_not_gt (fun h => hsmall ((forcing_split i k).mp h))
      have h' : (48000 : ℝ)≤denominator i k := by exact_mod_cast h
      rw [parameter_eq]
      linarith
    rw [max_eq_right hs3, max_eq_right (div_nonneg (sub_nonneg.mpr hact) ht.le)]
    have h := sub_le_sub_right (mul_le_mul_of_nonneg_left hi
      (show (0 : ℝ) ≤ ((j : ℝ)+121)/16000 by positivity)) (1/400)
    convert h using 1 <;> simp only [cut, scale, Nat.cast_ofNat] <;> field_simp [ne_of_gt ht] <;> ring

theorem forcing_term_le (i k : ℕ) :
    (1/400 : ℝ)*(3/(rowPoint i*edge k-1)-1) ≤
      (3*(roundedInverse i k : ℝ)-(scale : ℝ))/(400*(scale : ℝ)) := by
  have h := sub_le_sub_right (mul_le_mul_of_nonneg_left (inverse_bound i k)
    (show (0 : ℝ)≤3/400 by norm_num)) (1/400)
  convert h using 1 <;> norm_num only [scale, Nat.cast_ofNat] <;> ring

theorem matrix_round_bound (i j : ℕ) (p : ℕ → ℕ) :
    ((positiveNumerator i j p : ℝ)-((outerCount i j-forcingCount i : ℕ) : ℝ)*40*(scale : ℝ)) /
      (16000*(scale : ℝ)) ≤ (matrixEntry i p j : ℝ)/scale := by
  have ha := ceilDiv_real_bound (positiveNumerator i j p) 16000 (by norm_num)
  have hb := cast_sub_bound (ceilDiv (positiveNumerator i j p) 16000)
    ((outerCount i j-forcingCount i)*(scale/400))
  have h := (sub_le_sub_right ha (((outerCount i j-forcingCount i)*(scale/400) : ℕ) : ℝ)).trans hb
  have h' := div_le_div_of_nonneg_right h (show (0 : ℝ)≤scale by norm_num [scale])
  unfold matrixEntry
  convert h' using 1
  norm_num only [scale, Nat.reduceDiv, Nat.cast_mul, Nat.cast_ofNat]
  ring

theorem force_round_bound (i : ℕ) (p : ℕ → ℕ) :
    (3*(p (forcingCount i) : ℝ)-(forcingCount i : ℝ)*(scale : ℝ))/(400*(scale : ℝ)) ≤
      (forceEntry i p : ℝ)/scale := by
  have ha := ceilDiv_real_bound (3*p (forcingCount i)) 400 (by norm_num)
  have hb := cast_sub_bound (ceilDiv (3*p (forcingCount i)) 400) (forcingCount i*(scale/400))
  have h := (sub_le_sub_right ha ((forcingCount i*(scale/400) : ℕ) : ℝ)).trans hb
  have h' := div_le_div_of_nonneg_right h (show (0 : ℝ)≤scale by norm_num [scale])
  unfold forceEntry
  convert h' using 1
  norm_num only [scale, Nat.reduceDiv, Nat.cast_mul, Nat.cast_ofNat]
  ring

theorem cumulative_prefix_bound (i j : ℕ) (p : ℕ → ℕ) (hj : j<720)
    (hc : increments (roundedInverse i) p 0 (prefixLength i) = true) (hz : p 0=0) :
    cumulativeRectangles i j ≤ (matrixEntry i p j : ℝ)/scale := by
  have hs := increments_split (roundedInverse i) p (prefixLength i) hc hz
    (forcingCount i) (outerCount i j) (forcing_le_outer i j) (outer_le_prefixLength i j hj)
    ((j : ℝ)+1) ((j : ℝ)+121) (40*(scale : ℝ))
  have h := Finset.sum_le_sum (s := Finset.range (outerCount i j))
    (fun k hk => cumulative_term_le i j k (Finset.mem_range.mp hk))
  rw [← Finset.mul_sum, ← Finset.sum_div, hs] at h
  apply h.trans
  convert matrix_round_bound i j p using 1
  simp only [positiveNumerator, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  ring

theorem forcing_prefix_bound (i : ℕ) (p : ℕ → ℕ)
    (hc : increments (roundedInverse i) p 0 (prefixLength i) = true) (hz : p 0=0) :
    forcingRectangles i ≤ (forceEntry i p : ℝ)/scale := by
  have hk : forcingCount i ≤ prefixLength i := forcing_le_outer i 719
  have hp := increments_prefix (roundedInverse i) p (prefixLength i) hc hz (forcingCount i) hk
  have hp' : (∑ k ∈ Finset.range (forcingCount i), (roundedInverse i k : ℝ)) = p (forcingCount i) := by
    rw [hp, Nat.cast_sum]
  have h := Finset.sum_le_sum (s := Finset.range (forcingCount i)) (fun k _ => forcing_term_le i k)
  have hn : (∑ k ∈ Finset.range (forcingCount i),
      (3*(roundedInverse i k : ℝ)-(scale : ℝ))) =
      3*(p (forcingCount i) : ℝ)-(forcingCount i : ℝ)*(scale : ℝ) := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hp']
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [← Finset.mul_sum, ← Finset.sum_div, hn] at h
  exact h.trans (force_round_bound i p)

theorem forcing_coverage (i : ℕ) : 4/rowPoint i ≤ 1+(forcingCount i : ℝ)/400 := by
  have h : (64000 : ℝ)≤(80+(i : ℝ))*(400+(forcingCount i : ℝ)) := by exact_mod_cast forcing_cover i
  have hp : 0<rowPoint i := by unfold rowPoint; positivity
  apply (div_le_iff₀ hp).mpr
  unfold rowPoint
  nlinarith

theorem forcing_left (i k : ℕ) (hk : k<forcingCount i) : edge k ≤ 4/rowPoint i := by
  have h : (denominator i k : ℝ)<48000 := by exact_mod_cast (forcing_split i k).mpr hk
  have hp : 0<rowPoint i := by unfold rowPoint; positivity
  apply (le_div_iff₀ hp).mpr
  have he := parameter_eq i k
  nlinarith

theorem cumulative_coverage (i j : ℕ) : cut j+2 ≤ rowPoint i*edge (outerCount i j) := by
  have h : (400 : ℝ)*(121+(j : ℝ)+40) ≤ (80+(i : ℝ))*(400+(outerCount i j : ℝ)) := by
    exact_mod_cast outer_cover i j
  unfold cut rowPoint edge
  nlinarith

theorem weighted_telescope (v : ℕ → ℝ) (N : ℕ) :
    (∑ j ∈ Finset.range N, (v j-v (j+1))*((j : ℝ)+1)) =
      (∑ j ∈ Finset.range N, v j)-(N : ℝ)*v N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    push_cast
    ring

theorem area_identity (v : ℕ → ℝ) (N : ℕ) (hv : v N=0) :
    (∑ j ∈ Finset.range N, (v j-v (j+1))*(cut j-2)) =
      (∑ j ∈ Finset.range N, v j)/40 := by
  have he : (∑ j ∈ Finset.range N, (v j-v (j+1))*(cut j-2)) =
      (∑ j ∈ Finset.range N, (v j-v (j+1))*((j : ℝ)+1))/40 := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    unfold cut
    ring
  rw [he, weighted_telescope, hv, mul_zero, sub_zero]

run_cmd do
  for decl in [``parameter_eq, ``parameter_pos, ``inverse_bound, ``cumulative_term_le,
      ``forcing_term_le, ``matrix_round_bound, ``force_round_bound, ``cumulative_prefix_bound,
      ``forcing_prefix_bound, ``forcing_coverage, ``forcing_left, ``cumulative_coverage,
      ``weighted_telescope, ``area_identity] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "FINER GRID PREFIX RECTANGLE AND AREA SOUNDNESS"
end UpperProfileGridSoundness
end
