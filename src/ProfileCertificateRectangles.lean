import ProfileCertificateArithmetic

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000

noncomputable section
namespace ProfileCertificateRectangles
open ProfileCertificateArithmetic

def rowPoint (i : ℕ) : ℝ := ((i : ℝ)+10)/5
def childPoint (j : ℕ) : ℝ := ((j : ℝ)+11)/5
def outerPoint (k : ℕ) : ℝ := 1+(k : ℝ)/50
def cumulativeKernel (c s : ℝ) : ℝ := max 0 ((c+1-max 3 s)/s)
def cumulativeRectangles (i j : ℕ) : ℝ :=
  (1/50 : ℝ) * ∑ k ∈ Finset.range (outerCount i j),
    cumulativeKernel (childPoint j) (rowPoint i * outerPoint k - 1)
def forcingRectangles (i : ℕ) : ℝ :=
  (1/50 : ℝ) * ∑ k ∈ Finset.range (forcingCount i),
    (3/(rowPoint i * outerPoint k - 1)-1)

def roundedTerm (i j k : ℕ) : ℤ :=
  if denominator i k < 750 then ((j+1)*roundedInverse i k : ℕ)
  else ((j+16)*roundedInverse i k : ℕ) - (scale/50 : ℕ)
def roundedCumulative (i j : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (outerCount i j), roundedTerm i j k
def roundedForceTerm (i k : ℕ) : ℤ :=
  Int.ofNat (15*roundedInverse i k) - Int.ofNat (scale/50)
def roundedForcing (i : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (forcingCount i), roundedForceTerm i k

theorem parameter_eq (i k : ℕ) :
    rowPoint i * outerPoint k - 1 = (denominator i k : ℝ)/250 := by
  simp only [rowPoint, outerPoint, denominator, Nat.cast_add, Nat.cast_mul,
    Nat.cast_ofNat]
  ring

theorem cumulative_term_le (i j k : ℕ)
    (hactive : denominator i k ≤ 50*(j+16)) :
    (1/50 : ℝ) * cumulativeKernel (childPoint j)
      (rowPoint i * outerPoint k - 1) ≤ (roundedTerm i j k : ℝ)/scale := by
  have hd : (0 : ℝ) < denominator i k := by exact_mod_cast denominator_pos i k
  have hact : (denominator i k : ℝ) ≤ 50*((j : ℝ)+16) := by exact_mod_cast hactive
  have hi := roundedInverse_real_bound i k
  rw [parameter_eq]
  unfold cumulativeKernel childPoint roundedTerm
  split_ifs with hsmall
  · have hd3 : (denominator i k : ℝ)/250 ≤ 3 := by
      have : (denominator i k : ℝ) < 750 := by exact_mod_cast hsmall
      linarith
    rw [max_eq_left hd3]
    have hn : 0 ≤ (((j : ℝ)+11)/5+1-3) / ((denominator i k : ℝ)/250) := by
      apply div_nonneg
      · have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
        linarith
      · positivity
    rw [max_eq_right hn]
    have hid := mul_le_mul_of_nonneg_left hi (show (0 : ℝ) ≤ j+1 by positivity)
    push_cast
    convert hid using 1
    · field_simp [ne_of_gt hd]
      ring
    · field_simp [ne_of_gt hd]
  · have hd3 : 3 ≤ (denominator i k : ℝ)/250 := by
      have : 750 ≤ denominator i k := by omega
      have : (750 : ℝ) ≤ (denominator i k : ℝ) := by exact_mod_cast this
      linarith
    rw [max_eq_right hd3]
    have hn : 0 ≤ (((j : ℝ)+11)/5+1-(denominator i k : ℝ)/250) /
        ((denominator i k : ℝ)/250) := by
      apply div_nonneg
      · linarith
      · positivity
    rw [max_eq_right hn]
    have hid := mul_le_mul_of_nonneg_left hi (show (0 : ℝ) ≤ j+16 by positivity)
    push_cast
    norm_num only [scale, Nat.reduceDiv, Nat.cast_ofNat] at hid ⊢
    convert sub_le_sub_right hid (1/50) using 1 <;> field_simp [ne_of_gt hd] <;> ring

theorem forcing_term_le (i k : ℕ) :
    (1/50 : ℝ) * (3/(rowPoint i * outerPoint k - 1)-1) ≤
      (roundedForceTerm i k : ℝ)/scale := by
  unfold roundedForceTerm
  rw [parameter_eq]
  have hi := mul_le_mul_of_nonneg_left (roundedInverse_real_bound i k)
    (show (0 : ℝ) ≤ 15 by norm_num)
  simp only [Int.ofNat_eq_natCast, Int.cast_sub, Int.cast_natCast]
  push_cast
  norm_num only [scale, Nat.reduceDiv, Nat.cast_ofNat] at hi ⊢
  have hd : (denominator i k : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast denominator_pos i k)
  convert sub_le_sub_right hi (1/50) using 1 <;> field_simp [hd] <;> ring

theorem cumulative_rectangles_le (i j : ℕ)
    (hactive : ∀ k < outerCount i j, denominator i k ≤ 50*(j+16)) :
    cumulativeRectangles i j ≤ (roundedCumulative i j : ℝ)/scale := by
  unfold cumulativeRectangles roundedCumulative
  rw [Finset.mul_sum]
  push_cast
  rw [Finset.sum_div]
  exact Finset.sum_le_sum fun k hk => cumulative_term_le i j k (hactive k (Finset.mem_range.mp hk))

theorem forcing_rectangles_le (i : ℕ) :
    forcingRectangles i ≤ (roundedForcing i : ℝ)/scale := by
  have h := Finset.sum_le_sum (s := Finset.range (forcingCount i))
    (fun k _ => forcing_term_le i k)
  rw [← Finset.mul_sum, ← Finset.sum_div] at h
  simpa only [forcingRectangles, roundedForcing, Int.cast_sum] using h

theorem active_of_last (i j : ℕ)
    (hlast : outerCount i j = 0 ∨ denominator i (outerCount i j - 1) ≤ 50*(j+16)) :
    ∀ k < outerCount i j, denominator i k ≤ 50*(j+16) := by
  intro k hk
  rcases hlast with hz | hl
  · omega
  · apply le_trans _ hl
    unfold denominator
    have : k ≤ outerCount i j - 1 := by omega
    exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.mul_le_mul_left _ this) _) _

theorem outer_coverage (i j : ℕ)
    (h : 50*(j+21) ≤ (i+10)*(50+outerCount i j)) :
    (childPoint j+2)/rowPoint i ≤ 1+(outerCount i j : ℝ)/50 := by
  have h' : (50 : ℝ)*(j+21) ≤ (i+10)*(50+outerCount i j) := by exact_mod_cast h
  have hr : 0 < rowPoint i := by unfold rowPoint; positivity
  apply (div_le_iff₀ hr).mpr
  unfold rowPoint childPoint
  nlinarith

theorem forcing_coverage (i : ℕ)
    (h : 1000 ≤ (i+10)*(50+forcingCount i)) :
    4/rowPoint i ≤ 1+(forcingCount i : ℝ)/50 := by
  have h' : (1000 : ℝ) ≤ (i+10)*(50+forcingCount i) := by exact_mod_cast h
  have hr : 0 < rowPoint i := by unfold rowPoint; positivity
  apply (div_le_iff₀ hr).mpr
  unfold rowPoint
  nlinarith

theorem forcing_last (i : ℕ)
    (h : forcingCount i = 0 ∨ denominator i (forcingCount i-1) ≤ 750) :
    ∀ k < forcingCount i, outerPoint k ≤ 4/rowPoint i := by
  intro k hk
  have hd : denominator i k ≤ 750 := by
    rcases h with hz | hl
    · omega
    · apply le_trans _ hl
      unfold denominator
      have : k ≤ forcingCount i - 1 := by omega
      exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.mul_le_mul_left _ this) _) _
  have hd' : (denominator i k : ℝ) ≤ 750 := by exact_mod_cast hd
  have hr : 0 < rowPoint i := by unfold rowPoint; positivity
  apply (le_div_iff₀ hr).mpr
  have he := parameter_eq i k
  nlinarith

run_cmd do
  for decl in [``parameter_eq, ``cumulative_term_le, ``forcing_term_le,
    ``cumulative_rectangles_le, ``forcing_rectangles_le, ``active_of_last,
    ``outer_coverage, ``forcing_coverage, ``forcing_last] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "RATIONAL RECTANGLE INTERPRETATION: STANDARD AXIOMS ONLY"
end ProfileCertificateRectangles
end
