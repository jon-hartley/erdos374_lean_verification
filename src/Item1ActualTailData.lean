import Item1SourceGlue
import Item1TailIdentification

/-! UNCOMPILED, 2026-10-02. Supply the numerical data of the ACTUAL prime
source to the existing complete-tail theorem. All support and coefficient
hypotheses are discharged here, including the original full reference masses.
The source height and width are not changed. No small tail is a premise. -/
set_option autoImplicit false
set_option maxHeartbeats 32000000
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Item1ActualTailData
open Item1SourceGlue Item1SelectedWindow Item1SelectedFourier
open Item1TailIdentification Item1SourceLocalArithmetic
open SourceLiteralMoments SourceLiteralMass
open PositiveInteriorModel PositiveInteriorCells CancellationTransferEndpoints
open PositiveSharpCounts

/-- Exact first/second dyadic upper/lower bounds, unlike the coarser factor-eight
bounds needed for the third coordinate. -/
theorem first_support_bounds (X : ℝ) (j : ℕ×ℕ) (n : ℕ)
    (hn : n∈support X j 0) : scale j.1≤(n:ℝ) ∧ (n:ℝ)≤2*scale j.1 := by
  have h := Finset.mem_Ico.mp hn
  constructor
  · simpa [scale] using (show (((2:ℕ)^j.1:ℕ):ℝ)≤n by exact_mod_cast h.1)
  · simpa [scale] using (show (n:ℝ)≤(2*(2:ℕ)^j.1:ℕ) by exact_mod_cast h.2.le)

theorem second_support_bounds (X : ℝ) (j : ℕ×ℕ) (n : ℕ)
    (hn : n∈support X j 1) : scale j.2≤(n:ℝ) ∧ (n:ℝ)≤2*scale j.2 := by
  have h := Finset.mem_Ico.mp hn
  constructor
  · simpa [scale] using (show (((2:ℕ)^j.2:ℕ):ℝ)≤n by exact_mod_cast h.1)
  · simpa [scale] using (show (n:ℝ)≤(2*(2:ℕ)^j.2:ℕ) by exact_mod_cast h.2.le)

theorem source_product_bounds (X : ℝ) (j : ℕ×ℕ) (a : SourceTriple)
    (hX : 0<X) (ha : a∈sourceCoordinates X j) :
    X/8≤tripleProduct a ∧ tripleProduct a≤16*X := by
  rw [sourceCoordinates_eq] at ha
  have hp := (Finset.mem_product.mp ha).1
  have hr := (Finset.mem_product.mp (Finset.mem_product.mp ha).2).1
  have hn := (Finset.mem_product.mp (Finset.mem_product.mp ha).2).2
  have hpB := first_support_bounds X j a.1 hp
  have hrB := second_support_bounds X j a.2.1 hr
  have hnB := support_local_bounds X j 2 a.2.2 hX hn
  change thirdScale X j/8≤(a.2.2:ℝ) ∧ (a.2.2:ℝ)≤4*thirdScale X j at hnB
  have hP : 0<scale j.1 := by unfold scale; positivity
  have hR : 0<scale j.2 := by unfold scale; positivity
  have hL : 0<thirdScale X j := by unfold thirdScale; positivity
  have hLo := mul_le_mul (mul_le_mul hpB.1 hrB.1 hR.le (Nat.cast_nonneg _))
    hnB.1 (by positivity : 0≤thirdScale X j/8) (by positivity : 0≤(a.1:ℝ)*(a.2.1:ℝ))
  have hHi := mul_le_mul (mul_le_mul hpB.2 hrB.2 (Nat.cast_nonneg _) (by positivity))
    hnB.2 (Nat.cast_nonneg _) (by positivity : 0≤(2*scale j.1)*(2*scale j.2))
  have hloEq : scale j.1*scale j.2*(thirdScale X j/8)=X/8 := by
    unfold thirdScale
    field_simp <;> ring
  have hhiEq : (2*scale j.1)*(2*scale j.2)*(4*thirdScale X j)=16*X := by
    unfold thirdScale
    field_simp <;> ring
  rw [hloEq] at hLo
  rw [hhiEq] at hHi
  exact ⟨by simpa only [tripleProduct] using hLo, by simpa only [tripleProduct] using hHi⟩

/-- Every coordinate lies below X, with the source's fixed endpoint allowance. -/
theorem coordinate_log_bound (X : ℝ) (j : ℕ×ℕ) (i : Fin 3) (n : ℕ)
    (hX : 2≤X) (hlog : 1000000≤Real.log X) (hj : j∈boxes (mesh X))
    (hn : n∈support X j i) : Real.log (n:ℝ)≤Real.log X := by
  have hXp : 0<X := by linarith
  have hn0 : (0:ℝ)<n := by exact_mod_cast support_pos X j i n hn
  have hZ := ideal_positive X j hXp i
  have hle := Real.log_le_log hn0 (support_local_bounds X j i n hXp hn).2
  rw [Real.log_mul (by norm_num : (4:ℝ)≠0) hZ.ne',ideal_log X j (by linarith) i] at hle
  have hlog4 : Real.log 4≤2 := by
    rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow]
    have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at h2 ⊢
    linarith
  have he := mul_le_mul_of_nonneg_right (exponent_bounds X j (by linarith) hj i).2
    (show 0≤Real.log X by linarith)
  linarith

theorem actual_weight_bound (X : ℝ) (j : ℕ×ℕ) (a : SourceTriple)
    (hX : 2≤X) (hlog : 1000000≤Real.log X) (hj : j∈boxes (mesh X))
    (ha : a∈sourceCoordinates X j) : tripleWeight a≤(Real.log X)^3 := by
  rw [sourceCoordinates_eq] at ha
  have hp := (Finset.mem_product.mp ha).1
  have hr := (Finset.mem_product.mp (Finset.mem_product.mp ha).2).1
  have hn := (Finset.mem_product.mp (Finset.mem_product.mp ha).2).2
  have b0 := (ArithmeticFunction.vonMangoldt_le_log (n:=a.1)).trans
    (coordinate_log_bound X j 0 a.1 hX hlog hj hp)
  have b1 := (ArithmeticFunction.vonMangoldt_le_log (n:=a.2.1)).trans
    (coordinate_log_bound X j 1 a.2.1 hX hlog hj hr)
  have b2 := (ArithmeticFunction.vonMangoldt_le_log (n:=a.2.2)).trans
    (coordinate_log_bound X j 2 a.2.2 hX hlog hj hn)
  have hl : 0≤Real.log X := by linarith
  have hh := mul_le_mul (mul_le_mul b0 b1 ArithmeticFunction.vonMangoldt_nonneg hl)
    b2 ArithmeticFunction.vonMangoldt_nonneg (mul_nonneg hl hl)
  simpa only [tripleWeight,pow_succ,pow_zero,mul_one,one_mul,mul_assoc] using hh

theorem prime_tuple_mass_bound (X : ℝ) (j : ℕ×ℕ)
    (hX : 2≤X) (hlog : 1000000≤Real.log X) (hj : j∈boxes (mesh X)) :
    tupleMass (primeTuples X j)≤32*(Real.log X)^3 := by
  have hb := (tupleMass_mono (primeTuples_subset X j)).trans
    (source_tupleMass_bound X j hX hlog hj)
  have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤5)
    (show (5:ℝ)≤Real.log X by linarith) 3
  norm_num at hp
  linarith

theorem reference_mass_bound (X : ℝ) (j : ℕ×ℕ) (i : Fin 3)
    (hX : 2≤X) (hlog : 1000000≤Real.log X) (hj : j∈boxes (mesh X)) :
    (∑ n∈support X j i, |reciprocalCoefficient n|)≤Real.log X := by
  have he (n : ℕ) : |reciprocalCoefficient n|=ArithmeticFunction.vonMangoldt n/(n:ℝ) := by
    unfold reciprocalCoefficient
    exact abs_of_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg n))
  simp_rw [he]
  exact (mass_le_fifteen X j i hX hlog hj).trans (by linarith)

def cutoff (X : ℝ) : ℕ := ⌊16*X⌋₊

theorem prime_product_data (X : ℝ) (j : ℕ×ℕ) (a : SourceTriple)
    (hX : 0<X) (ha : a∈primeTuples X j) :
    (1≤Item1PrimeTripleFibers.product a ∧ Item1PrimeTripleFibers.product a≤cutoff X) ∧
      X/8≤(Item1PrimeTripleFibers.product a:ℝ) := by
  have hm := source_product_bounds X j a hX (primeTuples_subset X j ha)
  have hp := SourceLogWindow.triple_positive X j a (primeTuples_subset X j ha)
  have hpNat : 0<Item1PrimeTripleFibers.product a := by
    exact_mod_cast (show (0:ℝ)<(Item1PrimeTripleFibers.product a:ℝ) by simpa only [tripleProduct_cast] using hp)
  exact ⟨⟨by omega, Nat.le_floor (by simpa only [tripleProduct_cast] using hm.2)⟩,
    by simpa only [tripleProduct_cast] using hm.1⟩

/-- Direct call to the constructed infinite-tail theorem with all actual-cell
finite hypotheses instantiated. There is no abstract tuple-family premise left. -/
theorem actual_cell_tail (X Y H : ℝ) (j : ℕ×ℕ)
    (hX : 2≤X) (hlog : 1000000≤Real.log X) (hj : j∈boxes (mesh X))
    (hY : 0<Y) (hYX : Y≤X/2) (hH : 1≤H) :
    (∫ t in SourceDyadicTail.outside H, density X Y j (primeTuples X j) t)≤
      49152*(Real.log X)^6/((Y/X)^2*X*H)+
      98304*Item1FinitePolynomialTail.rowCost (cutoff X)*(Real.log X)^6/(3*(Y/X)^2*X*H^2)+
      64*(Real.log X)^4/(3*(Y/X)^2*H^3) := by
  have hXp : 0<X := by linarith
  have ht := Item1CenteredPrimeTail.mixed_center_sharp_tail
    (primeTuples X j) tripleWeight (cutoff X) (support X j 0) (support X j 1)
    reciprocalCoefficient reciprocalCoefficient
    (Real.log (thirdScale X j/8)) (Real.log (4*thirdScale X j))
    X (Real.log X) (Y/X) H hXp (by linarith) (div_pos hY hXp)
    ((div_le_iff₀ hXp).mpr (by linarith)) hH (selected_tuples_are_prime X j)
    (fun a ha => (prime_product_data X j a hXp ha).1)
    (fun a ha => (prime_product_data X j a hXp ha).2)
    (fun a _ => tripleWeight_nonneg a)
    (fun a ha => actual_weight_bound X j a hX hlog hj (primeTuples_subset X j ha))
    (by simpa only [tupleMass,tripleProduct_cast] using prime_tuple_mass_bound X j hX hlog hj)
    (reference_mass_bound X j 0 hX hlog hj) (reference_mass_bound X j 1 hX hlog hj)
  simpa only [density_eq_tail_integrand X Y _ j _ hXp hY hYX,
    SourceDyadicTail.outside,Item1CountableTail.outside] using ht

end Item1ActualTailData

-- ROOT SOURCE RECURSIVE AUDIT: exact original declarations.
run_cmd do
  for target in [
    ``Item1ActualTailData.first_support_bounds,
    ``Item1ActualTailData.second_support_bounds,
    ``Item1ActualTailData.source_product_bounds,
    ``Item1ActualTailData.coordinate_log_bound,
    ``Item1ActualTailData.actual_weight_bound,
    ``Item1ActualTailData.prime_tuple_mass_bound,
    ``Item1ActualTailData.reference_mass_bound,
    ``Item1ActualTailData.prime_product_data,
    ``Item1ActualTailData.actual_cell_tail] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "Item1ActualTailData: 9 original theorem guards passed."
