import Item1SourceLocalArithmetic

/-! UNCOMPILED. Prime projection on the literal source supports.
The reference is NEVER prime-projected: originalCentered uses full factor 0
and full factor 1 in SourceReferenceSigmaOne.referenceProduct.
No mean-square estimate or nontrivial prime cap is assumed here. -/
set_option autoImplicit false
set_option maxHeartbeats 18000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators
namespace Item1PrimeLowSpectrum
open SourceLiteralMoments SourceLiteralMass SourceMassDischarge SourceReferenceSigmaOne
open SourceCenteredMiddle SourceLiteralMiddle Item1SourceLocalArithmetic
open PositiveInteriorModel PositiveInteriorCells Erdos374.HarmanGram152

/-- Only this filter removes nonprime coordinates; the original supports remain exact. -/
def primeSupport (X : ℝ) (j : ℕ×ℕ) (i : Fin 3) : Finset ℕ :=
  (support X j i).filter Nat.Prime

def primeFactor (X : ℝ) (j : ℕ×ℕ) (i : Fin 3) (t : ℝ) : ℂ :=
  verticalDirichlet152 (primeSupport X j i) mangoldt 1 t

def badFactor (X : ℝ) (j : ℕ×ℕ) (i : Fin 3) (t : ℝ) : ℂ :=
  verticalDirichlet152 ((support X j i).filter (fun n => ¬ n.Prime)) mangoldt 1 t

def primeProduct (X : ℝ) (j : ℕ×ℕ) (t : ℝ) : ℂ :=
  primeFactor X j 0 t*primeFactor X j 1 t*primeFactor X j 2 t

def originalCentered (X : ℝ) (j : ℕ×ℕ) (t : ℝ) : ℂ :=
  primeProduct X j t-referenceProduct X j t

/-- Finite partition, including zero Mangoldt coefficients and every endpoint. -/
theorem factor_partition (X : ℝ) (j : ℕ×ℕ) (i : Fin 3) (t : ℝ) :
    factor X j i t = primeFactor X j i t+badFactor X j i t := by
  classical
  unfold factor primeFactor primeSupport badFactor verticalDirichlet152
  exact (Finset.sum_filter_add_sum_filter_not (support X j i) Nat.Prime
    (fun n => mangoldt n*(n:ℂ)^(-((1:ℂ)+Complex.I*(t:ℂ))))).symm

theorem subfactor_norm (X : ℝ) (j : ℕ×ℕ) (i : Fin 3) (S : Finset ℕ)
    (hS : S⊆support X j i) (t : ℝ) :
    ‖verticalDirichlet152 S mangoldt 1 t‖ ≤
      ∑ n∈S, ArithmeticFunction.vonMangoldt n/(n:ℝ) := by
  rw [verticalDirichlet_eq_exponential152 _ _ 1 t
    (fun n hn => support_pos X j i n (hS hn))]
  unfold Erdos374.HarmanAnalytic151MeanSquare.exponentialSum151
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro n hn
  simp only [norm_mul, Erdos374.HarmanAnalytic151MeanSquare.norm_kernel151,
    mul_one, normalizedCoefficients152, Real.rpow_one, Complex.ofReal_natCast,
    norm_div, Complex.norm_natCast, mangoldt, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  exact le_rfl

theorem prime_norm_le_mass (X : ℝ) (j : ℕ×ℕ) (i : Fin 3) (t : ℝ) :
    ‖primeFactor X j i t‖ ≤ reciprocalMass X j i := by
  have hs : primeSupport X j i⊆support X j i := Finset.filter_subset _ _
  apply (subfactor_norm X j i (primeSupport X j i) hs t).trans
  exact Finset.sum_le_sum_of_subset_of_nonneg hs
    (fun n _ _ => div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg _))

theorem prime_norm_le_fifteen (X : ℝ) (j : ℕ×ℕ) (i : Fin 3) (t : ℝ)
    (hX : 2≤X) (hlog : 1000000≤Real.log X) (hj : j∈boxes (mesh X)) :
    ‖primeFactor X j i t‖ ≤ 15 :=
  (prime_norm_le_mass X j i t).trans (mass_le_fifteen X j i hX hlog hj)

theorem bad_norm_le_mass (X : ℝ) (j : ℕ×ℕ) (i : Fin 3) (t : ℝ) :
    ‖badFactor X j i t‖ ≤ badMass X j i :=
  subfactor_norm X j i _ (Finset.filter_subset _ _) t

theorem prime_continuous (X : ℝ) (j : ℕ×ℕ) (i : Fin 3) :
    Continuous (primeFactor X j i) := by
  apply NormalizedMeanSquare.continuous_vertical
  intro n hn
  exact support_pos X j i n (Finset.mem_filter.mp hn).1

theorem originalCentered_continuous (X : ℝ) (j : ℕ×ℕ) (hX : 0<X) :
    Continuous (originalCentered X j) :=
  (((prime_continuous X j 0).mul (prime_continuous X j 1)).mul
    (prime_continuous X j 2)).sub (reference_continuous X j hX)

/-- The telescoping identity is exact; triples with multiple bad coordinates
are counted once in this equality, not independently deleted three times. -/
theorem product_deletion_identity (X : ℝ) (j : ℕ×ℕ) (t : ℝ) :
    sourceProduct X j t-primeProduct X j t =
      badFactor X j 0 t*factor X j 1 t*factor X j 2 t +
      primeFactor X j 0 t*badFactor X j 1 t*factor X j 2 t +
      primeFactor X j 0 t*primeFactor X j 1 t*badFactor X j 2 t := by
  unfold sourceProduct primeProduct
  rw [factor_partition X j 0 t, factor_partition X j 1 t,
    factor_partition X j 2 t]
  ring

/-- A finite scalar estimate with independently stated factor-error bounds. -/
theorem triple_norm_bound (a b c : ℂ) (A B C : ℝ)
    (ha : ‖a‖≤A) (hb : ‖b‖≤B) (hc : ‖c‖≤C) :
    ‖a*b*c‖≤A*B*C := by
  have hA : 0≤A := (norm_nonneg _).trans ha
  have hB : 0≤B := (norm_nonneg _).trans hb
  have hAB := mul_le_mul ha hb (norm_nonneg _) hA
  simpa only [norm_mul] using
    mul_le_mul hAB hc (norm_nonneg _) (mul_nonneg hA hB)

theorem product_deletion_bound (X t eps : ℝ) (j : ℕ×ℕ)
    (hX : 2≤X) (hlog : 1000000≤Real.log X) (hj : j∈boxes (mesh X))
    (hbad : ∀ i : Fin 3, badMass X j i≤eps) :
    ‖sourceProduct X j t-primeProduct X j t‖ ≤ 675*eps := by
  have hp (i : Fin 3) := prime_norm_le_fifteen X j i t hX hlog hj
  have hf (i : Fin 3) := factor_norm_le_fifteen X j i t hX hlog hj
  have hb (i : Fin 3) := (bad_norm_le_mass X j i t).trans (hbad i)
  rw [product_deletion_identity]
  have h0 := triple_norm_bound _ _ _ _ _ _ (hb 0) (hf 1) (hf 2)
  have h1 := triple_norm_bound _ _ _ _ _ _ (hp 0) (hb 1) (hf 2)
  have h2 := triple_norm_bound _ _ _ _ _ _ (hp 0) (hp 1) (hb 2)
  calc
    _ ≤ ‖badFactor X j 0 t*factor X j 1 t*factor X j 2 t‖ +
        ‖primeFactor X j 0 t*badFactor X j 1 t*factor X j 2 t‖ +
        ‖primeFactor X j 0 t*primeFactor X j 1 t*badFactor X j 2 t‖ := by
      exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ 675*eps := by nlinarith

/-- The full reference cancels in this identity; it is not replaced by a prime reference. -/
theorem original_center_identity (X : ℝ) (j : ℕ×ℕ) (t : ℝ) :
    originalCentered X j t = centeredProduct X j t-
      (sourceProduct X j t-primeProduct X j t) := by
  unfold originalCentered centeredProduct
  ring

run_cmd do
  for target in [``factor_partition, ``subfactor_norm, ``prime_norm_le_mass, ``prime_norm_le_fifteen, ``bad_norm_le_mass, ``prime_continuous, ``originalCentered_continuous, ``product_deletion_identity, ``triple_norm_bound, ``product_deletion_bound, ``original_center_identity] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "Item1PrimeLowSpectrum: 11 original theorem guards passed."

end Item1PrimeLowSpectrum
