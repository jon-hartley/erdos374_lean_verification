import Item1SelectedFourier
import Item1CenteredPrimeTail

/-! UNCOMPILED, 2026-10-02. Exact definitions connecting the selected-source
Fourier construction to the recovered tail package. These equalities do not
establish support/weight bounds, a prime cap, or a small spectral estimate.
The continuous reference uses both original unfiltered factor supports.
-/
set_option autoImplicit false
set_option maxHeartbeats 24000000
noncomputable section
open MeasureTheory Set
open scoped BigOperators Classical
namespace Item1TailIdentification
open Item1SelectedWindow Item1SelectedFourier SourceWindowFourier SourceLiteralTransform
open SourceLiteralMoments SourceLiteralMass SourceReferenceSigmaOne
open PositiveInteriorModel CancellationTransferEndpoints PositiveSharpCounts
open Erdos374.HarmanGram152 Erdos374.HarmanAnalytic151MeanSquare MellinWindowFactor

def reciprocalCoefficient (n : ℕ) : ℝ := ArithmeticFunction.vonMangoldt n/(n:ℝ)

theorem tripleProduct_cast (a : SourceTriple) :
    (Item1PrimeTripleFibers.product a:ℝ)=tripleProduct a := by
  simp only [Item1PrimeTripleFibers.product,tripleProduct,Nat.cast_mul]

theorem phase_eq_tail_kernel (t u : ℝ) :
    phase t u=exponentialKernel151 u (-t) := by
  unfold phase exponentialKernel151
  congr 1
  push_cast
  ring

theorem atomPolynomial_eq_tail_literal (S : Finset SourceTriple) (t : ℝ) :
    atomPolynomial S t=Item1CollectedPrimeTail.literal S tripleWeight t := by
  unfold atomPolynomial Item1CollectedPrimeTail.literal
  apply Finset.sum_congr rfl
  intro a _
  rw [tripleProduct_cast,phase_eq_tail_kernel]
  simp only [atomCoefficient,Complex.ofReal_div]

theorem source_factor_eq_tail_polynomial (X t : ℝ) (j : ℕ×ℕ) (i : Fin 3) :
    SourceLiteralMoments.factor X j i t =
      Item1FinitePolynomialTail.polynomial (support X j i) reciprocalCoefficient t := by
  unfold SourceLiteralMoments.factor verticalDirichlet152
    Item1FinitePolynomialTail.polynomial exponentialSum151
  apply Finset.sum_congr rfl
  intro n hn
  have hn0 : (0:ℝ)<n := by exact_mod_cast support_pos X j i n hn
  rw [←phase_eq_tail_kernel]
  have hp := phase_div (n:ℝ) t hn0
  push_cast at hp
  unfold reciprocalCoefficient
  push_cast
  rw [show (ArithmeticFunction.vonMangoldt n:ℂ)/(n:ℂ)*phase t (Real.log (n:ℝ)) =
      (ArithmeticFunction.vonMangoldt n:ℂ)*(phase t (Real.log (n:ℝ))/(n:ℂ)) by ring,hp]
  rfl

/-- Includes frequency zero; it does not use an endpoint quotient with t in its denominator. -/
theorem logReference_eq_source_cofactor (a b t : ℝ) (ha : 0<a) (hab : a≤b) :
    Item1CenteredPrimeTail.referenceFactor (Real.log a) (Real.log b) t =
      ContinuousCofactorMellin.cofactor a b (line 1 t) := by
  rw [←reference_interval_transform a b t ha hab]
  have hlog : Real.log a≤Real.log b := Real.log_le_log ha hab
  have hid : (fun u : ℝ => Complex.exp (-Complex.I*(t:ℂ)*(u:ℂ))*logInterval a b u) =
      (Icc (Real.log a) (Real.log b)).indicator
        (fun u => exponentialKernel151 (-t) u) := by
    funext u
    by_cases hu : u∈Icc (Real.log a) (Real.log b)
    · simp only [logInterval,Set.indicator_of_mem hu,mul_one]
      unfold exponentialKernel151
      congr 1
      push_cast
      ring
    · simp only [logInterval,Set.indicator_of_notMem hu,mul_zero]
  unfold angular
  rw [hid,integral_indicator measurableSet_Icc,integral_Icc_eq_integral_Ioc,
    ←intervalIntegral.integral_of_le hlog]
  rfl

theorem referenceProduct_eq_tail_reference (X t : ℝ) (j : ℕ×ℕ) (hX : 0<X) :
    referenceProduct X j t =
      Item1CenteredPrimeTail.mixedReference (support X j 0) (support X j 1)
        reciprocalCoefficient reciprocalCoefficient
        (Real.log (thirdScale X j/8)) (Real.log (4*thirdScale X j)) t := by
  have hL : 0<thirdScale X j := ideal_positive X j hX 2
  unfold referenceProduct Item1CenteredPrimeTail.mixedReference thirdReference
  rw [source_factor_eq_tail_polynomial,source_factor_eq_tail_polynomial,
    logReference_eq_source_cofactor _ _ t (by positivity) (by linarith)]

/-- Width factor equality: the old Mellin factor is UNNORMALIZED. -/
theorem normalizedMultiplier_eq_tail (eta t : ℝ) (he0 : 0<eta) (he1 : eta≤1/2) :
    normalizedMultiplier eta t=Item1SharpTail.multiplier eta t := by
  have hq : 0<1-eta := by linarith
  unfold normalizedMultiplier MellinWindowFactor.factor Item1SharpTail.multiplier
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hq.ne'),
    ←Complex.ofReal_log hq.le]
  simp only [line,Complex.ofReal_one]
  rw [show (Real.log (1-eta):ℂ)*((1:ℂ)+Complex.I*(t:ℂ)) =
    ((1:ℂ)+Complex.I*(t:ℂ))*(Real.log (1-eta):ℂ) by ring]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

/-- Equality of the actual centered density and the tail package integrand. -/
theorem density_eq_tail_integrand (X Y t : ℝ) (j : ℕ×ℕ) (S : Finset SourceTriple)
    (hX : 0<X) (hY : 0<Y) (hYX : Y≤X/2) :
    density X Y j S t =
      ‖Item1SharpTail.multiplier (Y/X) t *
        (Item1CollectedPrimeTail.literal S tripleWeight t-
          Item1CenteredPrimeTail.mixedReference (support X j 0) (support X j 1)
            reciprocalCoefficient reciprocalCoefficient
            (Real.log (thirdScale X j/8)) (Real.log (4*thirdScale X j)) t)‖^2 := by
  unfold density Item1SelectedFourier.spectrum
  rw [normalizedMultiplier_eq_tail (Y/X) t (div_pos hY hX)
    ((div_le_iff₀ hX).mpr (by linarith)),atomPolynomial_eq_tail_literal,
    referenceProduct_eq_tail_reference X t j hX]

theorem selected_tuples_are_prime (X : ℝ) (j : ℕ×ℕ) :
    ∀ a∈primeTuples X j, Item1PrimeTripleFibers.allPrime a := by
  intro a ha
  exact (Finset.mem_filter.mp ha).2

end Item1TailIdentification

-- ROOT SOURCE RECURSIVE AUDIT: exact original declarations.
run_cmd do
  for target in [
    ``Item1TailIdentification.tripleProduct_cast,
    ``Item1TailIdentification.phase_eq_tail_kernel,
    ``Item1TailIdentification.atomPolynomial_eq_tail_literal,
    ``Item1TailIdentification.source_factor_eq_tail_polynomial,
    ``Item1TailIdentification.logReference_eq_source_cofactor,
    ``Item1TailIdentification.referenceProduct_eq_tail_reference,
    ``Item1TailIdentification.normalizedMultiplier_eq_tail,
    ``Item1TailIdentification.density_eq_tail_integrand,
    ``Item1TailIdentification.selected_tuples_are_prime] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "Item1TailIdentification: 9 original theorem guards passed."
