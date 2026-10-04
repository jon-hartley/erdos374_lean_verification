import Item1OriginalCenterLow

/-! UNCOMPILED. The low-frequency prime product is the ordered prime-triple
source, with exact reciprocal weights. This module deliberately does NOT import
the parent's portable mean-square extraction, which redeclares baseline names.
The statement uses the same finite expression as the parent's `literal`.
A subsequent tail merge must reuse baseline mean-square declarations. -/
set_option autoImplicit false
set_option maxHeartbeats 18000000
noncomputable section
open scoped BigOperators Classical
namespace Item1PrimeSourceBinding
open Item1PrimeLowSpectrum SourceLiteralMoments SourceMassDischarge SourceLiteralMass
open CancellationTransferEndpoints Erdos374.HarmanGram152
open Erdos374.HarmanAnalytic151MeanSquare

abbrev Triple := ℕ×ℕ×ℕ

def allPrime (a : Triple) : Prop := a.1.Prime ∧ a.2.1.Prime ∧ a.2.2.Prime

def product (a : Triple) : ℕ := a.1*a.2.1*a.2.2

def weight (a : Triple) : ℝ := ArithmeticFunction.vonMangoldt a.1 *
  ArithmeticFunction.vonMangoldt a.2.1 * ArithmeticFunction.vonMangoldt a.2.2

def orderedTriples (X : ℝ) (j : ℕ×ℕ) : Finset Triple :=
  primeSupport X j 0 ×ˢ (primeSupport X j 1 ×ˢ primeSupport X j 2)

def atom (n : ℕ) (t : ℝ) : ℂ :=
  ((ArithmeticFunction.vonMangoldt n/(n:ℝ):ℝ):ℂ)*
    exponentialKernel151 (Real.log (n:ℝ)) (-t)

def orderedPolynomial (X : ℝ) (j : ℕ×ℕ) (t : ℝ) : ℂ :=
  ∑ a∈orderedTriples X j, ((weight a/(product a:ℝ):ℝ):ℂ)*
    exponentialKernel151 (Real.log (product a:ℝ)) (-t)

/-- Equality with a filter of the ACTUAL source constructor, not a new cube. -/
theorem orderedTriples_eq_source_filter (X : ℝ) (j : ℕ×ℕ) :
    orderedTriples X j = (sourceCoordinates X j).filter allPrime := by
  classical
  rw [sourceCoordinates_eq]
  ext a
  simp only [orderedTriples, primeSupport, Finset.mem_product, Finset.mem_filter, allPrime]
  tauto

theorem primeFactor_eq_atoms (X : ℝ) (j : ℕ×ℕ) (i : Fin 3) (t : ℝ) :
    primeFactor X j i t = ∑ n∈primeSupport X j i, atom n t := by
  unfold primeFactor
  rw [verticalDirichlet_eq_exponential152 (primeSupport X j i) mangoldt 1 t
    (fun n hn => support_pos X j i n (Finset.mem_filter.mp hn).1)]
  unfold exponentialSum151 atom normalizedCoefficients152 mangoldt
  simp only [Real.rpow_one, Complex.ofReal_div, Complex.ofReal_natCast]

/-- Product frequencies agree exactly; all three natural coordinates are positive. -/
theorem triple_phase (p r n : ℕ) (t : ℝ) (hp : 0<p) (hr : 0<r) (hn : 0<n) :
    exponentialKernel151 (Real.log ((p*r*n:ℕ):ℝ)) (-t) =
      exponentialKernel151 (Real.log (p:ℝ)) (-t) *
      exponentialKernel151 (Real.log (r:ℝ)) (-t) *
      exponentialKernel151 (Real.log (n:ℝ)) (-t) := by
  have hpR : (0:ℝ)<p := by exact_mod_cast hp
  have hrR : (0:ℝ)<r := by exact_mod_cast hr
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  rw [Nat.cast_mul, Nat.cast_mul,
    Real.log_mul (mul_pos hpR hrR).ne' hnR.ne', Real.log_mul hpR.ne' hrR.ne']
  unfold exponentialKernel151
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Exact term identity for the collected-polynomial normalization. -/
theorem triple_atom (p r n : ℕ) (t : ℝ) (hp : 0<p) (hr : 0<r) (hn : 0<n) :
    atom p t*atom r t*atom n t =
      ((weight (p,r,n)/(product (p,r,n):ℝ):ℝ):ℂ)*
        exponentialKernel151 (Real.log (product (p,r,n):ℝ)) (-t) := by
  unfold product weight
  rw [triple_phase p r n t hp hr hn]
  have hpC : (p:ℂ)≠0 := by exact_mod_cast hp.ne'
  have hrC : (r:ℂ)≠0 := by exact_mod_cast hr.ne'
  have hnC : (n:ℂ)≠0 := by exact_mod_cast hn.ne'
  unfold atom
  push_cast
  field_simp [hpC, hrC, hnC]
  <;> ring

/-- The exact source polynomial that both the low and prime-tail routes need.
No product multiplicity is lost: each ordered triple still contributes a term. -/
theorem primeProduct_eq_ordered (X : ℝ) (j : ℕ×ℕ) (t : ℝ) :
    primeProduct X j t = orderedPolynomial X j t := by
  classical
  unfold primeProduct
  rw [primeFactor_eq_atoms, primeFactor_eq_atoms, primeFactor_eq_atoms]
  unfold orderedPolynomial orderedTriples
  simp only [Finset.sum_product]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro n hn
  exact triple_atom p r n t
    (support_pos X j 0 p (Finset.mem_filter.mp hp).1)
    (support_pos X j 1 r (Finset.mem_filter.mp hr).1)
    (support_pos X j 2 n (Finset.mem_filter.mp hn).1)

/-- The reference remains full-Mangoldt after the source-binding rewrite. -/
theorem originalCentered_eq_ordered (X : ℝ) (j : ℕ×ℕ) (t : ℝ) :
    originalCentered X j t = orderedPolynomial X j t-
      SourceReferenceSigmaOne.referenceProduct X j t := by
  rw [originalCentered, primeProduct_eq_ordered]

run_cmd do
  for target in [``orderedTriples_eq_source_filter, ``primeFactor_eq_atoms, ``triple_phase, ``triple_atom, ``primeProduct_eq_ordered, ``originalCentered_eq_ordered] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "Item1PrimeSourceBinding: 6 original theorem guards passed."

end Item1PrimeSourceBinding
