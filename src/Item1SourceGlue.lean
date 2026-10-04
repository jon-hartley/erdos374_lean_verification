import Item1PrimeSourceBinding
import Item1SelectedFourier

/-! UNCOMPILED, 2026-10-02. Bind the independently written low-frequency and
normalized-transfer sources. Every equality concerns the literal ordered source
coordinates. The full Mangoldt reference is unchanged. No energy, prime cap,
PNT error, or physical deletion estimate is assumed in this module. -/
set_option autoImplicit false
set_option maxHeartbeats 24000000
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators
namespace Item1SourceGlue
open Item1SelectedWindow Item1SelectedFourier
open SourceLiteralMoments SourceLiteralMass SourceLiteralTransform
open PositiveInteriorModel PositiveInteriorCells CancellationTransferEndpoints PositiveSharpCounts
open Erdos374.HarmanGram152 Erdos374.HarmanAnalytic151MeanSquare MellinWindowFactor

/-- The two prior packages use definitionally identical primality predicates. -/
theorem primeTuples_eq_ordered (X : ℝ) (j : ℕ×ℕ) :
    primeTuples X j = Item1PrimeSourceBinding.orderedTriples X j := by
  rw [Item1PrimeSourceBinding.orderedTriples_eq_source_filter]
  rfl

theorem natural_product_cast (a : SourceTriple) :
    (Item1PrimeSourceBinding.product a:ℝ)=tripleProduct a := by
  simp only [Item1PrimeSourceBinding.product,tripleProduct,Nat.cast_mul]

theorem phase_eq_kernel (t u : ℝ) :
    phase t u=exponentialKernel151 u (-t) := by
  unfold phase exponentialKernel151
  congr 1
  push_cast
  ring

/-- No quotient by the number of representations occurs in this equality. -/
theorem prime_atoms_eq_ordered (X : ℝ) (j : ℕ×ℕ) (t : ℝ) :
    atomPolynomial (primeTuples X j) t =
      Item1PrimeSourceBinding.orderedPolynomial X j t := by
  rw [primeTuples_eq_ordered]
  unfold atomPolynomial Item1PrimeSourceBinding.orderedPolynomial
  apply Finset.sum_congr rfl
  intro a _
  rw [natural_product_cast,←phase_eq_kernel]
  rfl

theorem prime_atoms_eq_product (X : ℝ) (j : ℕ×ℕ) (t : ℝ) :
    atomPolynomial (primeTuples X j) t=Item1PrimeLowSpectrum.primeProduct X j t := by
  rw [prime_atoms_eq_ordered,Item1PrimeSourceBinding.primeProduct_eq_ordered]

/-- Extract the finite identity used inside the retained v9 transform proof. -/
theorem all_atoms_eq_product (X : ℝ) (j : ℕ×ℕ) (t : ℝ) :
    atomPolynomial (sourceCoordinates X j) t=SourceLiteralMiddle.sourceProduct X j t := by
  unfold atomPolynomial
  calc
    _ = ∑ a∈sourceCoordinates X j,
        (SourceMassDischarge.mangoldt a.1*(a.1:ℂ)^(-line 1 t))*
        (SourceMassDischarge.mangoldt a.2.1*(a.2.1:ℂ)^(-line 1 t))*
        (SourceMassDischarge.mangoldt a.2.2*(a.2.2:ℂ)^(-line 1 t)) := by
      apply Finset.sum_congr rfl
      intro a ha
      exact SourceLiteralTransform.triple_phase X t j a ha
    _ = _ := by
      rw [sourceCoordinates_eq]
      simp only [Finset.sum_product,SourceLiteralMiddle.sourceProduct,
        SourceLiteralMoments.factor,verticalDirichlet152,line,
        Complex.ofReal_one,mul_assoc]
      simp only [Finset.sum_mul_sum]
      simp only [Finset.mul_sum,mul_assoc]

def tupleMass (S : Finset SourceTriple) : ℝ :=
  ∑ a∈S, tripleWeight a/tripleProduct a

theorem tupleMass_nonneg (S : Finset SourceTriple) : 0≤tupleMass S := by
  exact Finset.sum_nonneg (fun a _ => div_nonneg (tripleWeight_nonneg a)
    (by unfold tripleProduct; positivity))

theorem atomPolynomial_zero (S : Finset SourceTriple) :
    atomPolynomial S 0=(tupleMass S:ℂ) := by
  simp only [atomPolynomial,phase,Complex.ofReal_zero,mul_zero,zero_mul,
    neg_zero,Complex.exp_zero,mul_one,atomCoefficient,tupleMass,Complex.ofReal_sum]

theorem norm_atomPolynomial_zero (S : Finset SourceTriple) :
    ‖atomPolynomial S 0‖=tupleMass S := by
  rw [atomPolynomial_zero,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (tupleMass_nonneg S)]

theorem tupleMass_mono {S T : Finset SourceTriple} (hST : S⊆T) :
    tupleMass S≤tupleMass T := by
  exact Finset.sum_le_sum_of_subset_of_nonneg hST (fun a _ _ =>
    div_nonneg (tripleWeight_nonneg a) (by unfold tripleProduct; positivity))

theorem source_tupleMass_bound (X : ℝ) (j : ℕ×ℕ)
    (hX : 2≤X) (hlog : 1000000≤Real.log X) (hj : j∈boxes (mesh X)) :
    tupleMass (sourceCoordinates X j)≤3375 := by
  rw [←norm_atomPolynomial_zero,all_atoms_eq_product]
  have h := Item1PrimeLowSpectrum.triple_norm_bound
    (SourceLiteralMoments.factor X j 0 0) (SourceLiteralMoments.factor X j 1 0)
    (SourceLiteralMoments.factor X j 2 0) 15 15 15
    (factor_norm_le_fifteen X j 0 0 hX hlog hj)
    (factor_norm_le_fifteen X j 1 0 hX hlog hj)
    (factor_norm_le_fifteen X j 2 0 hX hlog hj)
  simpa only [SourceLiteralMiddle.sourceProduct,show (15:ℝ)*15*15=3375 by norm_num] using h

/-- Zero frequency is used only to identify a NONNEGATIVE reciprocal mass.
No cancellation or small centered zero-frequency value is asserted. -/
theorem bad_tupleMass_bound (X eps : ℝ) (j : ℕ×ℕ)
    (hX : 2≤X) (hlog : 1000000≤Real.log X) (hj : j∈boxes (mesh X))
    (hbad : ∀ i : Fin 3, Item1SourceLocalArithmetic.badMass X j i≤eps) :
    tupleMass (badTuples X j)≤675*eps := by
  have hp := tuple_partition X j
    (fun a => atomCoefficient a*phase 0 (Real.log (tripleProduct a)))
  change atomPolynomial (primeTuples X j) 0+atomPolynomial (badTuples X j) 0=
    atomPolynomial (sourceCoordinates X j) 0 at hp
  rw [prime_atoms_eq_product,all_atoms_eq_product] at hp
  have hid : SourceLiteralMiddle.sourceProduct X j 0-
      Item1PrimeLowSpectrum.primeProduct X j 0=atomPolynomial (badTuples X j) 0 := by
    rw [←hp]
    ring
  have hb := Item1PrimeLowSpectrum.product_deletion_bound X 0 eps j hX hlog hj hbad
  rw [hid,norm_atomPolynomial_zero] at hb
  exact hb

theorem spectrum_eq_originalCentered (X : ℝ) (j : ℕ×ℕ) (t : ℝ) :
    spectrum X j (primeTuples X j) t=Item1PrimeLowSpectrum.originalCentered X j t := by
  unfold Item1SelectedFourier.spectrum Item1PrimeLowSpectrum.originalCentered
  rw [prime_atoms_eq_product]

theorem multiplier_eq_low (eta t : ℝ) :
    normalizedMultiplier eta t=Item1OriginalCenterLow.sharpMultiplier eta t := rfl

/-- The low proof now bounds exactly the normalized-transfer integrand. -/
theorem density_eq_low (X Y t : ℝ) (j : ℕ×ℕ) :
    density X Y j (primeTuples X j) t=
      ‖Item1OriginalCenterLow.sharpMultiplier (Y/X) t*
        Item1PrimeLowSpectrum.originalCentered X j t‖^2 := by
  rw [density,spectrum_eq_originalCentered,multiplier_eq_low]

end Item1SourceGlue


run_cmd do
  for target in [``Item1SourceGlue.primeTuples_eq_ordered,
    ``Item1SourceGlue.natural_product_cast,
    ``Item1SourceGlue.phase_eq_kernel,
    ``Item1SourceGlue.prime_atoms_eq_ordered,
    ``Item1SourceGlue.prime_atoms_eq_product,
    ``Item1SourceGlue.all_atoms_eq_product,
    ``Item1SourceGlue.tupleMass_nonneg,
    ``Item1SourceGlue.atomPolynomial_zero,
    ``Item1SourceGlue.norm_atomPolynomial_zero,
    ``Item1SourceGlue.tupleMass_mono,
    ``Item1SourceGlue.source_tupleMass_bound,
    ``Item1SourceGlue.bad_tupleMass_bound,
    ``Item1SourceGlue.spectrum_eq_originalCentered,
    ``Item1SourceGlue.multiplier_eq_low,
    ``Item1SourceGlue.density_eq_low] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"


