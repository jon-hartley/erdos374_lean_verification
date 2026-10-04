import Item1LogarithmicFirstCap
import Item1PrimeSourceBinding
import Item1FinitePolynomialTail
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! Exact positive-frequency interfaces for the ACTUAL prime source.
Real Mangoldt coefficients justify conjugation. There is no assertion that
arbitrary complex-coefficient Dirichlet polynomials have an even norm. -/
set_option autoImplicit false
set_option maxHeartbeats 16000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators ComplexConjugate
namespace Item1PrimeMiddleSymmetry
open Item1LogarithmicFirstCap Item1SourceLocalArithmetic Item1PrimeLowSpectrum
open Item1PrimeSourceBinding SourceLiteralMiddle
open PositiveInteriorModel PositiveInteriorCells

theorem atom_neg (n : ℕ) (t : ℝ) : atom n (-t)=conj (atom n t) := by
  unfold atom
  simp only [map_mul, Complex.conj_ofReal]
  rw [←Item1FinitePolynomialTail.kernel_neg]

theorem primeFactor_neg (X : ℝ) (j : ℕ×ℕ) (i : Fin 3) (t : ℝ) :
    primeFactor X j i (-t)=conj (primeFactor X j i t) := by
  simp only [primeFactor_eq_atoms, map_sum, atom_neg]

theorem primeProduct_neg (X : ℝ) (j : ℕ×ℕ) (t : ℝ) :
    primeProduct X j (-t)=conj (primeProduct X j t) := by
  simp only [primeProduct,primeFactor_neg,map_mul]

theorem norm_primeProduct_even (X : ℝ) (j : ℕ×ℕ) (t : ℝ) :
    ‖primeProduct X j (-t)‖=‖primeProduct X j t‖ := by
  rw [primeProduct_neg,Complex.norm_conj]

theorem normalizedFirst_neg (X : ℝ) (j : ℕ×ℕ) (t : ℝ) :
    normalizedFirst X j (-t)=conj (normalizedFirst X j t) := by
  simp only [normalizedFirst,primeFactor_neg,map_div₀,Complex.conj_ofReal]

theorem normalizedFirst_abs (X : ℝ) (j : ℕ×ℕ) (t : ℝ) :
    ‖normalizedFirst X j |t|‖=‖normalizedFirst X j t‖ := by
  by_cases ht : 0≤t
  · rw [abs_of_nonneg ht]
  · rw [abs_of_neg (lt_of_not_ge ht),normalizedFirst_neg,Complex.norm_conj]

def PositiveFirstCap (X : ℝ) (K : ℕ) : Prop :=
  ∀ j∈boxes (mesh X), ∀ t∈Icc (lowCut X K) (height X),
    ‖normalizedFirst X j t‖≤1/(Real.log X)^1024

def TwoSidedFirstCap (X : ℝ) (K : ℕ) : Prop :=
  ∀ j∈boxes (mesh X), ∀ t : ℝ, lowCut X K≤|t| → |t|≤height X →
    ‖normalizedFirst X j t‖≤1/(Real.log X)^1024

theorem two_sided_cap_of_positive (X : ℝ) (K : ℕ) (hc : PositiveFirstCap X K) :
    TwoSidedFirstCap X K := by
  intro j hj t hlow hhigh
  have hh := hc j hj |t| ⟨hlow,hhigh⟩
  simpa only [normalizedFirst_abs] using hh

theorem positive_cap_of_two_sided (X : ℝ) (K : ℕ) (hU : 0≤lowCut X K)
    (hc : TwoSidedFirstCap X K) : PositiveFirstCap X K := by
  intro j hj t ht
  have ht0 : 0≤t := hU.trans ht.1
  exact hc j hj t (by simpa only [abs_of_nonneg ht0] using ht.1)
    (by simpa only [abs_of_nonneg ht0] using ht.2)

theorem middle_eq_two_intervals (X U : ℝ) (hU : 0≤U) :
    middle X U=Icc (-height X) (-U) ∪ Icc U (height X) := by
  ext t
  simp only [middle,mem_inter_iff,mem_ofPred_eq,mem_Icc,mem_union]
  by_cases ht : 0≤t
  · rw [abs_of_nonneg ht]
    constructor
    · rintro ⟨⟨hl,hh⟩,hu⟩
      exact Or.inr ⟨hu,hh⟩
    · rintro (⟨hl,hu⟩ | ⟨hu,hh⟩)
      · exact ⟨⟨hl,by linarith⟩,by linarith⟩
      · exact ⟨⟨by linarith,hh⟩,hu⟩
  · rw [abs_of_neg (lt_of_not_ge ht)]
    constructor
    · rintro ⟨⟨hl,hh⟩,hu⟩
      exact Or.inl ⟨hl,by linarith⟩
    · rintro (⟨hl,hu⟩ | ⟨hu,hh⟩)
      · exact ⟨⟨hl,by linarith⟩,by linarith⟩
      · exfalso
        linarith

theorem frequency_intervals_disjoint (H U : ℝ) (hU : 0<U) :
    Disjoint (Icc (-H) (-U)) (Icc U H) := by
  rw [Set.disjoint_left]
  intro t hn hp
  have := hn.2
  have := hp.1
  linarith

/-- Reflection for set integrals, with the endpoint change performed through
Lebesgue's null-singleton identity. No small-energy estimate is used. -/
theorem even_integral_negative (f : ℝ→ℝ) (H U : ℝ) (hUH : U≤H)
    (heven : ∀ t, f (-t)=f t) :
    (∫ t in Icc (-H) (-U), f t)=(∫ t in Icc U H, f t) := by
  have hneg : -H≤-U := by linarith
  rw [integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le hneg,
    integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le hUH]
  have hh := intervalIntegral.integral_comp_neg (a:=U) (b:=H) f
  simpa only [heven] using hh.symm

theorem primeProduct_continuous (X : ℝ) (j : ℕ×ℕ) :
    Continuous (primeProduct X j) :=
  ((prime_continuous X j 0).mul (prime_continuous X j 1)).mul (prime_continuous X j 2)

theorem cell_middle_eq_twice_positive (X U : ℝ) (j : ℕ×ℕ)
    (hU : 0<U) (hUH : U≤height X) :
    (∫ t in middle X U, ‖primeProduct X j t‖^2)=
      2*(∫ t in Icc U (height X), ‖primeProduct X j t‖^2) := by
  have hc : Continuous (fun t => ‖primeProduct X j t‖^2) :=
    (primeProduct_continuous X j).norm.pow 2
  rw [middle_eq_two_intervals X U hU.le,
    setIntegral_union (μ := volume) (frequency_intervals_disjoint (height X) U hU)
      measurableSet_Icc hc.integrableOn_Icc hc.integrableOn_Icc,
    even_integral_negative (fun t => ‖primeProduct X j t‖^2) (height X) U hUH
      (fun t => by rw [norm_primeProduct_even])]
  ring

end Item1PrimeMiddleSymmetry

-- ROOT SOURCE RECURSIVE AUDIT: exact original declarations.
run_cmd do
  for target in [
    ``Item1PrimeMiddleSymmetry.atom_neg,
    ``Item1PrimeMiddleSymmetry.primeFactor_neg,
    ``Item1PrimeMiddleSymmetry.primeProduct_neg,
    ``Item1PrimeMiddleSymmetry.norm_primeProduct_even,
    ``Item1PrimeMiddleSymmetry.normalizedFirst_neg,
    ``Item1PrimeMiddleSymmetry.normalizedFirst_abs,
    ``Item1PrimeMiddleSymmetry.two_sided_cap_of_positive,
    ``Item1PrimeMiddleSymmetry.positive_cap_of_two_sided,
    ``Item1PrimeMiddleSymmetry.middle_eq_two_intervals,
    ``Item1PrimeMiddleSymmetry.frequency_intervals_disjoint,
    ``Item1PrimeMiddleSymmetry.even_integral_negative,
    ``Item1PrimeMiddleSymmetry.primeProduct_continuous,
    ``Item1PrimeMiddleSymmetry.cell_middle_eq_twice_positive] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "Item1PrimeMiddleSymmetry: 13 original theorem guards passed."
