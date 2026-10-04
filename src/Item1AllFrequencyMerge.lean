import Item1TailScalarMerge
import Item1LowEnergyMerge

/-! UNCOMPILED, 2026-10-02. Actual low/reference/high terms are constructed
inside this chain. The sole unresolved quantitative premise is the explicit
prime-only middle integral below. This does NOT prove that premise, the prime
cap, the fractional-moment specialization, Item 1 unconditionally, or Item 2. -/
set_option autoImplicit false
set_option maxHeartbeats 32000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators
namespace Item1AllFrequencyMerge
open Item1SourceGlue Item1PhysicalDeletion Item1LowEnergyMerge Item1TailScalarMerge
open Item1SelectedWindow Item1SelectedFourier Item1QuadraticAssembly
open Item1SourceLocalArithmetic Item1PrimeLowSpectrum SourceReferenceSigmaOne
open PositiveInteriorModel PositiveInteriorCells CancellationTransferCenter
open PositiveSharpMovingWindow

/-- Same full prime factors as the explicit-moment route; no masks or shifts.
The lower boundary is closed as in the inherited source-middle set. -/
def primeMiddle (X : ℝ) (K : ℕ) : ℝ :=
  ∑ j∈boxes (mesh X), ∫ t in SourceLiteralMiddle.middle X (lowCut X K),
    ‖primeProduct X j t‖^2

def centeredMiddle (X : ℝ) (K : ℕ) : ℝ :=
  ∑ j∈boxes (mesh X), ∫ t in SourceLiteralMiddle.middle X (lowCut X K),
    density X (width X) j (primeTuples X j) t

/-- Overlap at two boundary points is harmless for an upper bound; the covering
argument works before discarding any null sets. -/
theorem three_part_integral (f : ℝ→ℝ) (X U : ℝ) (hi : Integrable f)
    (hn : ∀ t, 0≤f t) :
    (∫ t, f t) ≤ (∫ t in Icc (-U) U, f t)+
      (∫ t in SourceLiteralMiddle.middle X U, f t)+
      (∫ t in SourceDyadicTail.outside (height X), f t) := by
  let A := Icc (-U) U
  let B := SourceLiteralMiddle.middle X U
  let C := SourceDyadicTail.outside (height X)
  have hA : MeasurableSet A := measurableSet_Icc
  have hB : MeasurableSet B := SourceLiteralMiddle.middle_measurable X U
  have hC : MeasurableSet C := SourceDyadicTail.outside_measurable (height X)
  have hpoint (t : ℝ) : f t≤A.indicator f t+B.indicator f t+C.indicator f t := by
    have hz (D : Set ℝ) : 0≤D.indicator f t := by
      by_cases ht : t∈D
      · simpa only [Set.indicator_of_mem ht] using hn t
      · simp only [Set.indicator_of_notMem ht,le_refl]
    by_cases ha : t∈A
    · rw [Set.indicator_of_mem ha]
      linarith [hz B,hz C]
    by_cases hc : t∈C
    · rw [Set.indicator_of_mem hc]
      linarith [hz A,hz B]
    have hl : U≤|t| := by
      have hh : ¬ |t|≤U := by
        intro ht
        exact ha (abs_le.mp ht)
      exact (lt_of_not_ge hh).le
    have hh : |t|≤height X := by
      exact le_of_not_gt hc
    have hb : t∈B := ⟨abs_le.mp hh,hl⟩
    rw [Set.indicator_of_mem hb]
    linarith [hz A,hz C]
  have hAB : Integrable (fun t => A.indicator f t+B.indicator f t) :=
    (hi.indicator hA).add (hi.indicator hB)
  have hb := integral_mono hi (hAB.add (hi.indicator hC)) hpoint
  simp only [Pi.add_apply] at hb
  rw [integral_add hAB (hi.indicator hC),
    integral_add (hi.indicator hA) (hi.indicator hB),
    integral_indicator hA,integral_indicator hB,integral_indicator hC] at hb
  exact hb

theorem totalEnergy_le_parts (X : ℝ) (K : ℕ) (hX : 2≤X)
    (hlog : 1000000≤Real.log X) :
    totalEnergy X (width X)≤lowEnergy X (width X) K+centeredMiddle X K+highEnergy X := by
  obtain ⟨hY,hYX⟩ := width_bounds X (by linarith)
  have hsum := Finset.sum_le_sum (fun j hj => three_part_integral
    (density X (width X) j (primeTuples X j)) X (lowCut X K)
    (density_integrable X (width X) j (primeTuples X j) hX hlog hj hY hYX)
    (fun t => sq_nonneg _))
  simpa only [totalEnergy,energy,lowEnergy,centeredMiddle,highEnergy,
    Finset.sum_add_distrib] using hsum

/-- Keeps and pays the full-reference square; no cross term is dropped. -/
theorem density_le_prime_reference (X Y t : ℝ) (j : ℕ×ℕ)
    (hX : 0<X) (hY : 0<Y) (hYX : Y≤X/2) :
    density X Y j (primeTuples X j) t≤2*‖primeProduct X j t‖^2+2*‖referenceProduct X j t‖^2 := by
  have he0 : 0<Y/X := div_pos hY hX
  have he1 : Y/X<1 := (div_lt_one hX).mpr (by linarith)
  have hK := Item1OriginalCenterLow.sharp_norm_le_one (Y/X) t he0 he1
  have hnorm := mul_le_mul_of_nonneg_right hK (norm_nonneg (originalCentered X j t))
  have htri := norm_sub_le (primeProduct X j t) (referenceProduct X j t)
  rw [density_eq_low,norm_mul]
  have hprod0 : 0≤‖Item1OriginalCenterLow.sharpMultiplier (Y/X) t‖*
      ‖originalCentered X j t‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  simp only [one_mul,originalCentered] at hnorm
  have hh := pow_le_pow_left₀ hprod0 (hnorm.trans htri) 2
  nlinarith [sq_nonneg (‖primeProduct X j t‖-‖referenceProduct X j t‖)]

theorem cell_centered_middle (X : ℝ) (K : ℕ) (j : ℕ×ℕ)
    (hX : 2≤X) (hlog : 1000000≤Real.log X) (hj : j∈boxes (mesh X)) :
    (∫ t in SourceLiteralMiddle.middle X (lowCut X K), density X (width X) j (primeTuples X j) t)≤
      2*(∫ t in SourceLiteralMiddle.middle X (lowCut X K), ‖primeProduct X j t‖^2)+
      1620000/lowCut X K := by
  have hXp : 0<X := by linarith
  obtain ⟨hY,hYX⟩ := width_bounds X (by linarith)
  have hU : 0<lowCut X K := lt_of_lt_of_le (by norm_num : (0:ℝ)<1)
    (lowCut_ge_one X K (by linarith))
  have hcont : Continuous (fun t => ‖primeProduct X j t‖^2) :=
    ((((prime_continuous X j 0).mul (prime_continuous X j 1)).mul
      (prime_continuous X j 2)).norm.pow 2)
  have hp := (hcont.integrableOn_Icc (μ := volume)).mono_set (SourceLiteralMiddle.middle_subset X (lowCut X K))
  have hrc : Continuous (fun t => ‖referenceProduct X j t‖^2) :=
    (reference_continuous X j hXp).norm.pow 2
  have hr := (hrc.integrableOn_Icc (μ := volume)).mono_set
    (SourceLiteralMiddle.middle_subset X (lowCut X K))
  have hd : IntegrableOn (density X (width X) j (primeTuples X j))
      (SourceLiteralMiddle.middle X (lowCut X K)) :=
    (density_integrable X (width X) j (primeTuples X j) hX hlog hj hY hYX).integrableOn
  have hs := setIntegral_mono_on hd ((hp.const_mul 2).add (hr.const_mul 2))
    (SourceLiteralMiddle.middle_measurable X (lowCut X K))
    (fun t _ => density_le_prime_reference X (width X) t j hXp hY hYX)
  simp only [Pi.add_apply] at hs
  rw [integral_add (hp.const_mul 2) (hr.const_mul 2),integral_const_mul,integral_const_mul] at hs
  have hb := SourceCenteredMiddle.reference_middle X (lowCut X K) j hX hlog hj hU
  calc
    _ ≤ 2*(∫ t in SourceLiteralMiddle.middle X (lowCut X K), ‖primeProduct X j t‖^2)+
        2*(∫ t in SourceLiteralMiddle.middle X (lowCut X K), ‖referenceProduct X j t‖^2) := hs
    _ ≤ 2*(∫ t in SourceLiteralMiddle.middle X (lowCut X K), ‖primeProduct X j t‖^2)+
        2*(810000/lowCut X K) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hb (by norm_num))
    _ = _ := by ring

/-- Cardinality is supplied from the actual grid, not the number of hosts. -/
theorem centered_middle_bound (X : ℝ) (K : ℕ)
    (hX : 2≤X) (hlog : 1000000≤Real.log X) (hm : mesh X≤1/1000000) :
    centeredMiddle X K≤2*primeMiddle X K+36000*(Real.log X)^2/lowCut X K := by
  have hsum := Finset.sum_le_sum (fun j hj => cell_centered_middle X K j hX hlog hj)
  simp only [Finset.sum_add_distrib,←Finset.mul_sum,Finset.sum_const,nsmul_eq_mul] at hsum
  have hl : 0<Real.log X := by linarith
  have hU : 0<lowCut X K := lt_of_lt_of_le (by norm_num : (0:ℝ)<1)
    (lowCut_ge_one X K (by linarith))
  have hc := (div_le_iff₀ (by positivity : 0<(Real.log X)^2)).mp
    (cell_card_normalized_bound X (by linarith) hm)
  have hc' := mul_le_mul_of_nonneg_right hc (show 0≤1620000/lowCut X K by positivity)
  change centeredMiddle X K≤2*primeMiddle X K+_ at hsum
  have hnum : ((boxes (mesh X)).card:ℝ)*(1620000/lowCut X K)≤
      36000*(Real.log X)^2/lowCut X K := by
    convert hc' using 1 <;> ring
  linarith

theorem reference_correction_small (X : ℝ) (K : ℕ)
    (hK : 20≤K) (hlog : 1000000≤Real.log X) :
    36000*(Real.log X)^2/lowCut X K≤1/4096 := by
  have hl : 1≤Real.log X := by linarith
  have hp : (Real.log X)^20≤lowCut X K := pow_le_pow_right₀ hl hK
  have hpow : (1000000:ℝ)^2≤(Real.log X)^18 :=
    (pow_le_pow_left₀ (by norm_num) hlog 2).trans (pow_le_pow_right₀ hl (by omega))
  calc
    _ ≤ 36000*(Real.log X)^2/(Real.log X)^20 :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hp
    _ = 36000/(Real.log X)^18 := by field_simp <;> ring
    _ ≤ 1/4096 := by
      apply (div_le_div_iff₀ (by positivity : 0<(Real.log X)^18) (by norm_num : (0:ℝ)<4096)).mpr
      norm_num at hpow
      linarith

/-- The remaining premise is visibly a PRIME MIDDLE INTEGRAL, not a renamed
physical source mean. Low/reference/high and physical deletion are built inside. -/
theorem eventually_literal_item1_of_prime_middle (K : ℕ) (hK : 20≤K) :
    ∀ᶠ X : ℝ in atTop, primeMiddle X K≤1/8192 →
      (∫ x in Icc X (2*X), sourceResidualAbs X x (x*width X/X))/X≤1/(Real.log X)^2 := by
  filter_upwards [eventually_geometry,eventually_low_budget K,eventually_high_budget,
    eventually_literal_item1_of_energy] with X hg hLow hHigh hEnd
  intro hMiddle
  obtain ⟨hY,hYX⟩ := width_bounds X (by linarith [hg.1])
  apply hEnd (width X) hY hYX
  have hparts := totalEnergy_le_parts X K hg.1 hg.2.1
  have hl := hLow (width X) hY hYX
  have hm := centered_middle_bound X K hg.1 hg.2.1 hg.2.2
  have hr := reference_correction_small X K hK hg.2.1
  linarith

/-- Not proved here. A proof must come from the actual-cell fractional-moment
argument and its genuine first-factor prime cap. -/
def PrimeMiddleBudget (K : ℕ) : Prop :=
  ∀ᶠ X : ℝ in atTop, primeMiddle X K≤1/8192

/-- Final CONDITIONAL type. Printing this type is part of the bounded audit. -/
theorem item1_of_prime_middle (K : ℕ) (hK : 20≤K) (hMiddle : PrimeMiddleBudget K) :
    ∀ᶠ X : ℝ in atTop,
      (∫ x in Icc X (2*X), sourceResidualAbs X x (x*width X/X))/X≤1/(Real.log X)^2 := by
  filter_upwards [eventually_literal_item1_of_prime_middle K hK,hMiddle] with X he hm
  exact he hm

/-- The fixed bound already used by the 1024-cap moment route is enough.
This is scalar absorption, NOT a proof of the moment estimate. -/
theorem primeMiddle_budget_of_rate (K : ℕ)
    (hRate : ∀ᶠ X : ℝ in atTop, primeMiddle X K≤(2:ℝ)^55/(Real.log X)^6) :
    PrimeMiddleBudget K := by
  filter_upwards [hRate,Real.tendsto_log_atTop.eventually (eventually_ge_atTop (4096:ℝ))]
    with X hr hl
  have hp : (4096:ℝ)^6≤(Real.log X)^6 := pow_le_pow_left₀ (by norm_num) hl 6
  apply hr.trans
  apply (div_le_div_iff₀ (by positivity : 0<(Real.log X)^6)
    (by norm_num : (0:ℝ)<8192)).mpr
  norm_num at hp ⊢
  linarith

end Item1AllFrequencyMerge

-- ROOT SOURCE RECURSIVE AUDIT: exact original declarations.
run_cmd do
  for target in [
    ``Item1AllFrequencyMerge.three_part_integral,
    ``Item1AllFrequencyMerge.totalEnergy_le_parts,
    ``Item1AllFrequencyMerge.density_le_prime_reference,
    ``Item1AllFrequencyMerge.cell_centered_middle,
    ``Item1AllFrequencyMerge.centered_middle_bound,
    ``Item1AllFrequencyMerge.reference_correction_small,
    ``Item1AllFrequencyMerge.eventually_literal_item1_of_prime_middle,
    ``Item1AllFrequencyMerge.item1_of_prime_middle,
    ``Item1AllFrequencyMerge.primeMiddle_budget_of_rate] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "Item1AllFrequencyMerge: 9 original theorem guards passed."
