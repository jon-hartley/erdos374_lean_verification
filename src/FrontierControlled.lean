import FrontierResidual
import FrontierEmptyProfile

/-! The complete actual lower source, after subtracting its explicit low-d
exceptional contribution, has a moving-window second-moment power saving.
Three literal signed divisor families retain all coefficient collisions.
This is not an estimate for the full signed high-index remainder. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace FrontierControlled

def componentSupport (X s z:ℝ) (i:Fin 3) : Finset ℕ :=
  if i=0 then
    FiniteDivisorFamily.support (FrontierSieveCovered.family X s)
      (FrontierSieveCovered.componentSupport X s z)
  else if i=1 then
    FiniteDivisorFamily.support (FrontierResidual.highFamily X s)
      (FrontierSmallBracketCovered.componentSupport X s z)
  else SieveUpperBoxWindow.smallCarrier (SieveWeightedCutoffs.level X s) s

def componentWeight (X s z:ℝ) (i:Fin 3) : ℕ→ℝ :=
  if i=0 then
    FiniteDivisorFamily.coefficient (FrontierSieveCovered.family X s)
      (FrontierSieveCovered.componentSupport X s z)
      (FrontierSieveCovered.componentWeight X s z)
  else if i=1 then
    FiniteDivisorFamily.coefficient (FrontierResidual.highFamily X s)
      (FrontierSmallBracketCovered.componentSupport X s z)
      (FrontierSmallBracketCovered.componentWeight X s z)
  else fun m => -SieveSmallWeights.weight ((SieveWeightedCutoffs.level X s)^s)
    ((SieveWeightedCutoffs.level X s)^(s^2)) false m

def remainder (X s z L R:ℝ) : ℝ :=
  HarmanDivisorWindow.remainder
    (FiniteDivisorFamily.support Finset.univ (componentSupport X s z))
    (FiniteDivisorFamily.coefficient Finset.univ (componentSupport X s z)
      (componentWeight X s z)) L R

theorem component_zero (X s z L R:ℝ) :
    HarmanDivisorWindow.remainder (componentSupport X s z 0)
      (componentWeight X s z 0) L R = FrontierSieveCovered.remainder X s z L R := by
  simp only [componentSupport,componentWeight,ite_true,FrontierSieveCovered.remainder]

theorem component_one (X s z L R:ℝ) :
    HarmanDivisorWindow.remainder (componentSupport X s z 1)
      (componentWeight X s z 1) L R = FrontierResidual.highRemainder X s z L R := by
  simp [componentSupport,componentWeight,FrontierResidual.highRemainder,
    FrontierSmallBracketCovered.remainder]

theorem component_two (X s z L R:ℝ) :
    HarmanDivisorWindow.remainder (componentSupport X s z 2)
      (componentWeight X s z 2) L R = -FrontierSieveEnumeration.emptyRemainder X s z L R := by
  have hh := FactoredDivisorScaling.remainder_scale
    (SieveUpperBoxWindow.smallCarrier (SieveWeightedCutoffs.level X s) s)
    (SieveSmallWeights.weight ((SieveWeightedCutoffs.level X s)^s)
      ((SieveWeightedCutoffs.level X s)^(s^2)) false) (-1) L R
  simpa [componentSupport,componentWeight,FrontierEmptyProfile.empty_eq_small_remainder] using hh

theorem remainder_eq (X s z L R:ℝ) :
    remainder X s z L R = FrontierSieveCovered.remainder X s z L R +
      FrontierResidual.highRemainder X s z L R - FrontierSieveEnumeration.emptyRemainder X s z L R := by
  simp only [remainder,FiniteDivisorFamily.remainder_eq_sum,Fin.sum_univ_succ,Fin.sum_univ_zero]
  change HarmanDivisorWindow.remainder (componentSupport X s z 0) (componentWeight X s z 0) L R +
    (HarmanDivisorWindow.remainder (componentSupport X s z 1) (componentWeight X s z 1) L R +
    (HarmanDivisorWindow.remainder (componentSupport X s z 2) (componentWeight X s z 2) L R + 0)) = _
  rw [component_zero,component_one,component_two]
  ring

theorem remainder_eq_source_sub_low (X s z L R:ℝ)
    (hD:1<SieveWeightedCutoffs.level X s) (hs:0<s)
    (hz:z≤SieveWeightedCutoffs.level X s) :
    remainder X s z L R =
      SieveBoxedWindow.sourceRemainder (SieveWeightedCutoffs.level X s) s z L R -
        FrontierResidual.lowRemainder X s z L R := by
  rw [remainder_eq,FrontierResidual.source_exact X s z L R hD hs hz]
  ring

theorem eventually_half_width_bound (s:ℝ) (hs:0<s) (hs1:s≤1/1000) :
    ∃c:ℝ, 0<c ∧ ∀ᶠ X:ℝ in atTop, 1<X ∧ ∀z:ℝ,
      z≤SieveWeightedCutoffs.level X s →
      let Y:=PositiveSharpPowerWindow.halfWidth X (101/1000)
      (1/X)*(∫x in Icc X (2*X),
        (SieveBoxedWindow.sourceRemainder (SieveWeightedCutoffs.level X s) s z
          (x-x*(Y/X)) x - FrontierResidual.lowRemainder X s z (x-x*(Y/X)) x)^2)
          ≤Y^2*X^(-c) := by
  obtain ⟨cB,hcB,hB⟩ := FrontierSieveCovered.eventually_half_width_bound s hs hs1
  obtain ⟨cH,hcH,hH⟩ := FrontierResidual.eventually_high_half_width_bound s hs hs1
  let c:ℝ := min cB (min cH (1/10))
  have hc:0<c := lt_min hcB (lt_min hcH (by norm_num))
  have hcB':c≤cB := min_le_left _ _
  have hcH':c≤cH := (min_le_right _ _).trans (min_le_left _ _)
  have hcE':c≤1/10 := (min_le_right _ _).trans (min_le_right _ _)
  have hcard := (tendsto_rpow_atTop (show 0<c/4 by positivity)).eventually
    (eventually_ge_atTop (3:ℝ))
  refine ⟨c/2,by positivity,?_⟩
  filter_upwards [hB,hH,FrontierEmptyProfile.eventually_half_width_bound s hs hs1,hcard,
    PositiveSharpPowerWindow.halfWidth_eventually (101/1000) (by norm_num)]
    with X hB hH hE hcard hhalf
  refine ⟨hB.1,?_⟩
  intro z hz
  let Y:=PositiveSharpPowerWindow.halfWidth X (101/1000)
  have hX:0<X := by linarith [hB.1]
  have hY:0<Y := hhalf.1
  have hYX:Y≤X := by have hh:Y≤X/4 := hhalf.2; linarith
  have hmean : ∀i∈(Finset.univ:Finset (Fin 3)),
      (1/X)*(∫x in Icc X (2*X),
        HarmanDivisorWindow.remainder (componentSupport X s z i)
          (componentWeight X s z i) (x-x*(Y/X)) x ^2)≤Y^2*X^(-c) := by
    intro i _
    fin_cases i
    · change (1/X)*(∫x in Icc X (2*X),HarmanDivisorWindow.remainder
        (componentSupport X s z 0) (componentWeight X s z 0) (x-x*(Y/X)) x ^2)≤_
      simp_rw [component_zero]
      exact (hB.2 z hz).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hB.1.le (neg_le_neg hcB')) (sq_nonneg Y))
    · change (1/X)*(∫x in Icc X (2*X),HarmanDivisorWindow.remainder
        (componentSupport X s z 1) (componentWeight X s z 1) (x-x*(Y/X)) x ^2)≤_
      simp_rw [component_one]
      exact (hH.2 z hz).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hB.1.le (neg_le_neg hcH')) (sq_nonneg Y))
    · change (1/X)*(∫x in Icc X (2*X),HarmanDivisorWindow.remainder
        (componentSupport X s z 2) (componentWeight X s z 2) (x-x*(Y/X)) x ^2)≤_
      simp_rw [component_two,neg_sq]
      exact (hE.2 z).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hB.1.le (neg_le_neg hcE')) (sq_nonneg Y))
  have hh := FiniteDivisorFamily.normalized_power_bound
    (Finset.univ:Finset (Fin 3)) (componentSupport X s z) (componentWeight X s z)
    X Y c hX hY.le hYX (by simpa using hcard) hmean
  have hD:1<SieveWeightedCutoffs.level X s := Real.one_lt_rpow hB.1 (by linarith)
  change (1/X)*(∫x in Icc X (2*X),remainder X s z (x-x*(Y/X)) x ^2)≤_ at hh
  simpa only [remainder_eq_source_sub_low X s z _ _ hD hs hz] using hh

run_cmd do
  for decl in [``component_zero,``component_one,``component_two,``remainder_eq,
      ``remainder_eq_source_sub_low,``eventually_half_width_bound] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "COMPLETE LOWER SOURCE MINUS LITERAL LOW-D EXCEPTIONS HAS POWER-SAVING SECOND MOMENT"

end FrontierControlled
