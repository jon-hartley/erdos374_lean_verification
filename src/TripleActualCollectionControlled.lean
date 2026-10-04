import TripleActualCollectionMoment
import PairControlled

/-! Complete lower-source moving second-moment saving at the actual first
cutoff. The separate source residual and upper-sieve obligations remain open. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace TripleActualCollectionControlled

def componentSupport (X s z : ℝ) (b : Bool) : Finset ℕ :=
  if b then FiniteDivisorFamily.support Finset.univ (PairControlled.componentSupport X s z)
  else TripleActualCollection.support X s z

def componentWeight (X s z : ℝ) (b : Bool) : ℕ→ℝ :=
  if b then FiniteDivisorFamily.coefficient Finset.univ (PairControlled.componentSupport X s z)
    (PairControlled.componentWeight X s z)
  else TripleActualCollection.coefficient X s z

def remainder (X s z L R : ℝ) : ℝ :=
  HarmanDivisorWindow.remainder
    (FiniteDivisorFamily.support Finset.univ (componentSupport X s z))
    (FiniteDivisorFamily.coefficient Finset.univ (componentSupport X s z)
      (componentWeight X s z)) L R

theorem component_true (X s z L R : ℝ) :
    HarmanDivisorWindow.remainder (componentSupport X s z true)
      (componentWeight X s z true) L R=PairControlled.remainder X s z L R := rfl

theorem component_false (X s z L R : ℝ) :
    HarmanDivisorWindow.remainder (componentSupport X s z false)
      (componentWeight X s z false) L R=TripleActualCollection.remainder X s z L R := rfl

theorem remainder_eq_source (X s z L R : ℝ) (hX : 1<X) (hs : 0<s) (hs1 : s≤1/1000)
    (hz : z≤SieveWeightedCutoffs.level X s) :
    remainder X s z L R=
      SieveBoxedWindow.sourceRemainder (SieveWeightedCutoffs.level X s) s z L R := by
  rw [remainder,FiniteDivisorFamily.remainder_eq_sum,Fintype.sum_bool,
    component_true,component_false,
    PairControlled.remainder_eq_source_sub_remaining X s z L R hX hs hs1 hz,
    TripleActualCollection.remainder_eq_actual X s z L R hX hs hs1]
  ring

theorem eventually_half_width_bound (s : ℝ) (hs : 0<s) (hs1 : s≤1/1000) :
    ∃c:ℝ,0<c ∧ ∀ᶠ X:ℝ in atTop,1<X ∧ ∀z:ℝ,
      z≤X^(SieveWeightedScalarBudget.alpha s) →
      let Y:=PositiveSharpPowerWindow.halfWidth X (101/1000)
      (1/X)*(∫x in Icc X (2*X),
        SieveBoxedWindow.sourceRemainder (SieveWeightedCutoffs.level X s) s z
          (x-x*(Y/X)) x ^2)≤Y^2*X^(-c) := by
  obtain ⟨cP,hcP,hP⟩ := PairControlled.eventually_half_width_bound s hs hs1
  obtain ⟨cT,hcT,hT⟩ := TripleActualCollectionMoment.eventually_half_width_bound s hs hs1
  let c:ℝ := min cP cT
  have hc : 0<c := lt_min hcP hcT
  have hcP' : c≤cP := min_le_left _ _
  have hcT' : c≤cT := min_le_right _ _
  have hcard := (tendsto_rpow_atTop (show 0<c/4 by positivity)).eventually
    (eventually_ge_atTop (2:ℝ))
  refine ⟨c/2,by positivity,?_⟩
  filter_upwards [hP,hT,hcard,
    PositiveSharpPowerWindow.halfWidth_eventually (101/1000) (by norm_num)]
    with X hP hT hcard hhalf
  refine ⟨hP.1,?_⟩
  intro z hz
  let Y:=PositiveSharpPowerWindow.halfWidth X (101/1000)
  have hX : 0<X := by linarith [hP.1]
  have hY : 0<Y := hhalf.1
  have hYX : Y≤X := by have hh:Y≤X/4 := hhalf.2; linarith
  have hzD : z≤SieveWeightedCutoffs.level X s := hz.trans
    (SingletonActualCollection.cutoff_le_level X s hP.1.le hs.le hs1)
  have hmean : ∀b∈(Finset.univ:Finset Bool),
      (1/X)*(∫x in Icc X (2*X),HarmanDivisorWindow.remainder (componentSupport X s z b)
        (componentWeight X s z b) (x-x*(Y/X)) x ^2)≤Y^2*X^(-c) := by
    intro b _
    cases b with
    | false =>
      simp_rw [component_false,TripleActualCollection.remainder_eq_actual X s z _ _ hP.1 hs hs1]
      exact (hT.2 z hz).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hP.1.le (neg_le_neg hcT')) (sq_nonneg Y))
    | true =>
      simp_rw [component_true,
        PairControlled.remainder_eq_source_sub_remaining X s z _ _ hP.1 hs hs1 hzD]
      exact (hP.2 z hz).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hP.1.le (neg_le_neg hcP')) (sq_nonneg Y))
  have hh := FiniteDivisorFamily.normalized_power_bound
    (Finset.univ:Finset Bool) (componentSupport X s z) (componentWeight X s z)
    X Y c hX hY.le hYX (by simpa using hcard) hmean
  change (1/X)*(∫x in Icc X (2*X),remainder X s z (x-x*(Y/X)) x ^2)≤_ at hh
  simpa only [remainder_eq_source X s z _ _ hP.1 hs hs1 hzD] using hh

run_cmd do
  for decl in [``component_true,``component_false,``remainder_eq_source,
      ``eventually_half_width_bound] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "COMPLETE LOWER SOURCE M2 POWER SAVING; UPPER AND SOURCE-RESIDUAL OBLIGATIONS OPEN"

end TripleActualCollectionControlled
