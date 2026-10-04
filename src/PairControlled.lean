import SingletonControlled
import PairActualResidual
import PairActualMoment

/-! At the actual first cutoff, the complete lower source is controlled up to
the explicit low-small-divisor outer-triple contribution. This does not bound
the separate upper-sieve families or source residual. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace PairControlled

def componentSupport (X s z : ℝ) (b : Bool) : Finset ℕ :=
  if b then FiniteDivisorFamily.support Finset.univ (SingletonControlled.componentSupport X s z)
  else PairActualCollection.support X s z

def componentWeight (X s z : ℝ) (b : Bool) : ℕ→ℝ :=
  if b then FiniteDivisorFamily.coefficient Finset.univ (SingletonControlled.componentSupport X s z)
    (SingletonControlled.componentWeight X s z)
  else PairActualCollection.coefficient X s z

def remainder (X s z L R : ℝ) : ℝ :=
  HarmanDivisorWindow.remainder
    (FiniteDivisorFamily.support Finset.univ (componentSupport X s z))
    (FiniteDivisorFamily.coefficient Finset.univ (componentSupport X s z)
      (componentWeight X s z)) L R

theorem component_true (X s z L R : ℝ) :
    HarmanDivisorWindow.remainder (componentSupport X s z true)
      (componentWeight X s z true) L R=SingletonControlled.remainder X s z L R := by
  rfl

theorem component_false (X s z L R : ℝ) :
    HarmanDivisorWindow.remainder (componentSupport X s z false)
      (componentWeight X s z false) L R=PairActualCollection.remainder X s z L R := by
  rfl

theorem remainder_eq (X s z L R : ℝ) :
    remainder X s z L R=SingletonControlled.remainder X s z L R+
      PairActualCollection.remainder X s z L R := by
  rw [remainder,FiniteDivisorFamily.remainder_eq_sum,Fintype.sum_bool]
  rw [component_true,component_false]

theorem remainder_eq_source_sub_remaining (X s z L R : ℝ)
    (hX : 1<X) (hs : 0<s) (hs1 : s≤1/1000)
    (hz : z≤SieveWeightedCutoffs.level X s) :
    remainder X s z L R =
      SieveBoxedWindow.sourceRemainder (SieveWeightedCutoffs.level X s) s z L R-
        PairActualResidual.remainder X s z L R := by
  have hD : 1<SieveWeightedCutoffs.level X s := Real.one_lt_rpow hX (by linarith)
  rw [remainder_eq,SingletonControlled.remainder_eq_source_sub_remaining X s z L R hD hs hz,
    PairActualResidual.remaining_eq_pair_add_outer X s z L R hX hs hs1 hz]
  ring

theorem eventually_half_width_bound (s : ℝ) (hs : 0<s) (hs1 : s≤1/1000) :
    ∃c:ℝ, 0<c ∧ ∀ᶠ X:ℝ in atTop, 1<X ∧ ∀z:ℝ,
      z≤X^(SieveWeightedScalarBudget.alpha s) →
      let Y:=PositiveSharpPowerWindow.halfWidth X (101/1000)
      (1/X)*(∫x in Icc X (2*X),
        (SieveBoxedWindow.sourceRemainder (SieveWeightedCutoffs.level X s) s z
          (x-x*(Y/X)) x-PairActualResidual.remainder X s z (x-x*(Y/X)) x)^2)
          ≤Y^2*X^(-c) := by
  obtain ⟨cS,hcS,hS⟩ := SingletonControlled.eventually_half_width_bound s hs hs1
  let c:ℝ := min cS (1/250)
  have hc : 0<c := lt_min hcS (by norm_num)
  have hcS' : c≤cS := min_le_left _ _
  have hcP' : c≤1/250 := min_le_right _ _
  have hcard := (tendsto_rpow_atTop (show 0<c/4 by positivity)).eventually
    (eventually_ge_atTop (2:ℝ))
  refine ⟨c/2,by positivity,?_⟩
  filter_upwards [hS,PairActualMoment.eventually_half_width_bound s hs hs1,hcard,
    PositiveSharpPowerWindow.halfWidth_eventually (101/1000) (by norm_num)]
    with X hS hP hcard hhalf
  refine ⟨hS.1,?_⟩
  intro z hz
  let Y:=PositiveSharpPowerWindow.halfWidth X (101/1000)
  have hX : 0<X := by linarith [hS.1]
  have hY : 0<Y := hhalf.1
  have hYX : Y≤X := by have hh:Y≤X/4 := hhalf.2; linarith
  have hzD : z≤SieveWeightedCutoffs.level X s := hz.trans
    (SingletonActualCollection.cutoff_le_level X s hS.1.le hs.le hs1)
  have hD : 1<SieveWeightedCutoffs.level X s := Real.one_lt_rpow hS.1 (by linarith)
  have hmean : ∀b∈(Finset.univ:Finset Bool),
      (1/X)*(∫x in Icc X (2*X),HarmanDivisorWindow.remainder (componentSupport X s z b)
        (componentWeight X s z b) (x-x*(Y/X)) x ^2)≤Y^2*X^(-c) := by
    intro b _
    cases b with
    | false =>
      simp_rw [component_false]
      exact (hP.2 z hz).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hS.1.le (neg_le_neg hcP')) (sq_nonneg Y))
    | true =>
      simp_rw [component_true,SingletonControlled.remainder_eq_source_sub_remaining X s z _ _ hD hs hzD]
      exact (hS.2 z hz).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hS.1.le (neg_le_neg hcS')) (sq_nonneg Y))
  have hh := FiniteDivisorFamily.normalized_power_bound
    (Finset.univ:Finset Bool) (componentSupport X s z) (componentWeight X s z)
    X Y c hX hY.le hYX (by simpa using hcard) hmean
  change (1/X)*(∫x in Icc X (2*X),remainder X s z (x-x*(Y/X)) x ^2)≤_ at hh
  simpa only [remainder_eq_source_sub_remaining X s z _ _ hS.1 hs hs1 hzD] using hh

run_cmd do
  for decl in [``component_true,``component_false,``remainder_eq,
      ``remainder_eq_source_sub_remaining,``eventually_half_width_bound] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "COMPLETE LOWER SOURCE MINUS ACTUAL LOW-D OUTER TRIPLES HAS M2 POWER SAVING"

end PairControlled
