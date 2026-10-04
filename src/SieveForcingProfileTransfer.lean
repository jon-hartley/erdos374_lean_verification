import SieveForcingProfileCalculus

/-! Actual discrete forcing has its exact continuous leading profile, with
an explicit uniform arithmetic error and no assumed density statement. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
open Real Set MeasureTheory SieveStoppingExpansion SieveStoppingTwoStep
  SieveStoppingForcing PrimeEulerLogBounds SieveForcingProfileInner
  SieveForcingProfileCalculus

namespace SieveForcingProfileTransfer

theorem tail_error_le (A a b x : ℝ) (ha : 2 ≤ a) (hab : a ≤ b)
    (hA : 2*log b ≤ A) (hla : log a=A/4) (hx : x ∈ Icc a b) :
    PrimeEulerDimensionOne.errorConstant*log b/(log x)^2 ≤ 4*epsilon b := by
  have hlb : 0 < log b := log_pos (by linarith)
  have hlx : 0 < log x := log_pos (by linarith [hx.1])
  have hlax : log a ≤ log x := log_le_log (by linarith) hx.1
  have hh : (log b)^2 ≤ 4*(log x)^2 := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hh PrimeEulerDimensionOne.errorConstant_pos.le
  apply (div_le_iff₀ (sq_pos_of_pos hlx)).mpr
  apply (mul_le_mul_iff_right₀ hlb).mp
  have hc : log b*(4*epsilon b*(log x)^2) =
      4*PrimeEulerDimensionOne.errorConstant*(log x)^2 := by
    unfold epsilon
    field_simp
  rw [hc]
  nlinarith

theorem weighted_test_bound (A a b : ℝ) (ha : 2 ≤ a) (hab : a ≤ b)
    (hA : 2*log b ≤ A) (hla : log a=A/4) :
    (∑ p ∈ intervalPrimes a b, test A (p:ℝ)*
      (PrimeEulerMass.weight p/primeEuler b)) ≤ profile (A/log b)+8*epsilon b := by
  have hlb : 0 < log b := log_pos (by linarith)
  have hA0 : 0 < A := by linarith
  have hAb : log b < A := by linarith
  have he : 0 ≤ epsilon b := div_nonneg PrimeEulerDimensionOne.errorConstant_pos.le hlb.le
  have ht := test_lower_endpoint A a (by linarith) hla
  have hfc := derivative_continuousOn A a b ha hAb
  have hfi : IntervalIntegrable (derivative A) volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
    exact hfc.integrableOn_Icc
  have hic : ContinuousOn (fun x => derivative A x*(log b/log x-1)) (Icc a b) := by
    exact hfc.mul ((continuousOn_const.div
      (continuousOn_id.log (fun x hx => by change x ≠ 0; linarith [hx.1]))
      (fun x hx => (log_pos (by change 1 < x; linarith [hx.1])).ne')).sub continuousOn_const)
  have hii : IntervalIntegrable (fun x => derivative A x*(log b/log x-1)) volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
    exact hic.integrableOn_Icc
  have hti : IntervalIntegrable
      (fun x => derivative A x*PrimeEulerWeightedTransfer.tailBound x b) volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
    exact (hfc.mul (PrimeEulerWeightedTransfer.tailBound_continuousOn a b ha)).integrableOn_Icc
  have hbnd := PrimeEulerWeightedTransfer.prime_weighted_transfer (test A) (derivative A) a b
    ha hab (by rw [ht]) (test_continuousOn A a b ha hAb) hfc
    (fun x hx => derivative_nonneg A x hA0.le (by linarith [hx.1]))
    (fun x hx => test_hasDerivAt A x (by linarith [hx.1])
      ((log_le_log (by linarith [hx.1] : 0 < x) hx.2.le).trans_lt hAb))
  rw [ht, zero_mul, zero_add] at hbnd
  have hcomp : (∫ x in a..b, derivative A x*PrimeEulerWeightedTransfer.tailBound x b) ≤
      (∫ x in a..b, derivative A x*(log b/log x-1)+derivative A x*(4*epsilon b)) := by
    apply intervalIntegral.integral_mono_on hab hti (hii.add (hfi.mul_const _))
    intro x hx
    have hh := mul_le_mul_of_nonneg_left (tail_error_le A a b x ha hab hA hla hx)
      (derivative_nonneg A x hA0.le (by linarith [hx.1]))
    unfold PrimeEulerWeightedTransfer.tailBound
    nlinarith
  rw [intervalIntegral.integral_add hii (hfi.mul_const _),
    intervalIntegral.integral_mul_const, ideal_integral A a b ha hab hAb hla,
    integral_derivative A a b ha hab hAb, ht, sub_zero] at hcomp
  have hm := mul_le_mul_of_nonneg_right (test_le_two A b (by linarith) hA)
    (by positivity : 0 ≤ 4*epsilon b)
  exact hbnd.trans (hcomp.trans (by nlinarith))

theorem forcing_profile_bound (T z : ℝ) (hz : 64 ≤ z)
    (hT : z^2 ≤ T) (hT4 : T ≤ z^4) :
    forcing T z ≤ profile (log T/log z)+17*epsilon z+36*(epsilon z)^2 := by
  have hz0 : 0 < z := by linarith
  have hT0 : 0 < T := (pow_pos hz0 2).trans_le hT
  have hlz : 0 < log z := log_pos (by linarith)
  have he : 0 ≤ epsilon z := div_nonneg PrimeEulerDimensionOne.errorConstant_pos.le hlz.le
  obtain ⟨hr2, _⟩ := SieveStoppingSharpForcing.parameter_bounds T z (by linarith) hT hT4
  have ha : 2 ≤ root T 4 := root_lower 2 T 4 (by norm_num) (by norm_num) (by nlinarith)
  have haz : root T 4 ≤ z := SieveStoppingSharpForcing.root_le_of_le_pow z T 4
    (by norm_num) hz0 hT0 hT4
  have hlogT : 2*log z ≤ log T := (le_div_iff₀ hlz).mp hr2
  have hw := weighted_test_bound (log T) (root T 4) z ha haz hlogT
    (by simp [root])
  have hmass := SieveStoppingSharpForcing.outer_interval_bound T z hz hT hT4
  have hratio : (4-log T/log z)/(log T/log z) ≤ 1 :=
    (div_le_iff₀ (by linarith : 0 < log T/log z)).mpr (by linarith)
  have hmass' : (∑ p ∈ intervalPrimes (root T 4) z,
      PrimeEulerMass.weight p/primeEuler z) ≤ 1+4*epsilon z := by linarith
  have hforce : forcing T z ≤
      (∑ p ∈ intervalPrimes (root T 4) z, test (log T) (p:ℝ)*
        (PrimeEulerMass.weight p/primeEuler z))+
      9*epsilon z*(∑ p ∈ intervalPrimes (root T 4) z,
        PrimeEulerMass.weight p/primeEuler z) := by
    rw [forcing_factored, Finset.mul_sum, ← Finset.sum_add_distrib,
      interval_eq_filter, Finset.sum_filter]
    apply Finset.sum_le_sum
    intro p hp
    split_ifs with ha
    · have hh := mul_le_mul_of_nonneg_left (inner_profile_bound T z p hz hT hp ha)
        (normalized_weight_nonneg p z)
      nlinarith
    · rw [SieveStoppingSharpForcing.innerRejected_zero_below T z p hT0 hp
        (lt_of_not_ge ha), mul_zero]
  have herr := mul_le_mul_of_nonneg_left hmass' (by positivity : 0 ≤ 9*epsilon z)
  nlinarith

theorem eventually_forcing_profile (δ : ℝ) (hδ : 0 < δ) :
    ∃ Z : ℝ, 64 ≤ Z ∧ ∀ z T : ℝ, Z ≤ z → z^2 ≤ T → T ≤ z^4 →
      forcing T z ≤ profile (log T/log z)+δ := by
  let K := PrimeEulerDimensionOne.errorConstant
  let B := max K (53*K/δ)
  refine ⟨max 64 (exp B), le_max_left _ _, ?_⟩
  intro z T hz hT hT4
  have hz64 : 64 ≤ z := (le_max_left _ _).trans hz
  have hlz : 0 < log z := log_pos (by linarith)
  have hlog : B ≤ log z := by
    have hh := log_le_log (exp_pos B) ((le_max_right _ _).trans hz)
    simpa only [log_exp] using hh
  have he0 : 0 ≤ epsilon z := div_nonneg PrimeEulerDimensionOne.errorConstant_pos.le hlz.le
  have he1 : epsilon z ≤ 1 := by
    apply (div_le_iff₀ hlz).mpr
    simpa only [one_mul] using (le_max_left K (53*K/δ)).trans hlog
  have heδ : 53*epsilon z ≤ δ := by
    have hh := (le_max_right K (53*K/δ)).trans hlog
    have hm := (div_le_iff₀ hδ).mp hh
    unfold epsilon
    calc
      53*(PrimeEulerDimensionOne.errorConstant/log z) =
          53*PrimeEulerDimensionOne.errorConstant/log z := by ring
      _ ≤ δ := (div_le_iff₀ hlz).mpr (by dsimp [K] at hm; nlinarith)
  have hh := forcing_profile_bound T z hz64 hT hT4
  have hesq : (epsilon z)^2 ≤ epsilon z := by nlinarith
  nlinarith

run_cmd do
  for decl in [``tail_error_le, ``weighted_test_bound, ``forcing_profile_bound,
    ``eventually_forcing_profile] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ACTUAL SHARP FORCING PROFILE WITH UNIFORM VANISHING ERROR CHECKED"

end SieveForcingProfileTransfer
end
