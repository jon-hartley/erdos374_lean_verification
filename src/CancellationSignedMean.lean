import CancellationDivisorBias
import MomentRemainderSupport

/-! The signed average of the COMPLETE physical remainder is unconditionally
small. The absolute value is outside the integral throughout. This does not
give the needed square mean or the positive harmful-tail estimate. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators

namespace CancellationSignedMean
open PositiveSharpRemainderAnalysisPhysical

theorem support_card_le (X s : ℝ) (hX : 0<X)
    (hsup : ∀m∈support X s, 0<m ∧ (m:ℝ)<X^(1-2*s)) :
    ((support X s).card:ℝ)≤X^(1-2*s) := by
  have hsub : support X s⊆Finset.Ioc 0 ⌊X^(1-2*s)⌋₊ := by
    intro m hm
    exact Finset.mem_Ioc.mpr ⟨(hsup m hm).1, Nat.le_floor (hsup m hm).2.le⟩
  have hc : ((support X s).card:ℝ)≤(⌊X^(1-2*s)⌋₊:ℝ) := by
    exact_mod_cast (by simpa using Finset.card_le_card hsub :
      (support X s).card≤⌊X^(1-2*s)⌋₊)
  exact hc.trans (Nat.floor_le (Real.rpow_pos_of_pos hX _).le)

theorem coefficient_mass_le (X s : ℝ) (hX : 0<X)
    (hc : ∀m∈support X s, 0<m ∧ (m:ℝ)<X^(1-2*s) ∧ |coefficient X s m|≤X^s) :
    (∑m∈support X s, |coefficient X s m|)≤X^(1-s) := by
  calc
    _ ≤ ∑_m∈support X s, X^s := Finset.sum_le_sum (fun m hm => (hc m hm).2.2)
    _ = (support X s).card*X^s := by simp
    _ ≤ X^(1-2*s)*X^s := mul_le_mul_of_nonneg_right
      (support_card_le X s hX (fun m hm => ⟨(hc m hm).1,(hc m hm).2.1⟩)) (by positivity)
    _ = X^(1-s) := by rw [←Real.rpow_add hX]; congr 1; ring

theorem signed_mean_bound (X s Y : ℝ) (hX : 0<X) (hY : 0≤Y) (hYX : Y<X)
    (hc : ∀m∈support X s, 0<m ∧ (m:ℝ)<X^(1-2*s) ∧ |coefficient X s m|≤X^s) :
    |(∫x in Icc X (2*X), PositiveSharpBoxedCount.signedRemainder X s x (x*Y/X))/X|≤
      2*Y*X^(-s) := by
  have hh := CancellationDivisorBias.moving_remainder_integral_bias
    (support X s) (coefficient X s) X Y hX hY hYX
  have hm := coefficient_mass_le X s hX hc
  have he : X^(1-s)=X*X^(-s) := by
    simpa only [sub_eq_add_neg, Real.rpow_one] using Real.rpow_add hX 1 (-s)
  simp_rw [signedRemainder_eq]
  rw [abs_div, abs_of_pos hX]
  apply (div_le_iff₀ hX).mpr
  calc
    _ ≤ 2*Y*(∑m∈support X s, |coefficient X s m|) := hh
    _ ≤ 2*Y*X^(1-s) := mul_le_mul_of_nonneg_left hm (by positivity)
    _ = _ := by rw [he]; ring

theorem eventually_signed_mean (s : ℝ) (hs : 0<s) (hs1 : s≤1/1000) :
    ∀ᶠ X:ℝ in atTop, 1<X ∧ ∀Y:ℝ, 0≤Y → Y<X →
      |(∫x in Icc X (2*X), PositiveSharpBoxedCount.signedRemainder X s x (x*Y/X))/X|≤
        2*Y*X^(-s) := by
  filter_upwards [MomentRemainderSupport.eventually_support_and_coefficient s s hs hs1 hs]
    with X hX
  exact ⟨hX.1,fun Y hY hYX => signed_mean_bound X s Y (by linarith [hX.1]) hY hYX hX.2⟩

theorem eventually_signed_mean_log (s : ℝ) (A : ℕ) (hs : 0<s) (hs1 : s≤1/1000) :
    ∀ᶠ X:ℝ in atTop, 1<X ∧ ∀Y:ℝ, 0≤Y → Y<X →
      |(∫x in Icc X (2*X), PositiveSharpBoxedCount.signedRemainder X s x (x*Y/X))/X|≤
        Y/(Real.log X)^A := by
  filter_upwards [eventually_signed_mean s hs hs1,
    PolynomialLogEnvelope.eventually_bound 2 A s (by norm_num) hs] with X hb he
  have hX : 0<X := by linarith [hb.1]
  have hl : 0<Real.log X := Real.log_pos hb.1
  have hlog : 2*(Real.log X)^A≤X^s := by
    apply le_trans _ he.2
    gcongr
    linarith
  have hunit : 2*X^(-s)*(Real.log X)^A≤1 := by
    calc
      _ = X^(-s)*(2*(Real.log X)^A) := by ring
      _ ≤ X^(-s)*X^s := mul_le_mul_of_nonneg_left hlog (by positivity)
      _ = 1 := by rw [←Real.rpow_add hX]; simp
  refine ⟨hb.1,?_⟩
  intro Y hY hYX
  apply (hb.2 Y hY hYX).trans
  apply (le_div_iff₀ (pow_pos hl A)).mpr
  have hh := mul_le_mul_of_nonneg_left hunit hY
  nlinarith

run_cmd do
  for decl in [``support_card_le, ``coefficient_mass_le, ``signed_mean_bound,
      ``eventually_signed_mean, ``eventually_signed_mean_log] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "WHOLE ACTUAL SIGNED REMAINDER BIAS HAS POWER AND LOG SAVINGS; SQUARE MEAN OPEN"

end CancellationSignedMean
