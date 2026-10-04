import Item1ParameterInner
import Item1ParameterPrefix
import Item1FixedCubicPhaseEndpoint

/-! The uniform parameter construction supplies the fixed cubic phase bound
and then the original literal Item 1 source-integral endpoint. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
open Filter MeasureTheory Set

namespace Item1ParameterEndpoint
open Item1ParameterCore Item1ParameterChoice Item1ParameterInner
open Item1ParameterPrefix Item1ParameterLoss Item1FixedCubicPhaseEndpoint
open Item1FiniteAbelPhase Item1LongLogPhase Item1ProductPrefixMoment

theorem cutoff_forces_eight (M : ℕ) (L : ℝ) (hMpos : 0 < M)
    (hL : (10:ℝ)^21 ≤ L)
    (hcut : 6*L^(2/3:ℝ)*Real.log L < Real.log (M:ℝ)) : 8 ≤ M := by
  have hM0 : (0:ℝ) < (M:ℝ) := by exact_mod_cast hMpos
  have hL1 : 1 ≤ L := (show (1:ℝ) ≤ (10:ℝ)^21 by norm_num).trans hL
  have hlogL := (cutoff_square_bound L (Real.log (M:ℝ)) hL hcut).2.1
  have hpow : 1 ≤ L^(2/3:ℝ) := Real.one_le_rpow hL1 (by norm_num)
  have hprod := one_le_mul_of_one_le_of_one_le hpow hlogL
  have hsix : 6 < Real.log (M:ℝ) := by nlinarith only [hprod, hcut]
  have hlogM := Real.log_le_sub_one_of_pos hM0
  have hseven : (7:ℝ) < (M:ℝ) := by linarith
  have hnat : 7 < M := by exact_mod_cast hseven
  omega

theorem exponent_identity (m L : ℝ) (hm : m ≠ 0) (hL : L ≠ 0) :
    -m/(4000000*(L/m)^2) = -(1/4000000:ℝ)*(m^3/L^2) := by
  field_simp <;> ring

theorem prefix_bound (M K : ℕ) (t : ℝ) (hMpos : 0 < M)
    (ht : Real.exp ((10:ℝ)^21) ≤ t) (hMt : (M:ℝ) < t)
    (hcut : 6*(Real.log t)^(2/3:ℝ)*Real.log (Real.log t) < Real.log (M:ℝ))
    (hK : K ≤ M) :
    ‖«prefix» (atom M t) K‖ ≤
      5*(M:ℝ)*Real.exp (-(1/4000000:ℝ)*((Real.log (M:ℝ))^3/(Real.log t)^2)) := by
  let L := Real.log t
  let m := Real.log (M:ℝ)
  have htpos : 0 < t := lt_of_lt_of_le (Real.exp_pos _) ht
  have hL : (10:ℝ)^21 ≤ L := by
    have h := Real.log_le_log (Real.exp_pos ((10:ℝ)^21)) ht
    simpa only [Real.log_exp] using h
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) hL
  have hM8 : 8 ≤ M := cutoff_forces_eight M L hMpos hL hcut
  have hM1 : (1:ℝ) < (M:ℝ) := by exact_mod_cast (show 1 < M by omega)
  have hM0 : (0:ℝ) < (M:ℝ) := by exact_mod_cast hMpos
  have hmpos : 0 < m := Real.log_pos hM1
  have hmL : m ≤ L := (Real.log_lt_log hM0 hMt).le
  have hlam : 1 ≤ L/m := by
    apply (le_div_iff₀ hmpos).mpr
    simpa only [one_mul] using hmL
  have hinner : ∀ n : ℕ, n < K →
      ‖U (positiveSet (scale M)) (degree (L/m)) (scale M)
        ((M:ℝ)+n) ((M:ℝ)^(L/m))‖/(scale M:ℝ)^2 ≤
          Real.exp (-m/(4000000*(L/m)^2)) := by
    intro n hn
    exact inner_bound M n L hM8 hL hcut hlam ((Nat.le_of_lt hn).trans hK)
  have hp := prefix_le_of_inner_bound M K (L/m) hM8 hlam hK hinner
  have htaylor : (M:ℝ)^(L/m)=t := rpow_log_div (M:ℝ) t hM1 htpos
  rw [htaylor] at hp
  have hid := exponent_identity m L hmpos.ne' hLpos.ne'
  change ‖«prefix» (atom M t) K‖ ≤ 5*(M:ℝ)*Real.exp (-m/(4000000*(L/m)^2)) at hp
  rw [hid] at hp
  exact hp

theorem fixed_cubic_phase_input :
    FixedCubicPhaseInput 5 (1/4000000) (Real.exp ((10:ℝ)^21)) := by
  intro t ht j _hj hMt hcut K hK
  exact prefix_bound (2^j) K t (by positivity) ht hMt hcut hK

theorem literal_item1_unconditional :
    ∀ᶠ X : ℝ in atTop,
      (∫ x in Icc X (2*X), CancellationTransferCenter.sourceResidualAbs X x
        (x*(X^((101:ℝ)/1000)/2)/X))/X ≤ 1/(Real.log X)^2 := by
  exact literal_item1_of_fixed_cubic 5 (1/4000000) (Real.exp ((10:ℝ)^21))
    (by norm_num) (by norm_num) fixed_cubic_phase_input

end Item1ParameterEndpoint

run_cmd do
  for target in [``Item1ParameterEndpoint.cutoff_forces_eight,
      ``Item1ParameterEndpoint.exponent_identity,
      ``Item1ParameterEndpoint.prefix_bound,
      ``Item1ParameterEndpoint.fixed_cubic_phase_input,
      ``Item1ParameterEndpoint.literal_item1_unconditional] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "PARAMETER ENDPOINT: 5 standard-axiom theorem guards passed."

#check Item1ParameterEndpoint.fixed_cubic_phase_input
#check Item1ParameterEndpoint.literal_item1_unconditional
