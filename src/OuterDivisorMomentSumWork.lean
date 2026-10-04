import OuterCenteredBlockMomentWork

/-! Summing a dyadic family of reciprocal-normalized divisor modes preserves
a uniform square-mean budget. Coefficients and pair masks may depend on d. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace OuterDivisorMomentSumWork

theorem sum_energy (D : Finset ℕ) (N : ℕ) (a b E : ℝ)
    (c F : ℕ→ℝ→ℂ) (hN : 1≤N) (hE : 0≤E)
    (hcard : D.card≤N) (hc : ∀d∈D,Continuous (c d)) (hF : ∀d∈D,Continuous (F d))
    (hcap : ∀d∈D,∀t∈Icc a b,‖c d t‖≤(N:ℝ)⁻¹)
    (hmean : ∀d∈D,(∫t in Icc a b,‖F d t‖^2)≤E) :
    (∫t in Icc a b,‖∑d∈D,c d t*F d t‖^2)≤E := by
  have hNp : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hcardR : (D.card:ℝ)≤N := by exact_mod_cast hcard
  have hpt (t : ℝ) (ht : t∈Icc a b) :
      ‖∑d∈D,c d t*F d t‖^2 ≤ (D.card:ℝ)*(N:ℝ)⁻¹^2*(∑d∈D,‖F d t‖^2) := by
    apply (Erdos374.ExponentialSum151.norm_sum_sq_le_card_energy D (fun d => c d t*F d t)).trans
    calc
      _ ≤ (D.card:ℝ)*(∑d∈D,(N:ℝ)⁻¹^2*‖F d t‖^2) := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        apply Finset.sum_le_sum
        intro d hd
        rw [norm_mul,mul_pow]
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (norm_nonneg _) (hcap d hd t ht) 2) (sq_nonneg _)
      _ = _ := by rw [←Finset.mul_sum]; ring
  have hsum : Continuous (fun t => ∑d∈D,c d t*F d t) :=
    continuous_finsetSum D (fun d hd => (hc d hd).mul (hF d hd))
  have hcont : Continuous (fun t => (D.card:ℝ)*(N:ℝ)⁻¹^2*(∑d∈D,‖F d t‖^2)) :=
    continuous_const.mul (continuous_finsetSum D (fun d hd => (hF d hd).norm.pow 2))
  have hh := setIntegral_mono_on (hsum.norm.pow 2).integrableOn_Icc (hcont.integrableOn_Icc (μ:=volume))
    measurableSet_Icc hpt
  have hFI : ∀d∈D, IntegrableOn (fun t => ‖F d t‖^2) (Icc a b) volume :=
    fun d hd => ((hF d hd).norm.pow 2).integrableOn_Icc
  rw [integral_const_mul,integral_finsetSum D hFI] at hh
  have hb : (∑d∈D,(∫t in Icc a b,‖F d t‖^2))≤(D.card:ℝ)*E := by
    simpa using Finset.sum_le_sum hmean
  have hratio : (D.card:ℝ)*(N:ℝ)⁻¹ ≤ 1 := by
    calc
      _ ≤ (N:ℝ)*(N:ℝ)⁻¹ := mul_le_mul_of_nonneg_right hcardR (by positivity)
      _ = 1 := mul_inv_cancel₀ hNp.ne'
  calc
    _ ≤ (D.card:ℝ)*(N:ℝ)⁻¹^2*(∑d∈D,(∫t in Icc a b,‖F d t‖^2)) := hh
    _ ≤ (D.card:ℝ)*(N:ℝ)⁻¹^2*((D.card:ℝ)*E) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = ((D.card:ℝ)*(N:ℝ)⁻¹)^2*E := by ring
    _ ≤ E := by
      have hsq := pow_le_pow_left₀ (by positivity : 0≤(D.card:ℝ)*(N:ℝ)⁻¹) hratio 2
      simpa using mul_le_mul_of_nonneg_right hsq hE

run_cmd do
  for decl in [``sum_energy] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end OuterDivisorMomentSumWork
