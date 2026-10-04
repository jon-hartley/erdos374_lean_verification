import PrimePowerLargeValuesWork
import PowerBandCountEnvelope

/-! Explicit eighth moment from a prime cap, with a logarithmic amplitude
band cost. The cap remains an application condition, not a new axiom. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace OuterPrimeEighthWork
open Erdos374.HarmanGram152 DyadicLevelParameters SupremumMoment MomentThreshold

def qConstant : ℝ := 516 * 3^3 * 8 * 27
def bConstant : ℝ := 516 * 1024^2 * 3^7 * 8 * 27^3
def Q (T : ℝ) : ℝ := qConstant * (1 + Real.log (T+1))
def B (N : ℕ) (T : ℝ) : ℝ :=
  bConstant * (1 + Real.log (T+1)) * T * (1 + Real.log (8*(N:ℝ)^3+1)) / (N:ℝ)^6
def M (N : ℕ) (T : ℝ) : ℝ :=
  27 * (T/(N:ℝ)^3 + 32*(1+3*Real.log (2*N)))
def bands (N : ℕ) : ℝ := (1+6/Real.log 2)*(1+Real.log N)

theorem quadratic_eq (N : ℕ) (T : ℝ) (hN : 1≤N) :
    quadratic (N^3) 3 T (PrimePowerLargeValuesWork.energyBudget 3 N 1)=Q T := by
  have hn : (N:ℝ)≠0 := by exact_mod_cast (show N≠0 by omega)
  unfold quadratic PrimePowerLargeValuesWork.energyBudget Q qConstant
  push_cast
  field_simp
  <;> ring

theorem sextic_eq (N : ℕ) (T : ℝ) (hN : 1≤N) :
    sextic (N^3) 3 T (PrimePowerLargeValuesWork.energyBudget 3 N 1)=B N T := by
  have hn : (N:ℝ)≠0 := by exact_mod_cast (show N≠0 by omega)
  unfold sextic PrimePowerLargeValuesWork.energyBudget B bConstant
  push_cast
  norm_num only [show (2:ℝ)^3=8 by norm_num]
  field_simp
  <;> ring

theorem B_lower (N : ℕ) (T : ℝ) (hN : 1≤N) (hT : 1≤T) :
    1/(N:ℝ)^6≤B N T := by
  have hn : (1:ℝ)≤N := by exact_mod_cast hN
  have hlT : 0≤Real.log (T+1) := Real.log_nonneg (by linarith)
  have hlN : 0≤Real.log (8*(N:ℝ)^3+1) := Real.log_nonneg (by have := pow_nonneg (Nat.cast_nonneg N : (0:ℝ)≤N) 3; nlinarith)
  have hc : (1:ℝ)≤bConstant := by norm_num [bConstant]
  unfold B
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hc (by linarith)) hT) (by linarith)

theorem band_bound (N : ℕ) (T μ U : ℝ) (hN : 1≤N) (hT : 1≤T)
    (hμ : 0<μ) (hμ1 : μ≤1) (hU : U≤1) :
    bandCountBound (cutoff (B N T) μ (8/3)) U ≤ bands N := by
  have hn : (1:ℝ)≤N := by exact_mod_cast hN
  have hnp : (0:ℝ)<N := by linarith
  have hrp : 0<1/(N:ℝ)^6 := by positivity
  have hr1 : 1/(N:ℝ)^6≤1 := (div_le_one (by positivity)).mpr (one_le_pow₀ hn)
  have hB := B_lower N T hN hT
  have hv : 1/(N:ℝ)^6≤cutoff (B N T) μ (8/3) := by
    unfold cutoff
    have hh : 1/(N:ℝ)^6≤B N T/μ :=
      hB.trans ((le_div_iff₀ hμ).mpr (mul_le_of_le_one_right (hrp.le.trans hB) hμ1))
    exact (Real.self_le_rpow_of_le_one hrp.le hr1 (by norm_num : 1/(6-(8/3:ℝ))≤1)).trans
      (Real.rpow_le_rpow hrp.le hh (by norm_num))
  have hh := BandCountEnvelope.logarithmic_bound_of_powers
    (cutoff (B N T) μ (8/3)) U (N:ℝ) 1 6 0 hn (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by simpa using hv) (by simpa using hU)
  simpa [bands] using hh

theorem eighth_bound (S : Finset ℕ) (N : ℕ) (coeff : ℕ→ℂ)
    (a T σ δ : ℝ) (hN : 1≤N) (hT : 1≤T) (hσ : 1≤σ)
    (hδ : 0<δ) (hδ1 : δ≤1)
    (hs : ∀p∈S,p.Prime ∧ N<p ∧ p≤2*N)
    (henergy : (∑p∈S,‖coeff p‖^2)≤N)
    (hcap : ∀t∈Icc a (a+T),‖verticalDirichlet152 S coeff σ t‖≤δ) :
    (∫t in Icc a (a+T),‖verticalDirichlet152 S coeff σ t‖^8) ≤
      (B N T/δ^2)^(1/5:ℝ)*M N T +
      bands N*(2:ℝ)^(8/3:ℝ)*(Q T*(2:ℝ)^(2/3:ℝ)+1)*δ^2 := by
  have hp : (δ^3)^((8/3:ℝ)-2)≤δ^2 := by
    rw [←Real.rpow_natCast_mul hδ.le]
    norm_num
  have hh := PrimePowerLargeValuesWork.integral_bound 3 (by norm_num) S N coeff
    a T 1 σ (δ^3) (8/3) (δ^2) hN (by linarith) (by norm_num) hσ (by positivity)
    (by norm_num) (by norm_num) (by positivity) hs (by simpa using henergy)
    (fun t ht => pow_le_pow_left₀ (norm_nonneg _) (hcap t ht) 3) hp
  dsimp only at hh
  rw [quadratic_eq N T hN,sextic_eq N T hN] at hh
  norm_num only [show (3:ℝ)*(8/3)=8 by norm_num, Real.rpow_natCast,
    show ((8/3:ℝ)-2)/(6-8/3)=1/5 by norm_num,
    show (8/3:ℝ)-2=2/3 by norm_num, Nat.cast_ofNat, one_pow, mul_one] at hh
  norm_cast at hh
  have hb := band_bound N T (δ^2) (δ^3) hN hT (by positivity)
    (pow_le_one₀ hδ.le hδ1) (pow_le_one₀ hδ.le hδ1)
  have hQ : 0≤Q T := by
    rw [←quadratic_eq N T hN]
    exact quadratic_nonnegative _ _ _ _ (by linarith)
      (PrimePowerLargeValuesWork.energyBudget_pos 3 N 1 (by norm_num) hN (by norm_num)).le
  apply hh.trans
  apply add_le_add
  · exact le_of_eq (by simp [M])
  · gcongr

run_cmd do
  for decl in [``quadratic_eq, ``sextic_eq, ``B_lower, ``band_bound, ``eighth_bound] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end OuterPrimeEighthWork
