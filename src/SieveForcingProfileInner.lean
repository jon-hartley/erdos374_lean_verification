import SieveStoppingSharpForcing
import PrimeEulerWeightedTransfer

/-! The rejected inner prime cutoff remains dependent on the outer prime.
Only the dimension-one error is made uniform over the parent interval. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open scoped BigOperators
open Real SieveStoppingExpansion SieveStoppingTwoStep SieveStoppingForcing PrimeEulerLogBounds

namespace SieveForcingProfileInner

def test (A x : ℝ) : ℝ := 3 * log x / (A - log x) - 1

def profile (r : ℝ) : ℝ := 1 - 4/r + (3/r)*log (3/(r-1))

theorem inner_profile_bound (T z : ℝ) (p : ℕ) (hz : 64 ≤ z)
    (hT : z^2 ≤ T) (hp : p ∈ SieveSmallWeights.pool z)
    (ha : root T 4 ≤ (p:ℝ)) :
    innerRejected T p ≤ test (log T) (p:ℝ) + 9*epsilon z := by
  have hz0 : 0 < z := by linarith
  have hT0 : 0 < T := (pow_pos hz0 2).trans_le hT
  obtain ⟨hpp, hpz⟩ := (SieveSmallWeights.mem_pool z p).mp hp
  have hp0 : (0:ℝ) < p := by exact_mod_cast hpp.pos
  have hp2 : (2:ℝ) ≤ p := by exact_mod_cast hpp.two_le
  have hlz : 0 < log z := log_pos (by linarith)
  have hlp : 0 < log (p:ℝ) := log_pos (by linarith)
  have hlpz : log (p:ℝ) ≤ log z := log_le_log hp0 hpz.le
  have hlT : 2*log z ≤ log T := by
    have hh := log_le_log (pow_pos hz0 2) hT
    simpa only [log_pow, Nat.cast_ofNat] using hh
  have hden : log z ≤ log T - log (p:ℝ) := by linarith
  have hden0 : 0 < log T - log (p:ℝ) := hlz.trans_le hden
  have hc2 : 2 ≤ root (T/(p:ℝ)) 3 := by
    apply root_lower 2 _ 3 (by norm_num) (by norm_num)
    apply (le_div_iff₀ hp0).mpr
    have hh := (div_le_div_of_nonneg_left hT0.le hp0 hpz.le)
    have hTz : z ≤ T/z := (le_div_iff₀ hz0).mpr (by nlinarith)
    have hh8 : (8:ℝ) ≤ T/(p:ℝ) := by linarith
    exact (le_div_iff₀ hp0).mp (by norm_num at hh8 ⊢; exact hh8)
  have hcp : root (T/(p:ℝ)) 3 ≤ (p:ℝ) := by
    have hh := log_le_log (exp_pos (log T/4)) ha
    change log (exp (log T/(4:ℝ))) ≤ log (p:ℝ) at hh
    rw [log_exp] at hh
    unfold root
    rw [log_div hT0.ne' hp0.ne', ← exp_log hp0]
    apply exp_le_exp.mpr
    norm_num
    linarith
  have hraw := (SieveStoppingSharpForcing.innerRejected_le_interval T (p:ℝ) p
    hT0 hp0 hp0 le_rfl).trans
      (PrimeEulerMass.normalized_interval_bound _ _ hc2 hcp)
  have heq : log (p:ℝ)/log (root (T/(p:ℝ)) 3)-1+
      PrimeEulerDimensionOne.errorConstant*log (p:ℝ)/(log (root (T/(p:ℝ)) 3))^2 =
      test (log T) (p:ℝ)+
        9*(PrimeEulerDimensionOne.errorConstant*log (p:ℝ)/(log T-log (p:ℝ))^2) := by
    simp only [root, log_exp, Nat.cast_ofNat, log_div hT0.ne' hp0.ne', test]
    field_simp
    ring
  have herr : PrimeEulerDimensionOne.errorConstant*log (p:ℝ)/(log T-log (p:ℝ))^2 ≤
      epsilon z := by
    unfold epsilon
    apply (div_le_iff₀ (sq_pos_of_pos hden0)).mpr
    have hs : (log z)^2 ≤ (log T-log (p:ℝ))^2 := pow_le_pow_left₀ hlz.le hden 2
    have hmul := mul_le_mul_of_nonneg_left hs
      (div_nonneg PrimeEulerDimensionOne.errorConstant_pos.le hlz.le)
    have hc : (PrimeEulerDimensionOne.errorConstant/log z)*(log z)^2 =
        PrimeEulerDimensionOne.errorConstant*log z := by field_simp
    rw [hc] at hmul
    exact (mul_le_mul_of_nonneg_left hlpz PrimeEulerDimensionOne.errorConstant_pos.le).trans hmul
  rw [heq] at hraw
  linarith

run_cmd do
  for decl in [``inner_profile_bound] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "PRIME-DEPENDENT INNER FORCING PROFILE CHECKED"

end SieveForcingProfileInner
end
