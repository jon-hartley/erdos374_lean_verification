import PrimeEulerMass

/-! Actual prime masses on finite inverse-logarithmic intervals.
The leading term is the interval length in the inverse logarithmic variable;
all errors are explicit powers of K/log z. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open Real
open scoped BigOperators

namespace PrimeEulerProfileIntervals
open SieveStoppingExpansion PrimeEulerLogBounds

def cut (z x : ℝ) : ℝ := exp (log z/x)

def mass (a b z : ℝ) : ℝ :=
  ∑ p ∈ intervalPrimes a b, PrimeEulerMass.weight p/primeEuler z

def epsilon (z : ℝ) : ℝ := PrimeEulerDimensionOne.errorConstant/log z

theorem mass_nonneg (a b z : ℝ) : 0 ≤ mass a b z := by
  apply Finset.sum_nonneg
  intro p hp
  exact div_nonneg (PrimeEulerMass.weight_nonneg p) (SieveEulerRatio.euler_pos z).le

theorem mass_eq_zero (a b z : ℝ) (hba : b ≤ a) : mass a b z = 0 := by
  apply Finset.sum_eq_zero
  intro p hp
  obtain ⟨_, hpb, hap⟩ := (mem_intervalPrimes a b p).mp hp
  linarith

theorem mass_factor (a b z : ℝ) :
    mass a b z = (primeEuler b/primeEuler z)*mass a b b := by
  unfold mass
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hb := (SieveEulerRatio.euler_pos b).ne'
  field_simp

theorem mass_bound (a b z : ℝ) (ha : 2 ≤ a) (hab : a ≤ b) (hbz : b ≤ z) :
    mass a b z ≤
      (log z/log b)*(1+PrimeEulerDimensionOne.errorConstant/log b)*
        (log b/log a-1+PrimeEulerDimensionOne.errorConstant*log b/(log a)^2) := by
  have hlb : 0 < log b := log_pos (by linarith)
  have hlz : 0 < log z := log_pos (by linarith)
  have hK := PrimeEulerDimensionOne.errorConstant_pos
  rw [mass_factor]
  exact mul_le_mul (PrimeEulerDimensionOne.ratio_bound b z (ha.trans hab) hbz)
    (PrimeEulerMass.normalized_interval_bound a b ha hab) (mass_nonneg a b b)
    (by positivity)

theorem cut_mono (z l u : ℝ) (hz : 1 ≤ z) (hl : 0 < l) (hlu : l ≤ u) :
    cut z u ≤ cut z l := by
  apply exp_le_exp.mpr
  exact div_le_div_of_nonneg_left (log_nonneg hz) hl hlu

theorem cut_le (z x : ℝ) (hz : 1 ≤ z) (hx : 1 ≤ x) : cut z x ≤ z := by
  have hz0 : 0 < z := by linarith
  calc
    _ ≤ exp (log z) := exp_le_exp.mpr (by
      simpa only [div_one] using div_le_div_of_nonneg_left (log_nonneg hz)
        (by norm_num : (0:ℝ) < 1) hx)
    _ = z := exp_log hz0

theorem log_cut (z x : ℝ) : log (cut z x) = log z/x := log_exp _

theorem mass_bound_inverse (a b z : ℝ) (ha : 2 ≤ a) (hab : a ≤ b) (hbz : b ≤ z) :
    mass a b z ≤
      (log z/log a-log z/log b+epsilon z*(log z/log a)^2)*
        (1+epsilon z*(log z/log b)) := by
  have hla : log a ≠ 0 := (log_pos (by linarith : 1 < a)).ne'
  have hlb : log b ≠ 0 := (log_pos (by linarith : 1 < b)).ne'
  have hlz : log z ≠ 0 := (log_pos (by linarith : 1 < z)).ne'
  convert mass_bound a b z ha hab hbz using 1
  unfold epsilon
  field_simp

/-- This is an actual finite prime sum, with no prime-density hypothesis. -/
theorem inverse_bin_bound (z l u : ℝ) (hz : 2 ≤ z) (hl : 1 ≤ l)
    (hlu : l ≤ u) (ha : 2 ≤ cut z u) :
    mass (cut z u) (cut z l) z ≤
      ((u-l)+epsilon z*u^2)*(1+epsilon z*l) := by
  have hl0 : 0 < l := by linarith
  have hu0 : 0 < u := by linarith
  have hz1 : 1 ≤ z := by linarith
  have hh := mass_bound (cut z u) (cut z l) z ha
    (cut_mono z l u hz1 hl0 hlu) (cut_le z l hz1 hl)
  rw [log_cut, log_cut] at hh
  have hlz : log z ≠ 0 := (log_pos (by linarith : 1 < z)).ne'
  convert hh using 1
  unfold epsilon
  field_simp

run_cmd do
  for decl in [``cut, ``mass, ``epsilon, ``mass_nonneg, ``mass_eq_zero, ``mass_factor,
    ``mass_bound, ``cut_mono, ``cut_le, ``log_cut, ``mass_bound_inverse, ``inverse_bin_bound] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ACTUAL PRIME INVERSE-LOG INTERVAL MASS BOUND PASSED"

end PrimeEulerProfileIntervals
end
