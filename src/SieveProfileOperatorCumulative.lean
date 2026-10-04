import PrimeEulerProfileIntervals
import PrimeEulerAcceptedInner
import SieveStoppingTwoStep

/-! Exact finite-prime cumulative masses for the accepted child ratio.
The acceptance endpoint stays strict; the cumulative upper endpoint is closed. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Real
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace SieveProfileOperatorCumulative
open SieveStoppingExpansion PrimeEulerLogBounds PrimeEulerProfileIntervals
open PrimeEulerAcceptedInner

def lowerCut (T c : ℝ) : ℝ := exp (log T/(c+1))

def innerMass (T z c : ℝ) : ℝ :=
  ∑ q ∈ acceptedPrimes T z,
    if log (T/(q:ℝ))/log (q:ℝ) ≤ c then PrimeEulerMass.weight q/primeEuler z else 0

def shape (c s : ℝ) : ℝ := max 0 ((c+1-max 3 s)/s)

theorem child_ratio_le_iff (T q c : ℝ) (hT : 0 < T) (hq : 1 < q)
    (hc : 0 < c+1) :
    log (T/q)/log q ≤ c ↔ lowerCut T c ≤ q := by
  have hq0 : 0 < q := by linarith
  have hex : exp (log T/(c+1)) ≤ q ↔ log T/(c+1) ≤ log q := by
    rw [← log_le_log_iff (exp_pos _) hq0, log_exp]
  rw [div_le_iff₀ (log_pos hq), log_div hT.ne' hq0.ne', lowerCut,
    hex, div_le_iff₀ hc]
  constructor <;> intro h <;> nlinarith

theorem innerMass_eq_interval (T z c : ℝ) (hT : 0 < T) (hc : 0 < c+1) :
    innerMass T z c = mass (lowerCut T c) (cutoff T z) z := by
  have hs : (acceptedPrimes T z).filter
      (fun q : ℕ => log (T/(q:ℝ))/log (q:ℝ) ≤ c) =
      intervalPrimes (lowerCut T c) (cutoff T z) := by
    rw [acceptedPrimes_eq_pool T z hT]
    ext q
    simp only [Finset.mem_filter, SieveSmallWeights.mem_pool, mem_intervalPrimes]
    constructor
    · rintro ⟨⟨hq, hqb⟩, hqc⟩
      exact ⟨hq, hqb, (child_ratio_le_iff T q c hT (by exact_mod_cast hq.one_lt) hc).mp hqc⟩
    · rintro ⟨hq, hqb, hqa⟩
      exact ⟨⟨hq, hqb⟩, (child_ratio_le_iff T q c hT (by exact_mod_cast hq.one_lt) hc).mpr hqa⟩
  simpa only [innerMass, mass, Finset.sum_filter] using congrArg
    (fun S : Finset ℕ => ∑ q ∈ S, PrimeEulerMass.weight q/primeEuler z) hs

theorem innerMass_nonneg (T z c : ℝ) : 0 ≤ innerMass T z c := by
  apply Finset.sum_nonneg
  intro q hq
  split_ifs
  · exact div_nonneg (PrimeEulerMass.weight_nonneg q) (SieveEulerRatio.euler_pos z).le
  · exact le_rfl

theorem shape_nonneg (c s : ℝ) : 0 ≤ shape c s := le_max_left _ _

theorem innerMass_zero (T z c : ℝ) (hz : 2 ≤ z) (hT : z ≤ T)
    (hc : 2 ≤ c) (hs : c+1 ≤ log T/log z) : innerMass T z c = 0 := by
  have hz0 : 0 < z := by linarith
  have hT0 : 0 < T := by linarith
  have hza : z ≤ lowerCut T c := by
    apply (log_le_log_iff hz0 (exp_pos _)).mp
    rw [log_exp, le_div_iff₀ (by linarith : 0 < c+1)]
    have hh := (le_div_iff₀ (log_pos (by linarith : 1 < z))).mp hs
    nlinarith
  rw [innerMass_eq_interval T z c hT0 (by linarith)]
  exact mass_eq_zero _ _ _ ((cutoff_le T z).trans hza)

theorem log_ratio_cutoff (T z : ℝ) (hz : 2 ≤ z) (hT : z ≤ T) :
    log z/log (cutoff T z) = max 1 (3/(log T/log z)) := by
  have hz0 : 0 < z := by linarith
  have hlz : 0 < log z := log_pos (by linarith)
  have hT1 : 1 < T := by linarith
  have hlT : 0 < log T := log_pos hT1
  have hs0 : 0 < log T/log z := div_pos hlT hlz
  rw [log_cutoff T z hz0]
  by_cases hs : 3 ≤ log T/log z
  · have hh : log z ≤ log T/3 := by
      have hh := (le_div_iff₀ hlz).mp hs
      linarith
    rw [min_eq_left hh, div_self hlz.ne', max_eq_left]
    exact (div_le_iff₀ hs0).mpr (by linarith)
  · have hh : log T/3 ≤ log z := by
      have hh := (div_le_iff₀ hlz).mp (le_of_not_ge hs)
      linarith
    rw [min_eq_right hh, max_eq_right]
    · field_simp
    · exact (le_div_iff₀ hs0).mpr (by linarith)

theorem shape_eq_sub (c s : ℝ) (hc : 2 ≤ c) (hs : 1 ≤ s) (hsc : s ≤ c+1) :
    shape c s = (c+1)/s-max 1 (3/s) := by
  have hs0 : 0 < s := by linarith
  unfold shape
  by_cases hs3 : 3 ≤ s
  · have hy : max 1 (3/s) = 1 := max_eq_left ((div_le_iff₀ hs0).mpr (by linarith))
    rw [max_eq_right hs3, hy, max_eq_right (div_nonneg (by linarith) hs0.le)]
    field_simp
  · have hs3' : s ≤ 3 := le_of_not_ge hs3
    have hy : max 1 (3/s) = 3/s := max_eq_right ((le_div_iff₀ hs0).mpr (by linarith))
    rw [max_eq_left hs3', hy, max_eq_right (div_nonneg (by linarith) hs0.le)]
    ring

theorem innerMass_bound (T z c : ℝ) (hz : 2 ≤ z) (hT : z ≤ T) (hc : 2 ≤ c)
    (ha : 2 ≤ lowerCut T c) :
    innerMass T z c ≤
      (shape c (log T/log z)+epsilon z*(c+1)^2)*(1+3*epsilon z) := by
  have hz0 : 0 < z := by linarith
  have hT0 : 0 < T := by linarith
  have hlz : 0 < log z := log_pos (by linarith)
  have hlT : 0 < log T := log_pos (by linarith)
  have hs : 1 ≤ log T/log z := (le_div_iff₀ hlz).mpr (by
    simpa only [one_mul] using log_le_log hz0 hT)
  have hs0 : 0 < log T/log z := by linarith
  have hc0 : 0 < c+1 := by linarith
  have he : 0 ≤ epsilon z := div_nonneg PrimeEulerDimensionOne.errorConstant_pos.le hlz.le
  by_cases hsc : c+1 ≤ log T/log z
  · rw [innerMass_zero T z c hz hT hc hsc]
    exact mul_nonneg (add_nonneg (shape_nonneg _ _) (by positivity)) (by positivity)
  · have hsc' : log T/log z ≤ c+1 := le_of_not_ge hsc
    have haz : lowerCut T c ≤ z := by
      apply (log_le_log_iff (exp_pos _) hz0).mp
      rw [log_exp]
      apply (div_le_iff₀ hc0).mpr
      have hh := (div_le_iff₀ hlz).mp hsc'
      nlinarith
    have hac : lowerCut T c ≤ exp (log T/3) :=
      exp_le_exp.mpr (div_le_div_of_nonneg_left hlT.le (by norm_num) (by linarith))
    have hab : lowerCut T c ≤ cutoff T z := le_min haz hac
    have hraw := mass_bound_inverse (lowerCut T c) (cutoff T z) z ha hab (cutoff_le T z)
    have hloga : log z/log (lowerCut T c) = (c+1)/(log T/log z) := by
      simp only [lowerCut, log_exp]
      field_simp
    rw [← innerMass_eq_interval T z c hT0 hc0, hloga, log_ratio_cutoff T z hz hT,
      ← shape_eq_sub c (log T/log z) hc hs hsc'] at hraw
    have hx0 : 0 ≤ (c+1)/(log T/log z) := div_nonneg hc0.le hs0.le
    have hx : (c+1)/(log T/log z) ≤ c+1 := div_le_self hc0.le hs
    have hy : max 1 (3/(log T/log z)) ≤ 3 := max_le (by norm_num)
      (by simpa using div_le_self (by norm_num : (0:ℝ) ≤ 3) hs)
    have hx2 := pow_le_pow_left₀ hx0 hx 2
    exact hraw.trans (mul_le_mul
      (add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hx2 he))
      (by nlinarith)
      (by positivity : 0 ≤ 1+epsilon z*max 1 (3/(log T/log z)))
      (add_nonneg (shape_nonneg _ _) (by positivity)))

theorem shape_eq_min (c s : ℝ) (hs : 0 < s) :
    shape c s = max 0 (min ((c-2)/s) ((c+1)/s-1)) := by
  have hid : (c+1)/s-1 = (c+1-s)/s := by field_simp
  rw [hid]
  unfold shape
  by_cases hs3 : 3 ≤ s
  · rw [max_eq_right hs3, min_eq_right ((div_le_div_iff_of_pos_right hs).mpr (by linarith))]
  · have hs3' : s ≤ 3 := le_of_not_ge hs3
    rw [max_eq_left hs3', min_eq_left ((div_le_div_iff_of_pos_right hs).mpr (by linarith))]
    congr 2
    ring

theorem shape_antitone (c s t : ℝ) (hc : 2 ≤ c) (hs : 0 < s) (hst : s ≤ t) :
    shape c t ≤ shape c s := by
  rw [shape_eq_min c s hs, shape_eq_min c t (hs.trans_le hst)]
  apply max_le_max (le_refl _)
  exact min_le_min (div_le_div_of_nonneg_left (by linarith) hs hst)
    (sub_le_sub_right (div_le_div_of_nonneg_left (by linarith) hs hst) 1)

theorem shape_le (c s : ℝ) (hc : 2 ≤ c) (hs : 1 ≤ s) : shape c s ≤ c+1 := by
  rw [shape_eq_min c s (by linarith)]
  apply max_le (by linarith)
  exact (min_le_left _ _).trans ((div_le_self (by linarith : 0 ≤ c-2) hs).trans (by linarith))

run_cmd do
  for decl in [``lowerCut, ``innerMass, ``shape, ``child_ratio_le_iff,
    ``innerMass_eq_interval, ``innerMass_nonneg, ``shape_nonneg,
    ``innerMass_zero, ``log_ratio_cutoff, ``shape_eq_sub, ``innerMass_bound,
    ``shape_eq_min, ``shape_antitone, ``shape_le] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ACTUAL ACCEPTED CHILD CUMULATIVE INTERVAL IDENTITIES PASSED"
end SieveProfileOperatorCumulative
end
