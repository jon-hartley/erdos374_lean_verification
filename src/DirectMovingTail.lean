import DirectMovingSawtoothCoefficients

/-! A width-independent anchored Fourier residual, with an exact two-point
identity and a quantitative tail on every physical interval. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open MeasureTheory Set intervalIntegral
open scoped Real ENNReal BigOperators

namespace DirectMovingTail
open PairFourier DirectMovingSawtooth

def anchoredProjection (n : ℕ) (hn : 0<n) (F : ℕ) (x : ℝ) : ℂ :=
  projection n (by exact_mod_cast hn) (sawtooth n) (hardModes n F) x

def residual (n : ℕ) (hn : 0<n) (F : ℕ) (x : ℝ) : ℂ :=
  sawtooth n x - anchoredProjection n hn F x

theorem residual_measurable (n : ℕ) (hn : 0<n) (F : ℕ) :
    Measurable (residual n hn F) := by
  exact (DirectMovingSawtooth.measurable n).sub (projection_continuous _ _ _ _).measurable

theorem phase_sub (n : ℕ) (k : ℤ) (x h : ℝ) :
    phase n k (x-h) = phase n (-k) h * phase n k x := by
  simp only [phase, fourier_coe_apply]
  rw [←Complex.exp_add]
  congr 1
  push_cast
  ring

theorem hardProjection_eq_difference (n : ℕ) (hn : 0<n) (F : ℕ) (h x : ℝ) :
    hardProjection n hn h F x =
      anchoredProjection n hn F x - anchoredProjection n hn F (x-h) := by
  unfold hardProjection anchoredProjection projection
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : k=0
  · subst k
    rw [PairFourier.coefficient_zero hn h, DirectMovingSawtooth.coefficient_zero n hn]
    simp
  · rw [PairFourier.coefficient_ne_zero hn h hk,
      DirectMovingSawtooth.coefficient_ne_zero n hn k hk, phase_sub]
    ring

theorem singleError_eq_difference (n : ℕ) (hn : 0<n) (F : ℕ) (h x : ℝ) :
    PairFourier.discrepancy n h x - hardProjection n hn h F x =
      residual n hn F x - residual n hn F (x-h) := by
  rw [DirectMovingSawtooth.discrepancy_eq, hardProjection_eq_difference]
  unfold residual
  ring

theorem residual_periodic (n : ℕ) (hn : 0<n) (F : ℕ) :
    Function.Periodic (residual n hn F) (n:ℝ) := by
  intro x
  unfold residual anchoredProjection
  rw [DirectMovingSawtooth.periodic n hn, projection_periodic]

theorem residual_memLp (n : ℕ) (hn : 0<n) (F : ℕ) (a b : ℝ) (p : ℝ≥0∞) :
    MemLp (residual n hn F) p (volume.restrict (Ioc a b)) := by
  exact (DirectMovingSawtooth.memLp n a b p).sub (projection_memLp _ _ _ _ a b p)

theorem square_periodic (n : ℕ) (hn : 0<n) (F : ℕ) :
    Function.Periodic (fun x => ‖residual n hn F x‖^2) (n:ℝ) := by
  intro x
  dsimp only
  rw [residual_periodic n hn F]

theorem square_integrable (n : ℕ) (hn : 0<n) (F : ℕ) (a b : ℝ) :
    IntervalIntegrable (fun x => ‖residual n hn F x‖^2) volume a b := by
  constructor <;> exact (residual_memLp n hn F _ _ 2).integrable_norm_pow (by norm_num)

theorem period_bound (n : ℕ) (hn : 0<n) (F : ℕ) (hF : 0<F) :
    (∫x in (0:ℝ)..n, ‖residual n hn F x‖^2) ≤ 4/(F:ℝ) := by
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have hF0 : (F:ℝ)≠0 := by exact_mod_cast hF.ne'
  have hK : 1≤n*F := Nat.succ_le_iff.mpr (Nat.mul_pos hn hF)
  have hs := residual_coefficients_summable (n:ℝ) hnR (sawtooth n)
    (DirectMovingSawtooth.memLp n 0 n 2) (hardModes n F)
  have ht := PairReciprocalTail.summable_tail (n*F) hK
  have hcomp : (∑' k:ℤ, if k∈hardModes n F then 0 else
      ‖fourierCoeffOn hnR (sawtooth n) k‖^2) ≤
      ∑' k:ℤ, PairReciprocalTail.fourierTail (n*F) k := by
    apply Summable.tsum_le_tsum _ hs ht
    intro k
    by_cases hk : k∈hardModes n F
    · rw [ite_eq_left hk]
      unfold PairReciprocalTail.fourierTail
      split_ifs <;> positivity
    · have hkm : ((n*F:ℕ):ℤ) < |k| := lt_of_not_ge ((mem_hardModes n F k).not.mp hk)
      have hk0 : k≠0 := by
        intro he
        subst k
        have := Int.natCast_nonneg (n*F)
        simp only [abs_zero] at hkm
        omega
      simp only [ite_eq_right hk, PairReciprocalTail.fourierTail, ite_eq_left hkm]
      exact pow_le_pow_left₀ (norm_nonneg _)
        (DirectMovingSawtooth.coefficient_norm_le n hn k hk0) 2
  have hb := hcomp.trans (PairReciprocalTail.tsum_tail_le_four (n*F) hK)
  rw [←residual_parseval (n:ℝ) hnR (sawtooth n)
    (DirectMovingSawtooth.memLp n 0 n 2) (hardModes n F)] at hb
  change (1/(n:ℝ))*(∫x in (0:ℝ)..n, ‖residual n hn F x‖^2) ≤ 4/(n*F:ℕ) at hb
  rw [one_div, ←div_eq_inv_mul] at hb
  calc
    _ ≤ (4/(n*F:ℕ))*(n:ℝ) := (div_le_iff₀ hnR).mp hb
    _ = _ := by push_cast; field_simp

theorem interval_bound (n : ℕ) (hn : 0<n) (F : ℕ) (hF : 0<F)
    (t T : ℝ) (hT : 0≤T) :
    (∫x in t..t+T, ‖residual n hn F x‖^2) ≤ (4/(F:ℝ))*(T/n+1) := by
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  calc
    _ ≤ (T/n+1)*(∫x in (0:ℝ)..n, ‖residual n hn F x‖^2) :=
      PairCommonPeriod.integral_le_cover _ n hnR (square_periodic n hn F)
        (square_integrable n hn F) (fun _ => sq_nonneg _) t T hT
    _ ≤ (T/n+1)*(4/(F:ℝ)) :=
      mul_le_mul_of_nonneg_left (period_bound n hn F hF) (by positivity)
    _ = _ := mul_comm _ _

run_cmd do
  for decl in [``anchoredProjection, ``residual, ``residual_measurable,
      ``phase_sub, ``hardProjection_eq_difference, ``singleError_eq_difference,
      ``residual_periodic, ``residual_memLp, ``square_periodic, ``square_integrable,
      ``period_bound, ``interval_bound] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ANCHORED SAWTOOTH FOURIER TAIL AND EXACT TWO-POINT ERROR PASSED"

end DirectMovingTail
