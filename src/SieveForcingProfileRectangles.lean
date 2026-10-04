import SieveForcingProfileTransfer
import SieveForcingProfileScalar

/-! Rational left rectangles for the actual forcing. Positive-part extension
handles the last cell, which may overshoot the end of the support. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open scoped BigOperators
open Real Set MeasureTheory SieveForcingProfileInner SieveForcingProfileScalar
  SieveStoppingTwoStep

namespace SieveForcingProfileRectangles

def positiveKernel (r v : ℝ) : ℝ := max 0 (kernel r v)
def rectangles (r h : ℝ) (N : ℕ) : ℝ :=
  h*∑ k ∈ Finset.range N, kernel r (1+(k:ℝ)*h)

theorem positiveKernel_continuousOn (r : ℝ) (hr : 2 ≤ r) :
    ContinuousOn (positiveKernel r) (Ici 1) := by
  have hd : ∀ v ∈ Ici (1:ℝ), r*v-1 ≠ 0 := by
    intro v hv
    change 1 ≤ v at hv
    have hr0 : 0 ≤ r := by linarith
    have hh : r ≤ r*v := by nlinarith
    linarith
  exact continuousOn_const.sup
    ((continuousOn_const.div ((continuousOn_const.mul continuousOn_id).sub continuousOn_const)
      hd).sub continuousOn_const)

theorem positiveKernel_antitoneOn (r : ℝ) (hr : 2 ≤ r) :
    AntitoneOn (positiveKernel r) (Ici 1) := by
  intro x hx y hy hxy
  exact max_le_max le_rfl (kernel_antitoneOn r hr hx hy hxy)

theorem kernel_parameter_le (r c v : ℝ) (hc : 2 ≤ c) (hcr : c ≤ r) (hv : 1 ≤ v) :
    kernel r v ≤ kernel c v := by
  have hc0 : 0 ≤ c := by linarith
  have hv0 : 0 ≤ v := by linarith
  have hd : 0 < c*v-1 := by nlinarith
  have hm : c*v-1 ≤ r*v-1 := by nlinarith
  exact sub_le_sub_right (div_le_div_of_nonneg_left (by norm_num) hd hm) 1

theorem positiveKernel_intervalIntegrable (r a b : ℝ) (hr : 2 ≤ r)
    (ha : 1 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (positiveKernel r) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
  exact ((positiveKernel_continuousOn r hr).mono (fun x hx => ha.trans hx.1)).integrableOn_Icc

theorem positive_integral_eq (r : ℝ) (hr2 : 2 ≤ r) (hr4 : r ≤ 4) :
    (∫ v in (1:ℝ)..(4/r), positiveKernel r v)=profile r := by
  rw [← profile_integral r hr2 hr4]
  apply intervalIntegral.integral_congr
  intro v hv
  rw [uIcc_of_le ((le_div_iff₀ (by linarith : 0 < r)).mpr (by linarith))] at hv
  exact max_eq_right (kernel_nonneg r v hr2 hv)

theorem profile_le_positive_rectangles (r h : ℝ) (N : ℕ) (hr2 : 2 ≤ r)
    (hr4 : r ≤ 4) (hh : 0 ≤ h) (hcover : 4/r ≤ 1+(N:ℝ)*h) :
    profile r ≤ h*∑ k ∈ Finset.range N, positiveKernel r (1+(k:ℝ)*h) := by
  have hab : 1 ≤ 4/r := (le_div_iff₀ (by linarith : 0 < r)).mpr (by linarith)
  have hend : 1 ≤ 1+(N:ℝ)*h := by nlinarith [Nat.cast_nonneg (α := ℝ) N]
  have hmono := intervalIntegral.integral_mono_interval (f := positiveKernel r)
    (le_refl (1:ℝ)) hab hcover
    (Filter.Eventually.of_forall (fun v => le_max_left 0 (kernel r v)))
    (positiveKernel_intervalIntegrable r 1 (1+(N:ℝ)*h) hr2 le_rfl hend)
  rw [positive_integral_eq r hr2 hr4] at hmono
  have hcell (k : ℕ) : IntervalIntegrable (positiveKernel r) volume
      (1+(k:ℝ)*h) (1+((k+1:ℕ):ℝ)*h) := by
    apply positiveKernel_intervalIntegrable r _ _ hr2
    · nlinarith [Nat.cast_nonneg (α := ℝ) k]
    · push_cast
      nlinarith
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun k : ℕ => 1+(k:ℝ)*h) (n := N) (fun k _ => hcell k)
  simp only [Nat.cast_zero, zero_mul, add_zero] at hsum
  rw [← hsum] at hmono
  apply hmono.trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k _hk
  have hstep : 1+(k:ℝ)*h ≤ 1+((k+1:ℕ):ℝ)*h := by push_cast; nlinarith
  have hleft : 1 ≤ 1+(k:ℝ)*h := by nlinarith [Nat.cast_nonneg (α := ℝ) k]
  have hc := intervalIntegral.integral_mono_on hstep (hcell k) intervalIntegrable_const
    (fun v hv => positiveKernel_antitoneOn r hr2 hleft (hleft.trans hv.1) hv.1)
  have heq : (∫ v in (1+(k:ℝ)*h)..(1+((k+1:ℕ):ℝ)*h),
      positiveKernel r (1+(k:ℝ)*h)) = h*positiveKernel r (1+(k:ℝ)*h) := by
    rw [intervalIntegral.integral_const]
    simp only [smul_eq_mul, Nat.cast_add, Nat.cast_one]
    ring
  exact hc.trans_eq heq

theorem profile_le_rectangles_of_lower (r c h : ℝ) (N : ℕ) (hc : 2 ≤ c)
    (hcr : c ≤ r) (hr4 : r ≤ 4) (hh : 0 ≤ h)
    (hcover : 4/c ≤ 1+(N:ℝ)*h)
    (hlast : ∀ k < N, 1+(k:ℝ)*h ≤ 4/c) :
    profile r ≤ rectangles c h N := by
  have hr2 := hc.trans hcr
  have hrcover : 4/r ≤ 1+(N:ℝ)*h :=
    (div_le_div_of_nonneg_left (by norm_num) (by linarith : 0 < c) hcr).trans hcover
  apply (profile_le_positive_rectangles r h N hr2 hr4 hh hrcover).trans
  apply mul_le_mul_of_nonneg_left _ hh
  apply Finset.sum_le_sum
  intro k hk
  have hv : 1 ≤ 1+(k:ℝ)*h := by nlinarith [Nat.cast_nonneg (α := ℝ) k]
  have hk0 := kernel_nonneg c (1+(k:ℝ)*h) hc ⟨hv, hlast k (Finset.mem_range.mp hk)⟩
  exact max_le hk0 (kernel_parameter_le r c _ hc hcr hv)

theorem rectangles_nonneg (c h : ℝ) (N : ℕ) (hc : 2 ≤ c) (hh : 0 ≤ h)
    (hlast : ∀ k < N, 1+(k:ℝ)*h ≤ 4/c) :
    0 ≤ rectangles c h N := by
  apply mul_nonneg hh
  apply Finset.sum_nonneg
  intro k hk
  exact kernel_nonneg c _ hc ⟨by nlinarith [Nat.cast_nonneg (α := ℝ) k],
    hlast k (Finset.mem_range.mp hk)⟩

theorem eventually_forcing_rectangles (c h : ℝ) (N : ℕ) (hc : 2 ≤ c) (hh : 0 ≤ h)
    (hcover : 4/c ≤ 1+(N:ℝ)*h)
    (hlast : ∀ k < N, 1+(k:ℝ)*h ≤ 4/c) (δ : ℝ) (hδ : 0 < δ) :
    ∃ Z : ℝ, 64 ≤ Z ∧ ∀ z T : ℝ, Z ≤ z → z^2 ≤ T → c ≤ log T/log z →
      forcing T z ≤ rectangles c h N+δ := by
  obtain ⟨Z, hZ, hb⟩ := SieveForcingProfileTransfer.eventually_forcing_profile δ hδ
  refine ⟨Z, hZ, ?_⟩
  intro z T hz hT hcr
  by_cases hT4 : z^4 ≤ T
  · rw [SieveStoppingForcing.forcing_eq_zero T z hT4]
    exact add_nonneg (rectangles_nonneg c h N hc hh hlast) hδ.le
  · have hz64 := hZ.trans hz
    have hr4 := (SieveStoppingSharpForcing.parameter_bounds T z (by linarith) hT
      (le_of_not_ge hT4)).2
    exact (hb z T hz hT (le_of_not_ge hT4)).trans
      (add_le_add (profile_le_rectangles_of_lower _ c h N hc hcr hr4 hh hcover hlast) le_rfl)

run_cmd do
  for decl in [``positiveKernel_continuousOn, ``positiveKernel_antitoneOn,
    ``kernel_parameter_le, ``positiveKernel_intervalIntegrable, ``positive_integral_eq,
    ``profile_le_positive_rectangles, ``profile_le_rectangles_of_lower,
    ``rectangles_nonneg, ``eventually_forcing_rectangles] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ACTUAL FORCING LEFT RECTANGLES INCLUDING LAST-CELL OVERSHOOT CHECKED"

end SieveForcingProfileRectangles
end
