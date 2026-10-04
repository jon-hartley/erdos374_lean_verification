import SieveForcingProfileCalculus

/-! Inverse-log-coordinate representation of the exact forcing profile.
It is suitable for finite monotone rectangle certificates. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Real Set MeasureTheory

namespace SieveForcingProfileScalar
open SieveForcingProfileInner

def kernel (r v : ℝ) : ℝ := 3/(r*v-1)-1

theorem kernel_nonneg (r v : ℝ) (hr : 2 ≤ r) (hv : v ∈ Icc 1 (4/r)) :
    0 ≤ kernel r v := by
  have hr0 : 0 < r := by linarith
  have hlow : 1 < r*v := by nlinarith [hv.1]
  have hhigh : r*v ≤ 4 := by
    have hh := (le_div_iff₀ hr0).mp hv.2
    nlinarith
  have hd : 0 < r*v-1 := by linarith
  unfold kernel
  have hh : 1 ≤ 3/(r*v-1) := (le_div_iff₀ hd).mpr (by linarith)
  linarith

theorem kernel_antitoneOn (r : ℝ) (hr : 2 ≤ r) :
    AntitoneOn (kernel r) (Ici 1) := by
  intro x hx y _hy hxy
  change 1 ≤ x at hx
  have hr0 : 0 ≤ r := by linarith
  have hx0 : 0 < r*x-1 := by nlinarith [hx]
  have hd : r*x-1 ≤ r*y-1 := by nlinarith
  exact sub_le_sub_right (div_le_div_of_nonneg_left (by norm_num) hx0 hd) 1

theorem profile_integral (r : ℝ) (hr2 : 2 ≤ r) (hr4 : r ≤ 4) :
    (∫ v in (1:ℝ)..(4/r), kernel r v)=profile r := by
  have hr0 : 0 < r := by linarith
  have hrr : r ≠ 0 := hr0.ne'
  have hab : 1 ≤ 4/r := (le_div_iff₀ hr0).mpr (by linarith)
  have hden : ∀ v ∈ Icc (1:ℝ) (4/r), r*v-1 ≠ 0 := by
    intro v hv
    have hrv : r ≤ r*v := by nlinarith [hv.1]
    linarith
  have hd : ∀ v ∈ Icc (1:ℝ) (4/r),
      HasDerivAt (fun x => (3/r)*log (r*x-1)-x) (kernel r v) v := by
    intro v hv
    have hh := ((((hasDerivAt_id v).const_mul r).sub_const 1).log (hden v hv)).const_mul (3/r)
    convert! hh.sub (hasDerivAt_id v) using 1
    dsimp [kernel]
    field_simp
  have hi : IntervalIntegrable (kernel r) volume 1 (4/r) := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
    exact ((continuousOn_const.div
      ((continuousOn_const.mul continuousOn_id).sub continuousOn_const) hden).sub
      continuousOn_const).integrableOn_Icc
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
    (fun v hv => (hd v hv).continuousAt.continuousWithinAt)
    (fun v hv => hd v ⟨hv.1.le, hv.2.le⟩) hi]
  have hlog : log (3:ℝ)-log (r-1)=log (3/(r-1)) :=
    (log_div (by norm_num) (by linarith)).symm
  have hmul : r*(4/r)-1=3 := by field_simp; norm_num
  rw [hmul]
  simp only [mul_one]
  unfold profile
  rw [← hlog]
  ring

run_cmd do
  for decl in [``kernel_nonneg, ``kernel_antitoneOn, ``profile_integral] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "INVERSE-LOG FORCING PROFILE REPRESENTATION CHECKED"

end SieveForcingProfileScalar
end
