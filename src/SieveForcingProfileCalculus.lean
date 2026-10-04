import SieveForcingProfileInner

/-! Exact calculus for the increasing forcing test on its relevant interval. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Real Set MeasureTheory

namespace SieveForcingProfileCalculus
open SieveForcingProfileInner

def derivative (A x : ℝ) : ℝ := 3*A/(x*(A-log x)^2)

def primitive (A B x : ℝ) : ℝ :=
  test A x*(B/log x-1)+B*((3/A)*(log (log x)-log (A-log x))+1/log x)

theorem test_hasDerivAt (A x : ℝ) (hx : 1 < x) (hA : log x < A) :
    HasDerivAt (test A) (derivative A x) x := by
  have hx0 : x ≠ 0 := by linarith
  have hd := hasDerivAt_log hx0
  have hden : A-log x ≠ 0 := by linarith
  have hh := ((hd.const_mul 3).div ((hasDerivAt_const x A).sub hd) hden).sub_const 1
  convert! hh using 1
  dsimp [derivative]
  field_simp
  ring

theorem primitive_hasDerivAt (A B x : ℝ) (hx : 1 < x) (hA : log x < A) :
    HasDerivAt (primitive A B) (derivative A x*(B/log x-1)) x := by
  have hx0 : x ≠ 0 := by linarith
  have hl : log x ≠ 0 := (log_pos hx).ne'
  have hden : A-log x ≠ 0 := by linarith
  have hA0 : A ≠ 0 := by linarith [log_pos hx]
  have hd := hasDerivAt_log hx0
  have h1 := (test_hasDerivAt A x hx hA).mul
    (((hasDerivAt_const x B).div hd hl).sub_const 1)
  have h2 := (((hd.log hl).sub (((hasDerivAt_const x A).sub hd).log hden)).const_mul
    (3/A)).add ((hasDerivAt_const x (1:ℝ)).div hd hl)
  convert! h1.add (h2.const_mul B) using 1
  dsimp [derivative, test]
  field_simp
  ring

theorem test_continuousOn (A a b : ℝ) (ha : 2 ≤ a) (hA : log b < A) :
    ContinuousOn (test A) (Icc a b) := by
  intro x hx
  apply (test_hasDerivAt A x (by linarith [hx.1]) ?_).continuousAt.continuousWithinAt
  exact (log_le_log (by linarith [hx.1] : 0 < x) hx.2).trans_lt hA

theorem derivative_continuousOn (A a b : ℝ) (ha : 2 ≤ a) (hA : log b < A) :
    ContinuousOn (derivative A) (Icc a b) := by
  have hx0 : ∀ x ∈ Icc a b, x ≠ 0 := fun x hx => by linarith [hx.1]
  have hd : ∀ x ∈ Icc a b, A-log x ≠ 0 := by
    intro x hx
    have hh := (log_le_log (by linarith [hx.1] : 0 < x) hx.2).trans_lt hA
    linarith
  exact continuousOn_const.div
    (continuousOn_id.mul ((continuousOn_const.sub (continuousOn_id.log hx0)).pow 2))
    (fun x hx => mul_ne_zero (hx0 x hx) (pow_ne_zero 2 (hd x hx)))

theorem derivative_nonneg (A x : ℝ) (hA : 0 ≤ A) (hx : 0 ≤ x) :
    0 ≤ derivative A x := by unfold derivative; positivity

theorem test_lower_endpoint (A a : ℝ) (ha : 1 < a) (hla : log a=A/4) :
    test A a = 0 := by
  have hA : A ≠ 0 := by linarith [log_pos ha]
  unfold test
  rw [hla]
  field_simp
  ring

theorem test_le_two (A x : ℝ) (hx : 1 < x) (hA : 2*log x ≤ A) :
    test A x ≤ 2 := by
  have hd : 0 < A-log x := by linarith [log_pos hx]
  unfold test
  have hh : 3*log x/(A-log x) ≤ 3 := (div_le_iff₀ hd).mpr (by linarith)
  linarith

theorem integral_derivative (A a b : ℝ) (ha : 2 ≤ a) (hab : a ≤ b)
    (hA : log b < A) :
    (∫ x in a..b, derivative A x) = test A b-test A a := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
    (test_continuousOn A a b ha hA)
  · intro x hx
    exact test_hasDerivAt A x (by linarith [hx.1])
      ((log_le_log (by linarith [hx.1] : 0 < x) hx.2.le).trans_lt hA)
  · rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
    exact (derivative_continuousOn A a b ha hA).integrableOn_Icc

theorem primitive_difference (A a b : ℝ) (ha : 2 ≤ a) (hab : a ≤ b)
    (hA : log b < A) (hla : log a=A/4) :
    primitive A (log b) b-primitive A (log b) a=profile (A/log b) := by
  have hlb : 0 < log b := log_pos (by linarith)
  have hla0 : 0 < log a := log_pos (by linarith)
  have hA0 : 0 < A := by linarith
  have hAd : 0 < A-log b := by linarith
  have hAa : 0 < A-log a := by linarith
  have ht := test_lower_endpoint A a (by linarith) hla
  have hlog : (log (log b)-log (A-log b))-(log (log a)-log (A-log a)) =
      log (3/(A/log b-1)) := by
    rw [← log_div hlb.ne' hAd.ne', ← log_div hla0.ne' hAa.ne',
      ← log_div (div_pos hlb hAd).ne' (div_pos hla0 hAa).ne']
    congr 1
    rw [hla]
    field_simp
    ring
  unfold primitive
  rw [ht, zero_mul, div_self hlb.ne']
  simp only [sub_self, mul_zero, zero_add]
  calc
    _ = (3*log b/A)*((log (log b)-log (A-log b))-
        (log (log a)-log (A-log a)))+1-log b/log a := by
      field_simp
      ring
    _ = _ := by
      rw [hlog, hla]
      unfold profile
      field_simp
      ring

theorem ideal_integral (A a b : ℝ) (ha : 2 ≤ a) (hab : a ≤ b)
    (hA : log b < A) (hla : log a=A/4) :
    (∫ x in a..b, derivative A x*(log b/log x-1))=profile (A/log b) := by
  have hc : ContinuousOn (primitive A (log b)) (Icc a b) := by
    intro x hx
    exact (primitive_hasDerivAt A (log b) x (by linarith [hx.1])
      ((log_le_log (by linarith [hx.1] : 0 < x) hx.2).trans_lt hA)).continuousAt.continuousWithinAt
  have hi : IntervalIntegrable (fun x => derivative A x*(log b/log x-1)) volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
    apply ContinuousOn.integrableOn_Icc
    exact (derivative_continuousOn A a b ha hA).mul
      ((continuousOn_const.div
        (continuousOn_id.log (fun x hx => by change x ≠ 0; linarith [hx.1]))
        (fun x hx => (log_pos (by change 1 < x; linarith [hx.1])).ne')).sub continuousOn_const)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hc
    (fun x hx => primitive_hasDerivAt A (log b) x (by linarith [hx.1])
      ((log_le_log (by linarith [hx.1] : 0 < x) hx.2.le).trans_lt hA)) hi]
  exact primitive_difference A a b ha hab hA hla

run_cmd do
  for decl in [``test_hasDerivAt, ``primitive_hasDerivAt, ``test_continuousOn,
    ``derivative_continuousOn, ``derivative_nonneg, ``test_lower_endpoint,
    ``test_le_two, ``integral_derivative, ``primitive_difference, ``ideal_integral] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "EXACT CONTINUOUS FORCING PROFILE CHECKED"

end SieveForcingProfileCalculus
end
