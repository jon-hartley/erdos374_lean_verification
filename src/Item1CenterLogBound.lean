import Item1ZeroFreeDisk
import Mathlib.Analysis.Calculus.LogDeriv

/-!
A center estimate for the remaining nonzero factor AFTER its
zeros have been removed. It must NOT be applied to a disk containing a zero
of the original function. The normalized logarithm is constructed by the
retained disk-primitive proof body; it is not the principal complex log.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
noncomputable section
open Set Metric Complex
namespace Item1CenterLogBound

/-- The center estimate costs one inverse radius, not two margin losses. -/
theorem center_logDeriv_bound (q : ℂ → ℂ) (R M : ℝ)
    (hR : 0 < R) (hM : 0 < M)
    (hq : DifferentiableOn ℂ q (ball 0 R))
    (hn : ∀ z ∈ ball (0:ℂ) R, q z ≠ 0)
    (hb : ∀ z ∈ ball (0:ℂ) R, ‖q z‖ ≤ Real.exp M * ‖q 0‖) :
    ‖logDeriv q (0:ℂ)‖ ≤ 4*M/R := by
  have h0 : (0:ℂ) ∈ ball 0 R := by simpa using hR
  have hq0 : 0 < ‖q 0‖ := norm_pos_iff.mpr (hn 0 h0)
  obtain ⟨g,hg0,hg⟩ := Item1ZeroFreeDisk.normalized_logarithm q 0 R hR hq hn
  have hgd : DifferentiableOn ℂ g (ball (0:ℂ) R) :=
    fun z hz => (hg z hz).1.differentiableAt.differentiableWithinAt
  have hre (z : ℂ) (hz : z ∈ ball (0:ℂ) R) : (g z).re ≤ M := by
    have he := congrArg norm (hg z hz).2
    rw [norm_mul,Complex.norm_exp] at he
    have hh : Real.exp (g z).re * ‖q 0‖ ≤ Real.exp M * ‖q 0‖ := by
      rw [←he]; exact hb z hz
    exact Real.exp_le_exp.mp (le_of_mul_le_mul_right hh hq0)
  have hsub : closedBall (0:ℂ) (R/2) ⊆ ball 0 R := by
    intro z hz
    rw [mem_ball,dist_eq_norm]
    have hz' : ‖z‖ ≤ R/2 := by simpa [mem_closedBall,dist_eq_norm] using hz
    simpa using lt_of_le_of_lt hz' (by linarith : R/2 < R)
  have hboundary (z : ℂ) (hz : z ∈ sphere (0:ℂ) (R/2)) : ‖g z‖ ≤ 2*M := by
    have hnz : ‖z‖ = R/2 := by simpa [mem_sphere,dist_eq_norm] using hz
    have hh := Item1ZeroFreeDisk.translated_borel g 0 z R M hR hM hgd hg0 hre
      (by simp only [sub_zero]; rw [hnz]; linarith)
    simp only [sub_zero] at hh
    rw [hnz] at hh
    convert hh using 1 <;> field_simp [hR.ne'] <;> ring
  have hdc : DiffContOnCl ℂ g (ball (0:ℂ) (R/2)) := by
    apply DiffContOnCl.mk_ball
    · exact hgd.mono (ball_subset_closedBall.trans hsub)
    · exact (hgd.mono hsub).continuousOn
  have hh := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    (show 0 < R/2 by positivity) hdc hboundary
  rw [(hg 0 h0).1.deriv] at hh
  change ‖logDeriv q 0‖ ≤ 2*M/(R/2) at hh
  convert hh using 1 <;> field_simp [hR.ne'] <;> ring

end Item1CenterLogBound

run_cmd do
  for ax in (← Lean.collectAxioms ``Item1CenterLogBound.center_logDeriv_bound) do
    unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
      throwError "Unexpected axiom {ax} in Item1CenterLogBound.center_logDeriv_bound"

#print axioms Item1CenterLogBound.center_logDeriv_bound
