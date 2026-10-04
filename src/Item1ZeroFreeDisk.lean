import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
A quantitative logarithmic-derivative lemma on
an actual zero-free disk. The logarithm is constructed from a primitive of
f'/f, not postulated and not identified with the principal logarithm.
No statement here proves a zero-free region for zeta.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
noncomputable section
open Set Metric Complex
namespace Item1ZeroFreeDisk

def logDerivative (f : ℂ → ℂ) (z : ℂ) : ℂ := deriv f z / f z

theorem logDerivative_differentiableOn (f : ℂ → ℂ) (c : ℂ) (R : ℝ)
    (hf : DifferentiableOn ℂ f (ball c R))
    (hn : ∀ z ∈ ball c R, f z ≠ 0) :
    DifferentiableOn ℂ (logDerivative f) (ball c R) := by
  exact (hf.deriv isOpen_ball).div hf hn

/-- A normalized holomorphic logarithm constructed by integrating f'/f.
The conclusion retains the derivative identity and the exact exponential
identity; there is no branch choice assumption in its arguments. -/
theorem normalized_logarithm (f : ℂ → ℂ) (c : ℂ) (R : ℝ) (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (ball c R))
    (hn : ∀ z ∈ ball c R, f z ≠ 0) :
    ∃ g : ℂ → ℂ, g c = 0 ∧ ∀ z ∈ ball c R,
      HasDerivAt g (logDerivative f z) z ∧
      f z = Complex.exp (g z) * f c := by
  obtain ⟨g,hgc,hg⟩ :=
    (logDerivative_differentiableOn f c R hf hn).isExactOn_ball.with_val_at c 0
  have hc : c ∈ ball c R := by simpa using hR
  let q : ℂ → ℂ := fun z => Complex.exp (-g z) * f z
  have hq (z : ℂ) (hz : z ∈ ball c R) : HasDerivAt q 0 z := by
    have hdf := (hf.differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt
    have h := ((hg z hz).neg.cexp).mul hdf
    have he : (Complex.exp (-g z) * (-logDerivative f z)) * f z +
        Complex.exp (-g z) * deriv f z = 0 := by
      dsimp [logDerivative]
      field_simp [hn z hz]
      <;> ring
    change HasDerivAt q
      ((Complex.exp (-g z) * (-logDerivative f z)) * f z +
        Complex.exp (-g z) * deriv f z) z at h
    rw [he] at h
    exact h
  have hqd : DifferentiableOn ℂ q (ball c R) :=
    fun z hz => (hq z hz).differentiableAt.differentiableWithinAt
  have hq0 : EqOn (deriv q) 0 (ball c R) := fun z hz => (hq z hz).deriv
  have hqc (z : ℂ) (hz : z ∈ ball c R) : q z = f c := by
    have he := isOpen_ball.is_const_of_deriv_eq_zero
      (convex_ball c R).isPreconnected hqd hq0 hz hc
    simpa [q,hgc] using he
  refine ⟨g,hgc,?_⟩
  intro z hz
  refine ⟨hg z hz,?_⟩
  calc
    f z = (Complex.exp (g z) * Complex.exp (-g z)) * f z := by
      rw [← Complex.exp_add]; simp
    _ = Complex.exp (g z) * q z := by dsimp [q]; ring
    _ = Complex.exp (g z) * f c := by rw [hqc z hz]

/-- Borel--Caratheodory after translation to the actual disk center. -/
theorem translated_borel (g : ℂ → ℂ) (c z : ℂ) (R M : ℝ)
    (hR : 0 < R) (hM : 0 < M)
    (hg : DifferentiableOn ℂ g (ball c R)) (hgc : g c = 0)
    (hre : ∀ w ∈ ball c R, (g w).re ≤ M) (hz : ‖z-c‖ < R) :
    ‖g z‖ ≤ 2*M*‖z-c‖/(R-‖z-c‖) := by
  let G : ℂ → ℂ := fun w => g (c+w)
  have hm (w : ℂ) (hw : w ∈ ball (0:ℂ) R) : c+w ∈ ball c R := by
    simpa [mem_ball,dist_eq_norm] using hw
  have hd : DifferentiableOn ℂ G (ball 0 R) := by
    intro w hw
    exact ((hg.differentiableAt (isOpen_ball.mem_nhds (hm w hw))).comp w
      ((differentiableAt_const c).add differentiableAt_id)).differentiableWithinAt
  have hb := Complex.borelCaratheodory_zero hM hd
    (fun w hw => hre _ (hm w hw)) hR
    (show z-c ∈ ball (0:ℂ) R by simpa [mem_ball,dist_eq_norm] using hz)
    (show G 0=0 by simpa [G] using hgc)
  simpa [G] using hb

/-- If the outer disk has radius 1+2d, the target radius 1+d leaves a
strict d-margin. No norm bound for a logarithmic derivative is assumed. -/
theorem logarithmic_derivative_disk (f : ℂ → ℂ) (c z : ℂ) (d M : ℝ)
    (hd : 0 < d) (hd1 : d ≤ 1/4) (hM : 0 < M)
    (hf : DifferentiableOn ℂ f (ball c (1+2*d)))
    (hn : ∀ w ∈ ball c (1+2*d), f w ≠ 0)
    (hb : ∀ w ∈ ball c (1+2*d), ‖f w‖ ≤ Real.exp M * ‖f c‖)
    (hz : ‖z-c‖ ≤ 1+d) :
    ‖deriv f z / f z‖ ≤ 16*M/d^2 := by
  have hR : 0 < 1+2*d := by linarith
  have hc : c ∈ ball c (1+2*d) := by simpa using hR
  have hfc : 0 < ‖f c‖ := norm_pos_iff.mpr (hn c hc)
  obtain ⟨g,hgc,hg⟩ := normalized_logarithm f c (1+2*d) hR hf hn
  have hgd : DifferentiableOn ℂ g (ball c (1+2*d)) :=
    fun w hw => (hg w hw).1.differentiableAt.differentiableWithinAt
  have hre (w : ℂ) (hw : w ∈ ball c (1+2*d)) : (g w).re ≤ M := by
    have he := congrArg norm (hg w hw).2
    rw [norm_mul,Complex.norm_exp] at he
    have hle : Real.exp ((g w).re) * ‖f c‖ ≤ Real.exp M * ‖f c‖ := by
      rw [←he]; exact hb w hw
    exact Real.exp_le_exp.mp (le_of_mul_le_mul_right hle hfc)
  have hsmall (w : ℂ) (hw : w ∈ closedBall z (d/2)) :
      ‖w-c‖ ≤ 1+3*d/2 := by
    have hh : ‖w-z‖ ≤ d/2 := by simpa [mem_closedBall,dist_eq_norm] using hw
    have ht : ‖w-c‖ ≤ ‖w-z‖+‖z-c‖ := by
      simpa only [sub_add_sub_cancel] using norm_add_le (w-z) (z-c)
    linarith
  have hsub : closedBall z (d/2) ⊆ ball c (1+2*d) := by
    intro w hw
    change dist w c < 1+2*d
    rw [dist_eq_norm]
    linarith [hsmall w hw]
  have hboundary (w : ℂ) (hw : w ∈ sphere z (d/2)) : ‖g w‖ ≤ 8*M/d := by
    have hwc : w ∈ closedBall z (d/2) := sphere_subset_closedBall hw
    have hr := hsmall w hwc
    have hri : ‖w-c‖ < 1+2*d := by linarith
    have hden : 0 < 1+2*d-‖w-c‖ := by linarith
    have hr2 : ‖w-c‖ ≤ 2 := by linarith
    have hgrowth := translated_borel g c w (1+2*d) M hR hM hgd hgc hre hri
    apply hgrowth.trans
    apply (div_le_div_iff₀ hden hd).mpr
    calc
      (2*M*‖w-c‖)*d ≤ ((2*M)*2)*d :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hr2 (by positivity)) hd.le
      _ = (4*M)*d := by ring
      _ ≤ (8*M)*(1+2*d-‖w-c‖) := by
        have hgap : d/2 ≤ 1+2*d-‖w-c‖ := by linarith
        nlinarith [mul_le_mul_of_nonneg_left hgap (by positivity : 0≤8*M)]
  have hdg : DiffContOnCl ℂ g (ball z (d/2)) := by
    apply DiffContOnCl.mk_ball
    · exact hgd.mono (ball_subset_closedBall.trans hsub)
    · exact (hgd.mono hsub).continuousOn
  have hder := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    (show 0<d/2 by positivity) hdg hboundary
  have hzbig : z ∈ ball c (1+2*d) := by
    rw [mem_ball,dist_eq_norm]; linarith
  rw [(hg z hzbig).1.deriv] at hder
  dsimp [logDerivative] at hder
  convert hder using 1 <;> field_simp <;> ring

end Item1ZeroFreeDisk

run_cmd do
  for target in [``Item1ZeroFreeDisk.logDerivative_differentiableOn,
    ``Item1ZeroFreeDisk.normalized_logarithm, ``Item1ZeroFreeDisk.translated_borel,
    ``Item1ZeroFreeDisk.logarithmic_derivative_disk] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"

#print axioms Item1ZeroFreeDisk.normalized_logarithm
#print axioms Item1ZeroFreeDisk.logarithmic_derivative_disk
