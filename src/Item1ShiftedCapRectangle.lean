import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Tactic

/-!
UNCOMPILED. A genuine Cauchy rectangle identity, not a contour identity assumed
as an input. Instantiation with the smoothed zeta integrand is NOT completed.
The pointwise logarithmic-derivative bound/zero-free input remains unproved.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory Set Complex
namespace Item1ShiftedCapRectangle

def horizontal (f : ℂ → ℂ) (a b v : ℝ) : ℂ :=
  ∫ σ in a..b, f ((σ:ℂ)+(v:ℂ)*Complex.I)
def vertical (f : ℂ → ℂ) (σ T : ℝ) : ℂ :=
  Complex.I*(∫ v in (-T)..T, f ((σ:ℂ)+(v:ℂ)*Complex.I))

/-- Shift only over imaginary offsets [-t/2,t/2]. The zeta pole at height
zero is then outside the translated rectangle. -/
theorem shifted_height (t v : ℝ) (ht : 8 ≤ t) (hv : |v| ≤ t/2) :
    3 < t+v ∧ t/2 ≤ t+v ∧ t+v ≤ 2*t := by
  have hh := abs_le.mp hv
  constructor
  · linarith
  constructor <;> linarith

theorem translated_no_pole (t σ v : ℝ) (ht : 8 ≤ t) (hv : |v| ≤ t/2) :
    (1:ℂ)+(σ:ℂ)+(t+v:ℝ)*Complex.I ≠ 1 := by
  intro hh
  have hi := congrArg Complex.im hh
  simp at hi
  have hpos := (shifted_height t v ht hv).1
  linarith

/-- No assumption of vanishing contour integral: call Mathlib's Cauchy theorem. -/
theorem shift_vertical (f : ℂ → ℂ) (a b T : ℝ)
    (hd : DifferentiableOn ℂ f (Set.uIcc a b ×ℂ Set.uIcc (-T) T)) :
    vertical f b T = vertical f a T + horizontal f a b T-horizontal f a b (-T) := by
  have hc := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f
    ((a:ℂ)+(-T:ℝ)*Complex.I) ((b:ℂ)+(T:ℂ)*Complex.I) (by simpa using hd)
  have hzero : horizontal f a b (-T)-horizontal f a b T+
      vertical f b T-vertical f a T=0 := by
    simpa [horizontal,vertical,smul_eq_mul] using hc
  linear_combination hzero

theorem norm_vertical_le (f : ℂ → ℂ) (a b T : ℝ)
    (hd : DifferentiableOn ℂ f (Set.uIcc a b ×ℂ Set.uIcc (-T) T)) :
    ‖vertical f b T‖ ≤ ‖vertical f a T‖+
      ‖horizontal f a b T‖+‖horizontal f a b (-T)‖ := by
  rw [shift_vertical f a b T hd]
  exact (norm_sub_le _ _).trans
    (add_le_add (norm_add_le _ _) le_rfl)

/-- Finite assembly of three edge bounds. Qualitative holomorphy is explicit;
none of the numeric bounds below is claimed to be the missing arithmetic input. -/
theorem norm_vertical_of_edges (f : ℂ → ℂ) (a b T V H : ℝ)
    (hd : DifferentiableOn ℂ f (Set.uIcc a b ×ℂ Set.uIcc (-T) T))
    (hV : ‖vertical f a T‖ ≤ V)
    (hTop : ‖horizontal f a b T‖ ≤ H)
    (hBottom : ‖horizontal f a b (-T)‖ ≤ H) :
    ‖vertical f b T‖ ≤ V+2*H := by
  have hh := norm_vertical_le f a b T hd
  linarith

end Item1ShiftedCapRectangle

run_cmd do
  for target in [``Item1ShiftedCapRectangle.shifted_height,
    ``Item1ShiftedCapRectangle.translated_no_pole,
    ``Item1ShiftedCapRectangle.shift_vertical,
    ``Item1ShiftedCapRectangle.norm_vertical_le,
    ``Item1ShiftedCapRectangle.norm_vertical_of_edges] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"

#print axioms Item1ShiftedCapRectangle.shift_vertical
#print axioms Item1ShiftedCapRectangle.norm_vertical_of_edges
