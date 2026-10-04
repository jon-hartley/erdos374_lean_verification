import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic

/-! Exact phase perturbation estimates for finite polynomial approximation.
These are error bounds, not assertions of cancellation. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped BigOperators

namespace Item1PhasePerturbation

def unitPhase (x : ℝ) : ℂ := Complex.exp ((x:ℂ)*Complex.I)

theorem unitPhase_norm (x : ℝ) : ‖unitPhase x‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I x

theorem unitPhase_add (x y : ℝ) :
    unitPhase (x+y) = unitPhase x*unitPhase y := by
  simp only [unitPhase,Complex.ofReal_add,add_mul,Complex.exp_add]

theorem unitPhase_sub_le (x y : ℝ) :
    ‖unitPhase x-unitPhase y‖ ≤ |x-y| := by
  have hid : unitPhase x-unitPhase y =
      unitPhase y*(unitPhase (x-y)-1) := by
    rw [mul_sub,mul_one,←unitPhase_add]
    congr 1
    ring
  rw [hid,norm_mul,unitPhase_norm,one_mul]
  simpa only [unitPhase,mul_comm,Real.norm_eq_abs] using
    (Real.norm_exp_I_mul_ofReal_sub_one_le (x := x-y))

theorem sum_phase_sub_le {ι : Type*} (s : Finset ι) (f g : ι → ℝ) :
    ‖(∑ i ∈ s, unitPhase (f i))-(∑ i ∈ s, unitPhase (g i))‖ ≤
      ∑ i ∈ s, |f i-g i| := by
  rw [←Finset.sum_sub_distrib]
  exact (norm_sum_le _ _).trans
    (Finset.sum_le_sum (fun i _ => unitPhase_sub_le (f i) (g i)))

theorem sum_phase_norm_le {ι : Type*} (s : Finset ι) (f g : ι → ℝ) :
    ‖∑ i ∈ s, unitPhase (f i)‖ ≤
      ‖∑ i ∈ s, unitPhase (g i)‖+∑ i ∈ s, |f i-g i| := by
  have hh := norm_add_le
    ((∑ i ∈ s, unitPhase (f i))-(∑ i ∈ s, unitPhase (g i)))
    (∑ i ∈ s, unitPhase (g i))
  rw [sub_add_cancel] at hh
  have hs := sum_phase_sub_le s f g
  linarith only [hh,hs]

theorem sum_phase_norm_le_uniform {ι : Type*} (s : Finset ι)
    (f g : ι → ℝ) (E : ℝ) (hE : ∀ i ∈ s, |f i-g i| ≤ E) :
    ‖∑ i ∈ s, unitPhase (f i)‖ ≤
      ‖∑ i ∈ s, unitPhase (g i)‖+(s.card:ℝ)*E := by
  have hs := Finset.sum_le_sum hE
  simp only [Finset.sum_const,nsmul_eq_mul] at hs
  exact (sum_phase_norm_le s f g).trans (add_le_add le_rfl hs)

end Item1PhasePerturbation

run_cmd do
  for target in [``Item1PhasePerturbation.unitPhase_norm,
      ``Item1PhasePerturbation.unitPhase_add,
      ``Item1PhasePerturbation.unitPhase_sub_le,
      ``Item1PhasePerturbation.sum_phase_sub_le,
      ``Item1PhasePerturbation.sum_phase_norm_le,
      ``Item1PhasePerturbation.sum_phase_norm_le_uniform] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "Item1PhasePerturbation: 6 standard-axiom theorem guards passed."
