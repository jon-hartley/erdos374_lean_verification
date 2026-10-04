import FiniteMellinInversion

/-!
A concrete choice satisfying the smoothing hypotheses. A normalized
smooth bump around 1 is multiplied by x so that its multiplicative
mass, the integral of Psi(x)/x, is exactly one.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set

namespace MellinSmoothingFunction

def bump : ContDiffBump (1 : ℝ) where
  rIn := 1 / 4
  rOut := 1 / 2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

def normalizedBump (x : ℝ) : ℝ := bump x / ∫ y : ℝ, bump y

theorem bump_integrable : Integrable (fun x : ℝ => bump x) :=
  bump.continuous.integrable_of_hasCompactSupport bump.hasCompactSupport

theorem bump_integral_pos : 0 < ∫ y : ℝ, bump y := by
  apply integral_pos_of_integrable_nonneg_nonzero bump.continuous bump_integrable
    bump.nonneg' (x := 1)
  rw [bump.one_of_mem_closedBall (Metric.mem_closedBall_self bump.rIn_pos.le)]
  norm_num

theorem normalized_mass : ∫ x : ℝ, normalizedBump x = 1 := by
  unfold normalizedBump
  rw [integral_div]
  exact div_self bump_integral_pos.ne'

def smoothing (x : ℝ) : ℝ := x * normalizedBump x

theorem differentiable : ContDiff ℝ 1 smoothing :=
  contDiff_id.mul (bump.contDiff.div_const _)

theorem nonnegative (x : ℝ) (hx : 0 < x) : 0 ≤ smoothing x :=
  mul_nonneg hx.le (div_nonneg bump.nonneg bump_integral_pos.le)

theorem bump_support : Function.support normalizedBump ⊆ Icc (1 / 2) 2 := by
  intro x hx
  have hxb : x ∈ Function.support bump := by
    intro hz
    exact hx (by simp [normalizedBump, hz])
  rw [bump.support_eq] at hxb
  have hh : |x - 1| < 1 / 2 := by
    simpa only [Metric.mem_ball, Real.dist_eq, bump] using hxb
  have hparts := abs_lt.mp hh
  constructor <;> linarith

theorem support : Function.support smoothing ⊆ Icc (1 / 2) 2 := by
  intro x hx
  apply bump_support
  change normalizedBump x ≠ 0
  intro hz
  exact hx (by simp [smoothing, hz])

theorem mass_one : ∫ x in Ioi 0, smoothing x / x = 1 := by
  calc
    _ = ∫ x in Ioi 0, normalizedBump x := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      unfold smoothing
      field_simp [ne_of_gt (show 0 < x from hx)]
    _ = ∫ x : ℝ, normalizedBump x := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      by_contra hz
      have hh := bump_support hz
      simp only [mem_Ioi, not_lt] at hx
      linarith [hh.1]
    _ = 1 := normalized_mass

theorem exists_smoothing : ∃ Ψ : ℝ → ℝ,
    ContDiff ℝ 1 Ψ ∧ (∀ x > 0, 0 ≤ Ψ x) ∧
      Function.support Ψ ⊆ Icc (1 / 2) 2 ∧
        (∫ x in Ioi 0, Ψ x / x) = 1 :=
  ⟨smoothing, differentiable, nonnegative, support, mass_one⟩

theorem finite_sum (s : Finset ℕ) (coeff : ℕ → ℂ) (X σ ε : ℝ)
    (hX : 0 < X) (hs : ∀ n ∈ s, 0 < n)
    (hσ : 1 < σ) (hσtwo : σ ≤ 2) (hε : ε ∈ Ioo 0 1) :
    (∑ n ∈ s, coeff n * (Smooth1 smoothing ε ((n : ℝ) / X) : ℂ)) =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ t : ℝ, Erdos374.HarmanGram152.verticalDirichlet152 s coeff σ t *
          mellin (fun x => (Smooth1 smoothing ε x : ℂ)) (MellinWindowFactor.line σ t) *
            (X : ℂ) ^ MellinWindowFactor.line σ t :=
  FiniteMellinInversion.smooth_finite_sum s coeff smoothing X σ ε hX hs hσ hσtwo hε
    differentiable nonnegative support mass_one

end MellinSmoothingFunction

#print axioms MellinSmoothingFunction.exists_smoothing
run_cmd do
  for decl in [``MellinSmoothingFunction.exists_smoothing, ``MellinSmoothingFunction.finite_sum] do
    let axioms ← Lean.collectAxioms decl
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "MELLIN SMOOTHING FUNCTION PASSED"
