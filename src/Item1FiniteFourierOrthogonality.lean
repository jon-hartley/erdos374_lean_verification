import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Tactic

/-! Exact finite Fourier collision counting on the unit torus.
The identity below is an orthogonality statement, not a Vinogradov mean-value
upper bound. Repeated frequencies are counted with their full multiplicities. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory UnitAddTorus
open scoped ComplexConjugate

-- Use exactly the normalized product Haar measure of AddCircleMulti.
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace Item1FiniteFourierOrthogonality

/-- Every finite Fourier sum has its genuine square norm integrable. -/
theorem integrable_sq_norm_sum {ι : Type*} [Fintype ι] (d : ℕ)
    (v : ι → (Fin d → ℤ)) :
    Integrable (fun a : UnitAddTorus (Fin d) =>
      ‖∑ i, mFourier (v i) a‖ ^ 2) := by
  have hc : Continuous (fun a : UnitAddTorus (Fin d) =>
      ‖∑ i, mFourier (v i) a‖ ^ 2) := by fun_prop
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- The integral is exactly the number of ordered frequency collisions.
No injectivity assumption is needed, including for empty index or coordinate sets. -/
theorem integral_sq_norm_sum_eq_collisions {ι : Type*} [Fintype ι] (d : ℕ)
    (v : ι → (Fin d → ℤ)) :
    (∫ a : UnitAddTorus (Fin d), ‖∑ i, mFourier (v i) a‖ ^ 2) =
      ∑ i, ∑ j, if v i = v j then (1 : ℝ) else 0 := by
  classical
  let F : C(UnitAddTorus (Fin d), ℂ) := ∑ i, mFourier (v i)
  have horth := orthonormal_iff_ite.mp (orthonormal_mFourier (d := Fin d))
  have hid : inner ℂ (ContinuousMap.toLp 2 volume ℂ F)
      (ContinuousMap.toLp 2 volume ℂ F) =
      ((∫ a : UnitAddTorus (Fin d), ‖F a‖ ^ 2 : ℝ) : ℂ) := by
    rw [ContinuousMap.inner_toLp]
    calc
      (∫ a : UnitAddTorus (Fin d), F a * conj (F a)) =
          ∫ a : UnitAddTorus (Fin d), ((‖F a‖ ^ 2 : ℝ) : ℂ) := by
        apply integral_congr_ae
        exact ae_of_all _ (fun a =>
          (RCLike.mul_conj (F a)).trans (Complex.ofReal_pow ‖F a‖ 2).symm)
      _ = _ := integral_ofReal (μ := volume)
  have hF : (fun a : UnitAddTorus (Fin d) => ‖F a‖ ^ 2) =
      (fun a : UnitAddTorus (Fin d) => ‖∑ i, mFourier (v i) a‖ ^ 2) := by
    funext a
    simp only [F, ContinuousMap.sum_apply]
  rw [hF] at hid
  apply Complex.ofReal_injective
  rw [← hid]
  dsimp only [F]
  simp only [map_sum, sum_inner, inner_sum]
  simp only [horth, Complex.ofReal_sum, apply_ite,
    Complex.ofReal_one, Complex.ofReal_zero, eq_comm]

end Item1FiniteFourierOrthogonality

run_cmd do
  for target in [``Item1FiniteFourierOrthogonality.integrable_sq_norm_sum,
      ``Item1FiniteFourierOrthogonality.integral_sq_norm_sum_eq_collisions] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "FINITE FOURIER ORTHOGONALITY: 2 standard-axiom theorem guards passed."
