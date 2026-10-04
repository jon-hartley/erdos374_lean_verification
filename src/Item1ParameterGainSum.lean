import Item1ParameterGain
import Item1ParameterFactorProduct

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open scoped BigOperators

namespace Item1ParameterGain
open Item1ParameterCore

theorem sum_fin_succ_eq_Icc (d : ℕ) (f : ℕ → ℝ) :
    (∑ j : Fin d, f (j.val+1)) = ∑ j ∈ Finset.Icc 1 d, f j := by
  apply Finset.sum_bij (fun (j : Fin d) _ => j.val+1)
  · intro j _
    exact Finset.mem_Icc.mpr ⟨by omega, by have := j.isLt; omega⟩
  · intro i _ j _ hij
    apply Fin.ext
    omega
  · intro j hj
    have hj' := Finset.mem_Icc.mp hj
    refine ⟨⟨j-1,by omega⟩,Finset.mem_univ _,?_⟩
    dsimp
    omega
  · intro j _
    rfl

theorem sum_gain_eq_totalGain (d : ℕ) (a : ℝ) :
    (∑ j : Fin d, gain a ((j.val+1:ℕ):ℝ)) = totalGain d a :=
  sum_fin_succ_eq_Icc d (fun j => gain a (j:ℝ))

theorem sum_modelExponent (d : ℕ) (a : ℝ) :
    (∑ j : Fin d, modelExponent a ((j.val+1:ℕ):ℝ)) =
      (d:ℝ)*((d:ℝ)+1)/3-totalGain d a := by
  have hlinear : (∑ j : Fin d, 2*((j.val+1:ℕ):ℝ)/3) =
      (d:ℝ)*((d:ℝ)+1)/3 := by
    calc
      (∑ j : Fin d, 2*((j.val+1:ℕ):ℝ)/3) =
          (2/3:ℝ)*(∑ j : Fin d, ((j.val+1:ℕ):ℝ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = _ := by rw [Item1ParameterFactorProduct.sum_degree_indices]; ring
  calc
    (∑ j : Fin d, modelExponent a ((j.val+1:ℕ):ℝ)) =
        (∑ j : Fin d, 2*((j.val+1:ℕ):ℝ)/3) -
          ∑ j : Fin d, gain a ((j.val+1:ℕ):ℝ) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _
      have h := model_gain_identity a ((j.val+1:ℕ):ℝ)
      linarith
    _ = _ := by rw [hlinear, sum_gain_eq_totalGain]

end Item1ParameterGain

run_cmd do
  for target in [``Item1ParameterGain.sum_fin_succ_eq_Icc,
      ``Item1ParameterGain.sum_gain_eq_totalGain, ``Item1ParameterGain.sum_modelExponent] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "PARAMETER GAIN SUM: 3 standard-axiom theorem guards passed."
