import FlatFourthMomentWork
import MaskedPrimeTupleMeanWork
import OuterNormalizedModeWork

/-! Fourth moments for correlated prime-pair coefficients. No factorization
of the pair mask is assumed, and no prime cap is needed. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open MeasureTheory Set
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CorrelatedPairFourthWork
open DirichletPowerCoefficients LongerTupleCollection Erdos374.HarmanGram152

theorem coefficient_cap (S : Finset (Fin 2 → ℕ)) (w : (Fin 2 → ℕ) → ℂ)
    (hS : ∀ f ∈ S, ∀ i, Nat.Prime (f i))
    (hw : ∀ f ∈ S, ‖w f‖ ≤ 1) (n : ℕ) :
    ‖coefficient S productIndex w n‖ ≤ 4 := by
  calc
    _ ≤ ∑ f ∈ S.filter (fun f => productIndex f=n), ‖w f‖ := norm_sum_le _ _
    _ ≤ ∑ _f ∈ S.filter (fun f => productIndex f=n), (1:ℝ) :=
      Finset.sum_le_sum (fun f hf => hw f (Finset.mem_filter.mp hf).1)
    _ = ((S.filter (fun f => productIndex f=n)).card:ℝ) := by simp
    _ ≤ 4 := by exact_mod_cast MaskedPrimeTupleMeanWork.fiber_card_le 2 S hS n

def polynomial (S : Finset (Fin 2 → ℕ)) (w : (Fin 2 → ℕ) → ℂ)
    (σ t : ℝ) : ℂ :=
  ∑ f ∈ S, w f * (productIndex f:ℂ)^(-MellinWindowFactor.line σ t)

theorem collected (S : Finset (Fin 2 → ℕ)) (w : (Fin 2 → ℕ) → ℂ)
    (D N : ℕ) (hS : ∀ f ∈ S, D < productIndex f ∧ productIndex f ≤ N)
    (σ t : ℝ) :
    polynomial S w σ t = verticalDirichlet152 (Finset.Ioc D N)
      (coefficient S productIndex w) σ t := by
  rw [polynomial, ← grouped_sum S productIndex w (fun n => (n:ℂ)^(-MellinWindowFactor.line σ t))]
  apply Finset.sum_subset
  · intro n hn
    obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp hn
    exact Finset.mem_Ioc.mpr (hS f hf)
  · intro n hn hnS
    rw [coefficient_zero_off_support S productIndex w n hnS, zero_mul]

theorem fourth_moment (S : Finset (Fin 2 → ℕ)) (w : (Fin 2 → ℕ) → ℂ)
    (D N : ℕ) (hD : 1 ≤ D) (hDN : D ≤ N)
    (hS : ∀ f ∈ S, (∀ i, Nat.Prime (f i)) ∧ D < productIndex f ∧ productIndex f ≤ N)
    (hw : ∀ f ∈ S, ‖w f‖ ≤ 1)
    (σ A B R : ℝ) (hσ : 1 ≤ σ) (hAB : A ≤ B)
    (hR : 1 ≤ R) (hN : (N:ℝ) ≤ R*D) (hT : B-A ≤ (D:ℝ)^2) :
    (∫ t in Icc A B, ‖polynomial S w σ t‖^4) ≤
      256*((1+4*R^2)*R^2*(1+Real.log ((N:ℝ)^2))^4) := by
  let c := coefficient S productIndex w
  have hc (n : ℕ) : ‖c n / (4:ℂ)‖ ≤ 1 := by
    rw [norm_div]
    norm_num
    have := coefficient_cap S w (fun f hf => (hS f hf).1) hw n
    dsimp [c]
    linarith
  have hm := FlatFourthMomentWork.fourth_moment_log D N hD hDN
    (fun n => c n / 4) (fun n _ => hc n) σ A B R hσ hAB hR hN hT
  have he (t : ℝ) : polynomial S w σ t =
      4 * verticalDirichlet152 (Finset.Ioc D N) (fun n => c n / 4) σ t := by
    rw [collected S w D N (fun f hf => (hS f hf).2)]
    unfold verticalDirichlet152
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    dsimp [c]
    ring
  have hn (t : ℝ) : ‖polynomial S w σ t‖^4 =
      256 * ‖verticalDirichlet152 (Finset.Ioc D N) (fun n => c n / 4) σ t‖^4 := by
    rw [he, norm_mul, mul_pow]
    norm_num
  simp_rw [hn]
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left hm (by norm_num)

run_cmd do
  for decl in [``coefficient_cap, ``collected, ``fourth_moment] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end CorrelatedPairFourthWork
