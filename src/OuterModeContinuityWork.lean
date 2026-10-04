import OuterDivisorModeWork
import FlatCofactorContour

/-! Continuity of normalized modes, including correlated tuple masks
and the actual sum over signed divisor atoms, for physical-window transfer. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace OuterModeContinuityWork
open OuterModeUnitCapWork OuterDivisorModeWork OuterCenteredFlatWork MellinWindowFactor
open Erdos374.HarmanGram152

theorem continuous_power (n : ℕ) (hn : 0<n) (σ u : ℝ) :
    Continuous (fun t : ℝ => (n:ℂ)^(-line σ (t-u))) := by
  have hh : Continuous (fun t : ℝ => -line σ (t-u)) := by unfold line; fun_prop
  exact hh.const_cpow (Or.inl (by exact_mod_cast Nat.ne_of_gt hn))

theorem continuous_pair (A B : Finset ℕ) (q : ℕ→ℕ→ℂ) (σ u v : ℝ)
    (hA : ∀a∈A,0<a) (hB : ∀b∈B,0<b) :
    Continuous (fun t => pairPolynomial A B q σ (t-u) (t-v)) := by
  change Continuous (fun t => ∑a∈A,
    verticalDirichlet152 B (q a) σ (t-v)*(a:ℂ)^(-line σ (t-u)))
  apply continuous_finsetSum
  intro a ha
  exact ((NormalizedMeanSquare.continuous_vertical B (q a) σ hB).comp
    (continuous_id.sub continuous_const)).mul (continuous_power a (hA a ha) σ u)

theorem continuous_remainingFactor (X s : ℝ) (i j d : ℕ) (ω : Fin 9→ℝ)
    (P A B : Finset ℕ) (q : ℕ→ℕ→ℂ) (σ : ℝ)
    (hP : ∀p∈P,0<p) (hA : ∀a∈A,0<a) (hB : ∀b∈B,0<b) :
    Continuous (remainingFactor X s i j d ω P A B q σ) := by
  exact ((NormalizedMeanSquare.continuous_vertical P _ σ hP).comp
    (continuous_id.sub continuous_const)).mul (continuous_pair A B q σ _ _ hA hB)

theorem continuous_divisorFactor (X s : ℝ) (i j : ℕ) (ω : Fin 9→ℝ)
    (D P A B : Finset ℕ) (q : ℕ→ℕ→ℕ→ℂ) (σ : ℝ)
    (hD : ∀d∈D,0<d) (hP : ∀p∈P,0<p) (hA : ∀a∈A,0<a) (hB : ∀b∈B,0<b) :
    Continuous (divisorFactor X s i j ω D P A B q σ) := by
  apply continuous_const.mul
  apply continuous_finsetSum
  intro d hd
  exact (continuous_power d (hD d hd) σ _).mul
    (continuous_remainingFactor X s i j d ω P A B (q d) σ hP hA hB)

theorem continuous_centeredFlat (lo hi : ℕ) (σ : ℝ)
    (hlo : 0<lo) (hhi : 0<hi) (hσ : 1<σ) :
    Continuous (centeredFlat lo hi σ) := by
  exact (NormalizedMeanSquare.continuous_vertical (Finset.Ioc lo hi) (fun _ => 1) σ
    (fun n hn => by have := (Finset.mem_Ioc.mp hn).1; omega)).sub
    (FlatCofactorContour.continuous_polynomial lo hi σ hlo hhi hσ)

run_cmd do
  for decl in [``continuous_power, ``continuous_pair, ``continuous_remainingFactor,
      ``continuous_divisorFactor, ``continuous_centeredFlat] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
end OuterModeContinuityWork
