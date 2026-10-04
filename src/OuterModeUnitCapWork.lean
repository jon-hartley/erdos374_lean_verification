import NormalizedDyadicCap
import OuterSeparatedFourierModeWork

/-! Uniform unit bounds for the actual divisor atom and a correlated
tuple mask on normalized rectangular factors. Prime cancellation is not
used; arbitrary translations of each factor are allowed. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped BigOperators
namespace OuterModeUnitCapWork
open Erdos374.HarmanGram152 OuterDivisorIntervalWork
open OuterMaskFrequencyWork

theorem unit_cap (S : Finset ℕ) (N : ℕ) (c : ℕ→ℂ) (σ t : ℝ)
    (hN : 1≤N) (hσ : 1≤σ)
    (hS : ∀n∈S,N<n ∧ n≤2*N) (hc : ∀n∈S,‖c n‖≤1) :
    ‖verticalDirichlet152 S c σ t‖≤1 := by
  have he : (∑n∈S,‖c n‖^2)≤1*(N:ℝ) := by
    calc
      _ ≤ ∑n∈S,(1:ℝ) := Finset.sum_le_sum (fun n hn => by
        simpa using pow_le_pow_left₀ (norm_nonneg _) (hc n hn) 2)
      _ = (S.card:ℝ) := by simp
      _ ≤ 1*(N:ℝ) := by simpa using NormalizedDyadicCap.card_bound S N hS
  have hh := NormalizedDyadicCap.norm_sq_le_energy S N c σ t 1 hN hσ
    (by norm_num) hS he
  nlinarith [norm_nonneg (verticalDirichlet152 S c σ t)]

def pairPolynomial (A B : Finset ℕ) (q : ℕ→ℕ→ℂ) (σ u v : ℝ) : ℂ :=
  verticalDirichlet152 A (fun a => verticalDirichlet152 B (q a) σ v) σ u

theorem pair_cap (A B : Finset ℕ) (Na Nb : ℕ) (q : ℕ→ℕ→ℂ)
    (σ u v : ℝ) (hNa : 1≤Na) (hNb : 1≤Nb) (hσ : 1≤σ)
    (hA : ∀a∈A,Na<a ∧ a≤2*Na) (hB : ∀b∈B,Nb<b ∧ b≤2*Nb)
    (hq : ∀a∈A,∀b∈B,‖q a b‖≤1) :
    ‖pairPolynomial A B q σ u v‖≤1 := by
  exact unit_cap A Na _ σ u hNa hσ hA
    (fun a ha => unit_cap B Nb (q a) σ v hNb hσ hB (hq a ha))

def remainingFactor (X s : ℝ) (i j d : ℕ) (ω : Fin 9→ℝ)
    (P A B : Finset ℕ) (q : ℕ→ℕ→ℂ) (σ t : ℝ) : ℂ :=
  verticalDirichlet152 P (fun p => ((divisorAtom X s d p).re:ℂ)) σ
    (t-shift ω primeSlope) *
  pairPolynomial A B q σ (t-shift ω (firstSlope s i))
    (t-shift ω (secondSlope s j))

theorem remainingFactor_cap (X s : ℝ) (i j d : ℕ) (ω : Fin 9→ℝ)
    (P A B : Finset ℕ) (Np Na Nb : ℕ) (q : ℕ→ℕ→ℂ)
    (σ t : ℝ) (hNp : 1≤Np) (hNa : 1≤Na) (hNb : 1≤Nb) (hσ : 1≤σ)
    (hP : ∀p∈P,Np<p ∧ p≤2*Np)
    (hA : ∀a∈A,Na<a ∧ a≤2*Na) (hB : ∀b∈B,Nb<b ∧ b≤2*Nb)
    (hq : ∀a∈A,∀b∈B,‖q a b‖≤1) :
    ‖remainingFactor X s i j d ω P A B q σ t‖≤1 := by
  rw [remainingFactor,norm_mul]
  exact (mul_le_mul (unit_cap P Np _ σ _ hNp hσ hP
    (fun p _ => by
      simpa only [Complex.norm_real,Real.norm_eq_abs] using
        (Complex.abs_re_le_norm (divisorAtom X s d p)).trans (divisorAtom_norm_le X s d p)))
    (pair_cap A B Na Nb q σ _ _ hNa hNb hσ hA hB hq)
    (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)

run_cmd do
  for decl in [``unit_cap, ``pair_cap, ``remainingFactor_cap] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
end OuterModeUnitCapWork
