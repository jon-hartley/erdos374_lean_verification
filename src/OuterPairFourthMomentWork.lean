import CorrelatedPairFourthWork

/-! The literal correlated pair polynomial with independently shifted
frequencies satisfies a logarithmic fourth moment. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open MeasureTheory Set
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace OuterPairFourthMomentWork
open OuterSeparatedFourierModeWork
open OuterModeUnitCapWork OuterNormalizedModeWork OuterMaskFrequencyWork
open CorrelatedPairFourthWork DirichletPowerCoefficients
open Erdos374.HarmanGram152 MellinWindowFactor

def pairSet (A B : Finset ℕ) : Finset (Fin 2 → ℕ) :=
  (A ×ˢ B).image (fun x => ![x.1,x.2])

def pairWeight (q : ℕ → ℕ → ℂ) (u v : ℝ) (f : Fin 2 → ℕ) : ℂ :=
  q (f 0) (f 1) * logPhase u (f 0) * logPhase v (f 1)

theorem pairWeight_cap (A B : Finset ℕ) (q : ℕ → ℕ → ℂ) (u v : ℝ)
    (hq : ∀ a ∈ A, ∀ b ∈ B, ‖q a b‖ ≤ 1) :
    ∀ f ∈ pairSet A B, ‖pairWeight q u v f‖ ≤ 1 := by
  intro f hf
  obtain ⟨⟨a,b⟩,hab,rfl⟩ := Finset.mem_image.mp hf
  have hh := Finset.mem_product.mp hab
  simpa [pairWeight, norm_mul, logPhase, phase_norm] using hq a hh.1 b hh.2

theorem pair_identity (A B : Finset ℕ) (q : ℕ → ℕ → ℂ) (σ t u v : ℝ)
    (hA : ∀ a ∈ A, 0<a) (hB : ∀ b ∈ B, 0<b) :
    pairPolynomial A B q σ (t-u) (t-v) =
      polynomial (pairSet A B) (pairWeight q u v) σ t := by
  rw [polynomial, pairSet, Finset.sum_image]
  · rw [Finset.sum_product]
    unfold pairPolynomial verticalDirichlet152
    apply Finset.sum_congr rfl
    intro a ha
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro b hb
    simp only [pairWeight, productIndex, Fin.prod_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, nat_mul_cpow]
    change q a b * (b:ℂ)^(-line σ (t-v)) * (a:ℂ)^(-line σ (t-u)) = _
    rw [←phase_shift a (hA a ha), ←phase_shift b (hB b hb)]
    dsimp only [line]
    ring
  · intro x hx y hy he
    have h0 := congrFun he 0
    have h1 := congrFun he 1
    exact Prod.ext (by simpa using h0) (by simpa using h1)

theorem pair_fourth_moment (A B : Finset ℕ) (Na Nb : ℕ)
    (q : ℕ → ℕ → ℂ) (σ lo hi u v : ℝ)
    (hNa : 1≤Na) (hNb : 1≤Nb) (hσ : 1≤σ) (hlohi : lo≤hi)
    (hA : ∀ a ∈ A, a.Prime ∧ Na<a ∧ a≤2*Na)
    (hB : ∀ b ∈ B, b.Prime ∧ Nb<b ∧ b≤2*Nb)
    (hq : ∀ a ∈ A, ∀ b ∈ B, ‖q a b‖≤1)
    (hT : hi-lo ≤ ((Na*Nb:ℕ):ℝ)^2) :
    (∫ t in Icc lo hi, ‖pairPolynomial A B q σ (t-u) (t-v)‖^4) ≤
      266240*(1+Real.log (((4*(Na*Nb):ℕ):ℝ)^2))^4 := by
  have hM : 1≤Na*Nb := by nlinarith
  have hs : ∀ f ∈ pairSet A B, (∀ i, Nat.Prime (f i)) ∧
      Na*Nb < productIndex f ∧ productIndex f ≤ 4*(Na*Nb) := by
    intro f hf
    obtain ⟨⟨a,b⟩,hab,rfl⟩ := Finset.mem_image.mp hf
    have ha := hA a (Finset.mem_product.mp hab).1
    have hb := hB b (Finset.mem_product.mp hab).2
    refine ⟨?_,?_,?_⟩
    · intro i
      fin_cases i
      · exact ha.1
      · exact hb.1
    · simp only [productIndex, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
      nlinarith
    · simp only [productIndex, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
      nlinarith [Nat.mul_le_mul ha.2.2 hb.2.2]
  have hm := CorrelatedPairFourthWork.fourth_moment (pairSet A B)
    (pairWeight q u v) (Na*Nb) (4*(Na*Nb)) hM (by omega) hs
    (pairWeight_cap A B q u v hq) σ lo hi 4 hσ hlohi (by norm_num)
    (by push_cast; rfl) hT
  simp_rw [pair_identity A B q σ _ u v
    (fun a ha => (hA a ha).1.pos) (fun b hb => (hB b hb).1.pos)]
  convert hm using 1 <;> ring

run_cmd do
  for decl in [``pairWeight_cap, ``pair_identity, ``pair_fourth_moment] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end OuterPairFourthMomentWork
