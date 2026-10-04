import OuterNormalizedModeWork
import OuterExceptionalBudgetWork

/-! Sum the actual small-divisor atoms inside a rectangular dyadic block.
Reciprocal normalization pays this sum with unit cost, even when tuple
coefficients depend on the divisor. This concerns factorized modes. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators
namespace OuterDivisorModeWork
open OuterModeUnitCapWork OuterNormalizedModeWork OuterMaskFrequencyWork
open MellinWindowFactor OuterExceptionalBudgetWork

def divisorFactor (X s : ℝ) (i j : ℕ) (ω : Fin 9→ℝ)
    (D P A B : Finset ℕ) (q : ℕ→ℕ→ℕ→ℂ) (σ t : ℝ) : ℂ :=
  phase (shift ω (constantSlope s)) (Real.log X) *
    ∑d∈D,(d:ℂ)^(-line σ (t-shift ω divisorSlope))*
      remainingFactor X s i j d ω P A B (q d) σ t

theorem divisorFactor_cap (X s : ℝ) (i j : ℕ) (ω : Fin 9→ℝ)
    (D P A B : Finset ℕ) (Nd Np Na Nb : ℕ) (q : ℕ→ℕ→ℕ→ℂ)
    (σ t : ℝ) (hNd : 1≤Nd) (hNp : 1≤Np) (hNa : 1≤Na) (hNb : 1≤Nb)
    (hσ : 1≤σ) (hD : ∀d∈D,Nd≤d ∧ d<2*Nd) (hP : ∀p∈P,Np<p ∧ p≤2*Np)
    (hA : ∀a∈A,Na<a ∧ a≤2*Na) (hB : ∀b∈B,Nb<b ∧ b≤2*Nb)
    (hq : ∀d∈D,∀a∈A,∀b∈B,‖q d a b‖≤1) :
    ‖divisorFactor X s i j ω D P A B q σ t‖≤1 := by
  have hNdR : (0:ℝ)<Nd := by exact_mod_cast (show 0<Nd by omega)
  have hcard : (D.card:ℝ)≤Nd := by
    have hh := Finset.card_le_card (show D⊆Finset.Ico Nd (2*Nd) from
      fun d hd => Finset.mem_Ico.mpr (hD d hd))
    rw [Nat.card_Ico] at hh
    exact_mod_cast (show D.card≤Nd by omega)
  rw [divisorFactor,norm_mul,phase_norm,one_mul]
  calc
    _ ≤ ∑d∈D,‖(d:ℂ)^(-line σ (t-shift ω divisorSlope))*
        remainingFactor X s i j d ω P A B (q d) σ t‖ := norm_sum_le _ _
    _ ≤ ∑d∈D,(Nd:ℝ)⁻¹ := Finset.sum_le_sum (fun d hd => by
      rw [norm_mul]
      have hc := remainingFactor_cap X s i j d ω P A B Np Na Nb (q d) σ t
        hNp hNa hNb hσ hP hA hB (hq d hd)
      have hdN := FlatCofactorApproximation.inverse_power_bound Nd d σ
        (line σ (t-shift ω divisorSlope)) hNd (hD d hd).1 hσ (by simp [line])
      exact (mul_le_mul hdN hc (norm_nonneg _) (by positivity)).trans_eq (by ring))
    _ = (D.card:ℝ)*(Nd:ℝ)⁻¹ := by simp
    _ ≤ (Nd:ℝ)*(Nd:ℝ)⁻¹ := mul_le_mul_of_nonneg_right
      hcard (by positivity)
    _ = 1 := mul_inv_cancel₀ hNdR.ne'

theorem source_sum_factorization (X s : ℝ) (i j : ℕ) (ω : Fin 9→ℝ)
    (D P A B K : Finset ℕ) (q : ℕ→ℕ→ℕ→ℂ) (σ t : ℝ)
    (hD : ∀d∈D,0<d) (hP : ∀p∈P,0<p) (hA : ∀a∈A,0<a)
    (hB : ∀b∈B,0<b) (hK : ∀k∈K,0<k) :
    (∑d∈D,sourcePolynomial X s i j d ω P A B K (q d) σ t) =
      divisorFactor X s i j ω D P A B q σ t *
        Erdos374.HarmanGram152.verticalDirichlet152 K (fun _ => 1) σ t := by
  simp only [divisorFactor,Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d hd
  exact (sourcePolynomial_factorization X s i j d ω P A B K (q d) σ t
    (hD d hd) hP hA hB hK).trans (by ring)

theorem eventually_divisor_modes :
    ∃κ : ℝ, 0<κ ∧ κ≤1/1000 ∧ ∀ (C : ℝ) (Aexp Bexp : ℕ), 0≤C →
      ∀ᶠ X : ℝ in atTop, 1<X ∧
        ∀ (s : ℝ) (i j : ℕ) (ω : Fin 9→ℝ)
          (D P A B : Finset ℕ) (Nd Np Na Nb N lo hi : ℕ)
          (q : ℕ→ℕ→ℕ→ℂ) (σ U : ℝ),
          1≤Nd → 1≤Np → 1≤Na → 1≤Nb →
          (∀d∈D,Nd≤d ∧ d<2*Nd) → (∀p∈P,Np<p ∧ p≤2*Np) →
          (∀a∈A,Na<a ∧ a≤2*Na) → (∀b∈B,Nb<b ∧ b≤2*Nb) →
          (∀d∈D,∀a∈A,∀b∈B,‖q d a b‖≤1) →
          X^(113/500:ℝ)≤(N:ℝ) → (N:ℝ)≤X →
          N≤lo → lo<hi → hi≤2*N → 1<σ → σ≤2 → 0≤U → U≤X^κ →
          C*(1+Real.log X)^Bexp*
            (lowEnergy X lo hi σ (divisorFactor X s i j ω D P A B q σ) +
              nearEnergy X (-(shift ω primeSlope)) U lo hi σ
                (divisorFactor X s i j ω D P A B q σ))
            ≤1/(Real.log X)^Aexp := by
  obtain ⟨κ,hκ,hκρ,hh⟩ := eventually_low_and_near
  refine ⟨κ,hκ,hκρ,?_⟩
  intro C Aexp Bexp hC
  filter_upwards [hh C Aexp Bexp hC] with X hX
  refine ⟨hX.1,?_⟩
  intro s i j ω D P A B Nd Np Na Nb N lo hi q σ U
    hNd hNp hNa hNb hD hP hA hB hq hN hNX hlo hhi hhiN hσ hσ2 hU hUX
  exact hX.2 N lo hi σ (-(shift ω primeSlope)) U
    (divisorFactor X s i j ω D P A B q σ)
    hN hNX hlo hhi hhiN hσ hσ2 hU hUX
    (fun t => divisorFactor_cap X s i j ω D P A B Nd Np Na Nb q σ t
      hNd hNp hNa hNb hσ.le hD hP hA hB hq)

run_cmd do
  for decl in [``divisorFactor_cap, ``source_sum_factorization,
      ``eventually_divisor_modes] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
end OuterDivisorModeWork
