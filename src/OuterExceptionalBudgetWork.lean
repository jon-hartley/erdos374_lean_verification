import OuterCenteredExceptionalWork

/-! All fixed logarithmic costs can be paid in the physical low band
and the translated prime near-zero band, for a centered factorized mode.
This includes costs 13 and 26. No bound on the complementary prime band
or identification with localizedNegativeMean is claimed. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Filter MeasureTheory Set
namespace OuterExceptionalBudgetWork
open OuterCenteredFlatWork OuterCenteredExceptionalWork OuterExceptionalFlatWork
open OuterModeUnitCapWork OuterMaskFrequencyWork

theorem absorb_power (C K κ : ℝ) (A B : ℕ)
    (hC : 0≤C) (hK : 0≤K) (hκ : 0<κ) :
    ∀ᶠ X : ℝ in atTop, 1<X ∧
      C*(1+Real.log X)^B*(K*X^(-κ))≤1/(Real.log X)^A := by
  filter_upwards [PolynomialLogEnvelope.eventually_bound (C*K) (A+B) κ
    (mul_nonneg hC hK) hκ,eventually_gt_atTop (1:ℝ)] with X hp hX
  refine ⟨hX,?_⟩
  have hx : 0<X := by linarith
  have hl : 0<Real.log X := Real.log_pos hX
  apply (le_div_iff₀ (pow_pos hl A)).mpr
  have he : C*K*(1+Real.log X)^B*(Real.log X)^A≤X^κ := by
    calc
      _ ≤ C*K*(1+Real.log X)^B*(1+Real.log X)^A :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hl.le (by linarith) A) (by positivity)
      _ = C*K*(1+Real.log X)^(A+B) := by rw [pow_add]; ring
      _ ≤ _ := hp.2
  calc
    _ = X^(-κ)*(C*K*(1+Real.log X)^B*(Real.log X)^A) := by ring
    _ ≤ X^(-κ)*X^κ := mul_le_mul_of_nonneg_left he (by positivity)
    _ = 1 := by rw [←Real.rpow_add hx]; simp

def lowEnergy (X : ℝ) (lo hi : ℕ) (σ : ℝ) (F : ℝ→ℂ) : ℝ :=
  ∫t in Icc (-(X^(1/1000:ℝ))) (X^(1/1000:ℝ)),
    ‖F t*centeredFlat lo hi σ t‖^2

def nearEnergy (X a U : ℝ) (lo hi : ℕ) (σ : ℝ) (F : ℝ→ℂ) : ℝ :=
  ∫t in exceptional X (1/1000) a U, ‖F t*centeredFlat lo hi σ t‖^2

theorem eventually_low_and_near :
    ∃κ : ℝ, 0<κ ∧ κ≤1/1000 ∧ ∀ (C : ℝ) (A B : ℕ), 0≤C →
      ∀ᶠ X : ℝ in atTop, 1<X ∧
        ∀ (N lo hi : ℕ) (σ a U : ℝ) (F : ℝ→ℂ),
          X^(113/500:ℝ)≤(N:ℝ) → (N:ℝ)≤X →
          N≤lo → lo<hi → hi≤2*N → 1<σ → σ≤2 →
          0≤U → U≤X^κ → (∀t,‖F t‖≤1) →
          C*(1+Real.log X)^B*
            (lowEnergy X lo hi σ F+nearEnergy X a U lo hi σ F)
              ≤1/(Real.log X)^A := by
  obtain ⟨κ,hκ,hκρ,hnear⟩ := eventually_centered_exceptional
    (113/500) (1/1000) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨κ,hκ,hκρ,?_⟩
  intro C A B hC
  filter_upwards [hnear,absorb_power C 50 κ A B hC (by norm_num) hκ]
    with X hn hb
  refine ⟨hb.1,?_⟩
  intro N lo hi σ a U F hN hNX hlo hhi hhiN hσ hσ2 hU hUX hF
  have hN1 : 1≤N := by
    have hh := (Real.one_le_rpow hn.1 (by norm_num : (0:ℝ)≤113/500)).trans hN
    exact_mod_cast hh
  have hlow : lowEnergy X lo hi σ F≤32*X^(-449/1000:ℝ) := by
    have hh := low_energy X (113/500) (1/1000) hn.1 (by norm_num)
      N lo hi σ F hN1 hN hlo hhi hσ hσ2 (fun t _ => hF t)
    norm_num only [show (3*(1/1000:ℝ)-2*(113/500))= -449/1000 by norm_num] at hh
    simpa only [lowEnergy,neg_div] using hh
  have hh : nearEnergy X a U lo hi σ F≤18*X^(-κ) :=
    hn.2 N lo hi σ a U F hN hNX hlo hhi hhiN hσ.le hU hUX (fun t _ => hF t)
  have hsum : lowEnergy X lo hi σ F+nearEnergy X a U lo hi σ F≤50*X^(-κ) := by
    have hp : X^(-449/1000:ℝ)≤X^(-κ) :=
      Real.rpow_le_rpow_of_exponent_le hn.1 (by linarith)
    nlinarith
  exact (mul_le_mul_of_nonneg_left hsum (by have := Real.log_nonneg hn.1; positivity)).trans hb.2

theorem eventually_actual_mode_low_and_near :
    ∃κ : ℝ, 0<κ ∧ κ≤1/1000 ∧ ∀ (C : ℝ) (Aexp Bexp : ℕ), 0≤C →
      ∀ᶠ X : ℝ in atTop, 1<X ∧
        ∀ (s : ℝ) (i j d : ℕ) (ω : Fin 9→ℝ)
          (P A B : Finset ℕ) (Np Na Nb N lo hi : ℕ) (q : ℕ→ℕ→ℂ) (σ U : ℝ),
          1≤Np → 1≤Na → 1≤Nb →
          (∀p∈P,Np<p ∧ p≤2*Np) →
          (∀a∈A,Na<a ∧ a≤2*Na) → (∀b∈B,Nb<b ∧ b≤2*Nb) →
          (∀a∈A,∀b∈B,‖q a b‖≤1) →
          X^(113/500:ℝ)≤(N:ℝ) → (N:ℝ)≤X →
          N≤lo → lo<hi → hi≤2*N → 1<σ → σ≤2 → 0≤U → U≤X^κ →
          C*(1+Real.log X)^Bexp*
            (lowEnergy X lo hi σ (remainingFactor X s i j d ω P A B q σ) +
              nearEnergy X (-(shift ω primeSlope)) U lo hi σ
                (remainingFactor X s i j d ω P A B q σ))
            ≤1/(Real.log X)^Aexp := by
  obtain ⟨κ,hκ,hκρ,hh⟩ := eventually_low_and_near
  refine ⟨κ,hκ,hκρ,?_⟩
  intro C Aexp Bexp hC
  filter_upwards [hh C Aexp Bexp hC] with X hX
  refine ⟨hX.1,?_⟩
  intro s i j d ω P A B Np Na Nb N lo hi q σ U hNp hNa hNb hP hA hB hq
    hN hNX hlo hhi hhiN hσ hσ2 hU hUX
  exact hX.2 N lo hi σ (-(shift ω primeSlope)) U
    (remainingFactor X s i j d ω P A B q σ)
    hN hNX hlo hhi hhiN hσ hσ2 hU hUX
    (fun t => remainingFactor_cap X s i j d ω P A B Np Na Nb q σ t
      hNp hNa hNb hσ.le hP hA hB hq)

run_cmd do
  for decl in [``absorb_power, ``eventually_low_and_near,
      ``eventually_actual_mode_low_and_near] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
end OuterExceptionalBudgetWork
