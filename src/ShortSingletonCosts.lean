import ShortSingletonMasks
import FourPrimeGlobalPartition

/-! The actual Fourier coefficient mass and dyadic family cost are uniformly
subpower. No bound by the number of Fourier frequencies is used. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open Filter
open scoped BigOperators

namespace ShortSingletonCosts
open ShortSingletonMasks

theorem scalar_mass_le_ambient (X : ℝ) (Q : ℕ) (hX : 1 ≤ X) (hQ : (Q : ℝ) ≤ X) :
    (∑ t : Mode Q, ‖scalar Q t‖) ≤ 12*(1+Real.log X)^2 := by
  have hlog : 0 ≤ Real.log X := Real.log_nonneg hX
  have hQlog : Real.log Q ≤ Real.log X := by
    by_cases hz : Q = 0
    · simpa only [hz, Nat.cast_zero, Real.log_zero] using hlog
    · exact Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hz) hQ
  have hQnonneg : 0 ≤ Real.log (Q : ℝ) := by
    by_cases hz : Q = 0
    · simp [hz]
    · exact Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hz)
  calc
    _ ≤ 2*(2+Real.log Q)*(3+Real.log Q) := scalar_mass_le_log Q
    _ ≤ 2*(2+Real.log X)*(3+Real.log X) := by gcongr
    _ ≤ _ := by nlinarith [sq_nonneg (Real.log X)]

theorem eventually_scalar_mass_cap (C δ : ℝ) (hC : 0 ≤ C) (hδ : 0 < δ) :
    ∀ᶠ X : ℝ in atTop, 1 ≤ X ∧ ∀ Q : ℕ, (Q : ℝ) ≤ X →
      C*(∑ t : Mode Q, ‖scalar Q t‖) ≤ X^δ := by
  filter_upwards [PolynomialLogEnvelope.eventually_bound (12*C) 2 δ (by positivity) hδ]
    with X hX
  refine ⟨hX.1, ?_⟩
  intro Q hQ
  calc
    _ ≤ C*(12*(1+Real.log X)^2) := mul_le_mul_of_nonneg_left
      (scalar_mass_le_ambient X Q hX.1 hQ) hC
    _ = (12*C)*(1+Real.log X)^2 := by ring
    _ ≤ _ := hX.2

theorem eventually_total_mass_cap (C δ : ℝ) (hC : 0 ≤ C) (hδ : 0 < δ) :
    ∀ᶠ X : ℝ in atTop, 1 ≤ X ∧ ∀ (S T : Finset ℕ) (Q : ℕ), (Q : ℝ) ≤ X →
      C*((FourPrimePartition.family S T 1 1 (FourPrimeGlobalPartition.k X)
        (FourPrimeGlobalPartition.k X)).card : ℝ)*
        (∑ t : Mode Q, ‖scalar Q t‖) ≤ X^δ := by
  filter_upwards [eventually_scalar_mass_cap C (δ/2) hC (by positivity),
    FourPrimeGlobalPartition.eventually_all_family_cost δ hδ] with X hmass hfamily
  refine ⟨hmass.1, ?_⟩
  intro S T Q hQ
  have hXp : 0 < X := by linarith [hmass.1]
  calc
    _ = (C*(∑ t : Mode Q, ‖scalar Q t‖))*
        ((FourPrimePartition.family S T 1 1 (FourPrimeGlobalPartition.k X)
          (FourPrimeGlobalPartition.k X)).card : ℝ) := by ring
    _ ≤ X^(δ/2)*X^(δ/2) := mul_le_mul (hmass.2 Q hQ) (hfamily.2 S T)
      (Nat.cast_nonneg _) (by positivity)
    _ = _ := by rw [←Real.rpow_add hXp]; congr 1; ring

theorem eventually_absorb_square_cost (c : ℝ) (hc : 0 < c) :
    ∀ᶠ X : ℝ in atTop, 1 ≤ X ∧ ∀ T W Y : ℝ,
      0 ≤ T → T ≤ X^(c/16) → 0 ≤ W → W ≤ X^(c/16) →
      4*T^2*W^2*Y^2*X^(-c) ≤ Y^2*X^(-(c/2)) := by
  filter_upwards [PolynomialLogEnvelope.eventually_constant_bound 4 (c/4)
    (by norm_num) (by positivity)] with X hX
  refine ⟨hX.1, ?_⟩
  intro T W Y hT hTcap hW hWcap
  have hXp : 0 < X := by linarith [hX.1]
  calc
    _ ≤ X^(c/4)*(X^(c/16))^2*(X^(c/16))^2*Y^2*X^(-c) := by
      gcongr
      exact hX.2
    _ = Y^2*X^(-(c/2)) := by
      rw [←Real.rpow_mul_natCast hXp.le]
      norm_num only [Nat.cast_ofNat]
      calc
        _ = Y^2*(X^(c/4)*X^((c/16)*2)*X^((c/16)*2)*X^(-c)) := by ring
        _ = _ := by
          rw [←Real.rpow_add hXp, ←Real.rpow_add hXp, ←Real.rpow_add hXp]
          congr 2
          ring

run_cmd do
  for decl in [``scalar_mass_le_ambient, ``eventually_scalar_mass_cap,
      ``eventually_total_mass_cap, ``eventually_absorb_square_cost] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "UNIFORM FOURIER AND DYADIC SUBPOWER COST ABSORPTION PASSED"

end ShortSingletonCosts
