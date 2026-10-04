import FlatDirichlet

/-!
Express flat Dirichlet cancellation in a larger ambient scale X. This is
the form relevant to Harman's equation (13), with the lower frequency
bound stated explicitly and proved sufficient here.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Filter
open scoped BigOperators

namespace FlatDirichletScale

/-- For fixed positive length and frequency exponents, every flat polynomial
of length between X^epsilon and X has a power saving throughout
X^rho <= |t| <= X. The result is uniform over sigma >= 1 and truncations. -/
theorem ambient_power_saving (ε ρ : ℝ) (hε : 0 < ε)
    (hρ : 0 < ρ) (hρone : ρ ≤ 1) :
    ∃ κ : ℝ, 0 < κ ∧ ∃ X₀ : ℝ, 1 ≤ X₀ ∧ ∀ X : ℝ, X₀ ≤ X →
      ∀ N lo hi : ℕ, X ^ ε ≤ (N : ℝ) → (N : ℝ) ≤ X →
        N ≤ lo → hi ≤ 2 * N → ∀ t σ : ℝ,
          X ^ ρ ≤ |t| → |t| ≤ X → 1 ≤ σ →
          ‖Erdos374.HarmanGram152.verticalDirichlet152
            (Finset.Ioc lo hi) (fun _ => 1) σ t‖ ≤ 10 * X ^ (-κ) := by
  let r : ℕ := ⌈1 / ε⌉₊
  have hr : 1 / ε ≤ (r : ℝ) := Nat.le_ceil _
  have hproduct : 1 ≤ ε * (r : ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hr hε.le
    have heq : ε * (1 / ε) = 1 := by field_simp
    rwa [heq] at hh
  obtain ⟨δ, hδ, cutoff, hc⟩ :=
    FlatDirichlet.flat_frequency_cancellation r ρ hρ hρone
  obtain ⟨threshold, hthreshold⟩ := eventually_atTop.mp
    ((tendsto_rpow_atTop hε).eventually (eventually_ge_atTop (cutoff : ℝ)))
  refine ⟨ε * δ, mul_pos hε hδ, max 1 threshold, le_max_left _ _, ?_⟩
  intro X hX N lo hi hNlower hNupper hlo hhi t σ htLower htUpper hσ
  have hXone : 1 ≤ X := (le_max_left _ _).trans hX
  have hXpos : 0 < X := by linarith
  have hNpos : (0 : ℝ) < N := (Real.rpow_pos_of_pos hXpos ε).trans_le hNlower
  have hcutoff : cutoff ≤ N := by
    have hh : (cutoff : ℝ) ≤ N :=
      (hthreshold X ((le_max_right _ _).trans hX)).trans hNlower
    exact_mod_cast hh
  have htNlower : (N : ℝ) ^ ρ ≤ |t| :=
    (Real.rpow_le_rpow hNpos.le hNupper hρ.le).trans htLower
  have htNupper : |t| ≤ (N : ℝ) ^ r := by
    calc
      _ ≤ X := htUpper
      _ = X ^ (1 : ℝ) := (Real.rpow_one X).symm
      _ ≤ X ^ (ε * (r : ℝ)) := Real.rpow_le_rpow_of_exponent_le hXone hproduct
      _ = (X ^ ε) ^ r := Real.rpow_mul_natCast hXpos.le _ _
      _ ≤ _ := pow_le_pow_left₀ (Real.rpow_nonneg hXpos.le ε) hNlower r
  calc
    _ ≤ 10 * (N : ℝ) ^ (-δ) := hc N lo hi hcutoff hlo hhi t σ htNlower htNupper hσ
    _ ≤ 10 * (X ^ ε) ^ (-δ) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hXpos ε)
        hNlower (by linarith)
    _ = 10 * X ^ (-(ε * δ)) := by
      rw [← Real.rpow_mul hXpos.le]
      congr 2
      ring

end FlatDirichletScale

#print axioms FlatDirichletScale.ambient_power_saving
run_cmd do
  let axioms ← Lean.collectAxioms ``FlatDirichletScale.ambient_power_saving
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"
  Lean.logInfo "FLAT DIRICHLET SCALE PASSED"
