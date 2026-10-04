import LogPhaseCancellation
import MonotoneWeight

/-!
Weighted logarithmic cancellation for flat Dirichlet polynomials. Partial
summation uses the decreasing weight x^(-sigma), uniformly for sigma >= 1.
The vertical complex-power identity comes from the frozen seed.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open scoped BigOperators

namespace FlatDirichlet

theorem weighted_log_cancellation (r : ℕ) (θ : ℝ)
    (hθ : 0 < θ) (hθone : θ ≤ 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ cutoff : ℕ, ∀ N M : ℕ,
      cutoff ≤ N → M ≤ N → ∀ a u σ : ℝ,
        (N : ℝ) ≤ a → a ≤ 2 * (N : ℝ) →
        (N : ℝ) ^ θ ≤ |u| → |u| ≤ (N : ℝ) ^ r → 1 ≤ σ →
        ‖∑ n ∈ Finset.range M,
          Erdos374.KusminLandau151.e (LogPhaseShape.phase u (a + n)) *
            (((a + n) ^ (-σ) : ℝ) : ℂ)‖ ≤ 10 * (N : ℝ) ^ (-δ) := by
  obtain ⟨δ, hδ, cutoff, hc⟩ :=
    LogPhaseCancellation.logarithmic_cancellation r θ hθ hθone
  refine ⟨δ, hδ, max 1 cutoff, ?_⟩
  intro N M hN hM a u σ ha haUpper huLow huHigh hσ
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hNOne : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hap : 0 < a := hNpos.trans_le ha
  have hw : ∀ n : ℕ, 0 ≤ (a + n) ^ (-σ) := fun n => Real.rpow_nonneg
    (by linarith [Nat.cast_nonneg (α := ℝ) n]) _
  have hm : Antitone (fun n : ℕ => (a + n) ^ (-σ)) := by
    intro m n hmn
    exact Real.rpow_le_rpow_of_nonpos
      (by linarith [Nat.cast_nonneg (α := ℝ) m])
      (add_le_add (le_refl a) (Nat.cast_le.mpr hmn)) (by linarith)
  have hh := MonotoneWeight.antitone_weight_bound M
    (fun n => Erdos374.KusminLandau151.e (LogPhaseShape.phase u (a + n)))
    (fun n => (a + n) ^ (-σ)) (10 * (N : ℝ) ^ (-δ) * (N : ℝ))
    (by positivity) hw hm
    (fun m hm => hc N m (by omega) (hm.trans hM) a u ha haUpper huLow huHigh)
  have hw0 : a ^ (-σ) ≤ (N : ℝ)⁻¹ := by
    calc
      _ ≤ (N : ℝ) ^ (-σ) := Real.rpow_le_rpow_of_nonpos hNpos ha (by linarith)
      _ ≤ (N : ℝ) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hNOne (by linarith)
      _ = _ := Real.rpow_neg_one _
  simp only [Nat.cast_zero, add_zero] at hh
  calc
    _ ≤ (10 * (N : ℝ) ^ (-δ) * (N : ℝ)) * a ^ (-σ) := hh
    _ ≤ (10 * (N : ℝ) ^ (-δ) * (N : ℝ)) * (N : ℝ)⁻¹ :=
      mul_le_mul_of_nonneg_left hw0 (by positivity)
    _ = _ := by rw [mul_assoc, mul_inv_cancel₀ hNpos.ne', mul_one]

theorem kernel_log_phase (x t : ℝ) :
    Erdos374.HarmanAnalytic151MeanSquare.exponentialKernel151 (Real.log x) (-t) =
      Erdos374.KusminLandau151.e
        (LogPhaseShape.phase (-t / (2 * Real.pi)) x) := by
  unfold Erdos374.HarmanAnalytic151MeanSquare.exponentialKernel151
    Erdos374.KusminLandau151.e LogPhaseShape.phase
  congr 1
  push_cast
  field_simp

theorem vertical_term (n : ℕ) (hn : 0 < n) (σ t : ℝ) :
    (n : ℂ) ^ (-((σ : ℂ) + Complex.I * (t : ℂ))) =
      Erdos374.KusminLandau151.e
        (LogPhaseShape.phase (-t / (2 * Real.pi)) n) *
          (((n : ℝ) ^ (-σ) : ℝ) : ℂ) := by
  rw [Erdos374.HarmanGram152.cpow_vertical_factor152 hn σ t, kernel_log_phase,
    Real.rpow_neg (by exact_mod_cast hn.le : (0 : ℝ) ≤ n), Complex.ofReal_inv]
  exact mul_comm _ _

/-- Flat polynomial on any integer subinterval of (N,2N], with the exact
vertical frequency t. This is uniform in sigma >= 1 and in both endpoints. -/
theorem flat_interval_cancellation (r : ℕ) (θ : ℝ)
    (hθ : 0 < θ) (hθone : θ ≤ 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ cutoff : ℕ, ∀ N lo hi : ℕ,
      cutoff ≤ N → N ≤ lo → hi ≤ 2 * N → ∀ t σ : ℝ,
        (N : ℝ) ^ θ ≤ |-t / (2 * Real.pi)| →
        |-t / (2 * Real.pi)| ≤ (N : ℝ) ^ r → 1 ≤ σ →
        ‖Erdos374.HarmanGram152.verticalDirichlet152
          (Finset.Ioc lo hi) (fun _ => 1) σ t‖ ≤ 10 * (N : ℝ) ^ (-δ) := by
  obtain ⟨δ, hδ, cutoff, hc⟩ := weighted_log_cancellation r θ hθ hθone
  refine ⟨δ, hδ, max 1 cutoff, ?_⟩
  intro N lo hi hN hlo hhi t σ huLow huHigh hσ
  have hNpos : 0 < N := by omega
  by_cases hempty : hi ≤ lo
  · simp only [Erdos374.HarmanGram152.verticalDirichlet152,
      Finset.Ioc_eq_empty_of_le hempty, Finset.sum_empty, norm_zero]
    positivity
  · have hset : Finset.Ioc lo hi = Finset.Ico (lo + 1) (hi + 1) := by
      ext d
      simp only [Finset.mem_Ioc, Finset.mem_Ico]
      omega
    unfold Erdos374.HarmanGram152.verticalDirichlet152
    rw [hset, Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_add_right, one_mul]
    have hh := hc N (hi - lo) (by omega) (by omega) ((lo : ℝ) + 1)
      (-t / (2 * Real.pi)) σ
      (by exact_mod_cast (show N ≤ lo + 1 by omega))
      (by exact_mod_cast (show lo + 1 ≤ 2 * N by omega)) huLow huHigh hσ
    convert hh using 1
    congr 1
    apply Finset.sum_congr rfl
    intro n hn
    rw [vertical_term _ (by omega)]
    push_cast
    congr 2

/-- The same estimate with the amplitude stated in the ordinary frequency
t, absorbing the fixed Fourier normalization into the cutoff. -/
theorem flat_frequency_cancellation (r : ℕ) (θ : ℝ)
    (hθ : 0 < θ) (hθone : θ ≤ 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ cutoff : ℕ, ∀ N lo hi : ℕ,
      cutoff ≤ N → N ≤ lo → hi ≤ 2 * N → ∀ t σ : ℝ,
        (N : ℝ) ^ θ ≤ |t| → |t| ≤ (N : ℝ) ^ r → 1 ≤ σ →
        ‖Erdos374.HarmanGram152.verticalDirichlet152
          (Finset.Ioc lo hi) (fun _ => 1) σ t‖ ≤ 10 * (N : ℝ) ^ (-δ) := by
  obtain ⟨δ, hδ, cutoff, hc⟩ := flat_interval_cancellation r (θ / 2)
    (by positivity) (by linarith)
  obtain ⟨constantCutoff, hconstant⟩ :=
    PowerDifferenceParameters.eventually_log_le_power (2 * Real.pi) (θ / 2)
      (by positivity) (by positivity)
  refine ⟨δ, hδ, max 1 (max cutoff constantCutoff), ?_⟩
  intro N lo hi hN hlo hhi t σ htLow htHigh hσ
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 ≤ Real.log ((N : ℝ) + 1) :=
    Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) N; linarith)
  have hcpos : 0 < 2 * Real.pi := by positivity
  have hcone : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hcbound : 2 * Real.pi ≤ (N : ℝ) ^ (θ / 2) := by
    have hh := hconstant N (by omega)
    nlinarith
  have habs : |-t / (2 * Real.pi)| = |t| / (2 * Real.pi) := by
    rw [abs_div, abs_neg, abs_of_pos hcpos]
  apply hc N lo hi (by omega) hlo hhi t σ _ _ hσ
  · rw [habs]
    apply (le_div_iff₀ hcpos).mpr
    calc
      _ ≤ (N : ℝ) ^ (θ / 2) * (N : ℝ) ^ (θ / 2) :=
        mul_le_mul_of_nonneg_left hcbound (by positivity)
      _ = (N : ℝ) ^ θ := by rw [← Real.rpow_add hNpos]; congr 1; ring
      _ ≤ _ := htLow
  · rw [habs]
    exact (div_le_self (abs_nonneg t) hcone).trans htHigh

end FlatDirichlet

#print axioms FlatDirichlet.flat_interval_cancellation
run_cmd do
  for target in [``FlatDirichlet.weighted_log_cancellation,
      ``FlatDirichlet.vertical_term, ``FlatDirichlet.flat_interval_cancellation,
      ``FlatDirichlet.flat_frequency_cancellation] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "FLAT DIRICHLET PASSED"
