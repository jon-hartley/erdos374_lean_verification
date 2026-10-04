import DifferenceParameters

/-!
Power savings from the same balanced finite-difference parameters used by
DifferenceParameters. A power window for the actual derivative scale is
enough; every auxiliary size condition is proved eventually.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Filter
open scoped BigOperators

namespace PowerDifferenceParameters
open Erdos374.HigherDifference152

theorem eventually_log_le_power (C η : ℝ) (hC : 0 ≤ C) (hη : 0 < η) :
    ∃ cutoff : ℕ, ∀ N : ℕ, cutoff ≤ N →
      C * (1 + Real.log ((N : ℝ) + 1)) ≤ (N : ℝ) ^ η := by
  have hlimit : Tendsto
      (fun x : ℝ => (3 * C) * Real.log x / x ^ η) atTop (nhds 0) := by
    simpa only [Real.rpow_one, mul_zero, mul_div_assoc] using
      (Real.tendsto_pow_log_div_pow_atTop η 1 hη).const_mul (3 * C)
  obtain ⟨threshold, hthreshold⟩ := eventually_atTop.mp
    (hlimit.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)))
  obtain ⟨cutoff, hcutoff⟩ := exists_nat_ge threshold
  obtain ⟨logCutoff, hlogCutoff⟩ :=
    Erdos374.RemainingAnalytic115.RemainingAnalytic127.eventually_log_ge127 1
  refine ⟨max 2 (max cutoff logCutoff), ?_⟩
  intro N hN
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast (show 2 ≤ N by omega)
  have hpos : (0 : ℝ) < N := by linarith
  have hlog := hlogCutoff N (by omega)
  have hnext := Real.log_le_log (by positivity : (0 : ℝ) < (N : ℝ) + 1)
    (show (N : ℝ) + 1 ≤ (N : ℝ) ^ 2 by nlinarith)
  rw [Real.log_pow] at hnext
  norm_num at hnext
  have hsmall := hthreshold (N : ℝ)
    (hcutoff.trans (Nat.cast_le.mpr (show cutoff ≤ N by omega)))
  have hbound : (3 * C) * Real.log (N : ℝ) ≤ (N : ℝ) ^ η :=
    ((div_lt_one (Real.rpow_pos_of_pos hpos η)).mp hsmall).le
  have hprod := mul_le_mul_of_nonneg_left
    (show 1 + Real.log ((N : ℝ) + 1) ≤ 3 * Real.log (N : ℝ) by linarith) hC
  nlinarith only [hprod, hbound]

/-- Uniform polynomial saving for actual finite differences whose balanced
scale lies between two fixed positive powers of the ambient length. -/
theorem cancellation_power_window (r : ℕ) (C η : ℝ)
    (hC : 1 ≤ C) (hη : 0 < η) (hηhalf : η ≤ 1 / 2) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ cutoff : ℕ, ∀ N M : ℕ,
      cutoff ≤ N → M ≤ N → ∀ scale : ℝ,
        (N : ℝ) ^ η ≤ scale → scale ≤ (N : ℝ) ^ (1 - η) →
        ∀ f : ℕ → ℝ,
          (∀ n < M,
            scale ^ (r + 1) / (N : ℝ) ^ (r + 2) ≤ difference (r + 2) f n ∧
            difference (r + 2) f n ≤
              C * (scale ^ (r + 1) / (N : ℝ) ^ (r + 2))) →
          (MonotoneOn (difference (r + 2) f) (Set.Iio M) ∨
            AntitoneOn (difference (r + 2) f) (Set.Iio M)) →
          ‖∑ n ∈ Finset.range M, Erdos374.KusminLandau151.e (f n)‖ ≤
            10 * (N : ℝ) ^ (-δ) * (N : ℝ) := by
  let d : ℝ := η / (r + 3)
  let δ : ℝ := d / ((2 ^ r : ℕ) : ℝ)
  have hd : 0 < d := by dsimp [d]; positivity
  have hdη : d < η := by
    dsimp [d]
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < (r : ℝ) + 3)).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) r]
  have hd1 : d < 1 := by linarith
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨NU, hNU⟩ := eventually_log_le_power 4 (η - d) (by norm_num) (by linarith)
  obtain ⟨NA, hNA⟩ := eventually_log_le_power (32 * C) (1 - d)
    (by positivity) (by linarith)
  obtain ⟨NL, hNL⟩ := eventually_log_le_power (64 * C * (4 : ℝ) ^ r) d
    (by positivity) hd
  refine ⟨δ, hδ, max 1 (max NU (max NA NL)), ?_⟩
  intro N M hN hM scale hsLower hsUpper f hdiff hmono
  have hNpos : 0 < N := by omega
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hNpos
  have hNone : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hscale : 1 ≤ scale := (Real.one_le_rpow hNone hη.le).trans hsLower
  have heps : 0 < (N : ℝ) ^ (-δ) := Real.rpow_pos_of_pos hNr _
  have hepsOne : (N : ℝ) ^ (-δ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hNone (by linarith)
  have hepsPow : ((N : ℝ) ^ (-δ)) ^ (2 ^ r) = (N : ℝ) ^ (-d) := by
    rw [← Real.rpow_mul_natCast hNr.le]
    congr 1
    dsimp [δ]
    field_simp
  have hlog : 0 ≤ Real.log ((N : ℝ) + 1) := Real.log_nonneg (by linarith)
  have hfour : (4 : ℝ) ≤ (N : ℝ) ^ (η - d) := by
    have hh := hNU N (by omega)
    nlinarith
  have hupper : 4 * scale ≤ (N : ℝ) * ((N : ℝ) ^ (-δ)) ^ (2 ^ r) := by
    rw [hepsPow]
    calc
      _ ≤ (N : ℝ) ^ (η - d) * (N : ℝ) ^ (1 - η) :=
        mul_le_mul hfour hsUpper (by linarith) (by positivity)
      _ = (N : ℝ) * (N : ℝ) ^ (-d) := by
        rw [← Real.rpow_add hNr, show η - d + (1 - η) = 1 + -d by ring,
          Real.rpow_add hNr, Real.rpow_one]
  have hambient : 32 * C * (1 + Real.log ((N : ℝ) + 1)) ≤
      (N : ℝ) * ((N : ℝ) ^ (-δ)) ^ (2 ^ r) := by
    rw [hepsPow]
    convert hNA N (by omega) using 1
    rw [sub_eq_add_neg, Real.rpow_add hNr, Real.rpow_one]
  have hlower : 64 * C * (1 + Real.log ((N : ℝ) + 1)) * (4 : ℝ) ^ r ≤
      scale * (((N : ℝ) ^ (-δ)) ^ (2 ^ r)) ^ (r + 2) := by
    rw [hepsPow]
    calc
      _ ≤ (N : ℝ) ^ d := by convert hNL N (by omega) using 1; ring
      _ = (N : ℝ) ^ η * ((N : ℝ) ^ (-d)) ^ (r + 2) := by
        rw [← Real.rpow_mul_natCast hNr.le, ← Real.rpow_add hNr]
        congr 1
        dsimp [d]
        push_cast
        field_simp
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hsLower (by positivity)
  exact DifferenceParameters.balanced_scale_cancellation r M N f scale C
    ((N : ℝ) ^ (-δ)) hNpos hM hscale hC heps hepsOne hupper hambient hlower
    hdiff hmono

end PowerDifferenceParameters

#print axioms PowerDifferenceParameters.cancellation_power_window
run_cmd do
  for target in [``PowerDifferenceParameters.eventually_log_le_power,
      ``PowerDifferenceParameters.cancellation_power_window] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "POWER DIFFERENCE PARAMETERS PASSED"
