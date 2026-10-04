import SieveWeightedCutoffs
import SieveFullCutoffTransfer

/-! The fourth source cutoff can exceed its outer prime near the lower
endpoint. Cap it at that prime and pay for the entire exceptional strip.
No monotonicity of the actual upper selector in its cutoff is assumed. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open Real Filter
open scoped BigOperators Topology
namespace SieveCappedUpperMainTerms
open SieveWeightedScalarBudget SieveWeightedCutoffs SieveStoppingExpansion

def cappedFourth (X s p : ℝ) : ℝ := min p (cutoffFour X s p)

def stripBudget (s t : ℝ) : ℝ :=
  (452/375)*(log ((upperExponent s/3)/alpha s)+10*t/alpha s)

theorem fullUpper_nonneg (T z : ℝ) : 0 ≤ SieveFullCutoffTransfer.fullUpper T z := by
  rw [SieveFullCutoffTransfer.fullUpper_eq_mass]
  exact (SieveReciprocalModel.euler_positive _ (SieveSmallWeights.primes_prime z)).le.trans
    (SieveReciprocalModel.mass_bounds (SieveRosser.cubicGate T) 1 _
      (SieveSmallWeights.primes_nodup z) (SieveSmallWeights.primes_prime z)).2

theorem three_le_prime (X s p : ℝ) (hX : 1 < X) (hs : 0 ≤ s)
    (hplo : X^(9/35:ℝ) ≤ p) : cutoffThree X s p ≤ p := by
  have hX0 : 0 < X := by linarith
  have hp : 0 < p := (rpow_pos_of_pos hX0 _).trans_le hplo
  have hlo := log_le_log (rpow_pos_of_pos hX0 (9/35:ℝ)) hplo
  rw [log_rpow hX0] at hlo
  have hsn := mul_nonneg hs (log_pos hX).le
  apply (log_le_log_iff (three_pos X s p hX0 hp) hp).mp
  rw [log_three X s p hX0 hp]
  nlinarith [log_pos hX]

theorem capped_le_prime (X s p : ℝ) : cappedFourth X s p ≤ p := min_le_left _ _

theorem capped_geometry (X s p : ℝ) (hX : 1 < X)
    (hs : 0 ≤ s) (hs1 : s ≤ 1/1000)
    (hplo : X^alpha s ≤ p) (hphi : p ≤ X^(9/35:ℝ)) :
    X^(1/7:ℝ) ≤ cappedFourth X s p ∧
      cappedFourth X s p ≤ p ∧ cappedFourth X s p^3 ≤ level X s/p := by
  have hX0 : 0 < X := by linarith
  have hpa : X^(1/7:ℝ) ≤ p :=
    (rpow_le_rpow_of_exponent_le hX.le (by
      have hh := (exponent_geometry s hs hs1).1
      linarith : (1/7:ℝ) ≤ alpha s)).trans hplo
  have hg := four_geometry X s p hX hs hs1 hplo hphi
  have hlo : X^(1/7:ℝ) ≤ cappedFourth X s p := le_min hpa hg.1
  refine ⟨hlo, capped_le_prime X s p, ?_⟩
  have hc0 : 0 ≤ cappedFourth X s p := (rpow_pos_of_pos hX0 _).le.trans hlo
  exact (pow_le_pow_left₀ hc0 (min_le_right p (cutoffFour X s p)) 3).trans hg.2.2

theorem changed_prime_upper (X s p : ℝ) (hX : 1 < X)
    (hp : 0 < p) (hchange : p < cutoffFour X s p) :
    p < X^(upperExponent s/3) := by
  have hX0 : 0 < X := by linarith
  have hh := log_lt_log hp hchange
  rw [log_four X s p hX0 hp] at hh
  apply (log_lt_log_iff hp (rpow_pos_of_pos hX0 _)).mp
  rw [log_rpow hX0]
  linarith

theorem strip_prime_bound (X s : ℝ) (S : Finset ℕ) (hX : 1 < X)
    (hs : 0 ≤ s) (hs1 : s ≤ 1/1000)
    (hS : ∀ p ∈ S, p.Prime ∧ X^alpha s ≤ (p:ℝ) ∧ (p:ℝ) ≤ X^(9/35:ℝ)) :
    (∑ p ∈ S.filter (fun p : ℕ => (p:ℝ) < cutoffFour X s p), (p:ℝ)⁻¹) ≤
      log ((upperExponent s/3)/alpha s)+10/(alpha s*log X) := by
  classical
  have hX0 : 0 < X := by linarith
  have ha : 0 < alpha s := by
    have hh := (exponent_geometry s hs hs1).1
    linarith
  have hab : alpha s ≤ upperExponent s/3 := by unfold alpha upperExponent; linarith
  have hh := MertensPrimeInterval.prime_reciprocal_interval
    (X^alpha s) (X^(upperExponent s/3))
    (S.filter (fun p : ℕ => (p:ℝ) < cutoffFour X s p)) (one_lt_rpow hX ha)
    (rpow_le_rpow_of_exponent_le hX.le hab) (fun p hp => by
      obtain ⟨hpS, hpc⟩ := Finset.mem_filter.mp hp
      obtain ⟨hpp, hlo, _⟩ := hS p hpS
      have hp0 : 0 < (p:ℝ) := (rpow_pos_of_pos hX0 _).trans_le hlo
      exact ⟨hpp, hlo, (changed_prime_upper X s p hX hp0 hpc).le⟩)
  simp only [log_rpow hX0] at hh
  have hid : ((upperExponent s/3)*log X)/(alpha s*log X) =
      (upperExponent s/3)/alpha s := by
    field_simp [(log_pos hX).ne', ha.ne']
  rwa [hid] at hh

/-- Pay for changed primes separately; the old upper mass is nonnegative. -/
theorem capped_sum_le (X s Z : ℝ) (S : Finset ℕ) (hX : 1 < X)
    (hs : 0 ≤ s) (hs1 : s ≤ 1/1000)
    (hZ : Z ≤ X^(1/7:ℝ))
    (hupper : ∀ z T : ℝ, Z ≤ z → z^3 ≤ T →
      SieveFullCutoffTransfer.fullUpper T z ≤ (452/375:ℝ)*primeEuler z)
    (hS : ∀ p ∈ S, p.Prime ∧ X^alpha s ≤ (p:ℝ) ∧ (p:ℝ) ≤ X^(9/35:ℝ)) :
    (∑ p ∈ S, (p:ℝ)⁻¹*SieveFullCutoffTransfer.fullUpper
      (level X s/(p:ℝ)) (cappedFourth X s p)) ≤
      (∑ p ∈ S, (p:ℝ)⁻¹*SieveFullCutoffTransfer.fullUpper
        (level X s/(p:ℝ)) (cutoffFour X s p))+
        stripBudget s (1/log X)*primeEuler (X^alpha s) := by
  classical
  let V := primeEuler (X^alpha s)
  let raw := fun p : ℕ => (p:ℝ)⁻¹*SieveFullCutoffTransfer.fullUpper
    (level X s/(p:ℝ)) (cutoffFour X s p)
  let extra := fun p : ℕ => if (p:ℝ) < cutoffFour X s p then
    (452/375:ℝ)*V*(p:ℝ)⁻¹ else 0
  have hpwise : ∀ p ∈ S, (p:ℝ)⁻¹*SieveFullCutoffTransfer.fullUpper
      (level X s/(p:ℝ)) (cappedFourth X s p) ≤ raw p+extra p := by
    intro p hp
    have hraw : 0 ≤ raw p := mul_nonneg (by positivity) (fullUpper_nonneg _ _)
    by_cases hc : (p:ℝ) < cutoffFour X s p
    · have heq : cappedFourth X s p = (p:ℝ) := min_eq_left hc.le
      obtain ⟨hlo, _, hlev⟩ := capped_geometry X s p hX hs hs1
        (hS p hp).2.1 (hS p hp).2.2
      have hu := hupper _ _ (hZ.trans hlo) hlev
      rw [heq] at hu
      have hv := SieveFiniteBase.euler_antitone (X^alpha s) (p:ℝ) (hS p hp).2.1
      have hub : SieveFullCutoffTransfer.fullUpper (level X s/(p:ℝ)) (p:ℝ) ≤
          (452/375:ℝ)*V := hu.trans (mul_le_mul_of_nonneg_left hv (by norm_num))
      rw [heq]
      have hm := mul_le_mul_of_nonneg_left hub (show 0 ≤ (p:ℝ)⁻¹ by positivity)
      simp only [extra, hc, ite_true]
      nlinarith
    · simp only [cappedFourth, min_eq_right (le_of_not_gt hc), extra, hc, ite_false,
        add_zero, raw, le_refl]
  have heq : (∑ p ∈ S, extra p) =
      ((452/375:ℝ)*V)*(∑ p ∈ S.filter (fun p : ℕ => (p:ℝ) < cutoffFour X s p), (p:ℝ)⁻¹) := by
    rw [Finset.sum_filter, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    by_cases hc : (p:ℝ) < cutoffFour X s p <;> simp [extra, hc]
  have hbound := mul_le_mul_of_nonneg_left (strip_prime_bound X s S hX hs hs1 hS)
    (show 0 ≤ (452/375:ℝ)*V from mul_nonneg (by norm_num) (SieveEulerRatio.euler_pos _).le)
  have hh := Finset.sum_le_sum hpwise
  rw [Finset.sum_add_distrib, heq] at hh
  have hend : ((452/375:ℝ)*V)*(log ((upperExponent s/3)/alpha s)+10/(alpha s*log X)) =
      stripBudget s (1/log X)*primeEuler (X^alpha s) := by
    unfold stripBudget V
    simp only [div_eq_mul_inv, mul_inv_rev, one_mul]
    ring
  exact hh.trans (add_le_add le_rfl (hbound.trans_eq hend))

theorem stripBudget_zero : stripBudget 0 0 = 0 := by
  norm_num [stripBudget, upperExponent, alpha]

theorem stripBudget_continuous :
    ContinuousAt (fun p : ℝ × ℝ => stripBudget p.1 p.2) (0, 0) := by
  unfold stripBudget upperExponent alpha
  fun_prop (disch := norm_num)

theorem eventually_strip_small :
    ∃ δ X₀ : ℝ, 0 < δ ∧ 1 < X₀ ∧ ∀ s X : ℝ, |s| < δ → X₀ ≤ X →
      stripBudget s (1/log X) ≤ (1847/5355000:ℝ) := by
  have he := stripBudget_continuous.eventually_lt_const
    (show stripBudget 0 0 < (1847/5355000:ℝ) by rw [stripBudget_zero]; norm_num)
  obtain ⟨δ, hδ, hb⟩ := Metric.eventually_nhds_iff.mp he
  have ht : Tendsto (fun X : ℝ => 1/log X) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_log_atTop
  have hta : Tendsto (fun X : ℝ => |1/log X|) atTop (𝓝 (0:ℝ)) := by
    simpa only [abs_zero] using ht.abs
  have ha : ∀ᶠ X : ℝ in atTop, |1/log X| < δ := hta.eventually_lt_const hδ
  obtain ⟨A, hA⟩ := eventually_atTop.mp ha
  refine ⟨δ, max 2 A, hδ, lt_of_lt_of_le (by norm_num : (1:ℝ) < 2)
    (le_max_left _ _), ?_⟩
  intro s X hs hX
  apply (hb (y := (s, 1/log X)) ?_).le
  simpa only [Prod.dist_eq, Real.dist_eq, sub_zero] using
    max_lt hs (hA X ((le_max_right _ _).trans hX))

run_cmd do
  for decl in [``fullUpper_nonneg, ``three_le_prime, ``capped_le_prime,
      ``capped_geometry, ``changed_prime_upper, ``strip_prime_bound,
      ``capped_sum_le, ``stripBudget_zero, ``stripBudget_continuous,
      ``eventually_strip_small] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "FOURTH CUTOFF CAPPED AT OUTER PRIME; ACTUAL THIN-STRIP COST RETAINED"
end SieveCappedUpperMainTerms
end
