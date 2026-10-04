import SieveThinPrimeInterval
import SieveBoxedFamily

/-! Actual finite prime subsets sharing one assigned geometric band have
small reciprocal mass. The band endpoints and its lower cutoff are proved. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators
open Real

namespace SievePrimeBandMass

def eta (D s : ℝ) : ℝ := s^9+10/(s^2*log D)

theorem eta_nonneg (D s : ℝ) (hD : 1 < D) (hs : 0 < s) : 0 ≤ eta D s := by
  have hl : 0 < log D := log_pos hD
  unfold eta
  positivity

theorem common_band_bound (D s z : ℝ) (S : Finset ℕ) (i : ℕ)
    (hD : 1 < D) (hs : 0 < s) (hz : z ≤ D)
    (hS : ∀ p ∈ S, p ∈ SieveBoxedFamily.pool D s z ∧
      SieveBoxTuples.boxIndex D s (p:ℝ) = i) :
    ∑ p ∈ S, (p:ℝ)⁻¹ ≤ eta D s := by
  have hD0 : 0 < D := by linarith
  have hu : 1 < D^(s^2) := Real.one_lt_rpow hD (sq_pos_of_pos hs)
  have hq : 1 < SieveGeometricGrid.ratio s := SieveGeometricGrid.one_lt_ratio s hs
  have hua : D^(s^2) ≤ SieveGeometricGrid.scale D s i := by
    rw [← SieveGeometricGrid.scale_zero D s]
    exact (SieveGeometricGrid.scale_strictMono D s hD hs).monotone (Nat.zero_le i)
  have hinterval : ∀ p ∈ S, p.Prime ∧ SieveGeometricGrid.scale D s i ≤ (p:ℝ) ∧
      (p:ℝ) ≤ (SieveGeometricGrid.scale D s i)^SieveGeometricGrid.ratio s := by
    intro p hp
    obtain ⟨hpool, hi⟩ := hS p hp
    obtain ⟨hprime, hpz, hpu⟩ := (SieveBoxedFamily.mem_pool D s z p).mp hpool
    have hb := SieveBoxTuples.boxIndex_spec D s p hD hs hpu (hpz.trans_le hz)
    rw [hi] at hb
    refine ⟨hprime, hb.1, ?_⟩
    simpa only [SieveGeometricGrid.scale_succ D s hD0.le] using hb.2.le
  have hm := MertensPrimeInterval.prime_reciprocal_geometric (D^(s^2))
    (SieveGeometricGrid.scale D s i) (SieveGeometricGrid.ratio s) S hu hua hq.le hinterval
  have hlog : log (SieveGeometricGrid.ratio s) ≤ s^9 := by
    have hh := log_le_sub_one_of_pos (zero_lt_one.trans hq)
    simpa only [SieveGeometricGrid.ratio, add_sub_cancel_left] using hh
  rw [Real.log_rpow hD0] at hm
  exact hm.trans (add_le_add hlog le_rfl)

run_cmd do
  for decl in [``eta_nonneg, ``common_band_bound] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ACTUAL COMMON-BAND PRIME RECIPROCAL MASS PASSED"
end SievePrimeBandMass
end
