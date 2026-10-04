import SieveBoxMass
import SieveProfileMassSharp

/-! Refined unsigned bounds for the complete actual signed box families. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open scoped BigOperators
namespace SieveBoxMass
open SieveBoxGrouping SieveGeometricGrid

theorem total_mass_le_product_of_band_bound (D s z : ℝ)
    (hD : 1 < D) (hs : 0 < s) (hz : z ≤ D)
    (hband : ∀ i ≤ cutoff s, bandMass D s z i < 1) :
    mass true D s z + mass false D s z ≤
      ∏ i : Fin (cutoff s+1), 1/(1-bandMass D s z i.val) := by
  classical
  rw [mass_eq_profile_mass true D s z hD hs hz,
    mass_eq_profile_mass false D s z hD hs hz, ← Finset.sum_union (profiles_disjoint D s)]
  have hdata : ∀ g ∈ profiles true D s ∪ profiles false D s,
      g.length ≤ SieveBoxLength.cutoff s ∧ (∀ i ∈ g, i < cutoff s+1) ∧ g.Pairwise (· ≥ ·) := by
    intro g hg
    rcases Finset.mem_union.mp hg with hg | hg
    · have h := (mem_profiles true D s g).mp hg
      exact ⟨h.1, fun i hi => Nat.lt_succ_of_le (h.2.1 i hi), profile_sorted true D s g hg⟩
    · have h := (mem_profiles false D s g).mp hg
      exact ⟨h.1, fun i hi => Nat.lt_succ_of_le (h.2.1 i hi), profile_sorted false D s g hg⟩
  exact SieveProfileMass.sorted_mass_le_product _ (cutoff s+1) (SieveBoxLength.cutoff s)
    (bandMass D s z) (fun g hg => (hdata g hg).1)
    (fun g hg => (hdata g hg).2.1) (fun g hg => (hdata g hg).2.2)
    (fun i _ => bandMass_nonneg D s z i) (fun i hi => hband i (Nat.lt_succ_iff.mp hi))

theorem total_mass_le_exp_sharp_of_band_bound (D s z : ℝ)
    (hD : 1 < D) (hs : 0 < s) (hz : z ≤ D)
    (hband : ∀ i ≤ cutoff s, bandMass D s z i ≤ 1/17) :
    mass true D s z + mass false D s z ≤ Real.exp ((17/16) * primeMass D s z) := by
  have h := SieveProfileMass.product_inverse_le_exp_sharp (cutoff s+1) (bandMass D s z)
    (fun i _ => bandMass_nonneg D s z i) (fun i hi => hband i (Nat.lt_succ_iff.mp hi))
  rw [sum_bandMass D s z hD hs hz] at h
  exact (total_mass_le_product_of_band_bound D s z hD hs hz
    (fun i hi => (hband i hi).trans_lt (by norm_num))).trans h

run_cmd do
  for decl in [``total_mass_le_product_of_band_bound, ``total_mass_le_exp_sharp_of_band_bound] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end SieveBoxMass
end
