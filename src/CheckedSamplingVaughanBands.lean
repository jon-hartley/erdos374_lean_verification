import CheckedSamplingCorrelationWindows

/-!
Insert the actual Vaughan coefficients and choose the nearby cutoff.
The resulting bounds have only band-level numerical hypotheses, with no
unproved per-pair cancellation or parameter-existence premise.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators ComplexConjugate

namespace VaughanBands
open Erdos374.Vaughan145 Erdos374.VaughanCoefficients152
open Erdos374.BilinearCorrelation152 CorrelationWindows TypeIICancellation

theorem beta_norm_on_band (V K k : ℕ)
    (hk : k ∈ Finset.Ioc K (2 * K)) :
    ‖(beta V k : ℂ)‖ ≤ Real.log (2 * (K : ℝ)) := by
  have hmem := Finset.mem_Ioc.mp hk
  have hkPos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (beta_bounds V k).1]
  exact (beta_bounds V k).2.trans
    (Real.log_le_log hkPos (by exact_mod_cast hmem.2))

theorem moebius_band_energy (U D E : ℕ) (hE : E ≤ 2 * D) :
    (∑ d ∈ Finset.Ioc D E, ‖(high U muR d : ℂ)‖ ^ 2) ≤ (D : ℝ) := by
  apply (high_moebius_energy (Finset.Ioc D E) U).trans
  rw [Nat.card_Ioc]
  exact_mod_cast (by omega : E - D ≤ D)

theorem norm_from_square_budget (z : ℂ) (D K W q energy near : ℝ)
    (hD : 0 ≤ D) (hK : 0 ≤ K) (hW : 0 ≤ W) (hq : 0 < q)
    (henergyUpper : energy ≤ D)
    (hnear : 0 ≤ near) (hnearUpper : near ≤ 3 * K / q ^ 2)
    (hsum : ‖z‖ ^ 2 ≤ energy * W ^ 2 * K *
      (near * D + K * (10 * D / q ^ 2))) :
    ‖z‖ ≤ 4 * D * K * W / q := by
  have hsquare : ‖z‖ ^ 2 ≤ 13 * (D * K * W / q) ^ 2 := by
    apply hsum.trans
    calc
      _ ≤ D * W ^ 2 * K * ((3 * K / q ^ 2) * D + K * (10 * D / q ^ 2)) := by
        gcongr
      _ = _ := by ring
  have hright : 0 ≤ D * K * W / q := by positivity
  have hid : 4 * D * K * W / q = 4 * (D * K * W / q) := by ring
  rw [hid]
  nlinarith [sq_nonneg (D * K * W / q), norm_nonneg z]

/-- Actual reciprocal Type II bands, with the cutoff chosen and every
far-pair window deduced from the original coefficients. -/
theorem reciprocal_band (r S : ℕ) :
    ∃ B cutoff : ℕ, ∀ D E K P M U V : ℕ, cutoff ≤ D → E ≤ 2 * D →
      Real.log (D : ℝ) ^ (2 * S) ≤ (K : ℝ) →
      ∀ u v : ℝ, u ≠ 0 →
        4 * (K : ℝ) * (D : ℝ) * Real.log (D : ℝ) ^ (B + 2 * S) ≤ |u| →
        2 * |u| ≤ (K : ℝ) * (D : ℝ) ^ r →
        4 * ((r + 3 : ℕ) : ℝ) * |v| ≤ |u| * (D : ℝ) * (K : ℝ) →
        ‖∑ d ∈ Finset.Ioc D E, (high U muR d : ℂ) *
          ∑ k ∈ Finset.Ioc K (2 * K), (beta V k : ℂ) * bandCharacter P M u v d k‖ ≤
          4 * (D : ℝ) * (K : ℝ) * Real.log (2 * (K : ℝ)) /
            Real.log (D : ℝ) ^ S := by
  obtain ⟨B, cutoff, hc⟩ := reciprocal_bilinear_cancellation r (2 * S)
  refine ⟨B, max 2 cutoff, ?_⟩
  intro D E K P M U V hD hE hK u v hu hlow hhigh hshape
  have hDtwo : 2 ≤ D := by omega
  have hlog : 0 < Real.log (D : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < D by omega))
  have hQ : 0 < Real.log (D : ℝ) ^ (2 * S) := pow_pos hlog _
  have hKpos : 0 < K := by exact_mod_cast (hQ.trans_le hK)
  have hKr : (0 : ℝ) < K := Nat.cast_pos.mpr hKpos
  have hW : 0 ≤ Real.log (2 * (K : ℝ)) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * K by omega))
  let Q := Real.log (D : ℝ) ^ (2 * S)
  have hs := hc D E P M (nearCutoff K Q) (by omega) hE
    (Finset.Ioc K (2 * K)) (by intro k hk; have := (Finset.mem_Ioc.mp hk).1; omega)
    u v hu (fun d => (high U muR d : ℂ)) (fun k => (beta V k : ℂ))
    (Real.log (2 * (K : ℝ))) hW (beta_norm_on_band V K)
    (by
      intro k hk l hl hfar _
      have hk' := Finset.mem_Ioc.mp hk
      have hl' := Finset.mem_Ioc.mp hl
      apply reciprocal_coefficient_window r D K k l Q (Real.log (D : ℝ) ^ B) u v
        hKr hQ hu (by exact_mod_cast hk'.1.le) (by exact_mod_cast hk'.2)
        (by exact_mod_cast hl'.1.le) (by exact_mod_cast hl'.2)
        (far_gap K k l Q hfar) _ hhigh hshape
      simpa only [Q, pow_add, mul_assoc, mul_left_comm, mul_comm] using hlow)
  have hcard : ((Finset.Ioc K (2 * K)).card : ℝ) = K := by
    simp [Nat.card_Ioc, two_mul]
  rw [hcard] at hs
  have hQid : Real.log (D : ℝ) ^ (2 * S) = (Real.log (D : ℝ) ^ S) ^ 2 := by
    rw [← pow_mul, Nat.mul_comm S 2]
  rw [hQid] at hs
  apply norm_from_square_budget _ D K (Real.log (2 * (K : ℝ)))
    (Real.log (D : ℝ) ^ S) _ _ (Nat.cast_nonneg D) hKr.le hW
    (pow_pos hlog S)
    (moebius_band_energy U D E hE) (Nat.cast_nonneg _) _ hs
  simpa only [Q, hQid] using nearby_budget K Q hQ hK

/-- Actual inverse-square Type II bands with the same selected cutoff. -/
theorem square_band (r S : ℕ) :
    ∃ B cutoff : ℕ, ∀ D E K P M U V : ℕ, cutoff ≤ D → E ≤ 2 * D →
      Real.log (D : ℝ) ^ (2 * S) ≤ (K : ℝ) →
      ∀ v : ℝ,
        4 * (K : ℝ) ^ 2 * (D : ℝ) ^ 2 * Real.log (D : ℝ) ^ (B + 2 * S) ≤ |v| →
        4 * |v| ≤ (K : ℝ) ^ 2 * (D : ℝ) ^ (r + 1) →
        ‖∑ d ∈ Finset.Ioc D E, (high U muR d : ℂ) *
          ∑ k ∈ Finset.Ioc K (2 * K), (beta V k : ℂ) * bandCharacter P M 0 v d k‖ ≤
          4 * (D : ℝ) * (K : ℝ) * Real.log (2 * (K : ℝ)) /
            Real.log (D : ℝ) ^ S := by
  obtain ⟨B, cutoff, hc⟩ := square_bilinear_cancellation r (2 * S)
  refine ⟨B, max 2 cutoff, ?_⟩
  intro D E K P M U V hD hE hK v hlow hhigh
  have hlog : 0 < Real.log (D : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < D by omega))
  have hQ : 0 < Real.log (D : ℝ) ^ (2 * S) := pow_pos hlog _
  have hKpos : 0 < K := by exact_mod_cast (hQ.trans_le hK)
  have hKr : (0 : ℝ) < K := Nat.cast_pos.mpr hKpos
  have hW : 0 ≤ Real.log (2 * (K : ℝ)) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * K by omega))
  let Q := Real.log (D : ℝ) ^ (2 * S)
  have hs := hc D E P M (nearCutoff K Q) (by omega) hE
    (Finset.Ioc K (2 * K)) (by intro k hk; have := (Finset.mem_Ioc.mp hk).1; omega)
    v (fun d => (high U muR d : ℂ)) (fun k => (beta V k : ℂ))
    (Real.log (2 * (K : ℝ))) hW (beta_norm_on_band V K)
    (by
      intro k hk l hl hfar _
      have hk' := Finset.mem_Ioc.mp hk
      have hl' := Finset.mem_Ioc.mp hl
      apply square_coefficient_window r D K k l Q (Real.log (D : ℝ) ^ B) v
        hKr hQ (by exact_mod_cast hk'.1.le) (by exact_mod_cast hk'.2)
        (by exact_mod_cast hl'.1.le) (by exact_mod_cast hl'.2)
        (far_gap K k l Q hfar) _ hhigh
      simpa only [Q, pow_add, mul_assoc, mul_left_comm, mul_comm] using hlow)
  have hcard : ((Finset.Ioc K (2 * K)).card : ℝ) = K := by
    simp [Nat.card_Ioc, two_mul]
  rw [hcard] at hs
  have hQid : Real.log (D : ℝ) ^ (2 * S) = (Real.log (D : ℝ) ^ S) ^ 2 := by
    rw [← pow_mul, Nat.mul_comm S 2]
  rw [hQid] at hs
  apply norm_from_square_budget _ D K (Real.log (2 * (K : ℝ)))
    (Real.log (D : ℝ) ^ S) _ _ (Nat.cast_nonneg D) hKr.le hW
    (pow_pos hlog S)
    (moebius_band_energy U D E hE) (Nat.cast_nonneg _) _ hs
  simpa only [Q, hQid] using nearby_budget K Q hQ hK

end VaughanBands

#print axioms VaughanBands.reciprocal_band
#print axioms VaughanBands.square_band
run_cmd do
  for target in [``VaughanBands.reciprocal_band, ``VaughanBands.square_band] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "VAUGHAN BANDS PASSED"

run_cmd do
  for target in [``VaughanBands.beta_norm_on_band,
      ``VaughanBands.moebius_band_energy,
      ``VaughanBands.norm_from_square_budget,
      ``VaughanBands.reciprocal_band,
      ``VaughanBands.square_band] do
    for ax in (← Lean.collectAxioms target) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "CHECKED SAMPLING PORT: ALL EXPORTED THEOREMS GUARDED"
