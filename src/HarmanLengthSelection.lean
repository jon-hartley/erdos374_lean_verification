import HarmanMomentSelection

/-!
Lift the moment selector from logarithmic coordinates to positive real
lengths. The finite bound on the integer power is fixed by lambda before
the ambient scale or factor lengths are chosen.
-/

set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section

namespace HarmanLengthSelection
open HarmanMomentSelection

def scaleExponent (X Y : ℝ) : ℝ := Real.log Y / Real.log X

theorem power_representation (X Y : ℝ) (hX : 1 < X) (hY : 0 < Y) :
    X ^ scaleExponent X Y = Y := by
  have hXp : 0 < X := by linarith
  have hlog : Real.log X ≠ 0 := ne_of_gt (Real.log_pos hX)
  rw [Real.rpow_def_of_pos hXp]
  have hid : Real.log X * scaleExponent X Y = Real.log Y := by
    unfold scaleExponent
    field_simp
  rw [hid, Real.exp_log hY]

theorem exists_uniform_order (lambda e : ℝ) (hlambda : 0 < lambda) (he : 0 < e) :
    ∃ H : ℕ, 4 ≤ H ∧ ∀ (X T Q G : ℝ),
      1 < X → 1 ≤ T → T ≤ X → 0 < Q → 0 < G → X ^ lambda ≤ G →
      X ^ (e / 10) * T ^ (10 / 9 : ℝ) ≤ Q * G →
      X ^ e * T ^ (6 / 7 : ℝ) ≤ Q →
      ∃ h : ℕ, ∃ beta : ℝ,
        4 ≤ h ∧ h ≤ H ∧ 2 * (h : ℝ) ≤ beta ∧ beta ≤ 2 * (h : ℝ) + 2 ∧
        T ^ (4 : ℕ) ≤ G ^ (beta + 2 * h) ∧
        X ^ (e / 10) * T ^ (4 / (pairedOrder beta + 2)) ≤ Q := by
  let H : ℕ := max 4 ⌈1 / lambda + 4⌉₊
  refine ⟨H, le_max_left _ _, ?_⟩
  intro X T Q G hX hT hTX hQ hG hGmin hproduct hpair
  have hXp : 0 < X := by linarith
  have hTp : 0 < T := by linarith
  let t := scaleExponent X T
  let q := scaleExponent X Q
  let g := scaleExponent X G
  have htr : X ^ t = T := power_representation X T hX hTp
  have hqr : X ^ q = Q := power_representation X Q hX hQ
  have hgr : X ^ g = G := power_representation X G hX hG
  have ht : 0 ≤ t := div_nonneg (Real.log_nonneg hT) (Real.log_pos hX).le
  have ht1 : t ≤ 1 := (div_le_one (Real.log_pos hX)).mpr (Real.log_le_log hTp hTX)
  have hg : lambda ≤ g := by
    apply (Real.rpow_le_rpow_left_iff hX).mp
    rw [hgr]
    exact hGmin
  have hprod : q + g ≥ (10 / 9) * t + e / 10 := by
    apply (Real.rpow_le_rpow_left_iff hX).mp
    calc
      _ = X ^ (e / 10) * T ^ (10 / 9 : ℝ) := by
        rw [Real.rpow_add hXp, mul_comm (10 / 9 : ℝ) t,
          Real.rpow_mul hXp.le, htr]
        ring
      _ ≤ Q * G := hproduct
      _ = _ := by rw [Real.rpow_add hXp, hqr, hgr]
  have hpair' : q ≥ (6 / 7) * t + e := by
    apply (Real.rpow_le_rpow_left_iff hX).mp
    calc
      _ = X ^ e * T ^ (6 / 7 : ℝ) := by
        rw [Real.rpow_add hXp, mul_comm (6 / 7 : ℝ) t,
          Real.rpow_mul hXp.le, htr]
        ring
      _ ≤ Q := hpair
      _ = X ^ q := hqr.symm
  obtain ⟨h, beta, hh, hlo, hhi, hbal, hpm, hbound, _⟩ :=
    HarmanMomentSelection.exists_order_uniform t g q e lambda ht ht1 hlambda hg he hprod hpair'
  have hmax : h ≤ H := by
    have hh' : (h : ℝ) ≤ ⌈1 / lambda + 4⌉₊ := hbound.trans (Nat.le_ceil _)
    have hh'' : h ≤ ⌈1 / lambda + 4⌉₊ := by exact_mod_cast hh'
    exact hh''.trans (le_max_right _ _)
  refine ⟨h, beta, hh, hmax, hlo, hhi, ?_, ?_⟩
  · calc
      T ^ (4 : ℕ) = X ^ (4 * t) := by
        rw [mul_comm 4 t, Real.rpow_mul hXp.le, htr]
        norm_num
      _ ≤ X ^ (g * (beta + 2 * h)) := Real.rpow_le_rpow_of_exponent_le hX.le hbal
      _ = G ^ (beta + 2 * h) := by rw [Real.rpow_mul hXp.le, hgr]
  · calc
      _ = X ^ (e / 10 + t * (4 / (pairedOrder beta + 2))) := by
        rw [Real.rpow_add hXp, Real.rpow_mul hXp.le, htr]
      _ ≤ X ^ q := by
        apply Real.rpow_le_rpow_of_exponent_le hX.le
        convert hpm using 1
        ring
      _ = Q := hqr

end HarmanLengthSelection

#print axioms HarmanLengthSelection.exists_uniform_order
run_cmd do
  for target in [``HarmanLengthSelection.power_representation,
      ``HarmanLengthSelection.exists_uniform_order] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "HARMAN LENGTH SELECTION PASSED"
