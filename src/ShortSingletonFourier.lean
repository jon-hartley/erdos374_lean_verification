import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Tactic

/-! Exact finite Fourier separation of an integer prefix. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped BigOperators

namespace ShortSingletonFourier

instance modulus_neZero (Q : ℕ) : NeZero (2 * Q + 1) := ⟨by omega⟩

def phase (Q : ℕ) (k : ZMod (2 * Q + 1)) (n : ℕ) : ℂ :=
  ZMod.stdAddChar (k * (n : ZMod (2 * Q + 1)))

def coefficient (Q : ℕ) (k : ZMod (2 * Q + 1)) : ℂ :=
  ((2 * Q + 1 : ℕ) : ℂ)⁻¹ *
    ∑ r ∈ Finset.range (Q + 1),
      ZMod.stdAddChar (-(k * (r : ZMod (2 * Q + 1))))

theorem phase_norm (Q : ℕ) (k : ZMod (2 * Q + 1)) (n : ℕ) :
    ‖phase Q k n‖ = 1 := by
  simp [phase, ZMod.stdAddChar_apply]

theorem character_sum (Q : ℕ) (a : ZMod (2 * Q + 1)) :
    (∑ k : ZMod (2 * Q + 1), ZMod.stdAddChar (k * a)) =
      if a = 0 then ((2 * Q + 1 : ℕ) : ℂ) else 0 := by
  split_ifs with h
  · simp [h]
  · simpa only [AddChar.mulShift_apply, mul_comm] using
      AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar (2 * Q + 1) h)

theorem residue_eq_iff (Q q J r : ℕ) (hq : q ≤ Q) (hJ : J ≤ Q)
    (hr : r ≤ Q) :
    ((J : ZMod (2 * Q + 1)) - q - r = 0) ↔ q + r = J := by
  have hcast : ((J : ZMod (2 * Q + 1)) - q - r = 0) ↔
      (J : ZMod (2 * Q + 1)) = ((q + r : ℕ) : ZMod (2 * Q + 1)) := by
    push_cast
    constructor <;> intro h <;> linear_combination h
  rw [hcast, ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (by omega : J < 2*Q+1),
    Nat.mod_eq_of_lt (by omega : q+r < 2*Q+1)]
  exact eq_comm

theorem expansion (Q q J : ℕ) :
    (∑ k : ZMod (2 * Q + 1), coefficient Q k * phase Q k J * phase Q (-k) q) =
      ((2 * Q + 1 : ℕ) : ℂ)⁻¹ *
        ∑ r ∈ Finset.range (Q + 1),
          ∑ k : ZMod (2 * Q + 1),
            ZMod.stdAddChar (k * ((J : ZMod (2 * Q + 1)) - (q : ZMod (2*Q+1)) - (r : ZMod (2*Q+1)))) := by
  unfold coefficient phase
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  congr 1
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro k _
  rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
  congr 1
  ring

theorem prefix_eq (Q q J : ℕ) (hq : q ≤ Q) (hJ : J ≤ Q) :
    (if q ≤ J then (1 : ℂ) else 0) =
      ∑ k : ZMod (2 * Q + 1), coefficient Q k * phase Q k J * phase Q (-k) q := by
  rw [expansion]
  have hsum : (∑ r ∈ Finset.range (Q+1),
      ∑ k : ZMod (2*Q+1), ZMod.stdAddChar (k*((J : ZMod (2*Q+1))-(q : ZMod (2*Q+1))-(r : ZMod (2*Q+1))))) =
      if q ≤ J then ((2*Q+1 : ℕ) : ℂ) else 0 := by
    simp_rw [character_sum]
    by_cases hqJ : q ≤ J
    · rw [ite_eq_left hqJ]
      rw [Finset.sum_eq_single (J-q)]
      · rw [ite_eq_left ((residue_eq_iff Q q J (J-q) hq hJ (by omega)).mpr (by omega))]
      · intro r hr hne
        rw [ite_eq_right]
        intro hz
        have := (residue_eq_iff Q q J r hq hJ (by simpa using hr)).mp hz
        omega
      · intro hnot
        exact False.elim (hnot (Finset.mem_range.mpr (by omega)))
    · rw [ite_eq_right hqJ]
      apply Finset.sum_eq_zero
      intro r hr
      rw [ite_eq_right]
      intro hz
      have := (residue_eq_iff Q q J r hq hJ (by simpa using hr)).mp hz
      omega
  rw [hsum]
  have hL : (((2*Q+1 : ℕ) : ℂ)) ≠ 0 := by
    exact_mod_cast (by omega : 2*Q+1 ≠ 0)
  split_ifs
  · rw [inv_mul_cancel₀ hL]
  · simp

run_cmd do
  for decl in [``phase_norm, ``character_sum, ``residue_eq_iff, ``expansion, ``prefix_eq] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "EXACT FINITE FOURIER PREFIX SEPARATION PASSED"

end ShortSingletonFourier
