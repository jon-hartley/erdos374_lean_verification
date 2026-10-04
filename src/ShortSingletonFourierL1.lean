import ShortSingletonFourierBounds

/-! Total absolute Fourier coefficient mass, with harmonic and logarithmic bounds. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open scoped BigOperators

namespace ShortSingletonFourier

def smallMajorant (Q : ℕ) (k : ZMod (2*Q+1)) : ℝ :=
  if 0 < k.val ∧ k.val ≤ Q then 1/(2*(k.val:ℝ)) else 0

theorem smallMajorant_nonneg (Q : ℕ) (k : ZMod (2*Q+1)) :
    0 ≤ smallMajorant Q k := by
  unfold smallMajorant
  split_ifs <;> positivity

theorem coefficient_norm_le_majorants (Q : ℕ) (k : ZMod (2*Q+1)) :
    ‖coefficient Q k‖ ≤ (if k=0 then 1 else 0) + smallMajorant Q k + smallMajorant Q (-k) := by
  by_cases hz : k=0
  · subst k
    simpa [smallMajorant] using coefficient_zero_norm_le Q
  have hv : 0 < k.val := by
    have : k.val ≠ 0 := by simpa using hz
    omega
  have hvlt := ZMod.val_lt k
  rw [ite_eq_right hz, zero_add]
  by_cases hk : k.val ≤ Q
  · have hb := coefficient_small_mode_le Q k hv hk
    have hm : smallMajorant Q k = 1/(2*(k.val:ℝ)) := ite_eq_left ⟨hv,hk⟩
    rw [hm]
    linarith [smallMajorant_nonneg Q (-k)]
  · have hneg : (-k).val = 2*Q+1-k.val := by rw [ZMod.neg_val, ite_eq_right hz]
    have hnv : 0 < (-k).val := by rw [hneg]; omega
    have hnQ : (-k).val ≤ Q := by rw [hneg]; omega
    have hb := coefficient_small_mode_le Q (-k) hnv hnQ
    rw [coefficient_norm_neg] at hb
    have hm : smallMajorant Q (-k) = 1/(2*((-k).val:ℝ)) := ite_eq_left ⟨hnv,hnQ⟩
    rw [hm]
    linarith [smallMajorant_nonneg Q k]

theorem smallMajorant_sum (Q : ℕ) :
    (∑ k : ZMod (2*Q+1), smallMajorant Q k) = (harmonic Q : ℝ)/2 := by
  change (∑ k : Fin (2*Q+1),
    if 0 < k.val ∧ k.val ≤ Q then (1:ℝ)/(2*k.val) else 0) = _
  rw [Fin.sum_univ_eq_sum_range
    (fun r : ℕ => if 0 < r ∧ r ≤ Q then (1:ℝ)/(2*(r:ℝ)) else 0)]
  have hn : 2*Q+1 = (Q+1)+Q := by omega
  rw [hn, Finset.sum_range_add]
  have hz : (∑ x ∈ Finset.range Q,
      if 0 < Q+1+x ∧ Q+1+x ≤ Q then (1:ℝ)/(2*(Q+1+x:ℕ)) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    rw [ite_eq_right (by omega)]
  rw [hz, add_zero, Finset.sum_range_succ']
  simp only [Nat.lt_irrefl, false_and, ite_false, add_zero]
  rw [harmonic, Rat.cast_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  have hiQ := Finset.mem_range.mp hi
  rw [ite_eq_left (by constructor <;> omega)]
  push_cast
  simp [div_eq_mul_inv, mul_inv_rev]

theorem coefficient_l1_le (Q : ℕ) :
    (∑ k : ZMod (2*Q+1), ‖coefficient Q k‖) ≤ 1+(harmonic Q : ℝ) := by
  have hneg : (∑ k : ZMod (2*Q+1), smallMajorant Q (-k)) =
      ∑ k : ZMod (2*Q+1), smallMajorant Q k := by
    exact Fintype.sum_equiv (Equiv.neg _) _ _ (fun _ => rfl)
  calc
    _ ≤ ∑ k : ZMod (2*Q+1),
        ((if k=0 then 1 else 0) + smallMajorant Q k + smallMajorant Q (-k)) :=
      Finset.sum_le_sum (fun k _ => coefficient_norm_le_majorants Q k)
    _ = 1+(harmonic Q : ℝ) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hneg, smallMajorant_sum]
      simp
      ring

theorem coefficient_l1_le_log (Q : ℕ) :
    (∑ k : ZMod (2*Q+1), ‖coefficient Q k‖) ≤ 2+Real.log Q := by
  have hh := harmonic_le_one_add_log Q
  linarith [coefficient_l1_le Q]

run_cmd do
  for decl in [``smallMajorant_nonneg, ``coefficient_norm_le_majorants,
      ``smallMajorant_sum, ``coefficient_l1_le, ``coefficient_l1_le_log] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "FINITE FOURIER HARMONIC AND LOGARITHMIC COEFFICIENT BOUNDS PASSED"

end ShortSingletonFourier
