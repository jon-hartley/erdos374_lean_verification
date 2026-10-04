import Item1FiniteAbelPhase

/-! Finite shift averaging with explicit endpoint errors.
All statements include the empty prefix. The only size hypothesis is a
pointwise unit bound; no cancellation estimate is assumed. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open scoped BigOperators

namespace Item1FiniteShiftAveraging
open Item1FiniteAbelPhase

/-- Shifting a prefix exchanges exactly two endpoint prefixes of length h. -/
theorem shifted_prefix_identity (a : ℕ → ℂ) (K h : ℕ) :
    «prefix» (fun n => a (n + h)) K - «prefix» a K =
      «prefix» (fun n => a (n + K)) h - «prefix» a h := by
  have hleft : «prefix» a (h + K) =
      «prefix» a h + «prefix» (fun n => a (n + h)) K := by
    unfold «prefix»
    rw [Finset.sum_range_add]
    simp only [Nat.add_comm]
  have hright : «prefix» a (K + h) =
      «prefix» a K + «prefix» (fun n => a (n + K)) h := by
    unfold «prefix»
    rw [Finset.sum_range_add]
    simp only [Nat.add_comm]
  calc
    _ = («prefix» a (h + K) - «prefix» a h) - «prefix» a K := by
      rw [hleft]
      abel
    _ = _ := by
      rw [Nat.add_comm h K, hright]
      abel

theorem unit_prefix_norm_le (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1) (K : ℕ) :
    ‖«prefix» a K‖ ≤ (K : ℝ) := by
  calc
    _ ≤ ∑ n ∈ Finset.range K, ‖a n‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.range K, (1 : ℝ) := Finset.sum_le_sum (fun n _ => ha n)
    _ = _ := by simp

/-- The two endpoint pieces each cost at most h. -/
theorem shifted_prefix_norm_le (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1) (K h : ℕ) :
    ‖«prefix» (fun n => a (n + h)) K - «prefix» a K‖ ≤ 2 * (h : ℝ) := by
  rw [shifted_prefix_identity]
  calc
    _ ≤ ‖«prefix» (fun n => a (n + K)) h‖ + ‖«prefix» a h‖ := norm_sub_le _ _
    _ ≤ (h : ℝ) + (h : ℝ) := add_le_add
      (unit_prefix_norm_le (fun n => a (n + K)) (fun n => ha (n + K)) h)
      (unit_prefix_norm_le a ha h)
    _ = _ := by ring

theorem twice_range_sum (H : ℕ) :
    (∑ h ∈ Finset.range H, (2 : ℝ) * (h : ℝ)) = (H : ℝ) * ((H : ℝ) - 1) := by
  induction H with
  | zero => simp
  | succ H ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

/-- Exact identity before estimating the finite sum of endpoint errors. -/
theorem shift_average_identity (a : ℕ → ℂ) (K H : ℕ) :
    (H : ℂ) * «prefix» a K =
      (∑ h ∈ Finset.range H, «prefix» (fun n => a (n + h)) K) +
      ∑ h ∈ Finset.range H, («prefix» a K - «prefix» (fun n => a (n + h)) K) := by
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  abel

/-- Averaging over h=0,...,H-1 has endpoint cost H-1, uniformly in K. -/
theorem finite_shift_average (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1)
    (K H : ℕ) (hH : 1 ≤ H) :
    ‖«prefix» a K‖ ≤
      (1 / (H : ℝ)) * ‖∑ h ∈ Finset.range H, ∑ n ∈ Finset.range K, a (n + h)‖ +
        ((H : ℝ) - 1) := by
  have hHp : 0 < (H : ℝ) := by exact_mod_cast (by omega : 0 < H)
  have herr : ‖∑ h ∈ Finset.range H,
      («prefix» a K - «prefix» (fun n => a (n + h)) K)‖ ≤
      (H : ℝ) * ((H : ℝ) - 1) := by
    calc
      _ ≤ ∑ h ∈ Finset.range H,
          ‖«prefix» a K - «prefix» (fun n => a (n + h)) K‖ := norm_sum_le _ _
      _ ≤ ∑ h ∈ Finset.range H, (2 : ℝ) * (h : ℝ) := by
        apply Finset.sum_le_sum
        intro h _
        rw [norm_sub_rev]
        exact shifted_prefix_norm_le a ha K h
      _ = _ := twice_range_sum H
  have htotal : (H : ℝ) * ‖«prefix» a K‖ ≤
      ‖∑ h ∈ Finset.range H, «prefix» (fun n => a (n + h)) K‖ +
        (H : ℝ) * ((H : ℝ) - 1) := by
    calc
      _ = ‖(H : ℂ) * «prefix» a K‖ := by rw [norm_mul]; simp
      _ = _ := congrArg norm (shift_average_identity a K H)
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add le_rfl herr)
  calc
    _ ≤ (‖∑ h ∈ Finset.range H, «prefix» (fun n => a (n + h)) K‖ +
        (H : ℝ) * ((H : ℝ) - 1)) / (H : ℝ) := by
      apply (le_div_iff₀ hHp).mpr
      nlinarith only [htotal]
    _ = _ := by
      simp only [«prefix»]
      field_simp [hHp.ne'] <;> ring

/-- Any nonempty finite family of shifts can be averaged. Distinct indices
may carry equal shifts, so this also applies to product-indexed families. -/
theorem finite_family_shift_average {ι : Type*} (s : Finset ι)
    (hs : s.Nonempty) (shift : ι → ℕ) (a : ℕ → ℂ)
    (ha : ∀ n, ‖a n‖ ≤ 1) (K : ℕ) :
    ‖«prefix» a K‖ ≤
      (‖∑ r ∈ s, «prefix» (fun n => a (n + shift r)) K‖ +
        2 * ∑ r ∈ s, (shift r : ℝ)) / (s.card : ℝ) := by
  have hcard : 0 < (s.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hs
  have hid : (s.card : ℂ) * «prefix» a K =
      (∑ r ∈ s, «prefix» (fun n => a (n + shift r)) K) +
        ∑ r ∈ s, («prefix» a K - «prefix» (fun n => a (n + shift r)) K) := by
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, nsmul_eq_mul]
    abel
  have herr : ‖∑ r ∈ s,
      («prefix» a K - «prefix» (fun n => a (n + shift r)) K)‖ ≤
      2 * ∑ r ∈ s, (shift r : ℝ) := by
    calc
      _ ≤ ∑ r ∈ s, ‖«prefix» a K - «prefix» (fun n => a (n + shift r)) K‖ :=
        norm_sum_le _ _
      _ ≤ ∑ r ∈ s, (2 : ℝ) * (shift r : ℝ) := by
        apply Finset.sum_le_sum
        intro r _
        rw [norm_sub_rev]
        exact shifted_prefix_norm_le a ha K (shift r)
      _ = _ := (Finset.mul_sum s (fun r => (shift r : ℝ)) 2).symm
  have htotal : (s.card : ℝ) * ‖«prefix» a K‖ ≤
      ‖∑ r ∈ s, «prefix» (fun n => a (n + shift r)) K‖ +
        2 * ∑ r ∈ s, (shift r : ℝ) := by
    calc
      _ = ‖(s.card : ℂ) * «prefix» a K‖ := by rw [norm_mul]; simp
      _ = _ := congrArg norm hid
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add le_rfl herr)
  apply (le_div_iff₀ hcard).mpr
  nlinarith only [htotal]

end Item1FiniteShiftAveraging

run_cmd do
  for target in [``Item1FiniteShiftAveraging.shifted_prefix_identity,
      ``Item1FiniteShiftAveraging.unit_prefix_norm_le,
      ``Item1FiniteShiftAveraging.shifted_prefix_norm_le,
      ``Item1FiniteShiftAveraging.twice_range_sum,
      ``Item1FiniteShiftAveraging.shift_average_identity,
      ``Item1FiniteShiftAveraging.finite_shift_average,
      ``Item1FiniteShiftAveraging.finite_family_shift_average] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "FINITE SHIFT AVERAGING: 7 standard-axiom theorem guards passed."
