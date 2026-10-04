import SieveEventualProfile
import SieveProfileExponentialTail

/-! Endpoint-safe interpretation of finite nonnegative staircase profiles.
The cumulative indicators are closed at their right endpoints. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Real
open scoped BigOperators
namespace SieveProfileStaircase

def left (i : ℕ) : ℝ := 2+(i:ℝ)/5
def cut (i : ℕ) : ℝ := 2+((i:ℝ)+1)/5
def staircase (N : ℕ) (v : ℕ → ℝ) (r : ℝ) : ℝ :=
  ∑ j ∈ Finset.range N, (v j-v (j+1))*(if r ≤ cut j then 1 else 0)
def profile (N : ℕ) (v : ℕ → ℝ) (r : ℝ) : ℝ :=
  staircase N v r + SieveProfileExponentialTail.tail r

theorem suffix_sum (N i : ℕ) (v : ℕ → ℝ) (hi : i ≤ N) :
    (∑ j ∈ Finset.range N, if i ≤ j then v j-v (j+1) else 0) = v i-v N := by
  induction N with
  | zero =>
    have : i = 0 := by omega
    subst i
    simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    by_cases h : i ≤ N
    · rw [ite_eq_left h, ih h]; ring
    · have he : i = N+1 := by omega
      subst i
      have hz : (∑ j ∈ Finset.range N, if N+1 ≤ j then v j-v (j+1) else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        rw [ite_eq_right (by have := Finset.mem_range.mp hj; omega)]
      rw [hz, ite_eq_right (by omega)]
      ring

theorem staircase_nonneg (N : ℕ) (v : ℕ → ℝ)
    (hd : ∀ j < N, 0 ≤ v j-v (j+1)) (r : ℝ) : 0 ≤ staircase N v r := by
  apply Finset.sum_nonneg
  intro j hj
  exact mul_nonneg (hd j (Finset.mem_range.mp hj)) (by split_ifs <;> norm_num)

theorem staircase_lower (N i : ℕ) (v : ℕ → ℝ)
    (hi : i ≤ N) (hd : ∀ j < N, 0 ≤ v j-v (j+1))
    (r : ℝ) (hr : r ≤ cut i) : v i-v N ≤ staircase N v r := by
  rw [← suffix_sum N i v hi]
  apply Finset.sum_le_sum
  intro j hj
  by_cases hij : i ≤ j
  · have hc : cut i ≤ cut j := by
      have hijR : (i:ℝ) ≤ (j:ℝ) := by exact_mod_cast hij
      unfold cut
      linarith
    simp only [hij, ite_true, hr.trans hc, mul_one, le_refl]
  · simp only [hij, ite_false]
    exact mul_nonneg (hd j (Finset.mem_range.mp hj)) (by split_ifs <;> norm_num)

theorem staircase_eq (N i : ℕ) (v : ℕ → ℝ) (hi : i ≤ N)
    (r : ℝ) (hl : left i < r) (hu : r ≤ cut i) :
    staircase N v r = v i-v N := by
  rw [← suffix_sum N i v hi]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hij : i ≤ j
  · have hc : cut i ≤ cut j := by
      have hijR : (i:ℝ) ≤ (j:ℝ) := by exact_mod_cast hij
      unfold cut
      linarith
    simp only [hij, ite_true, hu.trans hc, mul_one]
  · have hji : j+1 ≤ i := by omega
    have hc : cut j ≤ left i := by
      have hjiR : (j:ℝ)+1 ≤ (i:ℝ) := by exact_mod_cast hji
      unfold cut left
      linarith
    simp only [hij, ite_false, not_le.mpr (hc.trans_lt hl), mul_zero]

theorem grid_cover (r : ℝ) (hr : 2 ≤ r) (hR : r < 20) :
    ∃ i : ℕ, i < 90 ∧ left i ≤ r ∧ r ≤ cut i := by
  let i := ⌊5*(r-2)⌋₊
  have h0 : 0 ≤ 5*(r-2) := by linarith
  have hlo : (i:ℝ) ≤ 5*(r-2) := Nat.floor_le h0
  have hhi : 5*(r-2) < (i:ℝ)+1 := Nat.lt_floor_add_one _
  refine ⟨i, ?_, ?_, ?_⟩
  · have : (i:ℝ) < 90 := by linarith
    exact_mod_cast this
  · unfold left; linarith
  · unfold cut; linarith

theorem profile_nonneg (N : ℕ) (v : ℕ → ℝ)
    (hd : ∀ j < N, 0 ≤ v j-v (j+1)) (r : ℝ) : 0 ≤ profile N v r :=
  add_nonneg (staircase_nonneg N v hd r) (SieveProfileExponentialTail.tail_nonneg r)

theorem profile_lower (N i : ℕ) (v : ℕ → ℝ)
    (hi : i ≤ N) (hd : ∀ j < N, 0 ≤ v j-v (j+1)) (hN : v N = 0)
    (r : ℝ) (hr : r ≤ cut i) : v i ≤ profile N v r := by
  have h := staircase_lower N i v hi hd r hr
  rw [hN, sub_zero] at h
  exact h.trans (le_add_of_nonneg_right (SieveProfileExponentialTail.tail_nonneg r))

theorem profile_tail (N : ℕ) (v : ℕ → ℝ)
    (hd : ∀ j < N, 0 ≤ v j-v (j+1)) (r : ℝ) (hr : 20 ≤ r) :
    91*exp (-r) ≤ profile N v r := by
  unfold profile SieveProfileExponentialTail.tail
  rw [ite_eq_left hr]
  exact le_add_of_nonneg_left (staircase_nonneg N v hd r)

theorem profile_target (v : ℕ → ℝ) (hN : v 90 = 0) :
    profile 90 v (105/26:ℝ) = v 10 := by
  unfold profile
  rw [staircase_eq 90 10 v (by norm_num) _ (by norm_num [left]) (by norm_num [cut]), hN]
  norm_num [SieveProfileExponentialTail.tail]

theorem exponential_seed (i : ℕ) :
    91*exp (-left i) ≤ (4095/331:ℝ)*(5/6:ℝ)^i := by
  have he2 : (331/45:ℝ) ≤ exp 2 := by
    have h := sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 2) 7
    norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
    exact h
  have he5 : (6/5:ℝ) ≤ exp (1/5:ℝ) := by
    have h := add_one_le_exp (1/5:ℝ)
    linarith
  have hinv2 : exp (-2:ℝ) ≤ 45/331 := by
    rw [exp_neg]
    exact (inv_le_comm₀ (exp_pos 2) (by norm_num)).mpr (by simpa using he2)
  have hinv5 : exp (-1/5:ℝ) ≤ 5/6 := by
    rw [show (-1/5:ℝ) = -(1/5:ℝ) by ring, exp_neg]
    exact (inv_le_comm₀ (exp_pos (1/5:ℝ)) (by norm_num)).mpr (by simpa using he5)
  have hp := pow_le_pow_left₀ (exp_pos (-1/5:ℝ)).le hinv5 i
  have heq : exp (-left i) = exp (-2:ℝ)*(exp (-1/5:ℝ))^i := by
    rw [← exp_nat_mul, ← exp_add]
    congr 1
    unfold left
    ring
  rw [heq]
  have h := mul_le_mul hinv2 hp (pow_nonneg (exp_pos _).le _) (by norm_num)
  nlinarith

theorem seed_profile (v : ℕ → ℝ)
    (hd : ∀ j < 90, 0 ≤ v j-v (j+1)) (hN : v 90 = 0)
    (hseed : ∀ i < 90, (4095/331:ℝ)*(5/6:ℝ)^i ≤ v i) :
    SieveEventualProfile.EventualProfile (profile 90 v) := by
  apply SieveEventualProfile.profile_mono _ _ SieveEventualProfile.initial_profile
  intro r hr
  by_cases hR : r < 20
  · obtain ⟨i, hi, hl, hu⟩ := grid_cover r hr hR
    exact (mul_le_mul_of_nonneg_left (exp_le_exp.mpr (neg_le_neg hl)) (by norm_num : (0:ℝ) ≤ 91)).trans
      ((exponential_seed i).trans ((hseed i hi).trans (profile_lower 90 i v (by omega) hd hN r hu)))
  · exact profile_tail 90 v hd r (le_of_not_gt hR)

run_cmd do
  for decl in [``left, ``cut, ``staircase, ``profile, ``suffix_sum,
    ``staircase_nonneg, ``staircase_lower, ``staircase_eq, ``grid_cover,
    ``profile_nonneg, ``profile_lower, ``profile_tail, ``profile_target,
    ``exponential_seed, ``seed_profile] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ENDPOINT-SAFE STAIRCASE, EXPONENTIAL SEED, AND TARGET ROW INTERPRETATION"
end SieveProfileStaircase
end
