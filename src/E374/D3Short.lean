import E374.Asymp

/-!
# D3, Lemma 2.1: uniform shortness from the repair-mass lemma

Every three-factor configuration `q_a * P_h(m) = □` with `m ≤ X`, `h ≥ 1`, `a + h < m`
has `h < X^η` and `a < X^η` once `X` is large — uniformly over ALL configurations,
with no exceptional endpoint set. Inputs: the project's `Tasks.ValuationOneMass` (RM)
and `Tasks.FactorialClassGrowth`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.style.longLine false
set_option maxHeartbeats 1600000

noncomputable section
open scoped BigOperators

namespace Erdos374.D35

/-- `q_a ≤ m^h` whenever `q_a * P_h(m)` is a square (and `h ≤ m`). -/
theorem q_le_pow_of_isSquare {a h m : ℕ} (hhm : h ≤ m) (hs : IsSquare (q a * falling h m)) :
    q a ≤ m ^ h :=
  le_trans (Nat.le_of_dvd (falling_pos hhm) (q_dvd_of_isSquare hs)) (falling_le_pow h m)

/-- Growth: `a ≤ N₀ + 3 h log X` for every square configuration with `m ≤ X`. -/
theorem index_le_of_growth (hG : Tasks.FactorialClassGrowth) :
    ∃ N₀ : ℕ, ∀ X a h m : ℕ, 1 ≤ m → m ≤ X → h ≤ m →
      IsSquare (q a * falling h m) →
      (a : ℝ) ≤ N₀ + 3 * h * Real.log X := by
  obtain ⟨N₀, hN₀⟩ := hG
  refine ⟨N₀, fun X a h m hm1 hmX hhm hs => ?_⟩
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast le_trans hm1 hmX
  have hlog0 : 0 ≤ Real.log X := Real.log_nonneg hX1
  have hh0 : (0 : ℝ) ≤ h := Nat.cast_nonneg h
  by_cases ha : N₀ ≤ a
  · have hexp := hN₀ a ha
    have hqle : (q a : ℝ) ≤ (X : ℝ) ^ h := by
      have h1 := q_le_pow_of_isSquare hhm hs
      have h2 : m ^ h ≤ X ^ h := Nat.pow_le_pow_left hmX h
      exact_mod_cast le_trans h1 h2
    have hlogq : (a : ℝ) / 3 ≤ h * Real.log X := by
      have hq0 : (0 : ℝ) < q a := by exact_mod_cast q_pos a
      have := Real.log_le_log (Real.exp_pos _) (le_trans hexp hqle)
      rwa [Real.log_exp, Real.log_pow] at this
    have : (0 : ℝ) ≤ N₀ := Nat.cast_nonneg N₀
    linarith
  · push_neg at ha
    have : (a : ℝ) ≤ N₀ := by exact_mod_cast ha.le
    have : 0 ≤ 3 * (h : ℝ) * Real.log X := by positivity
    linarith

/-- An odd valuation contradicts squareness. -/
theorem not_isSquare_of_factorization_one {n p : ℕ} (hp : p.Prime) (hn : n ≠ 0)
    (h1 : n.factorization p = 1) : ¬ IsSquare n := by
  intro hs
  have := (Nat.isSquare_iff_even_factorization.mp hs) p hp
  rw [h1] at this
  exact Nat.not_even_one this

/-- **Lemma 2.1 (uniform shortness).** -/
theorem uniform_short (hRM : Tasks.ValuationOneMass) (hG : Tasks.FactorialClassGrowth)
    {η : ℝ} (hη : 0 < η) (hη1 : η < 1) :
    ∃ N : ℕ, ∀ X : ℕ, N ≤ X → ∀ m a h : ℕ, m ≤ X → 1 ≤ h → a + h < m →
      IsSquare (q a * falling h m) →
      (h : ℝ) < (X : ℝ) ^ (η / 2) ∧ (a : ℝ) < (X : ℝ) ^ η := by
  obtain ⟨N₀, hN₀⟩ := index_le_of_growth hG
  obtain ⟨X₀, hX₀⟩ := hRM (η / 2) (by linarith) (by linarith)
  -- `N₀ ≤ 7 log X` eventually
  obtain ⟨N₁, hN₁⟩ := nat_eventually_log_gt ((N₀ : ℝ) / 7)
  -- `N₀ + 3 X^{η/2} log X < X^η` eventually
  obtain ⟨N₂, hN₂⟩ := nat_eventually_rpow_log_dom (show η / 2 < η by linarith) 6
  obtain ⟨N₃, hN₃⟩ := nat_eventually_rpow_dom (show (0 : ℝ) < η by linarith) (2 * N₀)
  refine ⟨max (max X₀ N₁) (max (max N₂ N₃) 2), fun X hX m a h hmX hh hahm hs => ?_⟩
  have hXX₀ : X₀ ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX
  have hXN₁ : N₁ ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
  have hXN₂ : N₂ ≤ X :=
    le_trans (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_right _ _))) hX
  have hXN₃ : N₃ ≤ X :=
    le_trans (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_right _ _))) hX
  have hX2 : 2 ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hX
  have hX1R : (1 : ℝ) ≤ X := by exact_mod_cast (show 1 ≤ X by omega)
  have hX0R : (0 : ℝ) < X := by linarith
  have hlog0 : 0 ≤ Real.log X := Real.log_nonneg hX1R
  have hm1 : 1 ≤ m := by omega
  have hhm : h ≤ m := by omega
  have hidx := hN₀ X a h m hm1 hmX hhm hs
  have hlogbig := hN₁ X hXN₁
  have hhR : (1 : ℝ) ≤ h := by exact_mod_cast hh
  -- `a ≤ 10 h log X`
  have ha10 : (a : ℝ) ≤ 10 * ((m - (m - h) : ℕ) : ℝ) * Real.log X := by
    rw [Nat.sub_sub_self hhm]
    have : (N₀ : ℝ) ≤ 7 * h * Real.log X := by
      have : (N₀ : ℝ) ≤ 7 * Real.log X := by linarith
      nlinarith
    linarith
  -- shortness of `h` from RM
  have hshort : (h : ℝ) < (X : ℝ) ^ (η / 2) := by
    by_contra hcon
    push_neg at hcon
    have hb : a < m - h := by omega
    have hc : m - h < m := by omega
    have hcb : ((m - (m - h) : ℕ) : ℝ) = h := by rw [Nat.sub_sub_self hhm]
    obtain ⟨R, hR0, _, hRp, hRlog⟩ := hX₀ X a (m - h) m hXX₀ hb hc hmX
      (by rw [hcb]; exact hcon) ha10
    rw [Nat.sub_sub_self hhm] at hRp hRlog
    have hRgt : 1 < R := by
      by_contra hR1
      have hR : R = 1 := by omega
      rw [hR] at hRlog
      simp at hRlog
      linarith
    set p := R.minFac with hpdef
    have hpp : p.Prime := Nat.minFac_prime (by omega)
    obtain ⟨hap, hv⟩ := hRp p hpp (Nat.minFac_dvd R)
    have hq0 : (q a).factorization p = 0 :=
      Nat.factorization_eq_zero_of_not_dvd (not_dvd_q_of_lt hpp hap)
    have hv' : (q a * falling h m).factorization p = 1 := by
      rw [Nat.factorization_mul (q_ne_zero a) (falling_ne_zero hhm)]
      simp only [Finsupp.coe_add, Pi.add_apply, hq0, hv, zero_add]
    exact not_isSquare_of_factorization_one hpp
      (mul_ne_zero (q_ne_zero a) (falling_ne_zero hhm)) hv' hs
  refine ⟨hshort, ?_⟩
  -- `a ≤ N₀ + 3 h log X < N₀ + 3 X^{η/2} log X < X^η`
  have h1 : (a : ℝ) ≤ N₀ + 3 * (X : ℝ) ^ (η / 2) * Real.log X := by
    have : 3 * (h : ℝ) * Real.log X ≤ 3 * (X : ℝ) ^ (η / 2) * Real.log X := by
      apply mul_le_mul_of_nonneg_right _ hlog0
      linarith
    linarith
  have h2 := hN₂ X hXN₂
  have h3 := hN₃ X hXN₃
  have hrp : (X : ℝ) ^ (0 : ℝ) = 1 := Real.rpow_zero _
  rw [hrp, mul_one] at h3
  linarith

end Erdos374.D35

end
