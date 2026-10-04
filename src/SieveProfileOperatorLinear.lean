import SieveProfileOperatorTransfer

/-! Linearity and positive finite-combination lifting for the actual finite
two-step operator. Profile domination is required only at accepted ratios > 2. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open Real Filter
open scoped Topology BigOperators
attribute [local instance] Classical.propDecidable

namespace SieveProfileOperatorLinear
open SieveStoppingTwoStep SieveStoppingExpansion SieveProfileOperatorGrid
open SieveProfileOperatorCumulative SieveProfileOperatorTransfer

theorem coefficient_nonneg (p q : ℕ) (z : ℝ) :
    0 ≤ (p:ℝ)⁻¹*(q:ℝ)⁻¹*primeEuler (q:ℝ)/primeEuler z := by
  have hq := SieveEulerRatio.euler_pos (q:ℝ)
  have hz := SieveEulerRatio.euler_pos z
  positivity

theorem operator_add (f g : ℝ → ℝ → ℝ) (T z : ℝ) :
    operator (fun T z => f T z+g T z) T z = operator f T z+operator g T z := by
  unfold operator
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  split_ifs <;> ring

theorem operator_const_mul (a : ℝ) (f : ℝ → ℝ → ℝ) (T z : ℝ) :
    operator (fun T z => a*f T z) T z = a*operator f T z := by
  unfold operator
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  split_ifs <;> ring

theorem operator_sum {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (f : ι → ℝ → ℝ → ℝ) (T z : ℝ) :
    operator (fun T z => ∑ i ∈ S, f i T z) T z = ∑ i ∈ S, operator (f i) T z := by
  induction S using Finset.induction_on with
  | empty => simp [operator]
  | @insert i S hi ih =>
    simp only [Finset.sum_insert hi]
    rw [operator_add, ih]

theorem operator_mono (f g : ℝ → ℝ → ℝ) (T z : ℝ)
    (hfg : ∀ T z, f T z ≤ g T z) : operator f T z ≤ operator g T z := by
  unfold operator
  apply Finset.sum_le_sum
  intro p hp
  apply Finset.sum_le_sum
  intro q hq
  split_ifs
  · exact mul_le_mul_of_nonneg_left (hfg _ _) (coefficient_nonneg p q z)
  · exact le_rfl

theorem accepted_ratio_gt_two (T : ℝ) (p q : ℕ)
    (hq : q ∈ SieveSmallWeights.pool (p:ℝ)) (hg : (q:ℝ)^3 < T/(p:ℝ)) :
    2 < log ((T/(p:ℝ))/(q:ℝ))/log (q:ℝ) := by
  have hqp := ((SieveSmallWeights.mem_pool (p:ℝ) q).mp hq).1
  have hq0 : (0:ℝ) < q := by exact_mod_cast hqp.pos
  have hq1 : (1:ℝ) < q := by exact_mod_cast hqp.one_lt
  have hlevel : (q:ℝ)^2 < (T/(p:ℝ))/(q:ℝ) :=
    (lt_div_iff₀ hq0).mpr (by nlinarith)
  have hh := log_lt_log (pow_pos hq0 2) hlevel
  simp only [log_pow, Nat.cast_ofNat] at hh
  exact (lt_div_iff₀ (log_pos hq1)).mpr hh

theorem operator_profile_mono (φ ψ : ℝ → ℝ) (T z : ℝ)
    (hφ : ∀ t : ℝ, 2 < t → φ t ≤ ψ t) :
    operator (fun T z => φ (log T/log z)) T z ≤
      operator (fun T z => ψ (log T/log z)) T z := by
  unfold operator
  apply Finset.sum_le_sum
  intro p hp
  apply Finset.sum_le_sum
  intro q hq
  split_ifs with hg
  · exact mul_le_mul_of_nonneg_left (hφ _ (accepted_ratio_gt_two T p q hq hg))
      (coefficient_nonneg p q z)
  · exact le_rfl

theorem operator_combination_eq {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (d c : ι → ℝ) (T z : ℝ) :
    operator (fun T z => ∑ i ∈ S, d i*(if log T/log z ≤ c i then 1 else 0)) T z =
      ∑ i ∈ S, d i*operator (fun T z => if log T/log z ≤ c i then 1 else 0) T z := by
  rw [operator_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact operator_const_mul _ _ _ _

theorem eventually_combination {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (d c : ι → ℝ) (r h : ℝ) (N : ι → ℕ) (hr : 2 ≤ r) (hh : 0 ≤ h)
    (hd : ∀ i ∈ S, 0 ≤ d i) (hc : ∀ i ∈ S, 2 ≤ c i)
    (hcover : ∀ i ∈ S, c i+2 ≤ r*edge h (N i)) (δ : ℝ) (hδ : 0 < δ) :
    ∃ Z : ℝ, 2 ≤ Z ∧ ∀ z T : ℝ, Z ≤ z → z^2 ≤ T → r ≤ log T/log z →
      operator (fun T z => ∑ i ∈ S, d i*(if log T/log z ≤ c i then 1 else 0)) T z ≤
        (∑ i ∈ S, d i*(h*∑ k ∈ Finset.range (N i), shape (c i) (r*edge h k-1)))+δ := by
  let D : ℝ := ∑ i ∈ S, d i
  have hD : 0 ≤ D := Finset.sum_nonneg hd
  let η := δ/(1+D)
  have hη : 0 < η := div_pos hδ (by linarith)
  have he : ∀ᶠ z : ℝ in atTop, ∀ i ∈ S, ∀ T : ℝ,
      z^2 ≤ T → r ≤ log T/log z →
      operator (fun T z => if log T/log z ≤ c i then 1 else 0) T z ≤
        (h*∑ k ∈ Finset.range (N i), shape (c i) (r*edge h k-1))+η := by
    apply (eventually_all_finset S).mpr
    intro i hi
    obtain ⟨Z, hZ, hb⟩ := eventually_cumulative r (c i) h (N i) hr (hc i hi) hh
      (hcover i hi) η hη
    filter_upwards [eventually_ge_atTop Z] with z hz
    exact fun T hT hparam => hb z T hz hT hparam
  obtain ⟨Z₀, hZ₀⟩ := eventually_atTop.mp he
  refine ⟨max 2 Z₀, le_max_left _ _, ?_⟩
  intro z T hz hT hparam
  have hb := hZ₀ z ((le_max_right _ _).trans hz)
  have herr : η*D ≤ δ := by
    calc
      _ ≤ η*(1+D) := mul_le_mul_of_nonneg_left (by linarith) hη.le
      _ = δ := by dsimp [η]; field_simp
  rw [operator_combination_eq]
  calc
    _ ≤ ∑ i ∈ S, d i*((h*∑ k ∈ Finset.range (N i), shape (c i) (r*edge h k-1))+η) := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (hb i hi T hT hparam) (hd i hi)
    _ = (∑ i ∈ S, d i*(h*∑ k ∈ Finset.range (N i), shape (c i) (r*edge h k-1)))+η*D := by
      simp only [mul_add, Finset.sum_add_distrib]
      rw [← Finset.sum_mul]
      dsimp [D]
      ring
    _ ≤ _ := add_le_add (le_refl _) herr

run_cmd do
  for decl in [``coefficient_nonneg, ``operator_add, ``operator_const_mul,
    ``operator_sum, ``operator_mono, ``accepted_ratio_gt_two, ``operator_profile_mono,
    ``operator_combination_eq, ``eventually_combination] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ACTUAL OPERATOR FINITE POSITIVE PROFILE COMBINATION TRANSFER PASSED"
end SieveProfileOperatorLinear
end
