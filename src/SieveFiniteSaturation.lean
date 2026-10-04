import SieveStoppingRecurrence

/-! Finite saturation of the actual cubic selector. The explicit budget
d * (product of remaining primes)^3 decreases along every recursive branch. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace SieveFiniteSaturation

theorem list_product_one_le (ps : List ℕ) (hp : ∀ p ∈ ps, 1 ≤ p) : 1 ≤ ps.prod := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    simpa using Nat.mul_le_mul (hp p (by simp)) (ih (fun q hq => hp q (by simp [hq])))

theorem branch_budgets (d p m : ℕ) (hp : 1 ≤ p) (hm : 1 ≤ m) :
    d*m^3 ≤ d*(p*m)^3 ∧ (d*p)*m^3 ≤ d*(p*m)^3 ∧ d*p^3 ≤ d*(p*m)^3 := by
  have hmle : m ≤ p*m := by simpa using Nat.mul_le_mul_right m hp
  have hple : p ≤ p*m := by simpa using Nat.mul_le_mul_left p hm
  have hpcube : p ≤ p^3 := by nlinarith [sq_nonneg (p:ℤ)]
  refine ⟨Nat.mul_le_mul_left d (Nat.pow_le_pow_left hmle 3), ?_,
    Nat.mul_le_mul_left d (Nat.pow_le_pow_left hple 3)⟩
  calc
    (d*p)*m^3 ≤ (d*p^3)*m^3 := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left d hpcube)
    _ = d*(p*m)^3 := by ring

theorem selected_eq_open (T : ℝ) (mode : Bool) (d : ℕ) (ps : List ℕ)
    (hp : ∀ p ∈ ps, 1 ≤ p) (hT : ((d*ps.prod^3 : ℕ):ℝ) < T) :
    SievePrefix.selected (SieveRosser.cubicGate T) mode d ps =
      SievePrefix.selected (fun _ _ => True) mode d ps := by
  induction ps generalizing mode d with
  | nil => rfl
  | cons p ps ih =>
    have hp1 : 1 ≤ p := hp p (by simp)
    have hps : ∀ q ∈ ps, 1 ≤ q := fun q hq => hp q (by simp [hq])
    obtain ⟨hskip, htake, hgate⟩ := branch_budgets d p ps.prod hp1 (list_product_one_le ps hps)
    simp only [List.prod_cons] at hT
    have hs : ((d*ps.prod^3:ℕ):ℝ) < T := by
      apply lt_of_le_of_lt _ hT
      exact_mod_cast hskip
    have ht : (((d*p)*ps.prod^3:ℕ):ℝ) < T := by
      apply lt_of_le_of_lt _ hT
      exact_mod_cast htake
    have hg : SieveRosser.cubicGate T d p := by
      apply lt_of_le_of_lt _ hT
      exact_mod_cast hgate
    simp only [SievePrefix.selected, hg, or_true, ite_true, ih mode d hps hs,
      ih (!mode) (d*p) hps ht]

theorem loss_zero (T : ℝ) (d : ℕ) (ps : List ℕ) (b : ℕ → ℝ)
    (hnd : ps.Nodup) (hp : ∀ p ∈ ps, 1 ≤ p)
    (hT : ((d*ps.prod^3:ℕ):ℝ) < T) :
    SievePrefixLoss.lower (SieveRosser.cubicGate T) d ps b = 0 ∧
      SievePrefixLoss.upper (SieveRosser.cubicGate T) d ps b = 0 := by
  have heq : ∀ mode, SievePrefix.value (SieveRosser.cubicGate T) mode d ps b =
      SievePrefix.value (fun _ _ => True) mode d ps b := by
    intro mode
    simp only [SievePrefix.value, selected_eq_open T mode d ps hp hT]
  simpa only [SievePrefixLoss.lower, SievePrefixLoss.upper, heq] using
    SievePrefixLoss.open_gate_exact d ps b hnd

theorem actual_loss_zero (T z : ℝ)
    (hT : (((SieveSmallWeights.primes z).prod^3 : ℕ):ℝ) < T) :
    SieveStoppingRecurrence.lowerLoss T z = 0 ∧ SieveStoppingRecurrence.upperLoss T z = 0 := by
  exact loss_zero T 1 (SieveSmallWeights.primes z) (fun p => (p:ℝ)⁻¹)
    (SieveSmallWeights.primes_nodup z)
    (fun p hp => ((SieveSmallWeights.mem_primes z p).mp hp).1.one_le)
    (by simpa using hT)

theorem prime_product_mono (a b : ℝ) (hab : a ≤ b) :
    (SieveSmallWeights.primes a).prod ≤ (SieveSmallWeights.primes b).prod := by
  have heq (z : ℝ) : (SieveSmallWeights.primes z).prod =
      ∏ p ∈ SieveSmallWeights.pool z, p := by
    simpa [SieveSmallWeights.primes_toFinset] using
      (List.prod_toFinset (fun p : ℕ => p) (SieveSmallWeights.primes_nodup z)).symm
  rw [heq a, heq b]
  apply Finset.prod_le_prod_of_subset_of_one_le
  · intro p hp
    obtain ⟨hpp, hpa⟩ := (SieveSmallWeights.mem_pool a p).mp hp
    exact (SieveSmallWeights.mem_pool b p).mpr ⟨hpp, hpa.trans_le hab⟩
  · intro p hp _
    exact ((SieveSmallWeights.mem_pool b p).mp hp).1.one_le

theorem uniform_finite_cutoff (T z z₀ : ℝ) (hzz : z ≤ z₀)
    (hT : (((SieveSmallWeights.primes z₀).prod^3 : ℕ):ℝ) < T) :
    SieveStoppingRecurrence.lowerLoss T z = 0 ∧ SieveStoppingRecurrence.upperLoss T z = 0 := by
  apply actual_loss_zero
  have hn := Nat.pow_le_pow_left (prime_product_mono z z₀ hzz) 3
  apply lt_of_le_of_lt _ hT
  exact_mod_cast hn

run_cmd do
  for decl in [``list_product_one_le, ``branch_budgets, ``selected_eq_open, ``loss_zero,
    ``actual_loss_zero, ``prime_product_mono, ``uniform_finite_cutoff] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end SieveFiniteSaturation
end
