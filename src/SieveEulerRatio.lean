import SieveStoppingTail
import SieveBoxMass
import SieveProfileMassSharp

/-! Exact small/large-prime Euler factorization and its normalized ratio.
The large pool is the actual pool used by the boxed families. No prime-number
theorem or assumed prime reciprocal estimate is used here. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators

namespace SieveEulerRatio
open SieveStoppingExpansion

theorem pool_split (D s z : ℝ) (hu : D^(s^2) ≤ z) :
    SieveSmallWeights.pool z = SieveSmallWeights.pool (D^(s^2)) ∪
      SieveBoxedFamily.pool D s z := by
  classical
  ext p
  simp only [Finset.mem_union, SieveSmallWeights.mem_pool, SieveBoxedFamily.mem_pool]
  constructor
  · rintro ⟨hp, hpz⟩
    by_cases hpu : (p:ℝ) < D^(s^2)
    · exact Or.inl ⟨hp, hpu⟩
    · exact Or.inr ⟨hp, hpz, le_of_not_gt hpu⟩
  · rintro (⟨hp, hpu⟩ | ⟨hp, hpz, _⟩)
    · exact ⟨hp, hpu.trans_le hu⟩
    · exact ⟨hp, hpz⟩

theorem pools_disjoint (D s z : ℝ) :
    Disjoint (SieveSmallWeights.pool (D^(s^2))) (SieveBoxedFamily.pool D s z) := by
  classical
  apply Finset.disjoint_left.mpr
  intro p hp hq
  exact (not_le_of_gt ((SieveSmallWeights.mem_pool _ p).mp hp).2)
    ((SieveBoxedFamily.mem_pool D s z p).mp hq).2.2

theorem euler_pos (z : ℝ) : 0 < primeEuler z :=
  SieveReciprocalModel.euler_positive _ (SieveSmallWeights.primes_prime z)

/-- The left endpoint belongs to the large pool, the right endpoint to neither. -/
theorem euler_split (D s z : ℝ) (hu : D^(s^2) ≤ z) :
    primeEuler z = primeEuler (D^(s^2)) *
      ∏ p ∈ SieveBoxedFamily.pool D s z, (1-(p:ℝ)⁻¹) := by
  simp only [primeEuler, SievePrefixLoss.euler, SieveSmallWeights.primes_toFinset]
  rw [pool_split D s z hu, Finset.prod_union (pools_disjoint D s z)]

theorem ratio_eq_product_inverse (D s z : ℝ) (hu : D^(s^2) ≤ z) :
    primeEuler (D^(s^2)) / primeEuler z =
      ∏ p ∈ SieveBoxedFamily.pool D s z, 1/(1-(p:ℝ)⁻¹) := by
  rw [euler_split D s z hu, div_mul_eq_div_div,
    div_self (ne_of_gt (euler_pos (D^(s^2))))]
  simp only [one_div, Finset.prod_inv_distrib]

theorem ratio_nonneg (D s z : ℝ) : 0 ≤ primeEuler (D^(s^2)) / primeEuler z :=
  div_nonneg (euler_pos _).le (euler_pos _).le

theorem product_inverse_le_exp (P : Finset ℕ) (w : ℕ → ℝ)
    (hw : ∀ p ∈ P, 0 ≤ w p) (hw17 : ∀ p ∈ P, w p ≤ 1/17) :
    (∏ p ∈ P, 1/(1-w p)) ≤ Real.exp ((17/16) * ∑ p ∈ P, w p) := by
  calc
    _ ≤ ∏ p ∈ P, Real.exp ((17/16)*w p) := by
      apply Finset.prod_le_prod₀
      · intro p hp
        exact div_nonneg zero_le_one (by linarith [hw17 p hp])
      · intro p hp
        exact SieveProfileMass.inverse_le_exp_sharp (w p) (hw p hp) (hw17 p hp)
    _ = _ := by rw [← Real.exp_sum, ← Finset.mul_sum]

theorem reciprocal_le_seventeenth (D s z : ℝ) (h17 : 17 ≤ D^(s^2))
    (p : ℕ) (hp : p ∈ SieveBoxedFamily.pool D s z) : (p:ℝ)⁻¹ ≤ 1/17 := by
  have hpu := ((SieveBoxedFamily.mem_pool D s z p).mp hp).2.2
  simpa only [one_div] using
    one_div_le_one_div_of_le (show (0:ℝ) < 17 by norm_num) (h17.trans hpu)

theorem ratio_le_exp (D s z : ℝ) (hu : D^(s^2) ≤ z) (h17 : 17 ≤ D^(s^2)) :
    primeEuler (D^(s^2)) / primeEuler z ≤
      Real.exp ((17/16) * SieveBoxMass.primeMass D s z) := by
  rw [ratio_eq_product_inverse D s z hu]
  exact product_inverse_le_exp _ (fun p => (p:ℝ)⁻¹)
    (fun p _ => inv_nonneg.mpr (Nat.cast_nonneg p))
    (reciprocal_le_seventeenth D s z h17)

theorem euler_le_exp_mul (D s z : ℝ) (hu : D^(s^2) ≤ z) (h17 : 17 ≤ D^(s^2)) :
    primeEuler (D^(s^2)) ≤
      Real.exp ((17/16) * SieveBoxMass.primeMass D s z) * primeEuler z :=
  (div_le_iff₀ (euler_pos z)).mp (ratio_le_exp D s z hu h17)

run_cmd do
  for decl in [``pool_split, ``pools_disjoint, ``euler_pos, ``euler_split,
      ``ratio_eq_product_inverse, ``ratio_nonneg, ``product_inverse_le_exp,
      ``reciprocal_le_seventeenth, ``ratio_le_exp, ``euler_le_exp_mul] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ACTUAL EULER FACTORIZATION AND SHARP NORMALIZED RATIO PASSED"

end SieveEulerRatio
end
