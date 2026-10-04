import Item1FiniteFourierOrthogonality

/-! Exact even moments of finite polynomial Fourier sums.
These are identities counting ordered tuples with equal sums of frequencies.
They do not assert a Vinogradov mean-value upper bound. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory UnitAddTorus

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace Item1PolynomialMomentIdentity

/-- The frequency of an ordered tuple is the sum of its individual frequencies. -/
def tupleFrequency {ι : Type*} {d r : ℕ} (v : ι → (Fin d → ℤ))
    (p : Fin r → ι) : Fin d → ℤ := ∑ l, v (p l)

/-- Multiplication of finitely many torus characters adds their frequencies. -/
theorem mFourier_finset_sum {κ : Type*} (d : ℕ) (s : Finset κ)
    (v : κ → (Fin d → ℤ)) (a : UnitAddTorus (Fin d)) :
    mFourier (∑ i ∈ s, v i) a = ∏ i ∈ s, mFourier (v i) a := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, Finset.prod_empty, mFourier_zero,
      ContinuousMap.one_apply]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi, mFourier_add, ih]

/-- The power expansion keeps every ordered tuple, including repeated entries. -/
theorem fourier_sum_pow {ι : Type*} [Fintype ι] (d r : ℕ)
    (v : ι → (Fin d → ℤ)) (a : UnitAddTorus (Fin d)) :
    (∑ i, mFourier (v i) a) ^ r =
      ∑ p : Fin r → ι, mFourier (tupleFrequency v p) a := by
  classical
  rw [Fintype.sum_pow]
  apply Finset.sum_congr rfl
  intro p hp
  exact (mFourier_finset_sum d Finset.univ (fun l : Fin r => v (p l)) a).symm

/-- The even norm power is a square norm of the tuple expansion. -/
theorem norm_even_pow_eq_tuple_square {ι : Type*} [Fintype ι] (d r : ℕ)
    (v : ι → (Fin d → ℤ)) (a : UnitAddTorus (Fin d)) :
    ‖∑ i, mFourier (v i) a‖ ^ (2*r) =
      ‖∑ p : Fin r → ι, mFourier (tupleFrequency v p) a‖ ^ 2 := by
  rw [← fourier_sum_pow d r v a, norm_pow, ← pow_mul, Nat.mul_comm r 2]

/-- All the even moments used below are integrable on normalized Haar measure. -/
theorem integrable_even_moment {ι : Type*} [Fintype ι] (d r : ℕ)
    (v : ι → (Fin d → ℤ)) :
    Integrable (fun a : UnitAddTorus (Fin d) =>
      ‖∑ i, mFourier (v i) a‖ ^ (2*r)) := by
  simp_rw [norm_even_pow_eq_tuple_square d r v]
  exact Item1FiniteFourierOrthogonality.integrable_sq_norm_sum d (tupleFrequency v)

/-- The exact even moment is the ordered tuple-frequency collision count. -/
theorem even_moment_eq_collisions {ι : Type*} [Fintype ι] (d r : ℕ)
    (v : ι → (Fin d → ℤ)) :
    (∫ a : UnitAddTorus (Fin d), ‖∑ i, mFourier (v i) a‖ ^ (2*r)) =
      ∑ p : Fin r → ι, ∑ q : Fin r → ι,
        if tupleFrequency v p = tupleFrequency v q then (1 : ℝ) else 0 := by
  simp_rw [norm_even_pow_eq_tuple_square d r v]
  exact Item1FiniteFourierOrthogonality.integral_sq_norm_sum_eq_collisions d
    (tupleFrequency v)

/-- The integer polynomial frequency vector uses exactly degrees 1 through d. -/
def powerFrequency {ι : Type*} (d : ℕ) (w : ι → ℤ) (i : ι) : Fin d → ℤ :=
  fun j => w i ^ (j.val+1)

/-- Polynomial even moments count equal power sums in every prescribed degree.
The integer values may repeat; no estimate on the count is assumed. -/
theorem polynomial_moment_eq_power_sum_count {ι : Type*} [Fintype ι] (d r : ℕ)
    (w : ι → ℤ) :
    (∫ a : UnitAddTorus (Fin d),
      ‖∑ i, mFourier (powerFrequency d w i) a‖ ^ (2*r)) =
      ∑ p : Fin r → ι, ∑ q : Fin r → ι,
        if (∀ j : Fin d,
          ∑ l, w (p l) ^ (j.val+1) = ∑ l, w (q l) ^ (j.val+1))
        then (1 : ℝ) else 0 := by
  classical
  rw [even_moment_eq_collisions d r (powerFrequency d w)]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  have heq : tupleFrequency (powerFrequency d w) p =
      tupleFrequency (powerFrequency d w) q ↔
      ∀ j : Fin d, ∑ l, w (p l) ^ (j.val+1) = ∑ l, w (q l) ^ (j.val+1) := by
    simp only [funext_iff, tupleFrequency, Finset.sum_apply, powerFrequency]
  simp only [heq]

end Item1PolynomialMomentIdentity

run_cmd do
  for target in [``Item1PolynomialMomentIdentity.mFourier_finset_sum,
      ``Item1PolynomialMomentIdentity.fourier_sum_pow,
      ``Item1PolynomialMomentIdentity.norm_even_pow_eq_tuple_square,
      ``Item1PolynomialMomentIdentity.integrable_even_moment,
      ``Item1PolynomialMomentIdentity.even_moment_eq_collisions,
      ``Item1PolynomialMomentIdentity.polynomial_moment_eq_power_sum_count] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "POLYNOMIAL MOMENT IDENTITIES: 6 standard-axiom theorem guards passed."
