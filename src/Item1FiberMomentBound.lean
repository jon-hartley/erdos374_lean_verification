import Item1TupleCollisionCounting
import Item1FiniteMomentHolder

/-! A finite Holder bound in terms of exact frequency collisions.
The collision count and the final moment sum still require analytic estimates. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

namespace Item1FiberMomentBound
open Item1TupleCollisionCounting Item1FiniteMomentHolder

/-- Repeated frequencies produce the squared-multiplicity factor, rather
than the larger square of the number of original indices. -/
theorem norm_sum_fiber_even_pow_le {ι η : Type*} [Fintype ι] [DecidableEq η]
    (f : ι → η) (V : η → ℂ) (s : ℕ) (hs : 1 ≤ s) :
    ‖∑ i, V (f i)‖^(2*s) ≤
      (Fintype.card ι : ℝ)^(2*s-2) *
      (∑ c ∈ frequencyImage f, (fiberMultiplicity f c : ℝ)^2) *
      (∑ c ∈ frequencyImage f, ‖V c‖^(2*s)) := by
  have hpow := norm_sum_pow_le Finset.univ (fun i => V (f i)) s hs
  have hsq := pow_le_pow_left₀ (pow_nonneg (norm_nonneg _) s) hpow 2
  have he : (s-1)*2 = 2*s-2 := by omega
  have hfirst : ‖∑ i, V (f i)‖^(2*s) ≤
      (Fintype.card ι : ℝ)^(2*s-2)*(∑ i, ‖V (f i)‖^s)^2 := by
    simpa only [Finset.card_univ, mul_pow, ← pow_mul, he, Nat.mul_comm s 2] using hsq
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (frequencyImage f)
    (fun c => (fiberMultiplicity f c : ℝ)) (fun c => ‖V c‖^s)
  have hc' : (∑ c ∈ frequencyImage f, (fiberMultiplicity f c : ℝ)*‖V c‖^s)^2 ≤
      (∑ c ∈ frequencyImage f, (fiberMultiplicity f c : ℝ)^2)*
      (∑ c ∈ frequencyImage f, ‖V c‖^(2*s)) := by
    simpa only [← pow_mul, Nat.mul_comm s 2] using hc
  rw [sum_grouped f (fun c => ‖V c‖^s)] at hfirst
  exact hfirst.trans (by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hc'
      (show 0 ≤ (Fintype.card ι : ℝ)^(2*s-2) by positivity))

/-- The same bound for r-tuples, with the exact number (card ι)^r of tuples. -/
theorem norm_sum_tuple_fiber_even_pow_le {ι η : Type*}
    [Fintype ι] [DecidableEq η] (r : ℕ) (f : (Fin r → ι) → η)
    (V : η → ℂ) (s : ℕ) (hs : 1 ≤ s) :
    ‖∑ p : Fin r → ι, V (f p)‖^(2*s) ≤
      ((Fintype.card ι : ℝ)^r)^(2*s-2) *
      (∑ c ∈ frequencyImage f, (fiberMultiplicity f c : ℝ)^2) *
      (∑ c ∈ frequencyImage f, ‖V c‖^(2*s)) := by
  simpa only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow] using
    norm_sum_fiber_even_pow_le f V s hs

end Item1FiberMomentBound

run_cmd do
  for target in [``Item1FiberMomentBound.norm_sum_fiber_even_pow_le,
      ``Item1FiberMomentBound.norm_sum_tuple_fiber_even_pow_le] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "FIBER MOMENT BOUND: 2 standard-axiom theorem guards passed."
