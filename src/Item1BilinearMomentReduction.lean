import Item1FiberMomentBound
import Item1ComplexPhaseAlignment

/-! The finite bilinear Holder reduction. The tuple factorization is an
algebraic identity; neither of the two remaining factors is estimated here. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section

namespace Item1BilinearMomentReduction
open Item1TupleCollisionCounting Item1FiniteMomentHolder
open Item1FiberMomentBound Item1ComplexPhaseAlignment

/-- Two finite power-mean steps and Cauchy-Schwarz produce the exact
collision factor. Unit complex weights are constructed, including at zeros. -/
theorem bilinear_even_moment_reduction {ι κ η : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq η]
    (r s : ℕ) (hr : 1 ≤ r) (hs : 1 ≤ s)
    (z : ι → κ → ℂ) (f : (Fin r → ι) → η) (W : η → κ → ℂ)
    (hfactor : ∀ (p : Fin r → ι) (b : κ), ∏ l, z (p l) b = W (f p) b) :
    ∃ ε : κ → ℂ, (∀ b, ‖ε b‖ = 1) ∧
      ‖∑ b, ∑ i, z i b‖^(2*r*s) ≤
        (Fintype.card κ : ℝ)^(2*r*s-2*s) *
        (Fintype.card ι : ℝ)^(2*r*s-2*r) *
        (∑ c ∈ frequencyImage f, (fiberMultiplicity f c : ℝ)^2) *
        (∑ c ∈ frequencyImage f, ‖∑ b, ε b*W c b‖^(2*s)) := by
  classical
  let ε : κ → ℂ := fun b => aligningUnit ((∑ i, z i b)^r)
  let V : η → ℂ := fun c => ∑ b, ε b*W c b
  refine ⟨ε, fun b => norm_aligningUnit _, ?_⟩
  have hexp : r*(2*s) = 2*r*s := by ring
  have hexpB : (r-1)*(2*s) = 2*r*s-2*s := by
    rw [Nat.sub_mul, Nat.one_mul, hexp]
  have hexpA : r*(2*s-2) = 2*r*s-2*r := by
    rw [Nat.mul_sub, hexp]
    congr 1
    ring
  have hsum : (∑ b, ε b*(∑ i, z i b)^r) = ∑ p : Fin r → ι, V (f p) := by
    simp_rw [Fintype.sum_pow, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro b _
    rw [hfactor p b]
  have halign : (∑ b, ‖∑ i, z i b‖^r) = ‖∑ p : Fin r → ι, V (f p)‖ := by
    calc
      _ = ‖∑ b, ε b*(∑ i, z i b)^r‖ :=
        sum_norm_pow_eq_norm_aligned_sum Finset.univ (fun b => ∑ i, z i b) r
      _ = _ := congrArg norm hsum
  have hbase := norm_sum_pow_le Finset.univ (fun b => ∑ i, z i b) r hr
  rw [halign] at hbase
  have hraise := pow_le_pow_left₀ (pow_nonneg (norm_nonneg _) r) hbase (2*s)
  have hfirst : ‖∑ b, ∑ i, z i b‖^(2*r*s) ≤
      (Fintype.card κ : ℝ)^(2*r*s-2*s)*
        ‖∑ p : Fin r → ι, V (f p)‖^(2*s) := by
    simpa only [Finset.card_univ, mul_pow, ← pow_mul, hexp, hexpB] using hraise
  have hsecond : ‖∑ p : Fin r → ι, V (f p)‖^(2*s) ≤
      (Fintype.card ι : ℝ)^(2*r*s-2*r) *
      (∑ c ∈ frequencyImage f, (fiberMultiplicity f c : ℝ)^2) *
      (∑ c ∈ frequencyImage f, ‖V c‖^(2*s)) := by
    simpa only [← pow_mul, hexpA] using norm_sum_tuple_fiber_even_pow_le r f V s hs
  exact hfirst.trans (by
    simpa only [V, mul_assoc] using mul_le_mul_of_nonneg_left hsecond
      (show 0 ≤ (Fintype.card κ : ℝ)^(2*r*s-2*s) by positivity))

end Item1BilinearMomentReduction

run_cmd do
  for ax in (← Lean.collectAxioms ``Item1BilinearMomentReduction.bilinear_even_moment_reduction) do
    unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
      throwError "Unexpected axiom {ax} in bilinear_even_moment_reduction"
  Lean.logInfo "BILINEAR MOMENT REDUCTION: 1 standard-axiom theorem guard passed."
