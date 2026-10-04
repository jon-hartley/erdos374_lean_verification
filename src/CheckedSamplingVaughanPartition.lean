import CheckedSamplingDyadicVaughan

/-!
Exact finite partition of the Vaughan Type II convolution. Endpoints and
the omitted index one are accounted for before any norm estimate.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open scoped BigOperators

namespace VaughanPartition
open Erdos374.Vaughan145 Erdos374.BilinearCorrelation152
open Erdos374.ReciprocalCharacter151

theorem weighted_box (f g : ArithmeticFunction ℝ) (P M : ℕ) (u v : ℝ) :
    phaseSum (Finset.Ioc P M) (fun t => character u v t) (f * g) =
      ∑ d ∈ Finset.Ioc 0 M, ∑ k ∈ Finset.Ioc 0 M,
        (f d : ℂ) * (g k : ℂ) * bandCharacter P M u v d k := by
  classical
  rw [Erdos374.VaughanBilinear152.weighted_convolution_pairs,
    Finset.sum_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro k hk
  simp only [bandCharacter, Nat.cast_mul]
  split_ifs <;> simp

theorem sum_Ioc_extend (M N : ℕ) (f : ℕ → ℂ)
    (hMN : M ≤ N) (hN : 1 ≤ N) (h1 : f 1 = 0)
    (htail : ∀ i : ℕ, M < i → f i = 0) :
    (∑ i ∈ Finset.Ioc 0 M, f i) = ∑ i ∈ Finset.Ioc 1 N, f i := by
  have hext : (∑ i ∈ Finset.Ioc 0 M, f i) = ∑ i ∈ Finset.Ioc 0 N, f i := by
    apply Finset.sum_subset
    · intro i hi
      simp only [Finset.mem_Ioc] at hi ⊢
      omega
    · intro i hi hnot
      apply htail
      simp only [Finset.mem_Ioc] at hi hnot
      omega
  rw [← Finset.sum_Ioc_consecutive f (by omega : 0 ≤ 1) hN] at hext
  simpa [h1] using hext

theorem band_zero_outer (P M d k : ℕ) (u v : ℝ)
    (hd : M < d) (hk : 1 ≤ k) : bandCharacter P M u v d k = 0 := by
  have hprod : M < d * k := hd.trans_le (by nlinarith)
  simp [bandCharacter, show ¬d * k ≤ M by omega]

theorem band_zero_inner (P M d k : ℕ) (u v : ℝ)
    (hd : 1 ≤ d) (hk : M < k) : bandCharacter P M u v d k = 0 := by
  have hprod : M < d * k := hk.trans_le (by nlinarith)
  simp [bandCharacter, show ¬d * k ≤ M by omega]

theorem typeII_box_extend (U V P M N : ℕ) (u v : ℝ)
    (hU : 1 ≤ U) (hV : 1 ≤ V) (hMN : M ≤ N) (hN : 1 ≤ N) :
    phaseSum (Finset.Ioc P M) (fun t => character u v t)
      (high U muR * beta V) =
      ∑ d ∈ Finset.Ioc 1 N, ∑ k ∈ Finset.Ioc 1 N,
        (high U muR d : ℂ) * (beta V k : ℂ) * bandCharacter P M u v d k := by
  rw [weighted_box]
  trans ∑ d ∈ Finset.Ioc 0 M, ∑ k ∈ Finset.Ioc 1 N,
    (high U muR d : ℂ) * (beta V k : ℂ) * bandCharacter P M u v d k
  · apply Finset.sum_congr rfl
    intro d hd
    apply sum_Ioc_extend M N _ hMN hN
    · simp [beta_zero_of_le hV]
    · intro k hk
      rw [band_zero_inner P M d k u v (by have := (Finset.mem_Ioc.mp hd).1; omega) hk]
      simp
  · apply sum_Ioc_extend M N _ hMN hN
    · simp [high_zero_of_le muR hU]
    · intro d hd
      apply Finset.sum_eq_zero
      intro k hk
      rw [band_zero_outer P M d k u v hd (by have := (Finset.mem_Ioc.mp hk).1; omega)]
      simp

theorem typeII_dyadic_identity (U V P M L : ℕ) (u v : ℝ)
    (hU : 1 ≤ U) (hV : 1 ≤ V) (hM : M ≤ 2 ^ L) :
    phaseSum (Finset.Ioc P M) (fun t => character u v t)
      (high U muR * beta V) =
      ∑ j ∈ Finset.range L, ∑ h ∈ Finset.range L,
        ∑ d ∈ Finset.Ioc (2 ^ j) (2 ^ (j + 1)), (high U muR d : ℂ) *
          ∑ k ∈ Finset.Ioc (2 ^ h) (2 ^ (h + 1)),
            (beta V k : ℂ) * bandCharacter P M u v d k := by
  rw [typeII_box_extend U V P M (2 ^ L) u v hU hV hM
    (one_le_pow₀ (by norm_num))]
  symm
  simp_rw [Finset.mul_sum, ← mul_assoc]
  exact DyadicVaughan.double_sum_dyadic_intervals L _

end VaughanPartition

#print axioms VaughanPartition.typeII_dyadic_identity
run_cmd do
  let axioms ← Lean.collectAxioms ``VaughanPartition.typeII_dyadic_identity
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"
  Lean.logInfo "VAUGHAN PARTITION PASSED"

run_cmd do
  for target in [``VaughanPartition.weighted_box,
      ``VaughanPartition.sum_Ioc_extend,
      ``VaughanPartition.band_zero_outer,
      ``VaughanPartition.band_zero_inner,
      ``VaughanPartition.typeII_box_extend,
      ``VaughanPartition.typeII_dyadic_identity] do
    for ax in (← Lean.collectAxioms target) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "CHECKED SAMPLING PORT: ALL EXPORTED THEOREMS GUARDED"
