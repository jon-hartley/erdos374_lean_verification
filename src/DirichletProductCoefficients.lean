import DirichletPowerEnergy

/-!
Coefficients of a product of two different finite Dirichlet polynomials.
This extends the grouping argument in DirichletPowerCoefficients to
separate supports and weights. The energy loss uses the already proved
divisor bound; no mean-value or prime-distribution premise is introduced.
-/

set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open scoped BigOperators

namespace DirichletProductCoefficients

def productIndex (pair : ℕ × ℕ) : ℕ := pair.1 * pair.2

def pairWeight (left right : ℕ → ℂ) (pair : ℕ × ℕ) : ℂ :=
  left pair.1 * right pair.2

def coefficient (leftSupport rightSupport : Finset ℕ)
    (left right : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ pair ∈ (leftSupport ×ˢ rightSupport).filter
    (fun pair => productIndex pair = n), pairWeight left right pair

theorem fiber_card_bound (leftSupport rightSupport : Finset ℕ)
    (n : ℕ) (hn : n ≠ 0) :
    ((leftSupport ×ˢ rightSupport).filter
      (fun pair => productIndex pair = n)).card ≤ n.divisors.card ^ 2 := by
  have hsub : (leftSupport ×ˢ rightSupport).filter
      (fun pair => productIndex pair = n) ⊆ n.divisors ×ˢ n.divisors := by
    intro pair hp
    have heq := (Finset.mem_filter.mp hp).2
    apply Finset.mem_product.mpr
    constructor
    · apply Nat.mem_divisors.mpr
      exact ⟨⟨pair.2, heq.symm⟩, hn⟩
    · apply Nat.mem_divisors.mpr
      refine ⟨⟨pair.1, ?_⟩, hn⟩
      simpa only [productIndex, mul_comm] using heq.symm
  simpa only [Finset.card_product, pow_two] using Finset.card_le_card hsub

theorem pair_energy (leftSupport rightSupport : Finset ℕ)
    (left right : ℕ → ℂ) :
    (∑ pair ∈ leftSupport ×ˢ rightSupport, ‖pairWeight left right pair‖ ^ 2) =
      (∑ n ∈ leftSupport, ‖left n‖ ^ 2) *
        (∑ n ∈ rightSupport, ‖right n‖ ^ 2) := by
  simp only [Finset.sum_product, pairWeight, norm_mul, mul_pow,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem grouped_sum (leftSupport rightSupport target : Finset ℕ)
    (left right kernel : ℕ → ℂ)
    (hmap : ∀ pair ∈ leftSupport ×ˢ rightSupport, productIndex pair ∈ target) :
    (∑ n ∈ target, coefficient leftSupport rightSupport left right n * kernel n) =
      ∑ pair ∈ leftSupport ×ˢ rightSupport,
        pairWeight left right pair * kernel (productIndex pair) := by
  unfold coefficient
  simp_rw [Finset.sum_mul]
  have hh := Finset.sum_fiberwise_of_maps_to hmap
    (fun pair => pairWeight left right pair * kernel (productIndex pair))
  rw [← hh]
  apply Finset.sum_congr rfl
  intro n _
  apply Finset.sum_congr rfl
  intro pair hp
  rw [(Finset.mem_filter.mp hp).2]

theorem grouped_energy_bound (leftSupport rightSupport target : Finset ℕ)
    (left right : ℕ → ℂ) (D : ℝ)
    (hmap : ∀ pair ∈ leftSupport ×ˢ rightSupport, productIndex pair ∈ target)
    (hcard : ∀ n ∈ target,
      (((leftSupport ×ˢ rightSupport).filter
        (fun pair => productIndex pair = n)).card : ℝ) ≤ D) :
    (∑ n ∈ target, ‖coefficient leftSupport rightSupport left right n‖ ^ 2) ≤
      D * (∑ n ∈ leftSupport, ‖left n‖ ^ 2) *
        (∑ n ∈ rightSupport, ‖right n‖ ^ 2) := by
  calc
    _ ≤ ∑ n ∈ target, D * ∑ pair ∈ (leftSupport ×ˢ rightSupport).filter
        (fun pair => productIndex pair = n), ‖pairWeight left right pair‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro n hn
      apply (Erdos374.ExponentialSum151.norm_sum_sq_le_card_energy
        ((leftSupport ×ˢ rightSupport).filter (fun pair => productIndex pair = n))
        (pairWeight left right)).trans
      exact mul_le_mul_of_nonneg_right (hcard n hn)
        (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    _ = D * (∑ pair ∈ leftSupport ×ˢ rightSupport,
        ‖pairWeight left right pair‖ ^ 2) := by
      rw [← Finset.mul_sum, Finset.sum_fiberwise_of_maps_to hmap]
    _ = _ := by rw [pair_energy]; ring

theorem product_support (K M : ℕ) (hM : 1 ≤ M)
    (leftSupport rightSupport : Finset ℕ)
    (hleft : ∀ n ∈ leftSupport, K < n ∧ n ≤ 2 * K)
    (hright : ∀ n ∈ rightSupport, M < n ∧ n ≤ 2 * M)
    (pair : ℕ × ℕ) (hp : pair ∈ leftSupport ×ˢ rightSupport) :
    productIndex pair ∈ Finset.Ioc (K * M) (4 * K * M) := by
  obtain ⟨hl, hr⟩ := Finset.mem_product.mp hp
  have ha := hleft pair.1 hl
  have hb := hright pair.2 hr
  apply Finset.mem_Ioc.mpr
  constructor
  · have hh := Nat.mul_lt_mul_of_pos_right ha.1 (show 0 < M by omega)
    exact hh.trans_le (Nat.mul_le_mul_left pair.1 hb.1.le)
  · have hh := Nat.mul_le_mul ha.2 hb.2
    dsimp [productIndex]
    nlinarith

theorem energy_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ (K M : ℕ) (leftSupport rightSupport : Finset ℕ)
      (left right : ℕ → ℂ), 1 ≤ K → 1 ≤ M →
      (∀ n ∈ leftSupport, K < n ∧ n ≤ 2 * K) →
      (∀ n ∈ rightSupport, M < n ∧ n ≤ 2 * M) →
      (∑ n ∈ Finset.Ioc (K * M) (4 * K * M),
        ‖coefficient leftSupport rightSupport left right n‖ ^ 2) ≤
        D * ((4 * K * M : ℕ) : ℝ) ^ ε *
          (∑ n ∈ leftSupport, ‖left n‖ ^ 2) *
            (∑ n ∈ rightSupport, ‖right n‖ ^ 2) := by
  obtain ⟨D, hD, hdiv⟩ := DirichletPowerEnergy.divisor_power_bound 2 (by omega) ε hε
  refine ⟨D, hD, ?_⟩
  intro K M leftSupport rightSupport left right hK hM hleft hright
  apply grouped_energy_bound leftSupport rightSupport _ left right
    (D * ((4 * K * M : ℕ) : ℝ) ^ ε)
    (product_support K M hM leftSupport rightSupport hleft hright)
  intro n hn
  have hbounds := Finset.mem_Ioc.mp hn
  have hn0 : n ≠ 0 := by omega
  have hcast : (n : ℝ) ≤ (4 * K * M : ℕ) := by exact_mod_cast hbounds.2
  calc
    _ ≤ (n.divisors.card : ℝ) ^ 2 := by
      exact_mod_cast fiber_card_bound leftSupport rightSupport n hn0
    _ ≤ D * (n : ℝ) ^ ε := hdiv n
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg n) hcast hε.le) hD.le

end DirichletProductCoefficients

#print axioms DirichletProductCoefficients.energy_bound
run_cmd do
  for target in [``DirichletProductCoefficients.grouped_sum,
      ``DirichletProductCoefficients.energy_bound] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "DIRICHLET PRODUCT COEFFICIENTS PASSED"
