import HarmanProductTail
import TruncatedDyadicPartition

/-!
Extend the positive product tail to a consecutive cofactor interval
covered by a fixed number of doubling blocks. The block count is fixed
before X, and its squared summation cost is absorbed explicitly.
The construction follows HarmanProductTail.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators

namespace HarmanCofactorTail
open Erdos374.HarmanGram152

theorem eventually_positive_energy (ell nu e ρ η : ℝ) (k : ℕ)
    (hell : 0 < ell) (hnu : 0 < nu) (he : 0 < e)
    (hρ : 0 < ρ) (hρell : ρ ≤ ell) (hρone : ρ < 1)
    (hη : 0 < η) (hηρ : η ≤ ρ) :
    ∃ c : ℝ, 0 < c ∧ ∃ ε : ℝ, 0 < ε ∧
      ∀ᶠ X : ℝ in atTop, 2 ≤ X ∧
        ∀ (lo hi M N : ℕ) (sm sn : Finset ℕ)
          (am an : ℕ → ℂ) (H U σ : ℝ),
          X ^ ell ≤ (lo : ℝ) → ((2 ^ k * lo : ℕ) : ℝ) ≤ X →
          hi ≤ 2 ^ k * lo →
          1 ≤ M → (M : ℝ) ≤ X → 1 ≤ N → (N : ℝ) ≤ X →
          X ^ nu ≤ (N : ℝ) →
          X ^ (e / 10) * U ^ (10 / 9 : ℝ) ≤ (lo * M * N : ℕ) →
          X ^ e * U ^ (6 / 7 : ℝ) ≤ max (lo * M : ℕ) (M * N : ℕ) →
          X ^ η ≤ H → H ≤ U → 2 * X ^ ρ ≤ U → U ≤ X → 1 ≤ σ →
          (∀ n ∈ sm, M < n ∧ n ≤ 2 * M) →
          (∀ n ∈ sn, N < n ∧ n ≤ 2 * N) →
          (∑ n ∈ sm, ‖am n‖ ^ 2) ≤ X ^ ε * M →
          (∑ n ∈ sn, ‖an n‖ ^ 2) ≤ X ^ ε * N →
          (∫ t in Icc H U,
            ‖verticalDirichlet152 (Finset.Ioc lo hi) (fun _ => 1) σ t *
              verticalDirichlet152 sm am σ t *
                verticalDirichlet152 sn an σ t‖ ^ 2) ≤ X ^ (-c) := by
  obtain ⟨γ, hγ, ε, hε, htail⟩ := HarmanProductTail.eventually_positive_energy
    ell nu e ρ η hell hnu he hρ hρell hρone hη hηρ
  refine ⟨γ / 2, by positivity, ε, hε, ?_⟩
  filter_upwards [htail, PolynomialLogEnvelope.eventually_constant_bound
    ((k : ℝ) ^ 2) (γ / 2) (sq_nonneg _) (by positivity)] with X hp hk
  refine ⟨hp.1, ?_⟩
  intro lo hi M N sm sn am an H U σ hlo hcap hhi
    hM hMX hN hNX hNlow hproduct hpair hH hHU hUlow hUX hσ
    hsm hsn hem hen
  have hX : 1 ≤ X := by linarith [hp.1]
  have hXp : 0 < X := by linarith [hp.1]
  have hloNat : 1 ≤ lo := by
    exact_mod_cast (Real.one_le_rpow hX hell.le).trans hlo
  let F := fun t => verticalDirichlet152 sm am σ t * verticalDirichlet152 sn an σ t
  have hF : Continuous F := by
    apply Continuous.mul
    · apply NormalizedMeanSquare.continuous_vertical
      intro n hn
      have hh := (hsm n hn).1
      omega
    · apply NormalizedMeanSquare.continuous_vertical
      intro n hn
      have hh := (hsn n hn).1
      omega
  have hblocks : ∀ j ∈ Finset.range k,
      (∫ t in Icc H U,
        ‖verticalDirichlet152
          (Finset.Ioc (2 ^ j * lo) (min (2 ^ (j + 1) * lo) hi))
          (fun _ => 1) σ t * F t‖ ^ 2) ≤ X ^ (-γ) := by
    intro j hj
    have hjk : j ≤ k := (Finset.mem_range.mp hj).le
    have hpow : 2 ^ j ≤ (2 : ℕ) ^ k := Nat.pow_le_pow_right (by omega) hjk
    have hbase : lo ≤ 2 ^ j * lo := by
      have hh : 1 ≤ (2 : ℕ) ^ j := Nat.one_le_iff_ne_zero.mpr (by positivity)
      nlinarith
    have htop : 2 ^ j * lo ≤ 2 ^ k * lo := Nat.mul_le_mul_right lo hpow
    have hbaseR : (lo : ℝ) ≤ (2 ^ j * lo : ℕ) := by exact_mod_cast hbase
    have htopR : ((2 ^ j * lo : ℕ) : ℝ) ≤ X :=
      (by exact_mod_cast htop : ((2 ^ j * lo : ℕ) : ℝ) ≤ (2 ^ k * lo : ℕ)).trans hcap
    have hupper : min (2 ^ (j + 1) * lo) hi ≤ 2 * (2 ^ j * lo) := by
      calc
        _ ≤ 2 ^ (j + 1) * lo := min_le_left _ _
        _ = _ := by rw [pow_succ]; ring
    have hprod : (lo * M * N : ℕ) ≤ (2 ^ j * lo) * M * N :=
      Nat.mul_le_mul_right N (Nat.mul_le_mul_right M hbase)
    have hpairNat : max (lo * M) (M * N) ≤ max ((2 ^ j * lo) * M) (M * N) :=
      max_le_max (Nat.mul_le_mul_right M hbase) le_rfl
    have hh := hp.2 (2 ^ j * lo) (2 ^ j * lo)
      (min (2 ^ (j + 1) * lo) hi) M N sm sn am an H U σ
      (hlo.trans hbaseR) htopR le_rfl hupper hM hMX hN hNX hNlow
      (hproduct.trans (by exact_mod_cast hprod))
      (hpair.trans (by exact_mod_cast hpairNat))
      hH hHU hUlow hUX hσ hsm hsn hem hen
    simpa only [F, mul_assoc] using hh
  have hsum := TruncatedDyadicPartition.product_energy_bound
    lo hi k σ H U (X ^ (-γ)) F hloNat hhi hF hblocks
  calc
    _ ≤ (k : ℝ) ^ 2 * X ^ (-γ) := by
      simpa only [F, mul_assoc] using hsum
    _ ≤ X ^ (γ / 2) * X ^ (-γ) :=
      mul_le_mul_of_nonneg_right hk.2 (by positivity)
    _ = X ^ (-(γ / 2)) := by
      rw [← Real.rpow_add hXp]
      congr 1
      ring

end HarmanCofactorTail

#print axioms HarmanCofactorTail.eventually_positive_energy
run_cmd do
  let axioms ← Lean.collectAxioms ``HarmanCofactorTail.eventually_positive_energy
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"
  Lean.logInfo "HARMAN COFACTOR TAIL PASSED"
