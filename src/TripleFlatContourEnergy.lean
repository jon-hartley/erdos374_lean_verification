import TripleAdoptFlatProductSaving
import TruncatedDyadicPartition
import PolynomialLogEnvelope

/-! The actual flat cofactor polynomial on a fixed finite doubling partition.
The lower frequency is exactly X^ρ, so no low-frequency mass premise occurs. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators

namespace TripleFlatContourEnergy
open Erdos374.HarmanGram152

theorem eventually_positive_energy (η ρ : ℝ) (k : ℕ)
    (hη : 0 < η) (hρ : 0 < ρ) (hρone : ρ < 1) :
    ∃ c : ℝ, 0 < c ∧ ∃ ε : ℝ, 0 < ε ∧
      ∀ᶠ X : ℝ in atTop, 2 ≤ X ∧
        ∀ (lo hi M N : ℕ) (sm sn : Finset ℕ)
          (am an : ℕ → ℂ) (U σ : ℝ),
          1 ≤ lo → ((2 ^ k * lo : ℕ) : ℝ) ≤ X → hi ≤ 2 ^ k * lo →
          X ^ η * U ^ (2 / 7 : ℝ) ≤ (lo : ℝ) →
          2 * X ^ ρ ≤ U → U ≤ X → 1 ≤ σ →
          1 ≤ M → (M : ℝ) ≤ X → U ≤ (M : ℝ) ^ 4 →
          1 ≤ N → (N : ℝ) ≤ X → U ≤ (N : ℝ) ^ 2 →
          (∀ n ∈ sm, M ≤ n ∧ n ≤ 2 * M) →
          (∀ n ∈ sn, N ≤ n ∧ n ≤ 2 * N) →
          (∑ n ∈ sm, ‖am n‖ ^ 2) ≤ X ^ ε * M →
          (∑ n ∈ sn, ‖an n‖ ^ 2) ≤ X ^ ε * N →
          (∫ t in Icc (X ^ ρ) U,
            ‖verticalDirichlet152 (Finset.Ioc lo hi) (fun _ => 1) σ t *
              verticalDirichlet152 sm am σ t *
                verticalDirichlet152 sn an σ t‖ ^ 2) ≤ X ^ (-c) := by
  obtain ⟨γ, hγ, ε, hε, hflat⟩ :=
    TripleAdoptFlatProductSaving.eventually_bound η ρ hη hρ hρone
  refine ⟨γ / 2, by positivity, ε, hε, ?_⟩
  filter_upwards [hflat, eventually_ge_atTop (2 : ℝ),
    PolynomialLogEnvelope.eventually_constant_bound
      ((k : ℝ) ^ 2) (γ / 2) (sq_nonneg _) (by positivity)] with X hp hXtwo hk
  refine ⟨hXtwo, ?_⟩
  intro lo hi M N sm sn am an U σ hlo hcap hhi hlength hUlow hUX hσ
    hM hMX hUM hN hNX hUN hsm hsn hem hen
  have hXp : 0 < X := by linarith
  have hHone : 1 ≤ X ^ ρ := Real.one_le_rpow hp.1 hρ.le
  have hHpos : 0 < X ^ ρ := by positivity
  have hT : 1 ≤ U - X ^ ρ := by linarith
  have hTU : U - X ^ ρ ≤ U := by linarith
  have hTlength : X ^ η * (U - X ^ ρ) ^ (2 / 7 : ℝ) ≤ (lo : ℝ) := by
    apply le_trans _ hlength
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact Real.rpow_le_rpow (by linarith) hTU (by norm_num)
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
      (∫ t in Icc (X ^ ρ) U,
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
    have hh := hp.2 (2 ^ j * lo) (2 ^ j * lo)
      (min (2 ^ (j + 1) * lo) hi) M N sm sn am an (X ^ ρ) (U - X ^ ρ) σ
      (hTlength.trans hbaseR) htopR le_rfl hupper hT (hTU.trans hUX) hσ (by
        intro t ht
        have htpos : 0 < t := hHpos.trans_le ht.1
        rw [abs_of_pos htpos]
        constructor
        · exact ht.1
        · linarith [ht.2])
      hM hMX (hTU.trans hUM) hN hNX (hTU.trans hUN) hsm hsn hem hen
    have hend : X ^ ρ + (U - X ^ ρ) = U := by ring
    simpa only [hend, F, mul_assoc] using hh
  have hsum := TruncatedDyadicPartition.product_energy_bound
    lo hi k σ (X ^ ρ) U (X ^ (-γ)) F hlo hhi hF hblocks
  calc
    _ ≤ (k : ℝ) ^ 2 * X ^ (-γ) := by simpa only [F, mul_assoc] using hsum
    _ ≤ X ^ (γ / 2) * X ^ (-γ) :=
      mul_le_mul_of_nonneg_right hk.2 (by positivity)
    _ = X ^ (-(γ / 2)) := by
      rw [← Real.rpow_add hXp]
      congr 1
      ring

run_cmd do
  for ax in (← Lean.collectAxioms ``eventually_positive_energy) do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"

end TripleFlatContourEnergy
