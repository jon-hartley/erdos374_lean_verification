import HarmanProductSaving
import DyadicCoefficientEnergyMass
import FlatProductLowBand
import CompactIntegralSplit
import SmoothedWindowTransfer

/-!
Positive frequency tails starting above a fixed positive power of X.
The low band uses coefficient energy to bound absolute masses; no
pointwise bound of one is needed. The high band is HarmanProductSaving.
The construction follows HarmanProductWindow with this stronger input.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators

namespace HarmanProductTail
open Erdos374.HarmanGram152 SmoothedDirichletKernel

theorem eventually_positive_energy (ell nu e ρ η : ℝ)
    (hell : 0 < ell) (hnu : 0 < nu) (he : 0 < e)
    (hρ : 0 < ρ) (hρell : ρ ≤ ell) (hρone : ρ < 1)
    (hη : 0 < η) (hηρ : η ≤ ρ) :
    ∃ c : ℝ, 0 < c ∧ ∃ ε : ℝ, 0 < ε ∧
      ∀ᶠ X : ℝ in atTop, 2 ≤ X ∧
        ∀ (K lo hi M N : ℕ) (sm sn : Finset ℕ)
          (am an : ℕ → ℂ) (H U σ : ℝ),
          X ^ ell ≤ (K : ℝ) → (K : ℝ) ≤ X → K ≤ lo → hi ≤ 2 * K →
          1 ≤ M → (M : ℝ) ≤ X → 1 ≤ N → (N : ℝ) ≤ X →
          X ^ nu ≤ (N : ℝ) →
          X ^ (e / 10) * U ^ (10 / 9 : ℝ) ≤ (K * M * N : ℕ) →
          X ^ e * U ^ (6 / 7 : ℝ) ≤ max (K * M : ℕ) (M * N : ℕ) →
          X ^ η ≤ H → H ≤ U → 2 * X ^ ρ ≤ U → U ≤ X → 1 ≤ σ →
          (∀ n ∈ sm, M < n ∧ n ≤ 2 * M) →
          (∀ n ∈ sn, N < n ∧ n ≤ 2 * N) →
          (∑ n ∈ sm, ‖am n‖ ^ 2) ≤ X ^ ε * M →
          (∑ n ∈ sn, ‖an n‖ ^ 2) ≤ X ^ ε * N →
          (∫ t in Icc H U,
            ‖verticalDirichlet152 (Finset.Ioc lo hi) (fun _ => 1) σ t *
              verticalDirichlet152 sm am σ t *
                verticalDirichlet152 sn an σ t‖ ^ 2) ≤ X ^ (-c) := by
  obtain ⟨c₀, hc₀, ε₀, hε₀, hproduct⟩ :=
    HarmanProductSaving.eventually_bound ell nu e ρ hell hnu he hρ hρone.le
  let ε := min ε₀ (η / 8)
  let d := min c₀ (η / 2)
  have hε : 0 < ε := lt_min hε₀ (by positivity)
  have hd : 0 < d := lt_min hc₀ (by positivity)
  refine ⟨d / 2, by positivity, ε, hε, ?_⟩
  filter_upwards [hproduct, eventually_ge_atTop (2 : ℝ),
    PolynomialLogEnvelope.eventually_constant_bound ((16 * Real.pi) ^ 2)
      (η / 4) (sq_nonneg _) (by positivity),
    PolynomialLogEnvelope.eventually_constant_bound 2 (d / 2)
      (by norm_num) (by positivity)] with X hp hX2 hconst htwo
  refine ⟨hX2, ?_⟩
  intro K lo hi M N sm sn am an H U σ hKlow hKX hlo hhi
    hM hMX hN hNX hNlow hproductU hpairU hH hHU hUlower hUX
    hσ hsm hsn hem hen
  have hX : 1 ≤ X := by linarith
  have hXp : 0 < X := by linarith
  have hηpos : 0 < X ^ η := Real.rpow_pos_of_pos hXp _
  have hsplitpos : 0 < X ^ ρ := Real.rpow_pos_of_pos hXp _
  have hηsplit : X ^ η ≤ X ^ ρ :=
    Real.rpow_le_rpow_of_exponent_le hX hηρ
  have hsplitK : X ^ ρ ≤ (K : ℝ) :=
    (Real.rpow_le_rpow_of_exponent_le hX hρell).trans hKlow
  have hK : 1 ≤ K := by
    exact_mod_cast (Real.one_le_rpow hX hell.le).trans hKlow
  let T := U - X ^ ρ
  have hT : 1 ≤ T := by dsimp [T]; linarith [Real.one_le_rpow hX hρ.le]
  have hTU : T ≤ U := by dsimp [T]; linarith
  have hTX : T ≤ X := hTU.trans hUX
  have hproductT : X ^ (e / 10) * T ^ (10 / 9 : ℝ) ≤ (K * M * N : ℕ) := by
    apply le_trans _ hproductU
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by linarith) hTU (by norm_num)) (by positivity)
  have hpairT : X ^ e * T ^ (6 / 7 : ℝ) ≤ max (K * M : ℕ) (M * N : ℕ) := by
    apply le_trans _ hpairU
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by linarith) hTU (by norm_num)) (by positivity)
  have htimes : ∀ t ∈ Icc (X ^ ρ) (X ^ ρ + T),
      X ^ ρ ≤ |t| ∧ |t| ≤ X := by
    intro t ht
    rw [abs_of_pos (hsplitpos.trans_le ht.1)]
    have hupper : t ≤ U := by
      have hh := ht.2
      dsimp [T] at hh
      linarith
    exact ⟨ht.1, hupper.trans hUX⟩
  have hεle : X ^ ε ≤ X ^ ε₀ :=
    Real.rpow_le_rpow_of_exponent_le hX (min_le_left _ _)
  have hhigh := hp.2 K lo hi M N sm sn am an (X ^ ρ) T σ
    hKlow hKX hlo hhi hM hMX hN hNX hNlow hproductT hpairT
    hT hTX hσ hsm hsn
    (hem.trans (mul_le_mul_of_nonneg_right hεle (Nat.cast_nonneg M)))
    (hen.trans (mul_le_mul_of_nonneg_right hεle (Nat.cast_nonneg N))) htimes
  have hend : X ^ ρ + T = U := by dsimp [T]; ring
  rw [hend] at hhigh
  have hmpos : ∀ n ∈ sm, 0 < n := by
    intro n hn
    have hh := (hsm n hn).1
    omega
  have hnpos : ∀ n ∈ sn, 0 < n := by
    intro n hn
    have hh := (hsn n hn).1
    omega
  let F := fun t =>
    verticalDirichlet152 (Finset.Ioc lo hi) (fun _ => 1) σ t *
      verticalDirichlet152 sm am σ t * verticalDirichlet152 sn an σ t
  have hF : Continuous F := by
    exact ((NormalizedMeanSquare.continuous_vertical _ _ σ (by
      intro n hn
      have hh := (Finset.mem_Ioc.mp hn).1
      omega)).mul (NormalizedMeanSquare.continuous_vertical sm am σ hmpos)).mul
        (NormalizedMeanSquare.continuous_vertical sn an σ hnpos)
  have hm := DyadicCoefficientEnergyMass.rpow_bound sm M am σ X ε hM hσ hXp hsm hem
  have hn := DyadicCoefficientEnergyMass.rpow_bound sn N an σ X ε hN hσ hXp hsn hen
  have hmnonneg := mass_nonnegative sm am σ
  have hnnonneg := mass_nonnegative sn an σ
  have hmass : ((16 * Real.pi) * coefficientMass sm am σ *
      coefficientMass sn an σ) ^ 2 ≤ (16 * Real.pi) ^ 2 * X ^ (2 * ε) := by
    calc
      _ ≤ ((16 * Real.pi) * X ^ (ε / 2) * X ^ (ε / 2)) ^ 2 := by
        gcongr
      _ = _ := by
        rw [mul_assoc, ← Real.rpow_add hXp, mul_pow,
          ← Real.rpow_mul_natCast hXp.le]
        congr 2
        ring
  have hlow : (∫ t in Icc (X ^ η) (X ^ ρ), ‖F t‖ ^ 2) ≤ X ^ (-η / 2) := by
    apply (FlatProductLowBand.mean_square_bound K lo hi sm sn am an
      (X ^ η) (X ^ ρ) σ hK hlo hhi hηpos hsplitK hσ hmpos hnpos).trans
    calc
      _ ≤ ((16 * Real.pi) ^ 2 * X ^ (2 * ε)) / X ^ η :=
        div_le_div_of_nonneg_right hmass hηpos.le
      _ ≤ (X ^ (η / 4) * X ^ (2 * ε)) / X ^ η := by gcongr; exact hconst.2
      _ = X ^ (η / 4 + 2 * ε - η) := by
        rw [← Real.rpow_add hXp, ← Real.rpow_sub hXp]
      _ ≤ X ^ (-η / 2) := by
        apply Real.rpow_le_rpow_of_exponent_le hX
        have hh : ε ≤ η / 8 := min_le_right _ _
        linarith
  have htotal : (∫ t in Icc (X ^ η) U, ‖F t‖ ^ 2) ≤ X ^ (-d / 2) := by
    rw [CompactIntegralSplit.split (fun t => ‖F t‖ ^ 2) (X ^ η) (X ^ ρ) U
      hηsplit (by linarith) (hF.norm.pow 2).integrableOn_Icc]
    calc
      _ ≤ X ^ (-η / 2) + X ^ (-c₀) := add_le_add hlow hhigh
      _ ≤ X ^ (-d) + X ^ (-d) := by
        apply add_le_add
        · apply Real.rpow_le_rpow_of_exponent_le hX
          have hh : d ≤ η / 2 := min_le_right _ _
          linarith
        · apply Real.rpow_le_rpow_of_exponent_le hX
          have hh : d ≤ c₀ := min_le_left _ _
          linarith
      _ = 2 * X ^ (-d) := by ring
      _ ≤ X ^ (d / 2) * X ^ (-d) :=
        mul_le_mul_of_nonneg_right htwo.2 (by positivity)
      _ = X ^ (-d / 2) := by rw [← Real.rpow_add hXp]; congr 1; ring
  have hsubset : (∫ t in Icc H U, ‖F t‖ ^ 2) ≤
      ∫ t in Icc (X ^ η) U, ‖F t‖ ^ 2 := by
    apply setIntegral_mono_set (hF.norm.pow 2).integrableOn_Icc
    · filter_upwards with t
      exact sq_nonneg _
    · exact Filter.Eventually.of_forall (fun t ht => ⟨hH.trans ht.1, ht.2⟩)
  simpa only [neg_div] using hsubset.trans htotal

end HarmanProductTail

#print axioms HarmanProductTail.eventually_positive_energy
run_cmd do
  let axioms ← Lean.collectAxioms ``HarmanProductTail.eventually_positive_energy
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"
  Lean.logInfo "HARMAN PRODUCT TAIL PASSED"
