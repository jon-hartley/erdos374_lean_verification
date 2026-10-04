import FourPrimeScaleBudget
import FourPrimePartitionProduct
import FourPrimeGlobalPartition

/-! Pointwise construction of every geometric and coefficient input to
the family theorem with right support at most X^(8/35). The active dyadic
lower endpoint is strictly below an actual support member, so this upper
cutoff needs no factor-two loss. No analytic remainder estimate is an input. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
namespace FrontierGlobalData
open FourPrimeScaleBudget FourPrimePartition

theorem global_data (X s c : ℝ) (hX : 1 ≤ X) (hs : 0 < s) (hc : 0 < c)
    (hdiv : ∀ m : ℕ, (m : ℝ) ≤ X → (m.divisors.card : ℝ) ^ 4 ≤ X ^ (c / 2))
    (hbin : X ^ (lowerExponent s / 2) ≤ X ^ lowerExponent s / 2)
    (hcost : ((FourPrimeGlobalPartition.k X + 1 : ℕ) : ℝ) ^ 2 ≤ X ^ (c / 2))
    (S T : Finset ℕ) (a b : ℕ → ℝ) (hTne : T.Nonempty)
    (hS : ∀ m ∈ S, 2 ≤ m) (hT : ∀ n ∈ T, 2 ≤ n)
    (hTlow : ∀ n ∈ T, X ^ lowerExponent s ≤ (n : ℝ))
    (hTupper : ∀ n ∈ T, (n : ℝ) ≤ X ^ (8 / 35 : ℝ))
    (hprod : ∀ m ∈ S, ∀ n ∈ T, (m : ℝ) * n ≤ X ^ (1 - 2 * s))
    (ha : ∀ m ∈ S, |a m| ≤ (m.divisors.card : ℝ) ^ 4)
    (hbweight : ∀ n ∈ T, |b n| ≤ 1) :
    let k := FourPrimeGlobalPartition.k X
    let F := family S T 1 1 k k
    let M := fun ij : ℕ × ℕ => scale 1 ij.1
    let N := fun ij : ℕ × ℕ => scale 1 ij.2
    let sm := fun ij : ℕ × ℕ => block S 1 ij.1
    let sn := fun ij : ℕ × ℕ => block T 1 ij.2
    (∀ n ∈ S, 1 < n ∧ n ≤ scale 1 (k+1)) ∧
    (∀ n ∈ T, 1 < n ∧ n ≤ scale 1 (k+1)) ∧
    (F.card : ℝ) ≤ X ^ (c / 2) ∧
    ∀ ij ∈ F,
      1 ≤ M ij ∧ 1 ≤ N ij ∧
      X ^ (lowerExponent s / 2) ≤ ((M ij * N ij : ℕ) : ℝ) ∧
      ((M ij * N ij : ℕ) : ℝ) ≤ X ^ (1 - s / 2 - s / 2) ∧
      X ^ (lowerExponent s / 2) ≤ (N ij : ℝ) ∧
      ((N ij : ℝ) ≤ X ^ (8 / 35 : ℝ) ∨
        X ^ (27 / 35 : ℝ) ≤ ((M ij * N ij : ℕ) : ℝ)) ∧
      (∀ m ∈ sm ij, M ij < m ∧ m ≤ 2 * M ij) ∧
      (∀ n ∈ sn ij, N ij < n ∧ n ≤ 2 * N ij) ∧
      (∀ m ∈ sm ij, |a m| ≤ X ^ (c / 2)) ∧
      (∀ n ∈ sn ij, |b n| ≤ X ^ (c / 2)) := by
  dsimp only
  have hSup : ∀ m ∈ S, (m : ℝ) ≤ X := by
    intro m hm
    obtain ⟨n, hn⟩ := hTne
    have hn1 : (1 : ℝ) ≤ n := by
      exact_mod_cast (show 1 ≤ n by have := hT n hn; omega)
    have hh := (hprod m hm n hn).trans
      (show X ^ (1 - 2 * s) ≤ X by
        simpa using Real.rpow_le_rpow_of_exponent_le hX
          (by linarith : 1 - 2 * s ≤ (1 : ℝ)))
    nlinarith [show (0 : ℝ) ≤ m from Nat.cast_nonneg m]
  have hTup : ∀ n ∈ T, (n : ℝ) ≤ X := by
    intro n hn
    exact (hTupper n hn).trans (by
      simpa using Real.rpow_le_rpow_of_exponent_le hX
        (by norm_num : (8 / 35 : ℝ) ≤ 1))
  let k := FourPrimeGlobalPartition.k X
  let u : ℕ := 1
  let v : ℕ := 1
  have hu : 1 ≤ u := le_rfl
  have hv : 1 ≤ v := le_rfl
  have hcoverS := FourPrimeGlobalPartition.support_cover X hX S hS hSup
  have hcoverT := FourPrimeGlobalPartition.support_cover X hX T hT hTup
  let F := family S T u v k k
  let M := fun ij : ℕ × ℕ => scale u ij.1
  let N := fun ij : ℕ × ℕ => scale v ij.2
  let sm := fun ij : ℕ × ℕ => block S u ij.1
  let sn := fun ij : ℕ × ℕ => block T v ij.2
  have hcard : (F.card : ℝ) ≤ X ^ (c / 2) := by
    have hbound : F.card ≤ (k + 1) * (k + 1) := family_card_le S T u v k k
    have hh : (F.card : ℝ) ≤ ((k + 1 : ℕ) : ℝ) ^ 2 := by
      exact_mod_cast (by simpa only [pow_two] using hbound : F.card ≤ (k + 1) ^ 2)
    exact hh.trans hcost
  have hdata : ∀ ij ∈ F,
      1 ≤ M ij ∧ 1 ≤ N ij ∧
      X ^ (lowerExponent s / 2) ≤ ((M ij * N ij : ℕ) : ℝ) ∧
      ((M ij * N ij : ℕ) : ℝ) ≤ X ^ (1 - s / 2 - s / 2) ∧
      X ^ (lowerExponent s / 2) ≤ (N ij : ℝ) ∧
      ((N ij : ℝ) ≤ X ^ (8 / 35 : ℝ) ∨
        X ^ (27 / 35 : ℝ) ≤ ((M ij * N ij : ℕ) : ℝ)) ∧
      (∀ m ∈ sm ij, M ij < m ∧ m ≤ 2 * M ij) ∧
      (∀ n ∈ sn ij, N ij < n ∧ n ≤ 2 * N ij) ∧
      (∀ m ∈ sm ij, |a m| ≤ X ^ (c / 2)) ∧
      (∀ n ∈ sn ij, |b n| ≤ X ^ (c / 2)) := by
    intro ij hij
    have hij' : ij ∈ family S T u v k k := hij
    have hmem := Finset.mem_product.mp hij'
    have hM : 1 ≤ M ij := Nat.one_le_iff_ne_zero.mpr
      (Nat.ne_of_gt (scale_pos u ij.1 hu))
    have hN : 1 ≤ N ij := Nat.one_le_iff_ne_zero.mpr
      (Nat.ne_of_gt (scale_pos v ij.2 hv))
    have hMr : (1 : ℝ) ≤ M ij := by exact_mod_cast hM
    have hNr : (1 : ℝ) ≤ N ij := by exact_mod_cast hN
    have hNlow : X ^ (lowerExponent s / 2) ≤ (N ij : ℝ) :=
      hbin.trans (active_scale_lower T v k ij.2 _ hTlow hmem.2)
    have hAlow : X ^ (lowerExponent s / 2) ≤ ((M ij * N ij : ℕ) : ℝ) := by
      rw [Nat.cast_mul]
      nlinarith
    have hAupper : ((M ij * N ij : ℕ) : ℝ) ≤ X ^ (1 - s / 2 - s / 2) := by
      have hh := family_scale_product_lt S T u v k k _ hu hv hprod ij hij'
      have hpow := Real.rpow_le_rpow_of_exponent_le hX
        (by linarith : 1 - 2 * s ≤ 1 - s / 2 - s / 2)
      have hcast : ((M ij * N ij : ℕ) : ℝ) ≤ X ^ (1 - 2 * s) := by
        simpa only [Nat.cast_mul] using hh.le
      exact hcast.trans hpow
    have hNupper : (N ij : ℝ) ≤ X ^ (8 / 35 : ℝ) :=
      (active_scale_lt_upper T v k ij.2 _ hTupper hmem.2).le
    refine ⟨hM, hN, hAlow, hAupper, hNlow, Or.inl hNupper,
      block_bounds S u ij.1, block_bounds T v ij.2, ?_, ?_⟩
    · intro m hm
      have hmS := ((mem_block S u ij.1 m).mp hm).1
      exact (ha m hmS).trans (hdiv m (hSup m hmS))
    · intro n hn
      exact (hbweight n ((mem_block T v ij.2 n).mp hn).1).trans
        (Real.one_le_rpow hX (by positivity))
  exact ⟨hcoverS, hcoverT, hcard, hdata⟩

end FrontierGlobalData
run_cmd do
  for ax in (← Lean.collectAxioms ``FrontierGlobalData.global_data) do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"
  Lean.logInfo "FRONTIER EIGHT-THIRTY-FIFTHS GLOBAL DATA PASSED"
