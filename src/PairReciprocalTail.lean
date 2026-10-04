import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic

/-! Quantitative signed Fourier tail. The proof is a finite reciprocal-square
telescoping comparison, followed by the positive and negative integer halves. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped BigOperators

namespace PairReciprocalTail

def natTail (K n : ℕ) : ℝ := if K<n then ((n:ℝ)^2)⁻¹ else 0

def reciprocalTail (K : ℕ) (k : ℤ) : ℝ := if (K:ℤ) < |k| then 1/(k:ℝ)^2 else 0

def fourierTail (K : ℕ) (k : ℤ) : ℝ :=
  if (K:ℤ) < |k| then (1/(Real.pi*|(k:ℝ)|))^2 else 0

theorem natTail_nonneg (K n : ℕ) : 0≤natTail K n := by
  unfold natTail
  split_ifs <;> positivity

theorem natTail_sum_le (K : ℕ) (hK : 1≤K) (s : Finset ℕ) :
    ∑n∈s,natTail K n≤1/(K:ℝ) := by
  simp only [natTail,←Finset.sum_filter]
  have hsub : s.filter (fun n => K<n) ⊆ Finset.Ioc K (max K (s.sup id)) := by
    intro n hn
    obtain ⟨hn,hKn⟩ := Finset.mem_filter.mp hn
    exact Finset.mem_Ioc.mpr ⟨hKn,(Finset.le_sup (f:=id) hn).trans (le_max_right _ _)⟩
  calc
    _ ≤ ∑n∈Finset.Ioc K (max K (s.sup id)),((n:ℝ)^2)⁻¹ :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (by intro n _ _; positivity)
    _ ≤ (K:ℝ)⁻¹-((max K (s.sup id):ℕ):ℝ)⁻¹ :=
      sum_Ioc_inv_sq_le_sub (by omega) (le_max_left _ _)
    _ ≤ _ := by rw [one_div]; exact sub_le_self _ (by positivity)

theorem summable_natTail (K : ℕ) (hK : 1≤K) : Summable (natTail K) :=
  summable_of_sum_le (natTail_nonneg K) (natTail_sum_le K hK)

theorem tsum_natTail_le (K : ℕ) (hK : 1≤K) : ∑'n,natTail K n≤1/(K:ℝ) :=
  Real.tsum_le_of_sum_le (natTail_nonneg K) (natTail_sum_le K hK)

theorem reciprocalTail_nat (K n : ℕ) : reciprocalTail K n=natTail K n := by
  simp [reciprocalTail,natTail]

theorem reciprocalTail_neg_nat (K n : ℕ) : reciprocalTail K (-(n:ℤ))=natTail K n := by
  simp [reciprocalTail,natTail]

theorem reciprocalTail_nonneg (K : ℕ) (k : ℤ) : 0≤reciprocalTail K k := by
  unfold reciprocalTail
  split_ifs <;> positivity

theorem summable_reciprocalTail (K : ℕ) (hK : 1≤K) : Summable (reciprocalTail K) := by
  apply Summable.of_nat_of_neg
  · simpa only [reciprocalTail_nat] using summable_natTail K hK
  · simpa only [reciprocalTail_neg_nat] using summable_natTail K hK

theorem tsum_reciprocalTail_eq (K : ℕ) (hK : 1≤K) :
    (∑'k:ℤ,reciprocalTail K k)=2*(∑'n:ℕ,natTail K n) := by
  have hn : Summable (fun n:ℕ => reciprocalTail K n) := by
    simpa only [reciprocalTail_nat] using summable_natTail K hK
  have hm : Summable (fun n:ℕ => reciprocalTail K (-(n:ℤ))) := by
    simpa only [reciprocalTail_neg_nat] using summable_natTail K hK
  rw [hn.tsum_of_nat_of_neg hm]
  simp only [reciprocalTail_nat,reciprocalTail_neg_nat]
  simp [reciprocalTail,natTail,two_mul]

theorem tsum_reciprocalTail_le (K : ℕ) (hK : 1≤K) :
    (∑'k:ℤ,reciprocalTail K k)≤2/(K:ℝ) := by
  rw [tsum_reciprocalTail_eq K hK]
  simpa only [mul_one_div] using mul_le_mul_of_nonneg_left (tsum_natTail_le K hK) (by norm_num : (0:ℝ)≤2)

theorem fourierTail_nonneg (K : ℕ) (k : ℤ) : 0≤fourierTail K k := by
  unfold fourierTail
  split_ifs <;> positivity

theorem fourierTail_le_reciprocalTail (K : ℕ) (k : ℤ) :
    fourierTail K k≤reciprocalTail K k := by
  by_cases hk : k=0
  · subst k
    simp [fourierTail,reciprocalTail]
  have hkR : (k:ℝ)≠0 := by exact_mod_cast hk
  have hp : 1≤Real.pi := by linarith [Real.two_le_pi]
  unfold fourierTail reciprocalTail
  split_ifs
  · rw [div_pow,one_pow,mul_pow,sq_abs]
    apply one_div_le_one_div_of_le (sq_pos_of_ne_zero hkR)
    exact le_mul_of_one_le_left (sq_nonneg (k:ℝ)) (one_le_pow₀ hp)
  · rfl

theorem summable_tail (K : ℕ) (hK : 1≤K) : Summable (fourierTail K) :=
  (summable_reciprocalTail K hK).of_nonneg_of_le (fourierTail_nonneg K)
    (fourierTail_le_reciprocalTail K)

theorem tsum_tail_le (K : ℕ) (hK : 1≤K) :
    (∑'k:ℤ,fourierTail K k)≤2/(K:ℝ) := by
  exact (Summable.tsum_le_tsum (fourierTail_le_reciprocalTail K)
    (summable_tail K hK) (summable_reciprocalTail K hK)).trans (tsum_reciprocalTail_le K hK)

theorem tsum_tail_le_four (K : ℕ) (hK : 1≤K) :
    (∑'k:ℤ,fourierTail K k)≤4/(K:ℝ) := by
  exact (tsum_tail_le K hK).trans (div_le_div_of_nonneg_right (by norm_num) (Nat.cast_nonneg K))

run_cmd do
  for decl in [``natTail_nonneg,``natTail_sum_le,``summable_natTail,``tsum_natTail_le,
      ``reciprocalTail_nat,``reciprocalTail_neg_nat,``reciprocalTail_nonneg,
      ``summable_reciprocalTail,``tsum_reciprocalTail_eq,``tsum_reciprocalTail_le,
      ``fourierTail_nonneg,``fourierTail_le_reciprocalTail,``summable_tail,``tsum_tail_le,
      ``tsum_tail_le_four] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "QUANTITATIVE SIGNED RECIPROCAL-SQUARE FOURIER TAIL PASSED"

end PairReciprocalTail
