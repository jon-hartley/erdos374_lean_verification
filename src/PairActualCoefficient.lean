import PairActualCollection
import PairActualUnique

/-! The collected actual inner-pair coefficient has absolute value at most one.
The unit small divisor contributes exactly minus one at its pair product. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace PairActualCoefficient
open PairActualCollection

theorem index_injective (X s z : ℝ) (hX : 1<X) (hs : 0<s) (hs1 : s≤1/1000) :
    Set.InjOn index (representations X s z) := by
  intro a ha b hb hab
  obtain ⟨had,hat⟩ := Finset.mem_product.mp ha
  obtain ⟨hbd,hbt⟩ := Finset.mem_product.mp hb
  obtain ⟨hd,ht⟩ := PairActualUnique.representation_unique X s z hX hs hs1
    a.1 b.1 had hbd a.2 b.2 hat hbt hab
  exact Prod.ext hd ht

theorem coefficient_at_index (X s z : ℝ) (hX : 1<X) (hs : 0<s) (hs1 : s≤1/1000)
    (a : ℕ×List ℕ) (ha : a∈representations X s z) :
    coefficient X s z (index a) = -FrontierSmallBracket.smallWeight X s false a.1 := by
  unfold coefficient
  apply Finset.sum_eq_single a
  · intro b hb hba
    obtain ⟨hb,he⟩ := Finset.mem_filter.mp hb
    exact False.elim (hba (index_injective X s z hX hs hs1 hb ha he))
  · intro hnot
    exact False.elim (hnot (Finset.mem_filter.mpr ⟨ha,rfl⟩))

theorem coefficient_abs_le_one (X s z : ℝ) (hX : 1<X) (hs : 0<s)
    (hs1 : s≤1/1000) (m : ℕ) : |coefficient X s z m|≤1 := by
  by_cases hm : m∈support X s z
  · obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hm
    rw [coefficient_at_index X s z hX hs hs1 a ha,abs_neg]
    exact SieveSmallWeights.weight_abs_le_one _ _ _ _
  · rw [coefficient_zero_off_support X s z m hm]
    norm_num

theorem pair_product_coefficient (X s z : ℝ) (hX : 1<X) (hs : 0<s)
    (hs1 : s≤1/1000) (t : List ℕ) (ht : t∈PairActualGeometry.tuples X s z) :
    coefficient X s z t.prod = -1 := by
  have ha : (1,t)∈representations X s z := Finset.mem_product.mpr
    ⟨SingletonActualResidual.one_mem_lowSupport X s hX hs hs1,ht⟩
  simpa only [index,one_mul,FrontierSmallBracket.smallWeight,SieveSmallWeights.weight_one]
    using coefficient_at_index X s z hX hs hs1 (1,t) ha

run_cmd do
  for decl in [``index_injective,``coefficient_at_index,``coefficient_abs_le_one,
      ``pair_product_coefficient] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ACTUAL PAIR COEFFICIENT CAP ONE AND UNIT COEFFICIENT MINUS ONE PASSED"

end PairActualCoefficient
