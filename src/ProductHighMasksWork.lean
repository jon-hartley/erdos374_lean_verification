import ProductCappedMasksWork

/-! Exact lower-product truncation by raising the physical high endpoint. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace ProductHighMasksWork
open ShortSingletonMasks LongerTupleMaskedCollection ProductCappedMasksWork
open UpperAfter545Remaining

theorem high_prefix_max (cut cap q : ℕ) :
    1-prefixIndicator (max cut cap) q =
      (1-prefixIndicator cut q)*(1-prefixIndicator cap q) := by
  by_cases hcut : q≤cut <;> by_cases hcap : q≤cap <;>
    simp [prefixIndicator,le_max_iff,hcut,hcap]

theorem high_mask (U : ℝ) (m lo hi cut q : ℕ) (hU : 0≤U) (hm : 0<m) :
    (prefixIndicator hi q-prefixIndicator lo q)*
      (1-prefixIndicator (max cut (upperEndpoint U m)) q) =
      if U<((m*q:ℕ):ℝ) then
        (prefixIndicator hi q-prefixIndicator lo q)*(1-prefixIndicator cut q) else 0 := by
  rw [high_prefix_max]
  by_cases hc : U<((m*q:ℕ):ℝ)
  · have hn : ¬q≤upperEndpoint U m := by
      simpa only [←product_le_iff U m q hU hm] using not_le.mpr hc
    simp only [prefixIndicator,hn,hc,ite_false,ite_true,sub_zero,mul_one]
  · have hn := (product_le_iff U m q hU hm).mp (le_of_not_gt hc)
    simp only [prefixIndicator,hn,hc,ite_true,ite_false,sub_self,mul_zero]

#print axioms high_mask
run_cmd do
  for decl in [``high_prefix_max, ``high_mask] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"

end ProductHighMasksWork
