import LongerTupleMaskedCollection

/-! Exact upper-product truncation by clamping both interval endpoints.
Clamping only the upper endpoint would create spurious negative masks. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace ProductCappedMasksWork
open ShortSingletonMasks LongerTupleMaskedCollection
open UpperAfter545Remaining

def upperEndpoint (U : ℝ) (m : ℕ) : ℕ := Nat.floor (U/(m:ℝ))

theorem product_le_iff (U : ℝ) (m q : ℕ) (hU : 0≤U) (hm : 0<m) :
    ((m*q:ℕ):ℝ)≤U ↔ q≤upperEndpoint U m := by
  have hmR : (0:ℝ)<m := by exact_mod_cast hm
  rw [upperEndpoint,Nat.le_floor_iff (div_nonneg hU hmR.le),le_div_iff₀ hmR]
  simp only [Nat.cast_mul,mul_comm]

theorem prefix_min (J K q : ℕ) :
    prefixIndicator (min J K) q = prefixIndicator J q*prefixIndicator K q := by
  by_cases hJ : q≤J <;> by_cases hK : q≤K <;> simp [prefixIndicator,hJ,hK]

theorem clamped_interval (lo hi cap cut q : ℕ) :
    (prefixIndicator (min hi cap) q-prefixIndicator (min lo cap) q)*
      (1-prefixIndicator cut q) =
      ((prefixIndicator hi q-prefixIndicator lo q)*(1-prefixIndicator cut q))*
        prefixIndicator cap q := by
  rw [prefix_min,prefix_min]
  ring

theorem cap_mask (U : ℝ) (m lo hi cut q : ℕ) (hU : 0≤U) (hm : 0<m) :
    (prefixIndicator (min hi (upperEndpoint U m)) q-
      prefixIndicator (min lo (upperEndpoint U m)) q)*(1-prefixIndicator cut q) =
      if ((m*q:ℕ):ℝ)≤U then
        (prefixIndicator hi q-prefixIndicator lo q)*(1-prefixIndicator cut q) else 0 := by
  rw [clamped_interval]
  by_cases hc : ((m*q:ℕ):ℝ)≤U
  · simp only [prefixIndicator,(product_le_iff U m q hU hm).mp hc,hc,ite_true,mul_one]
  · have hn : ¬q≤upperEndpoint U m := by
      simpa only [←product_le_iff U m q hU hm] using hc
    simp only [prefixIndicator,hn,hc,ite_false,mul_zero]

theorem maskedSum_cap {α : Type*} (S : Finset α) (index : α → ℕ) (B : Finset ℕ)
    (w : α → ℂ) (lo hi : α → ℕ) (cut : ℕ → ℕ) (U L R : ℝ)
    (hU : 0≤U) (hpos : ∀ a∈S, 0 < index a) :
    maskedSum S index B w
      (fun a => min (lo a) (upperEndpoint U (index a)))
      (fun a => min (hi a) (upperEndpoint U (index a))) cut L R =
      ∑ a∈S,∑ q∈B,w a*
        ((prefixIndicator (hi a) q-prefixIndicator (lo a) q)*
          (1-prefixIndicator (cut (index a)) q))*
        (if ((index a*q:ℕ):ℝ)≤U then (floorKernel L R (index a*q):ℂ) else 0) := by
  unfold maskedSum
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro q _
  rw [cap_mask U (index a) _ _ _ q hU (hpos a ha)]
  by_cases hc : ((index a*q:ℕ):ℝ)≤U <;>
    simp only [hc,ite_true,ite_false,mul_zero,zero_mul]

#print axioms maskedSum_cap
run_cmd do
  for decl in [``product_le_iff, ``prefix_min, ``clamped_interval, ``cap_mask,
      ``maskedSum_cap] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"

end ProductCappedMasksWork
