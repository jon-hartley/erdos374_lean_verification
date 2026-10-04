import FourPrimeGlobalPartition
import ShortSingletonGeometry
import ShortSingletonComplex

/-! Uniform strict dyadic rectangles for the complete expanded singleton
factor ranges. Exact sum identities permit arbitrary signed or complex data. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open Filter
open scoped BigOperators

namespace ShortSingletonDyadic
open FourPrimePartition

theorem left_admissible (X : ℝ) (S : Finset ℕ) (hX : 1 < X)
    (hlog : 1000 ≤ Real.log X)
    (hS : ∀ m ∈ S, X^(9/35:ℝ) ≤ (m:ℝ) ∧ (m:ℝ) < X^(1003/2000:ℝ)) :
    ∀ m ∈ S, 2 ≤ m ∧ (m:ℝ) ≤ X := by
  intro m hm
  have h2 : (2:ℝ) ≤ m :=
    ((ShortSingletonGeometry.two_le_small_power X hX hlog).trans
      (Real.rpow_le_rpow_of_exponent_le hX.le (by norm_num))).trans (hS m hm).1
  refine ⟨by exact_mod_cast h2, ?_⟩
  apply (hS m hm).2.le.trans
  simpa only [Real.rpow_one] using
    Real.rpow_le_rpow_of_exponent_le hX.le (by norm_num : (1003/2000:ℝ) ≤ 1)

theorem right_admissible (X : ℝ) (T : Finset ℕ) (hX : 1 < X)
    (hlog : 1000 ≤ Real.log X)
    (hT : ∀ q ∈ T, X^(1/25:ℝ) < (q:ℝ) ∧ (q:ℝ) ≤ X^(8/35:ℝ)) :
    ∀ q ∈ T, 2 ≤ q ∧ (q:ℝ) ≤ X := by
  intro q hq
  have h2 : (2:ℝ) ≤ q :=
    ((ShortSingletonGeometry.two_le_small_power X hX hlog).trans
      (Real.rpow_le_rpow_of_exponent_le hX.le (by norm_num))).trans (hT q hq).1.le
  refine ⟨by exact_mod_cast h2, ?_⟩
  apply (hT q hq).2.trans
  simpa only [Real.rpow_one] using
    Real.rpow_le_rpow_of_exponent_le hX.le (by norm_num : (8/35:ℝ) ≤ 1)

theorem covers (X : ℝ) (S T : Finset ℕ) (hX : 1 < X)
    (hlog : 1000 ≤ Real.log X)
    (hS : ∀ m ∈ S, X^(9/35:ℝ) ≤ (m:ℝ) ∧ (m:ℝ) < X^(1003/2000:ℝ))
    (hT : ∀ q ∈ T, X^(1/25:ℝ) < (q:ℝ) ∧ (q:ℝ) ≤ X^(8/35:ℝ)) :
    (∀ m ∈ S, 1 < m ∧ m ≤ scale 1 (FourPrimeGlobalPartition.k X+1)) ∧
      (∀ q ∈ T, 1 < q ∧ q ≤ scale 1 (FourPrimeGlobalPartition.k X+1)) := by
  have hs := left_admissible X S hX hlog hS
  have ht := right_admissible X T hX hlog hT
  exact ⟨FourPrimeGlobalPartition.support_cover X hX.le S
      (fun m hm => (hs m hm).1) (fun m hm => (hs m hm).2),
    FourPrimeGlobalPartition.support_cover X hX.le T
      (fun q hq => (ht q hq).1) (fun q hq => (ht q hq).2)⟩

theorem active_rectangle (X : ℝ) (S T : Finset ℕ) (hX : 1 < X)
    (hlog : 1000 ≤ Real.log X)
    (hS : ∀ m ∈ S, X^(9/35:ℝ) ≤ (m:ℝ) ∧ (m:ℝ) < X^(1003/2000:ℝ))
    (hT : ∀ q ∈ T, X^(1/25:ℝ) < (q:ℝ) ∧ (q:ℝ) ≤ X^(8/35:ℝ))
    (ij : ℕ × ℕ)
    (hij : ij ∈ family S T 1 1 (FourPrimeGlobalPartition.k X) (FourPrimeGlobalPartition.k X)) :
    1 ≤ scale 1 ij.1 ∧ 1 ≤ scale 1 ij.2 ∧
      X^(59/200:ℝ) ≤ ((scale 1 ij.1*scale 1 ij.2:ℕ):ℝ) ∧
      ((scale 1 ij.1*scale 1 ij.2:ℕ):ℝ) ≤ X^(731/1000:ℝ) ∧
      X^(39/1000:ℝ) ≤ (scale 1 ij.2:ℝ) ∧ (scale 1 ij.2:ℝ) ≤ X^(8/35:ℝ) ∧
      (∀ m ∈ block S 1 ij.1, scale 1 ij.1 < m ∧ m ≤ 2*scale 1 ij.1) ∧
      (∀ q ∈ block T 1 ij.2, scale 1 ij.2 < q ∧ q ≤ 2*scale 1 ij.2) := by
  obtain ⟨⟨m,hm⟩,⟨q,hq⟩⟩ := family_blocks_nonempty S T 1 1 _ _ ij hij
  have hm' := (mem_block S 1 ij.1 m).mp hm
  have hq' := (mem_block T 1 ij.2 q).mp hq
  have hg := ShortSingletonGeometry.dyadic_rectangle_bounds X
    (scale 1 ij.1) (scale 1 ij.2) m q hX hlog
    (hS m hm'.1).1 (hS m hm'.1).2 (hT q hq'.1).1 (hT q hq'.1).2
    (by exact_mod_cast hm'.2.1) (by exact_mod_cast hm'.2.2)
    (by exact_mod_cast hq'.2.1) (by exact_mod_cast hq'.2.2)
  exact ⟨scale_pos 1 ij.1 le_rfl, scale_pos 1 ij.2 le_rfl,
    by simpa only [Nat.cast_mul] using hg.1,
    by simpa only [Nat.cast_mul] using hg.2.1,
    hg.2.2.1, hg.2.2.2.1, block_bounds S 1 ij.1, block_bounds T 1 ij.2⟩

theorem eventually_data (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ X : ℝ in atTop, 1 < X ∧ 1000 ≤ Real.log X ∧
      ∀ S T : Finset ℕ,
        (∀ m ∈ S, X^(9/35:ℝ) ≤ (m:ℝ) ∧ (m:ℝ) < X^(1003/2000:ℝ)) →
        (∀ q ∈ T, X^(1/25:ℝ) < (q:ℝ) ∧ (q:ℝ) ≤ X^(8/35:ℝ)) →
        let k := FourPrimeGlobalPartition.k X
        let F := family S T 1 1 k k
        (∀ m ∈ S, 1 < m ∧ m ≤ scale 1 (k+1)) ∧
        (∀ q ∈ T, 1 < q ∧ q ≤ scale 1 (k+1)) ∧
        (F.card : ℝ) ≤ X^ε ∧
        ∀ ij ∈ F,
          1 ≤ scale 1 ij.1 ∧ 1 ≤ scale 1 ij.2 ∧
          X^(59/200:ℝ) ≤ ((scale 1 ij.1*scale 1 ij.2:ℕ):ℝ) ∧
          ((scale 1 ij.1*scale 1 ij.2:ℕ):ℝ) ≤ X^(731/1000:ℝ) ∧
          X^(39/1000:ℝ) ≤ (scale 1 ij.2:ℝ) ∧ (scale 1 ij.2:ℝ) ≤ X^(8/35:ℝ) ∧
          (∀ m ∈ block S 1 ij.1, scale 1 ij.1 < m ∧ m ≤ 2*scale 1 ij.1) ∧
          (∀ q ∈ block T 1 ij.2, scale 1 ij.2 < q ∧ q ≤ 2*scale 1 ij.2) := by
  filter_upwards [eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1000),
    FourPrimeGlobalPartition.eventually_all_family_cost (2*ε) (by positivity)]
      with X hX hlog hcard
  refine ⟨hX,hlog,?_⟩
  intro S T hS hT
  dsimp only
  have hc := covers X S T hX hlog hS hT
  refine ⟨hc.1,hc.2,?_,fun ij hij => active_rectangle X S T hX hlog hS hT ij hij⟩
  simpa only [show 2*ε/2 = ε by ring] using hcard.2 S T

theorem sum_eq_sum_family {β : Type*} [AddCommMonoid β]
    (X : ℝ) (S T : Finset ℕ) (f : ℕ → ℕ → β) (hX : 1 < X)
    (hlog : 1000 ≤ Real.log X)
    (hS : ∀ m ∈ S, X^(9/35:ℝ) ≤ (m:ℝ) ∧ (m:ℝ) < X^(1003/2000:ℝ))
    (hT : ∀ q ∈ T, X^(1/25:ℝ) < (q:ℝ) ∧ (q:ℝ) ≤ X^(8/35:ℝ)) :
    (∑ m ∈ S, ∑ q ∈ T, f m q) =
      ∑ ij ∈ family S T 1 1 (FourPrimeGlobalPartition.k X) (FourPrimeGlobalPartition.k X),
        ∑ m ∈ block S 1 ij.1, ∑ q ∈ block T 1 ij.2, f m q := by
  have hc := covers X S T hX hlog hS hT
  exact (sum_family_blocks S T 1 1 _ _ f hc.1 hc.2).symm

theorem productSum_eq_sum_family (X : ℝ) (S T : Finset ℕ)
    (a b : ℕ → ℂ) (L R : ℝ) (hX : 1 < X) (hlog : 1000 ≤ Real.log X)
    (hS : ∀ m ∈ S, X^(9/35:ℝ) ≤ (m:ℝ) ∧ (m:ℝ) < X^(1003/2000:ℝ))
    (hT : ∀ q ∈ T, X^(1/25:ℝ) < (q:ℝ) ∧ (q:ℝ) ≤ X^(8/35:ℝ)) :
    ShortSingletonComplex.productSum S T a b L R =
      ∑ ij ∈ family S T 1 1 (FourPrimeGlobalPartition.k X) (FourPrimeGlobalPartition.k X),
        ShortSingletonComplex.productSum (block S 1 ij.1) (block T 1 ij.2) a b L R := by
  exact sum_eq_sum_family X S T
    (fun m q => a m*b q*(UpperAfter545Remaining.floorKernel L R (m*q):ℂ)) hX hlog hS hT

run_cmd do
  for decl in [``left_admissible, ``right_admissible, ``covers, ``active_rectangle,
      ``eventually_data, ``sum_eq_sum_family, ``productSum_eq_sum_family] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "UNIFORM SINGLETON DYADIC RECTANGLES AND EXACT COMPLEX SUM PARTITION PASSED"

end ShortSingletonDyadic
