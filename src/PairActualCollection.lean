import PairActualGeometry

/-! Exact physical-index collection of the actual low-d inner pairs. The source
sign is negative; all small-divisor and ordered-tuple multiplicities remain. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace PairActualCollection
open PairActualGeometry

def representations (X s z : ℝ) : Finset (ℕ×List ℕ) :=
  (FrontierSmallBracketSplit.lowSupport X s) ×ˢ tuples X s z

def index (a : ℕ×List ℕ) : ℕ := a.1*a.2.prod

def support (X s z : ℝ) : Finset ℕ := (representations X s z).image index

def coefficient (X s z : ℝ) (m : ℕ) : ℝ :=
  ∑a∈(representations X s z).filter (fun a => index a=m),
    -FrontierSmallBracket.smallWeight X s false a.1

def remainder (X s z L R : ℝ) : ℝ :=
  HarmanDivisorWindow.remainder (support X s z) (coefficient X s z) L R

theorem coefficient_eq_neg_collected (X s z : ℝ) (m : ℕ) :
    coefficient X s z m = -PositiveSharpRemainderAnalysis.collected
      (FrontierSmallBracketSplit.lowSupport X s)
      (FrontierSmallBracket.smallWeight X s false) (tuples X s z) m := by
  simp only [coefficient,PositiveSharpRemainderAnalysis.collected,
    PositiveSharpRemainderAnalysis.representations,representations,index,Finset.sum_neg_distrib]
  rfl

theorem coefficient_zero_off_support (X s z : ℝ) (m : ℕ) (hm : m∉support X s z) :
    coefficient X s z m=0 := by
  apply Finset.sum_eq_zero
  intro a ha
  obtain ⟨ha,he⟩ := Finset.mem_filter.mp ha
  exact False.elim (hm (Finset.mem_image.mpr ⟨a,ha,he⟩))

theorem support_positive (X s z : ℝ) (m : ℕ) (hm : m∈support X s z) : 0<m := by
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hm
  obtain ⟨hd,ht⟩ := Finset.mem_product.mp ha
  exact Nat.mul_pos (SingletonActualGeometry.low_positive X s a.1 hd)
    (tuple_positive X s z a.2 ht)

theorem support_lt (X s z : ℝ) (hX : 1<X) (hs : 0<s) (hs1 : s≤1/1000)
    (hz : z≤X^(SieveWeightedScalarBudget.alpha s))
    (m : ℕ) (hm : m∈support X s z) : (m:ℝ)<X^(62/125:ℝ) := by
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hm
  obtain ⟨hd,ht⟩ := Finset.mem_product.mp ha
  exact product_lt X s z hX hs hs1 hz a.1 hd a.2 ht

theorem support_le_floor (X s z : ℝ) (hX : 1<X) (hs : 0<s) (hs1 : s≤1/1000)
    (hz : z≤X^(SieveWeightedScalarBudget.alpha s))
    (m : ℕ) (hm : m∈support X s z) : 1≤m ∧ m≤⌊X^(62/125:ℝ)⌋₊ :=
  ⟨support_positive X s z m hm,Nat.le_floor (support_lt X s z hX hs hs1 hz m hm).le⟩

theorem kernel (X s z : ℝ) (f : ℕ→ℝ) :
    (∑m∈support X s z,coefficient X s z m*f m)=
      ∑a∈representations X s z,-FrontierSmallBracket.smallWeight X s false a.1*f (index a) := by
  simp only [coefficient,Finset.sum_mul]
  calc
    _ = ∑m∈support X s z,∑a∈(representations X s z).filter (fun a => index a=m),
        -FrontierSmallBracket.smallWeight X s false a.1*f (index a) := by
      apply Finset.sum_congr rfl
      intro m _
      apply Finset.sum_congr rfl
      intro a ha
      rw [(Finset.mem_filter.mp ha).2]
    _ = _ := Finset.sum_fiberwise_of_maps_to
      (fun a ha => Finset.mem_image.mpr ⟨a,ha,rfl⟩) _

theorem kernel_eq_sector (X s z : ℝ) (hX : 1<X) (hs : 0<s) (hs1 : s≤1/1000)
    (hz : z≤SieveWeightedCutoffs.level X s) (f : ℕ→ℝ) :
    (∑m∈support X s z,coefficient X s z m*f m)=
      ∑a∈sector X s,(if a.1 then -1 else 1)*
        FrontierSmallBracketSplit.lowKernel X s z (!a.1) (a.2.1++[a.2.2]) f := by
  rw [kernel,representations,Finset.sum_product]
  simp only [index,neg_mul]
  rw [Finset.sum_comm,tuples_sum X s z hX hs hs1 hz]
  apply Finset.sum_congr rfl
  intro a ha
  have hb := (Finset.mem_filter.mp ha).2.1
  simp only [hb,Bool.not_true,ite_true,neg_one_mul,FrontierSmallBracketSplit.lowKernel,
    ←Finset.sum_neg_distrib]
  rw [Finset.sum_comm]

theorem remainder_eq_sector (X s z L R : ℝ) (hX : 1<X) (hs : 0<s) (hs1 : s≤1/1000)
    (hz : z≤SieveWeightedCutoffs.level X s) :
    remainder X s z L R = ∑a∈sector X s,(if a.1 then -1 else 1)*
      FrontierSmallBracketSplit.lowRemainder X s z (!a.1) (a.2.1++[a.2.2]) L R := by
  rw [remainder,HarmanDivisorWindow.remainder_eq_sum]
  exact kernel_eq_sector X s z hX hs hs1 hz (FrontierSmallBracketSplit.windowKernel L R)

theorem kernel_eq_Icc (X s z : ℝ) (hX : 1<X) (hs : 0<s) (hs1 : s≤1/1000)
    (hz : z≤X^(SieveWeightedScalarBudget.alpha s)) (f : ℕ→ℝ) :
    (∑m∈support X s z,coefficient X s z m*f m)=
      ∑m∈Finset.Icc 1 ⌊X^(62/125:ℝ)⌋₊,coefficient X s z m*f m := by
  apply Finset.sum_subset
  · intro m hm
    exact Finset.mem_Icc.mpr (support_le_floor X s z hX hs hs1 hz m hm)
  · intro m _ hm
    rw [coefficient_zero_off_support X s z m hm,zero_mul]

theorem remainder_eq_Icc (X s z L R : ℝ) (hX : 1<X) (hs : 0<s) (hs1 : s≤1/1000)
    (hz : z≤X^(SieveWeightedScalarBudget.alpha s)) :
    remainder X s z L R = ∑m∈Finset.Icc 1 ⌊X^(62/125:ℝ)⌋₊,
      coefficient X s z m*FrontierSmallBracketSplit.windowKernel L R m := by
  rw [remainder,HarmanDivisorWindow.remainder_eq_sum]
  exact kernel_eq_Icc X s z hX hs hs1 hz _

theorem collected_eq_signed (S : Finset ℕ) (w : ℕ→ℝ) (T : Finset (List ℕ)) (m : ℕ) :
    PositiveSharpRemainderAnalysis.collected S w T m =
      SieveTupleConvolution.signedCoefficient S w (fun _ => 0) T ∅ m := by
  rw [SieveTupleConvolution.signedCoefficient,
    ←PositiveSharpRemainderAnalysis.collected_eq_convolution S _ w T
      (SieveTupleConvolution.support_subset_tupleCarrier_left T ∅),
    ←PositiveSharpRemainderAnalysis.collected_eq_convolution S _ (fun _ => 0) ∅
      (SieveTupleConvolution.support_subset_tupleCarrier_right T ∅)]
  simp [PositiveSharpRemainderAnalysis.collected]

theorem eventually_coefficient_cap (s ε : ℝ) (hs : 0<s) (hs1 : s≤1/1000) (hε : 0<ε) :
    ∀ᶠ X : ℝ in atTop, 1<X ∧ ∀z:ℝ, z≤X^(SieveWeightedScalarBudget.alpha s) →
      ∀m:ℕ, |coefficient X s z m|≤X^ε := by
  filter_upwards [PositiveSharpRemainderAnalysis.eventually_signedCoefficient_cap 2 ε hε,
    eventually_gt_atTop (1:ℝ)] with X hcap hX
  refine ⟨hX,?_⟩
  intro z hz m
  by_cases hm : m∈support X s z
  · rw [coefficient_eq_neg_collected,abs_neg,collected_eq_signed]
    apply hcap.2 _ _ _ _ _ m (support_positive X s z m hm).ne'
    · apply (support_lt X s z hX hs hs1 hz m hm).le.trans
      rw [←Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hX.le (by norm_num)
    · intro t ht
      exact (tuple_length X s z t ht).le
    · simp
    · intro d _
      exact SieveSmallWeights.weight_abs_le_one _ _ _ _
    · simp
  · rw [coefficient_zero_off_support X s z m hm,abs_zero]
    exact (Real.rpow_pos_of_pos (by linarith) _).le

run_cmd do
  for decl in [``coefficient_eq_neg_collected,``coefficient_zero_off_support,``support_positive,
      ``support_lt,``support_le_floor,``kernel,``kernel_eq_sector,``remainder_eq_sector,
      ``kernel_eq_Icc,``remainder_eq_Icc,``collected_eq_signed,``eventually_coefficient_cap] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ACTUAL NEGATIVE INNER-PAIR COLLECTION AND UNIFORM SUBPOWER CAP PASSED"

end PairActualCollection
