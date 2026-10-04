import SingletonActualGeometry

/-! Exact collection of the remaining outer singleton sector. Coefficients are
the original upper small weights and the unit divisor is retained. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace SingletonActualCollection
open SieveBoxGrouping SingletonActualGeometry

def sector (X s : ℝ) : Finset TailSieveCovered.Index :=
  (FrontierSieveDecomposition.exceptionalFamily X s).filter
    (fun a => a.1=false ∧ a.2.1=[])

def bands (X s : ℝ) : Finset ℕ := (sector X s).image (fun a => a.2.2)

def representations (X s z : ℝ) : Finset (ℕ × ℕ × ℕ) :=
  (bands X s).biUnion (fun j =>
    ((FrontierSmallBracketSplit.lowSupport X s) ×ˢ
      primeBand (SieveWeightedCutoffs.level X s) s z j).image (fun dp => (j,dp)))

def index (a : ℕ × ℕ × ℕ) : ℕ := a.2.1*a.2.2

def support (X s z : ℝ) : Finset ℕ := (representations X s z).image index

def coefficient (X s z : ℝ) (m : ℕ) : ℝ :=
  ∑a∈(representations X s z).filter (fun a => index a=m),
    FrontierSmallBracket.smallWeight X s true a.2.1

def remainder (X s z L R : ℝ) : ℝ :=
  HarmanDivisorWindow.remainder (support X s z) (coefficient X s z) L R

theorem mem_bands (X s : ℝ) (j : ℕ) :
    j∈bands X s ↔ (false,([],j))∈FrontierSieveDecomposition.exceptionalFamily X s := by
  constructor
  · intro hj
    obtain ⟨⟨b,g,k⟩,ha,hk⟩ := Finset.mem_image.mp hj
    obtain ⟨ha,hb,hg⟩ := Finset.mem_filter.mp ha
    dsimp at hb hg hk
    subst b; subst g; subst k
    exact ha
  · intro hj
    exact Finset.mem_image.mpr ⟨(false,([],j)),Finset.mem_filter.mpr ⟨hj,rfl,rfl⟩,rfl⟩

theorem mem_representations (X s z : ℝ) (a : ℕ × ℕ × ℕ) :
    a∈representations X s z ↔ a.1∈bands X s ∧
      a.2.1∈FrontierSmallBracketSplit.lowSupport X s ∧
      a.2.2∈primeBand (SieveWeightedCutoffs.level X s) s z a.1 := by
  rcases a with ⟨j,d,p⟩
  simp [representations]

theorem index_injective (X s z : ℝ) (hX : 1<X) (hs : 0<s)
    (hs1 : s≤1/1000) (hz : z≤SieveWeightedCutoffs.level X s) :
    Set.InjOn index (representations X s z) := by
  intro a ha b hb hab
  obtain ⟨_,had,hap⟩ := (mem_representations X s z a).mp ha
  obtain ⟨_,hbd,hbp⟩ := (mem_representations X s z b).mp hb
  obtain ⟨hj,hd,hp⟩ := singleton_index_unique X s z hX hs hs1 hz
    a.1 b.1 a.2.1 b.2.1 a.2.2 b.2.2 had hbd hap hbp hab
  exact Prod.ext hj (Prod.ext hd hp)

theorem coefficient_at_index (X s z : ℝ) (hX : 1<X) (hs : 0<s)
    (hs1 : s≤1/1000) (hz : z≤SieveWeightedCutoffs.level X s)
    (a : ℕ × ℕ × ℕ) (ha : a∈representations X s z) :
    coefficient X s z (index a)=FrontierSmallBracket.smallWeight X s true a.2.1 := by
  unfold coefficient
  apply Finset.sum_eq_single a
  · intro b hb hba
    obtain ⟨hb,he⟩ := Finset.mem_filter.mp hb
    exact False.elim (hba (index_injective X s z hX hs hs1 hz hb ha he))
  · intro hnot
    exact False.elim (hnot (Finset.mem_filter.mpr ⟨ha,rfl⟩))

theorem coefficient_zero_off_support (X s z : ℝ) (m : ℕ)
    (hm : m∉support X s z) : coefficient X s z m=0 := by
  apply Finset.sum_eq_zero
  intro a ha
  obtain ⟨ha,he⟩ := Finset.mem_filter.mp ha
  exact False.elim (hm (Finset.mem_image.mpr ⟨a,ha,he⟩))

theorem coefficient_abs_le_one (X s z : ℝ) (hX : 1<X) (hs : 0<s)
    (hs1 : s≤1/1000) (hz : z≤SieveWeightedCutoffs.level X s) (m : ℕ) :
    |coefficient X s z m|≤1 := by
  by_cases hm : m∈support X s z
  · obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hm
    rw [coefficient_at_index X s z hX hs hs1 hz a ha]
    exact SieveSmallWeights.weight_abs_le_one _ _ _ _
  · rw [coefficient_zero_off_support X s z m hm]
    norm_num

theorem support_positive (X s z : ℝ) (m : ℕ) (hm : m∈support X s z) : 0<m := by
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hm
  obtain ⟨_,hd,hp⟩ := (mem_representations X s z a).mp ha
  exact Nat.mul_pos (low_positive X s a.2.1 hd) ((mem_primeBand _ _ _ _ _).mp hp).1.pos

theorem support_lt (X s z : ℝ) (hX : 1<X) (hs : 0<s) (hs1 : s≤1/1000)
    (hz : z≤X^(SieveWeightedScalarBudget.alpha s))
    (m : ℕ) (hm : m∈support X s z) : (m:ℝ)<X^(31/125:ℝ) := by
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hm
  obtain ⟨_,hd,hp⟩ := (mem_representations X s z a).mp ha
  exact product_lt X s z hX hs hs1 hz a.1 a.2.1 a.2.2 hd hp

theorem cutoff_le_level (X s : ℝ) (hX : 1≤X) (_hs : 0≤s) (hs1 : s≤1/1000) :
    X^(SieveWeightedScalarBudget.alpha s)≤SieveWeightedCutoffs.level X s := by
  apply Real.rpow_le_rpow_of_exponent_le hX
  unfold SieveWeightedScalarBudget.alpha
  linarith

theorem support_le_floor (X s z : ℝ) (hX : 1<X) (hs : 0<s) (hs1 : s≤1/1000)
    (hz : z≤X^(SieveWeightedScalarBudget.alpha s))
    (m : ℕ) (hm : m∈support X s z) : 1≤m ∧ m≤⌊X^(31/125:ℝ)⌋₊ :=
  ⟨support_positive X s z m hm,Nat.le_floor (support_lt X s z hX hs hs1 hz m hm).le⟩

theorem coefficient_abs_le_one_at_first_cutoff (X s z : ℝ) (hX : 1<X) (hs : 0<s)
    (hs1 : s≤1/1000) (hz : z≤X^(SieveWeightedScalarBudget.alpha s)) (m : ℕ) :
    |coefficient X s z m|≤1 :=
  coefficient_abs_le_one X s z hX hs hs1
    (hz.trans (cutoff_le_level X s hX.le hs.le hs1)) m

theorem kernel (X s z : ℝ) (f : ℕ→ℝ) :
    (∑m∈support X s z,coefficient X s z m*f m)=
      ∑a∈representations X s z,
        FrontierSmallBracket.smallWeight X s true a.2.1*f (index a) := by
  simp only [coefficient,Finset.sum_mul]
  calc
    _ = ∑m∈support X s z,∑a∈(representations X s z).filter (fun a => index a=m),
        FrontierSmallBracket.smallWeight X s true a.2.1*f (index a) := by
      apply Finset.sum_congr rfl
      intro m _
      apply Finset.sum_congr rfl
      intro a ha
      rw [(Finset.mem_filter.mp ha).2]
    _ = _ := Finset.sum_fiberwise_of_maps_to
      (fun a ha => Finset.mem_image.mpr ⟨a,ha,rfl⟩) _

theorem representations_sum (X s z : ℝ) (F : (ℕ × ℕ × ℕ)→ℝ) :
    (∑a∈representations X s z,F a)=
      ∑j∈bands X s,∑d∈FrontierSmallBracketSplit.lowSupport X s,
        ∑p∈primeBand (SieveWeightedCutoffs.level X s) s z j,F (j,d,p) := by
  rw [representations,Finset.sum_biUnion]
  · apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_image (by intro a _ b _ h; exact Prod.mk.inj h |>.2),Finset.sum_product]
  · intro j _ k _ hjk
    apply Finset.disjoint_left.mpr
    intro a ha hb
    obtain ⟨u,_,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨v,_,hv⟩ := Finset.mem_image.mp hb
    exact hjk (congrArg Prod.fst hv).symm

theorem kernel_eq_band_sum (X s z : ℝ) (f : ℕ→ℝ) :
    (∑m∈support X s z,coefficient X s z m*f m)=
      ∑j∈bands X s,FrontierSmallBracketSplit.lowKernel X s z true [j] f := by
  rw [kernel,representations_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact (low_singleton_kernel X s z j f).symm

theorem kernel_eq_sector (X s z : ℝ) (f : ℕ→ℝ) :
    (∑m∈support X s z,coefficient X s z m*f m)=
      ∑a∈sector X s,(if a.1 then -1 else 1)*
        FrontierSmallBracketSplit.lowKernel X s z (!a.1) (a.2.1++[a.2.2]) f := by
  rw [kernel_eq_band_sum]
  symm
  apply Finset.sum_bij (fun a _ => a.2.2)
  · intro a ha
    exact Finset.mem_image.mpr ⟨a,ha,rfl⟩
  · intro a ha b hb he
    obtain ⟨_,ha1,ha2⟩ := Finset.mem_filter.mp ha
    obtain ⟨_,hb1,hb2⟩ := Finset.mem_filter.mp hb
    exact Prod.ext (ha1.trans hb1.symm) (Prod.ext (ha2.trans hb2.symm) he)
  · intro j hj
    obtain ⟨a,ha,he⟩ := Finset.mem_image.mp hj
    exact ⟨a,ha,he⟩
  · intro a ha
    obtain ⟨_,hb,hg⟩ := Finset.mem_filter.mp ha
    simp [hb,hg]

theorem remainder_eq_sector (X s z L R : ℝ) :
    remainder X s z L R =
      ∑a∈sector X s,(if a.1 then -1 else 1)*
        FrontierSmallBracketSplit.lowRemainder X s z (!a.1) (a.2.1++[a.2.2]) L R := by
  rw [remainder,HarmanDivisorWindow.remainder_eq_sum]
  exact kernel_eq_sector X s z (FrontierSmallBracketSplit.windowKernel L R)

theorem kernel_eq_Icc (X s z : ℝ) (hX : 1<X) (hs : 0<s) (hs1 : s≤1/1000)
    (hz : z≤X^(SieveWeightedScalarBudget.alpha s)) (f : ℕ→ℝ) :
    (∑m∈support X s z,coefficient X s z m*f m)=
      ∑m∈Finset.Icc 1 ⌊X^(31/125:ℝ)⌋₊,coefficient X s z m*f m := by
  apply Finset.sum_subset
  · intro m hm
    exact Finset.mem_Icc.mpr (support_le_floor X s z hX hs hs1 hz m hm)
  · intro m _ hm
    rw [coefficient_zero_off_support X s z m hm,zero_mul]

theorem remainder_eq_Icc (X s z L R : ℝ) (hX : 1<X) (hs : 0<s) (hs1 : s≤1/1000)
    (hz : z≤X^(SieveWeightedScalarBudget.alpha s)) :
    remainder X s z L R = ∑m∈Finset.Icc 1 ⌊X^(31/125:ℝ)⌋₊,
      coefficient X s z m * FrontierSmallBracketSplit.windowKernel L R m := by
  rw [remainder,HarmanDivisorWindow.remainder_eq_sum]
  exact kernel_eq_Icc X s z hX hs hs1 hz _

run_cmd do
  for decl in [``mem_bands,``mem_representations,``index_injective,
      ``coefficient_at_index,``coefficient_zero_off_support,``coefficient_abs_le_one,
      ``support_positive,``support_lt,``cutoff_le_level,``support_le_floor,
      ``coefficient_abs_le_one_at_first_cutoff,``kernel,``representations_sum,
      ``kernel_eq_band_sum,``kernel_eq_sector,``remainder_eq_sector,
      ``kernel_eq_Icc,``remainder_eq_Icc] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ACTUAL EXCEPTIONAL SINGLETON COLLECTED WITH UNIT COEFFICIENT CAP"

end SingletonActualCollection
