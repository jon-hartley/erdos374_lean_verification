import OuterSparseBoundaryWork

/-! Sparse boundary errors in an enlarged rectangular family, including
representations outside the original source. Weights may be any signed
unit coefficients. This is the error budget needed for smoothing masks. -/
set_option autoImplicit false
set_option maxHeartbeats 9000000
noncomputable section
attribute [local instance] Classical.propDecidable
open Filter MeasureTheory Set
open scoped BigOperators

namespace OuterBoundaryExtensionWork
open LongerTupleEncoding OuterSourceReindexWork UpperAfter545Remaining

def candidateSlices (X : ℝ) : Finset Slice :=
  Finset.Ioc 0 ⌊X^(1/1000:ℝ)⌋₊ ×ˢ
    (Finset.Ioc 0 ⌊X^(31/125:ℝ)⌋₊ ×ˢ Finset.Ioc 0 ⌊X^(31/125:ℝ)⌋₊)

def boundaryCandidates (X : ℝ) (B : Slice→Finset ℕ) : Finset Representation :=
  (candidateSlices X).biUnion (fun u => (B u).image (rebuild u))

theorem candidateSlices_card (X : ℝ) (hX : 0<X) :
    ((candidateSlices X).card:ℝ) ≤ X^(497/1000:ℝ) := by
  have hd := Nat.floor_le (Real.rpow_nonneg hX.le (1/1000:ℝ))
  have hq := Nat.floor_le (Real.rpow_nonneg hX.le (31/125:ℝ))
  simp only [candidateSlices,Finset.card_product,Nat.card_Ioc,Nat.sub_zero,Nat.cast_mul]
  calc
    _ ≤ X^(1/1000:ℝ)*(X^(31/125:ℝ)*X^(31/125:ℝ)) := by gcongr
    _ = _ := by rw [←Real.rpow_add hX,←Real.rpow_add hX]; norm_num

theorem source_slices_subset (X s : ℝ) (hX : 1<X) (hs : 0<s)
    (hs1 : s≤1/1000) (hlog : 1000≤Real.log X) :
    slices X s ⊆ candidateSlices X := by
  intro u hu
  obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hu
  have hd := LongPairDistinctMultiplicityWork.source_small_divisor_power
    X s hX hs hs1 hlog r (Finset.mem_filter.mp hr).1
  have hf := LongPairSeparatedCoreWork.source_factor_ranges X s hX hs hs1 hlog r hr
  have hl := (separated_source_data X s r hr).1
  have hq (second : Bool) : 0<ShortPairSplitWork.prime second r ∧
      (ShortPairSplitWork.prime second r:ℝ) ≤ X^(31/125:ℝ) := by
    have hh := hf.2.2 _ (ShortPairSplitWork.prime_mem second r hl)
    exact ⟨hh.1.pos,hh.2.2.le.trans
      (Real.rpow_le_rpow_of_exponent_le hX.le (by linarith))⟩
  have hd' : (r.2.1:ℝ) ≤ X^(1/1000:ℝ) := hd.2.le.trans
    (Real.rpow_le_rpow_of_exponent_le hX.le hs1)
  simp only [candidateSlices,drop,Finset.mem_product,Finset.mem_Ioc]
  exact ⟨⟨hd.1,Nat.le_floor hd'⟩,⟨(hq false).1,Nat.le_floor (hq false).2⟩,
    ⟨(hq true).1,Nat.le_floor (hq true).2⟩⟩

theorem boundaryCandidates_card (X : ℝ) (B : Slice→Finset ℕ) (K : ℕ)
    (hB : ∀u,(B u).card≤K) :
    (boundaryCandidates X B).card ≤ (candidateSlices X).card*K := by
  calc
    _ ≤ ∑u∈candidateSlices X,((B u).image (rebuild u)).card := Finset.card_biUnion_le
    _ ≤ ∑_u∈candidateSlices X,K :=
      Finset.sum_le_sum (fun u _ => Finset.card_image_le.trans (hB u))
    _ = _ := by simp

theorem eventually_boundaryCandidates_card (K : ℕ) :
    ∀ᶠ X : ℝ in atTop, 1<X ∧ ∀B : Slice→Finset ℕ, (∀u,(B u).card≤K) →
      ((boundaryCandidates X B).card:ℝ) ≤ X^(1/2:ℝ) := by
  filter_upwards [eventually_gt_atTop (1:ℝ),
    PolynomialLogEnvelope.eventually_constant_bound (K:ℝ) (3/1000)
      (Nat.cast_nonneg _) (by norm_num)] with X hX hc
  refine ⟨hX,?_⟩
  intro B hB
  calc
    _ ≤ (candidateSlices X).card*(K:ℝ) := by exact_mod_cast boundaryCandidates_card X B K hB
    _ ≤ X^(497/1000:ℝ)*K :=
      mul_le_mul_of_nonneg_right (candidateSlices_card X (by linarith)) (Nat.cast_nonneg _)
    _ ≤ X^(497/1000:ℝ)*X^(3/1000:ℝ) := mul_le_mul_of_nonneg_left hc.2 (by positivity)
    _ = _ := by rw [←Real.rpow_add (by linarith : 0<X)]; norm_num

theorem eventually_extended_boundary_absolute (K : ℕ) :
    ∀ᶠ X : ℝ in atTop, 1<X ∧ ∀B : Slice→Finset ℕ, (∀u,(B u).card≤K) →
      ∀S : Finset Representation, S⊆boundaryCandidates X B →
      (∀r∈S,X^(7/10:ℝ) ≤ (index r:ℝ)) →
      ∀w : Representation→ℝ, (∀r∈S,|w r|≤1) → ∀Y : ℝ, 0≤Y → Y≤X/2 →
        (1/X)*(∫x in Icc X (2*X),
          |∑r∈S,w r*floorKernel (x-x*(Y/X)) x (index r)|) ≤ Y*X^(-19/100:ℝ) := by
  filter_upwards [eventually_boundaryCandidates_card K,
    SparseFloorVariableMeanWork.eventually_sparse_absolute (α:=Representation)
      (1/2) (7/10) (19/100) (by norm_num) (by norm_num) (by norm_num)] with X hc hm
  refine ⟨hc.1,?_⟩
  intro B hB S hS hi w hw Y hY hYX
  have hcard' : (S.card:ℝ) ≤ (boundaryCandidates X B).card :=
    by exact_mod_cast Finset.card_le_card hS
  have hcard := hcard'.trans (hc.2 B hB)
  simpa only [neg_div] using hm.2 S index w Y hcard hi hw hY hYX

run_cmd do
  for decl in [``candidateSlices_card, ``source_slices_subset,
      ``boundaryCandidates_card, ``eventually_boundaryCandidates_card,
      ``eventually_extended_boundary_absolute] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end OuterBoundaryExtensionWork
