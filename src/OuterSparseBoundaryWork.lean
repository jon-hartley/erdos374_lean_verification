import OuterSourceReindexWork
import SparseFloorVariableMeanWork

/-! Any bounded number of outer primes per divisor/tuple gives a negligible
source family. Boundary locations may depend arbitrarily on X and the
divisor/tuple; the saving is uniform in those locations. -/
set_option autoImplicit false
set_option maxHeartbeats 9000000
noncomputable section
attribute [local instance] Classical.propDecidable
open Filter MeasureTheory Set
open scoped BigOperators

namespace OuterSparseBoundaryWork
open LongerTupleEncoding LongerTupleActualProfiles LongPairCloseDistinctMeanWork
open OuterSourceReindexWork UpperAfter545Remaining

def boundarySource (X s : ℝ) (B : Slice→Finset ℕ) : Finset Representation :=
  (separatedSource X s).filter (fun r => r.1∈B (drop r))

def boundaryRemainder (X s L R : ℝ) (B : Slice→Finset ℕ) : ℝ :=
  (∑r∈boundarySource X s B,originalWeight X s true r*(floorKernel L R (index r):ℂ)).re

theorem slices_card_bound (X s : ℝ) (hX : 1<X) (hs : 0<s)
    (hs1 : s≤1/1000) (hlog : 1000≤Real.log X) :
    ((slices X s).card:ℝ) ≤ 8*X^(497/1000:ℝ) := by
  let D := Finset.range (⌊X^(1/1000:ℝ)⌋₊+1)
  let Q := Finset.range (⌊X^(31/125:ℝ)⌋₊+1)
  have hsub : slices X s ⊆ D ×ˢ (Q ×ˢ Q) := by
    intro u hu
    obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hu
    have hd := LongPairDistinctMultiplicityWork.source_small_divisor_power
      X s hX hs hs1 hlog r (Finset.mem_filter.mp hr).1
    have hf := LongPairSeparatedCoreWork.source_factor_ranges X s hX hs hs1 hlog r hr
    have hl := (separated_source_data X s r hr).1
    have hq (second : Bool) : (ShortPairSplitWork.prime second r:ℝ) ≤ X^(31/125:ℝ) :=
      (hf.2.2 _ (ShortPairSplitWork.prime_mem second r hl)).2.2.le.trans
        (Real.rpow_le_rpow_of_exponent_le hX.le (by linarith))
    have hd' : (r.2.1:ℝ) ≤ X^(1/1000:ℝ) := hd.2.le.trans
      (Real.rpow_le_rpow_of_exponent_le hX.le hs1)
    simp only [drop,D,Q,Finset.mem_product,Finset.mem_range,Nat.lt_add_one_iff]
    exact ⟨Nat.le_floor hd',Nat.le_floor (hq false),Nat.le_floor (hq true)⟩
  have hfactor (e : ℝ) (he : 0≤e) : ((⌊X^e⌋₊+1:ℕ):ℝ) ≤ 2*X^e := by
    have hf := Nat.floor_le (Real.rpow_nonneg (by linarith : 0≤X) e)
    have h1 := Real.one_le_rpow hX.le he
    push_cast
    linarith
  have hXp : 0<X := by linarith
  calc
    _ ≤ ((D ×ˢ (Q ×ˢ Q)).card:ℝ) := by exact_mod_cast Finset.card_le_card hsub
    _ = (D.card:ℝ)*((Q.card:ℝ)*(Q.card:ℝ)) := by simp
    _ ≤ (2*X^(1/1000:ℝ))*((2*X^(31/125:ℝ))*(2*X^(31/125:ℝ))) := by
      dsimp [D,Q]
      simp only [Finset.card_range]
      gcongr
      · exact hfactor _ (by norm_num)
      · exact hfactor _ (by norm_num)
      · exact hfactor _ (by norm_num)
    _ = 8*X^(497/1000:ℝ) := by
      calc
        _ = 8*(X^(1/1000:ℝ)*X^(31/125:ℝ)*X^(31/125:ℝ)) := by ring
        _ = _ := by rw [←Real.rpow_add hXp,←Real.rpow_add hXp]; norm_num

theorem boundary_card (X s : ℝ) (B : Slice→Finset ℕ) (K : ℕ)
    (hB : ∀u,(B u).card≤K) :
    (boundarySource X s B).card ≤ (slices X s).card*K := by
  let F := (slices X s).biUnion (fun u => (B u).image (rebuild u))
  have hsub : boundarySource X s B ⊆ F := by
    intro r hr
    obtain ⟨hr,hB⟩ := Finset.mem_filter.mp hr
    exact Finset.mem_biUnion.mpr ⟨drop r,Finset.mem_image.mpr ⟨r,hr,rfl⟩,
      Finset.mem_image.mpr ⟨r.1,hB,rebuild_drop r (separated_source_data X s r hr).1⟩⟩
  calc
    _ ≤ F.card := Finset.card_le_card hsub
    _ ≤ ∑u∈slices X s,((B u).image (rebuild u)).card := Finset.card_biUnion_le
    _ ≤ ∑_u∈slices X s,K := Finset.sum_le_sum (fun u _ => Finset.card_image_le.trans (hB u))
    _ = _ := by simp

theorem eventually_boundary_card (s : ℝ) (K : ℕ) (hs : 0<s) (hs1 : s≤1/1000) :
    ∀ᶠ X : ℝ in atTop, 1<X ∧ 1000≤Real.log X ∧
      ∀B : Slice→Finset ℕ, (∀u,(B u).card≤K) →
        ((boundarySource X s B).card:ℝ) ≤ X^(1/2:ℝ) := by
  filter_upwards [eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1000:ℝ)),
    PolynomialLogEnvelope.eventually_constant_bound (8*K) (3/1000)
      (by positivity) (by norm_num)] with X hX hlog hc
  refine ⟨hX,hlog,?_⟩
  intro B hB
  calc
    _ ≤ (slices X s).card*(K:ℝ) := by exact_mod_cast boundary_card X s B K hB
    _ ≤ (8*X^(497/1000:ℝ))*K :=
      mul_le_mul_of_nonneg_right (slices_card_bound X s hX hs hs1 hlog) (Nat.cast_nonneg _)
    _ = (8*K)*X^(497/1000:ℝ) := by ring
    _ ≤ X^(3/1000:ℝ)*X^(497/1000:ℝ) := mul_le_mul_of_nonneg_right hc.2 (by positivity)
    _ = _ := by rw [←Real.rpow_add (by linarith : 0<X)]; norm_num

theorem eventually_boundary_absolute_power (s : ℝ) (K : ℕ) (hs : 0<s) (hs1 : s≤1/1000) :
    ∀ᶠ X : ℝ in atTop, 1<X ∧ 1000≤Real.log X ∧
      ∀B : Slice→Finset ℕ, (∀u,(B u).card≤K) → ∀Y : ℝ, 0≤Y → Y≤X/2 →
      (1/X)*(∫x in Icc X (2*X),|boundaryRemainder X s (x-x*(Y/X)) x B|) ≤
        Y*X^(-1/5:ℝ) := by
  filter_upwards [eventually_boundary_card s K hs hs1,
    SparseFloorVariableMeanWork.eventually_sparse_absolute (α:=Representation)
      (1/2) (26/35) (1/5) (by norm_num) (by norm_num) (by norm_num)] with X hc hm
  refine ⟨hc.1,hc.2.1,?_⟩
  intro B hB Y hY hYX
  have hh := hm.2 (boundarySource X s B) index
    (fun r => (originalWeight X s true r).re) Y (hc.2.2 B hB)
    (by intro r hr
        exact (LongPairSeparatedCoreWork.support_geometry X s hc.1 hs hs1 hc.2.1 _
          (Finset.mem_image.mpr ⟨r,(Finset.mem_filter.mp hr).1,rfl⟩)).1.le)
    (fun r _ => (Complex.abs_re_le_norm _).trans (originalWeight_norm_le X s true r)) hY hYX
  simpa only [boundaryRemainder,Complex.re_sum,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,mul_zero,sub_zero,neg_div] using hh

run_cmd do
  for decl in [``slices_card_bound, ``boundary_card, ``eventually_boundary_card,
      ``eventually_boundary_absolute_power] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end OuterSparseBoundaryWork
