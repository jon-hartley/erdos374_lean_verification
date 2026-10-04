import LongPairSmallGeometryWork
import TailRemainderBand

/-! Exact literal long-pair coefficients, retaining ordered representations
and collisions. Small coefficients and regularity do not assert a mean bound. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace LongPairCollectionWork
open LongerTupleActualProfiles LongerTupleEncoding LongerTupleCollection
open SieveWeightedCutoffs LongerTupleSector PositiveSharpBoxedCount
open UpperAfter545Sectors UpperAfter545Remaining SieveCappedUpperMainTerms

def source (X s : ℝ) (P : Finset ℕ) (z : ℝ → ℝ) : Finset Representation :=
  P.biUnion (fun p => (SieveUpperBoxWindow.smallCarrier (level X s/p) s).biUnion
    (fun d => ((SieveUpperBoxing.outerFamily (level X s/p) s (z p)).filter
      (fun t => t.length=2 ∧ allLong X t ∧ X^(109/200:ℝ)<((p*d*t.prod:ℕ):ℝ))).image
        (fun t => (p,d,t))))

theorem mem_source (X s : ℝ) (P : Finset ℕ) (z : ℝ → ℝ) (a : Representation) :
    a∈source X s P z ↔ a.1∈P ∧
      a.2.1∈SieveUpperBoxWindow.smallCarrier (level X s/a.1) s ∧
      a.2.2∈SieveUpperBoxing.outerFamily (level X s/a.1) s (z a.1) ∧
      a.2.2.length=2 ∧ allLong X a.2.2 ∧ X^(109/200:ℝ)<(index a:ℝ) := by
  rcases a with ⟨p,d,t⟩
  simp [source,index,and_assoc]

theorem source_sum (X s : ℝ) (P : Finset ℕ) (z : ℝ → ℝ) (f : Representation → ℂ) :
    (∑ a∈source X s P z,f a) =
      ∑ p∈P,∑ d∈SieveUpperBoxWindow.smallCarrier (level X s/p) s,
        ∑ t∈(SieveUpperBoxing.outerFamily (level X s/p) s (z p)).filter
          (fun t => t.length=2 ∧ allLong X t ∧ X^(109/200:ℝ)<((p*d*t.prod:ℕ):ℝ)),
            f (p,d,t) := by
  unfold source
  rw [Finset.sum_biUnion]
  · apply Finset.sum_congr rfl
    intro p _
    rw [Finset.sum_biUnion]
    · apply Finset.sum_congr rfl
      intro d _
      exact Finset.sum_image (fun t _ u _ he => (Prod.mk.inj (Prod.mk.inj he).2).2)
    · intro d _ e _ hde
      apply Finset.disjoint_left.mpr
      intro a ha hb
      obtain ⟨t,_,ht⟩ := Finset.mem_image.mp ha
      obtain ⟨u,_,hu⟩ := Finset.mem_image.mp hb
      exact hde (Prod.mk.inj (Prod.mk.inj (ht.trans hu.symm)).2).1
  · intro p _ q _ hpq
    apply Finset.disjoint_left.mpr
    intro a ha hb
    obtain ⟨d,_,hd⟩ := Finset.mem_biUnion.mp ha
    obtain ⟨e,_,he⟩ := Finset.mem_biUnion.mp hb
    obtain ⟨t,_,ht⟩ := Finset.mem_image.mp hd
    obtain ⟨u,_,hu⟩ := Finset.mem_image.mp he
    exact hpq (Prod.mk.inj (ht.trans hu.symm)).1

theorem longPairBand_eq_source (X s : ℝ) (P : Finset ℕ) (z : ℝ → ℝ) (f : ℕ → ℝ) :
    (longPairBand X s P z f:ℂ) =
      ∑ a∈source X s P z, originalWeight X s true a*(f (index a):ℂ) := by
  rw [source_sum]
  unfold longPairBand selectedKernel
  simp only [↓reduceIte,Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro d _
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro t _
  by_cases he : t.length=2 ∧ allLong X t <;>
    by_cases hh : X^(109/200:ℝ)<((p*(d*t.prod):ℕ):ℝ) <;>
    simp only [originalWeight,index,highKernel,Nat.mul_assoc,he,hh,
      ite_true,ite_false,and_true,and_false,mul_zero,Complex.ofReal_mul,Complex.ofReal_zero]

def divisorSupport (X s : ℝ) (P : Finset ℕ) (z : ℝ → ℝ) : Finset ℕ :=
  support (source X s P z) index

def divisorCoefficient (X s : ℝ) (P : Finset ℕ) (z : ℝ → ℝ) (m : ℕ) : ℝ :=
  (coefficient (source X s P z) index (originalWeight X s true) m).re

theorem band_eq_remainder (X s : ℝ) (P : Finset ℕ) (z : ℝ → ℝ) (L R : ℝ) :
    longPairBand X s P z (floorKernel L R) =
      HarmanDivisorWindow.remainder (divisorSupport X s P z)
        (divisorCoefficient X s P z) L R := by
  have hh := congrArg Complex.re
    ((longPairBand_eq_source X s P z (floorKernel L R)).trans
      (grouped_sum (source X s P z) index (originalWeight X s true)
        (fun m => (floorKernel L R m:ℂ))).symm)
  rw [HarmanDivisorWindow.remainder_eq_sum]
  simpa only [divisorSupport,divisorCoefficient,floorKernel,Complex.ofReal_re,
    Complex.re_sum,Complex.mul_re,Complex.ofReal_im,mul_zero,sub_zero] using hh

theorem band_moving_integrable (X s Y : ℝ) (P : Finset ℕ) (z : ℝ → ℝ) :
    IntegrableOn (fun x => longPairBand X s P z (floorKernel (x-x*(Y/X)) x))
      (Icc X (2*X)) := by
  simp_rw [band_eq_remainder]
  simpa only [mul_div_assoc] using TailRemainderBand.moving_remainder_integrable
    (divisorSupport X s P z) (divisorCoefficient X s P z) X Y

theorem source_small_geometry (X s : ℝ) (hX : 1<X) (hs : 0<s)
    (hs1 : s≤1/1000) (hlog : 1000≤Real.log X) (a : Representation)
    (ha : a∈source X s (smallPrimes X s) (cappedFourth X s)) :
    X^(109/200:ℝ)<(index a:ℝ) ∧ (index a:ℝ)<X^(26/35-s:ℝ) ∧
      X^(246/1000:ℝ)≤((a.1*a.2.1:ℕ):ℝ) ∧ X^(16/35:ℝ)<(a.2.2.prod:ℝ) := by
  obtain ⟨hp,hd,ht,hlen,hl,hhigh⟩ := (mem_source X s _ _ a).mp ha
  obtain ⟨u,v,he⟩ := List.length_eq_two.mp hlen
  have hphysical := LongPairSmallGeometryWork.small_band_physical_pair_lt X s
    a.1 a.2.1 u v hX hs hs1 hlog hp hd (by simpa only [he] using ht)
  have hfactor := LongPairSmallGeometryWork.factor_lower X s a.1 a.2.1 u v
    hX hs hs1 hp (UpperAfter545Geometry.smallCarrier_pos _ _ _ hd)
    (by simpa only [he] using hl)
  refine ⟨hhigh,?_,hfactor.1,?_⟩
  · simpa [index,he,mul_assoc] using hphysical.1
  · simpa [he] using hfactor.2

/-- Uniform arbitrarily small power cap on the full collected coefficient,
not merely on an individual representation's weight. -/
theorem eventually_coefficient_cap (δ : ℝ) (hδ : 0<δ) :
    ∀ᶠ X : ℝ in atTop, 1≤X ∧ ∀ (s : ℝ) (P : Finset ℕ) (z : ℝ → ℝ)
      (m : ℕ), 0<m → (m:ℝ)≤X^2 → |divisorCoefficient X s P z m|≤X^δ := by
  filter_upwards [LongerTupleEncoding.eventual_coefficient_cap 2 δ hδ] with X hm
  refine ⟨hm.1,?_⟩
  intro s P z m hpos hcap
  have hh := hm.2 (source X s P z) (originalWeight X s true)
    (fun a ha => ((mem_source X s P z a).mp ha).2.2.2.1)
    (fun a _ => originalWeight_norm_le X s true a) m hpos hcap
  exact (Complex.abs_re_le_norm _).trans hh

/-- Every occupied dyadic grouping cell has the exact scalar scale guards
required by the flat theorem. This does not assert coefficient separability. -/
theorem eventually_small_dyadic_scales :
    ∀ᶠ X : ℝ in atTop, 1<X ∧ ∀ (s : ℝ) (M N : ℕ) (a : Representation),
      0<s → s≤1/1000 → 1000≤Real.log X →
      a∈source X s (smallPrimes X s) (cappedFourth X s) →
      M<a.1*a.2.1 → a.1*a.2.1≤2*M → N<a.2.2.prod → a.2.2.prod≤2*N →
      X^TripleFlatParameters.primeExponent≤(M:ℝ) ∧
        X^TripleFlatParameters.pairExponent≤(N:ℝ) ∧
        ((M*N:ℕ):ℝ)≤X^(26/35:ℝ) := by
  filter_upwards [PolynomialLogEnvelope.eventually_constant_bound 2
      ((246/1000:ℝ)-TripleFlatParameters.primeExponent) (by norm_num)
        (by norm_num [TripleFlatParameters.primeExponent]),
    PolynomialLogEnvelope.eventually_constant_bound 2
      ((16/35:ℝ)-TripleFlatParameters.pairExponent) (by norm_num)
        (by norm_num [TripleFlatParameters.pairExponent]),
    eventually_gt_atTop (1:ℝ)] with X hm hn hX
  refine ⟨hX,?_⟩
  intro s M N a hs hs1 hlog ha hMlo hMhi hNlo hNhi
  have hX0 : 0<X := by linarith
  have hg := source_small_geometry X s hX hs hs1 hlog a ha
  have hM : 2*X^TripleFlatParameters.primeExponent≤X^(246/1000:ℝ) := by
    have hh := mul_le_mul_of_nonneg_right hm.2
      (Real.rpow_pos_of_pos hX0 TripleFlatParameters.primeExponent).le
    rw [←Real.rpow_add hX0,sub_add_cancel] at hh
    exact hh
  have hN : 2*X^TripleFlatParameters.pairExponent≤X^(16/35:ℝ) := by
    have hh := mul_le_mul_of_nonneg_right hn.2
      (Real.rpow_pos_of_pos hX0 TripleFlatParameters.pairExponent).le
    rw [←Real.rpow_add hX0,sub_add_cancel] at hh
    exact hh
  have hMhiR : ((a.1*a.2.1:ℕ):ℝ)≤2*(M:ℝ) := by exact_mod_cast hMhi
  have hNhiR : (a.2.2.prod:ℝ)≤2*(N:ℝ) := by exact_mod_cast hNhi
  refine ⟨by linarith [hg.2.2.1],by linarith [hg.2.2.2],?_⟩
  have hprod : M * N ≤ index a := by
    unfold index
    exact Nat.mul_le_mul hMlo.le hNlo.le
  exact (by exact_mod_cast hprod : ((M*N:ℕ):ℝ)≤(index a:ℝ)).trans
    (hg.2.1.le.trans (Real.rpow_le_rpow_of_exponent_le hX.le (by linarith)))

#print axioms band_eq_remainder
#print axioms eventually_coefficient_cap
#print axioms eventually_small_dyadic_scales
run_cmd do
  for decl in [``mem_source, ``source_sum, ``longPairBand_eq_source, ``band_eq_remainder,
      ``band_moving_integrable, ``source_small_geometry, ``eventually_coefficient_cap,
      ``eventually_small_dyadic_scales] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"

end LongPairCollectionWork
