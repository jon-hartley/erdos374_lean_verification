import OuterSmallCarrierCutoffWork

/-! Exact fixed-box expansion and relative interval structure of the
literal outer long-pair source. The index-pair count depends only on s. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
namespace OuterPairSourceIntervalWork
open SieveGeometricGrid SieveWeightedCutoffs SieveBoxedFamily
open LongerTupleEncoding OuterPairFixedBoxesWork OuterPairBoxIntervalsWork

def fixedBoxSource (X s : ℝ) (P : Finset ℕ) (z : ℝ→ℝ)
    (d a b i j p : ℕ) : Prop :=
  p∈P ∧ d∈SieveUpperBoxWindow.smallCarrier (level X s/p) s ∧
  a∈pool (level X s/p) s (z p) ∧ b∈pool (level X s/p) s (z p) ∧
  InBox (level X s/p) s (a:ℝ) i ∧ InBox (level X s/p) s (b:ℝ) j ∧
  j ≤ i ∧ 3*exponent s i < 1 ∧ LongerTupleSector.allLong X [a,b] ∧
  X^(109/200:ℝ)<(index (p,d,[a,b]):ℝ)

theorem source_iff_fixedBoxSource (X s : ℝ) (P : Finset ℕ) (z : ℝ→ℝ)
    (hD : ∀p∈P,1<level X s/p) (hz : ∀p∈P,z p≤level X s/p) (hs : 0<s)
    (p d a b : ℕ) :
    (p,d,[a,b])∈LongPairCollectionWork.source X s P z ↔
      ∃ i : ℕ, i∈boxIndices s ∧ ∃ j : ℕ, j∈boxIndices s ∧ fixedBoxSource X s P z d a b i j p := by
  rw [mem_source_iff_fixed_boxes X s P z hD hz hs]
  simp only [fixedBoxSource]
  constructor
  · rintro ⟨hp,hd,ha,hb,⟨i,hi,j,hj,hbia,hbjb,hji,hg⟩,hl,hm⟩
    exact ⟨i,hi,j,hj,hp,hd,ha,hb,hbia,hbjb,hji,hg,hl,hm⟩
  · rintro ⟨i,hi,j,hj,hp,hd,ha,hb,hbia,hbjb,hji,hg,hl,hm⟩
    exact ⟨hp,hd,ha,hb,⟨i,hi,j,hj,hbia,hbjb,hji,hg⟩,hl,hm⟩

/-- On a fixed pair of boxes, the literal source support is an interval
relative to the prime set P. -/
theorem fixedBoxSource_convex (X s : ℝ) (hX : 0<X) (hs : 0<s)
    (P : Finset ℕ) (z : ℝ→ℝ)
    (hz : ∀ p∈P, ∀ q∈P, p≤q → z q≤z p)
    (d a b i j p q r : ℕ) (hpq : p≤q) (hqr : q≤r)
    (hPq : q∈P)
    (hpr : fixedBoxSource X s P z d a b i j p)
    (hrr : fixedBoxSource X s P z d a b i j r) :
    fixedBoxSource X s P z d a b i j q := by
  obtain ⟨hPp,_,hap,hbp,haip,hbjp,hji,hgate,hlong,hprod⟩ := hpr
  obtain ⟨hPr,hdr,har,hbr,hair,hbjr,_,_,_,_⟩ := hrr
  have hp : 0<p := by
    by_contra hzero
    have he : p=0 := by omega
    subst p
    have hpow : 0<X^(109/200:ℝ) := Real.rpow_pos_of_pos hX _
    simp only [index,zero_mul,Nat.cast_zero] at hprod
    linarith
  have hcarrier := OuterSmallCarrierCutoffWork.original_carrier_stable_downward
    X s hX hs.le q r d (lt_of_lt_of_le hp hpq) hqr hdr
  have haq := pool_convex_outer X s hX hs p q r a hp hpq hqr z
    (hz q hPq r hPr hqr) hap har
  have hbq := pool_convex_outer X s hX hs p q r b hp hpq hqr z
    (hz q hPq r hPr hqr) hbp hbr
  have haiq := inBox_convex_outer X s hX hs p q r i hp hpq hqr (a:ℝ) haip hair
  have hbjq := inBox_convex_outer X s hX hs p q r j hp hpq hqr (b:ℝ) hbjp hbjr
  have hindex : index (p,d,[a,b])≤ index (q,d,[a,b]) := by
    simpa [index,Nat.mul_assoc] using Nat.mul_le_mul_right (d*(a*b)) hpq
  have hindexR : (index (p,d,[a,b]):ℝ)≤ index (q,d,[a,b]) := by exact_mod_cast hindex
  exact ⟨hPq,hcarrier,haq,hbq,haiq,hbjq,hji,hgate,hlong,hprod.trans_le hindexR⟩

run_cmd do
  for decl in [``source_iff_fixedBoxSource, ``fixedBoxSource_convex] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end OuterPairSourceIntervalWork
