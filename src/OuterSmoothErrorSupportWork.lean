import OuterSmoothStepWork
import OuterBoundaryExtensionWork

/-! The continuous nine-cutoff replacement differs from the exact mask
only on the enlarged sparse boundary family. Every nonzero error has
modulus at least X^.7, including representations outside the source. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
attribute [local instance] Classical.propDecidable

namespace OuterSmoothErrorSupportWork
open LongerTupleEncoding OuterSourceReindexWork OuterBufferedSourceWork
open OuterPairSourceDecompositionWork OuterCutoffBufferWork OuterSmoothStepWork
open OuterBoundaryExtensionWork PositiveSharpBoxedCount

def width (X : ℝ) : ℝ := 1/(4*X)

def maskError (X s : ℝ) (u : Slice) (i j p : ℕ) : ℝ :=
  sharpCuts (Real.log (p:ℝ)) (cutoffLogs X s u i j) -
    smoothCuts (width X) (Real.log (p:ℝ)) (cutoffLogs X s u i j)

def ambient (X : ℝ) : Finset Representation :=
  (candidateSlices X).biUnion (fun u => (largePrimes X).image (rebuild u))

def errorSupport (X s : ℝ) (i j : ℕ) : Finset Representation :=
  (ambient X).filter (fun r => maskError X s (drop r) i j r.1≠0)

theorem maskError_abs_le (X s : ℝ) (u : Slice) (i j p : ℕ) :
    |maskError X s u i j p|≤1 := cuts_error_abs_le _ _ _

theorem maskError_zero_off_boundary (X s : ℝ) (hX : 0<X) (u : Slice)
    (ij : ℕ×ℕ) (hij : ij∈boxPairs s) (p : ℕ) (hp : 0<p) (hpX : (p:ℝ)≤X)
    (hnot : p∉boundaryPrimes X s u) : maskError X s u ij.1 ij.2 p=0 := by
  have hwidth : width X≤1/(2*X) := by
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
  have hgap (n : Fin 9) : width X≤|Real.log (p:ℝ)-cutoffLogs X s u ij.1 ij.2 n| := by
    have hn : p∉nearCutoff (Real.exp (cutoffLogs X s u ij.1 ij.2 n)) := by
      intro hh
      exact hnot (Finset.mem_biUnion.mpr ⟨ij,hij,
        Finset.mem_biUnion.mpr ⟨n,Finset.mem_univ n,hh⟩⟩)
    have hh := log_gap_of_not_mem X _ p hp hpX (Real.exp_pos _) hn
    exact hwidth.trans (by simpa only [Real.log_exp] using hh)
  unfold maskError
  rw [smoothCuts_eq_sharp _ _ _ (by unfold width; positivity) hgap,sub_self]

theorem error_index_lower (X s : ℝ) (hX : 1<X) (hlog : 1000≤Real.log X)
    (u : Slice) (p i j : ℕ) (hp : 0<p)
    (hd : 0<u.1) (ha : 0<u.2.1) (hb : 0<u.2.2)
    (herr : maskError X s u i j p≠0) : X^(7/10:ℝ) ≤ (index (rebuild u p):ℝ) := by
  have hXp : 0<X := by linarith
  have hw : 0<width X := by unfold width; positivity
  have hw1 : width X≤1 := by
    unfold width
    exact (div_le_one (by positivity)).mpr (by linarith)
  have hh := error_nonzero_last_gap _ _ _ hw herr
  change -(width X) < Real.log (p:ℝ)-
    ((26/35:ℝ)*Real.log X-Real.log (u.1:ℝ)-Real.log (u.2.1:ℝ)-Real.log (u.2.2:ℝ)) at hh
  have hi : (0:ℝ) < index (rebuild u p) := by
    simp only [rebuild,index,List.prod_cons,List.prod_nil,Nat.cast_mul,Nat.cast_one]
    positivity
  apply (Real.log_le_log_iff (Real.rpow_pos_of_pos hXp _) hi).mp
  rw [Real.log_rpow hXp]
  change (7/10:ℝ)*Real.log X ≤ Real.log (index (p,u.1,[u.2.1,u.2.2]):ℝ)
  rw [OuterPairLogConstraintsWork.log_index p u.1 u.2.1 u.2.2 hp hd ha hb]
  linarith

theorem ambient_data (X : ℝ) (hX : 2≤X) (r : Representation) (hr : r∈ambient X) :
    r.2.2.length=2 ∧ drop r∈candidateSlices X ∧ 0<r.1 ∧ (r.1:ℝ)≤X ∧
      0<(drop r).1 ∧ 0<(drop r).2.1 ∧ 0<(drop r).2.2 := by
  obtain ⟨u,hu,hr⟩ := Finset.mem_biUnion.mp hr
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hr
  have hb := PositiveSharpSieveDecomposition.large_band_bounds X p hp
  have hsq : Real.sqrt (2*X)≤X := by
    apply (Real.sqrt_le_iff).mpr
    exact ⟨by linarith,by nlinarith⟩
  have hpos := Finset.mem_product.mp hu
  have hpos' := Finset.mem_product.mp hpos.2
  refine ⟨by simp [rebuild],?_⟩
  simp only [drop_rebuild]
  exact ⟨hu,hb.1.pos,hb.2.2.trans hsq,
    (Finset.mem_Ioc.mp hpos.1).1,(Finset.mem_Ioc.mp hpos'.1).1,(Finset.mem_Ioc.mp hpos'.2).1⟩

theorem errorSupport_subset (X s : ℝ) (hX : 2≤X) (ij : ℕ×ℕ) (hij : ij∈boxPairs s) :
    errorSupport X s ij.1 ij.2 ⊆ boundaryCandidates X (boundaryPrimes X s) := by
  intro r hr
  obtain ⟨hr,herr⟩ := Finset.mem_filter.mp hr
  have hd := ambient_data X hX r hr
  have hb : r.1∈boundaryPrimes X s (drop r) := by
    by_contra hn
    exact herr (maskError_zero_off_boundary X s (by linarith) (drop r) ij hij r.1 hd.2.2.1 hd.2.2.2.1 hn)
  exact Finset.mem_biUnion.mpr ⟨drop r,hd.2.1,
    Finset.mem_image.mpr ⟨r.1,hb,rebuild_drop r hd.1⟩⟩

theorem errorSupport_index (X s : ℝ) (hX : 2≤X) (hlog : 1000≤Real.log X)
    (i j : ℕ) (r : Representation) (hr : r∈errorSupport X s i j) :
    X^(7/10:ℝ) ≤ (index r:ℝ) := by
  obtain ⟨hr,herr⟩ := Finset.mem_filter.mp hr
  have hd := ambient_data X hX r hr
  have hh := error_index_lower X s (by linarith) hlog (drop r) r.1 i j hd.2.2.1
    hd.2.2.2.2.1 hd.2.2.2.2.2.1 hd.2.2.2.2.2.2 herr
  simpa only [rebuild_drop r hd.1] using hh

run_cmd do
  for decl in [``maskError_abs_le, ``maskError_zero_off_boundary,
      ``error_index_lower, ``ambient_data, ``errorSupport_subset, ``errorSupport_index] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end OuterSmoothErrorSupportWork
