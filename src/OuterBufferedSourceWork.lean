import OuterCutoffBufferWork
import OuterSeparatedLogMaskWork

/-! Excise the outer-prime boundaries of all nine logarithmic source
inequalities, uniformly over the finite box pairs. The discarded family
has an unconditional absolute-mean power saving; the retained source has
polynomial logarithmic distance from every source cutoff. -/
set_option autoImplicit false
set_option maxHeartbeats 9000000
noncomputable section
attribute [local instance] Classical.propDecidable
open Filter MeasureTheory Set
open scoped BigOperators

namespace OuterBufferedSourceWork
open LongerTupleEncoding LongerTupleActualProfiles LongPairCloseDistinctMeanWork
open OuterSourceReindexWork OuterPairSourceDecompositionWork SieveGeometricGrid
open OuterSparseBoundaryWork OuterCutoffBufferWork UpperAfter545Remaining

def cutoffLogs (X s : ℝ) (u : Slice) (i j : ℕ) : Fin 9→ℝ :=
  let H := (1-3*s)*Real.log X
  let a := Real.log (u.2.1:ℝ)
  let b := Real.log (u.2.2:ℝ)
  ![H-3*a,H-a/s^2,H-3*b,H-b/s^2,
    H-a/exponent s i,H-a/exponent s (i+1),
    H-b/exponent s j,H-b/exponent s (j+1),
    (26/35:ℝ)*Real.log X-Real.log (u.1:ℝ)-a-b]

def boundaryPrimes (X s : ℝ) (u : Slice) : Finset ℕ :=
  (boxPairs s).biUnion (fun ij => Finset.univ.biUnion
    (fun n : Fin 9 => nearCutoff (Real.exp (cutoffLogs X s u ij.1 ij.2 n))))

def bufferedSource (X s : ℝ) : Finset Representation :=
  (separatedSource X s).filter (fun r => r.1∉boundaryPrimes X s (drop r))

def bufferedRemainder (X s L R : ℝ) : ℝ :=
  (∑r∈bufferedSource X s,originalWeight X s true r*(floorKernel L R (index r):ℂ)).re

theorem boundaryPrimes_card (X s : ℝ) (u : Slice) :
    (boundaryPrimes X s u).card ≤ (boxPairs s).card*27 := by
  calc
    _ ≤ ∑ij∈boxPairs s,(Finset.univ.biUnion
        (fun n : Fin 9 => nearCutoff (Real.exp (cutoffLogs X s u ij.1 ij.2 n)))).card :=
      Finset.card_biUnion_le
    _ ≤ ∑_ij∈boxPairs s,27 := Finset.sum_le_sum (fun ij _ => by
      calc
        _ ≤ ∑n : Fin 9,(nearCutoff (Real.exp (cutoffLogs X s u ij.1 ij.2 n))).card :=
          Finset.card_biUnion_le
        _ ≤ ∑_n : Fin 9,3 := Finset.sum_le_sum (fun n _ => nearCutoff_card _)
        _ = 27 := by simp)
    _ = _ := by simp

theorem source_partition (X s L R : ℝ) :
    separatedRemainder X s L R =
      boundaryRemainder X s L R (boundaryPrimes X s)+bufferedRemainder X s L R := by
  unfold separatedRemainder boundaryRemainder bufferedRemainder boundarySource bufferedSource
  rw [←Complex.add_re]
  congr 1
  simp only [Finset.sum_filter,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _
  by_cases hr : r.1∈boundaryPrimes X s (drop r) <;> simp [hr]

theorem buffered_log_gap (X s : ℝ) (hX : 1<X) (hs : 0<s)
    (hs1 : s≤1/1000) (hlog : 1000≤Real.log X) (r : Representation)
    (hr : r∈bufferedSource X s) (ij : ℕ×ℕ) (hij : ij∈boxPairs s) (n : Fin 9) :
    1/(2*X) ≤ |Real.log (r.1:ℝ)-cutoffLogs X s (drop r) ij.1 ij.2 n| := by
  obtain ⟨hr,hnot⟩ := Finset.mem_filter.mp hr
  have hf := LongPairSeparatedCoreWork.source_factor_ranges X s hX hs hs1 hlog r hr
  have hp : 0<r.1 := by
    exact_mod_cast (Real.rpow_pos_of_pos (by linarith : 0<X) (9/35:ℝ)).trans_le hf.1
  have hpX : (r.1:ℝ)≤X := by
    apply hf.2.1.le.trans
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hX.le
      (by linarith : (313/1000:ℝ)-3*s≤1)
  have hcut : r.1∉nearCutoff (Real.exp (cutoffLogs X s (drop r) ij.1 ij.2 n)) := by
    intro hh
    apply hnot
    exact Finset.mem_biUnion.mpr ⟨ij,hij,Finset.mem_biUnion.mpr ⟨n,Finset.mem_univ n,hh⟩⟩
  simpa only [Real.log_exp] using log_gap_of_not_mem X _ r.1 hp hpX (Real.exp_pos _) hcut

theorem eventually_boundary_absolute_power (s : ℝ) (hs : 0<s) (hs1 : s≤1/1000) :
    ∀ᶠ X : ℝ in atTop, 1<X ∧ 1000≤Real.log X ∧ ∀Y : ℝ, 0≤Y → Y≤X/2 →
      (1/X)*(∫x in Icc X (2*X),
        |boundaryRemainder X s (x-x*(Y/X)) x (boundaryPrimes X s)|) ≤ Y*X^(-1/5:ℝ) := by
  filter_upwards [OuterSparseBoundaryWork.eventually_boundary_absolute_power
    s ((boxPairs s).card*27) hs hs1] with X hX
  exact ⟨hX.1,hX.2.1,hX.2.2 (boundaryPrimes X s) (boundaryPrimes_card X s)⟩

run_cmd do
  for decl in [``boundaryPrimes_card, ``source_partition, ``buffered_log_gap,
      ``eventually_boundary_absolute_power] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end OuterBufferedSourceWork
