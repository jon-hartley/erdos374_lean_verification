import OuterRampLengthWork

/-! A simple polynomial bound for the entire enlarged ambient family,
including the exterior terms introduced by source smoothing. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace OuterAmbientSizeWork
open OuterBoundaryExtensionWork OuterSmoothErrorSupportWork PositiveSharpBoxedCount
open OuterSourceReindexWork LongerTupleEncoding

theorem largePrimes_card_le (X : ℝ) (hX : 2 ≤ X) : ((largePrimes X).card:ℝ) ≤ X := by
  have hsub : largePrimes X ⊆ Finset.Ioc 0 ⌊X⌋₊ := by
    intro p hp
    have hb := PositiveSharpSieveDecomposition.large_band_bounds X p hp
    have hsq : Real.sqrt (2*X) ≤ X := by
      apply (Real.sqrt_le_iff).mpr
      exact ⟨by linarith,by nlinarith⟩
    exact Finset.mem_Ioc.mpr ⟨hb.1.pos,Nat.le_floor (hb.2.2.trans hsq)⟩
  have hc : (largePrimes X).card ≤ ⌊X⌋₊ := by
    simpa only [Nat.card_Ioc,Nat.sub_zero] using Finset.card_le_card hsub
  exact (by exact_mod_cast hc : ((largePrimes X).card:ℝ) ≤ ⌊X⌋₊).trans
    (Nat.floor_le (by linarith))

theorem ambient_card_le (X : ℝ) (hX : 2 ≤ X) : ((ambient X).card:ℝ) ≤ X^2 := by
  have hc : (ambient X).card ≤ (candidateSlices X).card*(largePrimes X).card := by
    calc
      _ ≤ ∑u∈candidateSlices X,((largePrimes X).image (rebuild u)).card := Finset.card_biUnion_le
      _ ≤ ∑_u∈candidateSlices X,(largePrimes X).card :=
        Finset.sum_le_sum (fun _ _ => Finset.card_image_le)
      _ = _ := by simp
  have hs : ((candidateSlices X).card:ℝ) ≤ X := by
    apply (candidateSlices_card X (by linarith)).trans
    simpa using Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ X)
      (by norm_num : (497/1000:ℝ) ≤ 1)
  calc
    _ ≤ ((candidateSlices X).card:ℝ)*((largePrimes X).card:ℝ) := by exact_mod_cast hc
    _ ≤ X*X := mul_le_mul hs (largePrimes_card_le X hX) (Nat.cast_nonneg _) (by linarith)
    _ = _ := (pow_two X).symm

theorem ambient_index_pos (X : ℝ) (hX : 2 ≤ X) (r : Representation)
    (hr : r ∈ ambient X) : 0 < index r := by
  have hd := ambient_data X hX r hr
  have hp := hd.2.2.1
  have h1 := hd.2.2.2.2.1
  have h2 := hd.2.2.2.2.2.1
  have h3 := hd.2.2.2.2.2.2
  rw [← rebuild_drop r hd.1]
  simp only [rebuild,index,List.prod_cons,List.prod_nil,mul_one]
  positivity

run_cmd do
  for decl in [``largePrimes_card_le, ``ambient_card_le, ``ambient_index_pos] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end OuterAmbientSizeWork
