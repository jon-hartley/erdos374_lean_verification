import SieveSignedComparison

/-! Finite sign-sensitive upper boxing. Positive even terms are enlarged;
negative odd terms are restricted. Tuple multiplicities are retained. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open scoped BigOperators
namespace SieveUpperBoxComparison
open SieveSignedComparison

theorem indicator_le_selected_split (gate : ℕ → ℕ → Prop) (d : ℕ)
    (ps : List ℕ) (hnd : ps.Nodup) (hp : ∀ p ∈ ps, p.Prime) (n : ℕ) :
    SieveDivisorWindow.indicator ps.toFinset n ≤
      (∑ s ∈ evenPart (SievePrefix.selected gate true d ps), subsetTerm s n) -
        ∑ s ∈ oddPart (SievePrefix.selected gate true d ps), subsetTerm s n := by
  rw [← signed_sum_split]
  have hb := (SieveSelectedWindow.evaluation_bounds gate d ps hnd hp n).2
  change _ ≤ (∑ m ∈ SievePrimeSubset.selectedSupport _, if m ∣ n then
    SievePrimeSubset.selectedCoefficient _ m else 0) at hb
  rw [SievePrimeSubset.sum_selectedCoefficient_dvd] at hb
  simpa only [subsetTerm, mul_ite, mul_one, mul_zero] using hb

theorem tuple_comparison (gate : ℕ → ℕ → Prop) (d : ℕ) (ps : List ℕ)
    (hnd : ps.Nodup) (hp : ∀ p ∈ ps, p.Prime)
    (I O : Finset (List ℕ)) (f : Finset ℕ → List ℕ)
    (hI : ∀ t ∈ I, t.toFinset ∈ oddPart (SievePrefix.selected gate true d ps))
    (hIN : ∀ t ∈ I, t.Nodup) (hII : Set.InjOn List.toFinset (↑I : Set (List ℕ)))
    (hO : ∀ s ∈ evenPart (SievePrefix.selected gate true d ps), f s ∈ O)
    (hOI : Set.InjOn f (↑(evenPart (SievePrefix.selected gate true d ps)) : Set (Finset ℕ)))
    (hOP : ∀ s ∈ evenPart (SievePrefix.selected gate true d ps),
      (f s).prod = SievePrimeSubset.subsetProduct s) (n : ℕ) :
    SieveDivisorWindow.indicator ps.toFinset n ≤ tupleCount O n-tupleCount I n := by
  have hi := sum_le_of_injection I _ List.toFinset (fun t => tupleTerm t n)
    (fun s => subsetTerm s n) hI hII
    (fun t ht => tupleTerm_toFinset t (hIN t ht) n)
    (fun s _ => subsetTerm_nonneg s n)
  have ho := sum_le_of_injection _ O f (fun s => subsetTerm s n)
    (fun t => tupleTerm t n) hO hOI
    (fun s hs => by simp only [subsetTerm, tupleTerm, hOP s hs])
    (fun t _ => tupleTerm_nonneg t n)
  exact (indicator_le_selected_split gate d ps hnd hp n).trans (sub_le_sub ho hi)

theorem bracket_mul (P N L U A B : ℝ) (hP : 0 ≤ P) (hN : 0 ≤ N)
    (hA : 0 ≤ A) (hL : L ≤ A) (hU : A ≤ U) (hPN : B ≤ P-N) :
    A*B ≤ U*P-L*N := by
  have hUP := mul_le_mul_of_nonneg_right hU hP
  have hLN := mul_le_mul_of_nonneg_right hL hN
  have hAB := mul_le_mul_of_nonneg_left hPN hA
  nlinarith

run_cmd do
  for decl in [``indicator_le_selected_split, ``tuple_comparison, ``bracket_mul] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "FINITE UPPER BOX INJECTION AND BRACKET COMPARISON"
end SieveUpperBoxComparison
end
