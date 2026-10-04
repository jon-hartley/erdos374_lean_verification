import SieveSelectedWindow
import SieveRosser

/-! Sign-sensitive finite comparison before divisor coefficients are collected.
Outer tuples retain literal product divisibility, including repetitions. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open scoped BigOperators

namespace SieveSignedComparison

def subsetTerm (s : Finset ℕ) (n : ℕ) : ℝ :=
  if SievePrimeSubset.subsetProduct s ∣ n then 1 else 0

def tupleTerm (ps : List ℕ) (n : ℕ) : ℝ := if ps.prod ∣ n then 1 else 0

def evenPart (A : Finset (Finset ℕ)) : Finset (Finset ℕ) :=
  A.filter (fun s => Even s.card)

def oddPart (A : Finset (Finset ℕ)) : Finset (Finset ℕ) :=
  A.filter (fun s => ¬Even s.card)

def tupleCount (T : Finset (List ℕ)) (n : ℕ) : ℝ := ∑ ps ∈ T, tupleTerm ps n

theorem subsetTerm_nonneg (s : Finset ℕ) (n : ℕ) : 0 ≤ subsetTerm s n := by
  unfold subsetTerm
  split_ifs <;> norm_num

theorem tupleTerm_nonneg (ps : List ℕ) (n : ℕ) : 0 ≤ tupleTerm ps n := by
  unfold tupleTerm
  split_ifs <;> norm_num

theorem tupleCount_nonneg (T : Finset (List ℕ)) (n : ℕ) : 0 ≤ tupleCount T n :=
  Finset.sum_nonneg (fun ps _ => tupleTerm_nonneg ps n)

theorem tupleTerm_toFinset (ps : List ℕ) (hps : ps.Nodup) (n : ℕ) :
    tupleTerm ps n = subsetTerm ps.toFinset n := by
  have hp : SievePrimeSubset.subsetProduct ps.toFinset = ps.prod := by
    simpa only [SievePrimeSubset.subsetProduct, List.map_id'] using
      List.prod_toFinset (fun p : ℕ => p) hps
  simp only [tupleTerm, subsetTerm, hp]

theorem signed_sum_split (A : Finset (Finset ℕ)) (n : ℕ) :
    (∑ s ∈ A, (-1 : ℝ)^s.card * subsetTerm s n) =
      (∑ s ∈ evenPart A, subsetTerm s n) - ∑ s ∈ oddPart A, subsetTerm s n := by
  classical
  simp only [evenPart, oddPart, Finset.sum_filter, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro s _
  rw [neg_one_pow_eq_ite]
  split_ifs <;> ring

theorem selected_split_le_indicator (gate : ℕ → ℕ → Prop) (d : ℕ)
    (ps : List ℕ) (hnd : ps.Nodup) (hp : ∀ p ∈ ps, p.Prime) (n : ℕ) :
    (∑ s ∈ evenPart (SievePrefix.selected gate false d ps), subsetTerm s n) -
      (∑ s ∈ oddPart (SievePrefix.selected gate false d ps), subsetTerm s n) ≤
        SieveDivisorWindow.indicator ps.toFinset n := by
  rw [← signed_sum_split]
  have hb := (SieveSelectedWindow.evaluation_bounds gate d ps hnd hp n).1
  change (∑ m ∈ SievePrimeSubset.selectedSupport _, if m ∣ n then
    SievePrimeSubset.selectedCoefficient _ m else 0) ≤ _ at hb
  rw [SievePrimeSubset.sum_selectedCoefficient_dvd] at hb
  simpa only [subsetTerm, mul_ite, mul_one, mul_zero] using hb

theorem sum_le_of_injection {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : Finset α) (B : Finset β) (f : α → β) (a : α → ℝ) (b : β → ℝ)
    (hmem : ∀ x ∈ A, f x ∈ B) (hinj : Set.InjOn f (↑A : Set α))
    (heq : ∀ x ∈ A, a x = b (f x)) (hb : ∀ y ∈ B, 0 ≤ b y) :
    ∑ x ∈ A, a x ≤ ∑ y ∈ B, b y := by
  classical
  calc
    _ = ∑ x ∈ A, b (f x) := Finset.sum_congr rfl heq
    _ = ∑ y ∈ A.image f, b y := (Finset.sum_image hinj).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
      (by intro y hy; obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy; exact hmem x hx)
      (fun y hy _ => hb y hy)

/-- The hypotheses are finite injection/coverage obligations; the following
module constructs them from the actual grid. No pointwise sieve bound is assumed. -/
theorem tuple_comparison (gate : ℕ → ℕ → Prop) (d : ℕ) (ps : List ℕ)
    (hnd : ps.Nodup) (hp : ∀ p ∈ ps, p.Prime)
    (I O : Finset (List ℕ)) (f : Finset ℕ → List ℕ)
    (hI : ∀ t ∈ I, t.toFinset ∈ evenPart (SievePrefix.selected gate false d ps))
    (hIN : ∀ t ∈ I, t.Nodup) (hII : Set.InjOn List.toFinset (↑I : Set (List ℕ)))
    (hO : ∀ s ∈ oddPart (SievePrefix.selected gate false d ps), f s ∈ O)
    (hOI : Set.InjOn f (↑(oddPart (SievePrefix.selected gate false d ps)) : Set (Finset ℕ)))
    (hOP : ∀ s ∈ oddPart (SievePrefix.selected gate false d ps),
      (f s).prod = SievePrimeSubset.subsetProduct s) (n : ℕ) :
    tupleCount I n - tupleCount O n ≤ SieveDivisorWindow.indicator ps.toFinset n := by
  have hi := sum_le_of_injection I _ List.toFinset (fun t => tupleTerm t n)
    (fun s => subsetTerm s n) hI hII
    (fun t ht => tupleTerm_toFinset t (hIN t ht) n)
    (fun s _ => subsetTerm_nonneg s n)
  have ho := sum_le_of_injection _ O f (fun s => subsetTerm s n)
    (fun t => tupleTerm t n) hO hOI
    (fun s hs => by simp only [subsetTerm, tupleTerm, hOP s hs])
    (fun t _ => tupleTerm_nonneg t n)
  exact (sub_le_sub hi ho).trans (selected_split_le_indicator gate d ps hnd hp n)

theorem bracket_mul (P N L U A B : ℝ) (hP : 0 ≤ P) (hN : 0 ≤ N)
    (hA : 0 ≤ A) (hL : L ≤ A) (hU : A ≤ U) (hPN : P-N ≤ B) :
    L*P-U*N ≤ A*B := by
  have hLP := mul_le_mul_of_nonneg_right hL hP
  have hUN := mul_le_mul_of_nonneg_right hU hN
  have hAB := mul_le_mul_of_nonneg_left hPN hA
  nlinarith

#print axioms tuple_comparison
run_cmd do
  for decl in [``subsetTerm_nonneg, ``tupleTerm_nonneg, ``tupleCount_nonneg,
      ``tupleTerm_toFinset, ``signed_sum_split, ``selected_split_le_indicator,
      ``sum_le_of_injection, ``tuple_comparison, ``bracket_mul] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end SieveSignedComparison
end
