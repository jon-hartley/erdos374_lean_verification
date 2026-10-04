import SieveUpperBoxFamily
import SieveUpperBoxLength
import SieveCompleteBoxing

/-! Complete finite upper boxing with the actual small-prime brackets.
This is a pointwise finite theorem, without an analytic main-term bound. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace SieveUpperBoxing
open SieveUpperBoxFamily SieveSignedComparison
open SieveBoxedFamily (pool primes scales boundedTuples mem_pool mem_boundedTuples)

def innerFamily (D s z : ℝ) : Finset (List ℕ) := inner D s z (SieveBoxLength.cutoff s)
def outerFamily (D s z : ℝ) : Finset (List ℕ) := outer D s z (SieveBoxLength.cutoff s)

theorem innerTest_length_bound (D s : ℝ) (hD : 1 < D) (hs : 0 < s)
    (t : List ℕ) (ht : innerTest D s t) : t.length ≤ SieveBoxLength.cutoff s := by
  simpa only [scales, List.length_map] using
    SieveUpperBoxLength.inner_length_le_cutoff D s (SieveGeometricGrid.ratio s)
      (scales D s t) hD hs (SieveGeometricGrid.one_lt_ratio s hs).le
      (SieveCompleteBoxing.scales_ge_initial D s hD hs t) ht.2.2

theorem outerTest_length_bound (D s : ℝ) (hD : 1 < D) (hs : 0 < s)
    (t : List ℕ) (ht : outerTest D s t) : t.length ≤ SieveBoxLength.cutoff s := by
  simpa only [scales, List.length_map] using
    SieveUpperBoxLength.upper_length_le_cutoff D s (scales D s t) hD hs
      (SieveCompleteBoxing.scales_ge_initial D s hD hs t) ht.2.2

theorem mem_innerFamily (D s z : ℝ) (hD : 1 < D) (hs : 0 < s) (t : List ℕ) :
    t ∈ innerFamily D s z ↔ (∀ p ∈ t, p ∈ pool D s z) ∧ innerTest D s t := by
  change t ∈ (boundedTuples _ _).filter _ ↔ _
  rw [Finset.mem_filter, mem_boundedTuples]
  constructor
  · rintro ⟨⟨_, hp⟩, ht⟩
    exact ⟨hp, ht⟩
  · rintro ⟨hp, ht⟩
    exact ⟨⟨innerTest_length_bound D s hD hs t ht, hp⟩, ht⟩

theorem mem_outerFamily (D s z : ℝ) (hD : 1 < D) (hs : 0 < s) (t : List ℕ) :
    t ∈ outerFamily D s z ↔ (∀ p ∈ t, p ∈ pool D s z) ∧ outerTest D s t := by
  change t ∈ (boundedTuples _ _).filter _ ↔ _
  rw [Finset.mem_filter, mem_boundedTuples]
  constructor
  · rintro ⟨⟨_, hp⟩, ht⟩
    exact ⟨hp, ht⟩
  · rintro ⟨hp, ht⟩
    exact ⟨⟨outerTest_length_bound D s hD hs t ht, hp⟩, ht⟩

theorem large_comparison (D s z : ℝ) (hD : 1 < D) (hs : 0 < s)
    (hz : z ≤ D) (n : ℕ) :
    SieveDivisorWindow.indicator (pool D s z) n ≤
      tupleCount (outerFamily D s z) n-tupleCount (innerFamily D s z) n := by
  apply comparison D s z _ hD hs hz _ n
  intro A hA
  apply SieveUpperBoxLength.selected_card_le_cutoff D s (primes D s z) A hD hs _ hA
  intro p hp
  exact ((mem_pool D s z p).mp ((SieveBoxTuples.mem_descending _ p).mp hp)).2.2

def upperEvaluation (D s z : ℝ) (n : ℕ) : ℝ :=
  SieveCompleteBoxing.smallEvaluation D s true n * tupleCount (outerFamily D s z) n -
    SieveCompleteBoxing.smallEvaluation D s false n * tupleCount (innerFamily D s z) n

/-- The lower small-prime bracket is allowed to be negative. Its coefficient
is replaced only after multiplying the nonnegative inner tuple count. -/
theorem indicator_le_upperEvaluation (D s z : ℝ) (hD : 1 < D) (hs : 0 < s)
    (hz : z ≤ D) (huz : D^(s^2) ≤ z) (n : ℕ) :
    SieveDivisorWindow.indicator (SieveSmallWeights.pool z) n ≤
      upperEvaluation D s z n := by
  rw [← SieveCompleteBoxing.pools_union D s z huz, SieveVector.indicator_union]
  exact SieveUpperBoxComparison.bracket_mul _ _ _ _ _ _
    (tupleCount_nonneg _ _) (tupleCount_nonneg _ _)
    (SieveVector.indicator_nonneg _ _) (SieveCompleteBoxing.smallEvaluation_bounds D s n).1
    (SieveCompleteBoxing.smallEvaluation_bounds D s n).2 (large_comparison D s z hD hs hz n)

theorem window_upper_bound (D s z : ℝ) (hD : 1 < D) (hs : 0 < s)
    (hz : z ≤ D) (huz : D^(s^2) ≤ z) (L R : ℝ) :
    ((SieveDivisorWindow.siftedWindow (SieveSmallWeights.pool z) L R).card : ℝ) ≤
      ∑ n ∈ FiniteSieveWindow.window L R, upperEvaluation D s z n := by
  rw [← SieveDivisorWindow.sum_indicator_eq_card]
  exact Finset.sum_le_sum (fun n _ => indicator_le_upperEvaluation D s z hD hs hz huz n)

theorem initial_term_included (D s z : ℝ) (n : ℕ) :
    tupleCount (outerFamily D s z) n =
      1+tupleCount ((outerFamily D s z).erase []) n := by
  have h := Finset.sum_erase_add (outerFamily D s z) (fun t => tupleTerm t n)
    (empty_mem_outer D s z (SieveBoxLength.cutoff s))
  have he : tupleTerm [] n = 1 := by simp [tupleTerm]
  unfold tupleCount
  rw [he] at h
  linarith

run_cmd do
  for decl in [``innerTest_length_bound, ``outerTest_length_bound, ``mem_innerFamily,
      ``mem_outerFamily, ``large_comparison, ``indicator_le_upperEvaluation,
      ``window_upper_bound, ``initial_term_included] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "COMPLETE ACTUAL UPPER BOX POINTWISE BOUND; ANALYTIC ESTIMATES OPEN"
end SieveUpperBoxing
end
