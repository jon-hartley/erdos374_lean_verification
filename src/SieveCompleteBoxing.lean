import SieveBoxedFamily
import SieveBoxLength

/-! Complete finite sign-sensitive boxing, including every admissible length.
The actual small-prime brackets are substituted only after multiplication by
their nonnegative sifted indicator. No main-term positivity is asserted. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace SieveCompleteBoxing
open SieveBoxedFamily SieveSignedComparison

def innerFamily (D s z : ℝ) : Finset (List ℕ) := inner D s z (SieveBoxLength.cutoff s)
def outerFamily (D s z : ℝ) : Finset (List ℕ) := outer D s z (SieveBoxLength.cutoff s)

theorem coordinate_ge_initial (D s : ℝ) (hD : 1 < D) (hs : 0 < s) (p : ℕ) :
    D^(s^2) ≤ coordinate D s p := by
  have h := (SieveGeometricGrid.scale_strictMono D s hD hs).monotone
    (Nat.zero_le (SieveBoxTuples.boxIndex D s (p : ℝ)))
  simpa only [SieveGeometricGrid.scale_zero, coordinate] using h

theorem scales_ge_initial (D s : ℝ) (hD : 1 < D) (hs : 0 < s) (t : List ℕ) :
    ∀ x ∈ scales D s t, D^(s^2) ≤ x := by
  intro x hx
  obtain ⟨p, _, rfl⟩ := List.mem_map.mp hx
  exact coordinate_ge_initial D s hD hs p

theorem innerTest_length_bound (D s : ℝ) (hD : 1 < D) (hs : 0 < s)
    (t : List ℕ) (ht : innerTest D s t) : t.length ≤ SieveBoxLength.cutoff s := by
  simpa only [scales, List.length_map] using
    SieveBoxLength.inner_length_le_cutoff D s (SieveGeometricGrid.ratio s) (scales D s t)
      hD hs (SieveGeometricGrid.one_lt_ratio s hs).le (scales_ge_initial D s hD hs t) ht.2.2

theorem outerTest_length_bound (D s : ℝ) (hD : 1 < D) (hs : 0 < s)
    (t : List ℕ) (ht : outerTest D s t) : t.length ≤ SieveBoxLength.cutoff s := by
  simpa only [scales, List.length_map] using SieveBoxLength.lower_length_le_cutoff D s
    (scales D s t) hD hs (scales_ge_initial D s hD hs t) ht.2.2

/-- No admissible positive tuple is lost to the finite length cutoff. -/
theorem mem_innerFamily (D s z : ℝ) (hD : 1 < D) (hs : 0 < s) (t : List ℕ) :
    t ∈ innerFamily D s z ↔ (∀ p ∈ t, p ∈ pool D s z) ∧ innerTest D s t := by
  change t ∈ (boundedTuples _ _).filter _ ↔ _
  rw [Finset.mem_filter, mem_boundedTuples]
  constructor
  · rintro ⟨⟨_, hp⟩, ht⟩
    exact ⟨hp, ht⟩
  · rintro ⟨hp, ht⟩
    exact ⟨⟨innerTest_length_bound D s hD hs t ht, hp⟩, ht⟩

/-- Includes repeated prime coordinates whenever the outer tests admit them. -/
theorem mem_outerFamily (D s z : ℝ) (hD : 1 < D) (hs : 0 < s) (t : List ℕ) :
    t ∈ outerFamily D s z ↔ (∀ p ∈ t, p ∈ pool D s z) ∧ outerTest D s t := by
  change t ∈ (boundedTuples _ _).filter _ ↔ _
  rw [Finset.mem_filter, mem_boundedTuples]
  constructor
  · rintro ⟨⟨_, hp⟩, ht⟩
    exact ⟨hp, ht⟩
  · rintro ⟨hp, ht⟩
    exact ⟨⟨outerTest_length_bound D s hD hs t ht, hp⟩, ht⟩

theorem assigned_indices_bounded (D s z : ℝ) (hD : 1 < D) (hs : 0 < s)
    (hz : z ≤ D) (t : List ℕ) (ht : ∀ p ∈ t, p ∈ pool D s z) :
    ∀ i ∈ indices D s t, i ≤ SieveGeometricGrid.cutoff s := by
  intro i hi
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hi
  have hr := range_of_pool D s z hz t ht p hp
  exact SieveBoxTuples.boxIndex_le_cutoff D s (p : ℝ) hD hs hr.1 hr.2

theorem large_comparison (D s z : ℝ) (hD : 1 < D) (hs : 0 < s)
    (hz : z ≤ D) (n : ℕ) :
    tupleCount (innerFamily D s z) n - tupleCount (outerFamily D s z) n ≤
      SieveDivisorWindow.indicator (pool D s z) n := by
  apply comparison D s z _ hD hs hz _ n
  intro A hA
  apply SieveBoxLength.selected_card_le_cutoff D s (primes D s z) A hD hs _ hA
  intro p hp
  exact ((mem_pool D s z p).mp ((SieveBoxTuples.mem_descending _ p).mp hp)).2.2

def smallEvaluation (D s : ℝ) (upper : Bool) (n : ℕ) : ℝ :=
  SieveVector.selectedEvaluation (SieveRosser.cubicGate (D^s)) upper 1
    (SieveSmallWeights.primes (D^(s^2))) n

def lowerEvaluation (D s z : ℝ) (n : ℕ) : ℝ :=
  smallEvaluation D s false n * tupleCount (innerFamily D s z) n -
    smallEvaluation D s true n * tupleCount (outerFamily D s z) n

theorem smallEvaluation_bounds (D s : ℝ) (n : ℕ) :
    smallEvaluation D s false n ≤ SieveDivisorWindow.indicator (SieveSmallWeights.pool (D^(s^2))) n ∧
    SieveDivisorWindow.indicator (SieveSmallWeights.pool (D^(s^2))) n ≤ smallEvaluation D s true n := by
  have h := SieveSelectedWindow.evaluation_bounds (SieveRosser.cubicGate (D^s)) 1
    (SieveSmallWeights.primes (D^(s^2))) (SieveSmallWeights.primes_nodup _)
    (SieveSmallWeights.primes_prime _) n
  simpa only [SieveSmallWeights.primes_toFinset, smallEvaluation,
    SieveVector.selectedEvaluation] using h

theorem pools_union (D s z : ℝ) (huz : D^(s^2) ≤ z) :
    SieveSmallWeights.pool (D^(s^2)) ∪ pool D s z = SieveSmallWeights.pool z := by
  ext p
  simp only [Finset.mem_union, SieveSmallWeights.mem_pool, mem_pool]
  constructor
  · rintro (⟨hp, hpu⟩ | ⟨hp, hpz, _⟩)
    · exact ⟨hp, hpu.trans_le huz⟩
    · exact ⟨hp, hpz⟩
  · rintro ⟨hp, hpz⟩
    by_cases hpu : (p : ℝ) < D^(s^2)
    · exact Or.inl ⟨hp, hpu⟩
    · exact Or.inr ⟨hp, hpz, le_of_not_gt hpu⟩

/-- The full constructed finite lower sieve. Lower small weights need not be
nonnegative, and repeated outer coordinates use literal product divisibility. -/
theorem lowerEvaluation_le_indicator (D s z : ℝ) (hD : 1 < D) (hs : 0 < s)
    (hz : z ≤ D) (huz : D^(s^2) ≤ z) (n : ℕ) :
    lowerEvaluation D s z n ≤ SieveDivisorWindow.indicator (SieveSmallWeights.pool z) n := by
  rw [← pools_union D s z huz, SieveVector.indicator_union]
  exact bracket_mul _ _ _ _ _ _ (tupleCount_nonneg _ _) (tupleCount_nonneg _ _)
    (SieveVector.indicator_nonneg _ _) (smallEvaluation_bounds D s n).1
    (smallEvaluation_bounds D s n).2 (large_comparison D s z hD hs hz n)

theorem window_lower_bound (D s z : ℝ) (hD : 1 < D) (hs : 0 < s)
    (hz : z ≤ D) (huz : D^(s^2) ≤ z) (L R : ℝ) :
    (∑ n ∈ FiniteSieveWindow.window L R, lowerEvaluation D s z n) ≤
      ((SieveDivisorWindow.siftedWindow (SieveSmallWeights.pool z) L R).card : ℝ) := by
  rw [← SieveDivisorWindow.sum_indicator_eq_card]
  exact Finset.sum_le_sum (fun n _ => lowerEvaluation_le_indicator D s z hD hs hz huz n)

theorem initial_term_included (D s z : ℝ) (n : ℕ) :
    tupleCount (innerFamily D s z) n =
      1 + tupleCount ((innerFamily D s z).erase []) n := by
  have h := Finset.sum_erase_add (innerFamily D s z) (fun t => tupleTerm t n)
    (empty_mem_inner D s z (SieveBoxLength.cutoff s))
  have he : tupleTerm [] n = 1 := by simp [tupleTerm]
  unfold tupleCount
  rw [he] at h
  linarith

#print axioms lowerEvaluation_le_indicator
#print axioms window_lower_bound
run_cmd do
  for decl in [``coordinate_ge_initial, ``scales_ge_initial, ``innerTest_length_bound,
    ``outerTest_length_bound, ``mem_innerFamily, ``mem_outerFamily, ``assigned_indices_bounded,
    ``large_comparison, ``smallEvaluation_bounds, ``pools_union,
    ``lowerEvaluation_le_indicator, ``window_lower_bound, ``initial_term_included] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
run_cmd Lean.logInfo "COMPLETE FINITE SIGNED BOXING PASSED; MAIN TERM POSITIVITY OPEN"
end SieveCompleteBoxing
end
