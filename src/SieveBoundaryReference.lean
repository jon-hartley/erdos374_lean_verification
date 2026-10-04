import SieveNormalizedCollisions

/-! The exact finite reference comparison for the two cubic strip errors.
The stronger positive inner level is preserved, and every discrepancy is
defined as a difference of actual finite tuple families. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace SieveBoundaryReference
open SieveBoxedFamily SieveCompleteBoxing SieveStoppingExpansion

def referenceTest (positive : Bool) (D s : ℝ) (t : List ℕ) : Prop :=
  (if positive then Even t.length else ¬Even t.length) ∧
    (indices D s t).Pairwise (· > ·) ∧
    SievePrefix.accepts (SieveRosser.cubicGate D) false 1 t

def reference (positive : Bool) (D s z : ℝ) : Finset (List ℕ) :=
  (boundedTuples (pool D s z) (SieveBoxLength.cutoff s)).filter (referenceTest positive D s)

abbrev refEven (D s z : ℝ) := reference true D s z
abbrev refOdd (D s z : ℝ) := reference false D s z

def outerDistinct (D s z : ℝ) : Finset (List ℕ) :=
  (outerFamily D s z).filter (fun t => (indices D s t).Nodup)

def innerOmissions (D s z : ℝ) : Finset (List ℕ) := refEven D s z \ innerFamily D s z
def outerExcess (D s z : ℝ) : Finset (List ℕ) := outerDistinct D s z \ refOdd D s z
def tupleMass (F : Finset (List ℕ)) : ℝ := ∑ t ∈ F, SieveBoxMass.reciprocal t
def referenceDistinct (D s z : ℝ) : ℝ :=
  primeEuler (D^(s^2))*(tupleMass (refEven D s z)-tupleMass (refOdd D s z))

theorem mem_reference (positive : Bool) (D s z : ℝ) (t : List ℕ) :
    t ∈ reference positive D s z ↔
      t.length ≤ SieveBoxLength.cutoff s ∧ (∀ p ∈ t, p ∈ pool D s z) ∧
        referenceTest positive D s t := by
  simp only [reference, Finset.mem_filter, mem_boundedTuples, and_assoc]

theorem mem_refEven (D s z : ℝ) (t : List ℕ) :
    t ∈ refEven D s z ↔
      t.length ≤ SieveBoxLength.cutoff s ∧ (∀ p ∈ t, p ∈ pool D s z) ∧
        Even t.length ∧ (indices D s t).Pairwise (· > ·) ∧
          SievePrefix.accepts (SieveRosser.cubicGate D) false 1 t := by
  simp only [refEven, mem_reference, referenceTest, ite_true]

theorem mem_refOdd (D s z : ℝ) (t : List ℕ) :
    t ∈ refOdd D s z ↔
      t.length ≤ SieveBoxLength.cutoff s ∧ (∀ p ∈ t, p ∈ pool D s z) ∧
        ¬Even t.length ∧ (indices D s t).Pairwise (· > ·) ∧
          SievePrefix.accepts (SieveRosser.cubicGate D) false 1 t := by
  simp only [refOdd, mem_reference, referenceTest, Bool.false_eq_true, ite_false]

theorem inner_subset_refEven (D s z : ℝ) (hD : 1 < D) (hs : 0 < s) (hz : z ≤ D) :
    innerFamily D s z ⊆ refEven D s z := by
  intro t ht
  obtain ⟨hb, he, hi, _⟩ := Finset.mem_filter.mp ht
  obtain ⟨hlen, hp⟩ := (mem_boundedTuples _ _ _).mp hb
  exact (mem_refEven D s z t).mpr ⟨hlen, hp, he, hi,
    SieveBoxedFamily.inner_accepts D s z _ hD hs hz t ht⟩

theorem refOdd_subset_outerDistinct (D s z : ℝ)
    (hD : 1 < D) (hs : 0 < s) (hz : z ≤ D) :
    refOdd D s z ⊆ outerDistinct D s z := by
  intro t ht
  obtain ⟨hlen, hp, hodd, hi, ha⟩ := (mem_refOdd D s z t).mp ht
  apply Finset.mem_filter.mpr
  refine ⟨?_, hi.imp (fun h => ne_of_gt h)⟩
  apply Finset.mem_filter.mpr
  refine ⟨(mem_boundedTuples _ _ _).mpr ⟨hlen, hp⟩,
    hodd, hi.imp (fun h => h.le), ?_⟩
  apply SieveBoxPrefix.outer_accepts_map D false (coordinate D s) t ?_ ha
  intro p hpt
  have hh := coordinate_bounds D s z hD hs hz p (hp p hpt)
  exact ⟨hh.1, hh.2.1⟩

/-- Weak descending indices plus no repeats give strict descending indices. -/
theorem outerDistinct_indices_strict (D s z : ℝ) (t : List ℕ)
    (ht : t ∈ outerDistinct D s z) : (indices D s t).Pairwise (· > ·) := by
  obtain ⟨ho, hn⟩ := Finset.mem_filter.mp ht
  obtain ⟨_, htest⟩ := Finset.mem_filter.mp ho
  exact (htest.2.1.and hn).imp (fun h => by omega)

theorem outerDistinct_eq_filter_strict (D s z : ℝ) :
    outerDistinct D s z = (outerFamily D s z).filter
      (fun t => (indices D s t).Pairwise (· > ·)) := by
  ext t
  constructor
  · intro ht
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp ht).1,
      outerDistinct_indices_strict D s z t ht⟩
  · intro ht
    obtain ⟨ho, hi⟩ := Finset.mem_filter.mp ht
    exact Finset.mem_filter.mpr ⟨ho, hi.imp (fun h => ne_of_gt h)⟩

theorem reference_strict (positive : Bool) (D s z : ℝ) (hD : 1 < D)
    (hs : 0 < s) (hz : z ≤ D) (t : List ℕ) (ht : t ∈ reference positive D s z) :
    t.Pairwise (· > ·) := by
  obtain ⟨_, hp, ht⟩ := (mem_reference positive D s z t).mp ht
  exact SieveBoxTuples.strict_box_indices_values D s hD hs t
    (range_of_pool D s z hz t hp) ht.2.1

theorem outerDistinct_strict (D s z : ℝ) (hD : 1 < D)
    (hs : 0 < s) (hz : z ≤ D) (t : List ℕ) (ht : t ∈ outerDistinct D s z) :
    t.Pairwise (· > ·) := by
  have ho := (Finset.mem_filter.mp ht).1
  have hp := ((mem_boundedTuples _ _ _).mp (Finset.mem_filter.mp ho).1).2
  exact SieveBoxTuples.strict_box_indices_values D s hD hs t
    (range_of_pool D s z hz t hp) (outerDistinct_indices_strict D s z t ht)

theorem innerOmissions_properties (D s z : ℝ) (t : List ℕ)
    (ht : t ∈ innerOmissions D s z) :
    (∀ p ∈ t, p ∈ pool D s z) ∧ Even t.length ∧
      (indices D s t).Pairwise (· > ·) ∧
      SievePrefix.accepts (SieveRosser.cubicGate D) false 1 t ∧ ¬innerTest D s t := by
  obtain ⟨hr, hn⟩ := Finset.mem_sdiff.mp ht
  obtain ⟨hl, hp, he, hi, ha⟩ := (mem_refEven D s z t).mp hr
  refine ⟨hp, he, hi, ha, ?_⟩
  intro htst
  exact hn (Finset.mem_filter.mpr ⟨(mem_boundedTuples _ _ _).mpr ⟨hl, hp⟩, htst⟩)

theorem outerExcess_properties (D s z : ℝ) (t : List ℕ)
    (ht : t ∈ outerExcess D s z) :
    (∀ p ∈ t, p ∈ pool D s z) ∧ outerTest D s t ∧
      (indices D s t).Pairwise (· > ·) ∧
      ¬SievePrefix.accepts (SieveRosser.cubicGate D) false 1 t := by
  obtain ⟨ho, hn⟩ := Finset.mem_sdiff.mp ht
  have hos := (Finset.mem_filter.mp ho).1
  obtain ⟨hb, htest⟩ := Finset.mem_filter.mp hos
  obtain ⟨hl, hp⟩ := (mem_boundedTuples _ _ _).mp hb
  have hi := outerDistinct_indices_strict D s z t ho
  refine ⟨hp, htest, hi, ?_⟩
  intro ha
  exact hn ((mem_refOdd D s z t).mpr ⟨hl, hp, htest.1, hi, ha⟩)

theorem tupleMass_nonneg (F : Finset (List ℕ)) : 0 ≤ tupleMass F :=
  Finset.sum_nonneg (fun t _ => inv_nonneg.mpr (Nat.cast_nonneg t.prod))

theorem innerOmissions_mass (D s z : ℝ) (hD : 1 < D) (hs : 0 < s) (hz : z ≤ D) :
    tupleMass (innerOmissions D s z) =
      tupleMass (refEven D s z) - SieveBoxMass.mass true D s z := by
  exact Finset.sum_sdiff_eq_sub (inner_subset_refEven D s z hD hs hz)

theorem outerExcess_mass (D s z : ℝ) (hD : 1 < D) (hs : 0 < s) (hz : z ≤ D) :
    tupleMass (outerExcess D s z) =
      SieveNormalizedCollisions.distinctMass false D s z - tupleMass (refOdd D s z) := by
  exact Finset.sum_sdiff_eq_sub (refOdd_subset_outerDistinct D s z hD hs hz)

/-- Both discrepancies reduce the actual strict ideal, with the stronger
inner cutoff retained literally in innerFamily. -/
theorem referenceDistinct_sub_strictIdeal (D s z : ℝ)
    (hD : 1 < D) (hs : 0 < s) (hz : z ≤ D) :
    referenceDistinct D s z - SieveNormalizedCollisions.strictIdeal D s z =
      primeEuler (D^(s^2)) *
        (tupleMass (innerOmissions D s z) + tupleMass (outerExcess D s z)) := by
  rw [innerOmissions_mass D s z hD hs hz, outerExcess_mass D s z hD hs hz]
  unfold referenceDistinct SieveNormalizedCollisions.strictIdeal
  ring

theorem referenceDistinct_gap_nonneg (D s z : ℝ)
    (hD : 1 < D) (hs : 0 < s) (hz : z ≤ D) :
    0 ≤ referenceDistinct D s z - SieveNormalizedCollisions.strictIdeal D s z := by
  rw [referenceDistinct_sub_strictIdeal D s z hD hs hz]
  exact mul_nonneg (SieveEulerRatio.euler_pos _).le
    (add_nonneg (tupleMass_nonneg _) (tupleMass_nonneg _))

run_cmd do
  for decl in [``mem_reference, ``mem_refEven, ``mem_refOdd, ``inner_subset_refEven,
    ``refOdd_subset_outerDistinct, ``outerDistinct_indices_strict,
    ``outerDistinct_eq_filter_strict, ``reference_strict, ``outerDistinct_strict,
    ``innerOmissions_properties, ``outerExcess_properties, ``tupleMass_nonneg,
    ``innerOmissions_mass, ``outerExcess_mass, ``referenceDistinct_sub_strictIdeal,
    ``referenceDistinct_gap_nonneg] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "EXACT REFERENCE MINUS STRICT IDEAL IS THE POSITIVE TWO-STRIP MASS"

end SieveBoundaryReference
end
