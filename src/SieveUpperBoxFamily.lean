import SieveUpperBoxComparison
import SieveBoxedFamily

/-! Actual upper-mode outer-even and inner-odd tuple families on the frozen
half-open geometric grid. Every outer tuple retains literal product divisibility. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace SieveUpperBoxFamily
open SieveBoxTuples SieveSignedComparison SieveBoxedFamily

def innerTest (D s : ℝ) (t : List ℕ) : Prop :=
  ¬Even t.length ∧ (indices D s t).Pairwise (· > ·) ∧
    SieveBoxPrefix.accepts (D^(1/SieveGeometricGrid.ratio s)) true 1 (scales D s t)
def outerTest (D s : ℝ) (t : List ℕ) : Prop :=
  Even t.length ∧ (indices D s t).Pairwise (· ≥ ·) ∧
    SieveBoxPrefix.accepts D true 1 (scales D s t)
def inner (D s z : ℝ) (K : ℕ) : Finset (List ℕ) :=
  (boundedTuples (pool D s z) K).filter (innerTest D s)
def outer (D s z : ℝ) (K : ℕ) : Finset (List ℕ) :=
  (boundedTuples (pool D s z) K).filter (outerTest D s)

theorem inner_strict (D s z : ℝ) (K : ℕ) (hD : 1 < D) (hs : 0 < s)
    (hz : z ≤ D) (t : List ℕ) (ht : t ∈ inner D s z K) : t.Pairwise (· > ·) := by
  obtain ⟨hb, hi⟩ := Finset.mem_filter.mp ht
  exact strict_box_indices_values D s hD hs t
    (range_of_pool D s z hz t ((mem_boundedTuples _ _ _).mp hb).2) hi.2.1

theorem inner_nodup (D s z : ℝ) (K : ℕ) (hD : 1 < D) (hs : 0 < s)
    (hz : z ≤ D) (t : List ℕ) (ht : t ∈ inner D s z K) : t.Nodup :=
  (inner_strict D s z K hD hs hz t ht).imp (fun h => ne_of_gt h)

theorem inner_accepts (D s z : ℝ) (K : ℕ) (hD : 1 < D) (hs : 0 < s)
    (hz : z ≤ D) (t : List ℕ) (ht : t ∈ inner D s z K) :
    SievePrefix.accepts (SieveRosser.cubicGate D) true 1 t := by
  obtain ⟨hb, hi⟩ := Finset.mem_filter.mp ht
  have hp := ((mem_boundedTuples _ _ _).mp hb).2
  apply SieveBoxPrefix.inner_accepts_map D (SieveGeometricGrid.ratio s) true
    (coordinate D s) t (by linarith) (lt_trans zero_lt_one (SieveGeometricGrid.one_lt_ratio s hs))
  · intro p hp'
    have h := coordinate_bounds D s z hD hs hz p (hp p hp')
    exact ⟨h.1, h.2.2.le⟩
  · exact hi.2.2

theorem inner_selected_odd (D s z : ℝ) (K : ℕ) (hD : 1 < D) (hs : 0 < s)
    (hz : z ≤ D) (t : List ℕ) (ht : t ∈ inner D s z K) :
    t.toFinset ∈ oddPart (SieveRosser.selected D true (primes D s z)) := by
  have htn := inner_nodup D s z K hD hs hz t ht
  have hto : t.Pairwise (· ≥ ·) := (inner_strict D s z K hD hs hz t ht).imp (fun h => h.le)
  obtain ⟨hb, hi⟩ := Finset.mem_filter.mp ht
  have hsub : t.toFinset ⊆ (primes D s z).toFinset := by
    rw [primes, descending_toFinset]
    intro p hp
    exact ((mem_boundedTuples _ _ _).mp hb).2 p (List.mem_toFinset.mp hp)
  have htsub : t.Sublist (primes D s z) := by
    rw [← descending_eq_of_sorted t htn hto]
    exact descending_sublist _ _ (descending_nodup _) (descending_pairwise _) hsub
  apply Finset.mem_filter.mpr
  refine ⟨SievePrefix.selected_of_sublist_accepts (SieveRosser.cubicGate D) true 1
    (primes D s z) t htsub (inner_accepts D s z K hD hs hz t ht), ?_⟩
  simpa only [List.toFinset_card_of_nodup htn] using hi.1

theorem inner_toFinset_injective (D s z : ℝ) (K : ℕ) (hD : 1 < D)
    (hs : 0 < s) (hz : z ≤ D) : Set.InjOn List.toFinset (↑(inner D s z K) : Set (List ℕ)) := by
  intro t ht v hv he
  exact toFinset_injective_on_sorted t v
    (inner_nodup D s z K hD hs hz t ht) (inner_nodup D s z K hD hs hz v hv)
    ((inner_strict D s z K hD hs hz t ht).imp (fun h => h.le))
    ((inner_strict D s z K hD hs hz v hv).imp (fun h => h.le)) he

theorem selected_even_to_outer (D s z : ℝ) (K : ℕ) (hD : 1 < D) (hs : 0 < s)
    (hz : z ≤ D) (A : Finset ℕ)
    (hA : A ∈ evenPart (SieveRosser.selected D true (primes D s z))) (hK : A.card ≤ K) :
    descending A ∈ outer D s z K := by
  obtain ⟨hsel, hodd⟩ := Finset.mem_filter.mp hA
  have hsub : A ⊆ pool D s z := by
    simpa only [primes, descending_toFinset] using
      SieveRosser.selected_subset D true (primes D s z) A hsel
  have hp : ∀ p ∈ descending A, p ∈ pool D s z := fun p h => hsub ((mem_descending A p).mp h)
  have ha := descending_selected_accepts (SieveRosser.cubicGate D) true 1
    (primes D s z) (descending_nodup _) (descending_pairwise _) A hsel
  apply Finset.mem_filter.mpr
  refine ⟨(mem_boundedTuples _ _ _).mpr ⟨by simpa only [descending_length] using hK, hp⟩, ?_⟩
  refine ⟨by simpa only [descending_length] using hodd,
    descending_box_indices D s hD hs (descending A) (descending_pairwise A)
      (range_of_pool D s z hz _ hp), ?_⟩
  apply SieveBoxPrefix.outer_accepts_map D true (coordinate D s) (descending A) _ ha
  intro p hp'
  have h := coordinate_bounds D s z hD hs hz p (hp p hp')
  exact ⟨h.1, h.2.1⟩

theorem comparison (D s z : ℝ) (K : ℕ) (hD : 1 < D) (hs : 0 < s) (hz : z ≤ D)
    (hcap : ∀ A ∈ SieveRosser.selected D true (primes D s z), A.card ≤ K) (n : ℕ) :
    SieveDivisorWindow.indicator (pool D s z) n ≤
      tupleCount (outer D s z K) n-tupleCount (inner D s z K) n := by
  have hh := SieveUpperBoxComparison.tuple_comparison (SieveRosser.cubicGate D) 1
    (primes D s z) (descending_nodup _)
    (fun p hp => ((mem_pool D s z p).mp ((mem_descending _ p).mp hp)).1)
    (inner D s z K) (outer D s z K) descending
    (inner_selected_odd D s z K hD hs hz) (inner_nodup D s z K hD hs hz)
    (inner_toFinset_injective D s z K hD hs hz)
    (fun A hA => selected_even_to_outer D s z K hD hs hz A hA
      (hcap A (Finset.mem_filter.mp hA).1))
    descending_injective.injOn (fun A _ => descending_prod A) n
  simpa only [primes, descending_toFinset] using hh

theorem empty_mem_outer (D s z : ℝ) (K : ℕ) : [] ∈ outer D s z K := by
  apply Finset.mem_filter.mpr
  refine ⟨(mem_boundedTuples _ _ _).mpr ⟨by simp, by simp⟩, ?_⟩
  simp [outerTest, indices, scales, SieveBoxPrefix.accepts]

run_cmd do
  for decl in [``inner_strict, ``inner_nodup, ``inner_accepts, ``inner_selected_odd,
      ``inner_toFinset_injective, ``selected_even_to_outer, ``comparison,
      ``empty_mem_outer] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ACTUAL UPPER BOX FAMILIES: OUTER EVEN MINUS INNER ODD"
end SieveUpperBoxFamily
end
