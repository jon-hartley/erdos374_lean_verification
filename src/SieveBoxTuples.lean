import SieveGeometricGrid
import SievePrimeSubsetEvaluation
import SievePrefixAcceptance
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Sort
import Mathlib.Data.List.FinRange

/-! Exact finite tuple bookkeeping for boxing. Cartesian tuples retain repeated
primes. Only distinct prime lists permit replacing product divisibility by
individual prime divisibility. No signed boxing inequality is assumed here. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace SieveBoxTuples

def boxIndex (D s p : ℝ) : ℕ :=
  if h : ∃ n : ℕ, SieveGeometricGrid.InBox D s p n then Classical.choose h else 0

theorem boxIndex_spec (D s p : ℝ) (hD : 1 < D) (hs : 0 < s)
    (hlo : D^(s^2) ≤ p) (hhi : p < D) :
    SieveGeometricGrid.InBox D s p (boxIndex D s p) := by
  have he := SieveGeometricGrid.exists_box D s p hD hs hlo hhi
  simp only [boxIndex, dite_eq_left he]
  exact Classical.choose_spec he

theorem boxIndex_le_cutoff (D s p : ℝ) (hD : 1 < D) (hs : 0 < s)
    (hlo : D^(s^2) ≤ p) (hhi : p < D) :
    boxIndex D s p ≤ SieveGeometricGrid.cutoff s :=
  SieveGeometricGrid.index_le_cutoff D s p hD hs hhi _
    (boxIndex_spec D s p hD hs hlo hhi)

theorem boxIndex_eq_of_inBox (D s p : ℝ) (hD : 1 < D) (hs : 0 < s)
    (n : ℕ) (hn : SieveGeometricGrid.InBox D s p n) :
    boxIndex D s p = n := by
  have he : ∃ j, SieveGeometricGrid.InBox D s p j := ⟨n, hn⟩
  have hj : SieveGeometricGrid.InBox D s p (boxIndex D s p) := by
    simp only [boxIndex, dite_eq_left he]
    exact Classical.choose_spec he
  exact SieveGeometricGrid.box_unique D s p hD hs _ n hj hn

theorem value_lt_of_index_lt (D s p q : ℝ) (hD : 1 < D) (hs : 0 < s)
    (i j : ℕ) (hp : SieveGeometricGrid.InBox D s p i)
    (hq : SieveGeometricGrid.InBox D s q j) (hij : i < j) : p < q := by
  exact hp.2.trans_le
    (((SieveGeometricGrid.scale_strictMono D s hD hs).monotone
      (Nat.succ_le_of_lt hij)).trans hq.1)

theorem index_le_of_value_le (D s p q : ℝ) (hD : 1 < D) (hs : 0 < s)
    (i j : ℕ) (hp : SieveGeometricGrid.InBox D s p i)
    (hq : SieveGeometricGrid.InBox D s q j) (hpq : p ≤ q) : i ≤ j := by
  by_contra h
  exact (not_lt_of_ge hpq) (value_lt_of_index_lt D s q p hD hs j i hq hp (by omega))

theorem antitone_indices {r : ℕ} (D s : ℝ) (hD : 1 < D) (hs : 0 < s)
    (p : Fin r → ℕ) (i : Fin r → ℕ)
    (hb : ∀ k, SieveGeometricGrid.InBox D s (p k) (i k))
    (hp : Antitone p) : Antitone i := by
  intro k l hkl
  exact index_le_of_value_le D s (p l) (p k) hD hs (i l) (i k)
    (hb l) (hb k) (by exact_mod_cast hp hkl)

theorem strictAnti_values {r : ℕ} (D s : ℝ) (hD : 1 < D) (hs : 0 < s)
    (p : Fin r → ℕ) (i : Fin r → ℕ)
    (hb : ∀ k, SieveGeometricGrid.InBox D s (p k) (i k))
    (hi : StrictAnti i) : StrictAnti p := by
  intro k l hkl
  exact_mod_cast value_lt_of_index_lt D s (p l) (p k) hD hs (i l) (i k)
    (hb l) (hb k) (hi hkl)

theorem nodup_of_strictAnti_indices {r : ℕ} (D s : ℝ) (hD : 1 < D) (hs : 0 < s)
    (p : Fin r → ℕ) (i : Fin r → ℕ)
    (hb : ∀ k, SieveGeometricGrid.InBox D s (p k) (i k))
    (hi : StrictAnti i) : (List.ofFn p).Nodup :=
  List.nodup_ofFn.mpr (strictAnti_values D s hD hs p i hb hi).injective

/-- Every list of the given length with entries in P, including repetitions. -/
def tupleLists (P : Finset ℕ) : ℕ → Finset (List ℕ)
  | 0 => {[]}
  | r+1 => P.biUnion (fun p => (tupleLists P r).image (List.cons p))

theorem mem_tupleLists (P : Finset ℕ) (r : ℕ) (ps : List ℕ) :
    ps ∈ tupleLists P r ↔ ps.length = r ∧ ∀ p ∈ ps, p ∈ P := by
  induction r generalizing ps with
  | zero =>
      cases ps <;> simp [tupleLists]
  | succ r ih =>
      cases ps with
      | nil => simp [tupleLists]
      | cons p ps =>
          simp [tupleLists, ih, and_assoc, and_left_comm]

theorem replicate_mem_tupleLists (P : Finset ℕ) (r p : ℕ) (hp : p ∈ P) :
    List.replicate r p ∈ tupleLists P r := by
  apply (mem_tupleLists P r _).mpr
  constructor
  · simp
  · intro q hq
    exact (List.eq_of_mem_replicate hq) ▸ hp

def descending (s : Finset ℕ) : List ℕ := s.sort (· ≥ ·)

theorem descending_toFinset (s : Finset ℕ) : (descending s).toFinset = s := by
  exact s.sort_toFinset (· ≥ ·)

theorem descending_length (s : Finset ℕ) : (descending s).length = s.card := by
  exact s.length_sort (· ≥ ·)

theorem descending_nodup (s : Finset ℕ) : (descending s).Nodup :=
  s.sort_nodup (· ≥ ·)

theorem descending_pairwise (s : Finset ℕ) : (descending s).Pairwise (· ≥ ·) :=
  s.pairwise_sort (· ≥ ·)

theorem descending_strict (s : Finset ℕ) : (descending s).Pairwise (· > ·) :=
  s.sortedGT_sort.pairwise

theorem mem_descending (s : Finset ℕ) (p : ℕ) : p ∈ descending s ↔ p ∈ s := by
  exact Finset.mem_sort (· ≥ ·)

theorem descending_injective : Function.Injective descending := by
  intro s t h
  have hh := congrArg List.toFinset h
  simpa only [descending_toFinset] using hh

theorem descending_eq_of_sorted (ps : List ℕ) (hn : ps.Nodup)
    (ho : ps.Pairwise (· ≥ ·)) : descending ps.toFinset = ps :=
  (List.toFinset_sort (· ≥ ·) hn).mpr ho

theorem toFinset_injective_on_sorted (ps qs : List ℕ)
    (hp : ps.Nodup) (hq : qs.Nodup)
    (hpo : ps.Pairwise (· ≥ ·)) (hqo : qs.Pairwise (· ≥ ·))
    (he : ps.toFinset = qs.toFinset) : ps = qs := by
  rw [← descending_eq_of_sorted ps hp hpo, ← descending_eq_of_sorted qs hq hqo, he]

theorem descending_sublist (s : Finset ℕ) (ps : List ℕ)
    (hn : ps.Nodup) (ho : ps.Pairwise (· ≥ ·)) (hsub : s ⊆ ps.toFinset) :
    (descending s).Sublist ps := by
  let qs := ps.filter (fun p => p ∈ s)
  have hqn : qs.Nodup := hn.filter _
  have hqo : qs.Pairwise (· ≥ ·) := ho.sublist List.filter_sublist
  have he : qs.toFinset = s := by
    ext p
    simp only [qs, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    constructor
    · exact And.right
    · intro hp
      exact ⟨List.mem_toFinset.mp (hsub hp), hp⟩
  rw [← he, descending_eq_of_sorted qs hqn hqo]
  exact List.filter_sublist

theorem descending_mem_tupleLists (P s : Finset ℕ) (hs : s ⊆ P) :
    descending s ∈ tupleLists P s.card :=
  (mem_tupleLists P s.card _).mpr
    ⟨descending_length s, fun p hp => hs ((mem_descending s p).mp hp)⟩

theorem descending_prod (s : Finset ℕ) :
    (descending s).prod = SievePrimeSubset.subsetProduct s := by
  have hh := List.prod_toFinset (fun p : ℕ => p) (descending_nodup s)
  simpa only [descending_toFinset, SievePrimeSubset.subsetProduct, List.map_id'] using hh.symm

theorem nodup_prod_dvd_iff (ps : List ℕ) (hn : ps.Nodup)
    (hp : ∀ p ∈ ps, p.Prime) (m : ℕ) :
    ps.prod ∣ m ↔ ∀ p ∈ ps, p ∣ m := by
  have he : SievePrimeSubset.subsetProduct ps.toFinset = ps.prod := by
    simpa only [SievePrimeSubset.subsetProduct, List.map_id'] using
      List.prod_toFinset (fun p : ℕ => p) hn
  rw [← he, SievePrimeSubset.subsetProduct_dvd_iff ps.toFinset m
    (fun p h => hp p (List.mem_toFinset.mp h))]
  simp only [List.mem_toFinset]

theorem descending_prod_dvd_iff (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (m : ℕ) :
    (descending s).prod ∣ m ↔ ∀ p ∈ s, p ∣ m := by
  rw [descending_prod]
  exact SievePrimeSubset.subsetProduct_dvd_iff s m hs

theorem sum_descending_kernel (A : Finset (Finset ℕ)) (f : List ℕ → ℝ) :
    ∑ ps ∈ A.image descending, f ps = ∑ s ∈ A, f (descending s) := by
  exact Finset.sum_image (fun s _ t _ h => descending_injective h)

theorem sum_descending_divisor (A : Finset (Finset ℕ)) (m : ℕ) :
    (∑ ps ∈ A.image descending, if ps.prod ∣ m then (-1 : ℝ)^ps.length else 0) =
      ∑ s ∈ A, if SievePrimeSubset.subsetProduct s ∣ m then (-1 : ℝ)^s.card else 0 := by
  rw [sum_descending_kernel]
  simp only [descending_prod, descending_length]

theorem descending_selected_accepts (gate : ℕ → ℕ → Prop) (upper : Bool) (d : ℕ)
    (ps : List ℕ) (hn : ps.Nodup) (ho : ps.Pairwise (· ≥ ·))
    (s : Finset ℕ) (hs : s ∈ SievePrefix.selected gate upper d ps) :
    SievePrefix.accepts gate upper d (descending s) := by
  obtain ⟨qs, hq, he, ha⟩ := SievePrefix.exists_sublist_accepts_of_selected gate upper d ps s hs
  have hnq := hn.sublist hq
  have hoq := ho.sublist hq
  rw [← he, descending_eq_of_sorted qs hnq hoq]
  exact ha

/-- Grid assignment preserves weak descent for every list in the grid range. -/
theorem descending_box_indices (D s : ℝ) (hD : 1 < D) (hs : 0 < s)
    (ps : List ℕ) (ho : ps.Pairwise (· ≥ ·))
    (hr : ∀ p ∈ ps, D^(s^2) ≤ (p : ℝ) ∧ (p : ℝ) < D) :
    (ps.map (fun p : ℕ => boxIndex D s (p : ℝ))).Pairwise (· ≥ ·) := by
  rw [List.pairwise_map]
  apply ho.imp_of_mem
  intro p q hp hq hpq
  exact index_le_of_value_le D s q p hD hs _ _
    (boxIndex_spec D s q hD hs (hr q hq).1 (hr q hq).2)
    (boxIndex_spec D s p hD hs (hr p hp).1 (hr p hp).2)
    (by exact_mod_cast hpq)

/-- Strictly descending assigned indices force distinct actual prime entries. -/
theorem strict_box_indices_values (D s : ℝ) (hD : 1 < D) (hs : 0 < s)
    (ps : List ℕ)
    (hr : ∀ p ∈ ps, D^(s^2) ≤ (p : ℝ) ∧ (p : ℝ) < D)
    (hi : (ps.map (fun p : ℕ => boxIndex D s (p : ℝ))).Pairwise (· > ·)) :
    ps.Pairwise (· > ·) := by
  rw [List.pairwise_map] at hi
  apply hi.imp_of_mem
  intro p q hp hq hpq
  exact_mod_cast value_lt_of_index_lt D s q p hD hs _ _
    (boxIndex_spec D s q hD hs (hr q hq).1 (hr q hq).2)
    (boxIndex_spec D s p hD hs (hr p hp).1 (hr p hp).2) hpq

theorem strict_box_indices_nodup (D s : ℝ) (hD : 1 < D) (hs : 0 < s)
    (ps : List ℕ)
    (hr : ∀ p ∈ ps, D^(s^2) ≤ (p : ℝ) ∧ (p : ℝ) < D)
    (hi : (ps.map (fun p : ℕ => boxIndex D s (p : ℝ))).Pairwise (· > ·)) :
    ps.Nodup :=
  (strict_box_indices_values D s hD hs ps hr hi).imp (fun h => ne_of_gt h)

#print axioms sum_descending_divisor
#print axioms descending_selected_accepts
run_cmd do
  for decl in [``boxIndex_spec, ``boxIndex_le_cutoff, ``boxIndex_eq_of_inBox,
    ``value_lt_of_index_lt, ``index_le_of_value_le, ``antitone_indices,
    ``strictAnti_values, ``nodup_of_strictAnti_indices, ``mem_tupleLists,
    ``replicate_mem_tupleLists, ``descending_toFinset, ``descending_length,
    ``descending_nodup, ``descending_pairwise, ``descending_strict, ``mem_descending,
    ``descending_injective, ``descending_eq_of_sorted, ``toFinset_injective_on_sorted,
    ``descending_sublist, ``descending_mem_tupleLists, ``descending_prod,
    ``nodup_prod_dvd_iff, ``descending_prod_dvd_iff, ``sum_descending_kernel,
    ``sum_descending_divisor, ``descending_selected_accepts, ``descending_box_indices,
    ``strict_box_indices_values, ``strict_box_indices_nodup] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
run_cmd Lean.logInfo "SIEVE BOX TUPLES PASSED; FINITE BOOKKEEPING ONLY"

end SieveBoxTuples
end
