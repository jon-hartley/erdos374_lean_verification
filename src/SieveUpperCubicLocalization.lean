import SieveUpperBoxFamily
import SieveCubicLocalization

/-! Actual upper-mode boxed discrepancies locate an even zero-based tested
coordinate in the raw cubic threshold strips. This is localization only:
no reciprocal-mass or analytic remainder bound is assumed or concluded. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
attribute [local instance] Classical.propDecidable
namespace SieveUpperCubicLocalization

theorem tested_index_even (n : ℕ) (hstate : SieveBoxPrefix.stateAt true n = true) :
    Even n := by
  rcases Nat.even_or_odd' n with ⟨k, hk | hk⟩
  · exact ⟨k, by omega⟩
  · simp only [hk, SieveBoxPrefix.stateAt_odd, Bool.not_true, Bool.false_eq_true] at hstate


/-- The zero-based terminal index is even, so the tested prefix has odd length. -/
theorem natural_acceptance_strip (L U : ℝ) (t : List ℕ)
    (hhigh : SievePrefix.accepts (SieveRosser.cubicGate U) true 1 t)
    (hlow : ¬SievePrefix.accepts (SieveRosser.cubicGate L) true 1 t) :
    ∃ (n : ℕ) (hn : n < t.length), Even n ∧
      L ≤ ((t.take n).prod:ℝ)*(t[n]:ℝ)^3 ∧ ((t.take n).prod:ℝ)*(t[n]:ℝ)^3 < U := by
  have hhigh' : SieveBoxPrefix.accepts U true 1 (t.map (fun p : ℕ => (p:ℝ))) := by
    simpa only [Nat.cast_one] using (SieveBoxPrefix.accepts_natCast_iff U true 1 t).mpr hhigh
  have hlow' : ¬SieveBoxPrefix.accepts L true 1 (t.map (fun p : ℕ => (p:ℝ))) := by
    intro h
    exact hlow ((SieveBoxPrefix.accepts_natCast_iff L true 1 t).mp
      (by simpa only [Nat.cast_one] using h))
  obtain ⟨n, hn, hstate, hl, hu⟩ := SieveCubicLocalization.acceptance_strip L U true _ hhigh' hlow'
  have hn' : n < t.length := by simpa only [List.length_map] using hn
  refine ⟨n, hn', tested_index_even n hstate, ?_, ?_⟩
  · simpa only [← List.map_take, List.getElem_map, ← Nat.cast_list_prod] using hl
  · simpa only [← List.map_take, List.getElem_map, ← Nat.cast_list_prod] using hu

/-- An ordinary accepted odd tuple with strict assigned indices can be
omitted by the inner test only in the actual lower cubic threshold strip. -/
theorem inner_omission (D s z : ℝ) (t : List ℕ)
    (hD : 1 < D) (hs : 0 < s) (hz : z ≤ D)
    (hpool : ∀ p ∈ t, p ∈ SieveBoxedFamily.pool D s z)
    (hodd : ¬Even t.length) (hindices : (SieveBoxedFamily.indices D s t).Pairwise (· > ·))
    (hraw : SievePrefix.accepts (SieveRosser.cubicGate D) true 1 t)
    (hinner : ¬SieveUpperBoxFamily.innerTest D s t) :
    ∃ (n : ℕ) (hn : n < t.length), Even n ∧
      D^(1/SieveGeometricGrid.ratio s) ≤ ((t.take n).prod:ℝ)*(t[n]:ℝ)^3 ∧
      ((t.take n).prod:ℝ)*(t[n]:ℝ)^3 < D := by
  apply natural_acceptance_strip _ D t hraw
  intro hlow
  apply hinner
  refine ⟨hodd, hindices, ?_⟩
  apply SieveBoxPrefix.outer_accepts_map _ true (SieveBoxedFamily.coordinate D s) t _ hlow
  intro p hp
  have hb := SieveBoxedFamily.coordinate_bounds D s z hD hs hz p (hpool p hp)
  exact ⟨hb.1, hb.2.1⟩

/-- An outer-admissible tuple rejected by the ordinary selector has a tested
raw cubic prefix at least D but strictly below D^q. Repetitions are allowed. -/
theorem outer_excess (D s z : ℝ) (t : List ℕ)
    (hD : 1 < D) (hs : 0 < s) (hz : z ≤ D)
    (hpool : ∀ p ∈ t, p ∈ SieveBoxedFamily.pool D s z)
    (houter : SieveUpperBoxFamily.outerTest D s t)
    (hraw : ¬SievePrefix.accepts (SieveRosser.cubicGate D) true 1 t) :
    ∃ (n : ℕ) (hn : n < t.length), Even n ∧
      D ≤ ((t.take n).prod:ℝ)*(t[n]:ℝ)^3 ∧
      ((t.take n).prod:ℝ)*(t[n]:ℝ)^3 < D^(SieveGeometricGrid.ratio s) := by
  apply natural_acceptance_strip D _ t _ hraw
  apply SieveCubicLocalization.raw_accepts_power_level D (SieveGeometricGrid.ratio s) true
    (SieveBoxedFamily.coordinate D s) t (by linarith)
    (zero_lt_one.trans (SieveGeometricGrid.one_lt_ratio s hs))
  · intro p hp
    have hb := SieveBoxedFamily.coordinate_bounds D s z hD hs hz p (hpool p hp)
    exact ⟨hb.1, hb.2.2.le⟩
  · exact houter.2.2

/-- Family-level inner omission: the tuple is already within the actual
finite domain, so failure of membership really is failure of its inner test. -/
theorem inner_omission_of_not_mem (D s z : ℝ) (K : ℕ) (t : List ℕ)
    (hD : 1 < D) (hs : 0 < s) (hz : z ≤ D)
    (hbounded : t ∈ SieveBoxedFamily.boundedTuples (SieveBoxedFamily.pool D s z) K)
    (hodd : ¬Even t.length) (hindices : (SieveBoxedFamily.indices D s t).Pairwise (· > ·))
    (hraw : SievePrefix.accepts (SieveRosser.cubicGate D) true 1 t)
    (hinner : t ∉ SieveUpperBoxFamily.inner D s z K) :
    ∃ (n : ℕ) (hn : n < t.length), Even n ∧
      D^(1/SieveGeometricGrid.ratio s) ≤ ((t.take n).prod:ℝ)*(t[n]:ℝ)^3 ∧
      ((t.take n).prod:ℝ)*(t[n]:ℝ)^3 < D := by
  apply inner_omission D s z t hD hs hz
    ((SieveBoxedFamily.mem_boundedTuples _ _ _).mp hbounded).2 hodd hindices hraw
  intro hi
  exact hinner (Finset.mem_filter.mpr ⟨hbounded, hi⟩)

theorem outer_excess_of_mem (D s z : ℝ) (K : ℕ) (t : List ℕ)
    (hD : 1 < D) (hs : 0 < s) (hz : z ≤ D)
    (houter : t ∈ SieveUpperBoxFamily.outer D s z K)
    (hraw : ¬SievePrefix.accepts (SieveRosser.cubicGate D) true 1 t) :
    ∃ (n : ℕ) (hn : n < t.length), Even n ∧
      D ≤ ((t.take n).prod:ℝ)*(t[n]:ℝ)^3 ∧
      ((t.take n).prod:ℝ)*(t[n]:ℝ)^3 < D^(SieveGeometricGrid.ratio s) := by
  obtain ⟨hb, ho⟩ := Finset.mem_filter.mp houter
  exact outer_excess D s z t hD hs hz
    ((SieveBoxedFamily.mem_boundedTuples _ _ _).mp hb).2 ho hraw

run_cmd do
  for decl in [``tested_index_even, ``natural_acceptance_strip,
      ``inner_omission, ``outer_excess, ``inner_omission_of_not_mem,
      ``outer_excess_of_mem] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ACTUAL UPPER CUBIC LOCALIZATION; EVEN ZERO-BASED TESTED INDICES"
end SieveUpperCubicLocalization
end
