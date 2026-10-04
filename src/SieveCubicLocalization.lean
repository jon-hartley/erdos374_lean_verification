import SieveBoxedFamily

/-! Actual discrepancies between boxed and ordinary lower Rosser acceptance
are localized at tested even prefixes. The stronger inner level is retained.
This file proves localization only, not a reciprocal strip-mass estimate. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
attribute [local instance] Classical.propDecidable

namespace SieveCubicLocalization

/-- Acceptance at the upper level and rejection at the lower level locate
a tested cubic prefix in the half-open threshold strip. -/
theorem acceptance_strip (L U : ℝ) (mode : Bool) (xs : List ℝ)
    (hhigh : SieveBoxPrefix.accepts U mode 1 xs)
    (hlow : ¬SieveBoxPrefix.accepts L mode 1 xs) :
    ∃ (n : ℕ) (hn : n < xs.length), SieveBoxPrefix.stateAt mode n = true ∧
      L ≤ (xs.take n).prod * xs[n]^3 ∧ (xs.take n).prod * xs[n]^3 < U := by
  by_contra hnone
  apply hlow
  apply (SieveBoxPrefix.accepts_iff_prefix_tests L mode 1 xs).mpr
  intro n hn hstate
  by_contra hfail
  apply hnone
  refine ⟨n, hn, hstate, ?_, ?_⟩
  · simpa only [one_mul] using le_of_not_gt hfail
  · simpa only [one_mul] using
      (SieveBoxPrefix.accepts_iff_prefix_tests U mode 1 xs).mp hhigh n hn hstate

theorem tested_index_odd (n : ℕ) (hstate : SieveBoxPrefix.stateAt false n = true) :
    Odd n := by
  rcases Nat.even_or_odd' n with ⟨k, hk | hk⟩
  · simp only [hk, SieveBoxPrefix.stateAt_even, Bool.false_eq_true] at hstate
  · exact ⟨k, by omega⟩

/-- The zero-based terminal index is odd, so the tested prefix has even length. -/
theorem natural_acceptance_strip (L U : ℝ) (t : List ℕ)
    (hhigh : SievePrefix.accepts (SieveRosser.cubicGate U) false 1 t)
    (hlow : ¬SievePrefix.accepts (SieveRosser.cubicGate L) false 1 t) :
    ∃ (n : ℕ) (hn : n < t.length), Odd n ∧
      L ≤ ((t.take n).prod:ℝ)*(t[n]:ℝ)^3 ∧ ((t.take n).prod:ℝ)*(t[n]:ℝ)^3 < U := by
  have hhigh' : SieveBoxPrefix.accepts U false 1 (t.map (fun p : ℕ => (p:ℝ))) := by
    simpa only [Nat.cast_one] using (SieveBoxPrefix.accepts_natCast_iff U false 1 t).mpr hhigh
  have hlow' : ¬SieveBoxPrefix.accepts L false 1 (t.map (fun p : ℕ => (p:ℝ))) := by
    intro h
    exact hlow ((SieveBoxPrefix.accepts_natCast_iff L false 1 t).mp
      (by simpa only [Nat.cast_one] using h))
  obtain ⟨n, hn, hstate, hl, hu⟩ := acceptance_strip L U false _ hhigh' hlow'
  have hn' : n < t.length := by simpa only [List.length_map] using hn
  refine ⟨n, hn', tested_index_odd n hstate, ?_, ?_⟩
  · simpa only [← List.map_take, List.getElem_map, ← Nat.cast_list_prod] using hl
  · simpa only [← List.map_take, List.getElem_map, ← Nat.cast_list_prod] using hu

/-- Scale acceptance at D implies raw acceptance at D^q whenever each raw
coordinate is bounded above by the q-th power of its scale. -/
theorem raw_accepts_power_level (D q : ℝ) (mode : Bool) (f : ℕ → ℝ) (t : List ℕ)
    (hD : 0 ≤ D) (hq : 0 < q)
    (hf : ∀ p ∈ t, 0 ≤ f p ∧ (p:ℝ) ≤ (f p)^q)
    (hscale : SieveBoxPrefix.accepts D mode 1 (t.map f)) :
    SievePrefix.accepts (SieveRosser.cubicGate (D^q)) mode 1 t := by
  apply SieveBoxPrefix.inner_accepts_map (D^q) q mode f t (Real.rpow_nonneg hD q) hq hf
  have hlevel : (D^q)^(1/q) = D := by
    rw [← Real.rpow_mul hD, show q*(1/q) = 1 by field_simp, Real.rpow_one]
  simpa only [hlevel] using hscale

/-- An ordinary accepted even tuple with strict assigned indices can be
omitted by the inner test only in the actual lower cubic threshold strip. -/
theorem inner_omission (D s z : ℝ) (t : List ℕ)
    (hD : 1 < D) (hs : 0 < s) (hz : z ≤ D)
    (hpool : ∀ p ∈ t, p ∈ SieveBoxedFamily.pool D s z)
    (heven : Even t.length) (hindices : (SieveBoxedFamily.indices D s t).Pairwise (· > ·))
    (hraw : SievePrefix.accepts (SieveRosser.cubicGate D) false 1 t)
    (hinner : ¬SieveBoxedFamily.innerTest D s t) :
    ∃ (n : ℕ) (hn : n < t.length), Odd n ∧
      D^(1/SieveGeometricGrid.ratio s) ≤ ((t.take n).prod:ℝ)*(t[n]:ℝ)^3 ∧
      ((t.take n).prod:ℝ)*(t[n]:ℝ)^3 < D := by
  apply natural_acceptance_strip _ D t hraw
  intro hlow
  apply hinner
  refine ⟨heven, hindices, ?_⟩
  apply SieveBoxPrefix.outer_accepts_map _ false (SieveBoxedFamily.coordinate D s) t _ hlow
  intro p hp
  have hb := SieveBoxedFamily.coordinate_bounds D s z hD hs hz p (hpool p hp)
  exact ⟨hb.1, hb.2.1⟩

/-- An outer-admissible tuple rejected by the ordinary selector has a tested
raw cubic prefix at least D but strictly below D^q. Repetitions are allowed. -/
theorem outer_excess (D s z : ℝ) (t : List ℕ)
    (hD : 1 < D) (hs : 0 < s) (hz : z ≤ D)
    (hpool : ∀ p ∈ t, p ∈ SieveBoxedFamily.pool D s z)
    (houter : SieveBoxedFamily.outerTest D s t)
    (hraw : ¬SievePrefix.accepts (SieveRosser.cubicGate D) false 1 t) :
    ∃ (n : ℕ) (hn : n < t.length), Odd n ∧
      D ≤ ((t.take n).prod:ℝ)*(t[n]:ℝ)^3 ∧
      ((t.take n).prod:ℝ)*(t[n]:ℝ)^3 < D^(SieveGeometricGrid.ratio s) := by
  apply natural_acceptance_strip D _ t _ hraw
  apply raw_accepts_power_level D (SieveGeometricGrid.ratio s) false
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
    (heven : Even t.length) (hindices : (SieveBoxedFamily.indices D s t).Pairwise (· > ·))
    (hraw : SievePrefix.accepts (SieveRosser.cubicGate D) false 1 t)
    (hinner : t ∉ SieveBoxedFamily.inner D s z K) :
    ∃ (n : ℕ) (hn : n < t.length), Odd n ∧
      D^(1/SieveGeometricGrid.ratio s) ≤ ((t.take n).prod:ℝ)*(t[n]:ℝ)^3 ∧
      ((t.take n).prod:ℝ)*(t[n]:ℝ)^3 < D := by
  apply inner_omission D s z t hD hs hz
    ((SieveBoxedFamily.mem_boundedTuples _ _ _).mp hbounded).2 heven hindices hraw
  intro hi
  exact hinner (Finset.mem_filter.mpr ⟨hbounded, hi⟩)

theorem outer_excess_of_mem (D s z : ℝ) (K : ℕ) (t : List ℕ)
    (hD : 1 < D) (hs : 0 < s) (hz : z ≤ D)
    (houter : t ∈ SieveBoxedFamily.outer D s z K)
    (hraw : ¬SievePrefix.accepts (SieveRosser.cubicGate D) false 1 t) :
    ∃ (n : ℕ) (hn : n < t.length), Odd n ∧
      D ≤ ((t.take n).prod:ℝ)*(t[n]:ℝ)^3 ∧
      ((t.take n).prod:ℝ)*(t[n]:ℝ)^3 < D^(SieveGeometricGrid.ratio s) := by
  obtain ⟨hb, ho⟩ := Finset.mem_filter.mp houter
  exact outer_excess D s z t hD hs hz
    ((SieveBoxedFamily.mem_boundedTuples _ _ _).mp hb).2 ho hraw

run_cmd do
  for decl in [``acceptance_strip, ``tested_index_odd, ``natural_acceptance_strip,
      ``raw_accepts_power_level, ``inner_omission, ``outer_excess,
      ``inner_omission_of_not_mem, ``outer_excess_of_mem] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ACTUAL CUBIC INNER/OUTER DISCREPANCY LOCALIZATION PASSED"

end SieveCubicLocalization
end
