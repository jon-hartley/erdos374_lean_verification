import UpperAfter545Geometry

/-! Exact upper-mode singleton membership in the original half-open grid.
Accepted indices depend only on s. Both directions retain the literal prime
pool and cubic cutoff; this is not the one-way Rosser acceptance implication. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
attribute [local instance] Classical.propDecidable

namespace ShortSingletonBoxes
open SieveGeometricGrid SieveUpperBoxing SieveBoxedFamily SieveBoxTuples

def acceptedIndices (s : ℝ) : Finset ℕ :=
  (Finset.range (SieveGeometricGrid.cutoff s+1)).filter
    (fun j => 3*exponent s j < 1/ratio s)

theorem mem_acceptedIndices (s : ℝ) (j : ℕ) :
    j ∈ acceptedIndices s ↔ j ≤ SieveGeometricGrid.cutoff s ∧ 3*exponent s j < 1/ratio s := by
  simp only [acceptedIndices, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]

theorem singleton_innerTest_iff (D s : ℝ) (q : ℕ) :
    SieveUpperBoxFamily.innerTest D s [q] ↔ (coordinate D s q)^3 < D^(1/ratio s) := by
  simp [SieveUpperBoxFamily.innerTest, indices, scales, SieveBoxPrefix.accepts]

theorem scale_cube_lt_iff (D s : ℝ) (hD : 1 < D) (j : ℕ) :
    (scale D s j)^3 < D^(1/ratio s) ↔ 3*exponent s j < 1/ratio s := by
  rw [scale, ←Real.rpow_mul_natCast (show 0 ≤ D by linarith)]
  norm_num only [Nat.cast_ofNat]
  rw [Real.rpow_lt_rpow_left_iff hD]
  simp only [mul_comm]

theorem accepted_box_bounds (D s q : ℝ) (hD : 1 < D) (hs : 0 < s)
    (j : ℕ) (ha : 3*exponent s j < 1/ratio s) (hb : InBox D s q j) :
    D^(s^2) ≤ q ∧ q < D^(1/3:ℝ) := by
  have hr : 0 < ratio s := (zero_lt_one.trans (one_lt_ratio s hs))
  have hae := (lt_div_iff₀ hr).mp ha
  have hsuc : exponent s (j+1) < (1/3:ℝ) := by
    unfold exponent at *
    rw [pow_succ (ratio s) j]
    nlinarith
  constructor
  · exact ((scale_zero D s).symm.trans_le
      ((scale_strictMono D s hD hs).monotone (Nat.zero_le j))).trans hb.1
  · exact hb.2.trans ((Real.rpow_lt_rpow_left_iff hD).mpr hsuc)

theorem inner_singleton_iff (D s : ℝ) (q : ℕ) (hD : 1 < D) (hs : 0 < s) :
    [q] ∈ innerFamily D s (D^(1/3:ℝ)) ↔
      q.Prime ∧ ∃ j ∈ acceptedIndices s, InBox D s (q:ℝ) j := by
  have htop : D^(1/3:ℝ) ≤ D := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hD.le (show (1/3:ℝ) ≤ 1 by norm_num)
  constructor
  · intro ht
    have hm := (mem_innerFamily D s (D^(1/3:ℝ)) hD hs [q]).mp ht
    have hp := (mem_pool D s (D^(1/3:ℝ)) q).mp (hm.1 q (by simp))
    have hb := boxIndex_spec D s q hD hs hp.2.2 (hp.2.1.trans_le htop)
    have hc := (singleton_innerTest_iff D s q).mp hm.2
    change (scale D s (boxIndex D s q))^3 < D^(1/ratio s) at hc
    exact ⟨hp.1,boxIndex D s q,(mem_acceptedIndices s _).mpr
      ⟨boxIndex_le_cutoff D s q hD hs hp.2.2 (hp.2.1.trans_le htop),
        (scale_cube_lt_iff D s hD _).mp hc⟩,hb⟩
  · rintro ⟨hp,j,hj,hb⟩
    have ha := ((mem_acceptedIndices s j).mp hj).2
    have hbounds := accepted_box_bounds D s q hD hs j ha hb
    have he := boxIndex_eq_of_inBox D s q hD hs j hb
    apply (mem_innerFamily D s (D^(1/3:ℝ)) hD hs [q]).mpr
    constructor
    · intro r hr
      have hrq : r = q := by simpa using hr
      subst r
      exact (mem_pool D s (D^(1/3:ℝ)) q).mpr ⟨hp,hbounds.2,hbounds.1⟩
    · rw [singleton_innerTest_iff, coordinate, he]
      exact (scale_cube_lt_iff D s hD j).mpr ha

theorem inner_singleton_iff_unique (D s : ℝ) (q : ℕ) (hD : 1 < D) (hs : 0 < s) :
    [q] ∈ innerFamily D s (D^(1/3:ℝ)) ↔
      q.Prime ∧ ∃! j, j ∈ acceptedIndices s ∧ InBox D s (q:ℝ) j := by
  rw [inner_singleton_iff D s q hD hs]
  constructor
  · rintro ⟨hp,j,hj,hb⟩
    exact ⟨hp,j,⟨hj,hb⟩,fun k hk => box_unique D s q hD hs k j hk.2 hb⟩
  · rintro ⟨hp,j,hj,_⟩
    exact ⟨hp,j,hj⟩

theorem inner_singleton_iff_explicit (D s : ℝ) (q : ℕ) (hD : 1 < D) (hs : 0 < s) :
    [q] ∈ innerFamily D s (D^(1/3:ℝ)) ↔
      q.Prime ∧ ∃ j ≤ SieveGeometricGrid.cutoff s,
        3*(s^2*(1+s^9)^j) < 1/(1+s^9) ∧
        D^(s^2*(1+s^9)^j) ≤ (q:ℝ) ∧ (q:ℝ) < D^(s^2*(1+s^9)^(j+1)) := by
  rw [inner_singleton_iff D s q hD hs]
  simp only [mem_acceptedIndices, InBox, scale, exponent, ratio]
  aesop

theorem actual_large_singleton_iff (X s : ℝ) (p q : ℕ) (hX : 1 < X)
    (hs : 0 < s) (hs1 : s ≤ 1/1000) (hlog : 1000 ≤ Real.log X)
    (hp : p ∈ PositiveSharpBoxedCount.largePrimes X) :
    [q] ∈ innerFamily (SieveWeightedCutoffs.level X s/p) s
      (SieveWeightedCutoffs.cutoffThree X s p) ↔
      q.Prime ∧ ∃ j ∈ acceptedIndices s,
        InBox (SieveWeightedCutoffs.level X s/p) s (q:ℝ) j := by
  have hg := UpperAfter545Geometry.large_geometry X s p hX hs hs1 hlog hp
  exact inner_singleton_iff _ s q hg.2.2.1 hs

run_cmd do
  for decl in [``mem_acceptedIndices, ``singleton_innerTest_iff, ``scale_cube_lt_iff,
      ``accepted_box_bounds, ``inner_singleton_iff, ``inner_singleton_iff_unique,
      ``inner_singleton_iff_explicit, ``actual_large_singleton_iff] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "EXACT UPPER SINGLETON MEMBERSHIP IN FIXED ACCEPTED GRID INDICES PASSED"

end ShortSingletonBoxes
