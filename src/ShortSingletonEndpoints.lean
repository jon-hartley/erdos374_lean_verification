import ShortSingletonMasks
import ShortSingletonSector

/-! Literal real grid and physical high masks as natural prefix endpoints.
The endpoint at a strict real bound B is ceil(B)-1, while the physical
strict lower mask uses floor(X^.545/m). No real endpoint is rounded before
these exact equivalences, and both p-dependent grid scales are retained. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace ShortSingletonEndpoints
open ShortSingletonMasks SieveGeometricGrid UpperAfter545Sectors
open SieveWeightedCutoffs PositiveSharpBoxedCount

def strictEndpoint (B : ℝ) : ℕ := Nat.ceil B - 1
def gridLo (D s : ℝ) (j : ℕ) : ℕ := strictEndpoint (scale D s j)
def gridHi (D s : ℝ) (j : ℕ) : ℕ := strictEndpoint (scale D s (j+1))
def physicalCut (X : ℝ) (m : ℕ) : ℕ := Nat.floor (X^(109/200:ℝ)/(m:ℝ))

theorem lt_iff_le_strictEndpoint (B : ℝ) (q : ℕ) (hB : 0 < B) :
    (q:ℝ) < B ↔ q ≤ strictEndpoint B := by
  have hc : 0 < Nat.ceil B := Nat.ceil_pos.mpr hB
  rw [←Nat.lt_ceil]
  unfold strictEndpoint
  omega

theorem strictEndpoint_mono (A B : ℝ) (hAB : A ≤ B) :
    strictEndpoint A ≤ strictEndpoint B := by
  exact Nat.sub_le_sub_right (Nat.ceil_mono hAB) 1

theorem strict_prefix (B : ℝ) (q : ℕ) (hB : 0 < B) :
    (if (q:ℝ) < B then (1:ℂ) else 0) = prefixIndicator (strictEndpoint B) q := by
  simp only [prefixIndicator, lt_iff_le_strictEndpoint B q hB]

theorem halfOpen_prefix (A B : ℝ) (q : ℕ) (hA : 0 < A) (hAB : A ≤ B) :
    (if A ≤ (q:ℝ) ∧ (q:ℝ) < B then (1:ℂ) else 0) =
      prefixIndicator (strictEndpoint B) q - prefixIndicator (strictEndpoint A) q := by
  rw [←strict_prefix B q (hA.trans_le hAB), ←strict_prefix A q hA]
  by_cases hqa : (q:ℝ) < A
  · have hqb : (q:ℝ) < B := hqa.trans_le hAB
    simp [hqa,hqb,not_le_of_gt hqa]
  · simp only [hqa, ite_false, sub_zero]
    simp [le_of_not_gt hqa]

theorem physicalHigh_iff (X : ℝ) (m q : ℕ) (hX : 0 ≤ X) (hm : 0 < m) :
    X^(109/200:ℝ) < ((m*q:ℕ):ℝ) ↔ physicalCut X m < q := by
  have hmR : 0 < (m:ℝ) := by exact_mod_cast hm
  have hdiv : 0 ≤ X^(109/200:ℝ)/(m:ℝ) :=
    div_nonneg (Real.rpow_nonneg hX _) hmR.le
  rw [physicalCut, Nat.floor_lt hdiv, div_lt_iff₀ hmR]
  simp only [Nat.cast_mul, mul_comm]

theorem physicalHigh_prefix (X : ℝ) (m q : ℕ) (hX : 0 ≤ X) (hm : 0 < m) :
    (if X^(109/200:ℝ) < ((m*q:ℕ):ℝ) then (1:ℂ) else 0) =
      1 - prefixIndicator (physicalCut X m) q := by
  simp only [physicalHigh_iff X m q hX hm]
  unfold prefixIndicator
  by_cases hq : q ≤ physicalCut X m
  · simp [hq,not_lt_of_ge hq]
  · simp [hq,lt_of_not_ge hq]

theorem grid_prefix (D s : ℝ) (j q : ℕ) (hD : 1 < D) (hs : 0 < s) :
    (if InBox D s (q:ℝ) j then (1:ℂ) else 0) =
      prefixIndicator (gridHi D s j) q - prefixIndicator (gridLo D s j) q := by
  have he := halfOpen_prefix (scale D s j) (scale D s (j+1)) q
    (Real.rpow_pos_of_pos (by linarith) _) ((scale_strictMono D s hD hs).monotone (by omega))
  by_cases hb : InBox D s (q:ℝ) j
  · have hb' : scale D s j ≤ (q:ℝ) ∧ (q:ℝ) < scale D s (j+1) := hb
    simpa only [ite_eq_left hb', gridHi, gridLo, ite_eq_left hb] using he
  · have hb' : ¬(scale D s j ≤ (q:ℝ) ∧ (q:ℝ) < scale D s (j+1)) := hb
    simpa only [ite_eq_right hb', gridHi, gridLo, ite_eq_right hb] using he

theorem inBox_iff_prefix_bounds (D s : ℝ) (j q : ℕ) (hD : 0 < D) :
    InBox D s (q:ℝ) j ↔ gridLo D s j < q ∧ q ≤ gridHi D s j := by
  have hlo := lt_iff_le_strictEndpoint (scale D s j) q (Real.rpow_pos_of_pos hD _)
  have hhi := lt_iff_le_strictEndpoint (scale D s (j+1)) q (Real.rpow_pos_of_pos hD _)
  change scale D s j ≤ (q:ℝ) ∧ (q:ℝ) < scale D s (j+1) ↔
    strictEndpoint (scale D s j) < q ∧ q ≤ strictEndpoint (scale D s (j+1))
  constructor
  · rintro ⟨hl,hh⟩
    exact ⟨lt_of_not_ge (fun h => (not_lt_of_ge hl) (hlo.mpr h)),hhi.mp hh⟩
  · rintro ⟨hl,hh⟩
    exact ⟨le_of_not_gt (fun h => (not_le_of_gt hl) (hlo.mp h)),hhi.mpr hh⟩

theorem mem_survivingPrimes_iff_endpoints (X D s : ℝ) (q : ℕ) (hD : 1 < D) (hs : 0 < s) :
    q ∈ ShortSingletonSector.survivingPrimes X D s (D^(1/3:ℝ)) ↔
      q.Prime ∧ X^(1/25:ℝ) < (q:ℝ) ∧ (q:ℝ) ≤ X^(8/35:ℝ) ∧
        ∃ j ∈ ShortSingletonBoxes.acceptedIndices s, gridLo D s j < q ∧ q ≤ gridHi D s j := by
  rw [ShortSingletonSector.mem_survivingPrimes_iff_boxes X D s q hD hs]
  simp_rw [inBox_iff_prefix_bounds D s _ q (by linarith : 0 < D)]

theorem grid_high_prefix (X D s : ℝ) (j m q : ℕ)
    (hX : 0 ≤ X) (hD : 1 < D) (hs : 0 < s) (hm : 0 < m) :
    (if InBox D s (q:ℝ) j ∧ X^(109/200:ℝ) < ((m*q:ℕ):ℝ) then (1:ℂ) else 0) =
      (prefixIndicator (gridHi D s j) q - prefixIndicator (gridLo D s j) q) *
        (1-prefixIndicator (physicalCut X m) q) := by
  rw [←grid_prefix D s j q hD hs, ←physicalHigh_prefix X m q hX hm]
  simp only [Nat.cast_mul]
  by_cases hb : InBox D s (q:ℝ) j <;>
    by_cases hh : X^(109/200:ℝ) < (m:ℝ)*(q:ℝ) <;> simp_all

theorem boxed_highKernel (X D s : ℝ) (j m q : ℕ) (f : ℕ → ℝ)
    (hX : 0 ≤ X) (hD : 1 < D) (hs : 0 < s) (hm : 0 < m) :
    ((if InBox D s (q:ℝ) j then highKernel X f (m*q) else 0 : ℝ):ℂ) =
      ((prefixIndicator (gridHi D s j) q - prefixIndicator (gridLo D s j) q) *
        (1-prefixIndicator (physicalCut X m) q)) * (f (m*q):ℂ) := by
  rw [←grid_high_prefix X D s j m q hX hD hs hm]
  simp only [highKernel, Nat.cast_mul]
  by_cases hb : InBox D s (q:ℝ) j <;>
    by_cases hh : X^(109/200:ℝ) < (m:ℝ)*(q:ℝ) <;> simp_all
  all_goals split_ifs <;> rfl

theorem grid_high_expansion (X D s : ℝ) (j m q Q : ℕ)
    (hX : 0 ≤ X) (hD : 1 < D) (hs : 0 < s) (hm : 0 < m) (hq : q ≤ Q) :
    (if InBox D s (q:ℝ) j ∧ X^(109/200:ℝ) < ((m*q:ℕ):ℝ) then (1:ℂ) else 0) =
      ∑ a : Mode Q, scalar Q a * leftPhase Q a (gridLo D s j) (gridHi D s j) *
        highPhase Q a (physicalCut X m) * rightPhase Q a q := by
  rw [grid_high_prefix X D s j m q hX hD hs hm]
  exact separation Q (gridLo D s j) (gridHi D s j) (physicalCut X m) q hq

theorem actual_grid_high_prefix (X s : ℝ) (p d q j : ℕ)
    (hX : 1 < X) (hs : 0 < s) (hs1 : s ≤ 1/1000) (hlog : 1000 ≤ Real.log X)
    (hp : p ∈ largePrimes X) (hd : d ∈ SieveUpperBoxWindow.smallCarrier (level X s/p) s) :
    (if InBox (level X s/p) s (q:ℝ) j ∧ X^(109/200:ℝ) < ((p*d*q:ℕ):ℝ)
      then (1:ℂ) else 0) =
      (prefixIndicator (gridHi (level X s/p) s j) q -
        prefixIndicator (gridLo (level X s/p) s j) q) *
          (1-prefixIndicator (physicalCut X (p*d)) q) := by
  have hg := UpperAfter545Geometry.large_geometry X s p hX hs hs1 hlog hp
  have hdpos := (ShortSingletonGeometry.actual_small_divisor_bound X s p d hX hs hs1 hlog hp hd).1
  exact grid_high_prefix X (level X s/p) s j (p*d) q (by linarith) hg.2.2.1 hs
    (Nat.mul_pos hg.1 hdpos)

run_cmd do
  for decl in [``lt_iff_le_strictEndpoint, ``strictEndpoint_mono, ``strict_prefix,
      ``halfOpen_prefix, ``physicalHigh_iff, ``physicalHigh_prefix, ``grid_prefix,
      ``inBox_iff_prefix_bounds, ``mem_survivingPrimes_iff_endpoints,
      ``grid_high_prefix, ``boxed_highKernel, ``grid_high_expansion, ``actual_grid_high_prefix] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "LITERAL GRID AND PHYSICAL HIGH PREFIX ENDPOINTS PASSED"

end ShortSingletonEndpoints
