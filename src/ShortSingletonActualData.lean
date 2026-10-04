import ShortSingletonActualBoxes

/-! Actual global support and coefficient data for the signed singleton
Fourier identity. These bounds apply to complete factor supports, every box
index and every mode; no masked subset estimate or cancellation is used. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Filter
open scoped BigOperators

namespace ShortSingletonActualData
open ShortSingletonActualBoxes ShortSingletonCollection ShortSingletonMaskedCollection
open ShortSingletonMasks ShortSingletonEndpoints ShortSingletonGeometry
open SieveWeightedCutoffs PositiveSharpBoxedCount

theorem mem_pairSupport (X s : ℝ) (p d : ℕ) :
    (p,d) ∈ pairSupport X s ↔ p ∈ largePrimes X ∧
      d ∈ SieveUpperBoxWindow.smallCarrier (level X s/p) s :=
  mem_representations _ _ p d

theorem first_support_bounds (X s : ℝ) (m : ℕ)
    (hX : 1 < X) (hs : 0 < s) (hs1 : s ≤ 1/1000) (hlog : 1000 ≤ Real.log X)
    (hm : m ∈ support (pairSupport X s)) :
    0 < m ∧ X^(9/35:ℝ) ≤ (m:ℝ) ∧ (m:ℝ) < X^(1003/2000:ℝ) ∧ (m:ℝ) ≤ X^2 := by
  obtain ⟨⟨p,d⟩,ha,rfl⟩ := Finset.mem_image.mp hm
  obtain ⟨hp,hd⟩ := (mem_pairSupport X s p d).mp ha
  have hg := actual_grouped_bounds X s p d hX hs hs1 hlog hp hd
  have hpR : 0 < ((p*d:ℕ):ℝ) :=
    (Real.rpow_pos_of_pos (by linarith : 0 < X) (9/35:ℝ)).trans_le hg.1
  have hpos : 0 < p*d := by exact_mod_cast hpR
  have hpow : X^(1003/2000:ℝ) ≤ X^2 := by
    simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_le hX.le
      (show (1003/2000:ℝ) ≤ (2:ℝ) by norm_num)
  exact ⟨hpos,hg.1,hg.2,hg.2.le.trans hpow⟩

theorem pairWeight_norm_le (X s : ℝ) (a : ℕ × ℕ) : ‖pairWeight X s a‖ ≤ 1 := by
  rw [pairWeight, Complex.norm_real, Real.norm_eq_abs]
  exact SieveSmallWeights.weight_abs_le_one _ _ _ _

theorem shortPrime_bounds (X : ℝ) (q : ℕ) (hX : 0 ≤ X) (hq : q ∈ shortPrimes X) :
    q.Prime ∧ 0 < q ∧ X^(1/25:ℝ) < (q:ℝ) ∧ (q:ℝ) ≤ X^(8/35:ℝ) ∧
      q ≤ primeCutoff X := by
  have hh := (mem_shortPrimes X q hX).mp hq
  exact ⟨hh.1,hh.1.pos,hh.2.1,hh.2.2,shortPrimes_le_cutoff X q hq⟩

theorem primeCutoff_cast_le (X : ℝ) (hX : 1 ≤ X) : (primeCutoff X:ℝ) ≤ X := by
  calc
    _ ≤ X^(8/35:ℝ) := Nat.floor_le (Real.rpow_nonneg (by linarith) _)
    _ ≤ X := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hX
        (show (8/35:ℝ) ≤ 1 by norm_num)

theorem primeCutoff_one_le (X : ℝ) (hX : 1 ≤ X) : 1 ≤ primeCutoff X := by
  apply Nat.le_floor
  simpa only [Nat.cast_one] using Real.one_le_rpow hX (by norm_num : (0:ℝ) ≤ 8/35)

theorem full_support_product_lt (X s : ℝ) (m q : ℕ)
    (hX : 1 < X) (hs : 0 < s) (hs1 : s ≤ 1/1000) (hlog : 1000 ≤ Real.log X)
    (hm : m ∈ support (pairSupport X s)) (hq : q ∈ shortPrimes X) :
    ((m*q:ℕ):ℝ) < X^(731/1000:ℝ) := by
  have hmb := first_support_bounds X s m hX hs hs1 hlog hm
  have hqb := (mem_shortPrimes X q (by linarith)).mp hq
  simpa only [Nat.cast_mul] using
    full_rectangle_product_lt X (m:ℝ) (q:ℝ) hX (Nat.cast_nonneg _) hmb.2.2.1 hqb.2.2

theorem eventually_actual_modeCoefficient_cap (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ X : ℝ in atTop, 1 < X ∧ 1000 ≤ Real.log X ∧
      ∀ (s : ℝ), 0 < s → s ≤ 1/1000 →
        ∀ (j : ℕ) (t : Mode (primeCutoff X)) (m : ℕ),
          m ∈ support (pairSupport X s) →
          ‖modeCoefficient (pairSupport X s) (primeCutoff X) t (pairWeight X s)
            (lowerEndpoint X s j) (upperEndpoint X s j) (physicalCut X) m‖ ≤ X^δ := by
  filter_upwards [eventual_modeCoefficient_cap δ hδ, eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1000:ℝ))] with X hc hX hlog
  refine ⟨hX,hlog,?_⟩
  intro s hs hs1 j t m hm
  have hmb := first_support_bounds X s m hX hs hs1 hlog hm
  exact hc.2 (pairSupport X s) (primeCutoff X) t (pairWeight X s)
    (lowerEndpoint X s j) (upperEndpoint X s j) (physicalCut X) m
    hmb.1 hmb.2.2.2 (fun a _ => pairWeight_norm_le X s a)

run_cmd do
  for decl in [``mem_pairSupport, ``first_support_bounds, ``pairWeight_norm_le,
      ``shortPrime_bounds, ``primeCutoff_cast_le, ``primeCutoff_one_le,
      ``full_support_product_lt, ``eventually_actual_modeCoefficient_cap] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ACTUAL GLOBAL SUPPORT AND UNIFORM MODE COEFFICIENT DATA PASSED"

end ShortSingletonActualData
