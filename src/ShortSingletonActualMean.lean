import ShortSingletonGlobalMean
import ShortSingletonActualData
import ShortSingletonRegularity
import TripleFirstMean

/-! A positive-power second mean and every fixed inverse-log absolute first
mean for the literal large-band short inner singleton sector. Other upper
tuple sectors and the full Mangoldt source residual remain separate. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators

namespace ShortSingletonActualMean
open ShortSingletonSector ShortSingletonActualBoxes ShortSingletonActualData
open ShortSingletonBoxes ShortSingletonEndpoints ShortSingletonMaskedCollection
open ShortSingletonRegularity PositiveSharpPowerWindow

def absoluteMean (X s Y : ℝ) : ℝ :=
  (1/X)*(∫ x in Icc X (2*X), |singletonRemainder X s (x-x*(Y/X)) x|)

theorem square_eq_masked (X s L R : ℝ)
    (hX : 1 < X) (hs : 0 < s) (hs1 : s ≤ 1/1000) (hlog : 1000 ≤ Real.log X) :
    singletonRemainder X s L R ^ 2 =
      (∑ j ∈ acceptedIndices s, boxMaskedSum X s j L R).re ^ 2 := by
  have hh := congrArg Complex.re (singleton_floor_eq_masked X s L R hX hs hs1 hlog)
  simp only [Complex.ofReal_re, Complex.neg_re] at hh
  rw [hh, neg_sq]

theorem eventually_square_bound (s : ℝ) (hs : 0 < s) (hs1 : s ≤ 1/1000) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℝ in atTop, 1 < X ∧ 1000 ≤ Real.log X ∧
      let Y := halfWidth X (101/1000)
      (1/X)*(∫ x in Icc X (2*X), singletonRemainder X s (x-x*(Y/X)) x ^ 2) ≤
        Y^2*X^(-c) := by
  obtain ⟨c,hc,hmean⟩ := ShortSingletonGlobalMean.eventually_bound (acceptedIndices s)
  refine ⟨c,hc,?_⟩
  filter_upwards [hmean, eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1000)] with X hm hX hlog
  refine ⟨hX,hlog,?_⟩
  dsimp only
  have hS : ∀ m ∈ ShortSingletonCollection.support (pairSupport X s),
      X^(9/35:ℝ) ≤ (m:ℝ) ∧ (m:ℝ) < X^(1003/2000:ℝ) := by
    intro m hm
    have hb := first_support_bounds X s m hX hs hs1 hlog hm
    exact ⟨hb.2.1,hb.2.2.1⟩
  have hB : ∀ q ∈ shortPrimes X, X^(1/25:ℝ) < (q:ℝ) ∧ (q:ℝ) ≤ X^(8/35:ℝ) := by
    intro q hq
    exact ((mem_shortPrimes X q (by linarith)).mp hq).2
  have hb := hm.2 (pairSupport X s) (shortPrimes X) (primeCutoff X) (pairWeight X s)
    (lowerEndpoint X s) (upperEndpoint X s) (physicalCut X) hS hB
    (fun q hq => shortPrimes_le_cutoff X q hq) (primeCutoff_cast_le X hX.le)
    (fun a _ => pairWeight_norm_le X s a)
  have he : (fun x => singletonRemainder X s (x-x*(halfWidth X (101/1000)/X)) x ^ 2) =
      (fun x => (∑ j ∈ acceptedIndices s,
        boxMaskedSum X s j (x-x*(halfWidth X (101/1000)/X)) x).re ^ 2) := by
    funext x
    exact square_eq_masked X s _ _ hX hs hs1 hlog
  rw [he]
  exact hb

theorem eventually_absolute_power (s : ℝ) (hs : 0 < s) (hs1 : s ≤ 1/1000) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℝ in atTop, 1 < X ∧ 1000 ≤ Real.log X ∧
      absoluteMean X s (halfWidth X (101/1000)) ≤ halfWidth X (101/1000)*X^(-c) := by
  obtain ⟨c,hc,hmean⟩ := eventually_square_bound s hs hs1
  refine ⟨c/2,by positivity,?_⟩
  filter_upwards [hmean, halfWidth_eventually (101/1000) (by norm_num)] with X hm hY
  have hXp : 0 < X := by linarith [hm.1]
  let Y := halfWidth X (101/1000)
  have hYX : Y ≤ X := by have hh := hY.2; linarith
  have hsq : (1/X)*(∫ x in Icc X (2*X), singletonRemainder X s (x-x*(Y/X)) x ^ 2) ≤
      (Y*X^(-(c/2)))^2 := by
    have he : (Y*X^(-(c/2)))^2 = Y^2*X^(-c) := by
      rw [mul_pow, ←Real.rpow_mul_natCast hXp.le]
      congr 2
      norm_num
    rw [he]
    exact hm.2.2
  refine ⟨hm.1,hm.2.1,?_⟩
  exact TripleFirstMean.absolute_mean_le _ X (Y*X^(-(c/2))) hXp
    (mul_pos hY.1 (Real.rpow_pos_of_pos hXp _))
    (moving_integrable X s Y hm.1 hs hs1 hm.2.1)
    (moving_square_integrable X s Y hm.1 hs hs1 hm.2.1 hY.1.le hYX) hsq

theorem eventually_absolute_log (s : ℝ) (A : ℕ) (hs : 0 < s) (hs1 : s ≤ 1/1000) :
    ∀ᶠ X : ℝ in atTop, 1 < X ∧ 1000 ≤ Real.log X ∧
      absoluteMean X s (halfWidth X (101/1000)) ≤
        halfWidth X (101/1000)/(Real.log X)^A := by
  obtain ⟨c,hc,hpower⟩ := eventually_absolute_power s hs hs1
  filter_upwards [hpower, PolynomialLogEnvelope.eventually_bound 1 A c (by norm_num) hc,
    halfWidth_eventually (101/1000) (by norm_num)] with X hb he hY
  have hXp : 0 < X := by linarith [hb.1]
  have hl : 0 < Real.log X := Real.log_pos hb.1
  have hlog : (Real.log X)^A ≤ X^c := by
    apply le_trans _ he.2
    simp only [one_mul]
    exact pow_le_pow_left₀ hl.le (by linarith) A
  have hunit : X^(-c)*(Real.log X)^A ≤ 1 := by
    calc
      _ ≤ X^(-c)*X^c := mul_le_mul_of_nonneg_left hlog (by positivity)
      _ = 1 := by rw [←Real.rpow_add hXp]; simp
  refine ⟨hb.1,hb.2.1,hb.2.2.trans ?_⟩
  apply (le_div_iff₀ (pow_pos hl A)).mpr
  have hh := mul_le_mul_of_nonneg_left hunit hY.1.le
  nlinarith

run_cmd do
  for decl in [``square_eq_masked, ``eventually_square_bound,
      ``eventually_absolute_power, ``eventually_absolute_log] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "ACTUAL LARGE SHORT INNER SINGLETON SECOND MEAN AND EVERY FIXED LOG FIRST MEAN PASSED"

end ShortSingletonActualMean
