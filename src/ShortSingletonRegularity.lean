import ShortSingletonActualBoxes
import ShortSingletonWeightedModes

/-! An exact real divisor remainder for the literal signed singleton sector.
This provides integrability of the function and its square independently of
the analytic bound. Its coefficients retain every box, phase and collision. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace ShortSingletonRegularity
open ShortSingletonMasks ShortSingletonCollection ShortSingletonMaskedCollection
open ShortSingletonComplex ShortSingletonWeightedModes ShortSingletonActualBoxes
open ShortSingletonSector ShortSingletonBoxes ShortSingletonEndpoints

def divisorSupport (X s : ℝ) : Finset ℕ :=
  FactoredDivisorWeights.support (support (pairSupport X s)) (shortPrimes X)

def divisorCoefficient (X s : ℝ) (n : ℕ) : ℝ :=
  -(∑ j ∈ acceptedIndices s, ∑ t : Mode (primeCutoff X),
    realCoefficient (support (pairSupport X s)) (shortPrimes X)
      (fun m => scalar (primeCutoff X) t *
        modeCoefficient (pairSupport X s) (primeCutoff X) t (pairWeight X s)
          (lowerEndpoint X s j) (upperEndpoint X s j) (physicalCut X) m)
      (rightPhase (primeCutoff X) t) n)

theorem singleton_eq_remainder (X s L R : ℝ)
    (hX : 1 < X) (hs : 0 < s) (hs1 : s ≤ 1/1000) (hlog : 1000 ≤ Real.log X) :
    singletonRemainder X s L R = HarmanDivisorWindow.remainder
      (divisorSupport X s) (divisorCoefficient X s) L R := by
  have hh := congrArg Complex.re (singleton_floor_eq_modes X s L R hX hs hs1 hlog)
  simp only [Complex.ofReal_re, Complex.neg_re, Complex.re_sum] at hh
  rw [hh]
  simp_rw [←productSum_mul_left, productSum_re_remainder]
  simp only [HarmanDivisorWindow.remainder_eq_sum, divisorSupport, divisorCoefficient,
    neg_mul, Finset.sum_mul, Finset.sum_neg_distrib]
  congr 1
  simp_rw [Finset.sum_comm (s := Finset.univ)
    (t := FactoredDivisorWeights.support (support (pairSupport X s)) (shortPrimes X))]
  rw [Finset.sum_comm]

theorem moving_integrable (X s Y : ℝ)
    (hX : 1 < X) (hs : 0 < s) (hs1 : s ≤ 1/1000) (hlog : 1000 ≤ Real.log X) :
    IntegrableOn (fun x => singletonRemainder X s (x-x*(Y/X)) x) (Icc X (2*X)) := by
  have he : (fun x => singletonRemainder X s (x-x*(Y/X)) x) =
      (fun x => HarmanDivisorWindow.remainder (divisorSupport X s)
        (divisorCoefficient X s) (x-x*(Y/X)) x) := by
    funext x
    exact singleton_eq_remainder X s _ _ hX hs hs1 hlog
  rw [he]
  simpa only [mul_div_assoc] using
    TailRemainderBand.moving_remainder_integrable (divisorSupport X s) (divisorCoefficient X s) X Y

theorem moving_square_integrable (X s Y : ℝ)
    (hX : 1 < X) (hs : 0 < s) (hs1 : s ≤ 1/1000) (hlog : 1000 ≤ Real.log X)
    (hY : 0 ≤ Y) (hYX : Y ≤ X) :
    IntegrableOn (fun x => singletonRemainder X s (x-x*(Y/X)) x ^ 2) (Icc X (2*X)) := by
  have he : (fun x => singletonRemainder X s (x-x*(Y/X)) x ^ 2) =
      (fun x => HarmanDivisorWindow.remainder (divisorSupport X s)
        (divisorCoefficient X s) (x-x*(Y/X)) x ^ 2) := by
    funext x
    rw [singleton_eq_remainder X s _ _ hX hs hs1 hlog]
  rw [he]
  exact SignedDivisorRegularity.integrable_remainder_square (divisorSupport X s)
    (divisorCoefficient X s) X (Y/X) (by linarith)
    ⟨div_nonneg hY (by linarith), (div_le_one (by linarith : 0<X)).mpr hYX⟩

run_cmd do
  for decl in [``singleton_eq_remainder, ``moving_integrable, ``moving_square_integrable] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "LITERAL SINGLETON REAL DIVISOR REPRESENTATION AND MOVING REGULARITY PASSED"

end ShortSingletonRegularity
