import SieveUpperBoxing
import SieveBoxedWindow
import SieveUpperSelectedWindow

/-! Actual upper boxed coefficients and their literal finite-window identity.
No analytic estimate of the main term or signed remainder is asserted. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open scoped BigOperators
namespace SieveUpperBoxWindow
open SieveUpperBoxing

def smallCarrier (D s : ℝ) : Finset ℕ :=
  SieveVectorConvolution.carrier (SieveRosser.cubicGate (D^s)) 1
    (SieveSmallWeights.primes (D^(s^2)))
def support (D s z : ℝ) : Finset ℕ :=
  SieveTupleConvolution.signedSupport (smallCarrier D s) (outerFamily D s z) (innerFamily D s z)
def coefficient (D s z : ℝ) : ℕ → ℝ :=
  SieveTupleConvolution.signedCoefficient (smallCarrier D s)
    (SieveSmallWeights.weight (D^s) (D^(s^2)) true)
    (SieveSmallWeights.weight (D^s) (D^(s^2)) false)
    (outerFamily D s z) (innerFamily D s z)
def mainTerm (D s z : ℝ) : ℝ :=
  SieveBoxedWindow.smallMass D s true * (∑ t ∈ outerFamily D s z, 1/(t.prod : ℝ)) -
    SieveBoxedWindow.smallMass D s false * (∑ t ∈ innerFamily D s z, 1/(t.prod : ℝ))
def remainder (D s z L R : ℝ) : ℝ :=
  HarmanDivisorWindow.remainder (support D s z) (coefficient D s z) L R

theorem tuple_entries (D s z : ℝ) (hD : 1 < D) (hs : 0 < s) :
    ∀ t ∈ outerFamily D s z ∪ innerFamily D s z, ∀ p ∈ t,
      p ∈ SieveBoxedFamily.pool D s z := by
  intro t ht p hp
  rcases Finset.mem_union.mp ht with ho | hi
  · exact ((mem_outerFamily D s z hD hs t).mp ho).1 p hp
  · exact ((mem_innerFamily D s z hD hs t).mp hi).1 p hp

theorem carrier_coprime (D s z : ℝ) (hD : 1 < D) (hs : 0 < s) :
    ∀ d ∈ smallCarrier D s,
      ∀ m ∈ SieveTupleConvolution.tupleCarrier (outerFamily D s z) (innerFamily D s z),
        d.Coprime m := by
  apply SieveTupleConvolution.carrier_coprime_tuples
    (SieveRosser.cubicGate (D^s)) 1 (SieveSmallWeights.primes (D^(s^2)))
    (SieveBoxedFamily.pool D s z) _ _ (SieveSmallWeights.primes_prime _)
    (fun p hp => ((SieveBoxedFamily.mem_pool D s z p).mp hp).1) ?_
    (tuple_entries D s z hD hs)
  apply Finset.disjoint_left.mpr
  intro p hp hq
  have hsmall := (SieveSmallWeights.mem_primes (D^(s^2)) p).mp (List.mem_toFinset.mp hp)
  exact (not_lt_of_ge ((SieveBoxedFamily.mem_pool D s z p).mp hq).2.2) hsmall.2

theorem support_positive (D s z : ℝ) (hD : 1 < D) (hs : 0 < s) :
    ∀ m ∈ support D s z, 0 < m :=
  SieveTupleConvolution.signedSupport_positive _ _ _
    (SieveVectorConvolution.carrier_positive _ _ _ (SieveSmallWeights.primes_prime _))
    (fun t ht p hp => ((SieveBoxedFamily.mem_pool D s z p).mp
      (tuple_entries D s z hD hs t ht p hp)).1.pos)

theorem literal_evaluation (D s z : ℝ) (hD : 1 < D) (hs : 0 < s) (n : ℕ) :
    SieveDivisorWindow.evaluation (support D s z) (coefficient D s z) n =
      upperEvaluation D s z n := by
  unfold support coefficient
  rw [SieveTupleConvolution.signed_evaluation _ _ _ _ _ (carrier_coprime D s z hD hs)]
  change SieveDivisorWindow.evaluation (smallCarrier D s)
      (SieveSelectedWindow.coefficient (SieveRosser.cubicGate (D^s)) true 1
        (SieveSmallWeights.primes (D^(s^2)))) n * _ -
    SieveDivisorWindow.evaluation (smallCarrier D s)
      (SieveSelectedWindow.coefficient (SieveRosser.cubicGate (D^s)) false 1
        (SieveSmallWeights.primes (D^(s^2)))) n * _ = _
  rw [smallCarrier, SieveVectorConvolution.evaluation_carrier,
    SieveVectorConvolution.evaluation_carrier]
  rfl

theorem reciprocal_mass (D s z : ℝ) :
    HarmanDivisorWindow.reciprocalMass (support D s z) (coefficient D s z) =
      mainTerm D s z := by
  unfold support coefficient
  rw [SieveTupleConvolution.signed_reciprocal_mass]
  change HarmanDivisorWindow.reciprocalMass (smallCarrier D s)
      (SieveSelectedWindow.coefficient (SieveRosser.cubicGate (D^s)) true 1
        (SieveSmallWeights.primes (D^(s^2)))) * _ -
    HarmanDivisorWindow.reciprocalMass (smallCarrier D s)
      (SieveSelectedWindow.coefficient (SieveRosser.cubicGate (D^s)) false 1
        (SieveSmallWeights.primes (D^(s^2)))) * _ = _
  rw [smallCarrier, SieveVectorConvolution.mass_carrier, SieveVectorConvolution.mass_carrier]
  rfl

theorem literal_kernel (D s z : ℝ) (f : ℕ → ℝ) :
    (∑ m ∈ support D s z, coefficient D s z m*f m) =
      (∑ d ∈ smallCarrier D s, ∑ t ∈ outerFamily D s z,
        SieveSmallWeights.weight (D^s) (D^(s^2)) true d*f (d*t.prod)) -
      ∑ d ∈ smallCarrier D s, ∑ t ∈ innerFamily D s z,
        SieveSmallWeights.weight (D^s) (D^(s^2)) false d*f (d*t.prod) :=
  SieveTupleConvolution.signed_kernel _ _ _ _ _ f

theorem indicator_le_literal (D s z : ℝ) (hD : 1 < D) (hs : 0 < s)
    (hz : z ≤ D) (huz : D^(s^2) ≤ z) (n : ℕ) :
    SieveDivisorWindow.indicator (SieveSmallWeights.pool z) n ≤
      SieveDivisorWindow.evaluation (support D s z) (coefficient D s z) n := by
  rw [literal_evaluation D s z hD hs]
  exact indicator_le_upperEvaluation D s z hD hs hz huz n

theorem sum_evaluation_eq_main_add_remainder (D s z : ℝ) (hD : 1 < D) (hs : 0 < s)
    (L R : ℝ) (hL : 0 ≤ L) (hLR : L ≤ R) :
    (∑ n ∈ FiniteSieveWindow.window L R,
      SieveDivisorWindow.evaluation (support D s z) (coefficient D s z) n) =
      (R-L)*mainTerm D s z+remainder D s z L R := by
  rw [SieveDivisorWindow.sum_evaluation_eq_main_add_remainder _ _ L R
    (support_positive D s z hD hs) hL hLR, reciprocal_mass]
  rfl

theorem remainder_eq_sum (D s z L R : ℝ) :
    remainder D s z L R = ∑ d ∈ support D s z, coefficient D s z d *
      (((⌊R/d⌋₊ : ℝ)-(⌊L/d⌋₊ : ℝ))-(R-L)/d) := by
  unfold remainder HarmanDivisorWindow.remainder HarmanDivisorWindow.divisorCount
    HarmanDivisorWindow.reciprocalMass
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  ring

theorem sifted_count_le (D s z : ℝ) (hD : 1 < D) (hs : 0 < s)
    (hz : z ≤ D) (huz : D^(s^2) ≤ z) (L R : ℝ) (hL : 0 ≤ L) (hLR : L ≤ R) :
    ((SieveDivisorWindow.siftedWindow (SieveSmallWeights.pool z) L R).card : ℝ) ≤
      (R-L)*mainTerm D s z+remainder D s z L R := by
  rw [← sum_evaluation_eq_main_add_remainder D s z hD hs L R hL hLR,
    ← SieveDivisorWindow.sum_indicator_eq_card]
  exact Finset.sum_le_sum (fun n _ => indicator_le_literal D s z hD hs hz huz n)

theorem prime_count_le (D s z : ℝ) (hD : 1 < D) (hs : 0 < s)
    (hz : z ≤ D) (huz : D^(s^2) ≤ z) (L R : ℝ) (hL : 0 ≤ L)
    (hLR : L ≤ R) (hzL : z ≤ L) :
    ((FiniteSieveWindow.primeWindow L R).card : ℝ) ≤
      (R-L)*mainTerm D s z+remainder D s z L R := by
  have hc : ((FiniteSieveWindow.primeWindow L R).card : ℝ) ≤
      ((SieveDivisorWindow.siftedWindow (SieveSmallWeights.pool z) L R).card : ℝ) := by
    exact_mod_cast Finset.card_le_card
      (SieveUpperSelectedWindow.primeWindow_subset_sifted z L R hL hLR hzL)
  exact hc.trans (sifted_count_le D s z hD hs hz huz L R hL hLR)

run_cmd do
  for decl in [``tuple_entries, ``carrier_coprime, ``support_positive,
      ``literal_evaluation, ``reciprocal_mass, ``literal_kernel, ``indicator_le_literal,
      ``sum_evaluation_eq_main_add_remainder, ``remainder_eq_sum, ``sifted_count_le,
      ``prime_count_le] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ACTUAL UPPER BOX WINDOW; LITERAL SIGNED REMAINDER RETAINED"
end SieveUpperBoxWindow
end
