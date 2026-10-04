import SieveCompleteBoxing
import SieveTupleConvolution

/-! The actual complete finite boxed coefficient, its exact reciprocal model,
and its literal interval remainder. No positivity of the model is assumed or
concluded; this is the finite construction-to-analytic-interface bridge. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped BigOperators

namespace SieveBoxedWindow
open SieveCompleteBoxing

def support (D s z : ℝ) : Finset ℕ :=
  SieveTupleConvolution.smallSupport (D^s) (D^(s^2)) (innerFamily D s z) (outerFamily D s z)

def coefficient (D s z : ℝ) : ℕ → ℝ :=
  SieveTupleConvolution.smallCoefficient (D^s) (D^(s^2)) (innerFamily D s z) (outerFamily D s z)

def smallMass (D s : ℝ) (upper : Bool) : ℝ :=
  HarmanDivisorWindow.reciprocalMass (SieveSmallWeights.support (D^s) (D^(s^2)) upper)
    (SieveSmallWeights.weight (D^s) (D^(s^2)) upper)

def mainTerm (D s z : ℝ) : ℝ :=
  smallMass D s false * (∑ t ∈ innerFamily D s z, 1/(t.prod : ℝ)) -
    smallMass D s true * (∑ t ∈ outerFamily D s z, 1/(t.prod : ℝ))

/-- The source's minus-R convention, for this very same constructed coefficient. -/
def sourceRemainder (D s z L R : ℝ) : ℝ :=
  -HarmanDivisorWindow.remainder (support D s z) (coefficient D s z) L R

theorem tuple_entries (D s z : ℝ) (hD : 1 < D) (hs : 0 < s) :
    ∀ t ∈ innerFamily D s z ∪ outerFamily D s z, ∀ p ∈ t,
      p.Prime ∧ D^(s^2) ≤ (p : ℝ) := by
  intro t ht p hpt
  have hp : p ∈ SieveBoxedFamily.pool D s z := by
    rcases Finset.mem_union.mp ht with hi | ho
    · exact ((mem_innerFamily D s z hD hs t).mp hi).1 p hpt
    · exact ((mem_outerFamily D s z hD hs t).mp ho).1 p hpt
  have hh := (SieveBoxedFamily.mem_pool D s z p).mp hp
  exact ⟨hh.1, hh.2.2⟩

theorem support_positive (D s z : ℝ) (hD : 1 < D) (hs : 0 < s) :
    ∀ m ∈ support D s z, 0 < m :=
  SieveTupleConvolution.smallSupport_positive (D^s) (D^(s^2)) _ _
    (fun t ht p hp => (tuple_entries D s z hD hs t ht p hp).1)

theorem literal_evaluation (D s z : ℝ) (hD : 1 < D) (hs : 0 < s) (n : ℕ) :
    SieveDivisorWindow.evaluation (support D s z) (coefficient D s z) n =
      lowerEvaluation D s z n := by
  exact SieveTupleConvolution.small_evaluation (D^s) (D^(s^2)) _ _
    (tuple_entries D s z hD hs) n

theorem reciprocal_mass (D s z : ℝ) :
    HarmanDivisorWindow.reciprocalMass (support D s z) (coefficient D s z) =
      mainTerm D s z :=
  SieveTupleConvolution.small_reciprocal_mass (D^s) (D^(s^2)) _ _

/-- Exact all-representation kernel identity; arbitrary kernels need no arithmetic hypotheses. -/
theorem literal_kernel (D s z : ℝ) (f : ℕ → ℝ) :
    (∑ m ∈ support D s z, coefficient D s z m * f m) =
      (∑ d ∈ SieveVectorConvolution.carrier (SieveRosser.cubicGate (D^s)) 1
          (SieveSmallWeights.primes (D^(s^2))),
        ∑ t ∈ innerFamily D s z, SieveSmallWeights.weight (D^s) (D^(s^2)) false d *
          f (d*t.prod)) -
      ∑ d ∈ SieveVectorConvolution.carrier (SieveRosser.cubicGate (D^s)) 1
          (SieveSmallWeights.primes (D^(s^2))),
        ∑ t ∈ outerFamily D s z, SieveSmallWeights.weight (D^s) (D^(s^2)) true d *
          f (d*t.prod) :=
  SieveTupleConvolution.signed_kernel _ _ _ _ _ f

theorem literal_le_indicator (D s z : ℝ) (hD : 1 < D) (hs : 0 < s)
    (hz : z ≤ D) (huz : D^(s^2) ≤ z) (n : ℕ) :
    SieveDivisorWindow.evaluation (support D s z) (coefficient D s z) n ≤
      SieveDivisorWindow.indicator (SieveSmallWeights.pool z) n := by
  rw [literal_evaluation D s z hD hs]
  exact lowerEvaluation_le_indicator D s z hD hs hz huz n

/-- The plus-remainder identity uses the literal floor-count remainder of the
constructed coefficient, not a replacement model or chosen error term. -/
theorem sum_evaluation_eq_main_add_remainder (D s z : ℝ) (hD : 1 < D) (hs : 0 < s)
    (L R : ℝ) (hL : 0 ≤ L) (hLR : L ≤ R) :
    (∑ n ∈ FiniteSieveWindow.window L R,
      SieveDivisorWindow.evaluation (support D s z) (coefficient D s z) n) =
      (R-L)*mainTerm D s z +
        HarmanDivisorWindow.remainder (support D s z) (coefficient D s z) L R := by
  rw [SieveDivisorWindow.sum_evaluation_eq_main_add_remainder _ _ L R
    (support_positive D s z hD hs) hL hLR, reciprocal_mass]

theorem main_add_remainder_le_count (D s z : ℝ) (hD : 1 < D) (hs : 0 < s)
    (hz : z ≤ D) (huz : D^(s^2) ≤ z) (L R : ℝ) (hL : 0 ≤ L) (hLR : L ≤ R) :
    (R-L)*mainTerm D s z +
        HarmanDivisorWindow.remainder (support D s z) (coefficient D s z) L R ≤
      ((SieveDivisorWindow.siftedWindow (SieveSmallWeights.pool z) L R).card : ℝ) := by
  rw [← sum_evaluation_eq_main_add_remainder D s z hD hs L R hL hLR,
    ← SieveDivisorWindow.sum_indicator_eq_card]
  exact Finset.sum_le_sum (fun n _ => literal_le_indicator D s z hD hs hz huz n)

theorem source_main_sub_remainder_eq_sum (D s z : ℝ) (hD : 1 < D) (hs : 0 < s)
    (L R : ℝ) (hL : 0 ≤ L) (hLR : L ≤ R) :
    (R-L)*mainTerm D s z - sourceRemainder D s z L R =
      ∑ n ∈ FiniteSieveWindow.window L R, lowerEvaluation D s z n := by
  simp only [sourceRemainder, sub_neg_eq_add]
  rw [← sum_evaluation_eq_main_add_remainder D s z hD hs L R hL hLR]
  exact Finset.sum_congr rfl (fun n _ => literal_evaluation D s z hD hs n)

theorem source_main_sub_remainder_le_count (D s z : ℝ) (hD : 1 < D) (hs : 0 < s)
    (hz : z ≤ D) (huz : D^(s^2) ≤ z) (L R : ℝ) (hL : 0 ≤ L) (hLR : L ≤ R) :
    (R-L)*mainTerm D s z - sourceRemainder D s z L R ≤
      ((SieveDivisorWindow.siftedWindow (SieveSmallWeights.pool z) L R).card : ℝ) := by
  simpa only [sourceRemainder, sub_neg_eq_add] using
    main_add_remainder_le_count D s z hD hs hz huz L R hL hLR

#print axioms reciprocal_mass
#print axioms source_main_sub_remainder_le_count
run_cmd do
  for decl in [``tuple_entries, ``support_positive, ``literal_evaluation, ``reciprocal_mass,
    ``literal_kernel, ``literal_le_indicator, ``sum_evaluation_eq_main_add_remainder,
    ``main_add_remainder_le_count, ``source_main_sub_remainder_eq_sum,
    ``source_main_sub_remainder_le_count] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
run_cmd Lean.logInfo "ACTUAL BOXED WINDOW BRIDGE PASSED; POSITIVE MAIN TERM NOT ASSERTED"

end SieveBoxedWindow
end

