import SieveProfileTailScalar

/-! Exact scalar budget for the proposed upper-term route. These statements
are real inequalities, not estimates for any arithmetic sieve family.
All arithmetic transfers and profile hypotheses remain separate. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Real
namespace SieveSignedScalarBudget

theorem log_twenty_six_ninths : log (26/9:ℝ) ≤ (17/16:ℝ) := by
  apply (log_le_iff_le_exp (by norm_num)).mpr
  have h := sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 17/16) 6
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith

theorem log_eighteen_seventeenths : log (18/17:ℝ) ≤ (1/17:ℝ) := by
  have h := log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 18/17)
  linarith

def negativeBudget (A : ℝ) : ℝ :=
  (3+A)*((26/105)*log (26/9)+(2/9)*log (18/17))

theorem negative_budget_le (A : ℝ) (hA0 : 0 ≤ A) (hA : A ≤ 77/125) :
    negativeBudget A ≤ (1336903/1338750:ℝ) := by
  have hb : (26/105:ℝ)*log (26/9)+(2/9)*log (18/17) ≤ 11831/42840 := by
    linarith [log_twenty_six_ninths, log_eighteen_seventeenths]
  unfold negativeBudget
  calc
    _ ≤ (3+A)*(11831/42840) := mul_le_mul_of_nonneg_left hb (by linarith)
    _ ≤ (3+77/125)*(11831/42840) := by nlinarith
    _ = _ := by norm_num

theorem negative_budget_gap (A : ℝ) (hA0 : 0 ≤ A) (hA : A ≤ 77/125) :
    negativeBudget A+(1847/1338750:ℝ) ≤ 1 := by
  linarith [negative_budget_le A hA0 hA]

theorem proposed_area_allowances :
    (3068866243439/5000000000000:ℝ)+1/10000+1/1000 ≤ 77/125 := by
  norm_num

theorem sharp_signed_margin :
    (104/1875:ℝ)-53589103/1000000000 = 5632691/3000000000 := by
  norm_num

/-- A scalar implication only: the three signed-family estimates here
are hypotheses, not supplied arithmetic sieve estimates. -/
theorem signed_positive_of_estimates (V y s e a b c : ℝ)
    (hV : 0 < V) (hy : 0 < y) (hs : s ≤ 1/1000) (he : e ≤ 1/10000)
    (ha : (946410897/1000000000-e)*y*V ≤ a)
    (hb : b ≤ (1+e)*y*V)
    (hc : ((104/1875)*(1-3*s)-e)*y*V ≤ c) :
    (1/1000)*y*V < a-b+c := by
  have hcoef : (1/1000:ℝ) <
      (946410897/1000000000-e)-(1+e)+((104/1875)*(1-3*s)-e) := by
    linarith
  have hmul := mul_lt_mul_of_pos_right
    (mul_lt_mul_of_pos_right hcoef hy) hV
  nlinarith

run_cmd do
  for decl in [``log_twenty_six_ninths, ``log_eighteen_seventeenths,
      ``negative_budget_le, ``negative_budget_gap, ``proposed_area_allowances,
      ``sharp_signed_margin, ``signed_positive_of_estimates] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "SCALAR SIGNED BUDGET CHECKED; ARITHMETIC FAMILY ESTIMATES REMAIN EXPLICIT"
end SieveSignedScalarBudget
end
