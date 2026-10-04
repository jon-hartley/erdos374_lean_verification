import SieveStoppingForcing
import SieveFiniteBase
import SieveStoppingArithmeticContraction

/-! Strong induction on the actual prime-pool cardinality assembles the finite
base case, rejected-gate forcing estimate, and arithmetic operator contraction
into exponential decay of the actual normalized lower stopping loss. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace SieveStoppingDecay
open SieveStoppingExpansion SieveStoppingRecurrence SieveStoppingTwoStep

def baseCutoff : ℝ := Real.exp (100000*PrimeEulerDimensionOne.errorConstant)
def decayConstant : ℝ :=
  max (SieveFiniteBase.exponentialConstant baseCutoff) (200*(100*Real.exp 4))

theorem decayConstant_pos : 0 < decayConstant :=
  lt_of_lt_of_le (SieveFiniteBase.exponentialConstant_pos baseCutoff) (le_max_left _ _)

theorem errorConstant_ge_twelve : 12 ≤ PrimeEulerDimensionOne.errorConstant := by
  have hlog : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  have he : 1 ≤ Real.exp (12/Real.log (2:ℝ)) := by
    calc
      (1:ℝ) = Real.exp 0 := by simp
      _ ≤ _ := Real.exp_le_exp.mpr (by positivity)
  unfold PrimeEulerDimensionOne.errorConstant
  linarith

theorem large_cutoff_conditions (z : ℝ) (hz : 2 ≤ z) (hlarge : baseCutoff < z) :
    64 ≤ z ∧ 100000*PrimeEulerDimensionOne.errorConstant ≤ Real.log z ∧
      SieveStoppingForcing.epsilon z ≤ 1 := by
  have hlog := Real.log_le_log (Real.exp_pos (100000*PrimeEulerDimensionOne.errorConstant)) hlarge.le
  simp only [Real.log_exp] at hlog
  have hlogz : 0 < Real.log z := Real.log_pos (by linarith)
  have hk := errorConstant_ge_twelve
  have hzlog := Real.log_le_sub_one_of_pos (by linarith : 0 < z)
  refine ⟨by linarith, hlog, ?_⟩
  unfold SieveStoppingForcing.epsilon
  apply (div_le_iff₀ hlogz).mpr
  nlinarith

theorem child_pool_card_lt (z : ℝ) (p q : ℕ)
    (hp : p ∈ SieveSmallWeights.pool z) (hq : q ∈ SieveSmallWeights.pool (p:ℝ)) :
    (SieveSmallWeights.pool (q:ℝ)).card < (SieveSmallWeights.pool z).card := by
  obtain ⟨_, hpz⟩ := (SieveSmallWeights.mem_pool z p).mp hp
  obtain ⟨hqp, hqp_lt⟩ := (SieveSmallWeights.mem_pool (p:ℝ) q).mp hq
  have hqz := hqp_lt.trans hpz
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨SieveFiniteBase.pool_mono (q:ℝ) z hqz.le, ?_⟩
  intro heq
  have hm : q ∈ SieveSmallWeights.pool z := (SieveSmallWeights.mem_pool z q).mpr ⟨hqp, hqz⟩
  rw [← heq] at hm
  exact lt_irrefl (q:ℝ) ((SieveSmallWeights.mem_pool (q:ℝ) q).mp hm).2

theorem accepted_child_level (T : ℝ) (p q : ℕ)
    (hq : q ∈ SieveSmallWeights.pool (p:ℝ)) (hgate : (q:ℝ)^3 < T/(p:ℝ)) :
    2 ≤ (q:ℝ) ∧ (q:ℝ)^2 ≤ (T/(p:ℝ))/(q:ℝ) := by
  have hqp := ((SieveSmallWeights.mem_pool (p:ℝ) q).mp hq).1
  have hq0 : (0:ℝ) < q := by exact_mod_cast hqp.pos
  refine ⟨by exact_mod_cast hqp.two_le, le_of_lt ?_⟩
  apply (lt_div_iff₀ hq0).mpr
  simpa only [pow_succ] using hgate

theorem operator_bound_of_children (T z C : ℝ)
    (hchild : ∀ p ∈ SieveSmallWeights.pool z, ∀ q ∈ SieveSmallWeights.pool (p:ℝ),
      (q:ℝ)^3 < T/(p:ℝ) →
      normalizedLower ((T/(p:ℝ))/(q:ℝ)) (q:ℝ) ≤
        C*Real.exp (-(Real.log ((T/(p:ℝ))/(q:ℝ)) / Real.log (q:ℝ)))) :
    operator normalizedLower T z ≤
      C*operator (fun T z => Real.exp (-(Real.log T / Real.log z))) T z := by
  unfold operator
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro q hq
  split_ifs with hgate
  · have hw : 0 ≤ (p:ℝ)⁻¹*(q:ℝ)⁻¹*primeEuler (q:ℝ)/primeEuler z :=
      div_nonneg (mul_nonneg (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg p))
        (inv_nonneg.mpr (Nat.cast_nonneg q))) (SieveEulerRatio.euler_pos _).le)
        (SieveEulerRatio.euler_pos _).le
    have hm := mul_le_mul_of_nonneg_left (hchild p hp q hq hgate) hw
    convert hm using 1
    ring
  · simp

/-- The only input here is the arithmetic contraction of the exact operator.
The later unconditional corollary supplies it from the proved prime estimates. -/
theorem lower_decay_from_contraction
    (hcontract : ∀ T z : ℝ, 64 ≤ z → z^2 ≤ T →
      100000*PrimeEulerDimensionOne.errorConstant ≤ Real.log z →
      operator (fun T z => Real.exp (-(Real.log T / Real.log z))) T z ≤
        (199/200)*Real.exp (-(Real.log T / Real.log z)))
    (T z : ℝ) (hz : 2 ≤ z) (hT : z^2 ≤ T) :
    normalizedLower T z ≤ decayConstant*Real.exp (-(Real.log T / Real.log z)) := by
  have hind : ∀ n : ℕ, ∀ z T : ℝ, (SieveSmallWeights.pool z).card = n →
      2 ≤ z → z^2 ≤ T →
      normalizedLower T z ≤ decayConstant*Real.exp (-(Real.log T / Real.log z)) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro z T hn hz hT
      by_cases hsmall : z ≤ baseCutoff
      · have hb := (SieveFiniteBase.finite_cutoff_exponential T z baseCutoff hz hsmall hT).1
        exact hb.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
          (Real.exp_pos _).le)
      · obtain ⟨hz64, hlog, heps⟩ := large_cutoff_conditions z hz (lt_of_not_ge hsmall)
        have hchild : ∀ p ∈ SieveSmallWeights.pool z, ∀ q ∈ SieveSmallWeights.pool (p:ℝ),
            (q:ℝ)^3 < T/(p:ℝ) →
            normalizedLower ((T/(p:ℝ))/(q:ℝ)) (q:ℝ) ≤
              decayConstant*Real.exp (-(Real.log ((T/(p:ℝ))/(q:ℝ)) / Real.log (q:ℝ))) := by
          intro p hp q hq hg
          obtain ⟨hq2, hqT⟩ := accepted_child_level T p q hq hg
          have hcard : (SieveSmallWeights.pool (q:ℝ)).card < n := by
            rw [← hn]
            exact child_pool_card_lt z p q hp hq
          exact ih _ hcard (q:ℝ) ((T/(p:ℝ))/(q:ℝ)) rfl hq2 hqT
        have hop := (operator_bound_of_children T z decayConstant hchild).trans
          (mul_le_mul_of_nonneg_left (hcontract T z hz64 hT hlog) decayConstant_pos.le)
        have hf := SieveStoppingForcing.forcing_exponential T z hz64 hT heps
        have hc : 200*(100*Real.exp 4) ≤ decayConstant := le_max_right _ _
        have hcoeff : 100*Real.exp 4+decayConstant*(199/200) ≤ decayConstant := by linarith
        calc
          normalizedLower T z = forcing T z+operator normalizedLower T z := normalizedLower_two_step T z
          _ ≤ (100*Real.exp 4)*Real.exp (-(Real.log T/Real.log z)) +
              decayConstant*((199/200)*Real.exp (-(Real.log T/Real.log z))) := add_le_add hf hop
          _ = (100*Real.exp 4+decayConstant*(199/200))*
              Real.exp (-(Real.log T/Real.log z)) := by ring
          _ ≤ decayConstant*Real.exp (-(Real.log T/Real.log z)) :=
            mul_le_mul_of_nonneg_right hcoeff (Real.exp_pos _).le
  exact hind _ z T rfl hz hT

theorem normalizedLower_bound (T z : ℝ) (hz : 2 ≤ z) (hT : z^2 ≤ T) :
    normalizedLower T z ≤ decayConstant*Real.exp (-(Real.log T/Real.log z)) :=
  lower_decay_from_contraction
    (fun T z hz64 hT hlog => SieveStoppingArithmeticContraction.operator_exponential_le T z hz64 hT hlog)
    T z hz hT

theorem exists_lower_decay : ∃ C : ℝ, 0 < C ∧ ∀ T z : ℝ, 2 ≤ z → z^2 ≤ T →
    lowerLoss T z/primeEuler z ≤ C*Real.exp (-(Real.log T/Real.log z)) :=
  ⟨decayConstant, decayConstant_pos, fun T z hz hT => normalizedLower_bound T z hz hT⟩

run_cmd do
  for decl in [``baseCutoff, ``decayConstant, ``decayConstant_pos,
      ``errorConstant_ge_twelve, ``large_cutoff_conditions, ``child_pool_card_lt,
      ``accepted_child_level, ``operator_bound_of_children, ``lower_decay_from_contraction,
      ``normalizedLower_bound, ``exists_lower_decay] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "UNCONDITIONAL ACTUAL NORMALIZED LOWER EXPONENTIAL DECAY PASSED"

end SieveStoppingDecay
end
