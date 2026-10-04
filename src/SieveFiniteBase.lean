import SieveStoppingTwoStep
import SieveFiniteSaturation

/-! Coarse finite-selector bounds and an explicit bounded-cutoff exponential
base case. The constant is allowed to depend on the fixed cutoff. This does
not supply uniform control as the cutoff tends to infinity. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace SieveFiniteBase
open SieveStoppingExpansion SieveStoppingRecurrence

theorem euler_le_one (ps : List ℕ) (b : ℕ → ℝ)
    (hb : ∀ p ∈ ps, 0 ≤ b p ∧ b p ≤ 1) : SievePrefixLoss.euler ps b ≤ 1 := by
  apply Finset.prod_le_one₀
  · intro p hp
    exact sub_nonneg.mpr (hb p (List.mem_toFinset.mp hp)).2
  · intro p hp
    exact sub_le_self 1 (hb p (List.mem_toFinset.mp hp)).1

theorem loss_le_power (gate : ℕ → ℕ → Prop) (d : ℕ) (ps : List ℕ)
    (b : ℕ → ℝ) (hnd : ps.Nodup) (hb : ∀ p ∈ ps, 0 ≤ b p ∧ b p ≤ 1) :
    SievePrefixLoss.lower gate d ps b ≤ (2:ℝ)^(ps.length+1) ∧
      SievePrefixLoss.upper gate d ps b ≤ (2:ℝ)^(ps.length+1) := by
  induction ps generalizing d with
  | nil => simpa only [(SievePrefixLoss.nil_losses gate d b).1,
      (SievePrefixLoss.nil_losses gate d b).2] using
      (show (0:ℝ) ≤ 2^(List.length ([]:List ℕ)+1) ∧
        (0:ℝ) ≤ 2^(List.length ([]:List ℕ)+1) from ⟨by positivity, by positivity⟩)
  | cons p ps ih =>
    obtain ⟨hp, hn⟩ := List.nodup_cons.mp hnd
    have hbp := hb p (by simp)
    have hbt : ∀ q ∈ ps, 0 ≤ b q ∧ b q ≤ 1 := fun q hq => hb q (by simp [hq])
    have hs := ih d hn hbt
    have ht := ih (d*p) hn hbt
    have hm (x : ℝ) (hx : x ≤ (2:ℝ)^(ps.length+1)) :
        b p * x ≤ (2:ℝ)^(ps.length+1) := by
      calc
        b p * x ≤ b p * (2:ℝ)^(ps.length+1) := mul_le_mul_of_nonneg_left hx hbp.1
        _ ≤ 1 * (2:ℝ)^(ps.length+1) := mul_le_mul_of_nonneg_right hbp.2 (by positivity)
        _ = _ := one_mul _
    have he : SievePrefixLoss.euler ps b ≤ (2:ℝ)^(ps.length+1) :=
      (euler_le_one ps b hbt).trans (one_le_pow₀ (by norm_num))
    have hlen : (2:ℝ)^((p::ps).length+1) =
        (2:ℝ)^(ps.length+1) + (2:ℝ)^(ps.length+1) := by
      simp only [List.length_cons, pow_succ]
      ring
    rw [SievePrefixLoss.lower_cons gate d p ps b hp,
      SievePrefixLoss.upper_cons gate d p ps b hp, hlen]
    constructor
    · exact add_le_add hs.1 (hm _ ht.2)
    · split_ifs
      · exact add_le_add hs.2 (hm _ ht.1)
      · exact add_le_add hs.2 (hm _ he)

theorem absolute_loss_le_power (gate : ℕ → ℕ → Prop) (d : ℕ) (ps : List ℕ)
    (b : ℕ → ℝ) (hnd : ps.Nodup) (hb : ∀ p ∈ ps, 0 ≤ b p ∧ b p ≤ 1) :
    |SievePrefixLoss.lower gate d ps b| ≤ (2:ℝ)^(ps.length+1) ∧
      |SievePrefixLoss.upper gate d ps b| ≤ (2:ℝ)^(ps.length+1) := by
  obtain ⟨hl, hu⟩ := SievePrefixLoss.nonnegative gate d ps b hnd hb
  rw [abs_of_nonneg hl, abs_of_nonneg hu]
  exact loss_le_power gate d ps b hnd hb

theorem pool_mono (a b : ℝ) (hab : a ≤ b) :
    SieveSmallWeights.pool a ⊆ SieveSmallWeights.pool b := by
  intro p hp
  obtain ⟨hpp, hpa⟩ := (SieveSmallWeights.mem_pool a p).mp hp
  exact (SieveSmallWeights.mem_pool b p).mpr ⟨hpp, hpa.trans_le hab⟩

theorem prime_length_mono (a b : ℝ) (hab : a ≤ b) :
    (SieveSmallWeights.primes a).length ≤ (SieveSmallWeights.primes b).length := by
  simpa only [SieveSmallWeights.primes, Finset.length_sort] using
    Finset.card_le_card (pool_mono a b hab)

theorem euler_antitone (a b : ℝ) (hab : a ≤ b) : primeEuler b ≤ primeEuler a := by
  simp only [primeEuler, SievePrefixLoss.euler, SieveSmallWeights.primes_toFinset]
  apply Finset.prod_le_prod_of_subset_of_le_one₀ (pool_mono a b hab)
  · intro p hp
    apply sub_nonneg.mpr
    apply inv_le_one_of_one_le₀
    exact_mod_cast ((SieveSmallWeights.mem_pool b p).mp hp).1.one_le
  · intro p hp _
    exact sub_le_self 1 (inv_nonneg.mpr (Nat.cast_nonneg p))

def lossBound (z₀ : ℝ) : ℝ :=
  (2:ℝ)^((SieveSmallWeights.primes z₀).length+1) / primeEuler z₀

theorem lossBound_pos (z₀ : ℝ) : 0 < lossBound z₀ :=
  div_pos (by positivity) (SieveEulerRatio.euler_pos z₀)

theorem normalized_losses_le (T z z₀ : ℝ) (hzz : z ≤ z₀) :
    lowerLoss T z / primeEuler z ≤ lossBound z₀ ∧
      upperLoss T z / primeEuler z ≤ lossBound z₀ := by
  have hb := loss_le_power (SieveRosser.cubicGate T) 1 (SieveSmallWeights.primes z)
    (fun p => (p:ℝ)⁻¹) (SieveSmallWeights.primes_nodup z)
    (SieveReciprocalModel.reciprocal_in_unit_interval _ (SieveSmallWeights.primes_prime z))
  have hp : (2:ℝ)^((SieveSmallWeights.primes z).length+1) ≤
      (2:ℝ)^((SieveSmallWeights.primes z₀).length+1) :=
    pow_le_pow_right₀ (by norm_num) (Nat.add_le_add_right (prime_length_mono z z₀ hzz) 1)
  have bound (x : ℝ) (hx : x ≤ (2:ℝ)^((SieveSmallWeights.primes z).length+1)) :
      x / primeEuler z ≤ lossBound z₀ := by
    calc
      x / primeEuler z ≤ (2:ℝ)^((SieveSmallWeights.primes z₀).length+1) / primeEuler z :=
        div_le_div_of_nonneg_right (hx.trans hp) (SieveEulerRatio.euler_pos z).le
      _ ≤ lossBound z₀ := div_le_div_of_nonneg_left (by positivity)
        (SieveEulerRatio.euler_pos z₀) (euler_antitone z z₀ hzz)
  exact ⟨bound _ hb.1, bound _ hb.2⟩

def saturationLevel (z₀ : ℝ) : ℝ :=
  max 4 ((((SieveSmallWeights.primes z₀).prod^3 : ℕ):ℝ) + 1)

def logRange (z₀ : ℝ) : ℝ := Real.log (saturationLevel z₀) / Real.log 2

def exponentialConstant (z₀ : ℝ) : ℝ := lossBound z₀ * Real.exp (logRange z₀)

theorem exponentialConstant_pos (z₀ : ℝ) : 0 < exponentialConstant z₀ :=
  mul_pos (lossBound_pos z₀) (Real.exp_pos _)

theorem ratio_le_logRange (T z z₀ : ℝ) (hT : 1 ≤ T) (hz : 2 ≤ z)
    (hlevel : T ≤ saturationLevel z₀) : Real.log T / Real.log z ≤ logRange z₀ := by
  have hlog2 : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  have hlogz : Real.log (2:ℝ) ≤ Real.log z := Real.log_le_log (by norm_num) hz
  calc
    Real.log T / Real.log z ≤ Real.log T / Real.log 2 :=
      div_le_div_of_nonneg_left (Real.log_nonneg hT) hlog2 hlogz
    _ ≤ logRange z₀ := div_le_div_of_nonneg_right
      (Real.log_le_log (by linarith) hlevel) hlog2.le

theorem bounded_ratio_exponential (z₀ r : ℝ) (hr : r ≤ logRange z₀) :
    lossBound z₀ ≤ exponentialConstant z₀ * Real.exp (-r) := by
  unfold exponentialConstant
  rw [mul_assoc, ← Real.exp_add]
  apply le_mul_of_one_le_right (lossBound_pos z₀).le
  calc
    (1:ℝ) = Real.exp 0 := by simp
    _ ≤ Real.exp (logRange z₀ + -r) := Real.exp_le_exp.mpr (by linarith)

theorem finite_cutoff_exponential (T z z₀ : ℝ) (hz : 2 ≤ z) (hzz : z ≤ z₀)
    (hT : z^2 ≤ T) :
    lowerLoss T z / primeEuler z ≤
        exponentialConstant z₀ * Real.exp (-(Real.log T / Real.log z)) ∧
      upperLoss T z / primeEuler z ≤
        exponentialConstant z₀ * Real.exp (-(Real.log T / Real.log z)) := by
  by_cases hlevel : T < saturationLevel z₀
  · have hT1 : 1 ≤ T := by nlinarith [sq_nonneg (z-2)]
    have he := bounded_ratio_exponential z₀ (Real.log T / Real.log z)
      (ratio_le_logRange T z z₀ hT1 hz hlevel.le)
    obtain ⟨hl, hu⟩ := normalized_losses_le T z z₀ hzz
    exact ⟨hl.trans he, hu.trans he⟩
  · have hp : (((SieveSmallWeights.primes z₀).prod^3 : ℕ):ℝ) < T := by
      have hmax : ((((SieveSmallWeights.primes z₀).prod^3 : ℕ):ℝ) + 1) ≤
          saturationLevel z₀ := le_max_right _ _
      linarith [le_of_not_gt hlevel]
    obtain ⟨hl, hu⟩ := SieveFiniteSaturation.uniform_finite_cutoff T z z₀ hzz hp
    rw [hl, hu, zero_div]
    have hpos := (mul_pos (exponentialConstant_pos z₀)
      (Real.exp_pos (-(Real.log T / Real.log z)))).le
    exact ⟨hpos, hpos⟩

run_cmd do
  for decl in [``euler_le_one, ``loss_le_power, ``absolute_loss_le_power,
      ``pool_mono, ``prime_length_mono, ``euler_antitone, ``lossBound,
      ``lossBound_pos, ``normalized_losses_le, ``saturationLevel, ``logRange,
      ``exponentialConstant, ``exponentialConstant_pos, ``ratio_le_logRange,
      ``bounded_ratio_exponential, ``finite_cutoff_exponential] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "FINITE-CUTOFF ACTUAL NORMALIZED EXPONENTIAL BASE CASE PASSED"

end SieveFiniteBase
end
