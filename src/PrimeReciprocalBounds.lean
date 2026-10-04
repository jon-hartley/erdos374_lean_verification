import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-! Unconditional dimension-one upper bounds for reciprocal prime intervals.
The only prime-counting input is Mathlib's proved Chebyshev estimate. -/

noncomputable section
open scoped BigOperators
open Filter MeasureTheory

namespace PrimeReciprocalBounds

def primeIndicator (n : ℕ) : ℝ := if n.Prime then 1 else 0

theorem sum_primeIndicator (x : ℝ) :
    ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, primeIndicator n = (Nat.primeCounting ⌊x⌋₊ : ℝ) := by
  rw [← Nat.primesLE_card_eq_primeCounting, Nat.primesLE_eq_filter_Icc_zero]
  simp [primeIndicator]

def openClosedPrimes (a b : ℝ) : Finset ℕ :=
  (Finset.Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime

theorem reciprocal_abel (a b : ℝ) (ha : 1 < a) (hab : a ≤ b) :
    ∑ p ∈ openClosedPrimes a b, (p : ℝ)⁻¹ =
      b⁻¹ * (Nat.primeCounting ⌊b⌋₊ : ℝ) -
        a⁻¹ * (Nat.primeCounting ⌊a⌋₊ : ℝ) +
          ∫ t in a..b, (t^2)⁻¹ * (Nat.primeCounting ⌊t⌋₊ : ℝ) := by
  have hcont : ContinuousOn (fun t : ℝ => -(t^2)⁻¹) (Set.Icc a b) := by
    fun_prop (disch := intro t ht; nlinarith [ht.1])
  have h := sum_mul_eq_sub_sub_integral_mul primeIndicator
    (f := fun t : ℝ => t⁻¹) (by linarith : 0 ≤ a) hab
    (fun t ht => (hasDerivAt_inv (by linarith [ht.1])).differentiableAt)
    (by simpa only [deriv_inv'] using hcont.integrableOn_Icc)
  simp only [sum_primeIndicator, deriv_inv, neg_mul,
    ← intervalIntegral.integral_of_le hab] at h
  simpa [openClosedPrimes, Finset.sum_filter, primeIndicator] using h

theorem count_inv_sq_integrable (a b : ℝ) (ha : 1 < a) (hab : a ≤ b) :
    IntervalIntegrable
      (fun t : ℝ => (t^2)⁻¹ * (Nat.primeCounting ⌊t⌋₊ : ℝ)) volume a b := by
  have hcont : ContinuousOn (fun t : ℝ => (t^2)⁻¹) (Set.Icc a b) := by
    fun_prop (disch := intro t ht; nlinarith [ht.1])
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
  simpa only [sum_primeIndicator] using
    integrableOn_mul_sum_Icc primeIndicator (m := 0) (by linarith : 0 ≤ a)
      hcont.integrableOn_Icc

theorem reciprocal_openClosed_le (a b : ℝ) (ha : 1 < a) (hab : a ≤ b)
    (hc : ∀ t ∈ Set.Icc a b,
      (Nat.primeCounting ⌊t⌋₊ : ℝ) ≤ 4*t / Real.log t) :
    ∑ p ∈ openClosedPrimes a b, (p : ℝ)⁻¹ ≤
      4 * (Real.log (Real.log b) - Real.log (Real.log a)) + 4 / Real.log a := by
  have hb : 1 < b := ha.trans_le hab
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hlog : ContinuousOn (fun t : ℝ => t⁻¹ / Real.log t) (Set.uIcc a b) := by
    rw [Set.uIcc_of_le hab]
    have hn : ∀ t ∈ Set.Icc a b, t ≠ 0 := fun t ht =>
      ne_of_gt (ha0.trans_le ht.1)
    exact (continuousOn_id.inv₀ hn).div (continuousOn_id.log hn)
      (fun t ht => ne_of_gt (Real.log_pos (ha.trans_le ht.1)))
  have hi := intervalIntegral.integral_mono_on hab
    (count_inv_sq_integrable a b ha hab) (hlog.const_mul 4).intervalIntegrable
    (fun t ht => show (t^2)⁻¹ * (Nat.primeCounting ⌊t⌋₊ : ℝ) ≤
      4 * (t⁻¹ / Real.log t) from calc
        _ ≤ (t^2)⁻¹ * (4*t / Real.log t) :=
          mul_le_mul_of_nonneg_left (hc t ht) (by positivity)
        _ = _ := by
          have ht0 : t ≠ 0 := by linarith [ht.1]
          field_simp)
  rw [intervalIntegral.integral_const_mul,
    integral_inv_div_log ha hb] at hi
  have hleft : 0 ≤ a⁻¹ * (Nat.primeCounting ⌊a⌋₊ : ℝ) := by positivity
  have hright : b⁻¹ * (Nat.primeCounting ⌊b⌋₊ : ℝ) ≤ 4 / Real.log b := calc
    _ ≤ b⁻¹ * (4*b / Real.log b) :=
      mul_le_mul_of_nonneg_left (hc b ⟨hab, le_rfl⟩) (by positivity)
    _ = _ := by field_simp
  have hinv : 4 / Real.log b ≤ 4 / Real.log a := by
    exact div_le_div_of_nonneg_left (by norm_num) (Real.log_pos ha)
      (Real.log_le_log ha0 hab)
  rw [reciprocal_abel a b ha hab]
  linarith

theorem eventual_primeCounting_bound :
    ∃ W : ℝ, 2 ≤ W ∧ ∀ x : ℝ, W ≤ x →
      (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ 4*x / Real.log x := by
  obtain ⟨W, hW⟩ := eventually_atTop.1
    (Chebyshev.eventually_primeCounting_le (by norm_num : (0 : ℝ) < 1))
  refine ⟨max 2 W, le_max_left _ _, fun x hx => ?_⟩
  have hx2 : 2 ≤ x := (le_max_left _ _).trans hx
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  refine (hW x ((le_max_right _ _).trans hx)).trans ?_
  apply div_le_div_of_nonneg_right _ hlog.le
  apply mul_le_mul_of_nonneg_right _ (by linarith)
  have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
  linarith

/-- Including the lower endpoint costs at most `1/log a`.  No upper-endpoint
primality convention or interval rounding is imposed on the finite set. -/
theorem sum_le_openClosed_add (S : Finset ℕ) (a b : ℝ) (ha : 1 < a)
    (hS : ∀ p ∈ S, p.Prime ∧ a ≤ (p : ℝ) ∧ (p : ℝ) ≤ b) :
    ∑ p ∈ S, (p : ℝ)⁻¹ ≤
      (∑ p ∈ openClosedPrimes a b, (p : ℝ)⁻¹) + 1 / Real.log a := by
  have ha0 : 0 ≤ a := by linarith
  have hsub : S ⊆ insert ⌊a⌋₊ (openClosedPrimes a b) := by
    intro p hp
    obtain ⟨hpp, hpa, hpb⟩ := hS p hp
    by_cases he : p = ⌊a⌋₊
    · simp [he]
    · apply Finset.mem_insert_of_mem
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_Ioc.mpr ⟨?_, Nat.le_floor hpb⟩, hpp⟩
      have hfloor : ⌊a⌋₊ ≤ p := by
        exact_mod_cast (Nat.floor_le ha0).trans hpa
      omega
  have hnot : ⌊a⌋₊ ∉ openClosedPrimes a b := by
    simp [openClosedPrimes]
  have hlog : Real.log a ≤ (⌊a⌋₊ : ℝ) := by
    have h1 := Real.log_le_sub_one_of_pos (by linarith : 0 < a)
    have h2 := Nat.lt_floor_add_one a
    linarith
  have hi : (⌊a⌋₊ : ℝ)⁻¹ ≤ 1 / Real.log a := by
    simpa only [one_div] using one_div_le_one_div_of_le (Real.log_pos ha) hlog
  calc
    _ ≤ ∑ p ∈ insert ⌊a⌋₊ (openClosedPrimes a b), (p : ℝ)⁻¹ :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => by positivity)
    _ = (⌊a⌋₊ : ℝ)⁻¹ + ∑ p ∈ openClosedPrimes a b, (p : ℝ)⁻¹ :=
      Finset.sum_insert hnot
    _ ≤ _ := by linarith

/-- A single absolute threshold works for every finite prime set and every pair
of enclosing real endpoints.  This is unconditional: Chebyshev supplies the
prime-counting estimate used in partial summation. -/
theorem eventual_reciprocal_interval_bound :
    ∃ W : ℝ, 2 ≤ W ∧ ∀ (a b : ℝ) (S : Finset ℕ), W ≤ a → a ≤ b →
      (∀ p ∈ S, p.Prime ∧ a ≤ (p : ℝ) ∧ (p : ℝ) ≤ b) →
      ∑ p ∈ S, (p : ℝ)⁻¹ ≤
        4 * Real.log (Real.log b / Real.log a) + 5 / Real.log a := by
  obtain ⟨W, hW2, hW⟩ := eventual_primeCounting_bound
  refine ⟨W, hW2, fun a b S ha hab hS => ?_⟩
  have ha1 : 1 < a := by linarith
  have hb1 : 1 < b := ha1.trans_le hab
  have hi := reciprocal_openClosed_le a b ha1 hab
    (fun t ht => hW t (ha.trans ht.1))
  have hs := sum_le_openClosed_add S a b ha1 hS
  rw [Real.log_div (ne_of_gt (Real.log_pos hb1)) (ne_of_gt (Real.log_pos ha1))]
  simp only [div_eq_mul_inv] at hi hs ⊢
  linarith

/-- The convenient common constant `5` version. -/
theorem eventual_reciprocal_interval_bound_five :
    ∃ W : ℝ, 2 ≤ W ∧ ∀ (a b : ℝ) (S : Finset ℕ), W ≤ a → a ≤ b →
      (∀ p ∈ S, p.Prime ∧ a ≤ (p : ℝ) ∧ (p : ℝ) ≤ b) →
      ∑ p ∈ S, (p : ℝ)⁻¹ ≤
        5 * (Real.log (Real.log b / Real.log a) + 1 / Real.log a) := by
  obtain ⟨W, hW2, hW⟩ := eventual_reciprocal_interval_bound
  refine ⟨W, hW2, fun a b S ha hab hS => ?_⟩
  have ha1 : 1 < a := by linarith
  have hl : 0 ≤ Real.log (Real.log b / Real.log a) := by
    apply Real.log_nonneg
    exact (one_le_div (Real.log_pos ha1)).2
      (Real.log_le_log (by linarith) hab)
  have := hW a b S ha hab hS
  simp only [div_eq_mul_inv] at this hl ⊢
  linarith

/-- Uniform in the band location and ratio: the threshold is absolute, before
`u`, `a`, `q`, and the actual prime set. -/
theorem eventual_reciprocal_geometric_bound :
    ∃ W : ℝ, 2 ≤ W ∧ ∀ (u a q : ℝ) (S : Finset ℕ), W ≤ u → u ≤ a → 1 ≤ q →
      (∀ p ∈ S, p.Prime ∧ a ≤ (p : ℝ) ∧ (p : ℝ) ≤ a^q) →
      ∑ p ∈ S, (p : ℝ)⁻¹ ≤ 4 * Real.log q + 5 / Real.log u := by
  obtain ⟨W, hW2, hW⟩ := eventual_reciprocal_interval_bound
  refine ⟨W, hW2, fun u a q S hu hua hq hS => ?_⟩
  have hu1 : 1 < u := by linarith
  have ha1 : 1 < a := hu1.trans_le hua
  have haa : a ≤ a^q := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le ha1.le hq
  have hi := hW a (a^q) S (hu.trans hua) haa hS
  rw [Real.log_rpow (by linarith : 0 < a), mul_div_cancel_right₀ _
    (ne_of_gt (Real.log_pos ha1))] at hi
  have hinv : 5 / Real.log a ≤ 5 / Real.log u :=
    div_le_div_of_nonneg_left (by norm_num) (Real.log_pos hu1)
      (Real.log_le_log (by linarith) hua)
  linarith

#print axioms reciprocal_openClosed_le
#print axioms eventual_primeCounting_bound
#print axioms eventual_reciprocal_interval_bound_five
#print axioms eventual_reciprocal_geometric_bound
run_cmd do
  for decl in [``sum_primeIndicator, ``reciprocal_abel, ``count_inv_sq_integrable,
    ``reciprocal_openClosed_le, ``eventual_primeCounting_bound, ``sum_le_openClosed_add,
    ``eventual_reciprocal_interval_bound, ``eventual_reciprocal_interval_bound_five,
    ``eventual_reciprocal_geometric_bound] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"

end PrimeReciprocalBounds
end
