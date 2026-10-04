import ShortSingletonCollection
import Mathlib.Data.Fintype.BigOperators

/-! Collection of ordered representations without discarding collisions.
An injective, product-preserving encoding by k ordered factors bounds every
fiber by the k-th power of the divisor count. The encoding is an explicit
hypothesis, so this file does not yet assert an actual upper-family adapter. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace LongerTupleCollection

variable {α : Type*}

def support (S : Finset α) (index : α → ℕ) : Finset ℕ := S.image index

def coefficient (S : Finset α) (index : α → ℕ) (w : α → ℂ) (n : ℕ) : ℂ :=
  ∑ a ∈ S.filter (fun a => index a = n), w a

theorem fiber_card_le (k : ℕ) (S : Finset α) (index : α → ℕ)
    (encode : α → Fin k → ℕ)
    (hprod : ∀ a ∈ S, index a = ∏ i, encode a i)
    (hinj : Set.InjOn encode (S : Set α)) (n : ℕ) (hn : n ≠ 0) :
    (S.filter (fun a => index a = n)).card ≤ n.divisors.card ^ k := by
  rw [← Fintype.card_piFinset_const n.divisors k]
  apply Finset.card_le_card_of_injOn encode
  · intro a ha
    obtain ⟨ha, he⟩ := Finset.mem_filter.mp ha
    apply Fintype.mem_piFinset.mpr
    intro i
    apply Nat.mem_divisors.mpr
    refine ⟨?_, hn⟩
    rw [← he, hprod a ha]
    exact Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  · intro a ha b hb hab
    exact hinj (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp hb).1 hab

theorem coefficient_norm_le (k : ℕ) (S : Finset α) (index : α → ℕ)
    (encode : α → Fin k → ℕ)
    (hprod : ∀ a ∈ S, index a = ∏ i, encode a i)
    (hinj : Set.InjOn encode (S : Set α)) (w : α → ℂ)
    (hw : ∀ a ∈ S, ‖w a‖ ≤ 1) (n : ℕ) (hn : n ≠ 0) :
    ‖coefficient S index w n‖ ≤ (n.divisors.card : ℝ) ^ k := by
  calc
    _ ≤ ∑ a ∈ S.filter (fun a => index a = n), ‖w a‖ := norm_sum_le _ _
    _ ≤ ∑ _a ∈ S.filter (fun a => index a = n), (1 : ℝ) :=
      Finset.sum_le_sum (fun a ha => hw a (Finset.mem_filter.mp ha).1)
    _ = ((S.filter (fun a => index a = n)).card : ℝ) := by simp
    _ ≤ _ := by exact_mod_cast fiber_card_le k S index encode hprod hinj n hn

theorem coefficient_zero_off_support (S : Finset α) (index : α → ℕ)
    (w : α → ℂ) (n : ℕ) (hn : n ∉ support S index) :
    coefficient S index w n = 0 := by
  apply Finset.sum_eq_zero
  intro a ha
  obtain ⟨ha, he⟩ := Finset.mem_filter.mp ha
  exact False.elim (hn (Finset.mem_image.mpr ⟨a, ha, he⟩))

theorem grouped_sum (S : Finset α) (index : α → ℕ) (w : α → ℂ) (f : ℕ → ℂ) :
    (∑ n ∈ support S index, coefficient S index w n * f n) =
      ∑ a ∈ S, w a * f (index a) := by
  unfold coefficient
  simp_rw [Finset.sum_mul]
  have hh := Finset.sum_fiberwise_of_maps_to
    (fun a (ha : a ∈ S) => show index a ∈ support S index from
      Finset.mem_image.mpr ⟨a, ha, rfl⟩)
    (fun a => w a * f (index a))
  rw [← hh]
  apply Finset.sum_congr rfl
  intro n _
  apply Finset.sum_congr rfl
  intro a ha
  rw [(Finset.mem_filter.mp ha).2]

theorem eventually_divisor_cap (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ X : ℝ in atTop, 1 ≤ X ∧
      ∀ n : ℕ, (n : ℝ) ≤ X^2 → (n.divisors.card : ℝ) ≤ X^δ := by
  obtain ⟨D, hD, hdiv⟩ := DivisorPowerBound.divisor_count_bound (δ/4) (by positivity)
  filter_upwards [PolynomialLogEnvelope.eventually_constant_bound D (δ/2)
    hD.le (by positivity)] with X hX
  refine ⟨hX.1, ?_⟩
  intro n hnX
  have hXp : 0 < X := by linarith [hX.1]
  have hp : (n : ℝ)^(δ/4) ≤ X^(δ/2) := by
    calc
      _ ≤ (X^2)^(δ/4) := Real.rpow_le_rpow (Nat.cast_nonneg n) hnX (by positivity)
      _ = _ := by rw [← Real.rpow_natCast_mul hXp.le]; congr 1; ring
  calc
    _ ≤ D*(n:ℝ)^(δ/4) := hdiv n
    _ ≤ X^(δ/2)*X^(δ/2) := mul_le_mul hX.2 hp (by positivity) (by positivity)
    _ = X^δ := by rw [← Real.rpow_add hXp]; congr 1; ring

theorem eventually_divisor_power_cap (k : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ X : ℝ in atTop, 1 ≤ X ∧
      ∀ n : ℕ, (n : ℝ) ≤ X^2 → (n.divisors.card : ℝ)^k ≤ X^δ := by
  have hk : (0 : ℝ) < k + 1 := by positivity
  filter_upwards [eventually_divisor_cap (δ / (k+1)) (div_pos hδ hk)] with X hX
  refine ⟨hX.1, ?_⟩
  intro n hnX
  calc
    _ ≤ (X^(δ / (k+1)))^k := pow_le_pow_left₀ (by positivity) (hX.2 n hnX) k
    _ = X^((δ / (k+1)) * k) := (Real.rpow_mul_natCast (by linarith [hX.1]) _ _).symm
    _ ≤ X^δ := by
      apply Real.rpow_le_rpow_of_exponent_le hX.1
      have hle : (k : ℝ) ≤ k+1 := by linarith
      calc
        δ / (k+1) * k ≤ δ / (k+1) * (k+1) :=
          mul_le_mul_of_nonneg_left hle (by positivity)
        _ = δ := div_mul_cancel₀ _ (ne_of_gt hk)

theorem eventual_coefficient_cap (k : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ X : ℝ in atTop, 1 ≤ X ∧
      ∀ (S : Finset α) (index : α → ℕ) (encode : α → Fin k → ℕ) (w : α → ℂ),
        (∀ a ∈ S, index a = ∏ i, encode a i) →
        Set.InjOn encode (S : Set α) → (∀ a ∈ S, ‖w a‖ ≤ 1) →
        ∀ n : ℕ, 0 < n → (n : ℝ) ≤ X^2 → ‖coefficient S index w n‖ ≤ X^δ := by
  filter_upwards [eventually_divisor_power_cap k δ hδ] with X hX
  refine ⟨hX.1, ?_⟩
  intro S index encode w hprod hinj hw n hn hnX
  exact (coefficient_norm_le k S index encode hprod hinj w hw n (by omega)).trans
    (hX.2 n hnX)

/-- A direct specialization retaining the full ordered factor vector. -/
theorem ordered_fiber_card_le (k : ℕ) (S : Finset (Fin k → ℕ)) (n : ℕ) (hn : n ≠ 0) :
    (S.filter (fun a => (∏ i, a i) = n)).card ≤ n.divisors.card^k := by
  exact fiber_card_le k S (fun a => ∏ i, a i) id (fun _ _ => rfl)
    (fun _ _ _ _ h => h) n hn

run_cmd do
  for decl in [``fiber_card_le, ``coefficient_norm_le, ``coefficient_zero_off_support,
      ``grouped_sum, ``eventually_divisor_cap, ``eventually_divisor_power_cap,
      ``eventual_coefficient_cap, ``ordered_fiber_card_le] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ORDERED REPRESENTATION COLLECTION AND DIVISOR-POWER CAP PASSED"

end LongerTupleCollection
