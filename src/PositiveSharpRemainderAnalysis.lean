import SieveTupleConvolution
import SieveBoxedFamily
import DivisorPowerBound

/-! All-length collected coefficients, preserving every tuple representation.
This provides an arithmetic multiplicity bound, not a mean-square estimate
or a separable factorization of the accepted tuple family. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace PositiveSharpRemainderAnalysis

def representations (S : Finset ℕ) (T : Finset (List ℕ)) (m : ℕ) :
    Finset (ℕ × List ℕ) :=
  (S ×ˢ T).filter (fun a => a.1 * a.2.prod = m)

def collected (S : Finset ℕ) (w : ℕ → ℝ) (T : Finset (List ℕ)) (m : ℕ) : ℝ :=
  ∑ a ∈ representations S T m, w a.1

theorem collected_eq_convolution (S R : Finset ℕ) (w : ℕ → ℝ)
    (T : Finset (List ℕ)) (hR : SieveTupleConvolution.tupleSupport T ⊆ R) (m : ℕ) :
    collected S w T m =
      FactoredDivisorWeights.coefficient S R w
        (SieveTupleConvolution.tupleCoefficient T) m := by
  symm
  calc
    _ = ∑ d ∈ S, ∑ k ∈ R, SieveTupleConvolution.tupleCoefficient T k *
        (if d * k = m then w d else 0) := by
      unfold FactoredDivisorWeights.coefficient
      rw [Finset.sum_filter, Finset.sum_product]
      simp only [DirichletProductCoefficients.productIndex]
      apply Finset.sum_congr rfl
      intro d _
      apply Finset.sum_congr rfl
      intro k _
      by_cases h : d*k=m <;> simp [h, mul_comm]
    _ = ∑ d ∈ S, ∑ t ∈ T, if d * t.prod = m then w d else 0 := by
      apply Finset.sum_congr rfl
      intro d _
      exact SieveTupleConvolution.tuple_kernel_on T R hR _
    _ = _ := by simp only [collected, representations, Finset.sum_filter, Finset.sum_product]

theorem tupleLists_card_le (P : Finset ℕ) (r : ℕ) :
    (SieveBoxTuples.tupleLists P r).card ≤ P.card ^ r := by
  induction r with
  | zero => simp [SieveBoxTuples.tupleLists]
  | succ r ih =>
      calc
        _ ≤ ∑ p ∈ P, ((SieveBoxTuples.tupleLists P r).image (List.cons p)).card :=
          Finset.card_biUnion_le
        _ ≤ ∑ _p ∈ P, P.card ^ r := Finset.sum_le_sum (fun _ _ =>
          (Finset.card_image_le).trans ih)
        _ = _ := by simp [pow_succ, mul_comm]

theorem boundedTuples_card_le (P : Finset ℕ) (K : ℕ) (hP : 1 ≤ P.card) :
    (SieveBoxedFamily.boundedTuples P K).card ≤ (K + 1) * P.card ^ K := by
  calc
    _ ≤ ∑ r ∈ Finset.range (K+1), (SieveBoxTuples.tupleLists P r).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _r ∈ Finset.range (K+1), P.card ^ K := by
      apply Finset.sum_le_sum
      intro r hr
      exact (tupleLists_card_le P r).trans
        (pow_le_pow_right₀ hP (by have := Finset.mem_range.mp hr; omega))
    _ = _ := by simp

/-- The small divisor is an additional coordinate. No distinctness is used. -/
theorem representations_card_le (S : Finset ℕ) (T : Finset (List ℕ))
    (K m : ℕ) (hm : m ≠ 0) (hK : ∀ t ∈ T, t.length ≤ K) :
    (representations S T m).card ≤ (K+2) * m.divisors.card ^ (K+1) := by
  have hinj : Set.InjOn (fun a : ℕ × List ℕ => a.1 :: a.2)
      (↑(representations S T m) : Set (ℕ × List ℕ)) := by
    intro a _ b _ hab
    exact Prod.ext (List.cons.inj hab).1 (List.cons.inj hab).2
  have hmap : Set.MapsTo (fun a : ℕ × List ℕ => a.1 :: a.2)
      (↑(representations S T m) : Set (ℕ × List ℕ))
      (↑(SieveBoxedFamily.boundedTuples m.divisors (K+1)) : Set (List ℕ)) := by
    intro a ha
    obtain ⟨ha, he⟩ := Finset.mem_filter.mp ha
    apply (SieveBoxedFamily.mem_boundedTuples _ _ _).mpr
    refine ⟨by simpa using Nat.succ_le_succ (hK a.2 (Finset.mem_product.mp ha).2), ?_⟩
    intro p hp
    apply Nat.mem_divisors.mpr
    refine ⟨?_, hm⟩
    have hp' := List.dvd_prod hp
    simpa only [List.prod_cons, he] using hp'
  have hcard : 1 ≤ m.divisors.card :=
    Finset.one_le_card.mpr ⟨1, Nat.one_mem_divisors.mpr hm⟩
  exact (Finset.card_le_card_of_injOn _ hmap hinj).trans
    (by simpa only [Nat.add_assoc] using boundedTuples_card_le m.divisors (K+1) hcard)

theorem collected_abs_le (S : Finset ℕ) (w : ℕ → ℝ) (T : Finset (List ℕ))
    (K m : ℕ) (hm : m ≠ 0) (hK : ∀ t ∈ T, t.length ≤ K)
    (hw : ∀ d ∈ S, |w d| ≤ 1) :
    |collected S w T m| ≤ ((K+2 : ℕ) : ℝ) * (m.divisors.card : ℝ) ^ (K+1) := by
  calc
    _ ≤ ∑ a ∈ representations S T m, |w a.1| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a ∈ representations S T m, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro a ha
      exact hw a.1 (Finset.mem_product.mp (Finset.mem_filter.mp ha).1).1
    _ = ((representations S T m).card : ℝ) := by simp
    _ ≤ _ := by exact_mod_cast representations_card_le S T K m hm hK

theorem signedCoefficient_abs_le (S : Finset ℕ) (l u : ℕ → ℝ)
    (I O : Finset (List ℕ)) (K m : ℕ) (hm : m ≠ 0)
    (hI : ∀ t ∈ I, t.length ≤ K) (hO : ∀ t ∈ O, t.length ≤ K)
    (hl : ∀ d ∈ S, |l d| ≤ 1) (hu : ∀ d ∈ S, |u d| ≤ 1) :
    |SieveTupleConvolution.signedCoefficient S l u I O m| ≤
      2 * ((K+2 : ℕ) : ℝ) * (m.divisors.card : ℝ) ^ (K+1) := by
  rw [SieveTupleConvolution.signedCoefficient,
    ← collected_eq_convolution S _ l I
      (SieveTupleConvolution.support_subset_tupleCarrier_left I O),
    ← collected_eq_convolution S _ u O
      (SieveTupleConvolution.support_subset_tupleCarrier_right I O)]
  have hi := collected_abs_le S l I K m hm hI hl
  have ho := collected_abs_le S u O K m hm hO hu
  have ht := abs_sub (collected S l I m) (collected S u O m)
  linarith

/-- For each fixed length cap, every positive power absorbs multiplicity.
The constant may depend on the length cap and the chosen exponent. -/
theorem signedCoefficient_power_bound (K : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset ℕ) (l u : ℕ → ℝ)
      (I O : Finset (List ℕ)) (m : ℕ), m ≠ 0 →
      (∀ t ∈ I, t.length ≤ K) → (∀ t ∈ O, t.length ≤ K) →
      (∀ d ∈ S, |l d| ≤ 1) → (∀ d ∈ S, |u d| ≤ 1) →
      |SieveTupleConvolution.signedCoefficient S l u I O m| ≤ C * (m : ℝ)^ε := by
  have hk : (0 : ℝ) < K+1 := by positivity
  obtain ⟨D, hD, hbound⟩ := DivisorPowerBound.divisor_count_bound
    (ε / (K+1)) (div_pos hε hk)
  refine ⟨2 * ((K+2 : ℕ) : ℝ) * D^(K+1), by positivity, ?_⟩
  intro S l u I O m hm hI hO hl hu
  have hp := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ m.divisors.card)
    (hbound m) (K+1)
  have he : ((m : ℝ) ^ (ε / (K+1))) ^ (K+1) = (m : ℝ)^ε := by
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg m)]
    congr 1
    push_cast
    exact div_mul_cancel₀ ε hk.ne'
  rw [mul_pow, he] at hp
  calc
    _ ≤ 2 * ((K+2 : ℕ) : ℝ) * (m.divisors.card : ℝ)^(K+1) :=
      signedCoefficient_abs_le S l u I O K m hm hI hO hl hu
    _ ≤ 2 * ((K+2 : ℕ) : ℝ) * (D^(K+1) * (m : ℝ)^ε) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ = _ := by ring

/-- Uniformity in the actual families is retained. The length cap is fixed
before the eventual ambient threshold; the index restriction stays explicit. -/
theorem eventually_signedCoefficient_cap (K : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ X : ℝ in Filter.atTop, 1 ≤ X ∧
      ∀ (S : Finset ℕ) (l u : ℕ → ℝ) (I O : Finset (List ℕ)) (m : ℕ),
        m ≠ 0 → (m : ℝ) ≤ X^(2 : ℕ) →
        (∀ t ∈ I, t.length ≤ K) → (∀ t ∈ O, t.length ≤ K) →
        (∀ d ∈ S, |l d| ≤ 1) → (∀ d ∈ S, |u d| ≤ 1) →
        |SieveTupleConvolution.signedCoefficient S l u I O m| ≤ X^ε := by
  obtain ⟨C, hC, hbound⟩ := signedCoefficient_power_bound K (ε/4) (by positivity)
  filter_upwards [PolynomialLogEnvelope.eventually_constant_bound C (ε/2)
    hC.le (by positivity)] with X hX
  refine ⟨hX.1, ?_⟩
  intro S l u I O m hm hmX hI hO hl hu
  have hXp : 0 < X := by linarith [hX.1]
  have hp : (m : ℝ)^(ε/4) ≤ X^(ε/2) := by
    calc
      _ ≤ (X^(2 : ℕ))^(ε/4) := Real.rpow_le_rpow (Nat.cast_nonneg m) hmX (by positivity)
      _ = _ := by rw [← Real.rpow_natCast_mul hXp.le]; congr 1; ring
  calc
    _ ≤ C * (m : ℝ)^(ε/4) := hbound S l u I O m hm hI hO hl hu
    _ ≤ X^(ε/2) * X^(ε/2) := mul_le_mul hX.2 hp (by positivity) (by positivity)
    _ = _ := by rw [← Real.rpow_add hXp]; congr 1; ring

run_cmd do
  for decl in [``collected_eq_convolution, ``tupleLists_card_le,
      ``boundedTuples_card_le, ``representations_card_le, ``collected_abs_le,
      ``signedCoefficient_abs_le, ``signedCoefficient_power_bound,
      ``eventually_signedCoefficient_cap] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ALL-LENGTH COLLECTED MULTIPLICITY BOUNDS PASSED"

end PositiveSharpRemainderAnalysis
