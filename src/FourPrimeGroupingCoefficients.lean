import DirichletPowerCoefficients

/-! Mixed-support four-factor coefficients. Every ordered representation is
retained. No primality, ordering, or distinctness restriction is inserted. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped BigOperators

namespace FourPrimeGrouping

abbrev Tuple := (ℕ × ℕ) × (ℕ × ℕ)

def tuples (S0 S1 S2 S3 : Finset ℕ) : Finset Tuple :=
  (S0 ×ˢ S1) ×ˢ (S2 ×ˢ S3)

def productIndex (f : Tuple) : ℕ := f.1.1 * f.1.2 * f.2.1 * f.2.2

def support (S0 S1 S2 S3 : Finset ℕ) : Finset ℕ :=
  (tuples S0 S1 S2 S3).image productIndex

def coefficient (S0 S1 S2 S3 : Finset ℕ) (C : ℕ → ℝ) (m : ℕ) : ℝ :=
  ∑ f ∈ (tuples S0 S1 S2 S3).filter (fun f => productIndex f = m), C f.1.1

def commonSupport (S0 S1 S2 S3 : Finset ℕ) : Finset ℕ := S0 ∪ S1 ∪ S2 ∪ S3

def tupleToFunction (f : Tuple) : Fin 4 → ℕ := ![f.1.1, f.1.2, f.2.1, f.2.2]

theorem tupleToFunction_injective : Function.Injective tupleToFunction := by
  intro f g h
  have h0 := congrFun h (0 : Fin 4)
  have h1 := congrFun h (1 : Fin 4)
  have h2 := congrFun h (2 : Fin 4)
  have h3 := congrFun h (3 : Fin 4)
  exact Prod.ext
    (Prod.ext (by simpa [tupleToFunction] using h0) (by simpa [tupleToFunction] using h1))
    (Prod.ext (by simpa [tupleToFunction] using h2) (by simpa [tupleToFunction] using h3))

theorem tupleToFunction_product (f : Tuple) :
    DirichletPowerCoefficients.productIndex (tupleToFunction f) = productIndex f := by
  simp [DirichletPowerCoefficients.productIndex, tupleToFunction,
    productIndex, Fin.prod_univ_succ, mul_assoc]

theorem tupleToFunction_mem (S0 S1 S2 S3 : Finset ℕ) (f : Tuple)
    (hf : f ∈ tuples S0 S1 S2 S3) :
    tupleToFunction f ∈ DirichletPowerCoefficients.tuples (commonSupport S0 S1 S2 S3) 4 := by
  obtain ⟨h01, h23⟩ := Finset.mem_product.mp hf
  obtain ⟨h0, h1⟩ := Finset.mem_product.mp h01
  obtain ⟨h2, h3⟩ := Finset.mem_product.mp h23
  apply Fintype.mem_piFinset.mpr
  intro i
  fin_cases i <;> simp_all [tupleToFunction, commonSupport]

theorem fiber_card_bound (S0 S1 S2 S3 : Finset ℕ) (m : ℕ) (hm : m ≠ 0) :
    ((tuples S0 S1 S2 S3).filter (fun f => productIndex f = m)).card ≤
      m.divisors.card ^ 4 := by
  have hi : ((tuples S0 S1 S2 S3).filter (fun f => productIndex f = m)).card ≤
      ((DirichletPowerCoefficients.tuples (commonSupport S0 S1 S2 S3) 4).filter
        (fun f => DirichletPowerCoefficients.productIndex f = m)).card := by
    apply Finset.card_le_card_of_injOn tupleToFunction
    · intro f hf
      obtain ⟨hf, hfm⟩ := Finset.mem_filter.mp hf
      exact Finset.mem_filter.mpr ⟨tupleToFunction_mem S0 S1 S2 S3 f hf,
        (tupleToFunction_product f).trans hfm⟩
    · exact tupleToFunction_injective.injOn
  exact hi.trans (DirichletPowerCoefficients.fiber_card_bound _ 4 m hm)

theorem product_positive (S0 S1 S2 S3 : Finset ℕ)
    (h0 : ∀ n ∈ S0, 0 < n) (h1 : ∀ n ∈ S1, 0 < n)
    (h2 : ∀ n ∈ S2, 0 < n) (h3 : ∀ n ∈ S3, 0 < n)
    (f : Tuple) (hf : f ∈ tuples S0 S1 S2 S3) : 0 < productIndex f := by
  obtain ⟨h01, h23⟩ := Finset.mem_product.mp hf
  obtain ⟨hf0, hf1⟩ := Finset.mem_product.mp h01
  obtain ⟨hf2, hf3⟩ := Finset.mem_product.mp h23
  exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (h0 _ hf0) (h1 _ hf1)) (h2 _ hf2)) (h3 _ hf3)

theorem support_positive (S0 S1 S2 S3 : Finset ℕ)
    (h0 : ∀ n ∈ S0, 0 < n) (h1 : ∀ n ∈ S1, 0 < n)
    (h2 : ∀ n ∈ S2, 0 < n) (h3 : ∀ n ∈ S3, 0 < n)
    (m : ℕ) (hm : m ∈ support S0 S1 S2 S3) : 0 < m := by
  obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hm
  exact product_positive S0 S1 S2 S3 h0 h1 h2 h3 f hf

theorem coefficient_zero_off_support (S0 S1 S2 S3 : Finset ℕ) (C : ℕ → ℝ)
    (m : ℕ) (hm : m ∉ support S0 S1 S2 S3) : coefficient S0 S1 S2 S3 C m = 0 := by
  apply Finset.sum_eq_zero
  intro f hf
  obtain ⟨hf, hfm⟩ := Finset.mem_filter.mp hf
  exact (hm (Finset.mem_image.mpr ⟨f, hf, hfm⟩)).elim

theorem coefficient_abs_le_fiber (S0 S1 S2 S3 : Finset ℕ) (C : ℕ → ℝ)
    (hC : ∀ ν ∈ S0, |C ν| ≤ 1) (m : ℕ) :
    |coefficient S0 S1 S2 S3 C m| ≤
      (((tuples S0 S1 S2 S3).filter (fun f => productIndex f = m)).card : ℝ) := by
  unfold coefficient
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _f ∈ (tuples S0 S1 S2 S3).filter (fun f => productIndex f = m), (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro f hf
      exact hC f.1.1 (Finset.mem_product.mp
        (Finset.mem_product.mp (Finset.mem_filter.mp hf).1).1).1
    _ = _ := by simp

theorem coefficient_abs_le_tau_four_nonzero (S0 S1 S2 S3 : Finset ℕ) (C : ℕ → ℝ)
    (hC : ∀ ν ∈ S0, |C ν| ≤ 1) (m : ℕ) (hm : m ≠ 0) :
    |coefficient S0 S1 S2 S3 C m| ≤ (m.divisors.card : ℝ) ^ 4 := by
  apply (coefficient_abs_le_fiber S0 S1 S2 S3 C hC m).trans
  exact_mod_cast fiber_card_bound S0 S1 S2 S3 m hm

theorem coefficient_abs_le_tau_four (S0 S1 S2 S3 : Finset ℕ) (C : ℕ → ℝ)
    (h0 : ∀ n ∈ S0, 0 < n) (h1 : ∀ n ∈ S1, 0 < n)
    (h2 : ∀ n ∈ S2, 0 < n) (h3 : ∀ n ∈ S3, 0 < n)
    (hC : ∀ ν ∈ S0, |C ν| ≤ 1) (m : ℕ) :
    |coefficient S0 S1 S2 S3 C m| ≤ (m.divisors.card : ℝ) ^ 4 := by
  by_cases hm : m = 0
  · subst m
    rw [coefficient_zero_off_support S0 S1 S2 S3 C 0
      (by intro h; exact (Nat.lt_irrefl 0) (support_positive S0 S1 S2 S3 h0 h1 h2 h3 0 h))]
    simp
  · exact coefficient_abs_le_tau_four_nonzero S0 S1 S2 S3 C hC m hm

theorem grouped_sum (S0 S1 S2 S3 target : Finset ℕ) (C kernel : ℕ → ℝ)
    (hmap : ∀ f ∈ tuples S0 S1 S2 S3, productIndex f ∈ target) :
    (∑ m ∈ target, coefficient S0 S1 S2 S3 C m * kernel m) =
      ∑ f ∈ tuples S0 S1 S2 S3, C f.1.1 * kernel (productIndex f) := by
  unfold coefficient
  simp_rw [Finset.sum_mul]
  have hh := Finset.sum_fiberwise_of_maps_to hmap
    (fun f => C f.1.1 * kernel (productIndex f))
  rw [← hh]
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro f hf
  rw [(Finset.mem_filter.mp hf).2]

theorem support_contains (S0 S1 S2 S3 : Finset ℕ) (f : Tuple)
    (hf : f ∈ tuples S0 S1 S2 S3) : productIndex f ∈ support S0 S1 S2 S3 :=
  Finset.mem_image.mpr ⟨f, hf, rfl⟩

theorem grouped_sum_support (S0 S1 S2 S3 : Finset ℕ) (C kernel : ℕ → ℝ) :
    (∑ m ∈ support S0 S1 S2 S3, coefficient S0 S1 S2 S3 C m * kernel m) =
      ∑ ν ∈ S0, ∑ p1 ∈ S1, ∑ p2 ∈ S2, ∑ p3 ∈ S3,
        C ν * kernel (ν * p1 * p2 * p3) := by
  rw [grouped_sum S0 S1 S2 S3 _ C kernel (support_contains S0 S1 S2 S3)]
  simp only [tuples, Finset.sum_product, productIndex]

#print axioms coefficient_abs_le_tau_four
#print axioms grouped_sum_support
run_cmd do
  for decl in [``tupleToFunction_injective, ``tupleToFunction_product,
      ``tupleToFunction_mem, ``fiber_card_bound, ``product_positive, ``support_positive,
      ``coefficient_zero_off_support, ``coefficient_abs_le_fiber,
      ``coefficient_abs_le_tau_four_nonzero, ``coefficient_abs_le_tau_four,
      ``grouped_sum, ``support_contains, ``grouped_sum_support] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end FourPrimeGrouping
end
