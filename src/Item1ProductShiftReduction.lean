import Item1LogPhasePolynomialReduction

/-! Logarithmic phase reduction for arbitrary finite families of shifts and
for product shifts. Empty prefixes, zero shifts, and degree zero are allowed.
The averaging family is explicitly nonempty. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped BigOperators

namespace Item1ProductShiftReduction
open Item1FiniteAbelPhase Item1LongLogPhase Item1PhasePerturbation
open Item1LogPhasePolynomialReduction

/-- A bounded finite family of shifts has a uniform Taylor error at every
point in the original prefix. Repeated shift values retain multiplicity. -/
theorem shifted_family_atom_sum_le {ι : Type*} (s : Finset ι) (shift : ι → ℕ)
    (d M n R : ℕ) (t : ℝ) (hM : 1 ≤ M) (hhalf : 2*R ≤ M)
    (hshift : ∀ r ∈ s, shift r ≤ R) :
    ‖∑ r ∈ s, atom M t (n+shift r)‖ ≤
      ‖∑ r ∈ s, polynomialPhase d ((M:ℝ)+n) t (shift r)‖+
        (s.card:ℝ)*(2*|t| *((R:ℝ)/M)^(d+1)) := by
  have hMp : 0 < (M:ℝ) := by exact_mod_cast (by omega : 0 < M)
  have hnp : 0 < (M:ℝ)+n := by positivity
  have hhalf' : (R:ℝ) ≤ ((M:ℝ)+n)/2 := by
    have hh : 2*(R:ℝ) ≤ M := by exact_mod_cast hhalf
    linarith only [hh, Nat.cast_nonneg (α := ℝ) n]
  have hs := finite_log_phase_sum_le s (fun r => (shift r:ℝ))
    d ((M:ℝ)+n) t R hnp (by positivity) hhalf' (by
      intro r hr
      exact ⟨by positivity, by exact_mod_cast hshift r hr⟩)
  have hratio : (R:ℝ)/((M:ℝ)+n) ≤ (R:ℝ)/M :=
    div_le_div_of_nonneg_left (by positivity) hMp
      (by linarith only [Nat.cast_nonneg (α := ℝ) n])
  have herr := mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by positivity : 0 ≤ (R:ℝ)/((M:ℝ)+n)) hratio (d+1))
    (show 0 ≤ (s.card:ℝ)*(2*|t|) by positivity)
  have hs' : ‖∑ r ∈ s, atom M t (n+shift r)‖ ≤
      ‖∑ r ∈ s, polynomialPhase d ((M:ℝ)+n) t (shift r)‖+
        (s.card:ℝ)*(2*|t| *((R:ℝ)/((M:ℝ)+n))^(d+1)) := by
    simpa only [atom, unitPhase, Nat.cast_add, add_assoc] using hs
  exact hs'.trans (add_le_add le_rfl (by simpa only [mul_assoc] using herr))

/-- Averaging an arbitrary nonempty finite shift family keeps the exact
average endpoint cost, with no positivity assumption on the prefix length. -/
theorem prefix_le_family_polynomial_shifts {ι : Type*} (s : Finset ι)
    (hs : s.Nonempty) (shift : ι → ℕ) (d M K R : ℕ) (t : ℝ)
    (hM : 1 ≤ M) (hhalf : 2*R ≤ M) (hshift : ∀ r ∈ s, shift r ≤ R) :
    ‖«prefix» (atom M t) K‖ ≤
      (1/(s.card:ℝ))*(∑ n ∈ Finset.range K,
        ‖∑ r ∈ s, polynomialPhase d ((M:ℝ)+n) t (shift r)‖)+
      (K:ℝ)*(2*|t| *((R:ℝ)/M)^(d+1))+
      (2*∑ r ∈ s, (shift r:ℝ))/(s.card:ℝ) := by
  have hcard : 0 < (s.card:ℝ) := by exact_mod_cast Finset.card_pos.mpr hs
  have havg := Item1FiniteShiftAveraging.finite_family_shift_average s hs shift (atom M t)
    (fun n => by simpa only [atom, unitPhase] using
      (unitPhase_norm (-t*Real.log ((M:ℝ)+n))).le) K
  have hsum : ‖∑ r ∈ s, «prefix» (fun n => atom M t (n+shift r)) K‖ ≤
      (∑ n ∈ Finset.range K,
        ‖∑ r ∈ s, polynomialPhase d ((M:ℝ)+n) t (shift r)‖)+
      (K:ℝ)*((s.card:ℝ)*(2*|t| *((R:ℝ)/M)^(d+1))) := by
    simp only [«prefix»]
    rw [Finset.sum_comm]
    apply (norm_sum_le _ _).trans
    have hh := Finset.sum_le_sum (s := Finset.range K)
      (fun n _ => shifted_family_atom_sum_le s shift d M n R t hM hhalf hshift)
    simpa only [Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul] using hh
  apply havg.trans
  have hh := div_le_div_of_nonneg_right
    (add_le_add_right hsum (2*∑ r ∈ s, (shift r:ℝ))) hcard.le
  convert hh using 1 <;> field_simp [hcard.ne'] <;> ring

/-- Product shifts (a+1)b, with a in Fin A and b in a nonempty finite set.
The two endpoint pieces together cost at most 2 A Bmax. The finite set may
contain zero, and the prefix may be empty; the averaging cardinal is positive. -/
theorem prefix_le_product_polynomial_shifts (B : Finset ℕ) (hBne : B.Nonempty)
    (d M K A Bmax : ℕ) (t : ℝ) (hM : 1 ≤ M) (hA : 1 ≤ A)
    (hB : ∀ b ∈ B, b ≤ Bmax) (hhalf : 2*(A*Bmax) ≤ M) :
    ‖«prefix» (atom M t) K‖ ≤
      (1/((A:ℝ)*(B.card:ℝ)))*(∑ n ∈ Finset.range K,
        ‖∑ a : Fin A, ∑ b ∈ B,
          polynomialPhase d ((M:ℝ)+n) t (((a.val+1)*b:ℕ):ℝ)‖)+
      (K:ℝ)*(2*|t| *((((A*Bmax:ℕ):ℝ))/M)^(d+1))+
      2*(A:ℝ)*(Bmax:ℝ) := by
  classical
  let s : Finset (Fin A × ℕ) := Finset.univ.product B
  let shift : Fin A × ℕ → ℕ := fun r => (r.1.val+1)*r.2
  have hs : s.Nonempty := by
    obtain ⟨b, hb⟩ := hBne
    exact ⟨(⟨0, by omega⟩, b), by simp [s, hb]⟩
  have hshift : ∀ r ∈ s, shift r ≤ A*Bmax := by
    intro r hr
    have hb : r.2 ∈ B := (Finset.mem_product.mp hr).2
    exact Nat.mul_le_mul (by omega) (hB r.2 hb)
  have hcard : 0 < (s.card:ℝ) := by exact_mod_cast Finset.card_pos.mpr hs
  have hsum : (∑ r ∈ s, (shift r:ℝ)) ≤ (s.card:ℝ)*((A*Bmax:ℕ):ℝ) := by
    calc
      _ ≤ ∑ _r ∈ s, (((A*Bmax:ℕ):ℝ)) := by
        apply Finset.sum_le_sum
        intro r hr
        exact_mod_cast hshift r hr
      _ = _ := by simp [nsmul_eq_mul]
  have hend : (2*∑ r ∈ s, (shift r:ℝ))/(s.card:ℝ) ≤
      2*(A:ℝ)*(Bmax:ℝ) := by
    apply (div_le_iff₀ hcard).mpr
    have hh := mul_le_mul_of_nonneg_left hsum (show (0:ℝ) ≤ 2 by norm_num)
    simpa only [Nat.cast_mul, mul_assoc, mul_left_comm, mul_comm] using hh
  have hmain := prefix_le_family_polynomial_shifts s hs shift d M K (A*Bmax) t
    hM hhalf hshift
  have hfinal := hmain.trans (add_le_add le_rfl hend)
  simpa only [s, shift, Finset.product_eq_sprod, Finset.card_product, Finset.card_univ,
    Fintype.card_fin, Nat.cast_mul, Finset.sum_product] using hfinal

end Item1ProductShiftReduction

run_cmd do
  for target in [``Item1ProductShiftReduction.shifted_family_atom_sum_le,
      ``Item1ProductShiftReduction.prefix_le_family_polynomial_shifts,
      ``Item1ProductShiftReduction.prefix_le_product_polynomial_shifts] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "PRODUCT SHIFT REDUCTION: 3 standard-axiom theorem guards passed."
