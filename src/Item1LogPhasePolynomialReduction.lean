import Item1PhasePerturbation
import Item1LogTaylorRemainder
import Item1FiniteShiftAveraging
import Item1LongLogPhase

/-! A constructive opening reduction for logarithmic phase cancellation.
The original prefix is bounded by short polynomial phase sums with explicit
endpoint and Taylor errors. No polynomial cancellation estimate is assumed. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
open scoped BigOperators

namespace Item1LogPhasePolynomialReduction
open Item1PhasePerturbation Item1LogTaylorRemainder
open Item1FiniteAbelPhase Item1LongLogPhase

def polynomialPhase (d : ℕ) (x t h : ℝ) : ℂ :=
  unitPhase (-t*logPolynomial d (h/x))

def phaseCoefficient (x t : ℝ) (k : ℕ) : ℝ :=
  (-t)*(-1:ℝ)^k/(((k:ℝ)+1)*x^(k+1))

/-- The approximating phase is a literal polynomial in h, with every
coefficient displayed. There is no logarithm remaining in the inner sum. -/
theorem polynomialPhase_eq (d : ℕ) (x t h : ℝ) :
    polynomialPhase d x t h =
      unitPhase (∑ k ∈ Finset.range d, phaseCoefficient x t k*h^(k+1)) := by
  unfold polynomialPhase logPolynomial
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  simp only [phaseCoefficient,div_pow,div_eq_mul_inv,mul_inv_rev]
  ring

theorem log_phase_error_le (d : ℕ) (x t h : ℝ)
    (hx : 0 < x) (hh : 0 ≤ h) (hhalf : h ≤ x/2) :
    |(-t*Real.log (x+h))-(-t*(Real.log x+logPolynomial d (h/x)))| ≤
      2*|t| *(h/x)^(d+1) := by
  have he := mul_le_mul_of_nonneg_left
    (shifted_log_taylor_error_le d x h hx hh hhalf) (abs_nonneg t)
  have hid : (-t*Real.log (x+h))-(-t*(Real.log x+logPolynomial d (h/x))) =
      -t*(Real.log (x+h)-(Real.log x+logPolynomial d (h/x))) := by ring
  rw [hid,abs_mul,abs_neg]
  simpa only [mul_assoc,mul_left_comm,mul_comm] using he

/-- A finite family may contain repeated shifts. Its constant phase factors
out exactly, and every remainder is bounded uniformly by the largest shift. -/
theorem finite_log_phase_sum_le {ι : Type*} (s : Finset ι) (h : ι → ℝ)
    (d : ℕ) (x t R : ℝ) (hx : 0 < x) (hR : 0 ≤ R) (hhalf : R ≤ x/2)
    (hh : ∀ i ∈ s, 0 ≤ h i ∧ h i ≤ R) :
    ‖∑ i ∈ s, unitPhase (-t*Real.log (x+h i))‖ ≤
      ‖∑ i ∈ s, polynomialPhase d x t (h i)‖+
        (s.card:ℝ)*(2*|t| *(R/x)^(d+1)) := by
  have herr (i : ι) (hi : i ∈ s) :
      |(-t*Real.log (x+h i))-(-t*(Real.log x+logPolynomial d (h i/x)))| ≤
        2*|t| *(R/x)^(d+1) := by
    apply (log_phase_error_le d x t (h i) hx (hh i hi).1
      ((hh i hi).2.trans hhalf)).trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact pow_le_pow_left₀ (div_nonneg (hh i hi).1 hx.le)
      (div_le_div_of_nonneg_right (hh i hi).2 hx.le) _
  have hs := sum_phase_norm_le_uniform s
    (fun i => -t*Real.log (x+h i))
    (fun i => -t*(Real.log x+logPolynomial d (h i/x)))
    (2*|t| *(R/x)^(d+1)) herr
  have hid : (∑ i ∈ s, unitPhase (-t*(Real.log x+logPolynomial d (h i/x)))) =
      unitPhase (-t*Real.log x)*(∑ i ∈ s, polynomialPhase d x t (h i)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_add,unitPhase_add]
    rfl
  rw [hid,norm_mul,unitPhase_norm,one_mul] at hs
  exact hs

theorem shifted_atom_sum_le (d M n H : ℕ) (t : ℝ)
    (hM : 1 ≤ M) (hhalf : 2*H ≤ M) :
    ‖∑ h ∈ Finset.range H, atom M t (n+h)‖ ≤
      ‖∑ h ∈ Finset.range H, polynomialPhase d ((M:ℝ)+n) t h‖+
        (H:ℝ)*(2*|t| *((H:ℝ)/M)^(d+1)) := by
  have hMp : 0 < (M:ℝ) := by exact_mod_cast (by omega : 0 < M)
  have hnp : 0 < (M:ℝ)+n := by positivity
  have hhalf' : (H:ℝ) ≤ ((M:ℝ)+n)/2 := by
    have hh : 2*(H:ℝ) ≤ M := by exact_mod_cast hhalf
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hs := finite_log_phase_sum_le (Finset.range H) (fun h : ℕ => (h:ℝ))
    d ((M:ℝ)+n) t H hnp (by positivity) hhalf' (by
      intro h hh
      exact ⟨by positivity, by exact_mod_cast (Finset.mem_range.mp hh).le⟩)
  have hratio : (H:ℝ)/((M:ℝ)+n) ≤ (H:ℝ)/M :=
    div_le_div_of_nonneg_left (by positivity) hMp
      (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have herr := mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by positivity : 0 ≤ (H:ℝ)/((M:ℝ)+n)) hratio (d+1))
    (show 0 ≤ (H:ℝ)*(2*|t|) by positivity)
  have hs' : ‖∑ h ∈ Finset.range H, atom M t (n+h)‖ ≤
      ‖∑ h ∈ Finset.range H, polynomialPhase d ((M:ℝ)+n) t h‖+
        (H:ℝ)*(2*|t| *((H:ℝ)/((M:ℝ)+n))^(d+1)) := by
    simpa only [Finset.card_range,atom,unitPhase,Nat.cast_add,add_assoc] using hs
  exact hs'.trans (add_le_add le_rfl (by simpa only [mul_assoc] using herr))

/-- The degree is arbitrary. The remaining polynomial sums are explicit;
the theorem neither assumes nor asserts a bound for their cancellation. -/
theorem prefix_le_polynomial_shifts (d M K H : ℕ) (t : ℝ)
    (hM : 1 ≤ M) (hH : 1 ≤ H) (hhalf : 2*H ≤ M) :
    ‖«prefix» (atom M t) K‖ ≤
      (1/(H:ℝ))*(∑ n ∈ Finset.range K,
        ‖∑ h ∈ Finset.range H, polynomialPhase d ((M:ℝ)+n) t h‖)+
      (K:ℝ)*(2*|t| *((H:ℝ)/M)^(d+1))+((H:ℝ)-1) := by
  have hHp : 0 < (H:ℝ) := by exact_mod_cast (by omega : 0 < H)
  have havg := Item1FiniteShiftAveraging.finite_shift_average (atom M t)
    (fun n => by simpa only [atom,unitPhase] using
      (unitPhase_norm (-t*Real.log ((M:ℝ)+n))).le) K H hH
  have hsum : ‖∑ h ∈ Finset.range H, ∑ n ∈ Finset.range K, atom M t (n+h)‖ ≤
      (∑ n ∈ Finset.range K,
        ‖∑ h ∈ Finset.range H, polynomialPhase d ((M:ℝ)+n) t h‖)+
      (K:ℝ)*((H:ℝ)*(2*|t| *((H:ℝ)/M)^(d+1))) := by
    rw [Finset.sum_comm]
    apply (norm_sum_le _ _).trans
    have hh := Finset.sum_le_sum (s := Finset.range K)
      (fun n _ => shifted_atom_sum_le d M n H t hM hhalf)
    simpa only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_range,nsmul_eq_mul] using hh
  apply havg.trans
  have hh := add_le_add
    (mul_le_mul_of_nonneg_left hsum (show 0 ≤ 1/(H:ℝ) by positivity))
    (le_rfl : (H:ℝ)-1 ≤ (H:ℝ)-1)
  convert hh using 1 <;> field_simp [hHp.ne'] <;> ring

end Item1LogPhasePolynomialReduction

run_cmd do
  for target in [``Item1LogPhasePolynomialReduction.log_phase_error_le,
      ``Item1LogPhasePolynomialReduction.polynomialPhase_eq,
      ``Item1LogPhasePolynomialReduction.finite_log_phase_sum_le,
      ``Item1LogPhasePolynomialReduction.shifted_atom_sum_le,
      ``Item1LogPhasePolynomialReduction.prefix_le_polynomial_shifts] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "LOG PHASE POLYNOMIAL REDUCTION: 5 standard-axiom theorem guards passed."
