import OuterRampTruncationWork

/-! Uniform truncation error for the product of all nine actual source
cuts. The Fourier height is free, and the error is explicit. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace OuterNineCutTruncationWork
open OuterRampTruncationWork OuterSourceFourierWork OuterRampLengthWork
open OuterRampConvolutionWork OuterSmoothStepWork OuterSmoothErrorSupportWork
open OuterBufferedSourceWork OuterSourceReindexWork LongerTupleEncoding

theorem finite_product_error {α : Type*} (S : Finset α) (f g : α → ℂ) (ε : ℝ)
    (hε : 0 ≤ ε) (hf : ∀n∈S, ‖f n‖ ≤ 1) (hg : ∀n∈S, ‖g n‖ ≤ 2)
    (he : ∀n∈S, ‖f n-g n‖ ≤ ε) :
    ‖(∏n∈S,f n)-(∏n∈S,g n)‖ ≤ (2^(S.card)-1)*ε := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    have hfS : ∀n∈S, ‖f n‖ ≤ 1 := fun n hn => hf n (Finset.mem_insert_of_mem hn)
    have hgS : ∀n∈S, ‖g n‖ ≤ 2 := fun n hn => hg n (Finset.mem_insert_of_mem hn)
    have heS : ∀n∈S, ‖f n-g n‖ ≤ ε := fun n hn => he n (Finset.mem_insert_of_mem hn)
    have hi := ih hfS hgS heS
    have hp : ‖∏n∈S,f n‖ ≤ 1 := by
      rw [norm_prod]
      exact Finset.prod_le_one₀ (fun n _ => norm_nonneg _) hfS
    have heA := he a (Finset.mem_insert_self _ _)
    have hgA := hg a (Finset.mem_insert_self _ _)
    rw [Finset.prod_insert ha,Finset.prod_insert ha,Finset.card_insert_of_notMem ha,pow_succ]
    calc
      _ = ‖(f a-g a)*(∏n∈S,f n)+g a*((∏n∈S,f n)-(∏n∈S,g n))‖ := by congr 1; ring
      _ ≤ ‖f a-g a‖*‖∏n∈S,f n‖+‖g a‖*‖(∏n∈S,f n)-(∏n∈S,g n)‖ := by
        simpa only [norm_mul] using norm_add_le ((f a-g a)*(∏n∈S,f n))
          (g a*((∏n∈S,f n)-(∏n∈S,g n)))
      _ ≤ ε*1+2*((2^S.card-1)*ε) := add_le_add
        (mul_le_mul heA hp (norm_nonneg _) hε)
        (mul_le_mul_of_nonneg_left hi (norm_nonneg (g a)) |>.trans
          (mul_le_mul_of_nonneg_right hgA ((norm_nonneg _).trans hi)))
      _ = _ := by ring

def errorBudget (X T : ℝ) : ℝ := (2*Real.pi)⁻¹*(4/(width X*T))
def truncatedCuts (X s T : ℝ) (r : Representation) (i j : ℕ) : ℂ :=
  ∏n : Fin 9, truncatedRamp (width X) (cutoffLength X s i j n) T
    (signedGap (Real.log (r.1:ℝ)) (cutoffLogs X s (drop r) i j) n)

theorem source_cut_error (X s T : ℝ) (hX : 2 ≤ X) (hT : 0 < T)
    (r : Representation) (hr : r ∈ ambient X) (i j : ℕ) (n : Fin 9) :
    ‖(transition (width X)
      (signedGap (Real.log (r.1:ℝ)) (cutoffLogs X s (drop r) i j) n):ℂ)-
      truncatedRamp (width X) (cutoffLength X s i j n) T
      (signedGap (Real.log (r.1:ℝ)) (cutoffLogs X s (drop r) i j) n)‖ ≤ errorBudget X T := by
  have hh := ramp_truncation_error (width X) (cutoffLength X s i j n) T
    (signedGap (Real.log (r.1:ℝ)) (cutoffLogs X s (drop r) i j) n)
    (by unfold width; positivity) (cutoffLength_pos X s hX i j n).le hT
  simpa only [ramp,ambient_compactRamp_eq X s hX r hr i j n,errorBudget] using hh

theorem source_nine_error (X s T : ℝ) (hX : 2 ≤ X) (hT : 0 < T)
    (hsmall : errorBudget X T ≤ 1) (r : Representation) (hr : r ∈ ambient X) (i j : ℕ) :
    ‖(smoothCuts (width X) (Real.log (r.1:ℝ)) (cutoffLogs X s (drop r) i j):ℂ)-
      truncatedCuts X s T r i j‖ ≤ 511*errorBudget X T := by
  let f : Fin 9 → ℂ := fun n => (transition (width X)
    (signedGap (Real.log (r.1:ℝ)) (cutoffLogs X s (drop r) i j) n):ℂ)
  let g : Fin 9 → ℂ := fun n => truncatedRamp (width X) (cutoffLength X s i j n) T
    (signedGap (Real.log (r.1:ℝ)) (cutoffLogs X s (drop r) i j) n)
  have hf (n : Fin 9) : ‖f n‖ ≤ 1 := by
    dsimp [f]
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (transition_bounds _ _).1]
    exact (transition_bounds _ _).2
  have he (n : Fin 9) : ‖f n-g n‖ ≤ errorBudget X T := source_cut_error X s T hX hT r hr i j n
  have hg (n : Fin 9) : ‖g n‖ ≤ 2 := by
    have hh := norm_add_le (g n-f n) (f n)
    rw [sub_add_cancel,norm_sub_rev] at hh
    linarith [he n,hf n]
  have hh := finite_product_error Finset.univ f g (errorBudget X T)
    (by unfold errorBudget width; positivity) (fun n _ => hf n) (fun n _ => hg n) (fun n _ => he n)
  norm_num only [Finset.card_univ,Fintype.card_fin, show (2:ℝ)^9-1=511 by norm_num] at hh
  simpa only [smoothCuts,truncatedCuts,Complex.ofReal_prod,f,g] using hh

theorem polynomial_errorBudget (X : ℝ) (hX : 2 ≤ X) :
    errorBudget X (X^4) = 8/(Real.pi*X^3) := by
  unfold errorBudget width
  have hx : X ≠ 0 := by linarith
  field_simp
  <;> ring

theorem source_nine_polynomial_error (X s : ℝ) (hX : 2 ≤ X)
    (r : Representation) (hr : r ∈ ambient X) (i j : ℕ) :
    ‖(smoothCuts (width X) (Real.log (r.1:ℝ)) (cutoffLogs X s (drop r) i j):ℂ)-
      truncatedCuts X s (X^4) r i j‖ ≤ 4088/(Real.pi*X^3) := by
  have hx3 : (8:ℝ) ≤ X^3 := by nlinarith [sq_nonneg (X-2)]
  have hsmall : errorBudget X (X^4) ≤ 1 := by
    rw [polynomial_errorBudget X hX]
    apply (div_le_one (by positivity : 0 < Real.pi*X^3)).mpr
    nlinarith [Real.pi_gt_three]
  have hh := source_nine_error X s (X^4) hX (by positivity) hsmall r hr i j
  rw [polynomial_errorBudget X hX] at hh
  convert hh using 1 <;> ring

run_cmd do
  for decl in [``finite_product_error, ``source_cut_error, ``source_nine_error,
      ``polynomial_errorBudget, ``source_nine_polynomial_error] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end OuterNineCutTruncationWork
