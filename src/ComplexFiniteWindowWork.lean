import SignedFiniteWindowApproximation
import ComplexSmoothingBoundary

/-! Uniform truncated Mellin approximation with arbitrary complex weights. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators
namespace ComplexFiniteWindowWork
open Erdos374.HarmanGram152 SmoothedWindowTransfer

def error (S : Finset ℕ) (w : ℕ→ℂ) (ε a b σ δ x : ℝ) : ℂ :=
  ComplexSmoothingBoundary.sharp S w x-ComplexSmoothingBoundary.sharp S w (x-x*δ)-
    ((1/(2*Real.pi):ℝ):ℂ)*transform (verticalDirichlet152 S w σ)
      MellinSmoothingFunction.smoothing ε a b σ δ x

theorem sharp_parts (S : Finset ℕ) (w : ℕ→ℂ) (x : ℝ) :
    ComplexSmoothingBoundary.sharp S w x =
      (SmoothedCountBoundary.sharp S (fun n => (w n).re) x:ℂ)+
      Complex.I*(SmoothedCountBoundary.sharp S (fun n => (w n).im) x:ℂ) := by
  simp only [ComplexSmoothingBoundary.sharp,SmoothedCountBoundary.sharp,
    Complex.ofReal_sum,Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  split_ifs <;> apply Complex.ext <;> simp

theorem vertical_parts (S : Finset ℕ) (w : ℕ→ℂ) (σ t : ℝ) :
    verticalDirichlet152 S w σ t =
      verticalDirichlet152 S (fun n => ((w n).re:ℂ)) σ t+
      Complex.I*verticalDirichlet152 S (fun n => ((w n).im:ℂ)) σ t := by
  simp only [verticalDirichlet152,Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  have he : w n=((w n).re:ℂ)+Complex.I*((w n).im:ℂ) := by apply Complex.ext <;> simp
  conv_lhs => rw [he]
  ring

theorem error_parts (S : Finset ℕ) (w : ℕ→ℂ) (ε a b σ δ x : ℝ)
    (hx : 0<x) (hleft : 0<x-x*δ) (hS : ∀n∈S,0<n)
    (hσ : 1<σ) (hσ2 : σ≤2) (hε : ε∈Ioo 0 1) :
    error S w ε a b σ δ x =
      SignedFiniteWindowApproximation.error S (fun n => (w n).re) ε a b σ δ x+
      Complex.I*SignedFiniteWindowApproximation.error S (fun n => (w n).im) ε a b σ δ x := by
  have hr := FiniteWindowFrequencySplit.integrable_kernel S (fun n => (w n).re)
    ε σ δ x hx hleft hS hσ hσ2 hε
  have hi := FiniteWindowFrequencySplit.integrable_kernel S (fun n => (w n).im)
    ε σ δ x hx hleft hS hσ hσ2 hε
  have ht : transform (verticalDirichlet152 S w σ) MellinSmoothingFunction.smoothing ε a b σ δ x =
      transform (verticalDirichlet152 S (fun n => ((w n).re:ℂ)) σ)
        MellinSmoothingFunction.smoothing ε a b σ δ x+
      Complex.I*transform (verticalDirichlet152 S (fun n => ((w n).im:ℂ)) σ)
        MellinSmoothingFunction.smoothing ε a b σ δ x := by
    unfold transform
    simp_rw [vertical_parts S w,add_mul,mul_assoc]
    simp only [mul_assoc] at hr hi
    rw [integral_add hr.integrableOn (hi.integrableOn.const_mul _),integral_const_mul]
  rw [error,sharp_parts,sharp_parts,ht]
  simp only [SignedFiniteWindowApproximation.error,Complex.ofReal_sub]
  ring

theorem eventual_approximation : ∀ᶠ X : ℝ in atTop, Real.exp 1≤X ∧
    ∀ (S : Finset ℕ) (w : ℕ→ℂ) (B : ℕ) (x δ : ℝ),
      1≤B → (B:ℝ)≤X^2 → (∀n∈S,0<n ∧ n≤B) →
      (∀n∈S,‖w n‖≤X^(1/200:ℝ)) → x∈Icc X (2*X) → δ∈Icc 0 (1/2) →
      ‖error S w (X^(-19/20:ℝ)) (-X) X (1+1/Real.log X) δ x‖≤8*X^(2/25:ℝ) := by
  filter_upwards [SignedFiniteWindowApproximation.eventual_approximation] with X hX
  refine ⟨hX.1,?_⟩
  intro S w B x δ hB hBX hS hw hx hδ
  have hXp : 0<X := (Real.exp_pos 1).trans_le hX.1
  have hxp : 0<x := hXp.trans_le hx.1
  have hleft : 0<x-x*δ := by nlinarith [hδ.2]
  have hlog : 1≤Real.log X := by simpa using Real.log_le_log (Real.exp_pos 1) hX.1
  have hσ : 1<1+1/Real.log X := by
    have : 0<1/Real.log X := by positivity
    linarith
  have hσ2 : 1+1/Real.log X≤2 := by
    have := (div_le_one (by linarith : 0<Real.log X)).mpr hlog
    linarith
  have hε : X^(-19/20:ℝ)∈Ioo 0 1 :=
    ⟨by positivity,Real.rpow_lt_one_of_one_lt_of_neg
      ((Real.one_lt_exp_iff.mpr (by norm_num)).trans_le hX.1) (by norm_num)⟩
  rw [error_parts S w _ _ _ _ _ _ hxp hleft (fun n hn => (hS n hn).1) hσ hσ2 hε]
  have hr := hX.2 S (fun n => (w n).re) B x δ hB hBX hS
    (fun n hn => (Complex.abs_re_le_norm _).trans (hw n hn)) hx hδ
  have hi := hX.2 S (fun n => (w n).im) B x δ hB hBX hS
    (fun n hn => (Complex.abs_im_le_norm _).trans (hw n hn)) hx hδ
  apply (norm_add_le _ _).trans
  rw [norm_mul,Complex.norm_I,one_mul]
  linarith

run_cmd do
  for decl in [``sharp_parts, ``vertical_parts, ``error_parts, ``eventual_approximation] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end ComplexFiniteWindowWork
