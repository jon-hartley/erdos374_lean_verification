import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-!
Elementary finite smoothing for the literal half-open dyadic block.
The smoothing is auxiliary to the pointwise cap; it does not change the source
window or its full-Mangoldt reference. No asymptotic cap is a premise here.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped BigOperators
namespace Item1LogRampSmoothing

def ramp (δ u : ℝ) : ℝ := min 1 (max 0 (u/δ))
def weight («λ» δ u : ℝ) : ℝ := ramp δ u-ramp δ (u-«λ»)
def sharp («λ» u : ℝ) : ℝ := if 0 ≤ u ∧ u < «λ» then 1 else 0
def Edge («λ» δ u : ℝ) : Prop := u ∈ Set.Icc 0 δ ∨ u ∈ Set.Icc «λ» («λ»+δ)

instance («λ» δ u : ℝ) : Decidable (Edge «λ» δ u) := Classical.propDecidable _

theorem ramp_nonneg (δ u : ℝ) : 0 ≤ ramp δ u :=
  le_min (by norm_num) (le_max_left _ _)

theorem ramp_le_one (δ u : ℝ) : ramp δ u ≤ 1 := min_le_left _ _

theorem ramp_mono (δ u v : ℝ) (hδ : 0 < δ) (huv : u ≤ v) :
    ramp δ u ≤ ramp δ v := by
  unfold ramp
  gcongr

theorem ramp_zero (δ u : ℝ) (hδ : 0 < δ) (hu : u ≤ 0) : ramp δ u = 0 := by
  have hh : u/δ ≤ 0 := div_nonpos_of_nonpos_of_nonneg hu hδ.le
  simp [ramp, max_eq_left hh]

theorem ramp_one (δ u : ℝ) (hδ : 0 < δ) (hu : δ ≤ u) : ramp δ u = 1 := by
  have hh : (1:ℝ) ≤ u/δ := (le_div_iff₀ hδ).mpr (by simpa using hu)
  exact min_eq_left (hh.trans (le_max_right _ _))

theorem weight_bounds («λ» δ u : ℝ) («hλ» : 0 ≤ «λ») (hδ : 0 < δ) :
    0 ≤ weight «λ» δ u ∧ weight «λ» δ u ≤ 1 := by
  have hm := ramp_mono δ (u-«λ») u hδ (by linarith)
  have hn := ramp_nonneg δ (u-«λ»)
  have hh := ramp_le_one δ u
  unfold weight
  constructor <;> linarith

theorem weight_left («λ» δ u : ℝ) («hλ» : 0 ≤ «λ») (hδ : 0 < δ) (hu : u ≤ 0) :
    weight «λ» δ u = 0 := by
  simp [weight, ramp_zero δ u hδ hu, ramp_zero δ (u-«λ») hδ (by linarith)]

theorem weight_right («λ» δ u : ℝ) («hλ» : 0 ≤ «λ») (hδ : 0 < δ)
    (hu : «λ»+δ ≤ u) : weight «λ» δ u = 0 := by
  simp [weight, ramp_one δ u hδ (by linarith), ramp_one δ (u-«λ») hδ (by linarith)]

theorem weight_core («λ» δ u : ℝ) (hδ : 0 < δ) (hlo : δ ≤ u) (hhi : u ≤ «λ») :
    weight «λ» δ u = 1 := by
  simp [weight, ramp_one δ u hδ hlo, ramp_zero δ (u-«λ») hδ (by linarith)]

theorem sharp_bounds («λ» u : ℝ) : 0 ≤ sharp «λ» u ∧ sharp «λ» u ≤ 1 := by
  unfold sharp
  split_ifs <;> norm_num

/-- Exact agreement outside the two transition strips; endpoints are included
in those strips, rather than incorrectly dropped from the Mangoldt block. -/
theorem weight_eq_sharp_off_edge («λ» δ u : ℝ) (hδ : 0 < δ) («hδλ» : δ ≤ «λ»)
    (ho : ¬ Edge «λ» δ u) : weight «λ» δ u = sharp «λ» u := by
  have «hλ» : 0 ≤ «λ» := by linarith
  by_cases hlo : u < 0
  · rw [weight_left «λ» δ u «hλ» hδ hlo.le]
    simp [sharp, not_le.mpr hlo]
  have hu0 : 0 ≤ u := le_of_not_gt hlo
  by_cases hhi : «λ»+δ < u
  · rw [weight_right «λ» δ u «hλ» hδ hhi.le]
    have hn : ¬ u < «λ» := by linarith
    simp [sharp,hn]
  have huhi : u ≤ «λ»+δ := le_of_not_gt hhi
  have hdu : δ < u := by
    by_contra hh
    exact ho (Or.inl ⟨hu0,le_of_not_gt hh⟩)
  have hul : u < «λ» := by
    by_contra hh
    exact ho (Or.inr ⟨le_of_not_gt hh,huhi⟩)
  rw [weight_core «λ» δ u hδ hdu.le hul.le]
  simp [sharp,hu0,hul]

theorem difference_bound («λ» δ u : ℝ) (hδ : 0 < δ) («hδλ» : δ ≤ «λ») :
    |sharp «λ» u-weight «λ» δ u| ≤ if Edge «λ» δ u then 1 else 0 := by
  by_cases hh : Edge «λ» δ u
  · rw [ite_eq_left hh]
    have hs := sharp_bounds «λ» u
    have hw := weight_bounds «λ» δ u (by linarith) hδ
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  · rw [ite_eq_right hh,weight_eq_sharp_off_edge «λ» δ u hδ «hδλ» hh]
    simp

/-- A generic finite coefficient bound, valid for complex coefficients and
repeated positions. The caller must still instantiate its actual edge count. -/
theorem finite_desmoothing (s : Finset ℕ) (a : ℕ → ℂ) (u : ℕ → ℝ)
    («λ» δ M : ℝ) (hδ : 0 < δ) («hδλ» : δ ≤ «λ») (hM : 0 ≤ M)
    (ha : ∀ n ∈ s, ‖a n‖ ≤ M) :
    ‖(∑ n ∈ s, a n*(sharp «λ» (u n):ℂ))-
      (∑ n ∈ s, a n*(weight «λ» δ (u n):ℂ))‖ ≤
      ((s.filter (fun n => Edge «λ» δ (u n))).card:ℝ)*M := by
  classical
  have hid : (∑ n ∈ s, a n*(sharp «λ» (u n):ℂ))-
      (∑ n ∈ s, a n*(weight «λ» δ (u n):ℂ)) =
      ∑ n ∈ s, a n*((sharp «λ» (u n)-weight «λ» δ (u n):ℝ):ℂ) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n _
    push_cast
    ring
  rw [hid]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ n ∈ s, if Edge «λ» δ (u n) then M else 0 := by
      apply Finset.sum_le_sum
      intro n hn
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
      have hd := difference_bound «λ» δ (u n) hδ «hδλ»
      by_cases hh : Edge «λ» δ (u n)
      · rw [ite_eq_left hh] at hd ⊢
        exact (mul_le_mul_of_nonneg_left hd (norm_nonneg _)).trans
          (by simpa using ha n hn)
      · rw [ite_eq_right hh] at hd ⊢
        have he : |sharp «λ» (u n)-weight «λ» δ (u n)|=0 :=
          le_antisymm hd (abs_nonneg _)
        simp [he]
    _ = ∑ n ∈ s.filter (fun n => Edge «λ» δ (u n)), M := by
      rw [Finset.sum_filter]
    _ = _ := by simp

/-- Entire-integral definition: no erroneous 0/0 convention at Mellin frequency 0. -/
def kernel («λ» δ : ℝ) (z : ℂ) : ℂ :=
  (∫ u in (0:ℝ)..«λ», Complex.exp (z*(u:ℂ))) *
    (∫ v in (0:ℝ)..δ, Complex.exp (z*(v:ℂ))) / (δ:ℂ)

theorem kernel_zero («λ» δ : ℝ) (hδ : δ ≠ 0) : kernel «λ» δ 0 = («λ»:ℂ) := by
  have hd : (δ:ℂ) ≠ 0 := by exact_mod_cast hδ
  simp [kernel, intervalIntegral.integral_const, hd]

end Item1LogRampSmoothing


run_cmd do
  for target in [
``Item1LogRampSmoothing.ramp_nonneg, ``Item1LogRampSmoothing.ramp_le_one, ``Item1LogRampSmoothing.ramp_mono, ``Item1LogRampSmoothing.ramp_zero, ``Item1LogRampSmoothing.ramp_one, ``Item1LogRampSmoothing.weight_bounds, ``Item1LogRampSmoothing.weight_left, ``Item1LogRampSmoothing.weight_right, ``Item1LogRampSmoothing.weight_core, ``Item1LogRampSmoothing.sharp_bounds, ``Item1LogRampSmoothing.weight_eq_sharp_off_edge, ``Item1LogRampSmoothing.difference_bound, ``Item1LogRampSmoothing.finite_desmoothing, ``Item1LogRampSmoothing.kernel_zero
] do
    for ax in (← Lean.collectAxioms target) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"
#print axioms Item1LogRampSmoothing.ramp_nonneg
#print axioms Item1LogRampSmoothing.ramp_le_one
#print axioms Item1LogRampSmoothing.ramp_mono
#print axioms Item1LogRampSmoothing.ramp_zero
#print axioms Item1LogRampSmoothing.ramp_one
#print axioms Item1LogRampSmoothing.weight_bounds
#print axioms Item1LogRampSmoothing.weight_left
#print axioms Item1LogRampSmoothing.weight_right
#print axioms Item1LogRampSmoothing.weight_core
#print axioms Item1LogRampSmoothing.sharp_bounds
#print axioms Item1LogRampSmoothing.weight_eq_sharp_off_edge
#print axioms Item1LogRampSmoothing.difference_bound
#print axioms Item1LogRampSmoothing.finite_desmoothing
#print axioms Item1LogRampSmoothing.kernel_zero



