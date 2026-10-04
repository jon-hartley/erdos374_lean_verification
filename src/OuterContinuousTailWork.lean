import OuterModeContinuityWork
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! The continuous cofactor subtraction has small square energy on every
compact physical-frequency interval away from zero, with no length loss. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory Set
namespace OuterContinuousTailWork
open OuterCenteredFlatWork MellinWindowFactor

theorem inverse_square_integral (a b H : ℝ) (hab : a≤b) (hH : 0<H)
    (haway : ∀t∈Icc a b,H≤|t|) :
    (∫t in Icc a b, (t^2)⁻¹) ≤ 2/H := by
  have hz : (0:ℝ)∉uIcc a b := by
    rw [uIcc_of_le hab]
    intro ht
    have := haway 0 ht
    norm_num at this
    linarith
  have he : (∫t in a..b, (t^2)⁻¹) = a⁻¹-b⁻¹ := by
    have hh := integral_zpow (a:=a) (b:=b) (n := -2) (Or.inr ⟨by norm_num,hz⟩)
    convert hh using 1 <;> simp <;> ring
  have hia : |a⁻¹|≤1/H := by
    rw [abs_inv]
    simpa only [one_div] using one_div_le_one_div_of_le hH (haway a ⟨le_rfl,hab⟩)
  have hib : |b⁻¹|≤1/H := by
    rw [abs_inv]
    simpa only [one_div] using one_div_le_one_div_of_le hH (haway b ⟨hab,le_rfl⟩)
  rw [integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le hab,he]
  calc
    _ ≤ |a⁻¹|+|b⁻¹| := by linarith [le_abs_self (a⁻¹), neg_le_abs (b⁻¹)]
    _ ≤ 1/H+1/H := add_le_add hia hib
    _ = _ := by ring

theorem continuous_energy (lo hi : ℕ) (σ a b H : ℝ) (F : ℝ→ℂ)
    (hlo : 1≤lo) (hhi : 1≤hi) (hσ : 1<σ) (hab : a≤b) (hH : 0<H)
    (hF : Continuous F) (hcap : ∀t∈Icc a b,‖F t‖≤1)
    (haway : ∀t∈Icc a b,H≤|t|) :
    (∫t in Icc a b, ‖F t*continuousFlat lo hi σ t‖^2) ≤ 8/H := by
  have hC : Continuous (continuousFlat lo hi σ) :=
    FlatCofactorContour.continuous_polynomial lo hi σ (by omega) (by omega) hσ
  have hg : IntegrableOn (fun t : ℝ => 4*(t^2)⁻¹) (Icc a b) := by
    apply ContinuousOn.integrableOn_Icc
    apply continuousOn_const.mul
    exact (continuousOn_id.pow 2).inv₀ (fun t ht =>
      pow_ne_zero _ (abs_pos.mp (hH.trans_le (haway t ht))))
  have hb := setIntegral_mono_on ((hF.mul hC).norm.pow 2).integrableOn_Icc hg
    measurableSet_Icc (fun t ht => show ‖F t*continuousFlat lo hi σ t‖^2 ≤ 4*(t^2)⁻¹ by
      have ht0 := hH.trans_le (haway t ht)
      have hc := continuousFlat_bound lo hi σ t hlo hhi hσ.le ht0
      have hh : ‖F t*continuousFlat lo hi σ t‖≤2/|t| := by
        rw [norm_mul]
        exact (mul_le_mul_of_nonneg_right (hcap t ht) (norm_nonneg _)).trans
          (by simpa using hc)
      have hs := pow_le_pow_left₀ (norm_nonneg _) hh 2
      norm_num [div_eq_mul_inv,mul_pow,←abs_inv,sq_abs] at hs ⊢
      exact hs)
  rw [integral_const_mul] at hb
  exact hb.trans ((mul_le_mul_of_nonneg_left
    (inverse_square_integral a b H hab hH haway) (by norm_num : (0:ℝ)≤4)).trans_eq (by ring))

theorem centered_energy (lo hi : ℕ) (σ a b H : ℝ) (F : ℝ→ℂ)
    (hlo : 1≤lo) (hhi : 1≤hi) (hσ : 1<σ) (hab : a≤b) (hH : 0<H)
    (hF : Continuous F) (hcap : ∀t∈Icc a b,‖F t‖≤1)
    (haway : ∀t∈Icc a b,H≤|t|) :
    (∫t in Icc a b, ‖F t*centeredFlat lo hi σ t‖^2) ≤
      2*(∫t in Icc a b, ‖F t * Erdos374.HarmanGram152.verticalDirichlet152
        (Finset.Ioc lo hi) (fun _ => 1) σ t‖^2) + 16/H := by
  let K := Erdos374.HarmanGram152.verticalDirichlet152 (Finset.Ioc lo hi) (fun _ => 1) σ
  have hK : Continuous K := NormalizedMeanSquare.continuous_vertical _ _ σ
    (by intro n hn; have := (Finset.mem_Ioc.mp hn).1; omega)
  have hC : Continuous (continuousFlat lo hi σ) :=
    FlatCofactorContour.continuous_polynomial lo hi σ (by omega) (by omega) hσ
  have hpt (t : ℝ) : ‖F t*centeredFlat lo hi σ t‖^2 ≤
      2*‖F t*K t‖^2+2*‖F t*continuousFlat lo hi σ t‖^2 := by
    have hh := norm_sub_le (F t*K t) (F t*continuousFlat lo hi σ t)
    have he : F t*centeredFlat lo hi σ t=F t*K t-F t*continuousFlat lo hi σ t := by
      dsimp [centeredFlat,K]; ring
    rw [he]
    nlinarith [norm_nonneg (F t*K t-F t*continuousFlat lo hi σ t),
      norm_nonneg (F t*K t),norm_nonneg (F t*continuousFlat lo hi σ t),
      sq_nonneg (‖F t*K t‖-‖F t*continuousFlat lo hi σ t‖)]
  have hKI := ((hF.mul hK).norm.pow 2).integrableOn_Icc (μ:=volume) (a:=a) (b:=b)
  have hCI := ((hF.mul hC).norm.pow 2).integrableOn_Icc (μ:=volume) (a:=a) (b:=b)
  have hcent := OuterModeContinuityWork.continuous_centeredFlat lo hi σ (by omega) (by omega) hσ
  have hh := setIntegral_mono_on ((hF.mul hcent).norm.pow 2).integrableOn_Icc
    ((hKI.const_mul 2).add (hCI.const_mul 2)) measurableSet_Icc (fun t _ => hpt t)
  simp only [Pi.add_apply, Pi.pow_apply, Pi.mul_apply] at hh hKI hCI
  change IntegrableOn (fun t => ‖F t*K t‖^2) (Icc a b) volume at hKI
  change IntegrableOn (fun t => ‖F t*continuousFlat lo hi σ t‖^2) (Icc a b) volume at hCI
  rw [integral_add (hKI.const_mul 2) (hCI.const_mul 2),integral_const_mul,integral_const_mul] at hh
  have hc := continuous_energy lo hi σ a b H F hlo hhi hσ hab hH hF hcap haway
  change _ ≤ 2*(∫t in Icc a b, ‖F t*K t‖^2)+16/H
  calc
    _ ≤ 2*(∫t in Icc a b, ‖F t*K t‖^2)+2*(∫t in Icc a b, ‖F t*continuousFlat lo hi σ t‖^2) := hh
    _ ≤ 2*(∫t in Icc a b, ‖F t*K t‖^2)+2*(8/H) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hc (by norm_num : (0:ℝ)≤2))
    _ = 2*(∫t in Icc a b, ‖F t*K t‖^2)+16/H := by ring

run_cmd do
  for decl in [``inverse_square_integral, ``continuous_energy, ``centered_energy] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end OuterContinuousTailWork
