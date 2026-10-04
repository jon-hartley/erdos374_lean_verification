import OuterLocalizedCoreWork
import RestSmoothCoreReductionWork

/-! Original item 2 reduced to the explicit finite-frequency centered
core, with the entire truncation error proved negligible. -/
set_option autoImplicit false
noncomputable section
open Filter MeasureTheory Set
namespace RestLocalizedCoreReductionWork
open OuterLocalizedCoreWork OuterSmoothCoreWork
open OuterSmoothApproximationWork RestSmoothCoreReductionWork
open OuterPairSourceDecompositionWork PositiveSharpPowerWindow

def localizedNegativeMean (X s Y : ℝ) : ℝ :=
  (1/X)*(∫x in Icc X (2*X),max (-localizedRemainder X s (x-x*(Y/X)) x) 0)

theorem smooth_mean_le_localized (X s Y : ℝ) (hX : 0<X) :
    smoothNegativeMean X s Y ≤
      (1/X)*(∫x in Icc X (2*X),
        |smoothRemainder X s (x-x*(Y/X)) x-localizedRemainder X s (x-x*(Y/X)) x|)+
      localizedNegativeMean X s Y := by
  have hs := smooth_moving_integrable X s Y
  have hm := localized_moving_integrable X s Y
  have he := (hs.sub hm).abs
  have hi := setIntegral_mono_on hs.neg_part (he.add hm.neg_part) measurableSet_Icc
    (fun x _ => by
      simp only [Pi.add_apply,Pi.sub_apply]
      apply max_le
      · have ha := neg_le_abs (smoothRemainder X s (x-x*(Y/X)) x-
          localizedRemainder X s (x-x*(Y/X)) x)
        have hb := le_max_left (-localizedRemainder X s (x-x*(Y/X)) x) (0:ℝ)
        linarith
      · exact add_nonneg (abs_nonneg _) (le_max_right _ _))
  simp only [Pi.add_apply] at hi
  rw [integral_add he hm.neg_part] at hi
  have hb := mul_le_mul_of_nonneg_left hi (one_div_nonneg.mpr hX.le)
  simpa only [smoothNegativeMean,localizedNegativeMean,mul_add,Pi.sub_apply] using hb

theorem eventually_localized_error_log_unit (s : ℝ) (A : ℕ) :
    ∀ᶠ X : ℝ in atTop, 2 ≤ X ∧ ∀Y : ℝ, 0 ≤ Y → Y ≤ X/2 →
      (1/X)*(∫x in Icc X (2*X),
        |smoothRemainder X s (x-x*(Y/X)) x-localizedRemainder X s (x-x*(Y/X)) x|) ≤
          Y/(Real.log X)^A := by
  let C : ℝ := 24528*(boxPairs s).card
  have hC : 0 ≤ C := by dsimp [C]; positivity
  filter_upwards [PolynomialLogEnvelope.eventually_bound C A 1 hC (by norm_num),
    eventually_ge_atTop (2:ℝ)] with X he hX
  refine ⟨hX,?_⟩
  intro Y hY hYX
  have hXp : 0 < X := by linarith
  have hl : 0 < Real.log X := Real.log_pos (by linarith)
  have he' : C*(Real.log X)^A ≤ X := by
    calc
      _ ≤ C*(1+Real.log X)^A := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hl.le (by linarith) A) hC
      _ ≤ X := by simpa using he.2
  apply (localized_full_error_mean X s Y hX hY hYX).trans
  apply (div_le_div_iff₀ hXp (pow_pos hl A)).mpr
  have hh := mul_le_mul_of_nonneg_left he' hY
  simpa only [C,mul_assoc,mul_left_comm,mul_comm] using hh

theorem eventually_rest_mean_le_localizedCore (s : ℝ) (A : ℕ)
    (hs : 0 < s) (hs1 : s ≤ 1/1000) :
    ∀ᶠ X : ℝ in atTop,
      ShortSingletonClosure.restNegativeMean X s (halfWidth X (101/1000)) ≤
        10*halfWidth X (101/1000)/(Real.log X)^A+
          localizedNegativeMean X s (halfWidth X (101/1000)) := by
  filter_upwards [eventually_rest_mean_le_smoothCore s A hs hs1,
    eventually_localized_error_log_unit s A,
    halfWidth_eventually (101/1000) (by norm_num)] with X hr he hY
  have hh := smooth_mean_le_localized X s (halfWidth X (101/1000)) (by linarith [he.1])
  have he' := he.2 _ hY.1.le (by linarith [hY.2])
  have hb := hr.trans (add_le_add le_rfl (hh.trans (add_le_add he' le_rfl)))
  convert hb using 1 <;> ring

run_cmd do
  for decl in [``smooth_mean_le_localized, ``eventually_localized_error_log_unit,
      ``eventually_rest_mean_le_localizedCore] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end RestLocalizedCoreReductionWork
