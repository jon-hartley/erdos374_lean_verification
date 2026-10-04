import OuterContourSpatialWork
import RestLocalizedCoreReductionWork

/-! Transfer the literal item-2 mean to the assembled contour remainder,
with all sharp approximation and normalization costs proved negligible. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Filter MeasureTheory Set
namespace RestContourReductionWork
open OuterContourSpatialWork OuterSharpContourAssemblyWork OuterLocalizedCoreWork
open RestLocalizedCoreReductionWork PositiveSharpPowerWindow

def contourNegativeMean (X s Y : ℝ) : ℝ :=
  (1/X)*(∫x in Icc X (2*X),max (-contourRemainder X s x (Y/X)) 0)

theorem eventually_localized_mean_le_contour (s : ℝ) (hs : 0≤s) (A : ℕ) :
    ∀ᶠ X : ℝ in atTop, 256≤X ∧ ∀Y : ℝ, X^(1/10:ℝ)≤Y → Y≤X/2 →
      localizedNegativeMean X s Y≤2*Y/(Real.log X)^A+contourNegativeMean X s Y := by
  have hεlim : Tendsto (fun X : ℝ => X^(-19/20:ℝ)) atTop (nhds 0) := by
    simpa only [neg_div] using (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<19/20))
  filter_upwards [eventually_localized_contour s hs A,eventually_ge_atTop (Real.exp 1),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1000000:ℝ)),
    hεlim.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/4))] with X happ hX hlog hε
  refine ⟨happ.1,?_⟩
  intro Y hY hYX
  have hXp : 0<X := by linarith [happ.1]
  have hY0 : 0≤Y := (Real.rpow_nonneg hXp.le _).trans hY
  have hi := contour_integrable X s Y hX (by linarith [happ.1]) hs hlog hY0 hYX ⟨by positivity,hε⟩
  have hc : IntegrableOn (fun _ : ℝ => 2*Y/(Real.log X)^A) (Icc X (2*X)) := continuous_const.integrableOn_Icc
  have hm := setIntegral_mono_on (localized_moving_integrable X s Y).neg_part (hc.add hi.neg_part)
    measurableSet_Icc (fun x hx => by
      simp only [Pi.add_apply]
      apply max_le
      · have he := neg_le_abs (localizedRemainder X s (x-x*(Y/X)) x-contourRemainder X s x (Y/X))
        have hb := happ.2 x Y hx hY hYX
        have hn := le_max_left (-contourRemainder X s x (Y/X)) (0:ℝ)
        linarith
      · exact add_nonneg (by positivity) (le_max_right _ _))
  simp only [Pi.add_apply] at hm
  rw [integral_add hc hi.neg_part,setIntegral_const,Real.volume_real_Icc_of_le (by linarith : X≤2*X)] at hm
  have hh := mul_le_mul_of_nonneg_left hm (one_div_nonneg.mpr hXp.le)
  change (1/X)*(∫x in Icc X (2*X),max (-localizedRemainder X s (x-x*(Y/X)) x) 0)≤_ at hh
  apply hh.trans_eq
  simp only [smul_eq_mul,contourNegativeMean]
  field_simp
  ring

theorem eventually_halfWidth_lower : ∀ᶠ X : ℝ in atTop,
    X^(1/10:ℝ)≤halfWidth X (101/1000) := by
  filter_upwards [(tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/1000)).eventually
    (eventually_ge_atTop (2:ℝ)),eventually_gt_atTop (0:ℝ)] with X hpow hX
  have hh := mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hX.le (1/10))
  have he : X^(1/10:ℝ)*X^(1/1000:ℝ)=X^(101/1000:ℝ) := by rw [←Real.rpow_add hX]; norm_num
  rw [he] at hh
  unfold halfWidth
  linarith

theorem eventually_rest_mean_le_contour (s : ℝ) (A : ℕ)
    (hs : 0<s) (hs1 : s≤1/1000) :
    ∀ᶠ X : ℝ in atTop,
      ShortSingletonClosure.restNegativeMean X s (halfWidth X (101/1000))≤
        12*halfWidth X (101/1000)/(Real.log X)^A+
          contourNegativeMean X s (halfWidth X (101/1000)) := by
  filter_upwards [eventually_rest_mean_le_localizedCore s A hs hs1,
    eventually_localized_mean_le_contour s hs.le A,eventually_halfWidth_lower,
    halfWidth_eventually (101/1000) (by norm_num)] with X hrest hcont hlo hhi
  have hh := hrest.trans (add_le_add le_rfl (hcont.2 _ hlo (by linarith [hhi.2])))
  apply hh.trans_eq
  ring

run_cmd do
  for decl in [``eventually_localized_mean_le_contour, ``eventually_halfWidth_lower,
      ``eventually_rest_mean_le_contour] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end RestContourReductionWork
