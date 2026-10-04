import SourceReferenceSigmaOne
import SourceLiteralMiddle
import IntegralTail

/-! v7. Centered middle energy for the literal source.
UNCOMPILED DRAFT. The continuous reference energy is constructed here.
The only outstanding analytic estimate assumed by the final theorem is
the same explicit first-factor cap as v6. Neither the low-frequency PNT
input nor the final physical source mean is proved by this module. -/
set_option autoImplicit false
set_option maxHeartbeats 14000000
noncomputable section
open MeasureTheory Set
namespace SourceCenteredMiddle
open SourceReferenceSigmaOne SourceLiteralMiddle SourceLiteralMoments
open SourceMassDischarge PositiveInteriorCells PositiveInteriorModel

/-- A nonnegative real version of the elementary one-sided inverse-square tail. -/
theorem positive_tail (f : ℝ → ℝ) (A T : ℝ) (hT : 0<T)
    (hf : ∀ t, 0≤f t) (hb : ∀ t, T<t → f t≤A/t^2) :
    (∫ t in Ioi T, f t) ≤ A/T := by
  have hp : (fun t : ℝ => A/t^2) = fun t => A*t^(-2:ℝ) := by
    funext t
    norm_num [Real.rpow_neg_natCast, div_eq_mul_inv]
  have hi : IntegrableOn (fun t : ℝ => A/t^2) (Ioi T) := by
    rw [hp]
    exact (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2:ℝ) < -1) hT).const_mul A
  calc
    _ ≤ ∫ t in Ioi T, A/t^2 := by
      apply integral_mono_of_nonneg (Filter.Eventually.of_forall hf) hi
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact hb t ht
    _ = A/T := by
      rw [hp, integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hT]
      norm_num [Real.rpow_neg_one]
      <;> ring

/-- Integrability is an explicit regularity premise, not inferred from totalized integrals. -/
theorem symmetric_gap (f : ℝ → ℝ) (A T : ℝ) (hT : 0<T)
    (hint : Integrable f) (hf : ∀ t, 0≤f t)
    (hzero : ∀ t∈Icc (-T) T, f t=0)
    (hbound : ∀ t, T< |t| → f t≤A/t^2) :
    (∫ t, f t) ≤ 2*A/T := by
  have hp := positive_tail f A T hT hf (by
    intro t ht
    apply hbound
    rwa [abs_of_pos (hT.trans ht)])
  have hn := positive_tail (fun t => f (-t)) A T hT (fun t => hf (-t)) (by
    intro t ht
    simpa only [abs_neg, abs_of_pos (hT.trans ht), neg_sq] using
      hbound (-t) (by simpa only [abs_neg, abs_of_pos (hT.trans ht)] using ht))
  rw [integral_comp_neg_Ioi, integral_Iic_eq_integral_Iio] at hn
  have hz : (∫ t in Icc (-T) T, f t)=0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact hzero t ht
  have hcompl : (Icc (-T) T)ᶜ = Iio (-T) ∪ Ioi T := by
    ext t
    simp only [mem_compl_iff, mem_Icc, not_and_or, not_le, mem_union, mem_Iio, mem_Ioi]
  have hs := setIntegral_compl (s := Icc (-T) T) measurableSet_Icc hint
  rw [hz, sub_zero, hcompl, setIntegral_union (by
    apply Set.disjoint_left.mpr
    intro t hl hr
    change t < -T at hl
    change T < t at hr
    linarith) measurableSet_Ioi hint.integrableOn hint.integrableOn] at hs
  rw [←hs]
  calc
    _ ≤ A/T+A/T := add_le_add hn hp
    _ = 2*A/T := by ring

/-- A T0/2 gap deliberately avoids endpoint bookkeeping; its factor two is harmless. -/
theorem reference_middle (X T0 : ℝ) (j : ℕ × ℕ)
    (hX : 2≤X) (hlog : 1000000≤Real.log X) (hj : j∈boxes (mesh X)) (hT0 : 0<T0) :
    (∫ t in middle X T0, ‖referenceProduct X j t‖^2) ≤ 810000/T0 := by
  let f : ℝ → ℝ := fun t => ‖referenceProduct X j t‖^2
  let g : ℝ → ℝ := (middle X T0).indicator f
  have hc : Continuous f := (reference_continuous X j (by linarith)).norm.pow 2
  have hfi : IntegrableOn f (middle X T0) :=
    hc.integrableOn_Icc.mono_set (middle_subset X T0)
  have hgi : Integrable g := hfi.integrable_indicator (middle_measurable X T0)
  have hg0 : ∀ t, 0≤g t := by
    intro t
    by_cases ht : t∈middle X T0 <;> simp [g, f, ht, sq_nonneg]
  have hz : ∀ t∈Icc (-(T0/2)) (T0/2), g t=0 := by
    intro t ht
    have hnot : t∉middle X T0 := by
      intro hm
      have hh : |t|≤T0/2 := abs_le.mpr ht
      have hlo : T0≤|t| := hm.2
      linarith
    simp [g,hnot]
  have hb : ∀ t, T0/2< |t| → g t≤202500/t^2 := by
    intro t ht
    by_cases hm : t∈middle X T0
    · have htn : t≠0 := by intro he; simp [he] at ht; linarith
      have hsq := pow_le_pow_left₀ (norm_nonneg (referenceProduct X j t))
        (reference_norm X t j hX hlog hj htn) 2
      have he : (450/|t|)^2=(202500:ℝ)/t^2 := by rw [div_pow, sq_abs]; norm_num
      simpa only [g, f, Set.indicator_of_mem hm, he] using hsq
    · simp only [g, Set.indicator_of_notMem hm]
      positivity
  have hh := symmetric_gap g 202500 (T0/2) (by positivity) hgi hg0 hz hb
  have he : (∫ t, g t) = ∫ t in middle X T0, f t := by
    exact integral_indicator (middle_measurable X T0)
  rw [he] at hh
  convert hh using 1 <;> ring

def centeredProduct (X : ℝ) (j : ℕ × ℕ) (t : ℝ) : ℂ :=
  sourceProduct X j t-referenceProduct X j t

theorem centered_continuous (X : ℝ) (j : ℕ × ℕ) (hX : 0<X) :
    Continuous (centeredProduct X j) :=
  (((factor_continuous X j 0).mul (factor_continuous X j 1)).mul
    (factor_continuous X j 2)).sub (reference_continuous X j hX)

/-- Construct the reference contribution; do not assume a centered energy bound. -/
theorem centered_middle_of_first_factor_cap (X T0 : ℝ) (j : ℕ × ℕ)
    (hX : 2≤X) (hlog : 1000000≤Real.log X) (hj : j∈boxes (mesh X))
    (hT0 : 0<T0)
    (hsmall : ∀ t∈middle X T0, ‖factor X j 0 t‖≤(1+Real.log X)^(-26000:ℝ)) :
    (∫ t in middle X T0, ‖centeredProduct X j t‖^2) ≤
      6*commonConstant/(1+Real.log X)^34+1620000/T0 := by
  have hu := middle_energy_of_first_factor_cap X T0 j hX hlog hj hsmall
  have hr := reference_middle X T0 j hX hlog hj hT0
  have hsub := middle_subset X T0
  have hpC : Continuous (fun t => ‖sourceProduct X j t‖^2) :=
    (((factor_continuous X j 0).mul (factor_continuous X j 1)).mul
      (factor_continuous X j 2)).norm.pow 2
  have hrC : Continuous (fun t => ‖referenceProduct X j t‖^2) :=
    (reference_continuous X j (by linarith)).norm.pow 2
  have hpI := (hpC.integrableOn_Icc (μ := volume)).mono_set hsub
  have hrI := (hrC.integrableOn_Icc (μ := volume)).mono_set hsub
  have hcI := (((centered_continuous X j (by linarith)).norm.pow 2).integrableOn_Icc
    (μ := volume)).mono_set hsub
  have hm := setIntegral_mono_on hcI ((hpI.const_mul 2).add (hrI.const_mul 2))
    (middle_measurable X T0) (by
      intro t _
      have hh := norm_sub_le (sourceProduct X j t) (referenceProduct X j t)
      have hn := norm_nonneg (sourceProduct X j t-referenceProduct X j t)
      change ‖sourceProduct X j t-referenceProduct X j t‖^2 ≤
        2*‖sourceProduct X j t‖^2+2*‖referenceProduct X j t‖^2
      have hsq := pow_le_pow_left₀ hn hh 2
      nlinarith [sq_nonneg (‖sourceProduct X j t‖-‖referenceProduct X j t‖)])
  change (∫ t in middle X T0, ‖centeredProduct X j t‖^2) ≤
    ∫ t in middle X T0, 2*‖sourceProduct X j t‖^2+2*‖referenceProduct X j t‖^2 at hm
  rw [integral_add (hpI.const_mul 2) (hrI.const_mul 2), integral_const_mul,
    integral_const_mul] at hm
  simp only [div_eq_mul_inv] at hu hr ⊢
  nlinarith

#print axioms centered_middle_of_first_factor_cap
run_cmd do
  for n in [``positive_tail, ``symmetric_gap, ``reference_middle,
      ``centered_continuous, ``centered_middle_of_first_factor_cap] do
    for ax in (← Lean.collectAxioms n) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {n}"
  Lean.logInfo "V7 CENTERED MIDDLE: PRIME CAP STILL EXPLICIT; COMPILATION REQUIRED"
end SourceCenteredMiddle
