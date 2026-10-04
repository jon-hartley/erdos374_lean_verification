import ContinuousCofactorMellin
import OscillatoryResolvent
import CompactIntegral

/-! Finite positive-frequency tail of the actual continuous cofactor Mellin contour. -/

set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology ComplexConjugate

namespace ContinuousCofactorTail
open MellinWindowFactor ContinuousCofactorMellin Erdos374.HarmanGram152
  SmoothedDirichletKernel

theorem window_integral (left x σ t : ℝ) (_hleft : 0 < left)
    (hlex : left ≤ x) (hσ : 0 < σ) :
    (∫ y in Icc left x, (y : ℂ) ^ (line σ t - 1)) =
      ((x : ℂ) ^ line σ t - (left : ℂ) ^ line σ t) /
        line σ t := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hlex]
  have hexp : -1 < (line σ t - 1).re := by simp [line]; linarith
  rw [integral_cpow (Or.inl hexp)]
  simp only [sub_add_cancel]

theorem spike_transform (Ψ : ℝ → ℝ) (ε σ t : ℝ)
    (hε : 0 < ε) (hσ : 0 < σ) (hdiff : ContDiff ℝ 1 Ψ)
    (hsupport : Function.support Ψ ⊆ Icc (1 / 2) 2) :
    line σ t * mellin (fun y => (Smooth1 Ψ ε y : ℂ)) (line σ t) =
      mellin (fun y => (Ψ y : ℂ)) ((ε : ℂ) * line σ t) := by
  have hh := MellinOfSmooth1a hdiff hsupport hε (by simpa [line] using hσ)
    (s := line σ t)
  rw [hh, ← mul_assoc, mul_inv_cancel₀ (line_ne_zero σ t hσ), one_mul]

theorem spike_transform_compact (Ψ : ℝ → ℝ) (z : ℂ)
    (hsupport : Function.support Ψ ⊆ Icc (1 / 2) 2) :
    mellin (fun v => (Ψ v : ℂ)) z =
      ∫ v in Icc (1 / 2 : ℝ) 2, (v : ℂ) ^ (z - 1) * (Ψ v : ℂ) := by
  unfold mellin
  have hsubset : Icc (1 / 2 : ℝ) 2 ⊆ Ioi 0 := by
    intro v hv
    exact lt_of_lt_of_le (by norm_num) hv.1
  rw [MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
    measurableSet_Ioi hsubset]
  · simp only [smul_eq_mul]
  · intro v hv
    have hnot : v ∉ Icc (1 / 2 : ℝ) 2 := hv.2
    have hzero : Ψ v = 0 := by
      by_contra hne
      exact hnot (hsupport hne)
    simp [hzero]

theorem spike_mass_compact (Ψ : ℝ → ℝ)
    (hsupport : Function.support Ψ ⊆ Icc (1 / 2) 2)
    (hmass : ∫ v in Ioi 0, Ψ v / v = 1) :
    (∫ v in Icc (1 / 2 : ℝ) 2, Ψ v / v) = 1 := by
  have hsubset : Icc (1 / 2 : ℝ) 2 ⊆ Ioi 0 := by
    intro v hv
    exact lt_of_lt_of_le (by norm_num) hv.1
  rw [MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
    measurableSet_Ioi hsubset] at hmass
  · exact hmass
  · intro v hv
    have hzero : Ψ v = 0 := by
      by_contra hne
      exact hv.2 (hsupport hne)
    simp [hzero]

theorem cpow_phase (r p q : ℝ) (hr : 0 < r) :
    (r : ℂ) ^ ((p : ℂ) + Complex.I * (q : ℂ)) =
      ((r ^ p : ℝ) : ℂ) * OscillatoryResolvent.phase q (Real.log r) := by
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  rw [Complex.cpow_def_of_ne_zero hrC,
    ← Complex.ofReal_log hr.le, mul_add, Complex.exp_add]
  have hreal : Complex.exp ((Real.log r : ℂ) * (p : ℂ)) =
      ((r ^ p : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_exp, Real.rpow_def_of_pos hr]
  rw [hreal]
  congr 1
  unfold OscillatoryResolvent.phase
  congr 1
  push_cast
  ring

def endpointPhase (d e y v ε : ℝ) : ℝ :=
  Real.log y + ε * Real.log v - Real.log d - Real.log e

def endpointAmplitude (d e y v ε σ : ℝ) : ℝ :=
  d ^ (-σ) * e ^ (1 - σ) * y ^ (σ - 1) * v ^ (ε * σ - 1)

theorem endpoint_numerator (d e y v ε σ t : ℝ)
    (hd : 0 < d) (he : 0 < e) (hy : 0 < y) (hv : 0 < v) :
    (d : ℂ) ^ (-line σ t) *
      (e : ℂ) ^ (1 - line σ t) *
        (y : ℂ) ^ (line σ t - 1) *
          (v : ℂ) ^ ((ε : ℂ) * line σ t - 1) =
      ((endpointAmplitude d e y v ε σ : ℝ) : ℂ) *
        OscillatoryResolvent.phase (endpointPhase d e y v ε) t := by
  have hdexp : -line σ t = (((-σ : ℝ) : ℂ) +
      Complex.I * ((-t : ℝ) : ℂ)) := by
    unfold line
    push_cast
    ring
  have heexp : 1 - line σ t = (((1 - σ : ℝ) : ℂ) +
      Complex.I * ((-t : ℝ) : ℂ)) := by
    unfold line
    push_cast
    ring
  have hyexp : line σ t - 1 = (((σ - 1 : ℝ) : ℂ) +
      Complex.I * (t : ℂ)) := by
    unfold line
    push_cast
    ring
  have hvexp : (ε : ℂ) * line σ t - 1 =
      (((ε * σ - 1 : ℝ) : ℂ) + Complex.I * (((ε * t : ℝ) : ℂ))) := by
    unfold line
    push_cast
    ring
  rw [hdexp, heexp, hyexp, hvexp,
    cpow_phase d (-σ) (-t) hd,
    cpow_phase e (1-σ) (-t) he,
    cpow_phase y (σ-1) t hy,
    cpow_phase v (ε*σ-1) (ε*t) hv]
  unfold endpointAmplitude endpointPhase OscillatoryResolvent.phase
  push_cast
  have hexp : Complex.exp
      (-(Complex.I * (t : ℂ) * (Real.log d : ℂ)) -
        Complex.I * (t : ℂ) * (Real.log e : ℂ) +
        Complex.I * (t : ℂ) * (Real.log y : ℂ) +
        Complex.I * (t : ℂ) * (ε : ℂ) * (Real.log v : ℂ)) =
      Complex.exp (-(Complex.I * (t : ℂ) * (Real.log d : ℂ))) *
        Complex.exp (-(Complex.I * (t : ℂ) * (Real.log e : ℂ))) *
          Complex.exp (Complex.I * (t : ℂ) * (Real.log y : ℂ)) *
            Complex.exp (Complex.I * (t : ℂ) * (ε : ℂ) * (Real.log v : ℂ)) := by
    rw [show -(Complex.I * (t : ℂ) * (Real.log d : ℂ)) -
        Complex.I * (t : ℂ) * (Real.log e : ℂ) +
        Complex.I * (t : ℂ) * (Real.log y : ℂ) +
        Complex.I * (t : ℂ) * (ε : ℂ) * (Real.log v : ℂ) =
      ((-(Complex.I * (t : ℂ) * (Real.log d : ℂ)) +
        -(Complex.I * (t : ℂ) * (Real.log e : ℂ))) +
        Complex.I * (t : ℂ) * (Real.log y : ℂ)) +
        Complex.I * (t : ℂ) * (ε : ℂ) * (Real.log v : ℂ) by ring]
    rw [Complex.exp_add, Complex.exp_add, Complex.exp_add]
  have hphaseexp : Complex.exp
      (Complex.I * (((Real.log y : ℂ) + (ε : ℂ) * (Real.log v : ℂ) -
        (Real.log d : ℂ) - (Real.log e : ℂ)) * (t : ℂ))) =
      Complex.exp
        (-(Complex.I * (t : ℂ) * (Real.log d : ℂ)) -
          Complex.I * (t : ℂ) * (Real.log e : ℂ) +
          Complex.I * (t : ℂ) * (Real.log y : ℂ) +
          Complex.I * (t : ℂ) * (ε : ℂ) * (Real.log v : ℂ)) := by
    congr 1
    ring
  rw [hphaseexp, hexp]
  ring_nf

theorem compact_oscillatory_average (a H U l r g B : ℝ)
    (A : ℝ → ℂ) (φ : ℝ → ℝ)
    (hH : 0 < H) (hHU : H ≤ U) (hlr : l ≤ r)
    (hg : 0 < g) (hB : 0 ≤ B)
    (hA : Continuous A) (hφ : Continuous φ)
    (hgap : ∀ y ∈ Icc l r, g ≤ |φ y|)
    (hamp : ∀ y ∈ Icc l r, ‖A y‖ ≤ B) :
    ‖∫ t in Icc H U, ∫ y in Icc l r,
        A y * OscillatoryResolvent.phase (φ y) t /
          OscillatoryResolvent.denominator a t‖ ≤
      (r - l) * B * (4 / (g * H)) := by
  let f : ℝ → ℝ → ℂ := fun t y =>
    A y * OscillatoryResolvent.phase (φ y) (max H t) /
      OscillatoryResolvent.denominator a (max H t)
  have hmax : ∀ t : ℝ, 0 < max H t := by
    intro t
    exact hH.trans_le (le_max_left H t)
  have hden : ∀ t : ℝ, OscillatoryResolvent.denominator a (max H t) ≠ 0 := by
    intro t hz
    have hh := congrArg Complex.im hz
    simp [OscillatoryResolvent.denominator] at hh
    linarith [hmax t]
  have hf : Continuous f.uncurry := by
    have hca : Continuous (fun z : ℝ × ℝ => A z.2) := hA.comp continuous_snd
    have hcφ : Continuous (fun z : ℝ × ℝ => φ z.2) := hφ.comp continuous_snd
    have hct : Continuous (fun z : ℝ × ℝ => max H z.1) :=
      continuous_const.max continuous_fst
    have hcp : Continuous (fun z : ℝ × ℝ =>
        OscillatoryResolvent.phase (φ z.2) (max H z.1)) := by
      unfold OscillatoryResolvent.phase
      fun_prop
    have hcd : Continuous (fun z : ℝ × ℝ =>
        OscillatoryResolvent.denominator a (max H z.1)) := by
      unfold OscillatoryResolvent.denominator
      fun_prop
    exact (hca.mul hcp).div hcd (fun z => hden z.1)
  have hswap := CompactIntegral.integral_swap H U l r f hf
  have houter :
      (∫ t in Icc H U, ∫ y in Icc l r,
          A y * OscillatoryResolvent.phase (φ y) t /
            OscillatoryResolvent.denominator a t) =
      ∫ y in Icc l r, A y *
        (∫ t in Icc H U,
          OscillatoryResolvent.phase (φ y) t /
            OscillatoryResolvent.denominator a t) := by
    calc
      _ = ∫ t in Icc H U, ∫ y in Icc l r, f t y := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
        apply integral_congr_ae
        filter_upwards with y
        simp [f, max_eq_right ht.1, div_eq_mul_inv, mul_assoc]
      _ = ∫ y in Icc l r, ∫ t in Icc H U, f t y := hswap
      _ = _ := by
        apply integral_congr_ae
        filter_upwards with y
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
        simp [f, max_eq_right ht.1, div_eq_mul_inv, mul_assoc]
  rw [houter]
  have hpoint : ∀ y ∈ Icc l r,
      ‖A y * (∫ t in Icc H U,
        OscillatoryResolvent.phase (φ y) t /
          OscillatoryResolvent.denominator a t)‖ ≤
        B * (4 / (g * H)) := by
    intro y hy
    have hφne : φ y ≠ 0 := by
      intro heq
      have hh := hgap y hy
      simp [heq] at hh
      linarith
    have hφpos : 0 < |φ y| := abs_pos.mpr hφne
    have hres := OscillatoryResolvent.bound a (φ y) H U hφne hH hHU
    have heq : (∫ t in Icc H U,
        OscillatoryResolvent.phase (φ y) t /
          OscillatoryResolvent.denominator a t) =
        ∫ t in H..U, OscillatoryResolvent.phase (φ y) t /
          OscillatoryResolvent.denominator a t := by
      rw [integral_Icc_eq_integral_Ioc,
        intervalIntegral.integral_of_le hHU]
    rw [norm_mul, heq]
    apply (mul_le_mul (hamp y hy) hres (norm_nonneg _) hB).trans
    exact mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_left (by norm_num)
        (mul_pos hg hH) (mul_le_mul_of_nonneg_right (hgap y hy) hH.le)) hB
  calc
    _ ≤ ∫ y in Icc l r, ‖A y *
      (∫ t in Icc H U,
        OscillatoryResolvent.phase (φ y) t /
          OscillatoryResolvent.denominator a t)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ y in Icc l r, B * (4 / (g * H)) := by
      apply integral_mono_of_nonneg
      · exact Filter.Eventually.of_forall (fun _ => norm_nonneg _)
      · exact integrable_const _
      · filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
        exact hpoint y hy
    _ = _ := by
      rw [setIntegral_const, Real.volume_real_Icc_of_le hlr]
      simp only [smul_eq_mul]
      ring

theorem compact_double_average (a H U l r vl vr g C : ℝ)
    (A : ℝ → ℝ → ℂ) (φ : ℝ → ℝ → ℝ) (B : ℝ → ℝ)
    (hH : 0 < H) (hHU : H ≤ U) (hlr : l ≤ r) (_hvr : vl ≤ vr)
    (hg : 0 < g) (_hC : 0 ≤ C)
    (hA : Continuous A.uncurry) (hφ : Continuous φ.uncurry)
    (hB : Continuous B) (hBnonneg : ∀ v ∈ Icc vl vr, 0 ≤ B v)
    (hgap : ∀ y ∈ Icc l r, ∀ v ∈ Icc vl vr, g ≤ |φ y v|)
    (hamp : ∀ y ∈ Icc l r, ∀ v ∈ Icc vl vr, ‖A y v‖ ≤ B v)
    (hBmass : (∫ v in Icc vl vr, B v) ≤ C) :
    ‖∫ t in Icc H U, ∫ v in Icc vl vr, ∫ y in Icc l r,
        A y v * OscillatoryResolvent.phase (φ y v) t /
          OscillatoryResolvent.denominator a t‖ ≤
      (r - l) * C * (4 / (g * H)) := by
  let G : ℝ → ℝ → ℂ := fun t v =>
    ∫ y in Icc l r,
      A y v * OscillatoryResolvent.phase (φ y v) (max H t) /
        OscillatoryResolvent.denominator a (max H t)
  have hmax : ∀ t : ℝ, 0 < max H t := by
    intro t
    exact hH.trans_le (le_max_left H t)
  have hden : ∀ t : ℝ,
      OscillatoryResolvent.denominator a (max H t) ≠ 0 := by
    intro t hz
    have hh := congrArg Complex.im hz
    simp [OscillatoryResolvent.denominator] at hh
    linarith [hmax t]
  have hG : Continuous G.uncurry := by
    apply continuous_parametric_integral_of_continuous _ isCompact_Icc
    have hproj : Continuous (fun z : (ℝ × ℝ) × ℝ => (z.2, z.1.2)) :=
      continuous_snd.prodMk (continuous_snd.comp continuous_fst)
    have hca : Continuous (fun z : (ℝ × ℝ) × ℝ => A z.2 z.1.2) := by
      exact hA.comp hproj
    have hcφ : Continuous (fun z : (ℝ × ℝ) × ℝ => φ z.2 z.1.2) := by
      exact hφ.comp hproj
    have hcp : Continuous (fun z : (ℝ × ℝ) × ℝ =>
        OscillatoryResolvent.phase (φ z.2 z.1.2) (max H z.1.1)) := by
      unfold OscillatoryResolvent.phase
      fun_prop
    have hcd : Continuous (fun z : (ℝ × ℝ) × ℝ =>
        OscillatoryResolvent.denominator a (max H z.1.1)) := by
      unfold OscillatoryResolvent.denominator
      fun_prop
    exact (hca.mul hcp).div hcd (fun z => hden z.1.1)
  have hswap := CompactIntegral.integral_swap H U vl vr G hG
  have houter :
      (∫ t in Icc H U, ∫ v in Icc vl vr, ∫ y in Icc l r,
          A y v * OscillatoryResolvent.phase (φ y v) t /
            OscillatoryResolvent.denominator a t) =
      ∫ v in Icc vl vr, ∫ t in Icc H U, ∫ y in Icc l r,
          A y v * OscillatoryResolvent.phase (φ y v) t /
            OscillatoryResolvent.denominator a t := by
    calc
      _ = ∫ t in Icc H U, ∫ v in Icc vl vr, G t v := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
        apply integral_congr_ae
        filter_upwards with v
        apply integral_congr_ae
        filter_upwards with y
        simp [max_eq_right ht.1]
      _ = ∫ v in Icc vl vr, ∫ t in Icc H U, G t v := hswap
      _ = _ := by
        apply integral_congr_ae
        filter_upwards with v
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
        apply integral_congr_ae
        filter_upwards with y
        simp [max_eq_right ht.1]
  rw [houter]
  have hpoint : ∀ v ∈ Icc vl vr,
      ‖∫ t in Icc H U, ∫ y in Icc l r,
          A y v * OscillatoryResolvent.phase (φ y v) t /
            OscillatoryResolvent.denominator a t‖ ≤
        (r - l) * B v * (4 / (g * H)) := by
    intro v hv
    have hproj : Continuous (fun y : ℝ => (y, v)) :=
      continuous_id.prodMk continuous_const
    exact compact_oscillatory_average a H U l r g (B v)
      (fun y => A y v) (fun y => φ y v)
      hH hHU hlr hg (hBnonneg v hv)
      (hA.comp hproj) (hφ.comp hproj)
      (fun y hy => hgap y hy v hv) (fun y hy => hamp y hy v hv)
  have hnonneg : 0 ≤ (r - l) * (4 / (g * H)) := by
    have : 0 ≤ r - l := sub_nonneg.mpr hlr
    positivity
  calc
    _ ≤ ∫ v in Icc vl vr,
        ‖∫ t in Icc H U, ∫ y in Icc l r,
            A y v * OscillatoryResolvent.phase (φ y v) t /
              OscillatoryResolvent.denominator a t‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ v in Icc vl vr, (r - l) * B v * (4 / (g * H)) := by
      apply integral_mono_of_nonneg
      · exact Filter.Eventually.of_forall (fun _ => norm_nonneg _)
      · exact (hB.const_mul (r - l)).mul_const (4 / (g * H)) |>.integrableOn_Icc
      · filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
        exact hpoint v hv
    _ = (r - l) * (∫ v in Icc vl vr, B v) * (4 / (g * H)) := by
      rw [← integral_const_mul, ← integral_mul_const]
    _ ≤ (r - l) * C * (4 / (g * H)) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hBmass (sub_nonneg.mpr hlr)) (by positivity)

theorem compact_double_average_negative (a H U l r vl vr g C : ℝ)
    (A : ℝ → ℝ → ℂ) (φ : ℝ → ℝ → ℝ) (B : ℝ → ℝ)
    (hH : 0 < H) (hHU : H ≤ U) (hlr : l ≤ r) (hvr : vl ≤ vr)
    (hg : 0 < g) (hC : 0 ≤ C)
    (hA : Continuous A.uncurry) (hφ : Continuous φ.uncurry)
    (hB : Continuous B) (hBnonneg : ∀ v ∈ Icc vl vr, 0 ≤ B v)
    (hgap : ∀ y ∈ Icc l r, ∀ v ∈ Icc vl vr, g ≤ |φ y v|)
    (hamp : ∀ y ∈ Icc l r, ∀ v ∈ Icc vl vr, ‖A y v‖ ≤ B v)
    (hBmass : (∫ v in Icc vl vr, B v) ≤ C) :
    ‖∫ t in Icc (-U) (-H), ∫ v in Icc vl vr, ∫ y in Icc l r,
        A y v * OscillatoryResolvent.phase (φ y v) t /
          OscillatoryResolvent.denominator a t‖ ≤
      (r - l) * C * (4 / (g * H)) := by
  let F : ℝ → ℂ := fun t =>
    ∫ v in Icc vl vr, ∫ y in Icc l r,
      A y v * OscillatoryResolvent.phase (φ y v) t /
        OscillatoryResolvent.denominator a t
  let G : ℝ → ℂ := fun t =>
    ∫ v in Icc vl vr, ∫ y in Icc l r,
      A y v * OscillatoryResolvent.phase (-φ y v) t /
        OscillatoryResolvent.denominator (-a) t
  have hreflect :
      (∫ t in Icc (-U) (-H), F t) =
        ∫ t in Icc H U, F (-t) := by
    rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (show -U ≤ -H by linarith),
      ← intervalIntegral.integral_comp_neg (f := F) (a := H) (b := U)]
    rw [intervalIntegral.integral_of_le hHU,
      ← integral_Icc_eq_integral_Ioc]
  have hpoint (t : ℝ) : F (-t) = -G t := by
    have hscalar (y v : ℝ) :
        A y v * OscillatoryResolvent.phase (φ y v) (-t) /
          OscillatoryResolvent.denominator a (-t) =
        -(A y v * OscillatoryResolvent.phase (-φ y v) t /
          OscillatoryResolvent.denominator (-a) t) := by
      have hphase : OscillatoryResolvent.phase (φ y v) (-t) =
          OscillatoryResolvent.phase (-φ y v) t := by
        unfold OscillatoryResolvent.phase
        congr 1
        push_cast
        ring
      have hden : OscillatoryResolvent.denominator a (-t) =
          -OscillatoryResolvent.denominator (-a) t := by
        unfold OscillatoryResolvent.denominator
        push_cast
        ring
      rw [hphase, hden]
      ring
    change (∫ v in Icc vl vr, ∫ y in Icc l r,
      A y v * OscillatoryResolvent.phase (φ y v) (-t) /
        OscillatoryResolvent.denominator a (-t)) =
      -(∫ v in Icc vl vr, ∫ y in Icc l r,
        A y v * OscillatoryResolvent.phase (-φ y v) t /
          OscillatoryResolvent.denominator (-a) t)
    calc
      _ = ∫ v in Icc vl vr, ∫ y in Icc l r,
          -(A y v * OscillatoryResolvent.phase (-φ y v) t /
            OscillatoryResolvent.denominator (-a) t) := by
              apply integral_congr_ae
              filter_upwards with v
              apply integral_congr_ae
              filter_upwards with y
              exact hscalar y v
      _ = _ := by simp only [integral_neg]
  rw [hreflect]
  have hneg : (∫ t in Icc H U, F (-t)) =
      -(∫ t in Icc H U, G t) := by
    simp_rw [hpoint]
    rw [integral_neg]
  rw [hneg, norm_neg]
  exact compact_double_average (-a) H U l r vl vr g C A
    (fun y v => -φ y v) B hH hHU hlr hvr hg hC hA
    (by
      change Continuous (fun z : ℝ × ℝ => -φ.uncurry z)
      exact hφ.neg)
    hB hBnonneg
    (by
      intro y hy v hv
      simpa only [abs_neg] using hgap y hy v hv)
    hamp hBmass

theorem endpoint_amplitude_bound (d e y v x ε σ : ℝ)
    (hd : 0 < d) (he : 0 < e) (hy : 0 < y) (hyx : y ≤ x)
    (hv : v ∈ Icc (1 / 2 : ℝ) 2) (hε : ε ∈ Ioo 0 1)
    (hσ : 1 ≤ σ) (hσtwo : σ ≤ 2) :
    endpointAmplitude d e y v ε σ ≤
      4 * d ^ (-σ) * e ^ (1 - σ) * x ^ (σ - 1) / v := by
  have hx : 0 < x := hy.trans_le hyx
  have hvpos : 0 < v := lt_of_lt_of_le (by norm_num) hv.1
  have hpowY : y ^ (σ - 1) ≤ x ^ (σ - 1) :=
    Real.rpow_le_rpow hy.le hyx (by linarith)
  have hpowV : v ^ (ε * σ) ≤ 4 := by
    calc
      _ ≤ (2 : ℝ) ^ (ε * σ) :=
        Real.rpow_le_rpow hvpos.le hv.2 (by nlinarith [hε.1, hσ])
      _ ≤ (2 : ℝ) ^ (2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith [hε.2, hσtwo])
      _ = 4 := by norm_num
  unfold endpointAmplitude
  rw [Real.rpow_sub hvpos, Real.rpow_one]
  have hbase : 0 ≤ d ^ (-σ) * e ^ (1 - σ) := by positivity
  have hmono := mul_le_mul_of_nonneg_left hpowY hbase
  have hinv : 0 ≤ v⁻¹ := inv_nonneg.mpr hvpos.le
  calc
    _ = (d ^ (-σ) * e ^ (1 - σ) * y ^ (σ - 1)) *
        (v ^ (ε * σ) * v⁻¹) := by ring
    _ ≤ (d ^ (-σ) * e ^ (1 - σ) * x ^ (σ - 1)) *
        (v ^ (ε * σ) * v⁻¹) := by
          apply mul_le_mul_of_nonneg_right hmono
          positivity
    _ ≤ (d ^ (-σ) * e ^ (1 - σ) * x ^ (σ - 1)) *
        (4 * v⁻¹) := by
          apply mul_le_mul_of_nonneg_left _
          positivity
          exact mul_le_mul_of_nonneg_right hpowV hinv
    _ = _ := by field_simp

theorem endpoint_integrand (Ψ : ℝ → ℝ)
    (d e left x ε σ t : ℝ)
    (hd : 0 < d) (he : 0 < e) (hleft : 0 < left)
    (hlex : left ≤ x) (hε : 0 < ε) (hσ : 1 < σ)
    (hdiff : ContDiff ℝ 1 Ψ)
    (hsupport : Function.support Ψ ⊆ Icc (1 / 2) 2) :
    (d : ℂ) ^ (-line σ t) *
      (e : ℂ) ^ (1 - line σ t) /
        OscillatoryResolvent.denominator (1 - σ) t *
          mellin (fun z => (Smooth1 Ψ ε z : ℂ)) (line σ t) *
            ((x : ℂ) ^ line σ t - (left : ℂ) ^ line σ t) =
      ∫ v in Icc (1 / 2 : ℝ) 2, ∫ y in Icc left x,
        ((endpointAmplitude d e y v ε σ * Ψ v : ℝ) : ℂ) *
          OscillatoryResolvent.phase (endpointPhase d e y v ε) t /
            OscillatoryResolvent.denominator (1 - σ) t := by
  have hs : line σ t ≠ 0 := line_ne_zero σ t (by linarith)
  have hspike := spike_transform Ψ ε σ t hε (by linarith) hdiff hsupport
  have hwin := window_integral left x σ t hleft hlex (by linarith)
  have hcompact := spike_transform_compact Ψ ((ε : ℂ) * line σ t) hsupport
  have hpre :
      mellin (fun z => (Smooth1 Ψ ε z : ℂ)) (line σ t) *
        ((x : ℂ) ^ line σ t - (left : ℂ) ^ line σ t) =
      (∫ v in Icc (1 / 2 : ℝ) 2,
        (v : ℂ) ^ ((ε : ℂ) * line σ t - 1) * (Ψ v : ℂ)) *
        (∫ y in Icc left x, (y : ℂ) ^ (line σ t - 1)) := by
    rw [← hcompact, hwin]
    have hh := hspike
    apply mul_left_cancel₀ hs
    calc
      line σ t * (mellin (fun z => (Smooth1 Ψ ε z : ℂ)) (line σ t) *
        ((x : ℂ) ^ line σ t - (left : ℂ) ^ line σ t)) =
          mellin (fun z => (Ψ z : ℂ)) ((ε : ℂ) * line σ t) *
            ((x : ℂ) ^ line σ t - (left : ℂ) ^ line σ t) := by
              rw [← mul_assoc, hh]
      _ = line σ t *
        (mellin (fun z => (Ψ z : ℂ)) ((ε : ℂ) * line σ t) *
          (((x : ℂ) ^ line σ t - (left : ℂ) ^ line σ t) / line σ t)) := by
            field_simp
  calc
    _ = ((d : ℂ) ^ (-line σ t) *
          (e : ℂ) ^ (1 - line σ t) /
            OscillatoryResolvent.denominator (1 - σ) t) *
          (mellin (fun z => (Smooth1 Ψ ε z : ℂ)) (line σ t) *
            ((x : ℂ) ^ line σ t - (left : ℂ) ^ line σ t)) := by ring
    _ = ((d : ℂ) ^ (-line σ t) *
          (e : ℂ) ^ (1 - line σ t) /
            OscillatoryResolvent.denominator (1 - σ) t) *
          (∫ v in Icc (1 / 2 : ℝ) 2,
            (v : ℂ) ^ ((ε : ℂ) * line σ t - 1) * (Ψ v : ℂ)) *
          (∫ y in Icc left x, (y : ℂ) ^ (line σ t - 1)) := by
            rw [hpre]
            ring
    _ = _ := by
      symm
      let C : ℂ := (d : ℂ) ^ (-line σ t) *
        (e : ℂ) ^ (1 - line σ t) /
          OscillatoryResolvent.denominator (1 - σ) t
      let Y : ℂ := ∫ y in Icc left x, (y : ℂ) ^ (line σ t - 1)
      calc
        _ = ∫ v in Icc (1 / 2 : ℝ) 2, ∫ y in Icc left x,
            (C * ((v : ℂ) ^ ((ε : ℂ) * line σ t - 1) * (Ψ v : ℂ))) *
              (y : ℂ) ^ (line σ t - 1) := by
                apply integral_congr_ae
                filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
                apply integral_congr_ae
                filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
                have hvpos : 0 < v := lt_of_lt_of_le (by norm_num) hv.1
                have hypos : 0 < y := hleft.trans_le hy.1
                calc
                  _ = ((endpointAmplitude d e y v ε σ : ℝ) : ℂ) *
                      OscillatoryResolvent.phase (endpointPhase d e y v ε) t *
                        (Ψ v : ℂ) /
                          OscillatoryResolvent.denominator (1 - σ) t := by
                            push_cast
                            ring
                  _ = ((d : ℂ) ^ (-line σ t) *
                      (e : ℂ) ^ (1 - line σ t) *
                        (y : ℂ) ^ (line σ t - 1) *
                          (v : ℂ) ^ ((ε : ℂ) * line σ t - 1)) *
                            (Ψ v : ℂ) /
                              OscillatoryResolvent.denominator (1 - σ) t := by
                                rw [← endpoint_numerator d e y v ε σ t hd he hypos hvpos]
                  _ = _ := by simp only [C]; ring
        _ = ∫ v in Icc (1 / 2 : ℝ) 2,
            (C * ((v : ℂ) ^ ((ε : ℂ) * line σ t - 1) * (Ψ v : ℂ))) * Y := by
              apply integral_congr_ae
              filter_upwards with v
              simp only [Y]
              rw [integral_const_mul]
        _ = (∫ v in Icc (1 / 2 : ℝ) 2,
            C * ((v : ℂ) ^ ((ε : ℂ) * line σ t - 1) * (Ψ v : ℂ))) * Y := by
              rw [integral_mul_const]
        _ = C * (∫ v in Icc (1 / 2 : ℝ) 2,
            (v : ℂ) ^ ((ε : ℂ) * line σ t - 1) * (Ψ v : ℂ)) * Y := by
              rw [integral_const_mul]
        _ = _ := rfl

theorem endpoint_triple_bound (Ψ : ℝ → ℝ)
    (d e left x ε σ H U g : ℝ)
    (hd : 0 < d) (he : 0 < e) (hleft : 0 < left)
    (hlex : left ≤ x) (hε : ε ∈ Ioo 0 1)
    (hσ : 1 ≤ σ) (hσtwo : σ ≤ 2)
    (hH : 0 < H) (hHU : H ≤ U) (hg : 0 < g)
    (hdiff : ContDiff ℝ 1 Ψ)
    (hnonneg : ∀ v > 0, 0 ≤ Ψ v)
    (hsupport : Function.support Ψ ⊆ Icc (1 / 2) 2)
    (hmass : ∫ v in Ioi 0, Ψ v / v = 1)
    (hgap : ∀ y ∈ Icc left x, ∀ v ∈ Icc (1 / 2 : ℝ) 2,
      g ≤ |endpointPhase d e y v ε|) :
    ‖∫ t in Icc H U, ∫ v in Icc (1 / 2 : ℝ) 2,
      ∫ y in Icc left x,
        ((endpointAmplitude d e y v ε σ * Ψ v : ℝ) : ℂ) *
          OscillatoryResolvent.phase (endpointPhase d e y v ε) t /
            OscillatoryResolvent.denominator (1 - σ) t‖ ≤
      (x - left) *
        (4 * d ^ (-σ) * e ^ (1 - σ) * x ^ (σ - 1)) *
          (4 / (g * H)) := by
  let Y : ℝ → ℝ := fun y => max left y
  let V : ℝ → ℝ := fun v => max (1 / 2 : ℝ) v
  let A : ℝ → ℝ → ℂ := fun y v =>
    ((endpointAmplitude d e (Y y) (V v) ε σ * Ψ (V v) : ℝ) : ℂ)
  let φ : ℝ → ℝ → ℝ := fun y v => endpointPhase d e (Y y) (V v) ε
  let B : ℝ → ℝ := fun v =>
    4 * d ^ (-σ) * e ^ (1 - σ) * x ^ (σ - 1) * (Ψ (V v) / V v)
  have hYpos : ∀ y, 0 < Y y := by
    intro y
    exact hleft.trans_le (le_max_left left y)
  have hVpos : ∀ v, 0 < V v := by
    intro v
    exact lt_of_lt_of_le (by norm_num) (le_max_left (1 / 2 : ℝ) v)
  have hY : Continuous Y := continuous_const.max continuous_id
  have hV : Continuous V := continuous_const.max continuous_id
  have hx : 0 < x := hleft.trans_le hlex
  have hYeq : ∀ y ∈ Icc left x, Y y = y := by
    intro y hy
    exact max_eq_right hy.1
  have hVeq : ∀ v ∈ Icc (1 / 2 : ℝ) 2, V v = v := by
    intro v hv
    exact max_eq_right hv.1
  have hYpair : Continuous (fun z : ℝ × ℝ => Y z.1) :=
    hY.comp continuous_fst
  have hVpair : Continuous (fun z : ℝ × ℝ => V z.2) :=
    hV.comp continuous_snd
  have hYpow : Continuous (fun z : ℝ × ℝ => Y z.1 ^ (σ - 1)) :=
    hYpair.rpow_const (fun z => Or.inl (ne_of_gt (hYpos z.1)))
  have hVpow : Continuous (fun z : ℝ × ℝ => V z.2 ^ (ε * σ - 1)) :=
    hVpair.rpow_const (fun z => Or.inl (ne_of_gt (hVpos z.2)))
  have hΨV : Continuous (fun v : ℝ => Ψ (V v)) :=
    hdiff.continuous.comp hV
  have hΨVpair : Continuous (fun z : ℝ × ℝ => Ψ (V z.2)) :=
    hΨV.comp continuous_snd
  have hA : Continuous A.uncurry := by
    change Continuous (fun z : ℝ × ℝ =>
      ((d ^ (-σ) * e ^ (1 - σ) * Y z.1 ^ (σ - 1) *
        V z.2 ^ (ε * σ - 1) * Ψ (V z.2) : ℝ) : ℂ))
    exact Complex.continuous_ofReal.comp
      ((((continuous_const.mul continuous_const).mul hYpow).mul hVpow).mul hΨVpair)
  have hφ : Continuous φ.uncurry := by
    change Continuous (fun z : ℝ × ℝ =>
      Real.log (Y z.1) + ε * Real.log (V z.2) - Real.log d - Real.log e)
    exact (((hYpair.log (fun z => ne_of_gt (hYpos z.1))).add
      (continuous_const.mul
        (hVpair.log (fun z => ne_of_gt (hVpos z.2))))).sub
          continuous_const).sub continuous_const
  have hB : Continuous B := by
    change Continuous (fun v : ℝ =>
      4 * d ^ (-σ) * e ^ (1 - σ) * x ^ (σ - 1) *
        (Ψ (V v) / V v))
    exact continuous_const.mul
      (hΨV.div hV (fun v => ne_of_gt (hVpos v)))
  have hBnonneg : ∀ v ∈ Icc (1 / 2 : ℝ) 2, 0 ≤ B v := by
    intro v hv
    change 0 ≤ 4 * d ^ (-σ) * e ^ (1 - σ) * x ^ (σ - 1) *
      (Ψ (V v) / V v)
    have hψ : 0 ≤ Ψ (V v) := hnonneg (V v) (hVpos v)
    positivity
  have hamp : ∀ y ∈ Icc left x, ∀ v ∈ Icc (1 / 2 : ℝ) 2,
      ‖A y v‖ ≤ B v := by
    intro y hy v hv
    change ‖((endpointAmplitude d e (Y y) (V v) ε σ *
        Ψ (V v) : ℝ) : ℂ)‖ ≤
      4 * d ^ (-σ) * e ^ (1 - σ) * x ^ (σ - 1) *
        (Ψ (V v) / V v)
    rw [hYeq y hy, hVeq v hv]
    have hψ : 0 ≤ Ψ v := hnonneg v (lt_of_lt_of_le (by norm_num) hv.1)
    have hbound := endpoint_amplitude_bound d e y v x ε σ hd he
      (hleft.trans_le hy.1) hy.2 hv hε hσ hσtwo
    have hAmp : 0 ≤ endpointAmplitude d e y v ε σ := by
      have hypos : 0 < y := hleft.trans_le hy.1
      have hvpos : 0 < v := lt_of_lt_of_le (by norm_num) hv.1
      unfold endpointAmplitude
      positivity
    change ‖((endpointAmplitude d e y v ε σ * Ψ v : ℝ) : ℂ)‖ ≤
      4 * d ^ (-σ) * e ^ (1 - σ) * x ^ (σ - 1) * (Ψ v / v)
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hAmp hψ)]
    calc
      _ ≤ (4 * d ^ (-σ) * e ^ (1 - σ) * x ^ (σ - 1) / v) *
        Ψ v := mul_le_mul_of_nonneg_right hbound hψ
      _ = _ := by ring
  have hBmass : (∫ v in Icc (1 / 2 : ℝ) 2, B v) ≤
      4 * d ^ (-σ) * e ^ (1 - σ) * x ^ (σ - 1) := by
    change (∫ v in Icc (1 / 2 : ℝ) 2,
      4 * d ^ (-σ) * e ^ (1 - σ) * x ^ (σ - 1) *
        (Ψ (V v) / V v)) ≤ _
    have hmass' := spike_mass_compact Ψ hsupport hmass
    have heq : (∫ v in Icc (1 / 2 : ℝ) 2,
        4 * d ^ (-σ) * e ^ (1 - σ) * x ^ (σ - 1) *
          (Ψ (V v) / V v)) =
        4 * d ^ (-σ) * e ^ (1 - σ) * x ^ (σ - 1) := by
      have hcongr :
          (∫ v in Icc (1 / 2 : ℝ) 2,
            4 * d ^ (-σ) * e ^ (1 - σ) * x ^ (σ - 1) *
              (Ψ (V v) / V v)) =
          ∫ v in Icc (1 / 2 : ℝ) 2,
            4 * d ^ (-σ) * e ^ (1 - σ) * x ^ (σ - 1) *
              (Ψ v / v) := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
        rw [hVeq v hv]
      rw [hcongr, integral_const_mul, hmass', mul_one]
    exact heq.le
  have hbound := compact_double_average (1 - σ) H U left x
    (1 / 2) 2 g
    (4 * d ^ (-σ) * e ^ (1 - σ) * x ^ (σ - 1))
    A φ B hH hHU hlex (by norm_num) hg (by positivity)
    hA hφ hB hBnonneg
    (by
      intro y hy v hv
      change g ≤ |endpointPhase d e (Y y) (V v) ε|
      rw [hYeq y hy, hVeq v hv]
      exact hgap y hy v hv)
    hamp hBmass
  convert hbound using 1
  · congr 1
    apply integral_congr_ae
    filter_upwards with t
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    rw [show A y v = ((endpointAmplitude d e y v ε σ * Ψ v : ℝ) : ℂ) by
      simp only [A, hYeq y hy, hVeq v hv],
      show φ y v = endpointPhase d e y v ε by
        simp only [φ, hYeq y hy, hVeq v hv]]

theorem endpoint_triple_negative_eq_positive_norm (Ψ : ℝ → ℝ)
    (d e left x ε σ H U : ℝ) (hHU : H ≤ U) :
    ‖∫ t in Icc (-U) (-H), ∫ v in Icc (1 / 2 : ℝ) 2,
      ∫ y in Icc left x,
        ((endpointAmplitude d e y v ε σ * Ψ v : ℝ) : ℂ) *
          OscillatoryResolvent.phase (endpointPhase d e y v ε) t /
            OscillatoryResolvent.denominator (1 - σ) t‖ =
    ‖∫ t in Icc H U, ∫ v in Icc (1 / 2 : ℝ) 2,
      ∫ y in Icc left x,
        ((endpointAmplitude d e y v ε σ * Ψ v : ℝ) : ℂ) *
          OscillatoryResolvent.phase (endpointPhase d e y v ε) t /
            OscillatoryResolvent.denominator (1 - σ) t‖ := by
  let F : ℝ → ℂ := fun t =>
    ∫ v in Icc (1 / 2 : ℝ) 2, ∫ y in Icc left x,
      ((endpointAmplitude d e y v ε σ * Ψ v : ℝ) : ℂ) *
        OscillatoryResolvent.phase (endpointPhase d e y v ε) t /
          OscillatoryResolvent.denominator (1 - σ) t
  have hpoint : ∀ t : ℝ, F (-t) = conj (F t) := by
    intro t
    have hscalar (y v : ℝ) :
        ((endpointAmplitude d e y v ε σ * Ψ v : ℝ) : ℂ) *
          OscillatoryResolvent.phase (endpointPhase d e y v ε) (-t) /
            OscillatoryResolvent.denominator (1 - σ) (-t) =
        conj (((endpointAmplitude d e y v ε σ * Ψ v : ℝ) : ℂ) *
          OscillatoryResolvent.phase (endpointPhase d e y v ε) t /
            OscillatoryResolvent.denominator (1 - σ) t) := by
      unfold OscillatoryResolvent.phase OscillatoryResolvent.denominator
      rw [map_div₀]
      simp only [map_mul, map_sub, Complex.conj_ofReal,
        ← Complex.exp_conj, Complex.conj_I, Complex.ofReal_neg]
      simp only [mul_neg, Complex.ofReal_neg]
      ring_nf
    change (∫ v in Icc (1 / 2 : ℝ) 2, ∫ y in Icc left x,
      ((endpointAmplitude d e y v ε σ * Ψ v : ℝ) : ℂ) *
        OscillatoryResolvent.phase (endpointPhase d e y v ε) (-t) /
          OscillatoryResolvent.denominator (1 - σ) (-t)) =
      conj (∫ v in Icc (1 / 2 : ℝ) 2, ∫ y in Icc left x,
        ((endpointAmplitude d e y v ε σ * Ψ v : ℝ) : ℂ) *
          OscillatoryResolvent.phase (endpointPhase d e y v ε) t /
            OscillatoryResolvent.denominator (1 - σ) t)
    calc
      _ = ∫ v in Icc (1 / 2 : ℝ) 2, ∫ y in Icc left x,
          conj (((endpointAmplitude d e y v ε σ * Ψ v : ℝ) : ℂ) *
            OscillatoryResolvent.phase (endpointPhase d e y v ε) t /
              OscillatoryResolvent.denominator (1 - σ) t) := by
                apply integral_congr_ae
                filter_upwards with v
                apply integral_congr_ae
                filter_upwards with y
                exact hscalar y v
      _ = _ := by simp only [integral_conj]
  have hreflect :
      (∫ t in Icc (-U) (-H), F t) =
        ∫ t in Icc H U, F (-t) := by
    rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (show -U ≤ -H by linarith),
      ← intervalIntegral.integral_comp_neg (f := F) (a := H) (b := U)]
    rw [intervalIntegral.integral_of_le hHU,
      ← integral_Icc_eq_integral_Ioc]
  change ‖∫ t in Icc (-U) (-H), F t‖ =
    ‖∫ t in Icc H U, F t‖
  rw [hreflect]
  simp_rw [hpoint]
  rw [integral_conj, Complex.norm_conj]

theorem endpoint_contour_bound (Ψ : ℝ → ℝ)
    (d e left x ε σ H U g : ℝ)
    (hd : 0 < d) (he : 0 < e) (hleft : 0 < left)
    (hlex : left ≤ x) (hε : ε ∈ Ioo 0 1)
    (hσ : 1 < σ) (hσtwo : σ ≤ 2)
    (hH : 0 < H) (hHU : H ≤ U) (hg : 0 < g)
    (hdiff : ContDiff ℝ 1 Ψ)
    (hnonneg : ∀ v > 0, 0 ≤ Ψ v)
    (hsupport : Function.support Ψ ⊆ Icc (1 / 2) 2)
    (hmass : ∫ v in Ioi 0, Ψ v / v = 1)
    (hgap : ∀ y ∈ Icc left x, ∀ v ∈ Icc (1 / 2 : ℝ) 2,
      g ≤ |endpointPhase d e y v ε|) :
    ‖∫ t in Icc H U,
      (d : ℂ) ^ (-line σ t) *
        (e : ℂ) ^ (1 - line σ t) /
          OscillatoryResolvent.denominator (1 - σ) t *
            mellin (fun z => (Smooth1 Ψ ε z : ℂ)) (line σ t) *
              ((x : ℂ) ^ line σ t - (left : ℂ) ^ line σ t)‖ ≤
      (x - left) *
        (4 * d ^ (-σ) * e ^ (1 - σ) * x ^ (σ - 1)) *
          (4 / (g * H)) := by
  have heq :
      (∫ t in Icc H U,
        (d : ℂ) ^ (-line σ t) *
          (e : ℂ) ^ (1 - line σ t) /
            OscillatoryResolvent.denominator (1 - σ) t *
              mellin (fun z => (Smooth1 Ψ ε z : ℂ)) (line σ t) *
                ((x : ℂ) ^ line σ t - (left : ℂ) ^ line σ t)) =
      ∫ t in Icc H U, ∫ v in Icc (1 / 2 : ℝ) 2,
        ∫ y in Icc left x,
          ((endpointAmplitude d e y v ε σ * Ψ v : ℝ) : ℂ) *
            OscillatoryResolvent.phase (endpointPhase d e y v ε) t /
              OscillatoryResolvent.denominator (1 - σ) t := by
    apply integral_congr_ae
    filter_upwards with t
    exact endpoint_integrand Ψ d e left x ε σ t hd he hleft hlex
      hε.1 hσ hdiff hsupport
  rw [heq]
  exact endpoint_triple_bound Ψ d e left x ε σ H U g
    hd he hleft hlex hε hσ.le hσtwo hH hHU hg
    hdiff hnonneg hsupport hmass hgap

theorem endpoint_contour_negative_bound (Ψ : ℝ → ℝ)
    (d e left x ε σ H U g : ℝ)
    (hd : 0 < d) (he : 0 < e) (hleft : 0 < left)
    (hlex : left ≤ x) (hε : ε ∈ Ioo 0 1)
    (hσ : 1 < σ) (hσtwo : σ ≤ 2)
    (hH : 0 < H) (hHU : H ≤ U) (hg : 0 < g)
    (hdiff : ContDiff ℝ 1 Ψ)
    (hnonneg : ∀ v > 0, 0 ≤ Ψ v)
    (hsupport : Function.support Ψ ⊆ Icc (1 / 2) 2)
    (hmass : ∫ v in Ioi 0, Ψ v / v = 1)
    (hgap : ∀ y ∈ Icc left x, ∀ v ∈ Icc (1 / 2 : ℝ) 2,
      g ≤ |endpointPhase d e y v ε|) :
    ‖∫ t in Icc (-U) (-H),
      (d : ℂ) ^ (-line σ t) *
        (e : ℂ) ^ (1 - line σ t) /
          OscillatoryResolvent.denominator (1 - σ) t *
            mellin (fun z => (Smooth1 Ψ ε z : ℂ)) (line σ t) *
              ((x : ℂ) ^ line σ t - (left : ℂ) ^ line σ t)‖ ≤
      (x - left) *
        (4 * d ^ (-σ) * e ^ (1 - σ) * x ^ (σ - 1)) *
          (4 / (g * H)) := by
  have heq :
      (∫ t in Icc (-U) (-H),
        (d : ℂ) ^ (-line σ t) *
          (e : ℂ) ^ (1 - line σ t) /
            OscillatoryResolvent.denominator (1 - σ) t *
              mellin (fun z => (Smooth1 Ψ ε z : ℂ)) (line σ t) *
                ((x : ℂ) ^ line σ t - (left : ℂ) ^ line σ t)) =
      ∫ t in Icc (-U) (-H), ∫ v in Icc (1 / 2 : ℝ) 2,
        ∫ y in Icc left x,
          ((endpointAmplitude d e y v ε σ * Ψ v : ℝ) : ℂ) *
            OscillatoryResolvent.phase (endpointPhase d e y v ε) t /
              OscillatoryResolvent.denominator (1 - σ) t := by
    apply integral_congr_ae
    filter_upwards with t
    exact endpoint_integrand Ψ d e left x ε σ t hd he hleft hlex
      hε.1 hσ hdiff hsupport
  rw [heq, endpoint_triple_negative_eq_positive_norm Ψ d e left x ε σ H U hHU]
  exact endpoint_triple_bound Ψ d e left x ε σ H U g
    hd he hleft hlex hε hσ.le hσtwo hH hHU hg
    hdiff hnonneg hsupport hmass hgap

theorem endpoint_contour_continuous (Ψ : ℝ → ℝ)
    (d e left x ε σ : ℝ)
    (hd : 0 < d) (he : 0 < e) (hleft : 0 < left)
    (hlex : left ≤ x) (hε : ε ∈ Ioo 0 1)
    (hσ : 1 < σ) (hdiff : ContDiff ℝ 1 Ψ)
    (hnonneg : ∀ v > 0, 0 ≤ Ψ v)
    (hsupport : Function.support Ψ ⊆ Icc (1 / 2) 2)
    (hmass : ∫ v in Ioi 0, Ψ v / v = 1) :
    Continuous (fun t : ℝ =>
      (d : ℂ) ^ (-line σ t) *
        (e : ℂ) ^ (1 - line σ t) /
          OscillatoryResolvent.denominator (1 - σ) t *
            mellin (fun z => (Smooth1 Ψ ε z : ℂ)) (line σ t) *
              ((x : ℂ) ^ line σ t - (left : ℂ) ^ line σ t)) := by
  have hx : 0 < x := hleft.trans_le hlex
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have heC : (e : ℂ) ≠ 0 := by exact_mod_cast he.ne'
  have hleftC : (left : ℂ) ≠ 0 := by exact_mod_cast hleft.ne'
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hdp : Continuous (fun t : ℝ => (d : ℂ) ^ (-line σ t)) := by
    simp_rw [Complex.cpow_def_of_ne_zero hdC]
    unfold line
    fun_prop
  have hep : Continuous (fun t : ℝ => (e : ℂ) ^ (1 - line σ t)) := by
    simp_rw [Complex.cpow_def_of_ne_zero heC]
    unfold line
    fun_prop
  have hxp : Continuous (fun t : ℝ => (x : ℂ) ^ line σ t) := by
    simp_rw [Complex.cpow_def_of_ne_zero hxC]
    unfold line
    fun_prop
  have hlp : Continuous (fun t : ℝ => (left : ℂ) ^ line σ t) := by
    simp_rw [Complex.cpow_def_of_ne_zero hleftC]
    unfold line
    fun_prop
  have hden : ∀ t, OscillatoryResolvent.denominator (1 - σ) t ≠ 0 := by
    intro t hz
    have hh := congrArg Complex.re hz
    simp [OscillatoryResolvent.denominator] at hh
    linarith
  have hdenC : Continuous (fun t : ℝ =>
      OscillatoryResolvent.denominator (1 - σ) t) := by
    unfold OscillatoryResolvent.denominator
    fun_prop
  have hm := SmoothMellinVertical.continuous Ψ ε σ
    hdiff hnonneg hsupport hmass hε (by linarith)
  exact (((hdp.mul hep).div hdenC hden).mul hm).mul (hxp.sub hlp)

theorem cofactor_contour_bound (Ψ : ℝ → ℝ)
    (d a b left x ε σ H U g : ℝ)
    (hd : 0 < d) (ha : 0 < a) (hab : a ≤ b)
    (hleft : 0 < left) (hlex : left ≤ x)
    (hε : ε ∈ Ioo 0 1) (hσ : 1 < σ) (hσtwo : σ ≤ 2)
    (hH : 0 < H) (hHU : H ≤ U) (hg : 0 < g)
    (hdiff : ContDiff ℝ 1 Ψ)
    (hnonneg : ∀ v > 0, 0 ≤ Ψ v)
    (hsupport : Function.support Ψ ⊆ Icc (1 / 2) 2)
    (hmass : ∫ v in Ioi 0, Ψ v / v = 1)
    (hgapA : ∀ y ∈ Icc left x, ∀ v ∈ Icc (1 / 2 : ℝ) 2,
      g ≤ |endpointPhase d a y v ε|)
    (hgapB : ∀ y ∈ Icc left x, ∀ v ∈ Icc (1 / 2 : ℝ) 2,
      g ≤ |endpointPhase d b y v ε|) :
    ‖∫ t in Icc H U,
      (d : ℂ) ^ (-line σ t) *
        cofactor a b (line σ t) *
          mellin (fun z => (Smooth1 Ψ ε z : ℂ)) (line σ t) *
            ((x : ℂ) ^ line σ t - (left : ℂ) ^ line σ t)‖ ≤
      (x - left) * (16 * d ^ (-σ) * x ^ (σ - 1) *
        (a ^ (1 - σ) + b ^ (1 - σ))) / (g * H) := by
  have hb : 0 < b := ha.trans_le hab
  let E : ℝ → ℝ → ℂ := fun e t =>
    (d : ℂ) ^ (-line σ t) * (e : ℂ) ^ (1 - line σ t) /
      OscillatoryResolvent.denominator (1 - σ) t *
        mellin (fun z => (Smooth1 Ψ ε z : ℂ)) (line σ t) *
          ((x : ℂ) ^ line σ t - (left : ℂ) ^ line σ t)
  have hEa : IntegrableOn (E a) (Icc H U) :=
    (endpoint_contour_continuous Ψ d a left x ε σ hd ha hleft hlex
      hε hσ hdiff hnonneg hsupport hmass).integrableOn_Icc
  have hEb : IntegrableOn (E b) (Icc H U) :=
    (endpoint_contour_continuous Ψ d b left x ε σ hd hb hleft hlex
      hε hσ hdiff hnonneg hsupport hmass).integrableOn_Icc
  have hsplit :
      (∫ t in Icc H U,
        (d : ℂ) ^ (-line σ t) *
          cofactor a b (line σ t) *
            mellin (fun z => (Smooth1 Ψ ε z : ℂ)) (line σ t) *
              ((x : ℂ) ^ line σ t - (left : ℂ) ^ line σ t)) =
      (∫ t in Icc H U, E b t) - (∫ t in Icc H U, E a t) := by
    calc
      _ = ∫ t in Icc H U, E b t - E a t := by
        apply integral_congr_ae
        filter_upwards with t
        have hdne : OscillatoryResolvent.denominator (1 - σ) t =
            1 - line σ t := by
          unfold OscillatoryResolvent.denominator line
          push_cast
          ring
        have hcof : cofactor a b (line σ t) =
            ((b : ℂ) ^ (1 - line σ t) -
              (a : ℂ) ^ (1 - line σ t)) /
                OscillatoryResolvent.denominator (1 - σ) t := by
          rw [cofactor_quotient a b σ t ha hab hσ, hdne]
        rw [hcof]
        simp only [E]
        ring
      _ = _ := integral_sub hEb hEa
  have hboundA := endpoint_contour_bound Ψ d a left x ε σ H U g
    hd ha hleft hlex hε hσ hσtwo hH hHU hg
    hdiff hnonneg hsupport hmass hgapA
  have hboundB := endpoint_contour_bound Ψ d b left x ε σ H U g
    hd hb hleft hlex hε hσ hσtwo hH hHU hg
    hdiff hnonneg hsupport hmass hgapB
  change ‖∫ t in Icc H U, E a t‖ ≤ _ at hboundA
  change ‖∫ t in Icc H U, E b t‖ ≤ _ at hboundB
  rw [hsplit]
  calc
    _ ≤ ‖∫ t in Icc H U, E b t‖ +
        ‖∫ t in Icc H U, E a t‖ := norm_sub_le _ _
    _ ≤ (x - left) *
        (4 * d ^ (-σ) * b ^ (1 - σ) * x ^ (σ - 1)) *
          (4 / (g * H)) +
        (x - left) *
        (4 * d ^ (-σ) * a ^ (1 - σ) * x ^ (σ - 1)) *
          (4 / (g * H)) := add_le_add hboundB hboundA
    _ = _ := by ring

theorem cofactor_contour_negative_bound (Ψ : ℝ → ℝ)
    (d a b left x ε σ H U g : ℝ)
    (hd : 0 < d) (ha : 0 < a) (hab : a ≤ b)
    (hleft : 0 < left) (hlex : left ≤ x)
    (hε : ε ∈ Ioo 0 1) (hσ : 1 < σ) (hσtwo : σ ≤ 2)
    (hH : 0 < H) (hHU : H ≤ U) (hg : 0 < g)
    (hdiff : ContDiff ℝ 1 Ψ)
    (hnonneg : ∀ v > 0, 0 ≤ Ψ v)
    (hsupport : Function.support Ψ ⊆ Icc (1 / 2) 2)
    (hmass : ∫ v in Ioi 0, Ψ v / v = 1)
    (hgapA : ∀ y ∈ Icc left x, ∀ v ∈ Icc (1 / 2 : ℝ) 2,
      g ≤ |endpointPhase d a y v ε|)
    (hgapB : ∀ y ∈ Icc left x, ∀ v ∈ Icc (1 / 2 : ℝ) 2,
      g ≤ |endpointPhase d b y v ε|) :
    ‖∫ t in Icc (-U) (-H),
      (d : ℂ) ^ (-line σ t) *
        cofactor a b (line σ t) *
          mellin (fun z => (Smooth1 Ψ ε z : ℂ)) (line σ t) *
            ((x : ℂ) ^ line σ t - (left : ℂ) ^ line σ t)‖ ≤
      (x - left) * (16 * d ^ (-σ) * x ^ (σ - 1) *
        (a ^ (1 - σ) + b ^ (1 - σ))) / (g * H) := by
  have hb : 0 < b := ha.trans_le hab
  let E : ℝ → ℝ → ℂ := fun e t =>
    (d : ℂ) ^ (-line σ t) * (e : ℂ) ^ (1 - line σ t) /
      OscillatoryResolvent.denominator (1 - σ) t *
        mellin (fun z => (Smooth1 Ψ ε z : ℂ)) (line σ t) *
          ((x : ℂ) ^ line σ t - (left : ℂ) ^ line σ t)
  have hEa : IntegrableOn (E a) (Icc (-U) (-H)) :=
    (endpoint_contour_continuous Ψ d a left x ε σ hd ha hleft hlex
      hε hσ hdiff hnonneg hsupport hmass).integrableOn_Icc
  have hEb : IntegrableOn (E b) (Icc (-U) (-H)) :=
    (endpoint_contour_continuous Ψ d b left x ε σ hd hb hleft hlex
      hε hσ hdiff hnonneg hsupport hmass).integrableOn_Icc
  have hsplit :
      (∫ t in Icc (-U) (-H),
        (d : ℂ) ^ (-line σ t) *
          cofactor a b (line σ t) *
            mellin (fun z => (Smooth1 Ψ ε z : ℂ)) (line σ t) *
              ((x : ℂ) ^ line σ t - (left : ℂ) ^ line σ t)) =
      (∫ t in Icc (-U) (-H), E b t) -
        (∫ t in Icc (-U) (-H), E a t) := by
    calc
      _ = ∫ t in Icc (-U) (-H), E b t - E a t := by
        apply integral_congr_ae
        filter_upwards with t
        have hdne : OscillatoryResolvent.denominator (1 - σ) t =
            1 - line σ t := by
          unfold OscillatoryResolvent.denominator line
          push_cast
          ring
        have hcof : cofactor a b (line σ t) =
            ((b : ℂ) ^ (1 - line σ t) -
              (a : ℂ) ^ (1 - line σ t)) /
                OscillatoryResolvent.denominator (1 - σ) t := by
          rw [cofactor_quotient a b σ t ha hab hσ, hdne]
        rw [hcof]
        simp only [E]
        ring
      _ = _ := integral_sub hEb hEa
  have hboundA := endpoint_contour_negative_bound Ψ d a left x ε σ H U g
    hd ha hleft hlex hε hσ hσtwo hH hHU hg
    hdiff hnonneg hsupport hmass hgapA
  have hboundB := endpoint_contour_negative_bound Ψ d b left x ε σ H U g
    hd hb hleft hlex hε hσ hσtwo hH hHU hg
    hdiff hnonneg hsupport hmass hgapB
  change ‖∫ t in Icc (-U) (-H), E a t‖ ≤ _ at hboundA
  change ‖∫ t in Icc (-U) (-H), E b t‖ ≤ _ at hboundB
  rw [hsplit]
  calc
    _ ≤ ‖∫ t in Icc (-U) (-H), E b t‖ +
        ‖∫ t in Icc (-U) (-H), E a t‖ := norm_sub_le _ _
    _ ≤ (x - left) *
        (4 * d ^ (-σ) * b ^ (1 - σ) * x ^ (σ - 1)) *
          (4 / (g * H)) +
        (x - left) *
        (4 * d ^ (-σ) * a ^ (1 - σ) * x ^ (σ - 1)) *
          (4 / (g * H)) := add_le_add hboundB hboundA
    _ = _ := by ring

def shortKernel (s : Finset ℕ) (coeff : ℕ → ℂ)
    (Ψ : ℝ → ℝ) (ε σ left x a b t : ℝ) : ℂ :=
  verticalDirichlet152 s coeff σ t *
    cofactor a b (line σ t) *
      mellin (fun z => (Smooth1 Ψ ε z : ℂ)) (line σ t) *
        ((x : ℂ) ^ line σ t - (left : ℂ) ^ line σ t)

theorem short_kernel_integrable (s : Finset ℕ) (coeff : ℕ → ℂ)
    (Ψ : ℝ → ℝ) (ε σ left x a b : ℝ)
    (hleft : 0 < left) (hx : 0 < x) (ha : 0 < a) (hab : a ≤ b)
    (hs : ∀ d ∈ s, 0 < d)
    (hσ : 1 < σ) (hσtwo : σ ≤ 2) (hε : ε ∈ Ioo 0 1)
    (hdiff : ContDiff ℝ 1 Ψ) (hnonneg : ∀ v > 0, 0 ≤ Ψ v)
    (hsupport : Function.support Ψ ⊆ Icc (1 / 2) 2)
    (hmass : ∫ v in Ioi 0, Ψ v / v = 1) :
    Integrable (shortKernel s coeff Ψ ε σ left x a b) := by
  have hix := finite_contour_integrable s coeff Ψ ε σ x a b
    hx ha hab hs hσ hσtwo hε hdiff hnonneg hsupport hmass
  have hil := finite_contour_integrable s coeff Ψ ε σ left a b
    hleft ha hab hs hσ hσtwo hε hdiff hnonneg hsupport hmass
  have h := hix.sub hil
  apply h.congr
  filter_upwards with t
  unfold shortKernel
  simp only [Pi.sub_apply]
  ring

theorem finite_cofactor_contour_bound (s : Finset ℕ) (coeff : ℕ → ℂ)
    (Ψ : ℝ → ℝ) (ε σ left x a b H U g : ℝ)
    (hleft : 0 < left) (hlex : left ≤ x)
    (ha : 0 < a) (hab : a ≤ b)
    (hs : ∀ d ∈ s, 0 < d)
    (hσ : 1 < σ) (hσtwo : σ ≤ 2) (hε : ε ∈ Ioo 0 1)
    (hH : 0 < H) (hHU : H ≤ U) (hg : 0 < g)
    (hdiff : ContDiff ℝ 1 Ψ) (hnonneg : ∀ v > 0, 0 ≤ Ψ v)
    (hsupport : Function.support Ψ ⊆ Icc (1 / 2) 2)
    (hmass : ∫ v in Ioi 0, Ψ v / v = 1)
    (hgapA : ∀ d ∈ s, ∀ y ∈ Icc left x,
      ∀ v ∈ Icc (1 / 2 : ℝ) 2,
      g ≤ |endpointPhase d a y v ε|)
    (hgapB : ∀ d ∈ s, ∀ y ∈ Icc left x,
      ∀ v ∈ Icc (1 / 2 : ℝ) 2,
      g ≤ |endpointPhase d b y v ε|) :
    ‖∫ t in Icc H U, shortKernel s coeff Ψ ε σ left x a b t‖ ≤
      (x - left) * (16 * x ^ (σ - 1) *
        (a ^ (1 - σ) + b ^ (1 - σ))) *
          coefficientMass s coeff σ / (g * H) := by
  let T : ℕ → ℝ → ℂ := fun d t => coeff d *
    ((d : ℂ) ^ (-line σ t) * cofactor a b (line σ t) *
      mellin (fun z => (Smooth1 Ψ ε z : ℂ)) (line σ t) *
        ((x : ℂ) ^ line σ t - (left : ℂ) ^ line σ t))
  have hx : 0 < x := hleft.trans_le hlex
  have hTInt : ∀ d ∈ s, IntegrableOn (T d) (Icc H U) := by
    intro d hd
    have hsingle := short_kernel_integrable ({d}) coeff Ψ ε σ left x a b
      hleft hx ha hab (by simpa using hs d hd)
      hσ hσtwo hε hdiff hnonneg hsupport hmass
    have heq : T d = shortKernel ({d}) coeff Ψ ε σ left x a b := by
      funext t
      simp only [T, shortKernel, verticalDirichlet152,
        Finset.sum_singleton]
      unfold line
      ring
    rw [heq]
    exact hsingle.integrableOn
  have hpoint (t : ℝ) :
      shortKernel s coeff Ψ ε σ left x a b t =
        ∑ d ∈ s, T d t := by
    unfold shortKernel verticalDirichlet152 T
    unfold line
    simp only [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro d hd
    ring
  have hsum :
      (∫ t in Icc H U, shortKernel s coeff Ψ ε σ left x a b t) =
        ∑ d ∈ s, ∫ t in Icc H U, T d t := by
    simp_rw [hpoint]
    exact integral_finsetSum s (fun d hd => hTInt d hd)
  rw [hsum]
  calc
    _ ≤ ∑ d ∈ s, ‖∫ t in Icc H U, T d t‖ := norm_sum_le _ _
    _ ≤ ∑ d ∈ s, ‖coeff d‖ *
        ((x - left) * (16 * (d : ℝ) ^ (-σ) * x ^ (σ - 1) *
          (a ^ (1 - σ) + b ^ (1 - σ))) / (g * H)) := by
      apply Finset.sum_le_sum
      intro d hd
      have hdpos : (0 : ℝ) < d := by exact_mod_cast hs d hd
      have hb := cofactor_contour_bound Ψ (d : ℝ) a b left x ε σ H U g
        hdpos ha hab hleft hlex hε hσ hσtwo hH hHU hg
        hdiff hnonneg hsupport hmass
        (hgapA d hd) (hgapB d hd)
      have heq : (∫ t in Icc H U, T d t) = coeff d *
          (∫ t in Icc H U,
            (d : ℂ) ^ (-line σ t) *
              cofactor a b (line σ t) *
                mellin (fun z => (Smooth1 Ψ ε z : ℂ)) (line σ t) *
                  ((x : ℂ) ^ line σ t - (left : ℂ) ^ line σ t)) := by
        simp only [T, integral_const_mul]
      rw [heq, norm_mul]
      exact mul_le_mul_of_nonneg_left hb (norm_nonneg _)
    _ = _ := by
      unfold coefficientMass
      calc
        _ = ∑ d ∈ s,
            ((x - left) *
              (16 * x ^ (σ - 1) *
                (a ^ (1 - σ) + b ^ (1 - σ))) / (g * H)) *
              (‖coeff d‖ * (d : ℝ) ^ (-σ)) := by
                apply Finset.sum_congr rfl
                intro d hd
                ring
        _ = _ := by rw [← Finset.mul_sum]; ring

theorem finite_cofactor_contour_negative_bound
    (s : Finset ℕ) (coeff : ℕ → ℂ)
    (Ψ : ℝ → ℝ) (ε σ left x a b H U g : ℝ)
    (hleft : 0 < left) (hlex : left ≤ x)
    (ha : 0 < a) (hab : a ≤ b)
    (hs : ∀ d ∈ s, 0 < d)
    (hσ : 1 < σ) (hσtwo : σ ≤ 2) (hε : ε ∈ Ioo 0 1)
    (hH : 0 < H) (hHU : H ≤ U) (hg : 0 < g)
    (hdiff : ContDiff ℝ 1 Ψ) (hnonneg : ∀ v > 0, 0 ≤ Ψ v)
    (hsupport : Function.support Ψ ⊆ Icc (1 / 2) 2)
    (hmass : ∫ v in Ioi 0, Ψ v / v = 1)
    (hgapA : ∀ d ∈ s, ∀ y ∈ Icc left x,
      ∀ v ∈ Icc (1 / 2 : ℝ) 2,
      g ≤ |endpointPhase d a y v ε|)
    (hgapB : ∀ d ∈ s, ∀ y ∈ Icc left x,
      ∀ v ∈ Icc (1 / 2 : ℝ) 2,
      g ≤ |endpointPhase d b y v ε|) :
    ‖∫ t in Icc (-U) (-H),
      shortKernel s coeff Ψ ε σ left x a b t‖ ≤
      (x - left) * (16 * x ^ (σ - 1) *
        (a ^ (1 - σ) + b ^ (1 - σ))) *
          coefficientMass s coeff σ / (g * H) := by
  let T : ℕ → ℝ → ℂ := fun d t => coeff d *
    ((d : ℂ) ^ (-line σ t) * cofactor a b (line σ t) *
      mellin (fun z => (Smooth1 Ψ ε z : ℂ)) (line σ t) *
        ((x : ℂ) ^ line σ t - (left : ℂ) ^ line σ t))
  have hx : 0 < x := hleft.trans_le hlex
  have hTInt : ∀ d ∈ s, IntegrableOn (T d) (Icc (-U) (-H)) := by
    intro d hd
    have hsingle := short_kernel_integrable ({d}) coeff Ψ ε σ left x a b
      hleft hx ha hab (by simpa using hs d hd)
      hσ hσtwo hε hdiff hnonneg hsupport hmass
    have heq : T d = shortKernel ({d}) coeff Ψ ε σ left x a b := by
      funext t
      simp only [T, shortKernel, verticalDirichlet152,
        Finset.sum_singleton]
      unfold line
      ring
    rw [heq]
    exact hsingle.integrableOn
  have hpoint (t : ℝ) :
      shortKernel s coeff Ψ ε σ left x a b t =
        ∑ d ∈ s, T d t := by
    unfold shortKernel verticalDirichlet152 T
    unfold line
    simp only [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro d hd
    ring
  have hsum :
      (∫ t in Icc (-U) (-H),
        shortKernel s coeff Ψ ε σ left x a b t) =
        ∑ d ∈ s, ∫ t in Icc (-U) (-H), T d t := by
    simp_rw [hpoint]
    exact integral_finsetSum s (fun d hd => hTInt d hd)
  rw [hsum]
  calc
    _ ≤ ∑ d ∈ s, ‖∫ t in Icc (-U) (-H), T d t‖ :=
      norm_sum_le _ _
    _ ≤ ∑ d ∈ s, ‖coeff d‖ *
        ((x - left) * (16 * (d : ℝ) ^ (-σ) * x ^ (σ - 1) *
          (a ^ (1 - σ) + b ^ (1 - σ))) / (g * H)) := by
      apply Finset.sum_le_sum
      intro d hd
      have hdpos : (0 : ℝ) < d := by exact_mod_cast hs d hd
      have hb := cofactor_contour_negative_bound Ψ (d : ℝ) a b
        left x ε σ H U g hdpos ha hab hleft hlex hε hσ hσtwo
        hH hHU hg hdiff hnonneg hsupport hmass
        (hgapA d hd) (hgapB d hd)
      have heq : (∫ t in Icc (-U) (-H), T d t) = coeff d *
          (∫ t in Icc (-U) (-H),
            (d : ℂ) ^ (-line σ t) *
              cofactor a b (line σ t) *
                mellin (fun z => (Smooth1 Ψ ε z : ℂ)) (line σ t) *
                  ((x : ℂ) ^ line σ t -
                    (left : ℂ) ^ line σ t)) := by
        simp only [T, integral_const_mul]
      rw [heq, norm_mul]
      exact mul_le_mul_of_nonneg_left hb (norm_nonneg _)
    _ = _ := by
      unfold coefficientMass
      calc
        _ = ∑ d ∈ s,
            ((x - left) *
              (16 * x ^ (σ - 1) *
                (a ^ (1 - σ) + b ^ (1 - σ))) / (g * H)) *
              (‖coeff d‖ * (d : ℝ) ^ (-σ)) := by
                apply Finset.sum_congr rfl
                intro d hd
                ring
        _ = _ := by rw [← Finset.mul_sum]; ring

theorem positive_infinite_cofactor_tail (s : Finset ℕ) (coeff : ℕ → ℂ)
    (Ψ : ℝ → ℝ) (ε σ left x a b H g : ℝ)
    (hleft : 0 < left) (hlex : left ≤ x)
    (ha : 0 < a) (hab : a ≤ b)
    (hs : ∀ d ∈ s, 0 < d)
    (hσ : 1 < σ) (hσtwo : σ ≤ 2) (hε : ε ∈ Ioo 0 1)
    (hH : 0 < H) (hg : 0 < g)
    (hdiff : ContDiff ℝ 1 Ψ) (hnonneg : ∀ v > 0, 0 ≤ Ψ v)
    (hsupport : Function.support Ψ ⊆ Icc (1 / 2) 2)
    (hmass : ∫ v in Ioi 0, Ψ v / v = 1)
    (hgapA : ∀ d ∈ s, ∀ y ∈ Icc left x,
      ∀ v ∈ Icc (1 / 2 : ℝ) 2,
      g ≤ |endpointPhase d a y v ε|)
    (hgapB : ∀ d ∈ s, ∀ y ∈ Icc left x,
      ∀ v ∈ Icc (1 / 2 : ℝ) 2,
      g ≤ |endpointPhase d b y v ε|) :
    ‖∫ t in Ioi H, shortKernel s coeff Ψ ε σ left x a b t‖ ≤
      (x - left) * (16 * x ^ (σ - 1) *
        (a ^ (1 - σ) + b ^ (1 - σ))) *
          coefficientMass s coeff σ / (g * H) := by
  have hx : 0 < x := hleft.trans_le hlex
  have hInt := short_kernel_integrable s coeff Ψ ε σ left x a b
    hleft hx ha hab hs hσ hσtwo hε hdiff hnonneg hsupport hmass
  have hlim :
      Tendsto (fun U : ℝ => ∫ t in Icc H U,
        shortKernel s coeff Ψ ε σ left x a b t) atTop
          (𝓝 (∫ t in Ioi H,
            shortKernel s coeff Ψ ε σ left x a b t)) := by
    apply Tendsto.congr' _ (intervalIntegral_tendsto_integral_Ioi
      H hInt.integrableOn tendsto_id)
    filter_upwards [eventually_ge_atTop H] with U hHU
    rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hHU]
    rfl
  have hnormlim := (continuous_norm.tendsto
    (∫ t in Ioi H, shortKernel s coeff Ψ ε σ left x a b t)).comp hlim
  apply le_of_tendsto hnormlim
  filter_upwards [eventually_ge_atTop H] with U hHU
  exact finite_cofactor_contour_bound s coeff Ψ ε σ left x a b H U g
    hleft hlex ha hab hs hσ hσtwo hε hH hHU hg
    hdiff hnonneg hsupport hmass hgapA hgapB

theorem negative_infinite_cofactor_tail (s : Finset ℕ) (coeff : ℕ → ℂ)
    (Ψ : ℝ → ℝ) (ε σ left x a b H g : ℝ)
    (hleft : 0 < left) (hlex : left ≤ x)
    (ha : 0 < a) (hab : a ≤ b)
    (hs : ∀ d ∈ s, 0 < d)
    (hσ : 1 < σ) (hσtwo : σ ≤ 2) (hε : ε ∈ Ioo 0 1)
    (hH : 0 < H) (hg : 0 < g)
    (hdiff : ContDiff ℝ 1 Ψ) (hnonneg : ∀ v > 0, 0 ≤ Ψ v)
    (hsupport : Function.support Ψ ⊆ Icc (1 / 2) 2)
    (hmass : ∫ v in Ioi 0, Ψ v / v = 1)
    (hgapA : ∀ d ∈ s, ∀ y ∈ Icc left x,
      ∀ v ∈ Icc (1 / 2 : ℝ) 2,
      g ≤ |endpointPhase d a y v ε|)
    (hgapB : ∀ d ∈ s, ∀ y ∈ Icc left x,
      ∀ v ∈ Icc (1 / 2 : ℝ) 2,
      g ≤ |endpointPhase d b y v ε|) :
    ‖∫ t in Iic (-H), shortKernel s coeff Ψ ε σ left x a b t‖ ≤
      (x - left) * (16 * x ^ (σ - 1) *
        (a ^ (1 - σ) + b ^ (1 - σ))) *
          coefficientMass s coeff σ / (g * H) := by
  have hx : 0 < x := hleft.trans_le hlex
  have hInt := short_kernel_integrable s coeff Ψ ε σ left x a b
    hleft hx ha hab hs hσ hσtwo hε hdiff hnonneg hsupport hmass
  have hlim :
      Tendsto (fun U : ℝ => ∫ t in Icc (-U) (-H),
        shortKernel s coeff Ψ ε σ left x a b t) atTop
          (𝓝 (∫ t in Iic (-H),
            shortKernel s coeff Ψ ε σ left x a b t)) := by
    apply Tendsto.congr' _ (intervalIntegral_tendsto_integral_Iic
      (-H) hInt.integrableOn tendsto_neg_atTop_atBot)
    filter_upwards [eventually_ge_atTop H] with U hHU
    rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (show -U ≤ -H by linarith)]
  have hnormlim := (continuous_norm.tendsto
    (∫ t in Iic (-H), shortKernel s coeff Ψ ε σ left x a b t)).comp hlim
  apply le_of_tendsto hnormlim
  filter_upwards [eventually_ge_atTop H] with U hHU
  exact finite_cofactor_contour_negative_bound s coeff Ψ ε σ
    left x a b H U g hleft hlex ha hab hs hσ hσtwo hε
    hH hHU hg hdiff hnonneg hsupport hmass hgapA hgapB

end ContinuousCofactorTail

#print axioms ContinuousCofactorTail.positive_infinite_cofactor_tail
#print axioms ContinuousCofactorTail.negative_infinite_cofactor_tail
run_cmd do
  for target in [``ContinuousCofactorTail.endpoint_integrand,
      ``ContinuousCofactorTail.cofactor_contour_bound,
      ``ContinuousCofactorTail.finite_cofactor_contour_bound,
      ``ContinuousCofactorTail.positive_infinite_cofactor_tail,
      ``ContinuousCofactorTail.negative_infinite_cofactor_tail] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice ||
          ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "CONTINUOUS COFACTOR TAIL PASSED"
