import SmoothedDirichletKernel
import SmoothMellinVertical

/-!
The continuous positive cofactor has the same Mellin kernel as a flat
Dirichlet polynomial. Smooth1 is evaluated at d*u/x, matching the seed's
finite inversion convention.
-/

set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace ContinuousCofactorMellin
open MellinWindowFactor Erdos374.HarmanGram152

def cofactor (a b : ℝ) (z : ℂ) : ℂ :=
  ∫ u in Icc a b, (u : ℂ) ^ (-z)

theorem cofactor_quotient (a b σ t : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hσ : 1 < σ) :
    cofactor a b (line σ t) =
      ((b : ℂ) ^ (1 - line σ t) -
        (a : ℂ) ^ (1 - line σ t)) / (1 - line σ t) := by
  have hnot : -(line σ t) ≠ -1 := by
    intro h
    have hr := congrArg Complex.re h
    simp [line] at hr
    linarith
  have hzero : (0 : ℝ) ∉ Set.uIcc a b := by
    rw [Set.uIcc_of_le hab]
    exact fun h => (not_le_of_gt ha) h.1
  unfold cofactor
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hab,
    integral_cpow (Or.inr ⟨hnot, hzero⟩)]
  congr 1
  · congr 1 <;> ring
  · ring

theorem ratio_power (d u x : ℝ) (hd : 0 < d) (hu : 0 < u)
    (hx : 0 < x) (z : ℂ) :
    ((d * u / x : ℝ) : ℂ) ^ (-z) =
      (d : ℂ) ^ (-z) * (u : ℂ) ^ (-z) * (x : ℂ) ^ z := by
  rw [FiniteMellinInversion.ratio_power (d * u) x (mul_pos hd hu) hx]
  rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hd.le hu.le]

theorem single_point (Ψ : ℝ → ℝ) (ε σ d u x : ℝ)
    (hd : 0 < d) (hu : 0 < u) (hx : 0 < x)
    (hσ : 1 < σ) (hσtwo : σ ≤ 2) (hε : ε ∈ Ioo 0 1)
    (hdiff : ContDiff ℝ 1 Ψ) (hnonneg : ∀ y > 0, 0 ≤ Ψ y)
    (hsupport : Function.support Ψ ⊆ Icc (1 / 2) 2)
    (hmass : ∫ y in Ioi 0, Ψ y / y = 1) :
    ((Smooth1 Ψ ε (d * u / x) : ℝ) : ℂ) =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ t : ℝ, ((d * u / x : ℝ) : ℂ) ^ (-line σ t) *
          mellin (fun y => (Smooth1 Ψ ε y : ℂ)) (line σ t) := by
  let f : ℝ → ℂ := fun y => (Smooth1 Ψ ε y : ℂ)
  have hr : 0 < d * u / x := by positivity
  have hconv : MellinConvergent f σ :=
    Smooth1MellinConvergent hdiff hsupport hε hnonneg hmass
      (by simp only [Complex.ofReal_re]; linarith)
  have hvert : Complex.VerticalIntegrable (mellin f) σ :=
    SmoothedChebyshevDirichlet_aux_integrable hdiff hnonneg hsupport hmass
      hε.1 hε.2 hσ hσtwo
  have hcontinuous : ContinuousAt f (d * u / x) :=
    Complex.continuous_ofReal.continuousAt.comp
      (Smooth1ContinuousAt hdiff hnonneg hsupport hε.1 hr)
  have hh := mellinInv_mellin_eq σ f hr hconv hvert hcontinuous
  simpa only [f, mellinInv, Complex.real_smul, smul_eq_mul, line,
    mul_comm Complex.I] using hh.symm

def joint (Ψ : ℝ → ℝ) (ε σ d x : ℝ) (z : ℝ × ℝ) : ℂ :=
  ((d * z.2 / x : ℝ) : ℂ) ^ (-line σ z.1) *
    mellin (fun y => (Smooth1 Ψ ε y : ℂ)) (line σ z.1)

theorem joint_integrable (Ψ : ℝ → ℝ) (ε σ d x a b : ℝ)
    (hd : 0 < d) (hx : 0 < x) (ha : 0 < a) (_hab : a ≤ b)
    (hσ : 1 < σ) (hσtwo : σ ≤ 2) (hε : ε ∈ Ioo 0 1)
    (hdiff : ContDiff ℝ 1 Ψ) (hnonneg : ∀ y > 0, 0 ≤ Ψ y)
    (hsupport : Function.support Ψ ⊆ Icc (1 / 2) 2)
    (hmass : ∫ y in Ioi 0, Ψ y / y = 1) :
    Integrable (joint Ψ ε σ d x)
      (volume.prod (volume.restrict (Icc a b))) := by
  let f : ℝ → ℂ := fun y => (Smooth1 Ψ ε y : ℂ)
  let M : ℝ → ℂ := fun t => mellin f (line σ t)
  let R : ℝ := (d * a / x) ^ (-σ)
  have hM : Integrable M :=
    SmoothMellinVertical.integrable Ψ ε σ hdiff hnonneg hsupport hmass
      hε (by linarith) hσtwo
  have hMc : Continuous M :=
    SmoothMellinVertical.continuous Ψ ε σ hdiff hnonneg hsupport hmass
      hε (by linarith)
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hdom : Integrable (fun z : ℝ × ℝ => R * ‖M z.1‖)
      (volume.prod (volume.restrict (Icc a b))) := by
    have hh := (hM.norm.const_mul R).mul_prod
      (integrable_const (1 : ℝ) (μ := volume.restrict (Icc a b)))
    simpa only [one_mul, mul_one] using hh
  have hpowmeas : Measurable (fun z : ℝ × ℝ =>
      ((d * z.2 / x : ℝ) : ℂ) ^ (-line σ z.1)) := by
    unfold line
    fun_prop
  have hMmeas : Measurable (fun z : ℝ × ℝ => M z.1) :=
    hMc.measurable.comp measurable_fst
  have hJmeas : Measurable (joint Ψ ε σ d x) := by
    unfold joint
    exact hpowmeas.mul hMmeas
  have haez : ∀ᵐ z ∂((volume : Measure ℝ).prod
      (volume.restrict (Icc a b))), z.2 ∈ Icc a b := by
    apply (Measure.ae_prod_iff_ae_ae
      (measurableSet_Icc.preimage measurable_snd)).mpr
    exact Filter.Eventually.of_forall (fun _ => ae_restrict_mem measurableSet_Icc)
  apply Integrable.mono' hdom hJmeas.aestronglyMeasurable
  filter_upwards [haez] with z hz
  have hu : 0 < z.2 := lt_of_lt_of_le ha hz.1
  have hr : 0 < d * z.2 / x := by positivity
  have hbase : d * a / x ≤ d * z.2 / x := by
    apply (div_le_div_iff₀ hx hx).mpr
    nlinarith [mul_le_mul_of_nonneg_left hz.1 hd.le]
  have hpow : (d * z.2 / x) ^ (-σ) ≤ R :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hbase (by linarith)
  dsimp [joint, M]
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hr]
  simp only [line, Complex.neg_re, Complex.add_re, Complex.ofReal_re,
    Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im,
    zero_mul, mul_zero, sub_zero, add_zero]
  exact mul_le_mul_of_nonneg_right hpow (norm_nonneg _)

theorem single_integrated (Ψ : ℝ → ℝ) (ε σ d x a b : ℝ)
    (hd : 0 < d) (hx : 0 < x) (ha : 0 < a) (hab : a ≤ b)
    (hσ : 1 < σ) (hσtwo : σ ≤ 2) (hε : ε ∈ Ioo 0 1)
    (hdiff : ContDiff ℝ 1 Ψ) (hnonneg : ∀ y > 0, 0 ≤ Ψ y)
    (hsupport : Function.support Ψ ⊆ Icc (1 / 2) 2)
    (hmass : ∫ y in Ioi 0, Ψ y / y = 1) :
    (∫ u in Icc a b, ((Smooth1 Ψ ε (d * u / x) : ℝ) : ℂ)) =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ t : ℝ, (d : ℂ) ^ (-line σ t) * cofactor a b (line σ t) *
          mellin (fun y => (Smooth1 Ψ ε y : ℂ)) (line σ t) *
          (x : ℂ) ^ line σ t := by
  let c : ℂ := ((1 / (2 * Real.pi) : ℝ) : ℂ)
  let M : ℝ → ℂ := fun t =>
    mellin (fun y => (Smooth1 Ψ ε y : ℂ)) (line σ t)
  have hJ := joint_integrable Ψ ε σ d x a b hd hx ha hab hσ hσtwo
    hε hdiff hnonneg hsupport hmass
  have hswap :
      (∫ u in Icc a b, ∫ t : ℝ, joint Ψ ε σ d x (t, u)) =
        ∫ t : ℝ, ∫ u in Icc a b, joint Ψ ε σ d x (t, u) :=
    (integral_integral_swap
      (f := fun t u => joint Ψ ε σ d x (t, u)) hJ).symm
  calc
    (∫ u in Icc a b, ((Smooth1 Ψ ε (d * u / x) : ℝ) : ℂ)) =
        ∫ u in Icc a b, c * ∫ t : ℝ, joint Ψ ε σ d x (t, u) := by
          apply integral_congr_ae
          filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
          exact single_point Ψ ε σ d u x hd (lt_of_lt_of_le ha hu.1) hx
            hσ hσtwo hε hdiff hnonneg hsupport hmass
    _ = c * ∫ u in Icc a b, ∫ t : ℝ, joint Ψ ε σ d x (t, u) :=
      integral_const_mul c _
    _ = c * ∫ t : ℝ, ∫ u in Icc a b, joint Ψ ε σ d x (t, u) := by rw [hswap]
    _ = c * ∫ t : ℝ, (d : ℂ) ^ (-line σ t) * cofactor a b (line σ t) *
          M t * (x : ℂ) ^ line σ t := by
          congr 1
          apply integral_congr_ae
          filter_upwards with t
          unfold cofactor
          have hinner :
              (∫ u in Icc a b, joint Ψ ε σ d x (t, u)) =
                ∫ u in Icc a b, (d : ℂ) ^ (-line σ t) *
                  (u : ℂ) ^ (-line σ t) * (x : ℂ) ^ line σ t * M t := by
            apply integral_congr_ae
            filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
            rw [joint, ratio_power d u x hd (lt_of_lt_of_le ha hu.1) hx]
          rw [hinner]
          simp only [integral_const_mul, integral_mul_const]
          ring

theorem contour_integrable (Ψ : ℝ → ℝ) (ε σ d x a b : ℝ)
    (hd : 0 < d) (hx : 0 < x) (ha : 0 < a) (hab : a ≤ b)
    (hσ : 1 < σ) (hσtwo : σ ≤ 2) (hε : ε ∈ Ioo 0 1)
    (hdiff : ContDiff ℝ 1 Ψ) (hnonneg : ∀ y > 0, 0 ≤ Ψ y)
    (hsupport : Function.support Ψ ⊆ Icc (1 / 2) 2)
    (hmass : ∫ y in Ioi 0, Ψ y / y = 1) :
    Integrable (fun t : ℝ => (d : ℂ) ^ (-line σ t) *
      cofactor a b (line σ t) *
      mellin (fun y => (Smooth1 Ψ ε y : ℂ)) (line σ t) *
      (x : ℂ) ^ line σ t) := by
  let M : ℝ → ℂ := fun t =>
    mellin (fun y => (Smooth1 Ψ ε y : ℂ)) (line σ t)
  have hJ := joint_integrable Ψ ε σ d x a b hd hx ha hab hσ hσtwo
    hε hdiff hnonneg hsupport hmass
  have h := hJ.integral_prod_left
  apply h.congr
  filter_upwards with t
  unfold cofactor
  have hinner :
      (∫ u in Icc a b, joint Ψ ε σ d x (t, u)) =
        ∫ u in Icc a b, (d : ℂ) ^ (-line σ t) *
          (u : ℂ) ^ (-line σ t) * (x : ℂ) ^ line σ t * M t := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    rw [joint, ratio_power d u x hd (lt_of_lt_of_le ha hu.1) hx]
  rw [hinner]
  simp only [integral_const_mul, integral_mul_const]
  ring

theorem finite_integrated (s : Finset ℕ) (coeff : ℕ → ℂ)
    (Ψ : ℝ → ℝ) (ε σ x a b : ℝ)
    (hx : 0 < x) (ha : 0 < a) (hab : a ≤ b)
    (hs : ∀ d ∈ s, 0 < d)
    (hσ : 1 < σ) (hσtwo : σ ≤ 2) (hε : ε ∈ Ioo 0 1)
    (hdiff : ContDiff ℝ 1 Ψ) (hnonneg : ∀ y > 0, 0 ≤ Ψ y)
    (hsupport : Function.support Ψ ⊆ Icc (1 / 2) 2)
    (hmass : ∫ y in Ioi 0, Ψ y / y = 1) :
    (∑ d ∈ s, coeff d *
      ∫ u in Icc a b, ((Smooth1 Ψ ε ((d : ℝ) * u / x) : ℝ) : ℂ)) =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ t : ℝ, verticalDirichlet152 s coeff σ t *
          cofactor a b (line σ t) *
          mellin (fun y => (Smooth1 Ψ ε y : ℂ)) (line σ t) *
          (x : ℂ) ^ line σ t := by
  have hterm (d : ℕ) (hd : d ∈ s) :
      coeff d *
        (∫ u in Icc a b,
          ((Smooth1 Ψ ε ((d : ℝ) * u / x) : ℝ) : ℂ)) =
        ((1 / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ t : ℝ, coeff d * ((d : ℂ) ^ (-line σ t) *
            cofactor a b (line σ t) *
            mellin (fun y => (Smooth1 Ψ ε y : ℂ)) (line σ t) *
            (x : ℂ) ^ line σ t) := by
    have hdpos : (0 : ℝ) < d := by exact_mod_cast hs d hd
    rw [single_integrated Ψ ε σ (d : ℝ) x a b hdpos hx ha hab
      hσ hσtwo hε hdiff hnonneg hsupport hmass]
    push_cast
    simp only [integral_const_mul]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  congr 1
  rw [← integral_finsetSum]
  · apply integral_congr_ae
    filter_upwards with t
    unfold verticalDirichlet152
    rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro d hd
    unfold line
    ring
  · intro d hd
    have hdpos : (0 : ℝ) < d := by exact_mod_cast hs d hd
    exact (contour_integrable Ψ ε σ (d : ℝ) x a b hdpos hx ha hab
      hσ hσtwo hε hdiff hnonneg hsupport hmass).const_mul (coeff d)

theorem finite_contour_integrable (s : Finset ℕ) (coeff : ℕ → ℂ)
    (Ψ : ℝ → ℝ) (ε σ x a b : ℝ)
    (hx : 0 < x) (ha : 0 < a) (hab : a ≤ b)
    (hs : ∀ d ∈ s, 0 < d)
    (hσ : 1 < σ) (hσtwo : σ ≤ 2) (hε : ε ∈ Ioo 0 1)
    (hdiff : ContDiff ℝ 1 Ψ) (hnonneg : ∀ y > 0, 0 ≤ Ψ y)
    (hsupport : Function.support Ψ ⊆ Icc (1 / 2) 2)
    (hmass : ∫ y in Ioi 0, Ψ y / y = 1) :
    Integrable (fun t : ℝ => verticalDirichlet152 s coeff σ t *
      cofactor a b (line σ t) *
      mellin (fun y => (Smooth1 Ψ ε y : ℂ)) (line σ t) *
      (x : ℂ) ^ line σ t) := by
  have hsum : Integrable (fun t : ℝ =>
      ∑ d ∈ s, coeff d * ((d : ℂ) ^ (-line σ t) *
        cofactor a b (line σ t) *
        mellin (fun y => (Smooth1 Ψ ε y : ℂ)) (line σ t) *
        (x : ℂ) ^ line σ t)) := by
    apply integrable_finsetSum s
    intro d hd
    have hdpos : (0 : ℝ) < d := by exact_mod_cast hs d hd
    exact (contour_integrable Ψ ε σ (d : ℝ) x a b hdpos hx ha hab
      hσ hσtwo hε hdiff hnonneg hsupport hmass).const_mul (coeff d)
  apply hsum.congr
  filter_upwards with t
  unfold verticalDirichlet152 line
  rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d hd
  ring

theorem finite_short_window (s : Finset ℕ) (coeff : ℕ → ℂ)
    (Ψ : ℝ → ℝ) (ε σ x left a b : ℝ)
    (hx : 0 < x) (hleft : 0 < left) (ha : 0 < a) (hab : a ≤ b)
    (hs : ∀ d ∈ s, 0 < d)
    (hσ : 1 < σ) (hσtwo : σ ≤ 2) (hε : ε ∈ Ioo 0 1)
    (hdiff : ContDiff ℝ 1 Ψ) (hnonneg : ∀ y > 0, 0 ≤ Ψ y)
    (hsupport : Function.support Ψ ⊆ Icc (1 / 2) 2)
    (hmass : ∫ y in Ioi 0, Ψ y / y = 1) :
    (∑ d ∈ s, coeff d *
      ((∫ u in Icc a b,
        ((Smooth1 Ψ ε ((d : ℝ) * u / x) : ℝ) : ℂ)) -
       (∫ u in Icc a b,
        ((Smooth1 Ψ ε ((d : ℝ) * u / left) : ℝ) : ℂ)))) =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ t : ℝ, verticalDirichlet152 s coeff σ t *
          cofactor a b (line σ t) *
          mellin (fun y => (Smooth1 Ψ ε y : ℂ)) (line σ t) *
          ((x : ℂ) ^ line σ t - (left : ℂ) ^ line σ t) := by
  have hsum :
      (∑ d ∈ s, coeff d *
        ((∫ u in Icc a b,
          ((Smooth1 Ψ ε ((d : ℝ) * u / x) : ℝ) : ℂ)) -
         (∫ u in Icc a b,
          ((Smooth1 Ψ ε ((d : ℝ) * u / left) : ℝ) : ℂ)))) =
      (∑ d ∈ s, coeff d *
        (∫ u in Icc a b,
          ((Smooth1 Ψ ε ((d : ℝ) * u / x) : ℝ) : ℂ))) -
      (∑ d ∈ s, coeff d *
        (∫ u in Icc a b,
          ((Smooth1 Ψ ε ((d : ℝ) * u / left) : ℝ) : ℂ))) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    ring
  rw [hsum,
    finite_integrated s coeff Ψ ε σ x a b hx ha hab hs
      hσ hσtwo hε hdiff hnonneg hsupport hmass,
    finite_integrated s coeff Ψ ε σ left a b hleft ha hab hs
      hσ hσtwo hε hdiff hnonneg hsupport hmass,
    ← mul_sub]
  congr 1
  rw [← integral_sub
    (finite_contour_integrable s coeff Ψ ε σ x a b hx ha hab hs
      hσ hσtwo hε hdiff hnonneg hsupport hmass)
    (finite_contour_integrable s coeff Ψ ε σ left a b hleft ha hab hs
      hσ hσtwo hε hdiff hnonneg hsupport hmass)]
  apply integral_congr_ae
  filter_upwards with t
  ring

theorem cutoff_integrable (Ψ : ℝ → ℝ) (ε d x a b : ℝ)
    (hd : 0 < d) (hx : 0 < x) (ha : 0 < a) (hε : 0 < ε)
    (hdiff : ContDiff ℝ 1 Ψ) (hnonneg : ∀ y > 0, 0 ≤ Ψ y)
    (hsupport : Function.support Ψ ⊆ Icc (1 / 2) 2) :
    Integrable (fun u : ℝ => ((Smooth1 Ψ ε (d * u / x) : ℝ) : ℂ))
      (volume.restrict (Icc a b)) := by
  have hc : ContinuousOn
      (fun u : ℝ => ((Smooth1 Ψ ε (d * u / x) : ℝ) : ℂ))
      (Icc a b) := by
    intro u hu
    have hu : 0 < u := lt_of_lt_of_le ha hu.1
    have hr : 0 < d * u / x := by positivity
    have hratio : ContinuousAt (fun v : ℝ => d * v / x) u := by fun_prop
    have hcut : ContinuousAt
        (fun r : ℝ => ((Smooth1 Ψ ε r : ℝ) : ℂ))
        (d * u / x) :=
      Complex.continuous_ofReal.continuousAt.comp
        (Smooth1ContinuousAt hdiff hnonneg hsupport hε hr)
    exact (ContinuousAt.comp' (f := fun v : ℝ => d * v / x)
      hcut hratio).continuousWithinAt
  exact hc.integrableOn_compact isCompact_Icc

theorem finite_short_window_integrand (s : Finset ℕ) (coeff : ℕ → ℂ)
    (Ψ : ℝ → ℝ) (ε σ x left a b : ℝ)
    (hx : 0 < x) (hleft : 0 < left) (ha : 0 < a) (hab : a ≤ b)
    (hs : ∀ d ∈ s, 0 < d)
    (hσ : 1 < σ) (hσtwo : σ ≤ 2) (hε : ε ∈ Ioo 0 1)
    (hdiff : ContDiff ℝ 1 Ψ) (hnonneg : ∀ y > 0, 0 ≤ Ψ y)
    (hsupport : Function.support Ψ ⊆ Icc (1 / 2) 2)
    (hmass : ∫ y in Ioi 0, Ψ y / y = 1) :
    (∑ d ∈ s, coeff d *
      (∫ u in Icc a b,
        (((Smooth1 Ψ ε ((d : ℝ) * u / x) : ℝ) : ℂ) -
         ((Smooth1 Ψ ε ((d : ℝ) * u / left) : ℝ) : ℂ)))) =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ t : ℝ, verticalDirichlet152 s coeff σ t *
          cofactor a b (line σ t) *
          mellin (fun y => (Smooth1 Ψ ε y : ℂ)) (line σ t) *
          ((x : ℂ) ^ line σ t - (left : ℂ) ^ line σ t) := by
  rw [← finite_short_window s coeff Ψ ε σ x left a b hx hleft ha hab hs
    hσ hσtwo hε hdiff hnonneg hsupport hmass]
  apply Finset.sum_congr rfl
  intro d hd
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hs d hd
  rw [integral_sub
    (cutoff_integrable Ψ ε (d : ℝ) x a b hdpos hx ha hε.1
      hdiff hnonneg hsupport)
    (cutoff_integrable Ψ ε (d : ℝ) left a b hdpos hleft ha hε.1
      hdiff hnonneg hsupport)]

theorem mellin_one_eq_integral (Ψ : ℝ → ℝ) (ε : ℝ) :
    mellin (fun y => (Smooth1 Ψ ε y : ℂ)) 1 =
      ∫ u in Ioi (0 : ℝ), (Smooth1 Ψ ε u : ℂ) := by
  simp [mellin]

theorem scaled_cutoff_integral (Ψ : ℝ → ℝ) (ε d x : ℝ)
    (hd : 0 < d) (hx : 0 < x) :
    (∫ u in Ioi (0 : ℝ), (Smooth1 Ψ ε (d * u / x) : ℂ)) =
      ((x / d : ℝ) : ℂ) *
        mellin (fun y => (Smooth1 Ψ ε y : ℂ)) 1 := by
  have hr : 0 < d / x := div_pos hd hx
  have heq : (fun u : ℝ => (Smooth1 Ψ ε (d * u / x) : ℂ)) =
      (fun u : ℝ => (Smooth1 Ψ ε ((d / x) * u) : ℂ)) := by
    funext u
    congr 1
    ring
  rw [heq, integral_comp_mul_left_Ioi (fun u : ℝ =>
    (Smooth1 Ψ ε u : ℂ)) 0 hr]
  simp only [mul_zero, Complex.real_smul, mellin_one_eq_integral]
  congr 1
  exact_mod_cast (by field_simp : (d / x)⁻¹ = x / d)

theorem cutoff_integrable_positive (Ψ : ℝ → ℝ) (ε : ℝ)
    (hε : ε ∈ Ioo 0 1)
    (hdiff : ContDiff ℝ 1 Ψ) (hnonneg : ∀ y > 0, 0 ≤ Ψ y)
    (hsupport : Function.support Ψ ⊆ Icc (1 / 2) 2)
    (hmass : ∫ y in Ioi 0, Ψ y / y = 1) :
    Integrable (fun u : ℝ => (Smooth1 Ψ ε u : ℂ))
      (volume.restrict (Ioi 0)) := by
  have hconv : MellinConvergent
      (fun y => (Smooth1 Ψ ε y : ℂ)) 1 :=
    Smooth1MellinConvergent hdiff hsupport hε hnonneg hmass
      (by norm_num)
  change IntegrableOn (fun u : ℝ => (Smooth1 Ψ ε u : ℂ)) (Ioi 0)
  simpa [MellinConvergent] using hconv

theorem scaled_cutoff_integrable_positive (Ψ : ℝ → ℝ) (ε d x : ℝ)
    (hd : 0 < d) (hx : 0 < x)
    (hε : ε ∈ Ioo 0 1)
    (hdiff : ContDiff ℝ 1 Ψ) (hnonneg : ∀ y > 0, 0 ≤ Ψ y)
    (hsupport : Function.support Ψ ⊆ Icc (1 / 2) 2)
    (hmass : ∫ y in Ioi 0, Ψ y / y = 1) :
    Integrable (fun u : ℝ => (Smooth1 Ψ ε (d * u / x) : ℂ))
      (volume.restrict (Ioi 0)) := by
  have hr : 0 < d / x := div_pos hd hx
  have hbase : IntegrableOn (fun u : ℝ => (Smooth1 Ψ ε u : ℂ))
      (Ioi 0) := cutoff_integrable_positive Ψ ε hε hdiff hnonneg
        hsupport hmass
  have hh := (integrableOn_Ioi_comp_mul_left_iff
    (fun u : ℝ => (Smooth1 Ψ ε u : ℂ)) 0 hr).mpr
      (by simpa using hbase)
  change IntegrableOn (fun u : ℝ => (Smooth1 Ψ ε (d * u / x) : ℂ))
    (Ioi 0)
  convert hh using 1
  ext u
  congr 1
  ring

theorem short_window_support (Ψ : ℝ → ℝ) (ε d x left a b : ℝ)
    (hd : 0 < d) (hx : 0 < x) (hleft : 0 < left)
    (ha : 0 < a) (_hab : a ≤ b) (hε : ε ∈ Ioo 0 1)
    (hsupport : Function.support Ψ ⊆ Icc (1 / 2) 2)
    (hmass : ∫ y in Ioi 0, Ψ y / y = 1)
    (hloX : d * a / x ≤ 1 - Real.log 2 * ε)
    (hloLeft : d * a / left ≤ 1 - Real.log 2 * ε)
    (hhiX : 1 + 2 * Real.log 2 * ε ≤ d * b / x)
    (hhiLeft : 1 + 2 * Real.log 2 * ε ≤ d * b / left) :
    (∫ u in Icc a b,
      ((Smooth1 Ψ ε (d * u / x) : ℝ) : ℂ) -
        ((Smooth1 Ψ ε (d * u / left) : ℝ) : ℂ)) =
    ∫ u in Ioi (0 : ℝ),
      ((Smooth1 Ψ ε (d * u / x) : ℝ) : ℂ) -
        ((Smooth1 Ψ ε (d * u / left) : ℝ) : ℂ) := by
  let g : ℝ → ℂ := fun u =>
    ((Smooth1 Ψ ε (d * u / x) : ℝ) : ℂ) -
      ((Smooth1 Ψ ε (d * u / left) : ℝ) : ℂ)
  have hzero (u : ℝ) (hpos : 0 < u) (hout : u ∉ Icc a b) : g u = 0 := by
    by_cases hlow : u < a
    · have hrx : 0 < d * u / x := by positivity
      have hrl : 0 < d * u / left := by positivity
      have hux : d * u / x ≤ 1 - Real.log 2 * ε := by
        apply le_trans (b := d * a / x) ?_ hloX
        apply (div_le_div_iff₀ hx hx).mpr
        nlinarith [mul_le_mul_of_nonneg_left hlow.le hd.le]
      have hul : d * u / left ≤ 1 - Real.log 2 * ε := by
        apply le_trans (b := d * a / left) ?_ hloLeft
        apply (div_le_div_iff₀ hleft hleft).mpr
        nlinarith [mul_le_mul_of_nonneg_left hlow.le hd.le]
      obtain ⟨c, _, hc, hbelow⟩ := Smooth1Properties_below hsupport hmass
      have hbx : Smooth1 Ψ ε (d * u / x) = 1 :=
        hbelow ε (d * u / x) hε.1 hrx (by simpa [hc] using hux)
      have hbl : Smooth1 Ψ ε (d * u / left) = 1 :=
        hbelow ε (d * u / left) hε.1 hrl (by simpa [hc] using hul)
      simp [g, hbx, hbl]
    · have hhigh : b < u := by
        simp only [mem_Icc, not_and_or, not_le] at hout
        rcases hout with h | h
        · exact False.elim (hlow h)
        · exact h
      have hux : 1 + 2 * Real.log 2 * ε ≤ d * u / x := by
        apply le_trans hhiX
        apply (div_le_div_iff₀ hx hx).mpr
        nlinarith [mul_le_mul_of_nonneg_left hhigh.le hd.le]
      have hul : 1 + 2 * Real.log 2 * ε ≤ d * u / left := by
        apply le_trans hhiLeft
        apply (div_le_div_iff₀ hleft hleft).mpr
        nlinarith [mul_le_mul_of_nonneg_left hhigh.le hd.le]
      obtain ⟨c, _, hc, habove⟩ := Smooth1Properties_above hsupport
      have hax : Smooth1 Ψ ε (d * u / x) = 0 :=
        habove ε (d * u / x) hε (by simpa [hc] using hux)
      have hal : Smooth1 Ψ ε (d * u / left) = 0 :=
        habove ε (d * u / left) hε (by simpa [hc] using hul)
      simp [g, hax, hal]
  change (∫ u in Icc a b, g u) = ∫ u in Ioi (0 : ℝ), g u
  rw [← integral_indicator measurableSet_Icc,
    ← integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  filter_upwards with u
  by_cases hin : u ∈ Icc a b
  · have hpos : u ∈ Ioi (0 : ℝ) := lt_of_lt_of_le ha hin.1
    simp [Set.indicator_of_mem hin, Set.indicator_of_mem hpos]
  · by_cases hpos : 0 < u
    · have hz := hzero u hpos hin
      simp [Set.indicator, hin,
        (show u ∈ Ioi (0 : ℝ) from hpos), hz]
    · have hnot : u ∉ Ioi (0 : ℝ) := hpos
      simp [Set.indicator, hin, hnot]

theorem continuous_short_window_main_term (Ψ : ℝ → ℝ)
    (ε d x left a b : ℝ)
    (hd : 0 < d) (hx : 0 < x) (hleft : 0 < left)
    (ha : 0 < a) (hab : a ≤ b) (hε : ε ∈ Ioo 0 1)
    (hdiff : ContDiff ℝ 1 Ψ) (hnonneg : ∀ y > 0, 0 ≤ Ψ y)
    (hsupport : Function.support Ψ ⊆ Icc (1 / 2) 2)
    (hmass : ∫ y in Ioi 0, Ψ y / y = 1)
    (hloX : d * a / x ≤ 1 - Real.log 2 * ε)
    (hloLeft : d * a / left ≤ 1 - Real.log 2 * ε)
    (hhiX : 1 + 2 * Real.log 2 * ε ≤ d * b / x)
    (hhiLeft : 1 + 2 * Real.log 2 * ε ≤ d * b / left) :
    (∫ u in Icc a b,
      ((Smooth1 Ψ ε (d * u / x) : ℝ) : ℂ) -
        ((Smooth1 Ψ ε (d * u / left) : ℝ) : ℂ)) =
      (((x - left) / d : ℝ) : ℂ) *
        mellin (fun y => (Smooth1 Ψ ε y : ℂ)) 1 := by
  rw [short_window_support Ψ ε d x left a b hd hx hleft ha hab hε
    hsupport hmass hloX hloLeft hhiX hhiLeft]
  rw [integral_sub
    (scaled_cutoff_integrable_positive Ψ ε d x hd hx hε hdiff
      hnonneg hsupport hmass)
    (scaled_cutoff_integrable_positive Ψ ε d left hd hleft hε hdiff
      hnonneg hsupport hmass)]
  rw [scaled_cutoff_integral Ψ ε d x hd hx,
    scaled_cutoff_integral Ψ ε d left hd hleft]
  rw [← sub_mul, ← Complex.ofReal_sub]
  congr 1
  rw [sub_div]

theorem finite_continuous_main_term (s : Finset ℕ) (coeff : ℕ → ℂ)
    (Ψ : ℝ → ℝ) (ε x left a b : ℝ)
    (hx : 0 < x) (hleft : 0 < left) (ha : 0 < a) (hab : a ≤ b)
    (hs : ∀ d ∈ s, 0 < d)
    (hε : ε ∈ Ioo 0 1)
    (hdiff : ContDiff ℝ 1 Ψ) (hnonneg : ∀ y > 0, 0 ≤ Ψ y)
    (hsupport : Function.support Ψ ⊆ Icc (1 / 2) 2)
    (hmass : ∫ y in Ioi 0, Ψ y / y = 1)
    (hloX : ∀ d ∈ s, (d : ℝ) * a / x ≤ 1 - Real.log 2 * ε)
    (hloLeft : ∀ d ∈ s, (d : ℝ) * a / left ≤ 1 - Real.log 2 * ε)
    (hhiX : ∀ d ∈ s, 1 + 2 * Real.log 2 * ε ≤ (d : ℝ) * b / x)
    (hhiLeft : ∀ d ∈ s, 1 + 2 * Real.log 2 * ε ≤ (d : ℝ) * b / left) :
    (∑ d ∈ s, coeff d *
      (∫ u in Icc a b,
        ((Smooth1 Ψ ε ((d : ℝ) * u / x) : ℝ) : ℂ) -
          ((Smooth1 Ψ ε ((d : ℝ) * u / left) : ℝ) : ℂ))) =
      ((x - left : ℝ) : ℂ) *
        mellin (fun y => (Smooth1 Ψ ε y : ℂ)) 1 *
        (∑ d ∈ s, coeff d / (d : ℂ)) := by
  classical
  have hterm (d : ℕ) (hd : d ∈ s) :
      (∫ u in Icc a b,
        ((Smooth1 Ψ ε ((d : ℝ) * u / x) : ℝ) : ℂ) -
          ((Smooth1 Ψ ε ((d : ℝ) * u / left) : ℝ) : ℂ)) =
        (((x - left) / d : ℝ) : ℂ) *
          mellin (fun y => (Smooth1 Ψ ε y : ℂ)) 1 := by
    have hdpos : (0 : ℝ) < d := by exact_mod_cast hs d hd
    exact continuous_short_window_main_term Ψ ε (d : ℝ) x left a b
      hdpos hx hleft ha hab hε hdiff hnonneg hsupport hmass
      (hloX d hd) (hloLeft d hd) (hhiX d hd) (hhiLeft d hd)
  calc
    _ = ∑ d ∈ s, coeff d * (((x - left) / d : ℝ) : ℂ) *
        mellin (fun y => (Smooth1 Ψ ε y : ℂ)) 1 := by
          apply Finset.sum_congr rfl
          intro d hd
          rw [hterm d hd]
          ring
    _ = _ := by
      simp only [Complex.ofReal_div, Complex.ofReal_sub]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      push_cast
      simp only [div_eq_mul_inv]
      ring

end ContinuousCofactorMellin

run_cmd do
  for target in [``ContinuousCofactorMellin.cofactor_quotient,
      ``ContinuousCofactorMellin.ratio_power,
      ``ContinuousCofactorMellin.single_point,
      ``ContinuousCofactorMellin.joint_integrable,
      ``ContinuousCofactorMellin.single_integrated,
      ``ContinuousCofactorMellin.contour_integrable,
      ``ContinuousCofactorMellin.finite_integrated,
      ``ContinuousCofactorMellin.finite_contour_integrable,
      ``ContinuousCofactorMellin.finite_short_window,
      ``ContinuousCofactorMellin.cutoff_integrable,
      ``ContinuousCofactorMellin.finite_short_window_integrand,
      ``ContinuousCofactorMellin.mellin_one_eq_integral,
      ``ContinuousCofactorMellin.scaled_cutoff_integral,
      ``ContinuousCofactorMellin.cutoff_integrable_positive,
      ``ContinuousCofactorMellin.scaled_cutoff_integrable_positive,
      ``ContinuousCofactorMellin.short_window_support,
      ``ContinuousCofactorMellin.continuous_short_window_main_term,
      ``ContinuousCofactorMellin.finite_continuous_main_term] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "CONTINUOUS COFACTOR MELLIN PASSED"
