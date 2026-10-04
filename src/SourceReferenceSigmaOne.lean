import ContinuousCofactorMellin
import CompactIntegral
import SourceLiteralMass

/-! v7. The literal continuous reference at Re(s)=1.
The inherited quotient lemma assumed sigma>1. This file
proves the sigma=1, t!=0 case directly instead of using that lemma out of range.
Continuity at t=0 is supplied by the integral definition, not by a zero denominator. -/
set_option autoImplicit false
set_option maxHeartbeats 12000000
noncomputable section
open MeasureTheory Set
namespace SourceReferenceSigmaOne
open ContinuousCofactorMellin MellinWindowFactor
open SourceLiteralMoments SourceLiteralMass PositiveInteriorModel PositiveInteriorCells

/-- Endpoint formula on the critical integration line; only t=0 is excluded. -/
theorem quotient (a b t : ℝ) (ha : 0<a) (hab : a≤b) (ht : t≠0) :
    cofactor a b (line 1 t) =
      ((b:ℂ)^(1-line 1 t)-(a:ℂ)^(1-line 1 t))/(1-line 1 t) := by
  have hnot : -(line 1 t) ≠ -1 := by
    intro he
    have hi := congrArg Complex.im he
    simp [line] at hi
    exact ht (by linarith)
  have hzero : (0:ℝ) ∉ Set.uIcc a b := by
    rw [Set.uIcc_of_le hab]
    exact fun h => (not_le_of_gt ha) h.1
  unfold cofactor
  rw [integral_Icc_eq_integral_Ioc, ←intervalIntegral.integral_of_le hab,
    integral_cpow (Or.inr ⟨hnot,hzero⟩)]
  congr 1
  · congr 1 <;> ring
  · ring

theorem oscillating_endpoint_norm (a t : ℝ) (ha : 0<a) :
    ‖(a:ℂ)^(1-line 1 t)‖ = 1 := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos ha]
  simp [line]

theorem norm_le (a b t : ℝ) (ha : 0<a) (hab : a≤b) (ht : t≠0) :
    ‖cofactor a b (line 1 t)‖ ≤ 2/|t| := by
  rw [quotient a b t ha hab ht, norm_div]
  have hden : (1:ℂ)-line 1 t = -(Complex.I*(t:ℂ)) := by simp [line]
  have hd : ‖(1:ℂ)-line 1 t‖ = |t| := by
    rw [hden, norm_neg, norm_mul, Complex.norm_I, one_mul,
      Complex.norm_real, Real.norm_eq_abs]
  rw [hd]
  apply div_le_div_of_nonneg_right _ (abs_nonneg t)
  have hh := norm_sub_le ((b:ℂ)^(1-line 1 t)) ((a:ℂ)^(1-line 1 t))
  rw [oscillating_endpoint_norm b t (ha.trans_le hab),
    oscillating_endpoint_norm a t ha] at hh
  norm_num at hh ⊢
  exact hh

/-- Clamp the real base away from zero to get a globally continuous integrand. -/
theorem continuous_cofactor (a b : ℝ) (ha : 0<a) :
    Continuous (fun t : ℝ => cofactor a b (line 1 t)) := by
  let f : ℝ → ℝ → ℂ := fun t u =>
    Complex.exp (-(line 1 t)*(Real.log (max a u):ℂ))
  have hl : Continuous (fun u : ℝ => Real.log (max a u)) :=
    (continuous_const.max continuous_id).log (fun u =>
      (lt_of_lt_of_le ha (le_max_left a u)).ne')
  have hf : Continuous f.uncurry := by
    have hlog : Continuous (fun p : ℝ × ℝ => (Real.log (max a p.2):ℂ)) :=
      Complex.continuous_ofReal.comp (hl.comp continuous_snd)
    have hline : Continuous (fun p : ℝ × ℝ => -(line 1 p.1)) := by
      unfold line
      fun_prop
    exact (hline.mul hlog).cexp
  have hc := CompactIntegral.continuous_integral a b f hf
  have he : (fun t : ℝ => cofactor a b (line 1 t)) =
      (fun t => ∫ u in Icc a b, f t u) := by
    funext t
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    have hup : 0<u := ha.trans_le hu.1
    dsimp [f]
    rw [max_eq_right hu.1, Complex.cpow_def_of_ne_zero (by exact_mod_cast hup.ne'),
      ←Complex.ofReal_log hup.le]
    congr 1
    ring
  rw [he]
  exact hc

def thirdReference (X : ℝ) (j : ℕ × ℕ) (t : ℝ) : ℂ :=
  cofactor (thirdScale X j/8) (4*thirdScale X j) (line 1 t)

def referenceProduct (X : ℝ) (j : ℕ × ℕ) (t : ℝ) : ℂ :=
  factor X j 0 t*factor X j 1 t*thirdReference X j t

theorem reference_continuous (X : ℝ) (j : ℕ × ℕ) (hX : 0<X) :
    Continuous (referenceProduct X j) := by
  have hL : 0<thirdScale X j := ideal_positive X j hX 2
  exact ((factor_continuous X j 0).mul (factor_continuous X j 1)).mul
    (continuous_cofactor _ _ (by positivity))

theorem reference_norm (X t : ℝ) (j : ℕ × ℕ)
    (hX : 2≤X) (hlog : 1000000≤Real.log X) (hj : j∈boxes (mesh X)) (ht : t≠0) :
    ‖referenceProduct X j t‖ ≤ 450/|t| := by
  have hXp : 0<X := by linarith
  have hL : 0<thirdScale X j := ideal_positive X j hXp 2
  have ha := factor_norm_le_fifteen X j 0 t hX hlog hj
  have hb := factor_norm_le_fifteen X j 1 t hX hlog hj
  have hc := norm_le (thirdScale X j/8) (4*thirdScale X j) t
    (by positivity) (by linarith) ht
  have hab := mul_le_mul ha hb (norm_nonneg _) (by norm_num)
  have hh := mul_le_mul hab hc (norm_nonneg _) (by norm_num)
  calc
    _ = ‖factor X j 0 t‖*‖factor X j 1 t‖*‖thirdReference X j t‖ := by
      simp only [referenceProduct, norm_mul]
    _ ≤ 15*15*(2/|t|) := hh
    _ = 450/|t| := by ring

#print axioms quotient
#print axioms reference_norm
run_cmd do
  for n in [``quotient, ``oscillating_endpoint_norm, ``norm_le,
      ``continuous_cofactor, ``reference_continuous, ``reference_norm] do
    for ax in (← Lean.collectAxioms n) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {n}"
  Lean.logInfo "V7 SIGMA-ONE REFERENCE: VALID ONLY AFTER COMPILATION"
end SourceReferenceSigmaOne
