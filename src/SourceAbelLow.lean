import SourceCenteredMiddle
import PositiveInteriorMass
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
v8. Exact sigma-one Abel transfer from a LOCAL relative psi-error to the
literal centered source on low frequencies. UNCOMPILED DRAFT.
The psi-error is a visible arithmetic premise. This file does not assert that
the inherited exp(-c log(x)^(1/10)) PNT controls the larger v4 low-frequency
cutoff, nor does it postulate a stronger PNT as an axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 18000000
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace SourceAbelLow
open SourceLiteralMoments SourceLiteralMass SourceReferenceSigmaOne SourceCenteredMiddle
open SourceLiteralMiddle PositiveInteriorModel PositiveInteriorCells
open MellinWindowFactor ContinuousCofactorMellin
open Erdos374.PositiveInteriorMass Erdos374.WeightedPrimeSampling151

def test (t u : ℝ) : ℂ := (u:ℂ)^(-line 1 t)

def testDeriv (t u : ℝ) : ℂ := (-line 1 t)*(u:ℂ)^(-line 1 t-1)

 theorem exponent_ne_zero (t : ℝ) : -(line 1 t)≠0 ∧ -(line 1 t)-1≠0 := by
  constructor
  · intro he
    have hr := congrArg Complex.re he
    norm_num [line] at hr
  · intro he
    have hr := congrArg Complex.re he
    norm_num [line] at hr

 theorem test_derivative (t u : ℝ) (hu : 0<u) :
    HasDerivAt (test t) (testDeriv t u) u := by
  exact hasDerivAt_ofReal_cpow_const hu.ne' (exponent_ne_zero t).1

 theorem testDeriv_continuousOn (a b t : ℝ) (ha : 0<a) :
    ContinuousOn (testDeriv t) (Icc a b) := by
  intro u hu
  have hup : 0<u := ha.trans_le hu.1
  have hc : ContinuousAt (fun z : ℝ => (z:ℂ)^(-line 1 t-1)) u :=
    ((differentiableAt_id : DifferentiableAt ℝ (fun z : ℝ => z) u).ofReal_cpow_const
      hup.ne' (exponent_ne_zero t).2).continuousAt
  exact (continuousAt_const.mul hc).continuousWithinAt

 theorem test_norm (t u : ℝ) (hu : 0<u) : ‖test t u‖=1/u := by
  unfold test
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hu]
  norm_num [line,Real.rpow_neg_one,one_div]

 theorem testDeriv_norm (t u : ℝ) (hu : 0<u) :
    ‖testDeriv t u‖=‖line 1 t‖/u^2 := by
  unfold testDeriv
  rw [norm_mul,norm_neg,Complex.norm_cpow_eq_rpow_re_of_pos hu]
  norm_num [line,Real.rpow_neg_natCast,div_eq_mul_inv]

 theorem line_norm_le (t : ℝ) : ‖line 1 t‖≤1+|t| := by
  have hh := norm_add_le (1:ℂ) (Complex.I*(t:ℂ))
  simpa only [line,Complex.ofReal_one,norm_one,norm_mul,Complex.norm_I,
    one_mul,Complex.norm_real,Real.norm_eq_abs] using hh

/-- Relative errors are kept inside the Abel integral; there is no extra
factor equal to the reciprocal of the shortest interval scale. -/
 theorem relative_abel (a b t ε : ℝ) (ha : 0<a) (hab : a≤b) (hε : 0≤ε)
    (hpsi : ∀ u∈Icc a b, |Chebyshev.psi u-u|≤ε*u) :
    ‖(∑ n∈Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, test t n*mangoldtComplex n)-
      (∫ u in a..b, test t u)‖ ≤ ε*(2+‖line 1 t‖*Real.log (b/a)) := by
  have hd : ∀ u∈Icc a b, HasDerivAt (test t) (testDeriv t u) u :=
    fun u hu => test_derivative t u (ha.trans_le hu.1)
  have hc := testDeriv_continuousOn a b t ha
  have hti : IntervalIntegrable (fun u => testDeriv t u*(u:ℂ)) volume a b :=
    (hc.mul Complex.continuous_ofReal.continuousOn).intervalIntegrable_of_Icc hab
  have he : (∑ n∈Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, test t n*mangoldtComplex n)-
      (∫ u in a..b, test t u) =
      test t b*((Chebyshev.psi b-b:ℝ):ℂ)-
      test t a*((Chebyshev.psi a-a:ℝ):ℂ)-
      ∫ u in a..b, testDeriv t u*((Chebyshev.psi u-u:ℝ):ℂ) := by
    rw [weighted_psi_abel ha.le hab hd hc,weighted_identity_integral hab hd hc]
    simp only [Complex.ofReal_sub,mul_sub]
    rw [intervalIntegral.integral_sub (weighted_psi_kernel_integrable ha.le hab hc) hti]
    ring
  have hend (u : ℝ) (hu : u∈Icc a b) :
      ‖test t u*((Chebyshev.psi u-u:ℝ):ℂ)‖≤ε := by
    have hup : 0<u := ha.trans_le hu.1
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,test_norm t u hup]
    have hh := mul_le_mul_of_nonneg_left (hpsi u hu) (by positivity : 0≤1/u)
    convert hh using 1 <;> field_simp
  have hmajor : IntervalIntegrable (fun u : ℝ => ε*‖line 1 t‖/u) volume a b := by
    have hcm : ContinuousOn (fun u : ℝ => ε*‖line 1 t‖/u) (Icc a b) :=
      continuousOn_const.div continuousOn_id (fun u hu => (ha.trans_le hu.1).ne')
    exact hcm.intervalIntegrable_of_Icc hab
  have hnorm : ‖∫ u in a..b, testDeriv t u*((Chebyshev.psi u-u:ℝ):ℂ)‖≤
      ε*‖line 1 t‖*Real.log (b/a) := by
    have hh : ‖∫ u in a..b, testDeriv t u*((Chebyshev.psi u-u:ℝ):ℂ)‖≤
        ∫ u in a..b, ε*‖line 1 t‖/u := by
      apply intervalIntegral.norm_integral_le_of_norm_le hab
      · apply Filter.Eventually.of_forall
        intro u hu
        have hup : 0<u := ha.trans_le hu.1.le
        rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,testDeriv_norm t u hup]
        have hm := mul_le_mul_of_nonneg_left (hpsi u ⟨hu.1.le,hu.2⟩)
          (by positivity : 0≤‖line 1 t‖/u^2)
        convert hm using 1 <;> field_simp <;> ring
      · exact hmajor
    have hi : (∫ u in a..b, ε*‖line 1 t‖/u)=ε*‖line 1 t‖*Real.log (b/a) := by
      have heq : (fun u : ℝ => ε*‖line 1 t‖/u)=fun u => (ε*‖line 1 t‖)*u⁻¹ := by
        funext u
        exact div_eq_mul_inv _ _
      rw [heq,intervalIntegral.integral_const_mul,integral_inv_of_pos ha (ha.trans_le hab)]
    exact hh.trans_eq hi
  rw [he]
  have ht := (norm_sub_le
    (test t b*((Chebyshev.psi b-b:ℝ):ℂ)-test t a*((Chebyshev.psi a-a:ℝ):ℂ))
    (∫ u in a..b, testDeriv t u*((Chebyshev.psi u-u:ℝ):ℂ))).trans
      (add_le_add (norm_sub_le _ _) le_rfl)
  have hb := hend b ⟨hab,le_rfl⟩
  have ha' := hend a ⟨le_rfl,hab⟩
  nlinarith

 def LocalPsiError (X : ℝ) (j : ℕ×ℕ) (ε : ℝ) : Prop :=
  ∀ u∈Icc (thirdScale X j/8) (4*thirdScale X j), |Chebyshev.psi u-u|≤ε*u

/-- Exact first-moment centering on the third source interval. The first two
factor reciprocal masses are not approximated. -/
 theorem third_error (X t ε : ℝ) (j : ℕ×ℕ) (hX : 0<X) (hε : 0≤ε)
    (hpsi : LocalPsiError X j ε) :
    ‖factor X j 2 t-thirdReference X j t‖≤7*ε*(1+|t|) := by
  have hL : 0<thirdScale X j := ideal_positive X j hX 2
  have hh := relative_abel (thirdScale X j/8) (4*thirdScale X j) t ε
    (by positivity) (by linarith) hε hpsi
  have hsum : (∑ n∈Finset.Ioc ⌊thirdScale X j/8⌋₊ ⌊4*thirdScale X j⌋₊,
      test t n*mangoldtComplex n)=factor X j 2 t := by
    unfold SourceLiteralMoments.factor Erdos374.HarmanGram152.verticalDirichlet152
    change (∑ n∈Finset.Ioc ⌊thirdScale X j/8⌋₊ ⌊4*thirdScale X j⌋₊,
      test t n*mangoldtComplex n)=_
    apply Finset.sum_congr rfl
    intro n _
    unfold test mangoldtComplex SourceMassDischarge.mangoldt line
    push_cast
    ring
  have hint : (∫ u in (thirdScale X j/8)..(4*thirdScale X j), test t u)=
      thirdReference X j t := by
    rw [intervalIntegral.integral_of_le (by linarith : thirdScale X j/8≤4*thirdScale X j),
      ←integral_Icc_eq_integral_Ioc]
    rfl
  rw [hsum,hint] at hh
  have hratio : 4*thirdScale X j/(thirdScale X j/8)=(32:ℝ) := by field_simp <;> ring
  rw [hratio] at hh
  have hlog0 : 0≤Real.log 32 := Real.log_nonneg (by norm_num)
  have hlog5 : Real.log 32≤5 := by
    have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    rw [show (32:ℝ)=2^5 by norm_num,Real.log_pow]
    norm_num at *
    linarith
  have hnorm := line_norm_le t
  have hm := mul_le_mul hnorm hlog5 hlog0 (by positivity : 0≤1+|t|)
  have hb : 2+‖line 1 t‖*Real.log 32≤7*(1+|t|) := by
    nlinarith [abs_nonneg t]
  exact hh.trans (by nlinarith [mul_le_mul_of_nonneg_left hb hε])

 theorem centered_pointwise (X t ε : ℝ) (j : ℕ×ℕ) (hX : 2≤X)
    (hlog : 1000000≤Real.log X) (hj : j∈boxes (mesh X)) (hε : 0≤ε)
    (hpsi : LocalPsiError X j ε) :
    ‖centeredProduct X j t‖≤1575*ε*(1+|t|) := by
  have hP := factor_norm_le_fifteen X j 0 t hX hlog hj
  have hR := factor_norm_le_fifteen X j 1 t hX hlog hj
  have hQ := third_error X t ε j (by linarith) hε hpsi
  have he : centeredProduct X j t=
      factor X j 0 t*factor X j 1 t*(factor X j 2 t-thirdReference X j t) := by
    unfold centeredProduct sourceProduct referenceProduct
    ring
  rw [he,norm_mul,norm_mul]
  have hPR := mul_le_mul hP hR (norm_nonneg _) (by norm_num)
  have hh := mul_le_mul hPR hQ (norm_nonneg _) (by norm_num)
  convert hh using 1 <;> ring

/-- Finite low-frequency energy from the displayed local PNT error, not from
an assumed centered source energy or an unproved small physical remainder. -/
 theorem low_energy (X T ε : ℝ) (j : ℕ×ℕ) (hX : 2≤X)
    (hlog : 1000000≤Real.log X) (hj : j∈boxes (mesh X)) (hT : 1≤T)
    (hε : 0≤ε) (hpsi : LocalPsiError X j ε) :
    (∫ t in Icc (-T) T, ‖centeredProduct X j t‖^2)≤19845000*ε^2*T^3 := by
  have hc := (centered_continuous X j (by linarith)).norm.pow 2
  have hi : IntegrableOn (fun _ : ℝ => (1575*ε*(1+T))^2) (Icc (-T) T) :=
    continuous_const.integrableOn_Icc
  have hm := setIntegral_mono_on hc.integrableOn_Icc hi measurableSet_Icc (by
    intro t ht
    have ht' : |t|≤T := abs_le.mpr ht
    have hb := (centered_pointwise X t ε j hX hlog hj hε hpsi).trans
      (mul_le_mul_of_nonneg_left (by linarith : 1+|t|≤1+T) (by positivity))
    exact pow_le_pow_left₀ (norm_nonneg _) hb 2)
  rw [setIntegral_const,Real.volume_real_Icc_of_le (by linarith : -T≤T),smul_eq_mul] at hm
  change (∫ t in Icc (-T) T, ‖centeredProduct X j t‖^2) ≤
    (T - -T)*(1575*ε*(1+T))^2 at hm
  have hsq : (1+T)^2≤4*T^2 := by nlinarith
  have hh := mul_le_mul_of_nonneg_left hsq (show 0≤2*T*1575^2*ε^2 by positivity)
  nlinarith

/-- The explicit local error needed for the final log budget. -/
 theorem low_energy_at_local_budget (X T : ℝ) (j : ℕ×ℕ) (hX : 2≤X)
    (hlog : 1000000≤Real.log X) (hj : j∈boxes (mesh X)) (hT : 1≤T)
    (hpsi : LocalPsiError X j (1/((1+Real.log X)^20*T^2))) :
    (∫ t in Icc (-T) T, ‖centeredProduct X j t‖^2)≤
      19845000/((1+Real.log X)^40*T) := by
  have hLp : 0<1+Real.log X := by linarith
  have hTp : 0<T := by linarith
  have hh := low_energy X T (1/((1+Real.log X)^20*T^2)) j hX hlog hj hT
    (by positivity) hpsi
  convert hh using 1 <;> field_simp <;> ring

#print axioms low_energy_at_local_budget
run_cmd do
  for n in [``exponent_ne_zero,``test_derivative,``testDeriv_continuousOn,
      ``test_norm,``testDeriv_norm,``line_norm_le,``relative_abel,``third_error,
      ``centered_pointwise,``low_energy,``low_energy_at_local_budget] do
    for ax in (← Lean.collectAxioms n) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {n}"
  Lean.logInfo "V8 LOCAL PSI TO LOW ENERGY: PSI INPUT STILL EXPLICIT; COMPILATION REQUIRED"
end SourceAbelLow
