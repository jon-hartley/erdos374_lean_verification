import Mathlib.Analysis.MeanInequalities
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic

/-! v6: extract the entire moment surplus from the FIRST factor.
UNCOMPILED DRAFT. Only nonnegative moment algebra and integration are proved
here. No pointwise prime-polynomial estimate is declared or assumed as an axiom.
The integrated lemma exposes its pointwise-smallness hypothesis explicitly. -/
set_option autoImplicit false
set_option maxHeartbeats 12000000
noncomputable section
open MeasureTheory Set
namespace SourceFirstFactorSaving

def firstWeight (_A B C : ℝ) : ℝ := 1-2/B-2/C

def extracted (A B C : ℝ) : ℝ := 2-A*firstWeight A B C

theorem weight_data (A B C : ℝ) (hA : 4 ≤ A) (hB : 4 ≤ B) (hC : 4 ≤ C)
    (hS : (2001/2000:ℝ) ≤ 2/A+2/B+2/C) :
    0 ≤ firstWeight A B C ∧ firstWeight A B C ≤ 1 ∧
      0 ≤ 2/B ∧ 2/B ≤ 1 ∧ 0 ≤ 2/C ∧ 2/C ≤ 1 ∧
      firstWeight A B C+2/B+2/C=1 ∧
      (1/500:ℝ) ≤ extracted A B C ∧ extracted A B C ≤ 2 := by
  have hAp : 0 < A := by linarith
  have hBp : 0 < B := by linarith
  have hCp : 0 < C := by linarith
  have hb0 : 0 ≤ 2/B := by positivity
  have hc0 : 0 ≤ 2/C := by positivity
  have hb1 : 2/B ≤ (1/2:ℝ) := (div_le_iff₀ hBp).mpr (by linarith)
  have hc1 : 2/C ≤ (1/2:ℝ) := (div_le_iff₀ hCp).mpr (by linarith)
  have hw0 : 0 ≤ firstWeight A B C := by unfold firstWeight; linarith
  have hw1 : firstWeight A B C ≤ 1 := by unfold firstWeight; linarith
  have he : extracted A B C = A*(2/A+2/B+2/C-1) := by
    unfold extracted firstWeight
    field_simp
    <;> ring
  have hm := mul_le_mul_of_nonneg_left hS hAp.le
  have htwo : A*(2/A) = 2 := by field_simp
  have halow : (1/500:ℝ) ≤ extracted A B C := by
    rw [he]
    nlinarith [htwo]
  refine ⟨hw0,hw1,hb0,by linarith,hc0,by linarith,?_,halow,?_⟩
  · unfold firstWeight; ring
  · unfold extracted
    nlinarith [mul_nonneg hAp.le hw0]

/-- All amplitude sizes are allowed. In particular b and c need no cap. -/
theorem scalar (a b c A B C : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hA : 4 ≤ A) (hB : 4 ≤ B) (hC : 4 ≤ C)
    (hS : (2001/2000:ℝ) ≤ 2/A+2/B+2/C) :
    (a*b*c)^2 ≤ a^(extracted A B C)*(a^A+b^B+c^C) := by
  have hg := weight_data A B C hA hB hC hS
  by_cases haz : a=0
  · subst a
    simp only [zero_mul,zero_pow (by decide : (2:ℕ) ≠ 0)]
    positivity
  have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm haz)
  have hAp : 0 ≤ a^A := Real.rpow_nonneg ha _
  have hBp : 0 ≤ b^B := Real.rpow_nonneg hb _
  have hCp : 0 ≤ c^C := Real.rpow_nonneg hc _
  have he1 : 0 ≤ firstWeight A B C := hg.1
  have he2 : 0 ≤ 2/B := hg.2.2.1
  have he3 : 0 ≤ 2/C := hg.2.2.2.2.1
  have hesum : firstWeight A B C+2/B+2/C=1 := hg.2.2.2.2.2.2.1
  have hgm := Real.geom_mean_le_arith_mean3_weighted he1 he2 he3 hAp hBp hCp hesum
  have hBne : B ≠ 0 := by linarith
  have hCne : C ≠ 0 := by linarith
  have hpowB : (b^B)^(2/B) = b^2 := by
    rw [←Real.rpow_mul hb]
    have hid : B*(2/B)=(2:ℝ) := by field_simp
    rw [hid,Real.rpow_two]
  have hpowC : (c^C)^(2/C) = c^2 := by
    rw [←Real.rpow_mul hc]
    have hid : C*(2/C)=(2:ℝ) := by field_simp
    rw [hid,Real.rpow_two]
  have hpowA : (a^A)^(firstWeight A B C) = a^(A*firstWeight A B C) :=
    (Real.rpow_mul ha _ _).symm
  rw [hpowA,hpowB,hpowC] at hgm
  have hweighted : firstWeight A B C*a^A+(2/B)*b^B+(2/C)*c^C ≤ a^A+b^B+c^C := by
    have hu := mul_le_mul_of_nonneg_right hg.2.1 hAp
    have hv := mul_le_mul_of_nonneg_right hg.2.2.2.1 hBp
    have hw := mul_le_mul_of_nonneg_right hg.2.2.2.2.2.1 hCp
    nlinarith
  have hs := mul_le_mul_of_nonneg_left (hgm.trans hweighted)
    (Real.rpow_nonneg ha (extracted A B C))
  have hid : a^(extracted A B C)*(a^(A*firstWeight A B C)*b^2*c^2)=(a*b*c)^2 := by
    rw [show a^(extracted A B C)*(a^(A*firstWeight A B C)*b^2*c^2) =
      (a^(extracted A B C)*a^(A*firstWeight A B C))*b^2*c^2 by ring,
      ←Real.rpow_add hap]
    have hsum : extracted A B C+A*firstWeight A B C=(2:ℝ) := by unfold extracted; ring
    rw [hsum,Real.rpow_two]
    ring
  simpa only [hid] using hs

/-- A single small factor pays all excess reciprocal moment. -/
theorem scalar_of_cap (a b c A B C ε : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hA : 4 ≤ A) (hB : 4 ≤ B) (hC : 4 ≤ C)
    (hS : (2001/2000:ℝ) ≤ 2/A+2/B+2/C)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hsmall : a ≤ ε) :
    (a*b*c)^2 ≤ ε^(1/500:ℝ)*(a^A+b^B+c^C) := by
  have hg := weight_data A B C hA hB hC hS
  have hα : (1/500:ℝ) ≤ extracted A B C := hg.2.2.2.2.2.2.2.1
  have hbound : a^(extracted A B C) ≤ ε^(1/500:ℝ) := by
    calc
      _ ≤ ε^(extracted A B C) := Real.rpow_le_rpow ha hsmall (by linarith)
      _ ≤ ε^(1/500:ℝ) := Real.rpow_le_rpow_of_exponent_ge hε hε1 hα
  exact (scalar a b c A B C ha hb hc hA hB hC hS).trans
    (mul_le_mul_of_nonneg_right hbound (by positivity))

/-- Integration pays the three moment bounds, but no caps on factors 2 or 3.
Integrability is supplied separately, not deduced from a purported estimate. -/
theorem integral_of_cap (μ : Measure ℝ) (a b c : ℝ → ℝ) (A B C ε H : ℝ)
    (ha : ∀ t, 0 ≤ a t) (hb : ∀ t, 0 ≤ b t) (hc : ∀ t, 0 ≤ c t)
    (hA : 4 ≤ A) (hB : 4 ≤ B) (hC : 4 ≤ C)
    (hS : (2001/2000:ℝ) ≤ 2/A+2/B+2/C)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hsmall : ∀ᵐ t ∂μ, a t ≤ ε)
    (hfa : Integrable (fun t => a t^A) μ)
    (hfb : Integrable (fun t => b t^B) μ)
    (hfc : Integrable (fun t => c t^C) μ)
    (hp : AEStronglyMeasurable (fun t => (a t*b t*c t)^2) μ)
    (hIa : (∫ t, a t^A ∂μ) ≤ H) (hIb : (∫ t, b t^B ∂μ) ≤ H)
    (hIc : (∫ t, c t^C ∂μ) ≤ H) :
    (∫ t, (a t*b t*c t)^2 ∂μ) ≤ 3*H*ε^(1/500:ℝ) := by
  have hmajor : Integrable (fun t => ε^(1/500:ℝ)*(a t^A+b t^B+c t^C)) μ :=
    ((hfa.add hfb).add hfc).const_mul _
  have hpoint : ∀ᵐ t ∂μ, (a t*b t*c t)^2 ≤ ε^(1/500:ℝ)*(a t^A+b t^B+c t^C) := by
    filter_upwards [hsmall] with t ht
    exact scalar_of_cap (a t) (b t) (c t) A B C ε (ha t) (hb t) (hc t)
      hA hB hC hS hε hε1 ht
  have hint : Integrable (fun t => (a t*b t*c t)^2) μ := by
    apply hmajor.mono' hp
    filter_upwards [hpoint] with t ht
    simpa only [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (a t*b t*c t))] using ht
  have hh := integral_mono_ae hint hmajor hpoint
  have hfab : Integrable (fun t => a t^A+b t^B) μ := hfa.add hfb
  rw [integral_const_mul,integral_add hfab hfc,integral_add hfa hfb] at hh
  have hm := mul_le_mul_of_nonneg_left (add_le_add (add_le_add hIa hIb) hIc)
    (Real.rpow_nonneg hε.le (1/500:ℝ))
  nlinarith

theorem log_budget (L K : ℝ) (hL : 0 < L) :
    3*(K*L^18)*(L^(-26000:ℝ))^(1/500:ℝ)=3*K/L^34 := by
  have hpower : (L^(-26000:ℝ))^(1/500:ℝ)=L^(-52:ℝ) := by
    rw [←Real.rpow_mul hL.le]
    norm_num
  have hinv : L^(-52:ℝ)=(L^52)⁻¹ := by
    rw [Real.rpow_neg hL.le]
    exact congrArg (fun r : ℝ => r⁻¹) (Real.rpow_natCast L 52)
  rw [hpower,hinv]
  field_simp
  <;> ring

#print axioms scalar_of_cap
#print axioms integral_of_cap
run_cmd do
  for n in [``weight_data,``scalar,``scalar_of_cap,``integral_of_cap,``log_budget] do
    for ax in (← Lean.collectAxioms n) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {n}"
  Lean.logInfo "FIRST-FACTOR MOMENT EXTRACTION: VALID ONLY AFTER SUCCESSFUL COMPILATION"
end SourceFirstFactorSaving
