import ClippedPrimeMomentWork
import ProductMomentHolder
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open MeasureTheory Set
namespace ClippedProductEnergyWork
open ClippedPrimeMomentWork

theorem pointwise (P K Q : ℂ) (δ C : ℝ) (hδ : 0<δ) (hC : 0≤C)
    (hP : ‖P‖≤1) (hK : ‖K‖≤C) (hQ : ‖Q‖≤1) :
    ‖P*K*Q‖^2≤‖clip δ P*K*Q‖^2+(C^2/δ^8)*‖P‖^8 := by
  simp only [norm_mul,norm_clip δ P hδ.le]
  by_cases hp : ‖P‖≤δ
  · rw [min_eq_left hp]
    exact le_add_of_nonneg_right (by positivity)
  · have hp8 : δ^8≤‖P‖^8 := pow_le_pow_left₀ hδ.le (le_of_not_ge hp) 8
    have hh : ‖P‖*‖K‖*‖Q‖≤C := by
      calc
        _ ≤ 1*C*1 := mul_le_mul (mul_le_mul hP hK (norm_nonneg _) (by norm_num)) hQ
          (norm_nonneg _) (by positivity)
        _ = C := by ring
    have hh2 := pow_le_pow_left₀ (by positivity : 0≤‖P‖*‖K‖*‖Q‖) hh 2
    have herr : C^2≤(C^2/δ^8)*‖P‖^8 := by
      calc
        _ = (C^2/δ^8)*δ^8 := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left hp8 (by positivity)
    exact (hh2.trans herr).trans (le_add_of_nonneg_left (sq_nonneg _))

theorem integral_bound (a b δ C : ℝ) (P K Q : ℝ→ℂ)
    (hδ : 0<δ) (hC : 0≤C) (hP : Continuous P) (hK : Continuous K) (hQ : Continuous Q)
    (hPc : ∀t∈Icc a b,‖P t‖≤1) (hKc : ∀t∈Icc a b,‖K t‖≤C)
    (hQc : ∀t∈Icc a b,‖Q t‖≤1) :
    (∫t in Icc a b,‖P t*K t*Q t‖^2)≤
      (∫t in Icc a b,‖clip δ (P t)*K t*Q t‖^2)+
        (C^2/δ^8)*(∫t in Icc a b,‖P t‖^8) := by
  have hclip := continuous_clip δ P hP
  have hi : IntegrableOn (fun t => ‖clip δ (P t)*K t*Q t‖^2) (Icc a b) :=
    (((hclip.mul hK).mul hQ).norm.pow 2).continuousOn.integrableOn_Icc
  have hj : IntegrableOn (fun t => (C^2/δ^8)*‖P t‖^8) (Icc a b) :=
    ((hP.norm.pow 8).continuousOn.integrableOn_Icc).const_mul _
  have hh := setIntegral_mono_on (((hP.mul hK).mul hQ).norm.pow 2).continuousOn.integrableOn_Icc
    (hi.add hj) measurableSet_Icc
    (fun t ht => pointwise (P t) (K t) (Q t) δ C hδ hC (hPc t ht) (hKc t ht) (hQc t ht))
  simp only [Pi.pow_apply,Pi.mul_apply,Pi.add_apply] at hh
  simpa only [integral_add hi hj,integral_const_mul] using hh

run_cmd do
  for decl in [``pointwise, ``integral_bound] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end ClippedProductEnergyWork
