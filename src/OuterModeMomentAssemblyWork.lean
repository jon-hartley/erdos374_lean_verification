import FlatEighthMomentWork
import OuterPairFourthMomentWork
import ProductMomentHolder

/-! The 8/8/4 Holder step with an explicit logarithmic budget.
This remains conditional on the outer prime eighth moment. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open MeasureTheory Set
namespace OuterModeMomentAssemblyWork

theorem mixed_moments (a b : ℝ) (P K Q : ℝ → ℂ)
    (hP : Continuous P) (hK : Continuous K) (hQ : Continuous Q) :
    (∫ t in Icc a b, ‖P t*K t*Q t‖^2)^4 ≤
      (∫ t in Icc a b, ‖P t‖^8) * (∫ t in Icc a b, ‖K t‖^8) *
        (∫ t in Icc a b, ‖Q t‖^4)^2 := by
  have hfirst := ProductMomentHolder.cauchy_square a b
    (fun t => ‖P t‖^2*‖K t‖^2) (fun t => ‖Q t‖^2)
    (by fun_prop) (by fun_prop) (fun _ => by positivity) (fun _ => by positivity)
  have hsecond := ProductMomentHolder.cauchy_square a b
    (fun t => ‖P t‖^4) (fun t => ‖K t‖^4)
    (by fun_prop) (by fun_prop) (fun _ => by positivity) (fun _ => by positivity)
  have hpair (u v : ℝ) : (u^2*v^2)^2=u^4*v^4 := by ring
  have hfour (u : ℝ) : (u^2)^2=u^4 := by ring
  have heighth (u : ℝ) : (u^4)^2=u^8 := by ring
  simp_rw [hpair,hfour] at hfirst
  simp_rw [heighth] at hsecond
  have hh := pow_le_pow_left₀ (sq_nonneg _) hfirst 2
  rw [mul_pow] at hh
  have hh2 := mul_le_mul_of_nonneg_right hsecond
    (sq_nonneg (∫ t in Icc a b, ‖Q t‖^4))
  apply le_trans (le_of_eq ?_) ((hh.trans hh2).trans_eq (by ring))
  simp only [norm_mul,mul_pow,←pow_mul]

theorem log_budget (a b L Cp Ck Cq : ℝ) (A : ℕ) (P K Q : ℝ → ℂ)
    (hL : 0<L) (hCp : 0≤Cp) (hCk : 0≤Ck) (hCq : 0≤Cq)
    (hP : Continuous P) (hK : Continuous K) (hQ : Continuous Q)
    (hp : (∫ t in Icc a b, ‖P t‖^8) ≤ Cp/L^(4*A+24))
    (hk : (∫ t in Icc a b, ‖K t‖^8) ≤ Ck*L^16)
    (hq : (∫ t in Icc a b, ‖Q t‖^4) ≤ Cq*L^4) :
    (∫ t in Icc a b, ‖P t*K t*Q t‖^2) ≤ (1+Cp+Ck+Cq)/L^A := by
  have hnon (F : ℝ → ℂ) (n : ℕ) : 0≤∫ t in Icc a b, ‖F t‖^n :=
    integral_nonneg (fun _ => by positivity)
  have hh := mixed_moments a b P K Q hP hK hQ
  have hb := mul_le_mul
    (mul_le_mul hp hk (hnon K 8) (by positivity))
    (pow_le_pow_left₀ (hnon Q 4) hq 2)
    (sq_nonneg _) (by positivity : 0≤(Cp/L^(4*A+24))*(Ck*L^16))
  have he : (Cp/L^(4*A+24))*(Ck*L^16)*(Cq*L^4)^2 =
      Cp*Ck*Cq^2/(L^A)^4 := by
    rw [pow_add, pow_mul L 4 A, show (L^4)^A=(L^A)^4 by rw [←pow_mul,←pow_mul]; congr 1; omega]
    field_simp
    <;> ring
  rw [he] at hb
  let C := 1+Cp+Ck+Cq
  have hC : 0≤C := by dsimp [C]; positivity
  have hpC : Cp≤C := by dsimp [C]; linarith
  have hkC : Ck≤C := by dsimp [C]; linarith
  have hqC : Cq≤C := by dsimp [C]; linarith
  have hprod : Cp*Ck*Cq^2 ≤ C^4 := by
    have hh := mul_le_mul (mul_le_mul hpC hkC hCk hC)
      (pow_le_pow_left₀ hCq hqC 2) (sq_nonneg _) (mul_nonneg hC hC)
    nlinarith
  have hfin : (∫ t in Icc a b, ‖P t*K t*Q t‖^2)^4 ≤ (C/L^A)^4 := by
    apply (hh.trans hb).trans
    rw [div_pow]
    exact div_le_div_of_nonneg_right hprod (by positivity)
  exact (pow_le_pow_iff_left₀ (hnon (fun t => P t*K t*Q t) 2)
    (by positivity : 0≤C/L^A) (by norm_num : (4:ℕ)≠0)).mp hfin

run_cmd do
  for decl in [``mixed_moments, ``log_budget] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end OuterModeMomentAssemblyWork
