import PrimePowerMomentWork
import ProductMomentHolder
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! A logarithmic square-mean estimate for four actual prime factors,
uniform in unit complex coefficient phases. This does not replace the
flat or sieve-weighted cofactor in the outstanding rest estimate. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace FourPrimeMomentWork
open Erdos374.HarmanGram152

theorem four_eighth_moments (a b : ℝ) (F G H J : ℝ → ℂ)
    (hF : Continuous F) (hG : Continuous G) (hH : Continuous H) (hJ : Continuous J) :
    (∫ t in Icc a b, ‖F t * G t * H t * J t‖^2)^4 ≤
      (∫ t in Icc a b, ‖F t‖^8) * (∫ t in Icc a b, ‖G t‖^8) *
        (∫ t in Icc a b, ‖H t‖^8) * (∫ t in Icc a b, ‖J t‖^8) := by
  have hfirst := ProductMomentHolder.cauchy_square a b
    (fun t => ‖F t‖^2 * ‖G t‖^2) (fun t => ‖H t‖^2 * ‖J t‖^2)
    (by fun_prop) (by fun_prop) (fun _ => by positivity) (fun _ => by positivity)
  have hsecond := ProductMomentHolder.cauchy_square a b
    (fun t => ‖F t‖^4) (fun t => ‖G t‖^4)
    (by fun_prop) (by fun_prop) (fun _ => by positivity) (fun _ => by positivity)
  have hthird := ProductMomentHolder.cauchy_square a b
    (fun t => ‖H t‖^4) (fun t => ‖J t‖^4)
    (by fun_prop) (by fun_prop) (fun _ => by positivity) (fun _ => by positivity)
  have hpair (u v : ℝ) : (u^2*v^2)^2 = u^4*v^4 := by ring
  have heighth (u : ℝ) : (u^4)^2 = u^8 := by ring
  simp_rw [hpair] at hfirst
  simp_rw [heighth] at hsecond hthird
  have hh := pow_le_pow_left₀ (sq_nonneg _) hfirst 2
  rw [mul_pow] at hh
  have hp := mul_le_mul hsecond hthird (sq_nonneg _)
    (mul_nonneg (integral_nonneg (fun _ => by positivity))
      (integral_nonneg (fun _ => by positivity)))
  apply le_trans (le_of_eq ?_) ((hh.trans hp).trans_eq (by ring))
  simp only [norm_mul, mul_pow, ← pow_mul]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun t => by ring)

theorem square_bound_of_eighth (a b B : ℝ) (F : Fin 4 → ℝ → ℂ)
    (hB : 0 ≤ B) (hF : ∀ i, Continuous (F i))
    (hm : ∀ i, (∫ t in Icc a b, ‖F i t‖^8) ≤ B) :
    (∫ t in Icc a b, ‖F 0 t * F 1 t * F 2 t * F 3 t‖^2) ≤ B := by
  have hh := four_eighth_moments a b (F 0) (F 1) (F 2) (F 3)
    (hF 0) (hF 1) (hF 2) (hF 3)
  have hmi (i : Fin 4) : 0 ≤ ∫ t in Icc a b, ‖F i t‖^8 :=
    integral_nonneg (fun _ => by positivity)
  have hb := mul_le_mul (mul_le_mul (mul_le_mul (hm 0) (hm 1) (hmi 1) hB)
    (hm 2) (hmi 2) (mul_nonneg hB hB)) (hm 3) (hmi 3)
    (mul_nonneg (mul_nonneg hB hB) hB)
  have hp : (∫ t in Icc a b, ‖F 0 t * F 1 t * F 2 t * F 3 t‖^2)^4 ≤ B^4 :=
    (hh.trans hb).trans_eq (by ring)
  exact (pow_le_pow_iff_left₀ (integral_nonneg (fun _ => sq_nonneg _)) hB
    (by norm_num : (4 : ℕ) ≠ 0)).mp hp

def momentConstant : ℝ :=
  GaussianMeanSquareWork.meanSquareConstant * (4^4 : ℕ) * (8 : ℝ)^4

theorem momentConstant_pos : 0 < momentConstant := by
  unfold momentConstant
  exact mul_pos (mul_pos GaussianMeanSquareWork.meanSquareConstant_pos (by norm_num)) (by norm_num)

theorem eventual_square_bound :
    ∃ W : ℝ, 2 ≤ W ∧ ∀ (N : Fin 4 → ℕ), (∀ i, W ≤ (N i : ℝ)) →
      ∀ (S : Fin 4 → Finset ℕ) (coeff : Fin 4 → ℕ → ℂ) (a T σ ell : ℝ),
        0 ≤ T → 1 ≤ σ → 0 < ell →
        (∀ i, ell ≤ Real.log (N i)) →
        (∀ i, T ≤ ((2*N i)^4 : ℕ)) →
        (∀ i, ∀ p ∈ S i, Nat.Prime p ∧ N i ≤ p ∧ p ≤ 2*N i) →
        (∀ i, ∀ p ∈ S i, ‖coeff i p‖ ≤ 1) →
        (∫ t in Icc a (a+T),
          ‖verticalDirichlet152 (S 0) (coeff 0) σ t *
            verticalDirichlet152 (S 1) (coeff 1) σ t *
            verticalDirichlet152 (S 2) (coeff 2) σ t *
            verticalDirichlet152 (S 3) (coeff 3) σ t‖^2) ≤ momentConstant/ell^4 := by
  obtain ⟨W, hW, hm⟩ := PrimePowerMomentWork.eventual_unit_prime_moment 4
  refine ⟨W, hW, ?_⟩
  intro N hNW S coeff a T σ ell hT hσ hell hlog hTN hs hw
  let F : Fin 4 → ℝ → ℂ := fun i => verticalDirichlet152 (S i) (coeff i) σ
  have hF (i : Fin 4) : Continuous (F i) :=
    NormalizedMeanSquare.continuous_vertical (S i) (coeff i) σ
      (fun p hp => (hs i p hp).1.pos)
  have hmoment (i : Fin 4) : (∫ t in Icc a (a+T), ‖F i t‖^8) ≤ momentConstant/ell^4 := by
    have hh := hm (N i) (hNW i) (S i) (coeff i) a T σ hT hσ (hTN i) (hs i) (hw i)
    apply hh.trans
    exact div_le_div_of_nonneg_left momentConstant_pos.le (pow_pos hell 4)
      (pow_le_pow_left₀ hell.le (hlog i) 4)
  exact square_bound_of_eighth a (a+T) (momentConstant/ell^4) F
    (div_nonneg momentConstant_pos.le (pow_nonneg hell.le 4)) hF hmoment

def point101Constant : ℝ := momentConstant / (57/250 : ℝ)^4

theorem eventually_point101 :
    ∀ᶠ X : ℝ in Filter.atTop, 1 < X ∧
      ∀ (N : Fin 4 → ℕ), (∀ i, X^(57/250 : ℝ) ≤ (N i : ℝ)) →
        ∀ (S : Fin 4 → Finset ℕ) (coeff : Fin 4 → ℕ → ℂ) (a T σ : ℝ),
          0 ≤ T → T ≤ X^(1124/1250 : ℝ) → 1 ≤ σ →
          (∀ i, ∀ p ∈ S i, Nat.Prime p ∧ N i ≤ p ∧ p ≤ 2*N i) →
          (∀ i, ∀ p ∈ S i, ‖coeff i p‖ ≤ 1) →
          (∫ t in Icc a (a+T),
            ‖verticalDirichlet152 (S 0) (coeff 0) σ t *
              verticalDirichlet152 (S 1) (coeff 1) σ t *
              verticalDirichlet152 (S 2) (coeff 2) σ t *
              verticalDirichlet152 (S 3) (coeff 3) σ t‖^2) ≤
                point101Constant/(Real.log X)^4 := by
  obtain ⟨W, hW, hm⟩ := eventual_square_bound
  have hlarge := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 57/250)).eventually
    (Filter.eventually_ge_atTop W)
  filter_upwards [hlarge, Filter.eventually_gt_atTop (1 : ℝ)] with X hWlarge hX
  refine ⟨hX, ?_⟩
  intro N hN S coeff a T σ hT hTX hσ hs hw
  have hX0 : 0 < X := by linarith
  have hlogX : 0 < Real.log X := Real.log_pos hX
  have hlog (i : Fin 4) : (57/250 : ℝ)*Real.log X ≤ Real.log (N i) := by
    have hh := Real.log_le_log (Real.rpow_pos_of_pos hX0 _) (hN i)
    rwa [Real.log_rpow hX0] at hh
  have hTN (i : Fin 4) : T ≤ ((2*N i)^4 : ℕ) := by
    calc
      T ≤ X^(1124/1250 : ℝ) := hTX
      _ ≤ X^((57/250 : ℝ)*4) := Real.rpow_le_rpow_of_exponent_le hX.le (by norm_num)
      _ = (X^(57/250 : ℝ))^4 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hX0.le]
        norm_num
      _ ≤ (N i : ℝ)^4 := pow_le_pow_left₀ (Real.rpow_nonneg hX0.le _) (hN i) 4
      _ ≤ (2*(N i : ℝ))^4 := pow_le_pow_left₀ (Nat.cast_nonneg _) (by linarith) 4
      _ = _ := by push_cast; rfl
  apply (hm N (fun i => hWlarge.trans (hN i)) S coeff a T σ
    ((57/250 : ℝ)*Real.log X) hT hσ (mul_pos (by norm_num) hlogX) hlog hTN hs hw).trans_eq
  dsimp [point101Constant]
  rw [mul_pow]
  ring

#print axioms eventually_point101
#print axioms eventual_square_bound
run_cmd do
  for decl in [``four_eighth_moments, ``square_bound_of_eighth,
      ``momentConstant_pos, ``eventual_square_bound, ``eventually_point101] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "FOUR PRIME LOGARITHMIC SQUARE MEAN PASSED"
end FourPrimeMomentWork
