import DirectMovingEnergy
import DirectMovingPolynomial
import DirectMovingIntegral

/-! The complete moving base polynomial, with low derivative energy and
high base energy. No freezing in the moving width is used. -/
set_option autoImplicit false
set_option maxHeartbeats 7000000
noncomputable section
open scoped BigOperators
open MeasureTheory

namespace Erdos374.DirectMovingEnergyPolynomial
open PairSpacingRational DirectMovingEnergy DirectMovingPolynomial

def lowCoefficient (H : ℝ) (b : ℝ → ℂ) (ξ : ℝ) : ℂ :=
  if |ξ| ≤ 1/(4*H) then b ξ else 0

def highCoefficient (H : ℝ) (b : ℝ → ℂ) (ξ : ℝ) : ℂ :=
  if |ξ| ≤ 1/(4*H) then 0 else b ξ

theorem polynomial_split (Q F : ℕ) (b : ℝ → ℂ) (H x : ℝ) :
    polynomial Q F b x = polynomial Q F (lowCoefficient H b) x +
      polynomial Q F (highCoefficient H b) x := by
  unfold polynomial PairSpacingKernel.exponentialSum
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ξ hξ
  simp only [lowCoefficient, highCoefficient]
  split_ifs <;> simp

theorem high_energy (Q F : ℕ) (a : ℕ → ℝ) (B H : ℝ)
    (hB : 0 ≤ B) (hH : 0 < H)
    (ha : ∀ n ∈ Finset.Icc 1 Q, |a n| ≤ B) :
    (∑ ξ ∈ frequencies Q F, ‖highCoefficient H (baseCoefficient Q F a) ξ‖^2) ≤
      2*B^2*H*SingletonHarmonic.harmonicSum Q^3 := by
  have heq : (∑ ξ ∈ frequencies Q F, ‖highCoefficient H (baseCoefficient Q F a) ξ‖^2) =
      ∑ ξ ∈ highFrequencies Q F H, ‖baseCoefficient Q F a ξ‖^2 := by
    rw [highFrequencies, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro ξ hξ
    simp only [highCoefficient]
    split_ifs <;> simp_all
  rw [heq]
  exact high_energy_le Q F a B H hB hH ha

theorem low_derivative_energy (Q F : ℕ) (a : ℕ → ℝ) (B H : ℝ)
    (hB : 0 ≤ B) (hH : 0 < H)
    (ha : ∀ n ∈ Finset.Icc 1 Q, |a n| ≤ B) :
    (∑ ξ ∈ frequencies Q F,
      ‖derivativeCoefficient (lowCoefficient H (baseCoefficient Q F a)) ξ‖^2) ≤
      4*B^2*SingletonHarmonic.harmonicSum Q^3/H := by
  have hid (ξ : ℝ) : (Complex.I * ((2*Real.pi*ξ : ℝ) : ℂ)) =
      (2*Real.pi*Complex.I*ξ : ℂ) := by push_cast; ring
  have heq : (∑ ξ ∈ frequencies Q F,
      ‖derivativeCoefficient (lowCoefficient H (baseCoefficient Q F a)) ξ‖^2) =
      ∑ ξ ∈ lowFrequencies Q F H,
        ‖(2*Real.pi*Complex.I*ξ : ℂ)*baseCoefficient Q F a ξ‖^2 := by
    rw [lowFrequencies, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro ξ hξ
    simp only [derivativeCoefficient, lowCoefficient, hid]
    split_ifs <;> simp
  rw [heq]
  exact low_energy_le Q F a B H hB hH ha

theorem low_motion_mean_square (Q F : ℕ) (hQ : 1 ≤ Q) (hF : 1 ≤ F)
    (b : ℝ → ℂ) (X H : ℝ) (hX : 0 < X) (hH : 0 < H) (hHX : H ≤ X/2) :
    (∫ x in X..2*X, ‖polynomial Q F b x-polynomial Q F b ((1-H/X)*x)‖^2) ≤
      4*H^2*(X+8*(Q:ℝ)^2*kappa Q F)*
        ∑ ξ ∈ frequencies Q F, ‖derivativeCoefficient b ξ‖^2 := by
  let α := 1-H/X
  have hα : α ≤ 1 := by
    dsimp [α]
    have hh : 0 ≤ H/X := by positivity
    linarith
  have hαlow : 1/2 ≤ α := by
    dsimp [α]
    have hh : H/X ≤ 1/2 := (div_le_iff₀ hX).mpr (by linarith)
    linarith
  have he := DirectMovingIntegral.low_motion_bound (polynomial Q F b)
    (polynomial Q F (derivativeCoefficient b)) (continuous_polynomial _ _ _)
    (continuous_polynomial _ _ _) X α
    ((X+8*(Q:ℝ)^2*kappa Q F)*∑ ξ ∈ frequencies Q F, ‖derivativeCoefficient b ξ‖^2)
    hX hα
    (fun x hx => polynomial_motion_integral Q F b x α (ne_of_gt (hX.trans_le hx.1)))
    (fun t ht => scaled_mean_square Q F hQ hF (derivativeCoefficient b) X t
      (hαlow.trans ht.1))
  change (∫ x in X..2*X, ‖polynomial Q F b x-polynomial Q F b ((1-H/X)*x)‖^2) ≤ _ at he
  convert he using 1
  dsimp [α]
  field_simp
  ring

theorem base_motion_mean_square (Q F : ℕ) (hQ : 1 ≤ Q) (hF : 1 ≤ F)
    (a : ℕ → ℝ) (B X H : ℝ) (hB : 0 ≤ B) (hX : 0 < X)
    (hH : 0 < H) (hHX : H ≤ X/2)
    (ha : ∀ n ∈ Finset.Icc 1 Q, |a n| ≤ B) :
    (1/X)*(∫ x in X..2*X,
      ‖polynomial Q F (baseCoefficient Q F a) x-
        polynomial Q F (baseCoefficient Q F a) ((1-H/X)*x)‖^2) ≤
      88*B^2*H*SingletonHarmonic.harmonicSum Q^3*
        (1+4*(Q:ℝ)^2*kappa Q F/X) := by
  let b := baseCoefficient Q F a
  let lo := lowCoefficient H b
  let hi := highCoefficient H b
  let α := 1-H/X
  let J := SingletonHarmonic.harmonicSum Q
  let D := (Q:ℝ)^2*kappa Q F
  have hJ : 0 ≤ J := SingletonHarmonic.harmonicSum_nonneg Q
  have hD : 0 ≤ D := mul_nonneg (sq_nonneg _) (kappa_nonneg Q F hQ hF)
  have hα : 1/2 ≤ α := by
    dsimp [α]
    have hh : H/X ≤ 1/2 := (div_le_iff₀ hX).mpr (by linarith)
    linarith
  have hlo := low_motion_mean_square Q F hQ hF lo X H hX hH hHX
  have hle := low_derivative_energy Q F a B H hB hH ha
  have hl : (∫ x in X..2*X, ‖polynomial Q F lo x-polynomial Q F lo (α*x)‖^2) ≤
      16*B^2*H*J^3*(X+8*D) := by
    calc
      _ ≤ 4*H^2*(X+8*D)*(∑ ξ ∈ frequencies Q F, ‖derivativeCoefficient lo ξ‖^2) := by
        simpa only [α, D, mul_assoc] using hlo
      _ ≤ 4*H^2*(X+8*D)*(4*B^2*J^3/H) :=
        mul_le_mul_of_nonneg_left hle (by positivity)
      _ = _ := by field_simp; ring
  have hhi := motion_mean_square Q F hQ hF hi X α hX.le hα
  have hhe := high_energy Q F a B H hB hH ha
  have hh : (∫ x in X..2*X, ‖polynomial Q F hi x-polynomial Q F hi (α*x)‖^2) ≤
      (4*X+24*D)*(2*B^2*H*J^3) := by
    apply hhi.trans
    simpa only [D, mul_assoc] using
      mul_le_mul_of_nonneg_left hhe (show 0 ≤ 4*X+24*D by positivity)
  have hcont (c : ℝ → ℂ) : Continuous (fun x => ‖polynomial Q F c x-
      polynomial Q F c (α*x)‖^2) := by
    have hc := continuous_polynomial Q F c
    fun_prop
  have hilo : IntervalIntegrable (fun x =>
      2*‖polynomial Q F lo x-polynomial Q F lo (α*x)‖^2) volume X (2*X) :=
    ((hcont lo).const_mul 2).intervalIntegrable _ _
  have hihi : IntervalIntegrable (fun x =>
      2*‖polynomial Q F hi x-polynomial Q F hi (α*x)‖^2) volume X (2*X) :=
    ((hcont hi).const_mul 2).intervalIntegrable _ _
  have hsum := intervalIntegral.integral_mono_on (μ := volume) (by linarith : X ≤ 2*X)
    ((hcont b).intervalIntegrable _ _)
    (hilo.add hihi)
    (fun x _ => show ‖polynomial Q F b x-polynomial Q F b (α*x)‖^2 ≤
      2*‖polynomial Q F lo x-polynomial Q F lo (α*x)‖^2 +
        2*‖polynomial Q F hi x-polynomial Q F hi (α*x)‖^2 from by
      rw [polynomial_split Q F b H x, polynomial_split Q F b H (α*x)]
      have heq : polynomial Q F (lowCoefficient H b) x + polynomial Q F (highCoefficient H b) x -
          (polynomial Q F (lowCoefficient H b) (α*x) + polynomial Q F (highCoefficient H b) (α*x)) =
          (polynomial Q F lo x-polynomial Q F lo (α*x)) -
            -(polynomial Q F hi x-polynomial Q F hi (α*x)) := by dsimp [lo, hi]; ring
      rw [heq]
      simpa only [norm_neg] using norm_sub_sq_le
        (polynomial Q F lo x-polynomial Q F lo (α*x))
        (-(polynomial Q F hi x-polynomial Q F hi (α*x))))
  rw [intervalIntegral.integral_add hilo hihi,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hsum
  have hfinal : (∫ x in X..2*X, ‖polynomial Q F b x-polynomial Q F b (α*x)‖^2) ≤
      88*B^2*H*J^3*(X+4*D) := by
    nlinarith [mul_nonneg (show 0 ≤ B^2*H*J^3 by positivity) hX.le]
  calc
    _ ≤ (1/X)*(88*B^2*H*J^3*(X+4*D)) :=
      mul_le_mul_of_nonneg_left hfinal (by positivity)
    _ = _ := by dsimp [J, D]; field_simp

run_cmd do
  for decl in [``polynomial_split, ``high_energy, ``low_derivative_energy,
      ``low_motion_mean_square, ``base_motion_mean_square] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "FULL DIRECT MOVING BASE POLYNOMIAL BOUND PASSED"

end Erdos374.DirectMovingEnergyPolynomial
