import PairActualCoefficient
import SingletonActualEnvelope

/-! Scalar envelope for the proposed quantitative Fourier moving bound.
This file proves no mean-square estimate and adds no analytic hypothesis. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open Filter

namespace PairActualEnvelope

def proposedBound (Q F : ℕ) (X Y : ℝ) : ℝ :=
  30*Y*SingletonHarmonic.harmonicSum Q^3+
  144*Y^2*((Q:ℝ)^2/X)*(1+Real.log (2*(F:ℝ)*(Q:ℝ)^2))*SingletonHarmonic.harmonicSum Q^3+
  48*(Q:ℝ)*SingletonHarmonic.harmonicSum Q/F+96*Y*(Q:ℝ)^2/((F:ℝ)*X)

theorem data (X : ℝ) (hX : 1<X) (Q : ℕ) (hQ : 1≤Q)
    (hQX : (Q:ℝ)≤X^(62/125:ℝ)) :
    let F:=⌈X^2⌉₊
    (0:ℝ)<F ∧ (Q:ℝ)≤F ∧ (Q:ℝ)^2≤F ∧
      (Q:ℝ)^2/X≤X^(-(1/125:ℝ)) ∧
      SingletonHarmonic.harmonicSum Q≤1+Real.log X ∧
      1+Real.log (2*(F:ℝ)*(Q:ℝ)^2)≤6*(1+Real.log X) := by
  let F:=⌈X^2⌉₊
  have hXp : 0<X := by linarith
  have hQp : (0:ℝ)<Q := by exact_mod_cast (show 0<Q by omega)
  have hlog : 0≤Real.log X := Real.log_nonneg hX.le
  have hQ2 : (Q:ℝ)^2≤X^(124/125:ℝ) := by
    have hp := pow_le_pow_left₀ hQp.le hQX 2
    rw [←Real.rpow_mul_natCast hXp.le] at hp
    norm_num at hp
    exact hp
  have hQ2X : (Q:ℝ)^2≤X := hQ2.trans (by
    simpa using Real.rpow_le_rpow_of_exponent_le hX.le (by norm_num : (124/125:ℝ)≤1))
  have hQX1 : (Q:ℝ)≤X := hQX.trans (by
    simpa using Real.rpow_le_rpow_of_exponent_le hX.le (by norm_num : (62/125:ℝ)≤1))
  have hF : X^2≤(F:ℝ) := Nat.le_ceil _
  have hFup : (F:ℝ)≤2*X^2 := by
    have hh := Nat.ceil_lt_add_one (sq_nonneg X)
    dsimp [F]
    nlinarith
  have hFp : (0:ℝ)<F := lt_of_lt_of_le (sq_pos_of_pos hXp) hF
  refine ⟨hFp,hQX1.trans (by nlinarith),hQ2X.trans (by nlinarith),?_,?_,?_⟩
  · calc
      (Q:ℝ)^2/X ≤ X^(124/125:ℝ)/X := div_le_div_of_nonneg_right hQ2 hXp.le
      _ = _ := by
        rw [show (-(1/125:ℝ))=(124/125:ℝ)-1 by norm_num,Real.rpow_sub hXp,Real.rpow_one]
  · exact (SingletonHarmonic.harmonicSum_le_one_add_log Q).trans
      (add_le_add le_rfl (Real.log_le_log hQp hQX1))
  · have hprod : 2*(F:ℝ)*(Q:ℝ)^2≤4*X^3 := by
      calc
        _ ≤ 2*(2*X^2)*X := mul_le_mul (by nlinarith) hQ2X (sq_nonneg _) (by positivity)
        _ = _ := by ring
    have hl := Real.log_le_log (by positivity : 0<2*(F:ℝ)*(Q:ℝ)^2) hprod
    rw [Real.log_mul (by norm_num : (4:ℝ)≠0) (pow_ne_zero _ hXp.ne'),Real.log_pow] at hl
    have h4 : Real.log 4≤3 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4)]
    change 1+Real.log (2*(F:ℝ)*(Q:ℝ)^2)≤6*(1+Real.log X)
    norm_num at hl
    linarith

theorem scalar_bound (X Y : ℝ) (hX : 1<X) (hY : X^(1/125:ℝ)≤Y)
    (Q : ℕ) (hQ : 1≤Q) (hQX : (Q:ℝ)≤X^(62/125:ℝ)) :
    proposedBound Q ⌈X^2⌉₊ X Y≤1038*Y^2*X^(-(1/125:ℝ))*(1+Real.log X)^4 := by
  let F:=⌈X^2⌉₊
  let L:=1+Real.log X
  let H:=SingletonHarmonic.harmonicSum Q
  have hXp : 0<X := by linarith
  have hL : 1≤L := by dsimp [L]; linarith [Real.log_nonneg hX.le]
  have hL0 : 0≤L := by linarith
  have hY1 : 1≤Y := (Real.one_le_rpow hX.le (by norm_num : (0:ℝ)≤1/125)).trans hY
  have hY0 : 0≤Y := by linarith
  obtain ⟨hF,hQF,hQ2F,hbd,hH,hκ⟩ := data X hX Q hQ hQX
  have hH0 : 0≤H := SingletonHarmonic.harmonicSum_nonneg Q
  have hH3 : H^3≤L^3 := pow_le_pow_left₀ hH0 hH 3
  have hL3 : L≤L^3 := by nlinarith [sq_nonneg (L-1)]
  have hL34 : L^3≤L^4 := by nlinarith [pow_nonneg hL0 3]
  have hL31 : 1≤L^3 := one_le_pow₀ hL
  have hLY : L≤Y*L^3 := hL3.trans (le_mul_of_one_le_left (pow_nonneg hL0 _) hY1)
  have h1 : 30*Y*H^3≤30*Y*L^3 := mul_le_mul_of_nonneg_left hH3 (by positivity)
  have h3 : 48*(Q:ℝ)*H/(F:ℝ)≤48*L := by
    have hr : (Q:ℝ)/(F:ℝ)≤1 := (div_le_one hF).mpr hQF
    calc
      _ = 48*((Q:ℝ)/(F:ℝ))*H := by ring
      _ ≤48*1*L := mul_le_mul (mul_le_mul_of_nonneg_left hr (by norm_num)) hH hH0 (by norm_num)
      _ = _ := by ring
  have h4 : 96*Y*(Q:ℝ)^2/((F:ℝ)*X)≤96*Y := by
    have hQ2FX : (Q:ℝ)^2≤(F:ℝ)*X := hQ2F.trans (le_mul_of_one_le_right hF.le hX.le)
    have hr : (Q:ℝ)^2/((F:ℝ)*X)≤1 := (div_le_one (mul_pos hF hXp)).mpr hQ2FX
    calc
      _ = (96*Y)*((Q:ℝ)^2/((F:ℝ)*X)) := by ring
      _ ≤(96*Y)*1 := mul_le_mul_of_nonneg_left hr (by positivity)
      _ = _ := mul_one _
  have h2 : 144*Y^2*((Q:ℝ)^2/X)*(1+Real.log (2*(F:ℝ)*(Q:ℝ)^2))*H^3≤
      864*Y^2*X^(-(1/125:ℝ))*L^4 := by
    have hQ1 : (1:ℝ)≤Q := by exact_mod_cast hQ
    have hF1 : (1:ℝ)≤F := hQ1.trans hQF
    have hprod : 1≤2*(F:ℝ)*(Q:ℝ)^2 := by nlinarith
    have hκ0 : 0≤1+Real.log (2*(F:ℝ)*(Q:ℝ)^2) := by
      linarith [Real.log_nonneg hprod]
    calc
      _ ≤144*Y^2*(X^(-(1/125:ℝ)))*(6*L)*L^3 := by
        apply mul_le_mul
        · apply mul_le_mul
          · exact mul_le_mul_of_nonneg_left hbd (by positivity)
          · exact hκ
          · exact hκ0
          · positivity
        · exact hH3
        · positivity
        · positivity
      _ = _ := by ring
  have hYX : 1≤Y*X^(-(1/125:ℝ)) := by
    have hh := mul_le_mul_of_nonneg_right hY (Real.rpow_pos_of_pos hXp (-(1/125:ℝ))).le
    rw [←Real.rpow_add hXp] at hh
    norm_num at hh
    exact hh
  have hYY : Y≤Y^2*X^(-(1/125:ℝ)) := by nlinarith
  have hmain : 174*Y*L^3≤174*Y^2*X^(-(1/125:ℝ))*L^4 := by
    calc
      _ ≤174*(Y^2*X^(-(1/125:ℝ)))*L^4 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hYY (by norm_num)) hL34 (by positivity) (by positivity)
      _ = _ := by ring
  change 30*Y*H^3+144*Y^2*((Q:ℝ)^2/X)*(1+Real.log (2*(F:ℝ)*(Q:ℝ)^2))*H^3+
    48*(Q:ℝ)*H/(F:ℝ)+96*Y*(Q:ℝ)^2/((F:ℝ)*X)≤_
  have hYL3 : Y≤Y*L^3 := le_mul_of_one_le_right hY0 hL31
  nlinarith

theorem eventually_uniform_bound :
    ∀ᶠ X : ℝ in atTop, 1<X ∧ ∀Q:ℕ, 1≤Q → (Q:ℝ)≤X^(62/125:ℝ) →
      let Y:=PositiveSharpPowerWindow.halfWidth X (101/1000)
      proposedBound Q ⌈X^2⌉₊ X Y≤Y^2*X^(-(1/250:ℝ)) := by
  filter_upwards [PolynomialLogEnvelope.eventually_bound 1038 4 (1/250)
    (by norm_num) (by norm_num),eventually_gt_atTop (1:ℝ),
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<93/1000)).eventually
      (eventually_ge_atTop (2:ℝ))] with X he hX hp
  refine ⟨hX,?_⟩
  intro Q hQ hQX
  let Y:=PositiveSharpPowerWindow.halfWidth X (101/1000)
  change proposedBound Q ⌈X^2⌉₊ X Y≤Y^2*X^(-(1/250:ℝ))
  have hXp : 0<X := by linarith
  have hY : X^(1/125:ℝ)≤Y := by
    have hmul := mul_le_mul_of_nonneg_left hp (Real.rpow_pos_of_pos hXp (1/125:ℝ)).le
    rw [←Real.rpow_add hXp] at hmul
    norm_num at hmul
    dsimp [Y,PositiveSharpPowerWindow.halfWidth]
    linarith
  have hh := scalar_bound X Y hX hY Q hQ hQX
  calc
    _ ≤1038*Y^2*X^(-(1/125:ℝ))*(1+Real.log X)^4 := hh
    _ = Y^2*X^(-(1/125:ℝ))*(1038*(1+Real.log X)^4) := by ring
    _ ≤Y^2*X^(-(1/125:ℝ))*X^(1/250:ℝ) :=
      mul_le_mul_of_nonneg_left he.2 (by positivity)
    _ = _ := by rw [mul_assoc,←Real.rpow_add hXp]; norm_num

run_cmd do
  for decl in [``data,``scalar_bound,``eventually_uniform_bound] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "PAIR SCALAR ENVELOPE SAVES X^(-1/250); NO MOMENT ESTIMATE ASSERTED"

end PairActualEnvelope
