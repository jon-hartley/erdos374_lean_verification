import OuterPrimeEighthEnvelopeWork

/-! The finite exponent gain in the outer-prime eighth moment, including
a small amount of slack in the prime scale and a lower cap-budget floor. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace OuterPrimeEighthScalingWork
open OuterPrimeEighthEnvelopeWork Erdos374.HarmanGram152

theorem ratio_bound (X N T δ g t κ : ℝ) (hX : 1≤X) (hN : X^g≤N)
    (hT : 0≤T) (hTmax : T≤X^t) (hδ : X^(-κ)≤δ) :
    T/(N^6*δ^2)≤X^(t-6*g+2*κ) ∧ T/N^3≤X^(t-3*g) := by
  have hx : 0<X := by linarith
  have hn : 0<N := (Real.rpow_pos_of_pos hx g).trans_le hN
  have hd : 0<δ := (Real.rpow_pos_of_pos hx (-κ)).trans_le hδ
  have hn6 : X^(6*g)≤N^6 := by
    convert pow_le_pow_left₀ (Real.rpow_nonneg hx.le g) hN 6 using 1
    rw [←Real.rpow_mul_natCast hx.le]; congr 1; ring
  have hn3 : X^(3*g)≤N^3 := by
    convert pow_le_pow_left₀ (Real.rpow_nonneg hx.le g) hN 3 using 1
    rw [←Real.rpow_mul_natCast hx.le]; congr 1; ring
  have hd2 : X^(-2*κ)≤δ^2 := by
    convert pow_le_pow_left₀ (Real.rpow_nonneg hx.le (-κ)) hδ 2 using 1
    rw [←Real.rpow_mul_natCast hx.le]; congr 1; ring
  have hden : X^(6*g-2*κ)≤N^6*δ^2 := by
    have hh := mul_le_mul hn6 hd2 (Real.rpow_nonneg hx.le _) (by positivity)
    rw [←Real.rpow_add hx] at hh
    convert hh using 1 <;> congr 1 <;> ring
  constructor
  · calc
      _ ≤ X^t/(N^6*δ^2) := div_le_div_of_nonneg_right hTmax (by positivity)
      _ ≤ X^t/X^(6*g-2*κ) := div_le_div_of_nonneg_left (by positivity) (by positivity) hden
      _ = _ := by rw [←Real.rpow_sub hx]; congr 1; ring
  · calc
      _ ≤ X^t/N^3 := div_le_div_of_nonneg_right hTmax (by positivity)
      _ ≤ X^t/X^(3*g) := div_le_div_of_nonneg_left (by positivity) (by positivity) hn3
      _ = _ := (Real.rpow_sub hx _ _).symm

theorem power_term_bound (X N T δ g t κ : ℝ) (hX : 1≤X) (hN : X^g≤N)
    (hT : 0≤T) (hTmax : T≤X^t) (hδ : X^(-κ)≤δ) (hbalance : 3*g≤t) :
    (T/(N^6*δ^2))^(1/5:ℝ)*(1+T/N^3)≤2*X^((6*t-21*g+2*κ)/5) := by
  have hx : 0<X := by linarith
  have hn : 0<N := (Real.rpow_pos_of_pos hx g).trans_le hN
  obtain ⟨ha,hb⟩ := ratio_bound X N T δ g t κ hX hN hT hTmax hδ
  have hroot := Real.rpow_le_rpow (show 0≤T/(N^6*δ^2) by positivity) ha (by norm_num : (0:ℝ)≤1/5)
  rw [←Real.rpow_mul hx.le] at hroot
  have hone := Real.one_le_rpow hX (show 0≤t-3*g by linarith)
  have hsum : 1+T/N^3≤2*X^(t-3*g) := by linarith
  have hh := mul_le_mul hroot hsum (by positivity : 0≤1+T/N^3) (by positivity)
  apply hh.trans_eq
  rw [←mul_assoc, mul_comm (X^((t-6*g+2*κ)*(1/5))) 2, mul_assoc, ←Real.rpow_add hx]
  congr 2
  ring

theorem scaled_eighth_bound (S : Finset ℕ) (N : ℕ) (coeff : ℕ→ℂ)
    (X a T σ δ : ℝ) (hX : 1≤X) (hN : 1≤N)
    (hNscale : X^(257/1000:ℝ)≤N) (hT : 1≤T) (hTmax : T≤X^(1124/1250:ℝ))
    (hσ : 1≤σ) (hδ : X^(-1/10000:ℝ)≤δ) (hδ1 : δ≤1)
    (hs : ∀p∈S,p.Prime ∧ N<p ∧ p≤2*N)
    (henergy : (∑p∈S,‖coeff p‖^2)≤N)
    (hcap : ∀t∈Icc a (a+T),‖verticalDirichlet152 S coeff σ t‖≤δ) :
    (∫t in Icc a (a+T),‖verticalDirichlet152 S coeff σ t‖^8) ≤
      envelopeConstant*(logSize N T)^3*(2*X^(-1/3125:ℝ)+δ^2) := by
  have hx : 0<X := by linarith
  have hd : 0<δ := (Real.rpow_pos_of_pos hx _).trans_le hδ
  have hm := schematic_bound S N coeff a T σ δ hN hT hσ hd hδ1 hs henergy hcap
  have hh := power_term_bound X N T δ (257/1000) (1124/1250) (1/10000)
    hX hNscale (by linarith) hTmax (by convert hδ using 1 <;> norm_num) (by norm_num)
  norm_num only [show (6*(1124/1250:ℝ)-21*(257/1000)+2*(1/10000))/5 = -1/3125 by norm_num] at hh
  apply hm.trans
  apply mul_le_mul_of_nonneg_left
  · have he : (-(1/3125:ℝ))= -1/3125 := by ring
    rw [he] at hh
    exact add_le_add hh le_rfl
  · have := (logSize_bounds N T hN hT).1
    exact mul_nonneg envelopeConstant_pos.le (pow_nonneg (by linarith) _)

run_cmd do
  for decl in [``ratio_bound, ``power_term_bound, ``scaled_eighth_bound] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end OuterPrimeEighthScalingWork
