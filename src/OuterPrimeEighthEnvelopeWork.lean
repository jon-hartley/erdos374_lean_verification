import OuterPrimeEighthWork

/-! A finite, explicit logarithmic envelope for the outer-prime route.
All cap assumptions are visible; no endpoint estimate is asserted. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace OuterPrimeEighthEnvelopeWork
open OuterPrimeEighthWork Erdos374.HarmanGram152

def logSize (N : ℕ) (T : ℝ) : ℝ :=
  1+Real.log (T+1)+Real.log (8*(N:ℝ)^3+1)+Real.log (2*N)
def tailConstant : ℝ := (1+6/Real.log 2)*(2:ℝ)^(8/3:ℝ)*(qConstant*(2:ℝ)^(2/3:ℝ)+1)
def envelopeConstant : ℝ := bConstant*2592+tailConstant

theorem envelopeConstant_pos : 0<envelopeConstant := by
  have hl : 0<Real.log 2 := Real.log_pos (by norm_num)
  unfold envelopeConstant tailConstant bConstant qConstant
  positivity

theorem logSize_bounds (N : ℕ) (T : ℝ) (hN : 1≤N) (hT : 1≤T) :
    1≤logSize N T ∧ 1+Real.log (T+1)≤logSize N T ∧
    1+Real.log (8*(N:ℝ)^3+1)≤logSize N T ∧
    1+Real.log (2*N)≤logSize N T ∧ 1+Real.log N≤logSize N T := by
  have hn : (1:ℝ)≤N := by exact_mod_cast hN
  have hnp : (0:ℝ)<N := by linarith
  have ha := Real.log_nonneg (show 1≤T+1 by linarith)
  have hb := Real.log_nonneg (show 1≤8*(N:ℝ)^3+1 by have := pow_nonneg (Nat.cast_nonneg N : (0:ℝ)≤N) 3; nlinarith)
  have hc := Real.log_nonneg (show 1≤2*(N:ℝ) by linarith)
  have hd := Real.log_le_log hnp (show (N:ℝ)≤2*N by linarith)
  dsimp [logSize]
  constructor; linarith
  constructor; linarith
  constructor; linarith
  constructor <;> linarith

theorem schematic_bound (S : Finset ℕ) (N : ℕ) (coeff : ℕ→ℂ)
    (a T σ δ : ℝ) (hN : 1≤N) (hT : 1≤T) (hσ : 1≤σ)
    (hδ : 0<δ) (hδ1 : δ≤1)
    (hs : ∀p∈S,p.Prime ∧ N<p ∧ p≤2*N)
    (henergy : (∑p∈S,‖coeff p‖^2)≤N)
    (hcap : ∀t∈Icc a (a+T),‖verticalDirichlet152 S coeff σ t‖≤δ) :
    (∫t in Icc a (a+T),‖verticalDirichlet152 S coeff σ t‖^8) ≤
      envelopeConstant*(logSize N T)^3 *
        ((T/((N:ℝ)^6*δ^2))^(1/5:ℝ)*(1+T/(N:ℝ)^3)+δ^2) := by
  let L := logSize N T
  obtain ⟨hL,hLT,hLN,hL2N,hLlogN⟩ := logSize_bounds N T hN hT
  have hLp : 0<L := by dsimp [L]; linarith
  have hn : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have ht : 0≤T := by linarith
  have hc : 1≤bConstant := by norm_num [bConstant]
  have hq : 0≤qConstant := by norm_num [qConstant]
  have hl2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hB : B N T/δ^2 ≤ (bConstant*L^2)*(T/((N:ℝ)^6*δ^2)) := by
    have hh : (1+Real.log (T+1))*(1+Real.log (8*(N:ℝ)^3+1))≤L^2 := by
      simpa [pow_two] using mul_le_mul hLT hLN
        (by have := Real.log_nonneg (show 1≤8*(N:ℝ)^3+1 by have := pow_nonneg (Nat.cast_nonneg N : (0:ℝ)≤N) 3; nlinarith); linarith) hLp.le
    have hh' := mul_le_mul_of_nonneg_left hh (show 0≤bConstant*T/((N:ℝ)^6*δ^2) by positivity)
    dsimp [B]
    convert hh' using 1 <;> ring
  have hroot : (B N T/δ^2)^(1/5:ℝ) ≤
      bConstant*L^2*(T/((N:ℝ)^6*δ^2))^(1/5:ℝ) := by
    have hh := Real.rpow_le_rpow (show 0≤B N T/δ^2 by
      have hb0 : 0≤B N T := (by positivity : (0:ℝ)≤1/(N:ℝ)^6).trans (B_lower N T hN hT)
      exact div_nonneg hb0 (sq_nonneg δ)) hB (by norm_num : (0:ℝ)≤1/5)
    rw [Real.mul_rpow (by positivity) (by positivity)] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right
      (Real.rpow_le_self_of_one_le (one_le_mul_of_one_le_of_one_le hc (one_le_pow₀ hL))
        (by norm_num : (1/5:ℝ)≤1)) (by positivity))
  have hM : M N T≤2592*L*(1+T/(N:ℝ)^3) := by
    have htN : 0≤T/(N:ℝ)^3 := by positivity
    have hprod : T/(N:ℝ)^3≤L*(T/(N:ℝ)^3) := le_mul_of_one_le_left htN hL
    dsimp [M]
    nlinarith
  have hM0 : 0≤M N T := by
    have hn1 : (1:ℝ)≤N := by exact_mod_cast hN
    have := Real.log_nonneg (show 1≤2*(N:ℝ) by linarith)
    dsimp [M]; positivity
  have hfirst := mul_le_mul hroot hM hM0 (by positivity)
  have htail : bands N*(2:ℝ)^(8/3:ℝ)*(Q T*(2:ℝ)^(2/3:ℝ)+1)*δ^2 ≤
      tailConstant*L^2*δ^2 := by
    have hband : bands N≤(1+6/Real.log 2)*L := by
      exact mul_le_mul_of_nonneg_left hLlogN (by positivity)
    have hQ : Q T≤qConstant*L := mul_le_mul_of_nonneg_left hLT hq
    have hterm : Q T*(2:ℝ)^(2/3:ℝ)+1≤(qConstant*(2:ℝ)^(2/3:ℝ)+1)*L := by
      have := mul_le_mul_of_nonneg_right hQ (by positivity : 0≤(2:ℝ)^(2/3:ℝ))
      nlinarith
    have hterm0 : 0≤Q T*(2:ℝ)^(2/3:ℝ)+1 := by
      have : 0≤Q T := by unfold Q; have := Real.log_nonneg (show 1≤T+1 by linarith); positivity
      positivity
    have hh := mul_le_mul (mul_le_mul_of_nonneg_right hband (by positivity : 0≤(2:ℝ)^(8/3:ℝ)))
      hterm hterm0 (by positivity)
    have hh' := mul_le_mul_of_nonneg_right hh (sq_nonneg δ)
    exact hh'.trans_eq (by dsimp [tailConstant]; ring)
  have htail0 : 0≤tailConstant := by unfold tailConstant; positivity
  have hL23 : L^2≤L^3 := by nlinarith [sq_nonneg L, mul_nonneg (sq_nonneg L) (sub_nonneg.mpr hL)]
  have htail' := htail.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hL23 htail0) (sq_nonneg δ))
  have hm := eighth_bound S N coeff a T σ δ hN hT hσ hδ hδ1 hs henergy hcap
  apply (hm.trans (add_le_add hfirst htail')).trans
  have hr : 0≤(T/((N:ℝ)^6*δ^2))^(1/5:ℝ)*(1+T/(N:ℝ)^3) := by positivity
  have hextra1 : 0≤tailConstant*L^3*((T/((N:ℝ)^6*δ^2))^(1/5:ℝ)*(1+T/(N:ℝ)^3)) := by positivity
  have hextra2 : 0≤bConstant*2592*L^3*δ^2 := by positivity
  dsimp [envelopeConstant]
  nlinarith

run_cmd do
  for decl in [``envelopeConstant_pos, ``logSize_bounds, ``schematic_bound] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end OuterPrimeEighthEnvelopeWork
