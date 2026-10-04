import OuterPrimeEighthScalingWork
import PolynomialLogEnvelope

/-! Conditional local eighth moments with every fixed logarithmic saving.
The polynomial-height prime cap is explicitly required and remains open. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators
namespace OuterPrimeEighthLogWork
open OuterPrimeEighthEnvelopeWork OuterPrimeEighthScalingWork Erdos374.HarmanGram152

def momentConstant : ℝ := 1+8000*envelopeConstant

theorem logSize_le (X T : ℝ) (N : ℕ) (hX : 1≤X) (hlog : 1≤Real.log X)
    (hN : 1≤N) (hNX : (N:ℝ)≤X) (hT : 1≤T) (hTX : T≤X) :
    logSize N T≤20*Real.log X := by
  have hx : 0<X := by linarith
  have hn : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have h1 := Real.log_le_log (show 0<T+1 by linarith) (show T+1≤2*X by linarith)
  rw [Real.log_mul (by norm_num : (2:ℝ)≠0) hx.ne'] at h1
  have hcube : (N:ℝ)^3≤X^3 := pow_le_pow_left₀ hn.le hNX 3
  have hx3 : 1≤X^3 := one_le_pow₀ hX
  have h2 := Real.log_le_log (show 0<8*(N:ℝ)^3+1 by positivity)
    (show 8*(N:ℝ)^3+1≤9*X^3 by nlinarith)
  rw [Real.log_mul (by norm_num : (9:ℝ)≠0) (by positivity),Real.log_pow] at h2
  have h3 := Real.log_le_log (show 0<2*(N:ℝ) by positivity) (show 2*(N:ℝ)≤2*X by linarith)
  rw [Real.log_mul (by norm_num : (2:ℝ)≠0) hx.ne'] at h3
  have hl2 : Real.log 2≤2 := (Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)).trans (by norm_num)
  have hl9 : Real.log 9≤9 := (Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<9)).trans (by norm_num)
  norm_num only [Nat.cast_ofNat] at h2
  unfold logSize
  linarith

theorem eventually_eighth_of_cap (A : ℕ) :
    ∀ᶠ X : ℝ in atTop, 1<X ∧ ∀ (S : Finset ℕ) (N : ℕ) (coeff : ℕ→ℂ)
      (a T σ : ℝ), X^(257/1000:ℝ)≤N → (N:ℝ)≤X →
      1≤T → T≤X^(1124/1250:ℝ) → 1≤σ →
      (∀p∈S,p.Prime ∧ N<p ∧ p≤2*N) →
      (∑p∈S,‖coeff p‖^2)≤N →
      (∀t∈Icc a (a+T),‖verticalDirichlet152 S coeff σ t‖≤1/(Real.log X)^(A+4)) →
      (∫t in Icc a (a+T),‖verticalDirichlet152 S coeff σ t‖^8)≤
        momentConstant/(Real.log X)^A := by
  filter_upwards [eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ)),
    PolynomialLogEnvelope.eventually_bound 1 (A+4) (1/10000) (by norm_num) (by norm_num),
    PolynomialLogEnvelope.eventually_bound (16000*envelopeConstant) (A+3) (1/3125)
      (by have := envelopeConstant_pos; positivity) (by norm_num)] with X hX hlog hfloor hsmall
  refine ⟨hX,?_⟩
  intro S N coeff a T σ hNscale hNX hT hTmax hσ hs henergy hcap
  have hx : 0<X := by linarith
  have hl : 0<Real.log X := by linarith
  have hN : 1≤N := by
    have := (Real.one_le_rpow hX.le (by norm_num : (0:ℝ)≤257/1000)).trans hNscale
    exact_mod_cast this
  let δ := 1/(Real.log X)^(A+4)
  have hd : 0<δ := by dsimp [δ]; positivity
  have hd1 : δ≤1 := by
    exact (div_le_one (by positivity)).mpr (one_le_pow₀ hlog)
  have hf : (Real.log X)^(A+4)≤X^(1/10000:ℝ) := by
    apply le_trans _ (by simpa using hfloor.2)
    gcongr
    linarith
  have hdfloor : X^(-1/10000:ℝ)≤δ := by
    have hh := one_div_le_one_div_of_le (pow_pos hl (A+4)) hf
    rw [show (-1/10000:ℝ)= -(1/10000) by ring,Real.rpow_neg hx.le]
    simpa only [one_div,δ] using hh
  have hm := scaled_eighth_bound S N coeff X a T σ δ hX.le hN hNscale hT hTmax hσ
    hdfloor hd1 hs henergy hcap
  have hTX : T≤X := hTmax.trans (by
    simpa using Real.rpow_le_rpow_of_exponent_le hX.le (show (1124/1250:ℝ)≤1 by norm_num))
  have hL := logSize_le X T N hX.le hlog hN hNX hT hTX
  have hL0 : 0≤logSize N T := by have := (logSize_bounds N T hN hT).1; linarith
  have hm' : (∫t in Icc a (a+T),‖verticalDirichlet152 S coeff σ t‖^8) ≤
      8000*envelopeConstant*(Real.log X)^3*(2*X^(-1/3125:ℝ)+δ^2) := by
    apply hm.trans
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hL0 hL 3) envelopeConstant_pos.le)
      (show 0≤2*X^(-1/3125:ℝ)+δ^2 by positivity)
    exact hh.trans_eq (by ring)
  have hsp : 16000*envelopeConstant*(Real.log X)^(A+3)≤X^(1/3125:ℝ) := by
    apply le_trans _ hsmall.2
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hl.le (by linarith : Real.log X≤1+Real.log X) _)
      (by have := envelopeConstant_pos; positivity)
  have hfirst : 16000*envelopeConstant*(Real.log X)^3*X^(-1/3125:ℝ)≤1/(Real.log X)^A := by
    apply (le_div_iff₀ (pow_pos hl A)).mpr
    calc
      _ = X^(-1/3125:ℝ)*(16000*envelopeConstant*(Real.log X)^(A+3)) := by rw [pow_add]; ring
      _ ≤ X^(-1/3125:ℝ)*X^(1/3125:ℝ) := mul_le_mul_of_nonneg_left hsp (by positivity)
      _ = 1 := by rw [←Real.rpow_add hx]; norm_num
  have hsecond : (Real.log X)^3*δ^2≤1/(Real.log X)^A := by
    apply (le_div_iff₀ (pow_pos hl A)).mpr
    have hp : (Real.log X)^(A+3)≤(Real.log X)^((A+4)*2) :=
      pow_le_pow_right₀ hlog (by omega)
    dsimp [δ]
    calc
      _ = (Real.log X)^(A+3)/(Real.log X)^((A+4)*2) := by
        rw [pow_add,pow_mul]
        field_simp
        <;> ring
      _ ≤ 1 := (div_le_one (pow_pos hl ((A+4)*2))).mpr hp
  have hsecond' := mul_le_mul_of_nonneg_left hsecond (show 0≤8000*envelopeConstant by have := envelopeConstant_pos; positivity)
  apply hm'.trans
  calc
    _ = (16000*envelopeConstant*(Real.log X)^3*X^(-1/3125:ℝ)) +
        8000*envelopeConstant*((Real.log X)^3*δ^2) := by ring
    _ ≤ 1/(Real.log X)^A + 8000*envelopeConstant*(1/(Real.log X)^A) := add_le_add hfirst hsecond'
    _ = _ := by unfold momentConstant; ring


/-- The original outer-prime dyadic lower scale, with unit coefficient energy
proved automatically. The prime cap is still an explicit hypothesis. -/
theorem eventually_outer_prime_eighth_of_cap (A : ℕ) :
    ∀ᶠ X : ℝ in atTop, 1<X ∧ ∀ (S : Finset ℕ) (N : ℕ) (coeff : ℕ→ℂ)
      (a T σ : ℝ), (1/2:ℝ)*X^(9/35:ℝ)≤N → (N:ℝ)≤X →
      1≤T → T≤X^(1124/1250:ℝ) → 1≤σ →
      (∀p∈S,p.Prime ∧ N<p ∧ p≤2*N) →
      (∀p∈S,‖coeff p‖≤1) →
      (∀t∈Icc a (a+T),‖verticalDirichlet152 S coeff σ t‖≤1/(Real.log X)^(A+4)) →
      (∫t in Icc a (a+T),‖verticalDirichlet152 S coeff σ t‖^8)≤
        momentConstant/(Real.log X)^A := by
  filter_upwards [eventually_eighth_of_cap A,
    PolynomialLogEnvelope.eventually_constant_bound 2 (1/7000) (by norm_num) (by norm_num)]
    with X hm he
  refine ⟨hm.1,?_⟩
  intro S N coeff a T σ hNscale hNX hT hTmax hσ hs hw hcap
  have hx : 0<X := by linarith [hm.1]
  have hscale : X^(257/1000:ℝ)≤(1/2:ℝ)*X^(9/35:ℝ) := by
    calc
      _ ≤ (1/2:ℝ)*X^(1/7000:ℝ)*X^(257/1000:ℝ) := by
        have hh := mul_le_mul_of_nonneg_right he.2 (Real.rpow_nonneg hx.le (257/1000))
        nlinarith
      _ = _ := by rw [mul_assoc,←Real.rpow_add hx]; norm_num
  have henergy : (∑p∈S,‖coeff p‖^2)≤N := by
    calc
      _ ≤ ∑p∈S,(1:ℝ) := Finset.sum_le_sum (fun p hp => by
        simpa using pow_le_pow_left₀ (norm_nonneg _) (hw p hp) 2)
      _ = (S.card:ℝ) := by simp
      _ ≤ ((Finset.Ioc N (2*N)).card:ℝ) := by
        exact_mod_cast Finset.card_le_card (show S⊆Finset.Ioc N (2*N) from
          fun p hp => Finset.mem_Ioc.mpr (hs p hp).2)
      _ = (N:ℝ) := by rw [Nat.card_Ioc]; congr 1; omega
  exact hm.2 S N coeff a T σ (hscale.trans hNscale) hNX hT hTmax hσ hs henergy hcap

run_cmd do
  for decl in [``logSize_le, ``eventually_eighth_of_cap, ``eventually_outer_prime_eighth_of_cap] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end OuterPrimeEighthLogWork
