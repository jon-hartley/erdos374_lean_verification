import ClippedPrimeMomentWork
import OuterPrimeEighthLogWork
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators
namespace OuterClippedPrimeEighthWork
open ClippedPrimeMomentWork OuterPrimeEighthWork OuterPrimeEighthEnvelopeWork
open OuterPrimeEighthScalingWork OuterPrimeEighthLogWork Erdos374.HarmanGram152
open DyadicLevelParameters
theorem eighth_bound (S : Finset ℕ) (N : ℕ) (coeff : ℕ→ℂ)
    (a T σ δ : ℝ) (hN : 1≤N) (hT : 1≤T) (hσ : 1≤σ)
    (hδ : 0<δ) (hδ1 : δ≤1)
    (hs : ∀p∈S,p.Prime ∧ N<p ∧ p≤2*N)
    (henergy : (∑p∈S,‖coeff p‖^2)≤N)
    :
    (∫t in Icc a (a+T),‖clip δ (verticalDirichlet152 S coeff σ t)‖^8) ≤
      (B N T/δ^2)^(1/5:ℝ)*M N T +
      bands N*(2:ℝ)^(8/3:ℝ)*(Q T*(2:ℝ)^(2/3:ℝ)+1)*δ^2 := by
  have hp : (δ^3)^((8/3:ℝ)-2)≤δ^2 := by
    rw [←Real.rpow_natCast_mul hδ.le]
    norm_num
  have hh := ClippedPrimeMomentWork.integral_bound 3 (by norm_num) S N coeff
    a T 1 σ δ (8/3) (δ^2) hN (by linarith) (by norm_num) hσ (by positivity)
    (by norm_num) (by norm_num) (by positivity) hs (by simpa using henergy)
    hp
  dsimp only at hh
  rw [quadratic_eq N T hN,sextic_eq N T hN] at hh
  norm_num only [show (3:ℝ)*(8/3)=8 by norm_num, Real.rpow_natCast,
    show ((8/3:ℝ)-2)/(6-8/3)=1/5 by norm_num,
    show (8/3:ℝ)-2=2/3 by norm_num, Nat.cast_ofNat, one_pow, mul_one] at hh
  norm_cast at hh
  have hb := band_bound N T (δ^2) (δ^3) hN hT (by positivity)
    (pow_le_one₀ hδ.le hδ1) (pow_le_one₀ hδ.le hδ1)
  have hQ : 0≤Q T := by
    rw [←quadratic_eq N T hN]
    exact quadratic_nonnegative _ _ _ _ (by linarith)
      (PrimePowerLargeValuesWork.energyBudget_pos 3 N 1 (by norm_num) hN (by norm_num)).le
  apply hh.trans
  apply add_le_add
  · exact le_of_eq (by simp [M])
  · gcongr

theorem schematic_bound (S : Finset ℕ) (N : ℕ) (coeff : ℕ→ℂ)
    (a T σ δ : ℝ) (hN : 1≤N) (hT : 1≤T) (hσ : 1≤σ)
    (hδ : 0<δ) (hδ1 : δ≤1)
    (hs : ∀p∈S,p.Prime ∧ N<p ∧ p≤2*N)
    (henergy : (∑p∈S,‖coeff p‖^2)≤N)
    :
    (∫t in Icc a (a+T),‖clip δ (verticalDirichlet152 S coeff σ t)‖^8) ≤
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
  have hm := eighth_bound S N coeff a T σ δ hN hT hσ hδ hδ1 hs henergy
  apply (hm.trans (add_le_add hfirst htail')).trans
  have hr : 0≤(T/((N:ℝ)^6*δ^2))^(1/5:ℝ)*(1+T/(N:ℝ)^3) := by positivity
  have hextra1 : 0≤tailConstant*L^3*((T/((N:ℝ)^6*δ^2))^(1/5:ℝ)*(1+T/(N:ℝ)^3)) := by positivity
  have hextra2 : 0≤bConstant*2592*L^3*δ^2 := by positivity
  dsimp [envelopeConstant]
  nlinarith

theorem scaled_eighth_bound (S : Finset ℕ) (N : ℕ) (coeff : ℕ→ℂ)
    (X a T σ δ : ℝ) (hX : 1≤X) (hN : 1≤N)
    (hNscale : X^(257/1000:ℝ)≤N) (hT : 1≤T) (hTmax : T≤X^(1124/1250:ℝ))
    (hσ : 1≤σ) (hδ : X^(-1/10000:ℝ)≤δ) (hδ1 : δ≤1)
    (hs : ∀p∈S,p.Prime ∧ N<p ∧ p≤2*N)
    (henergy : (∑p∈S,‖coeff p‖^2)≤N)
    :
    (∫t in Icc a (a+T),‖clip δ (verticalDirichlet152 S coeff σ t)‖^8) ≤
      envelopeConstant*(logSize N T)^3*(2*X^(-1/3125:ℝ)+δ^2) := by
  have hx : 0<X := by linarith
  have hd : 0<δ := (Real.rpow_pos_of_pos hx _).trans_le hδ
  have hm := schematic_bound S N coeff a T σ δ hN hT hσ hd hδ1 hs henergy
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

theorem eventually_eighth (A : ℕ) :
    ∀ᶠ X : ℝ in atTop, 1<X ∧ ∀ (S : Finset ℕ) (N : ℕ) (coeff : ℕ→ℂ)
      (a T σ : ℝ), X^(257/1000:ℝ)≤N → (N:ℝ)≤X →
      1≤T → T≤X^(1124/1250:ℝ) → 1≤σ →
      (∀p∈S,p.Prime ∧ N<p ∧ p≤2*N) →
      (∑p∈S,‖coeff p‖^2)≤N →
      (∫t in Icc a (a+T),‖clip (1/(Real.log X)^(A+4)) (verticalDirichlet152 S coeff σ t)‖^8)≤
        momentConstant/(Real.log X)^A := by
  filter_upwards [eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ)),
    PolynomialLogEnvelope.eventually_bound 1 (A+4) (1/10000) (by norm_num) (by norm_num),
    PolynomialLogEnvelope.eventually_bound (16000*envelopeConstant) (A+3) (1/3125)
      (by have := envelopeConstant_pos; positivity) (by norm_num)] with X hX hlog hfloor hsmall
  refine ⟨hX,?_⟩
  intro S N coeff a T σ hNscale hNX hT hTmax hσ hs henergy
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
    hdfloor hd1 hs henergy
  have hTX : T≤X := hTmax.trans (by
    simpa using Real.rpow_le_rpow_of_exponent_le hX.le (show (1124/1250:ℝ)≤1 by norm_num))
  have hL := logSize_le X T N hX.le hlog hN hNX hT hTX
  have hL0 : 0≤logSize N T := by have := (logSize_bounds N T hN hT).1; linarith
  have hm' : (∫t in Icc a (a+T),‖clip (1/(Real.log X)^(A+4)) (verticalDirichlet152 S coeff σ t)‖^8) ≤
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


/-- The clipped moment has no prime cancellation hypothesis. -/
theorem eventually_outer_prime_eighth (A : ℕ) :
    ∀ᶠ X : ℝ in atTop, 1<X ∧ ∀ (S : Finset ℕ) (N : ℕ) (coeff : ℕ→ℂ)
      (a T σ : ℝ), (1/2:ℝ)*X^(9/35:ℝ)≤N → (N:ℝ)≤X →
      1≤T → T≤X^(1124/1250:ℝ) → 1≤σ →
      (∀p∈S,p.Prime ∧ N<p ∧ p≤2*N) →
      (∀p∈S,‖coeff p‖≤1) →
      (∫t in Icc a (a+T),‖clip (1/(Real.log X)^(A+4)) (verticalDirichlet152 S coeff σ t)‖^8)≤
        momentConstant/(Real.log X)^A := by
  filter_upwards [eventually_eighth A,
    PolynomialLogEnvelope.eventually_constant_bound 2 (1/7000) (by norm_num) (by norm_num)]
    with X hm he
  refine ⟨hm.1,?_⟩
  intro S N coeff a T σ hNscale hNX hT hTmax hσ hs hw
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
  exact hm.2 S N coeff a T σ (hscale.trans hNscale) hNX hT hTmax hσ hs henergy

run_cmd do
  for decl in [``eighth_bound, ``schematic_bound, ``scaled_eighth_bound,
      ``eventually_eighth, ``eventually_outer_prime_eighth] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end OuterClippedPrimeEighthWork
