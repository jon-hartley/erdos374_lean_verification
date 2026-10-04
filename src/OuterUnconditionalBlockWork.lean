import OuterClippedPrimeEighthWork
import ClippedProductEnergyWork
import OuterWideBlockMomentWork
import OuterWideFlatCapWork
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators
namespace OuterUnconditionalBlockWork
open Erdos374.HarmanGram152 OuterModeUnitCapWork OuterWideBlockMomentWork
open OuterBlockMomentWork (pair_log_bound translated_integral pairConstant)
open ClippedPrimeMomentWork OuterCenteredFlatWork

def rawConstant : ℝ := GaussianMeanSquareWork.meanSquareConstant*256*16

theorem rawConstant_pos : 0<rawConstant := by
  have := GaussianMeanSquareWork.meanSquareConstant_pos
  unfold rawConstant
  positivity

theorem prime_eighth (X T : ℝ) (P : Finset ℕ) (Np : ℕ) (c : ℕ→ℂ) (σ a : ℝ)
    (hX : 1≤X) (hNp : (1/2:ℝ)*X^(9/35:ℝ)≤Np) (hNp1 : 1≤Np)
    (hT : 0≤T) (hTX : T≤X^(1124/1250:ℝ)) (hσ : 1≤σ)
    (hP : ∀p∈P,p.Prime ∧ Np<p ∧ p≤2*Np) (hc : ∀p∈P,‖c p‖≤1) :
    (∫t in Icc a (a+T),‖verticalDirichlet152 P c σ t‖^8)≤rawConstant := by
  have hXp : 0<X := by linarith
  have he : (∑p∈P,‖c p‖^2)≤(1:ℝ)*Np := by
    calc
      _ ≤ ∑p∈P,(1:ℝ) := Finset.sum_le_sum (fun p hp => by
        simpa using pow_le_pow_left₀ (norm_nonneg _) (hc p hp) 2)
      _ = (P.card:ℝ) := by simp
      _ ≤ ((Finset.Ioc Np (2*Np)).card:ℝ) := by
        exact_mod_cast Finset.card_le_card (show P⊆Finset.Ioc Np (2*Np) from
          fun p hp => Finset.mem_Ioc.mpr (hP p hp).2)
      _ = _ := by rw [Nat.card_Ioc]; norm_cast; omega
  have hlen : T≤((2*Np)^4:ℕ) := by
    have hh := pow_le_pow_left₀ (Real.rpow_nonneg hXp.le (9/35))
      (show X^(9/35:ℝ)≤2*(Np:ℝ) by linarith) 4
    rw [←Real.rpow_mul_natCast hXp.le] at hh
    have hr : X^(1124/1250:ℝ)≤X^((9/35:ℝ)*4) :=
      Real.rpow_le_rpow_of_exponent_le hX (by norm_num)
    exact_mod_cast hTX.trans (hr.trans hh)
  simpa [rawConstant,show (2:ℝ)^4=16 by norm_num] using PrimePowerMomentWork.sharp_normalized_integral_bound P 4 Np c a T 1 σ
    hNp1 hT hσ hlen (fun p hp => ⟨(hP p hp).1,(hP p hp).2.1.le,(hP p hp).2.2⟩) he

theorem eventually_block (E : ℕ) :
    ∀ᶠ X : ℝ in atTop, 1<X ∧ ∀ (P A B : Finset ℕ) (Np Na Nb D N : ℕ)
      (c : ℕ→ℂ) (q : ℕ→ℕ→ℂ) (σ a T u v w : ℝ),
      (1/2:ℝ)*X^(9/35:ℝ)≤Np → (Np:ℝ)≤X → 1≤Np →
      1≤Na → 1≤Nb → 1≤D → D≤N → N≤2049*D → (N:ℝ)≤X →
      X^(113/500:ℝ)≤D → ((4*(Na*Nb):ℕ):ℝ)≤X →
      1≤T → T≤X^(1124/1250:ℝ) → T≤(D:ℝ)^4 → T≤((Na*Nb:ℕ):ℝ)^2 → 1≤σ →
      (∀p∈P,p.Prime ∧ Np<p ∧ p≤2*Np) →
      (∀a∈A,a.Prime ∧ Na<a ∧ a≤2*Na) →
      (∀b∈B,b.Prime ∧ Nb<b ∧ b≤2*Nb) →
      (∀p∈P,‖c p‖≤1) → (∀a∈A,∀b∈B,‖q a b‖≤1) →
      (∀t∈Icc a (a+T),X^(1/1000:ℝ)≤|t| ∧ |t|≤X) →
      (∫t in Icc a (a+T), ‖verticalDirichlet152 P c σ (t-u) *
        verticalDirichlet152 (Finset.Ioc D N) (fun _ => 1) σ t *
          pairPolynomial A B q σ (t-v) (t-w)‖^2) ≤ (blockConstant+1)/(Real.log X)^E := by
  obtain ⟨κ,hκ,hκρ,hflat⟩ := OuterWideFlatCapWork.eventually_wide_centered_cap
    (113/500) (1/1000) (by norm_num) (by norm_num) (by norm_num)
  filter_upwards [OuterClippedPrimeEighthWork.eventually_outer_prime_eighth (4*E+24),hflat,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ)),
    PolynomialLogEnvelope.eventually_bound (256*rawConstant) (E+8*(4*E+28)) (2*κ)
      (by have := rawConstant_pos; positivity) (by positivity)] with X hp hf hlog herr
  refine ⟨hp.1,?_⟩
  intro P A B Np Na Nb D N c q σ a T u v w hNp hNpX hNp1 hNa hNb hD hDN hN hNX hDscale
    hpairX hT hTX hTD hTpair hσ hP hA hB hc hq hband
  have hXp : 0<X := by linarith [hp.1]
  have hl : 0<Real.log X := by linarith
  let δ : ℝ := 1/(Real.log X)^(4*E+28)
  let PP := fun t => verticalDirichlet152 P c σ (t-u)
  let KK := fun t => verticalDirichlet152 (Finset.Ioc D N) (fun _ => 1) σ t
  let QQ := fun t => pairPolynomial A B q σ (t-v) (t-w)
  have hd : 0<δ := by dsimp [δ]; positivity
  have hPc : Continuous PP := (NormalizedMeanSquare.continuous_vertical P c σ
    (fun p hp => (hP p hp).1.pos)).comp (continuous_id.sub continuous_const)
  have hKc : Continuous KK := NormalizedMeanSquare.continuous_vertical _ _ σ
    (by intro n hn; have := (Finset.mem_Ioc.mp hn).1; omega)
  have hQc : Continuous QQ := OuterModeContinuityWork.continuous_pair A B q σ v w
    (fun a ha => (hA a ha).1.pos) (fun b hb => (hB b hb).1.pos)
  have hprime := hp.2 P Np c (a-u) T σ hNp hNpX hT hTX hσ hP hc
  have hprime' : (∫t in Icc a (a+T),‖clip δ (PP t)‖^8) ≤
      OuterPrimeEighthLogWork.momentConstant/(Real.log X)^(4*E+24) := by
    rw [translated_integral (fun t => ‖clip δ (verticalDirichlet152 P c σ t)‖^8) a T u (by linarith)]
    convert hprime using 1 <;> congr 1 <;> omega
  have hclipped : (∫t in Icc a (a+T),‖clip δ (PP t)*KK t*QQ t‖^2)≤blockConstant/(Real.log X)^E := by
    apply OuterModeMomentAssemblyWork.log_budget a (a+T) (Real.log X)
      OuterPrimeEighthLogWork.momentConstant flatConstant pairConstant E
      (fun t => clip δ (PP t)) KK QQ hl
      (by unfold OuterPrimeEighthLogWork.momentConstant; have := OuterPrimeEighthEnvelopeWork.envelopeConstant_pos; positivity)
      (by unfold flatConstant; positivity) (by unfold OuterBlockMomentWork.pairConstant; positivity)
      (continuous_clip δ PP hPc) hKc hQc hprime'
    · exact flat_log_bound X σ a (a+T) D N hlog hD hDN hN hNX hσ (by linarith) (by linarith)
    · exact pair_log_bound X σ a (a+T) v w A B Na Nb q hlog hNa hNb hpairX hσ
        (by linarith) hA hB hq (by linarith)
  have hKcap (t : ℝ) (ht : t∈Icc a (a+T)) : ‖KK t‖≤16*X^(-κ) := by
    have hb := hband t ht
    have hf' := hf.2 D N σ t hDscale hNX hDN hN hσ hb.1 hb.2
    have hcont : ‖continuousFlat D N σ t‖≤2*X^(-κ) := by
      calc
        _ ≤ 2/|t| := continuousFlat_bound D N σ t hD (hD.trans hDN) hσ
          ((Real.rpow_pos_of_pos hXp _).trans_le hb.1)
        _ ≤ 2/(X^(1/1000:ℝ)) := div_le_div_of_nonneg_left (by norm_num) (by positivity) hb.1
        _ = 2*X^(-(1/1000:ℝ)) := by rw [Real.rpow_neg hXp.le,div_eq_mul_inv]
        _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hp.1.le (by linarith)) (by norm_num)
    have hh := norm_add_le (centeredFlat D N σ t) (continuousFlat D N σ t)
    simp only [centeredFlat,sub_add_cancel] at hh
    dsimp only [centeredFlat] at hf'
    exact hh.trans (by linarith)
  have hsplit := ClippedProductEnergyWork.integral_bound a (a+T) δ (16*X^(-κ)) PP KK QQ hd (by positivity)
    hPc hKc hQc
    (fun t _ => unit_cap P Np c σ (t-u) hNp1 hσ (fun p hp => (hP p hp).2) hc) hKcap
    (fun t _ => pair_cap A B Na Nb q σ (t-v) (t-w) hNa hNb hσ
      (fun a ha => (hA a ha).2) (fun b hb => (hB b hb).2) hq)
  have hraw : (∫t in Icc a (a+T),‖PP t‖^8)≤rawConstant := by
    rw [translated_integral (fun t => ‖verticalDirichlet152 P c σ t‖^8) a T u (by linarith)]
    exact prime_eighth X T P Np c σ (a-u) hp.1.le hNp hNp1 (by linarith) hTX hσ hP hc
  have hpoly : 256*rawConstant*(Real.log X)^(E+8*(4*E+28))≤X^(2*κ) := by
    apply le_trans _ herr.2
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hl.le (by linarith : Real.log X≤1+Real.log X) _)
      (by have := rawConstant_pos; positivity)
  have herror : ((16*X^(-κ))^2/δ^8)*rawConstant≤1/(Real.log X)^E := by
    apply (le_div_iff₀ (pow_pos hl E)).mpr
    calc
      _ = X^(-(2*κ))*(256*rawConstant*(Real.log X)^(E+8*(4*E+28))) := by
        dsimp [δ]
        rw [mul_pow,←Real.rpow_mul_natCast hXp.le]
        have hex : (-κ)*(2:ℕ)= -(2*κ) := by ring
        rw [hex,pow_add,pow_mul]
        field_simp
        <;> ring
      _ ≤ X^(-(2*κ))*X^(2*κ) := mul_le_mul_of_nonneg_left hpoly (by positivity)
      _ = 1 := by rw [←Real.rpow_add hXp]; norm_num
  exact (hsplit.trans (add_le_add hclipped
    ((mul_le_mul_of_nonneg_left hraw (by positivity)).trans herror))).trans_eq (by ring)

run_cmd do
  for decl in [``rawConstant_pos, ``prime_eighth, ``eventually_block] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end OuterUnconditionalBlockWork
