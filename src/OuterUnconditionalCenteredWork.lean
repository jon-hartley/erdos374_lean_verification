import OuterUnconditionalBlockWork
import OuterContinuousTailWork

/-! Unconditional high physical-frequency centered block means using clipped
prime moments and flat cancellation on the large-prime-amplitude set. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Filter MeasureTheory Set
namespace OuterUnconditionalCenteredWork
open Erdos374.HarmanGram152 OuterModeUnitCapWork OuterWideBlockMomentWork

theorem eventually_centered_block (E : ℕ) :
    ∀ᶠ X : ℝ in atTop, 1<X ∧ ∀ (P A B : Finset ℕ) (Np Na Nb D N : ℕ)
      (c : ℕ→ℂ) (q : ℕ→ℕ→ℂ) (σ a T u v w : ℝ),
      (1/2:ℝ)*X^(9/35:ℝ)≤Np → (Np:ℝ)≤X →
      1≤Np → 1≤Na → 1≤Nb → 1≤D → D≤N → N≤2049*D → (N:ℝ)≤X →
      X^(113/500:ℝ)≤D → ((4*(Na*Nb):ℕ):ℝ)≤X → 1≤T → T≤X^(1124/1250:ℝ) →
      T≤(D:ℝ)^4 → T≤((Na*Nb:ℕ):ℝ)^2 → 1<σ →
      (∀p∈P,p.Prime ∧ Np<p ∧ p≤2*Np) →
      (∀a∈A,a.Prime ∧ Na<a ∧ a≤2*Na) →
      (∀b∈B,b.Prime ∧ Nb<b ∧ b≤2*Nb) →
      (∀p∈P,‖c p‖≤1) → (∀a∈A,∀b∈B,‖q a b‖≤1) →
      (∀t∈Icc a (a+T), X^(1/1000:ℝ)≤|t| ∧ |t|≤X) →
      (∫t in Icc a (a+T), ‖verticalDirichlet152 P c σ (t-u) *
        OuterCenteredFlatWork.centeredFlat D N σ t *
          pairPolynomial A B q σ (t-v) (t-w)‖^2) ≤ (2*(blockConstant+1)+1)/(Real.log X)^E := by
  filter_upwards [OuterUnconditionalBlockWork.eventually_block E,
    PolynomialLogEnvelope.eventually_bound 16 E (1/1000) (by norm_num) (by norm_num),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with X hm hsmall hlog
  refine ⟨hm.1,?_⟩
  intro P A B Np Na Nb D N c q σ a T u v w hNp hNpX hNp1 hNa hNb hD hDN hN hNX hDscale
    hpairX hT hTX hTD hTpair hσ hP hA hB hc hq hband
  have hdiscrete := hm.2 P A B Np Na Nb D N c q σ a T u v w hNp hNpX hNp1
    hNa hNb hD hDN hN hNX hDscale hpairX hT hTX hTD hTpair hσ.le hP hA hB hc hq hband
  let F : ℝ→ℂ := fun t => verticalDirichlet152 P c σ (t-u)*pairPolynomial A B q σ (t-v) (t-w)
  have hF : Continuous F :=
    ((NormalizedMeanSquare.continuous_vertical P c σ (fun p hp => (hP p hp).1.pos)).comp
      (continuous_id.sub continuous_const)).mul
    (OuterModeContinuityWork.continuous_pair A B q σ v w
      (fun a ha => (hA a ha).1.pos) (fun b hb => (hB b hb).1.pos))
  have hFcap (t : ℝ) : ‖F t‖≤1 := by
    dsimp [F]
    rw [norm_mul]
    exact (mul_le_mul (unit_cap P Np c σ (t-u) hNp1 hσ.le
      (fun p hp => (hP p hp).2) hc)
      (pair_cap A B Na Nb q σ (t-v) (t-w) hNa hNb hσ.le
        (fun a ha => (hA a ha).2) (fun b hb => (hB b hb).2) hq)
      (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)
  have htail := OuterContinuousTailWork.centered_energy D N σ a (a+T) (X^(1/1000:ℝ)) F
    hD (hD.trans hDN) hσ (by linarith) (by have := hm.1; positivity) hF (fun t _ => hFcap t) (fun t ht => (hband t ht).1)
  have he (K : ℝ→ℂ) (t : ℝ) : F t*K t =
      verticalDirichlet152 P c σ (t-u)*K t*pairPolynomial A B q σ (t-v) (t-w) := by
    dsimp [F]; ring
  simp_rw [he] at htail
  have hpow : 16*(Real.log X)^E≤X^(1/1000:ℝ) := by
    apply le_trans _ hsmall.2
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by linarith : 0≤Real.log X) (by linarith : Real.log X≤1+Real.log X) E)
      (by norm_num)
  have herror : 16/(X^(1/1000:ℝ))≤1/(Real.log X)^E := by
    apply (div_le_div_iff₀ (by have := hm.1; positivity : 0<X^(1/1000:ℝ))
      (by positivity : 0<(Real.log X)^E)).mpr
    simpa using hpow
  calc
    _ ≤ _ := htail
    _ ≤ 2*((blockConstant+1)/(Real.log X)^E)+1/(Real.log X)^E := by linarith
    _ = _ := by ring

run_cmd do
  for decl in [``eventually_centered_block] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end OuterUnconditionalCenteredWork
