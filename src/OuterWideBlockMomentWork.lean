import OuterBlockMomentWork

/-! Conditional block moments for the literal cofactor endpoint ratio 2049.
The fixed-ratio flat moment costs only an explicit constant, with the same
logarithmic exponents and prime-cap hypothesis as the dyadic theorem. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Filter MeasureTheory Set
namespace OuterWideBlockMomentWork
open Erdos374.HarmanGram152 OuterModeUnitCapWork
open OuterBlockMomentWork (pair_log_bound translated_integral pairConstant)

def flatConstant : ℝ := (1+4*2049^4)*2049^4*5^16
def blockConstant : ℝ := 1+OuterPrimeEighthLogWork.momentConstant+flatConstant+pairConstant

theorem flat_log_bound (X σ lo hi : ℝ) (D N : ℕ)
    (hlog : 1≤Real.log X) (hD : 1≤D) (hDN : D≤N) (hN : N≤2049*D)
    (hNX : (N:ℝ)≤X) (hσ : 1≤σ) (hlohi : lo≤hi) (hT : hi-lo≤(D:ℝ)^4) :
    (∫t in Icc lo hi, ‖verticalDirichlet152 (Finset.Ioc D N) (fun _ => 1) σ t‖^8)
      ≤ flatConstant*(Real.log X)^16 := by
  have hm := FlatEighthMomentWork.eighth_moment_log D N hD hDN
    (fun _ => 1) (by intros; simp) σ lo hi 2049 hσ hlohi (by norm_num) (by exact_mod_cast hN) hT
  rw [Real.log_pow] at hm
  have hNp : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hlogN := Real.log_nonneg (show (1:ℝ)≤N by exact_mod_cast hD.trans hDN)
  have hlogNX := Real.log_le_log hNp hNX
  apply hm.trans
  have hh := mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by linarith : 0≤1+4*Real.log (N:ℝ))
      (by linarith : 1+4*Real.log (N:ℝ)≤5*Real.log X) 16) (by positivity : (0:ℝ)≤(1+4*2049^4)*2049^4)
  simpa [flatConstant,mul_pow,mul_assoc] using hh

theorem eventually_block_of_cap (E : ℕ) :
    ∀ᶠ X : ℝ in atTop, 1<X ∧ ∀ (P A B : Finset ℕ) (Np Na Nb D N : ℕ)
      (c : ℕ→ℂ) (q : ℕ→ℕ→ℂ) (σ a T u v w : ℝ),
      (1/2:ℝ)*X^(9/35:ℝ)≤Np → (Np:ℝ)≤X →
      1≤Na → 1≤Nb → 1≤D → D≤N → N≤2049*D → (N:ℝ)≤X →
      ((4*(Na*Nb):ℕ):ℝ)≤X → 1≤T → T≤X^(1124/1250:ℝ) →
      T≤(D:ℝ)^4 → T≤((Na*Nb:ℕ):ℝ)^2 → 1≤σ →
      (∀p∈P,p.Prime ∧ Np<p ∧ p≤2*Np) →
      (∀a∈A,a.Prime ∧ Na<a ∧ a≤2*Na) →
      (∀b∈B,b.Prime ∧ Nb<b ∧ b≤2*Nb) →
      (∀p∈P,‖c p‖≤1) → (∀a∈A,∀b∈B,‖q a b‖≤1) →
      (∀t∈Icc a (a+T), ‖verticalDirichlet152 P c σ (t-u)‖≤
        1/(Real.log X)^((4*E+24)+4)) →
      (∫t in Icc a (a+T), ‖verticalDirichlet152 P c σ (t-u) *
        verticalDirichlet152 (Finset.Ioc D N) (fun _ => 1) σ t *
          pairPolynomial A B q σ (t-v) (t-w)‖^2) ≤ blockConstant/(Real.log X)^E := by
  filter_upwards [OuterPrimeEighthLogWork.eventually_outer_prime_eighth_of_cap (4*E+24),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with X hp hlog
  refine ⟨hp.1,?_⟩
  intro P A B Np Na Nb D N c q σ a T u v w hNp hNpX hNa hNb hD hDN hN hNX
    hpairX hT hTX hTD hTpair hσ hP hA hB hc hq hcap
  have hprime := hp.2 P Np c (a-u) T σ hNp hNpX hT hTX hσ hP hc (by
    intro t ht
    have hh := hcap (t+u) ⟨by linarith [ht.1],by linarith [ht.2]⟩
    simpa using hh)
  have hprime' : (∫t in Icc a (a+T), ‖verticalDirichlet152 P c σ (t-u)‖^8) ≤
      OuterPrimeEighthLogWork.momentConstant/(Real.log X)^(4*E+24) := by
    rw [translated_integral (fun t => ‖verticalDirichlet152 P c σ t‖^8) a T u (by linarith)]
    exact hprime
  apply OuterModeMomentAssemblyWork.log_budget a (a+T) (Real.log X)
    OuterPrimeEighthLogWork.momentConstant flatConstant pairConstant E
    (fun t => verticalDirichlet152 P c σ (t-u))
    (fun t => verticalDirichlet152 (Finset.Ioc D N) (fun _ => 1) σ t)
    (fun t => pairPolynomial A B q σ (t-v) (t-w)) (by linarith)
    (by unfold OuterPrimeEighthLogWork.momentConstant; have := OuterPrimeEighthEnvelopeWork.envelopeConstant_pos; positivity)
    (by unfold flatConstant; positivity) (by unfold OuterBlockMomentWork.pairConstant; positivity)
    ((NormalizedMeanSquare.continuous_vertical P c σ (fun p hp => (hP p hp).1.pos)).comp
      (continuous_id.sub continuous_const))
    (NormalizedMeanSquare.continuous_vertical _ _ σ (by intro n hn; have := (Finset.mem_Ioc.mp hn).1; omega))
    (OuterModeContinuityWork.continuous_pair A B q σ v w
      (fun a ha => (hA a ha).1.pos) (fun b hb => (hB b hb).1.pos)) hprime'
  · exact flat_log_bound X σ a (a+T) D N hlog hD hDN hN hNX hσ (by linarith) (by linarith)
  · exact pair_log_bound X σ a (a+T) v w A B Na Nb q hlog hNa hNb hpairX hσ
      (by linarith) hA hB hq (by linarith)

run_cmd do
  for decl in [``flat_log_bound, ``eventually_block_of_cap] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end OuterWideBlockMomentWork
