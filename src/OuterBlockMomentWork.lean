import OuterModeMomentAssemblyWork
import OuterModeContinuityWork
import OuterPrimeEighthLogWork

/-! Conditional square mean for actual shifted prime / flat / correlated-pair
blocks. Only the prime cap is an analytic hypothesis; flat and pair moments
are discharged. This is a discrete block estimate, not source identification. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Filter MeasureTheory Set
namespace OuterBlockMomentWork
open Erdos374.HarmanGram152 OuterModeUnitCapWork

def flatConstant : ℝ := 1040*5^16
def pairConstant : ℝ := 266240*3^4
def blockConstant : ℝ := 1+OuterPrimeEighthLogWork.momentConstant+flatConstant+pairConstant

theorem flat_log_bound (X σ lo hi : ℝ) (D N : ℕ)
    (hlog : 1≤Real.log X) (hD : 1≤D) (hDN : D≤N) (hN : N≤2*D)
    (hNX : (N:ℝ)≤X) (hσ : 1≤σ) (hlohi : lo≤hi) (hT : hi-lo≤(D:ℝ)^4) :
    (∫t in Icc lo hi, ‖verticalDirichlet152 (Finset.Ioc D N) (fun _ => 1) σ t‖^8)
      ≤ flatConstant*(Real.log X)^16 := by
  have hm := FlatEighthMomentWork.dyadic_eighth_moment D N hD hDN hN
    (fun _ => 1) (by intros; simp) σ lo hi hσ hlohi hT
  have hNp : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hlogN := Real.log_nonneg (show (1:ℝ)≤N by exact_mod_cast hD.trans hDN)
  have hlogNX := Real.log_le_log hNp hNX
  apply hm.trans
  have hh := mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by linarith : 0≤1+4*Real.log (N:ℝ))
      (by linarith : 1+4*Real.log (N:ℝ)≤5*Real.log X) 16) (by norm_num : (0:ℝ)≤1040)
  simpa [flatConstant,mul_pow,mul_assoc] using hh

theorem pair_log_bound (X σ lo hi u v : ℝ) (A B : Finset ℕ) (Na Nb : ℕ)
    (q : ℕ→ℕ→ℂ) (hlog : 1≤Real.log X) (hNa : 1≤Na) (hNb : 1≤Nb)
    (hNX : ((4*(Na*Nb):ℕ):ℝ)≤X) (hσ : 1≤σ) (hlohi : lo≤hi)
    (hA : ∀a∈A,a.Prime ∧ Na<a ∧ a≤2*Na)
    (hB : ∀b∈B,b.Prime ∧ Nb<b ∧ b≤2*Nb)
    (hq : ∀a∈A,∀b∈B,‖q a b‖≤1) (hT : hi-lo≤((Na*Nb:ℕ):ℝ)^2) :
    (∫t in Icc lo hi, ‖pairPolynomial A B q σ (t-u) (t-v)‖^4)
      ≤ pairConstant*(Real.log X)^4 := by
  have hm := OuterPairFourthMomentWork.pair_fourth_moment A B Na Nb q σ lo hi u v
    hNa hNb hσ hlohi hA hB hq hT
  have hN : 1≤4*(Na*Nb) := by nlinarith
  have hNp : (0:ℝ)<(4*(Na*Nb):ℕ) := by exact_mod_cast (show 0<4*(Na*Nb) by omega)
  have hlogN := Real.log_nonneg (show (1:ℝ)≤(4*(Na*Nb):ℕ) by exact_mod_cast hN)
  have hlogNX := Real.log_le_log hNp hNX
  rw [Real.log_pow] at hm
  apply hm.trans
  have hh := mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by positivity : 0≤1+2*Real.log ((4*(Na*Nb):ℕ):ℝ))
      (by linarith : 1+2*Real.log ((4*(Na*Nb):ℕ):ℝ)≤3*Real.log X) 4)
      (by norm_num : (0:ℝ)≤266240)
  simpa [pairConstant,mul_pow,mul_assoc] using hh

theorem translated_integral (f : ℝ→ℝ) (a T u : ℝ) (hT : 0≤T) :
    (∫t in Icc a (a+T), f (t-u)) = ∫t in Icc (a-u) (a-u+T), f t := by
  rw [integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc,
    ←intervalIntegral.integral_of_le (show a≤a+T by linarith),
    ←intervalIntegral.integral_of_le (show a-u≤a-u+T by linarith),
    intervalIntegral.integral_comp_sub_right]
  congr 1 <;> ring

theorem eventually_block_of_cap (E : ℕ) :
    ∀ᶠ X : ℝ in atTop, 1<X ∧ ∀ (P A B : Finset ℕ) (Np Na Nb D N : ℕ)
      (c : ℕ→ℂ) (q : ℕ→ℕ→ℂ) (σ a T u v w : ℝ),
      (1/2:ℝ)*X^(9/35:ℝ)≤Np → (Np:ℝ)≤X →
      1≤Na → 1≤Nb → 1≤D → D≤N → N≤2*D → (N:ℝ)≤X →
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
    (by unfold flatConstant; positivity) (by unfold pairConstant; positivity)
    ((NormalizedMeanSquare.continuous_vertical P c σ (fun p hp => (hP p hp).1.pos)).comp
      (continuous_id.sub continuous_const))
    (NormalizedMeanSquare.continuous_vertical _ _ σ (by intro n hn; have := (Finset.mem_Ioc.mp hn).1; omega))
    (OuterModeContinuityWork.continuous_pair A B q σ v w
      (fun a ha => (hA a ha).1.pos) (fun b hb => (hB b hb).1.pos)) hprime'
  · exact flat_log_bound X σ a (a+T) D N hlog hD hDN hN hNX hσ (by linarith) (by linarith)
  · exact pair_log_bound X σ a (a+T) v w A B Na Nb q hlog hNa hNb hpairX hσ
      (by linarith) hA hB hq (by linarith)

run_cmd do
  for decl in [``flat_log_bound, ``pair_log_bound, ``translated_integral, ``eventually_block_of_cap] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end OuterBlockMomentWork
