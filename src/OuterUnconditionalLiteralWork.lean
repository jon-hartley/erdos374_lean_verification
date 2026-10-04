import OuterLiteralScaleWork
import OuterUnconditionalCenteredWork
import OuterDivisorMomentSumWork

/-! Apply the unconditional clipped-prime/flat/pair moment theorem to the original
centered block, including its exact signed small-divisor sum. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators
namespace OuterUnconditionalLiteralWork
open OuterLiteralFactorizationWork OuterLiteralScaleWork OuterActiveDyadicWork
open OuterBlockCofactorWork OuterBlockMainTermWork OuterCompletedEnergyWork
open OuterModeUnitCapWork OuterDivisorIntervalWork OuterMaskFrequencyWork
open Erdos374.HarmanGram152 MellinWindowFactor OuterCenteredFlatWork

def momentConstant : ℝ := 2*(OuterWideBlockMomentWork.blockConstant+1)+1

theorem momentConstant_pos : 0<momentConstant := by
  unfold momentConstant OuterWideBlockMomentWork.blockConstant OuterWideBlockMomentWork.flatConstant
    OuterBlockMomentWork.pairConstant OuterPrimeEighthLogWork.momentConstant
  have := OuterPrimeEighthEnvelopeWork.envelopeConstant_pos
  positivity

theorem eventually_literal_energy (E : ℕ) :
    ∀ᶠ X : ℝ in atTop,256≤X ∧ ∀(s σ a T : ℝ) (i j : ℕ) (k : BlockKey) (ω : Fin 9→ℝ),
      0≤s → k∈activeKeys X s i j → 1<σ → 1≤T → T≤X^(1124/1250:ℝ) →
      (∀t∈Icc a (a+T),X^(1/1000:ℝ)≤|t| ∧ |t|≤X) →
      (∫t in Icc a (a+T),‖centeredPolynomial X s σ i j k ω t‖^2)≤momentConstant/(Real.log X)^E := by
  filter_upwards [OuterUnconditionalCenteredWork.eventually_centered_block E,
    eventually_active_scales,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1000000:ℝ))] with X hm hg hlog
  refine ⟨hg.1,?_⟩
  intro s σ a T i j k ω hs hk hσ hT hTX hband
  have hX : 2≤X := by linarith [hg.1]
  have hXp : 0<X := by linarith
  have hX1 : 1≤X := by linarith
  have hl : 0<Real.log X := by linarith
  obtain ⟨hNp,hNpX,hNp16,hNa,hNb,hNa2,hNb2,hpairX,hupperX⟩ := hg.2 s i j k hk
  obtain ⟨hscale,hflat,hwide⟩ := OuterBlockCofactorScaleWork.active_lower X s hX hs hlog i j k hk
  have hD := lower_pos X k hscale
  have hDN := lower_le_upper X k hXp
  have hP := primeSet_bounds X k (by omega)
  have hA := firstPrimes_bounds X k hNa2
  have hB := secondPrimes_bounds X k hNb2
  have hflatT : T≤(lower X k:ℝ)^4 := by
    have hh := pow_le_pow_left₀ (Real.rpow_nonneg hXp.le _) hflat 4
    rw [←Real.rpow_mul_natCast hXp.le] at hh
    have he : X^(1124/1250:ℝ)≤X^((113/500:ℝ)*4) := Real.rpow_le_rpow_of_exponent_le hX1 (by norm_num)
    exact hTX.trans (he.trans hh)
  have hpairT : T≤((firstScale k*secondScale k:ℕ):ℝ)^2 := by
    have hh := mul_le_mul hNa hNb (Real.rpow_nonneg hXp.le _) ((Real.rpow_nonneg hXp.le _).trans hNa)
    rw [←Real.rpow_add hXp] at hh
    have hh2 := pow_le_pow_left₀ (Real.rpow_nonneg hXp.le _) hh 2
    rw [←Real.rpow_mul_natCast hXp.le] at hh2
    have he : X^(1124/1250:ℝ)≤X^(((227/1000:ℝ)+227/1000)*2) := Real.rpow_le_rpow_of_exponent_le hX1 (by norm_num)
    simpa only [Nat.cast_mul] using hTX.trans (he.trans hh2)
  let c : ℕ→ℝ→ℂ := fun d t => (d:ℂ)^(-line σ (t-shift ω divisorSlope))
  let F : ℕ→ℝ→ℂ := fun d t =>
    verticalDirichlet152 (primeSet X k) (fun p => ((divisorAtom X s d p).re:ℂ)) σ (t-shift ω primeSlope) *
      centeredFlat (lower X k) (upper X k) σ t *
      pairPolynomial (firstPrimes X k) (secondPrimes X k) (pairWeight X s i j) σ
        (t-shift ω (firstSlope s i)) (t-shift ω (secondSlope s j))
  have hE : 0≤momentConstant/(Real.log X)^E := by have := momentConstant_pos; positivity
  have hcard : (divisorSet X k).card≤divisorScale k := by
    have hh := Finset.card_le_card (show divisorSet X k⊆Finset.Ico (divisorScale k) (2*divisorScale k) from
      fun d hd => Finset.mem_Ico.mpr (divisorSet_bounds X k d hd))
    rw [Nat.card_Ico] at hh
    omega
  have hNd : 1≤divisorScale k := by unfold divisorScale; exact Nat.one_le_pow _ _ (by norm_num)
  have hc (d : ℕ) (hd : d∈divisorSet X k) : Continuous (c d) := by
    have hd0 : d≠0 := by have := (divisorSet_bounds X k d hd).1; omega
    dsimp [c,line]
    exact (show Continuous (fun t : ℝ => -((σ:ℂ)+Complex.I*((t-shift ω divisorSlope:ℝ):ℂ))) by fun_prop).const_cpow
      (Or.inl (by exact_mod_cast hd0))
  have hF (d : ℕ) (_hd : d∈divisorSet X k) : Continuous (F d) := by
    exact (((NormalizedMeanSquare.continuous_vertical _ _ σ (fun p hp => (hP p hp).1.pos)).comp
      (continuous_id.sub continuous_const)).mul
      (OuterModeContinuityWork.continuous_centeredFlat _ _ σ (by omega) (by omega) hσ)).mul
      (OuterModeContinuityWork.continuous_pair _ _ _ σ _ _
        (fun a ha => (hA a ha).1.pos) (fun b hb => (hB b hb).1.pos))
  have hmean (d : ℕ) (hd : d∈divisorSet X k) :
      (∫t in Icc a (a+T),‖F d t‖^2)≤momentConstant/(Real.log X)^E := by
    apply hm.2 (primeSet X k) (firstPrimes X k) (secondPrimes X k)
      (primeScale k) (firstScale k) (secondScale k) (lower X k) (upper X k)
      (fun p => ((divisorAtom X s d p).re:ℂ)) (pairWeight X s i j) σ a T
      (shift ω primeSlope) (shift ω (firstSlope s i)) (shift ω (secondSlope s j))
      hNp hNpX (by omega) (by omega) (by omega) hD hDN hwide hupperX hflat hpairX hT hTX hflatT hpairT
      hσ hP hA hB
    · intro p hp
      simpa only [Complex.norm_real,Real.norm_eq_abs] using
        (Complex.abs_re_le_norm (divisorAtom X s d p)).trans (divisorAtom_norm_le X s d p)
    · intro a ha b hb
      exact pairWeight_norm X s i j a b
    · exact hband
  have hh := OuterDivisorMomentSumWork.sum_energy (divisorSet X k) (divisorScale k) a (a+T)
    (momentConstant/(Real.log X)^E) c F hNd hE hcard hc hF
    (fun d hd t ht => FlatCofactorApproximation.inverse_power_bound (divisorScale k) d σ
      (line σ (t-shift ω divisorSlope)) hNd (divisorSet_bounds X k d hd).1 hσ.le (by simp [line])) hmean
  apply le_trans (le_of_eq ?_) hh
  apply integral_congr_ae
  filter_upwards with t
  rw [centeredPolynomial,mode_prime_factorization X s σ t i j k ω hX,
    OuterDivisorModeWork.divisorFactor,mul_assoc,norm_mul,phase_norm,one_mul,Finset.sum_mul]
  congr 2
  apply Finset.sum_congr rfl
  intro d hd
  dsimp [c,F,remainingFactor]
  ring

run_cmd do
  for decl in [``momentConstant_pos, ``eventually_literal_energy] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end OuterUnconditionalLiteralWork
