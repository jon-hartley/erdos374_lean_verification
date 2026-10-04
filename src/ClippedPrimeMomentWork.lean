import OuterPrimeEighthWork

/-! Capping the amplitude preserves large-value upper bounds. This gives
small-amplitude prime moments without assuming pointwise prime cancellation. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace ClippedPrimeMomentWork
open Erdos374.HarmanGram152 DyadicLevelParameters SupremumMoment MomentThreshold

def clip (δ : ℝ) (z : ℂ) : ℂ := (min ‖z‖ δ : ℝ)

theorem norm_clip (δ : ℝ) (z : ℂ) (hδ : 0≤δ) : ‖clip δ z‖=min ‖z‖ δ := by
  simp [clip,abs_of_nonneg (le_min (norm_nonneg _) hδ)]

theorem continuous_clip (δ : ℝ) (F : ℝ→ℂ) (hF : Continuous F) :
    Continuous (fun t => clip δ (F t)) := by
  exact Complex.continuous_ofReal.comp (hF.norm.min continuous_const)

theorem integral_bound (k : ℕ) (hk : 1≤k)
    (s : Finset ℕ) (N : ℕ) (coeff : ℕ→ℂ) (a T A σ δ p μ : ℝ)
    (hN : 1≤N) (hT : 0<T) (hA : 0<A) (hσ : 1≤σ) (hδ : 0≤δ)
    (hp : 2≤p) (hp6 : p<6) (hμ : 0<μ)
    (hs : ∀q∈s,q.Prime ∧ N<q ∧ q≤2*N)
    (henergy : (∑q∈s,‖coeff q‖^2)≤A*N)
    (hpower : (δ^k)^(p-2)≤μ) :
    let Q := quadratic (N^k) k T (PrimePowerLargeValuesWork.energyBudget k N A)
    let B := sextic (N^k) k T (PrimePowerLargeValuesWork.energyBudget k N A)
    (∫t in Icc a (a+T),‖clip δ (verticalDirichlet152 s coeff σ t)‖^((k:ℝ)*p)) ≤
      (B/μ)^((p-2)/(6-p))*((k^k:ℕ)*A^k*
        (T/(N:ℝ)^k+4*(2:ℝ)^k*(1+k*Real.log (2*N)))) +
      bandCountBound (cutoff B μ p) (δ^k)*(2:ℝ)^p*(Q*(2:ℝ)^(p-2)+1)*μ := by
  let P := fun t => verticalDirichlet152 s coeff σ t
  let F := fun t => clip δ (P t)^k
  let Q := quadratic (N^k) k T (PrimePowerLargeValuesWork.energyBudget k N A)
  let B := sextic (N^k) k T (PrimePowerLargeValuesWork.energyBudget k N A)
  have he := PrimePowerLargeValuesWork.energyBudget_pos k N A hk hN hA
  have hP : Continuous P := NormalizedMeanSquare.continuous_vertical s coeff σ
    (fun q hq => (hs q hq).1.pos)
  have hF : Continuous F := (continuous_clip δ P hP).pow k
  have hQ : 0≤Q := quadratic_nonnegative _ _ _ _ hT.le he.le
  have hB : 0<B := sextic_positive _ _ _ _ (one_le_pow₀ hN) hk hT he
  have hle (t : ℝ) : ‖F t‖≤‖P t^k‖ := by
    dsimp [F]
    rw [norm_pow,norm_pow,norm_clip δ _ hδ]
    exact pow_le_pow_left₀ (le_min (norm_nonneg _) hδ) (min_le_left _ _) k
  have hc : ∀t∈Icc a (a+T),‖F t‖≤δ^k := by
    intro t ht
    dsimp [F]
    rw [norm_pow,norm_clip δ _ hδ]
    exact pow_le_pow_left₀ (le_min (norm_nonneg _) hδ) (min_le_right _ _) k
  have hl : ∀w:ℝ,0<w → volume (DirichletLargeValueMeasure.levelSet F a T w)≤ENNReal.ofReal (Q/w^2+B/w^6) := by
    intro w hw
    apply le_trans (measure_mono (show DirichletLargeValueMeasure.levelSet F a T w ⊆
      DirichletLargeValueMeasure.levelSet (fun t => P t^k) a T w from
      fun t ht => ⟨ht.1,ht.2.trans (hle t)⟩))
    exact PrimePowerLargeValuesWork.measure_bound k hk s N coeff a T A σ w hN hT.le hA hσ hw hs henergy
  have hh := MomentThreshold.integral_bound F a T (δ^k) p Q B μ hF (by positivity)
    hp hp6 hQ hB hμ hc hpower hl
  have hm := PrimePowerMomentWork.normalized_integral_bound s k N coeff a T A σ hN hT.le hσ
    (fun q hq => ⟨(hs q hq).1,(hs q hq).2.1.le,(hs q hq).2.2⟩) henergy
  have hsmall : (∫t in Icc a (a+T),‖F t‖^2)≤
      (k^k:ℕ)*A^k*(T/(N:ℝ)^k+4*(2:ℝ)^k*(1+k*Real.log (2*N))) := by
    apply le_trans (setIntegral_mono_on (hF.norm.pow 2).continuousOn.integrableOn_Icc
      (hP.norm.pow (2*k)).continuousOn.integrableOn_Icc measurableSet_Icc
      (fun t ht => ?_)) hm
    have hh := pow_le_pow_left₀ (norm_nonneg _) (hle t) 2
    simpa only [norm_pow,←pow_mul,Nat.mul_comm,Pi.pow_apply] using hh
  have heq (t:ℝ) : ‖F t‖^p=‖clip δ (P t)‖^((k:ℝ)*p) := by
    dsimp [F]
    rw [norm_pow,←Real.rpow_natCast_mul (norm_nonneg _)]
  simp only [heq] at hh
  exact hh.trans (add_le_add (mul_le_mul_of_nonneg_left hsmall (by positivity)) le_rfl)

run_cmd do
  for decl in [``norm_clip, ``continuous_clip, ``integral_bound] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end ClippedPrimeMomentWork
