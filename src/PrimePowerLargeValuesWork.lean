import PrimePowerMomentWork
import NormalizedPowerMoment

/-! Prime-power large-value and intermediate-moment estimates with an
exact coefficient-energy budget: no arbitrary positive power loss.
The moment's pointwise cap is an explicit application hypothesis. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open MeasureTheory Set
open scoped BigOperators ComplexConjugate ENNReal
namespace PrimePowerLargeValuesWork
open Erdos374.HarmanGram152 Erdos374.HarmanAnalytic151MeanSquare
open DirichletPowerCoefficients DirichletLargeValueMeasure DyadicLevelParameters
open SupremumMoment MomentThreshold

def energyBudget (k N : ℕ) (A : ℝ) : ℝ := (k^k:ℕ)*(A/N)^k

theorem energyBudget_pos (k N : ℕ) (A : ℝ) (hk : 1≤k) (hN : 1≤N) (hA : 0<A) :
    0<energyBudget k N A := by
  have hkp : 0<k := by omega
  have hNp : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  unfold energyBudget
  positivity

theorem measure_bound (k : ℕ) (hk : 1≤k)
    (s : Finset ℕ) (N : ℕ) (coeff : ℕ→ℂ) (a T A σ V : ℝ)
    (hN : 1≤N) (hT : 0≤T) (hA : 0<A) (hσ : 1≤σ) (hV : 0<V)
    (hs : ∀p∈s,p.Prime ∧ N<p ∧ p≤2*N)
    (henergy : (∑p∈s,‖coeff p‖^2)≤A*N) :
    volume (levelSet (fun t => verticalDirichlet152 s coeff σ t^k) a T V) ≤
      ENNReal.ofReal (quadratic (N^k) k T (energyBudget k N A)/V^2 +
        sextic (N^k) k T (energyBudget k N A)/V^6) := by
  have hNp : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  let weighted : ℕ→ℂ := fun p => conj (normalizedCoefficients152 coeff σ p)
  have he : (∑p∈s,‖weighted p‖^2)≤A/N := by
    dsimp [weighted]
    simp only [RCLike.norm_conj]
    apply (normalized_coefficients_energy152 s coeff N hN σ hσ
      (fun p hp => (hs p hp).2.1.le)).trans
    calc
      _ ≤ (A*N)/(N:ℝ)^2 := div_le_div_of_nonneg_right henergy (sq_nonneg _)
      _ = _ := by field_simp
  have hbudget : (∑n∈Finset.Ioc (N^k) (2^k*N^k),‖coefficient s k weighted n‖^2)≤
      energyBudget k N A := by
    calc
      _ ≤ ∑n∈Finset.Icc 1 ((2*N)^k),‖coefficient s k weighted n‖^2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro n hn
          obtain ⟨hl,hu⟩ := Finset.mem_Ioc.mp hn
          apply Finset.mem_Icc.mpr
          constructor
          · omega
          · simpa only [mul_pow] using hu
        · intro n hn hnot
          exact sq_nonneg _
      _ ≤ (k^k:ℕ)*(∑p∈s,‖weighted p‖^2)^k :=
        PrimePowerMomentWork.energy_bound s k (2*N) weighted (fun p hp => ⟨(hs p hp).1,(hs p hp).2.2⟩)
      _ ≤ energyBudget k N A := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (Finset.sum_nonneg (fun p hp => sq_nonneg _)) he k) (Nat.cast_nonneg _)
  have hnorm (t : ℝ) : ‖verticalDirichlet152 s coeff σ t^k‖ =
      ‖exponentialSum151 (Finset.Ioc (N^k) (2^k*N^k)) (coefficient s k weighted)
        (fun n => Real.log n) t‖ := by
    rw [norm_pow,verticalDirichlet_norm152 s coeff σ t (fun p hp => (hs p hp).1.pos),←norm_pow]
    exact congrArg norm (DirichletPowerSupport.expansion s N k weighted t hk
      (fun p hp => ⟨(hs p hp).2.1,(hs p hp).2.2⟩))
  have hset : levelSet (fun t => verticalDirichlet152 s coeff σ t^k) a T V =
      levelSet (exponentialSum151 (Finset.Ioc (N^k) (2^k*N^k)) (coefficient s k weighted)
        (fun n => Real.log n)) a T V := by
    ext t
    simp only [levelSet,Set.mem_inter_iff,Set.mem_ofPred_eq,hnorm]
  rw [hset]
  exact DyadicLevelParameters.measure_bound (N^k) k (coefficient s k weighted) a T
    (energyBudget k N A) V (one_le_pow₀ hN) hk hT (energyBudget_pos k N A hk hN hA) hV hbudget

theorem integral_bound (k : ℕ) (hk : 1≤k)
    (s : Finset ℕ) (N : ℕ) (coeff : ℕ→ℂ) (a T A σ U p μ : ℝ)
    (hN : 1≤N) (hT : 0<T) (hA : 0<A) (hσ : 1≤σ) (hU : 0≤U)
    (hp : 2≤p) (hp6 : p<6) (hμ : 0<μ)
    (hs : ∀q∈s,q.Prime ∧ N<q ∧ q≤2*N)
    (henergy : (∑q∈s,‖coeff q‖^2)≤A*N)
    (hcap : ∀t∈Icc a (a+T),‖verticalDirichlet152 s coeff σ t‖^k≤U)
    (hpower : U^(p-2)≤μ) :
    let Q := quadratic (N^k) k T (energyBudget k N A)
    let B := sextic (N^k) k T (energyBudget k N A)
    (∫t in Icc a (a+T),‖verticalDirichlet152 s coeff σ t‖^((k:ℝ)*p)) ≤
      (B/μ)^((p-2)/(6-p))*((k^k:ℕ)*A^k*
        (T/(N:ℝ)^k+4*(2:ℝ)^k*(1+k*Real.log (2*N)))) +
      bandCountBound (cutoff B μ p) U*(2:ℝ)^p*(Q*(2:ℝ)^(p-2)+1)*μ := by
  let F := fun t => verticalDirichlet152 s coeff σ t^k
  let Q := quadratic (N^k) k T (energyBudget k N A)
  let B := sextic (N^k) k T (energyBudget k N A)
  have he := energyBudget_pos k N A hk hN hA
  have hF : Continuous F := (NormalizedMeanSquare.continuous_vertical s coeff σ
    (fun q hq => (hs q hq).1.pos)).pow k
  have hQ : 0≤Q := quadratic_nonnegative _ _ _ _ hT.le he.le
  have hB : 0<B := sextic_positive _ _ _ _ (one_le_pow₀ hN) hk hT he
  have hc : ∀t∈Icc a (a+T),‖F t‖≤U := by simpa only [F,norm_pow] using hcap
  have hl : ∀w:ℝ,0<w → volume (levelSet F a T w)≤ENNReal.ofReal (Q/w^2+B/w^6) := by
    intro w hw
    exact measure_bound k hk s N coeff a T A σ w hN hT.le hA hσ hw hs henergy
  have hh := MomentThreshold.integral_bound F a T U p Q B μ hF hU hp hp6 hQ hB hμ hc hpower hl
  have hm := PrimePowerMomentWork.normalized_integral_bound s k N coeff a T A σ hN hT.le hσ
    (fun q hq => ⟨(hs q hq).1,(hs q hq).2.1.le,(hs q hq).2.2⟩) henergy
  have heq (t:ℝ) : ‖F t‖^p=‖verticalDirichlet152 s coeff σ t‖^((k:ℝ)*p) := by
    dsimp [F]
    rw [norm_pow,←Real.rpow_natCast_mul (norm_nonneg _)]
  have heq2 (t:ℝ) : ‖F t‖^2=‖verticalDirichlet152 s coeff σ t‖^(2*k) := by
    dsimp [F]
    rw [norm_pow,←pow_mul,Nat.mul_comm]
  simp only [heq,heq2] at hh
  exact hh.trans (add_le_add (mul_le_mul_of_nonneg_left hm (by positivity)) le_rfl)

/-- Positive exponent margin for the outer-prime eighth-moment route.
This arithmetic does not supply the needed pointwise prime cap. -/
theorem outer_prime_eighth_margin :
    (6*(1124/1250:ℝ)-21*(9/35))/5= -3/3125 := by norm_num

run_cmd do
  for decl in [``energyBudget_pos, ``measure_bound, ``integral_bound, ``outer_prime_eighth_margin] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end PrimePowerLargeValuesWork
