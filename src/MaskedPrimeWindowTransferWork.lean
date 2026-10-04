import MaskedFourPrimeMeanWork
import GaussianMellinTransferWork
import MellinSmoothingFunction
import SmoothedWindowRegularity
import TripleFirstMean

/-! The lossless local smoothed-window square mean for a fixed arbitrary
prime-tuple mask. Identifying sharp counts and summing blocks are separate. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators ComplexConjugate
namespace MaskedPrimeWindowTransferWork
open DirichletPowerCoefficients Erdos374.HarmanAnalytic151MeanSquare
open Erdos374.HarmanGram152 GaussianMellinTransferWork

def polynomial (S : Finset (Fin 4 → ℕ)) (w : (Fin 4 → ℕ) → ℂ) (σ t : ℝ) : ℂ :=
  ∑ f ∈ S, (w f / (((productIndex f : ℝ)^σ : ℝ) : ℂ)) *
    exponentialKernel151 (Real.log (productIndex f)) (-t)

theorem polynomial_eq_cpow (S : Finset (Fin 4 → ℕ)) (w : (Fin 4 → ℕ) → ℂ)
    (σ t : ℝ) (hS : ∀ f ∈ S, 0<productIndex f) :
    polynomial S w σ t = ∑ f ∈ S, w f * (productIndex f : ℂ)^(-((σ : ℂ)+Complex.I*t)) := by
  apply Finset.sum_congr rfl
  intro f hf
  rw [cpow_vertical_factor152 (hS f hf)]
  ring

theorem polynomial_continuous (S : Finset (Fin 4 → ℕ)) (w : (Fin 4 → ℕ) → ℂ) (σ : ℝ) :
    Continuous (polynomial S w σ) := by
  unfold polynomial exponentialKernel151
  fun_prop

theorem polynomial_norm (S : Finset (Fin 4 → ℕ)) (w : (Fin 4 → ℕ) → ℂ) (σ t : ℝ) :
    ‖polynomial S w σ t‖ =
      ‖∑ f ∈ S, (conj (w f) / (((productIndex f : ℝ)^σ : ℝ) : ℂ)) *
        exponentialKernel151 (Real.log (productIndex f)) t‖ := by
  have he : conj (∑ f ∈ S, (conj (w f) / (((productIndex f : ℝ)^σ : ℝ) : ℂ)) *
        exponentialKernel151 (Real.log (productIndex f)) t) = polynomial S w σ t := by
    simp only [map_sum, map_mul, map_div₀, starRingEnd_self_apply,
      Complex.conj_ofReal, conj_kernel152, polynomial]
  rw [← he, RCLike.norm_conj]

def window (X Y ε a T : ℝ) (S : Finset (Fin 4 → ℕ)) (w : (Fin 4 → ℕ) → ℂ)
    (x : ℝ) : ℂ :=
  SmoothedWindowTransfer.transform (polynomial S w (1+1/Real.log X))
    MellinSmoothingFunction.smoothing ε a (a+T) (1+1/Real.log X) (Y/X) x

def windowConstant : ℝ :=
  16 * transferConstant * FourPrimeMomentWork.point101Constant

theorem eventually_window_square :
    ∀ᶠ X : ℝ in atTop, Real.exp 1≤X ∧ ∀ (N : Fin 4 → ℕ),
      (∀ i, X^(57/250 : ℝ)≤(N i : ℝ)) →
      ∀ (P : Fin 4 → Finset ℕ) (S : Finset (Fin 4 → ℕ))
        (w : (Fin 4 → ℕ) → ℂ) (Y ε a T : ℝ),
        0≤Y → Y<X → ε∈Ioo 0 1 → 0≤T → T≤X^(1124/1250 : ℝ) →
        (∀ i, ∀ p∈P i, Nat.Prime p ∧ N i≤p ∧ p≤2*N i) →
        S⊆Fintype.piFinset P → (∀ f∈S, ‖w f‖≤1) →
        (1/X)*(∫ x in Icc X (2*X), ‖window X Y ε a T S w x‖^2) ≤
          windowConstant * Y^2/(Real.log X)^4 := by
  filter_upwards [MaskedFourPrimeMeanWork.eventually_point101,
    eventually_ge_atTop (Real.exp 1)] with X hm hX
  refine ⟨hX,?_⟩
  intro N hN P S w Y ε a T hY hYX hε hT hTX hP hS hw
  have hσ : 1≤1+1/Real.log X := by
    have : 0<Real.log X := Real.log_pos hm.1
    have : 0≤1/Real.log X := by positivity
    linarith
  have he := hm.2 N hN P S (fun f => conj (w f)) a T
    (1+1/Real.log X) hT hTX hσ hP hS (by simpa only [RCLike.norm_conj] using hw)
  have ht := smoothed_window_bound MellinSmoothingFunction.smoothing
    MellinSmoothingFunction.differentiable MellinSmoothingFunction.support
    MellinSmoothingFunction.nonnegative MellinSmoothingFunction.mass_one
    X Y ε a (a+T) hX hY hYX hε (polynomial S w (1+1/Real.log X))
    (polynomial_continuous S w _)
  simp_rw [← polynomial_norm S w] at he
  exact (ht.trans (mul_le_mul_of_nonneg_left he
    (mul_nonneg (mul_nonneg (by norm_num) transferConstant_pos.le) (sq_nonneg Y)))).trans_eq (by
      unfold windowConstant
      ring)

theorem windowConstant_pos : 0<windowConstant := by
  unfold windowConstant FourPrimeMomentWork.point101Constant
  exact mul_pos (mul_pos (by norm_num) transferConstant_pos)
    (div_pos FourPrimeMomentWork.momentConstant_pos (by positivity))

theorem eventually_window_first_mean :
    ∀ᶠ X : ℝ in atTop, Real.exp 1≤X ∧ ∀ (N : Fin 4 → ℕ),
      (∀ i, X^(57/250 : ℝ)≤(N i : ℝ)) →
      ∀ (P : Fin 4 → Finset ℕ) (S : Finset (Fin 4 → ℕ))
        (w : (Fin 4 → ℕ) → ℂ) (Y ε a T : ℝ),
        0<Y → Y<X → ε∈Ioo 0 1 → 0≤T → T≤X^(1124/1250 : ℝ) →
        (∀ i, ∀ p∈P i, Nat.Prime p ∧ N i≤p ∧ p≤2*N i) →
        S⊆Fintype.piFinset P → (∀ f∈S, ‖w f‖≤1) →
        (1/X)*(∫ x in Icc X (2*X), ‖window X Y ε a T S w x‖) ≤
          Real.sqrt windowConstant * Y/(Real.log X)^2 := by
  filter_upwards [eventually_window_square, eventually_gt_atTop (1:ℝ)] with X hm hX
  refine ⟨hm.1,?_⟩
  intro N hN P S w Y ε a T hY hYX hε hT hTX hP hS hw
  have hXp : 0<X := by linarith
  have hl : 0<Real.log X := Real.log_pos hX
  have hσ : 0<1+1/Real.log X := by positivity
  have hc : ContinuousOn (window X Y ε a T S w) (Ioi 0) :=
    SmoothedWindowRegularity.continuousOn_transform
      (polynomial S w (1+1/Real.log X)) MellinSmoothingFunction.smoothing
      ε a (a+T) (1+1/Real.log X) (Y/X) (polynomial_continuous S w _) hε hσ
      ((div_lt_one hXp).mpr hYX) MellinSmoothingFunction.differentiable
      MellinSmoothingFunction.nonnegative MellinSmoothingFunction.support
      MellinSmoothingFunction.mass_one
  have hc' := hc.mono (show Icc X (2*X)⊆Ioi 0 from fun x hx => hXp.trans_le hx.1)
  have hsq := hm.2 N hN P S w Y ε a T hY.le hYX hε hT hTX hP hS hw
  have hb : 0<Real.sqrt windowConstant * Y/(Real.log X)^2 := by
    exact div_pos (mul_pos (Real.sqrt_pos.mpr windowConstant_pos) hY) (sq_pos_of_pos hl)
  have he : (Real.sqrt windowConstant * Y/(Real.log X)^2)^2 =
      windowConstant * Y^2/(Real.log X)^4 := by
    rw [div_pow, mul_pow, Real.sq_sqrt windowConstant_pos.le]
    ring
  have hh := TripleFirstMean.absolute_mean_le (fun x => ‖window X Y ε a T S w x‖)
    X (Real.sqrt windowConstant * Y/(Real.log X)^2) hXp hb
    (hc'.norm.integrableOn_compact isCompact_Icc) ((hc'.norm.pow 2).integrableOn_compact isCompact_Icc) (by rwa [he])
  simpa only [abs_of_nonneg (norm_nonneg _)] using hh

#print axioms eventually_window_square
run_cmd do
  for decl in [``polynomial_eq_cpow, ``polynomial_continuous, ``polynomial_norm,
      ``eventually_window_square, ``windowConstant_pos, ``eventually_window_first_mean] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end MaskedPrimeWindowTransferWork
