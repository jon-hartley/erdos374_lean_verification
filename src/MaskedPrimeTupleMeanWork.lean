import PrimePowerMomentWork
import LongerTupleCollection

/-! Direct Gaussian mean squares for arbitrarily masked ordered prime tuples.
The weight may depend on the whole tuple. No separation of its coordinates
or Fourier expansion of its mask is required. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open MeasureTheory Set
open scoped BigOperators ComplexConjugate
attribute [local instance] Classical.propDecidable

namespace MaskedPrimeTupleMeanWork
open DirichletPowerCoefficients Erdos374.HarmanAnalytic151MeanSquare
open Erdos374.HarmanGram152

 theorem fiber_card_le (k : ℕ) (S : Finset (Fin k → ℕ))
    (hS : ∀ f ∈ S, ∀ i, Nat.Prime (f i)) (n : ℕ) :
    (S.filter (fun f => productIndex f = n)).card ≤ k^k := by
  let P := S.biUnion (fun f => Finset.univ.image f)
  have hp : ∀ p ∈ P, Nat.Prime p := by
    intro p hp
    obtain ⟨f,hf,hp⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hp
    exact hS f hf i
  apply le_trans (Finset.card_le_card (show
    S.filter (fun f => productIndex f=n) ⊆
      (tuples P k).filter (fun f => productIndex f=n) from ?_))
    (PrimePowerMomentWork.fiber_card_le P k n hp)
  intro f hf
  refine Finset.mem_filter.mpr ⟨?_, (Finset.mem_filter.mp hf).2⟩
  apply Fintype.mem_piFinset.mpr
  intro i
  exact Finset.mem_biUnion.mpr ⟨f,(Finset.mem_filter.mp hf).1,
    Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩

 theorem energy_bound (k : ℕ) (S : Finset (Fin k → ℕ)) (w : (Fin k → ℕ) → ℂ)
    (hS : ∀ f ∈ S, ∀ i, Nat.Prime (f i)) :
    (∑ n ∈ LongerTupleCollection.support S productIndex,
      ‖LongerTupleCollection.coefficient S productIndex w n‖^2) ≤
        (k^k : ℕ) * ∑ f ∈ S, ‖w f‖^2 := by
  calc
    _ ≤ ∑ n ∈ LongerTupleCollection.support S productIndex,
        (k^k : ℕ) * ∑ f ∈ S.filter (fun f => productIndex f=n), ‖w f‖^2 := by
      apply Finset.sum_le_sum
      intro n hn
      apply (Erdos374.ExponentialSum151.norm_sum_sq_le_card_energy _ w).trans
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast fiber_card_le k S hS n)
        (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    _ = _ := by
      rw [← Finset.mul_sum, Finset.sum_fiberwise_of_maps_to]
      intro f hf
      exact Finset.mem_image.mpr ⟨f,hf,rfl⟩

 theorem integral_bound (k : ℕ) (S : Finset (Fin k → ℕ)) (w : (Fin k → ℕ) → ℂ)
    (L : ℕ) (a T : ℝ) (hL : 1 ≤ L) (hT : 0 ≤ T)
    (hS : ∀ f ∈ S, (∀ i, Nat.Prime (f i)) ∧ productIndex f ≤ L) :
    (∫ t in Icc a (a+T),
      ‖∑ f ∈ S, w f * exponentialKernel151 (Real.log (productIndex f)) t‖^2) ≤
        GaussianMeanSquareWork.meanSquareConstant * max T (L : ℝ) *
          (k^k : ℕ) * ∑ f ∈ S, ‖w f‖^2 := by
  have hh := GaussianMeanSquareWork.dirichlet_mean_square_max
    (LongerTupleCollection.support S productIndex)
    (LongerTupleCollection.coefficient S productIndex w) L a T hL hT (by
      intro n hn
      obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp hn
      refine ⟨?_,(hS f hf).2⟩
      exact Finset.prod_pos (fun i _ => (hS f hf).1 i |>.pos))
  have he (t : ℝ) : exponentialSum151 (LongerTupleCollection.support S productIndex)
      (LongerTupleCollection.coefficient S productIndex w) (fun n => Real.log n) t =
      ∑ f ∈ S, w f * exponentialKernel151 (Real.log (productIndex f)) t :=
    LongerTupleCollection.grouped_sum S productIndex w _
  simp_rw [he] at hh
  exact (hh.trans (mul_le_mul_of_nonneg_left
    (energy_bound k S w (fun f hf => (hS f hf).1))
    (mul_nonneg GaussianMeanSquareWork.meanSquareConstant_pos.le
      (le_trans hT (le_max_left _ _))))).trans_eq (by ring)

/-- Arbitrary correlated unit weights cost only the prime collision constant.
The normalized coefficients are taken at the complete product. -/
 theorem normalized_integral_bound (k : ℕ) (S : Finset (Fin k → ℕ))
    (w : (Fin k → ℕ) → ℂ) (M L : ℕ) (a T σ : ℝ)
    (hM : 1 ≤ M) (hL : 1 ≤ L) (hT : 0 ≤ T) (hσ : 1 ≤ σ)
    (hS : ∀ f ∈ S, (∀ i, Nat.Prime (f i)) ∧ M ≤ productIndex f ∧ productIndex f ≤ L)
    (hw : ∀ f ∈ S, ‖w f‖ ≤ 1) :
    (∫ t in Icc a (a+T),
      ‖∑ f ∈ S, (w f / (((productIndex f : ℝ)^σ : ℝ) : ℂ)) *
        exponentialKernel151 (Real.log (productIndex f)) t‖^2) ≤
      GaussianMeanSquareWork.meanSquareConstant * max T (L : ℝ) *
        (k^k : ℕ) * (S.card : ℝ) / (M : ℝ)^2 := by
  have hMp : (0 : ℝ) < M := by exact_mod_cast (show 0<M by omega)
  have he : (∑ f ∈ S, ‖w f / (((productIndex f : ℝ)^σ : ℝ) : ℂ)‖^2) ≤
      (S.card : ℝ)/(M : ℝ)^2 := by
    calc
      _ ≤ ∑ _f ∈ S, 1/(M : ℝ)^2 := by
        apply Finset.sum_le_sum
        intro f hf
        have hm : (M : ℝ) ≤ productIndex f := by exact_mod_cast (hS f hf).2.1
        have hn : (1 : ℝ) ≤ productIndex f := (by exact_mod_cast hM : (1:ℝ)≤M).trans hm
        have hr : (M : ℝ) ≤ (productIndex f : ℝ)^σ := hm.trans (by
          simpa using Real.rpow_le_rpow_of_exponent_le hn hσ)
        have hrp : 0 < (productIndex f : ℝ)^σ := hMp.trans_le hr
        have hh : ‖w f / (((productIndex f : ℝ)^σ : ℝ) : ℂ)‖ ≤ 1/(M : ℝ) := by
          rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrp]
          exact (div_le_div_of_nonneg_right (hw f hf) hrp.le).trans
            (one_div_le_one_div_of_le hMp hr)
        simpa [div_pow] using pow_le_pow_left₀ (norm_nonneg _) hh 2
      _ = _ := by simp [div_eq_mul_inv]
  exact ((integral_bound k S (fun f => w f / (((productIndex f : ℝ)^σ : ℝ) : ℂ))
    L a T hL hT (fun f hf => ⟨(hS f hf).1,(hS f hf).2.2⟩)).trans
      (mul_le_mul_of_nonneg_left he (mul_nonneg
        (mul_nonneg GaussianMeanSquareWork.meanSquareConstant_pos.le
          (le_trans hT (le_max_left _ _))) (Nat.cast_nonneg _)))).trans_eq (by ring)

/-- A local block estimate with no cost for an arbitrary tuple mask. -/
 theorem block_bound (k : ℕ) (P : Fin k → Finset ℕ) (N : Fin k → ℕ)
    (S : Finset (Fin k → ℕ)) (w : (Fin k → ℕ) → ℂ) (a T σ B : ℝ)
    (hN : ∀ i, 1 ≤ N i) (hT : 0 ≤ T) (hσ : 1 ≤ σ) (hB : 0 ≤ B)
    (hTL : T ≤ (∏ i, (2*N i) : ℕ))
    (hP : ∀ i, ∀ p ∈ P i, Nat.Prime p ∧ N i ≤ p ∧ p ≤ 2*N i)
    (hcard : ∀ i, ((P i).card : ℝ) ≤ B*N i)
    (hS : S ⊆ Fintype.piFinset P) (hw : ∀ f ∈ S, ‖w f‖ ≤ 1) :
    (∫ t in Icc a (a+T),
      ‖∑ f ∈ S, (w f / (((productIndex f : ℝ)^σ : ℝ) : ℂ)) *
        exponentialKernel151 (Real.log (productIndex f)) t‖^2) ≤
      GaussianMeanSquareWork.meanSquareConstant * (2 : ℝ)^k * (k^k : ℕ) * B^k := by
  let M : ℕ := ∏ i, N i
  let L : ℕ := ∏ i, 2*N i
  have hM : 1 ≤ M := Finset.one_le_prod (fun i _ => hN i)
  have hL : 1 ≤ L := Finset.one_le_prod (fun i _ => by have := hN i; omega)
  have hMp : (0 : ℝ) < M := by exact_mod_cast (show 0<M by omega)
  have hlen : (L : ℝ) = (2 : ℝ)^k * M := by
    simp [L, M, Finset.prod_mul_distrib]
  have hc : (S.card : ℝ) ≤ B^k * M := by
    calc
      _ ≤ ((Fintype.piFinset P).card : ℝ) := by exact_mod_cast Finset.card_le_card hS
      _ = ∏ i, ((P i).card : ℝ) := by simp
      _ ≤ ∏ i, B*(N i : ℝ) := Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _)
        (fun i _ => hcard i)
      _ = _ := by simp [Finset.prod_mul_distrib, M]
  have hh := normalized_integral_bound k S w M L a T σ hM hL hT hσ (by
    intro f hf
    have hfP := Fintype.mem_piFinset.mp (hS hf)
    refine ⟨fun i => (hP i (f i) (hfP i)).1, ?_, ?_⟩
    · exact Finset.prod_le_prod (fun i _ => (hP i (f i) (hfP i)).2.1)
    · exact Finset.prod_le_prod (fun i _ => (hP i (f i) (hfP i)).2.2)) hw
  rw [max_eq_right hTL, hlen] at hh
  apply hh.trans
  calc
    _ ≤ (GaussianMeanSquareWork.meanSquareConstant * ((2 : ℝ)^k * M) *
        (k^k : ℕ)) * (B^k * M) / (M : ℝ)^2 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hc (by
        exact mul_nonneg (mul_nonneg GaussianMeanSquareWork.meanSquareConstant_pos.le
          (by positivity)) (Nat.cast_nonneg _))) (sq_nonneg _)
    _ = _ := by field_simp

#print axioms normalized_integral_bound
run_cmd do
  for decl in [``fiber_card_le, ``energy_bound, ``integral_bound, ``normalized_integral_bound, ``block_bound] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end MaskedPrimeTupleMeanWork
