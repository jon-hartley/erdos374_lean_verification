import MaskedFourPrimeMeanWork
import MaskedPrimeWindowTransferWork

/-! Full-height local estimates when the total tuple product is near X. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators ComplexConjugate
namespace MaskedPrimeFullHeightWork
open MaskedPrimeTupleMeanWork DirichletPowerCoefficients
open Erdos374.HarmanAnalytic151MeanSquare
 theorem block_bound_four (k : ℕ) (P : Fin k → Finset ℕ) (N : Fin k → ℕ)
    (S : Finset (Fin k → ℕ)) (w : (Fin k → ℕ) → ℂ) (a T σ B : ℝ)
    (hN : ∀ i, 1 ≤ N i) (hT : 0 ≤ T) (hσ : 1 ≤ σ) (hB : 0 ≤ B)
    (hTL : T ≤ 4*(∏ i, (2*N i) : ℕ))
    (hP : ∀ i, ∀ p ∈ P i, Nat.Prime p ∧ N i ≤ p ∧ p ≤ 2*N i)
    (hcard : ∀ i, ((P i).card : ℝ) ≤ B*N i)
    (hS : S ⊆ Fintype.piFinset P) (hw : ∀ f ∈ S, ‖w f‖ ≤ 1) :
    (∫ t in Icc a (a+T),
      ‖∑ f ∈ S, (w f / (((productIndex f : ℝ)^σ : ℝ) : ℂ)) *
        exponentialKernel151 (Real.log (productIndex f)) t‖^2) ≤
      4 * GaussianMeanSquareWork.meanSquareConstant * (2 : ℝ)^k * (k^k : ℕ) * B^k := by
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
  have hmax : max T (L : ℝ) ≤ 4*(L : ℝ) := max_le hTL (by nlinarith [show (0:ℝ)≤L from Nat.cast_nonneg L])
  have hfactor : GaussianMeanSquareWork.meanSquareConstant * max T (L : ℝ) *
      (k^k : ℕ) * (S.card : ℝ) / (M : ℝ)^2 ≤
      GaussianMeanSquareWork.meanSquareConstant * (4*(L : ℝ)) *
      (k^k : ℕ) * (S.card : ℝ) / (M : ℝ)^2 := by
    gcongr
    exact GaussianMeanSquareWork.meanSquareConstant_pos.le
  have hh := hh.trans hfactor
  rw [hlen] at hh
  apply hh.trans
  calc
    _ ≤ (GaussianMeanSquareWork.meanSquareConstant * (4*((2 : ℝ)^k * M)) *
        (k^k : ℕ)) * (B^k * M) / (M : ℝ)^2 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hc (by
        exact mul_nonneg (mul_nonneg GaussianMeanSquareWork.meanSquareConstant_pos.le
          (by positivity)) (Nat.cast_nonneg _))) (sq_nonneg _)
    _ = _ := by field_simp


theorem eventually_full_height :
    ∀ᶠ X : ℝ in atTop, 1<X ∧ ∀ (N : Fin 4 → ℕ),
      (∀ i, X^(57/250 : ℝ)≤(N i : ℝ)) →
      ∀ (P : Fin 4 → Finset ℕ) (S : Finset (Fin 4 → ℕ))
        (w : (Fin 4 → ℕ) → ℂ) (a T σ : ℝ),
        0≤T → T≤2*X → 1≤σ →
        (∀ i, ∀ p∈P i, Nat.Prime p ∧ N i≤p ∧ p≤2*N i) →
        S⊆Fintype.piFinset P → (∀ f∈S, ‖w f‖≤1) →
        (∀ f∈S, X/2≤(productIndex f : ℝ)) →
        (∫ t in Icc a (a+T), ‖MaskedPrimeWindowTransferWork.polynomial S w σ t‖^2) ≤
          4*FourPrimeMomentWork.point101Constant/(Real.log X)^4 := by
  obtain ⟨W,hW,hcount⟩ := MaskedFourPrimeMeanWork.eventual_prime_block_card
  have hlarge := (tendsto_rpow_atTop (by norm_num : (0:ℝ)<57/250)).eventually
    (eventually_ge_atTop W)
  filter_upwards [hlarge,eventually_gt_atTop (1:ℝ)] with X hlarge hX
  refine ⟨hX,?_⟩
  intro N hN P S w a T σ hT hTX hσ hP hS hw hprod
  have hX0 : 0<X := by linarith
  have hlogX : 0<Real.log X := Real.log_pos hX
  have hNW (i : Fin 4) : W≤(N i : ℝ) := hlarge.trans (hN i)
  have hNi (i : Fin 4) : 1≤N i := by
    have hh := hW.trans (hNW i)
    exact_mod_cast (show (1:ℝ)≤N i by linarith)
  have hell : 0<(57/250 : ℝ)*Real.log X := mul_pos (by norm_num) hlogX
  have hlog (i : Fin 4) : (57/250 : ℝ)*Real.log X≤Real.log (N i) := by
    have hh := Real.log_le_log (Real.rpow_pos_of_pos hX0 _) (hN i)
    rwa [Real.log_rpow hX0] at hh
  by_cases hne : S.Nonempty
  · obtain ⟨f,hf⟩ := hne
    have hfP := Fintype.mem_piFinset.mp (hS hf)
    have hupper : productIndex f≤∏ i,2*N i :=
      Finset.prod_le_prod (fun i _ => (hP i _ (hfP i)).2.2)
    have hTL : T≤4*(∏ i,2*N i : ℕ) := by
      have hh : (productIndex f : ℝ)≤(∏ i,2*N i : ℕ) := by exact_mod_cast hupper
      linarith [hprod f hf]
    have hcard (i : Fin 4) : ((P i).card : ℝ)≤(4/((57/250 : ℝ)*Real.log X))*N i := by
      apply (hcount (N i) (hNW i) (P i) (hP i)).trans
      calc
        _ ≤ 4*(N i : ℝ)/((57/250 : ℝ)*Real.log X) :=
          div_le_div_of_nonneg_left (by positivity) hell (hlog i)
        _ = _ := by ring
    have hh := block_bound_four 4 P N S (fun f => conj (w f)) a T σ
      (4/((57/250 : ℝ)*Real.log X)) hNi hT hσ (by positivity) hTL hP hcard hS
      (by simpa only [RCLike.norm_conj] using hw)
    simp_rw [← MaskedPrimeWindowTransferWork.polynomial_norm S w] at hh
    apply hh.trans_eq
    unfold FourPrimeMomentWork.point101Constant FourPrimeMomentWork.momentConstant
    ring
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    simp only [MaskedPrimeWindowTransferWork.polynomial, Finset.sum_empty, norm_zero,
      zero_pow (by omega : 2≠0), integral_zero]
    exact div_nonneg (mul_nonneg (by norm_num)
      (div_nonneg FourPrimeMomentWork.momentConstant_pos.le (by positivity))) (by positivity)

open MaskedPrimeWindowTransferWork GaussianMellinTransferWork

def windowConstant : ℝ :=
  64 * transferConstant * FourPrimeMomentWork.point101Constant

theorem eventually_window_square :
    ∀ᶠ X : ℝ in atTop, Real.exp 1≤X ∧ ∀ (N : Fin 4 → ℕ),
      (∀ i, X^(57/250 : ℝ)≤(N i : ℝ)) →
      ∀ (P : Fin 4 → Finset ℕ) (S : Finset (Fin 4 → ℕ))
        (w : (Fin 4 → ℕ) → ℂ) (Y ε a T : ℝ),
        0≤Y → Y<X → ε∈Ioo 0 1 → 0≤T → T≤2*X →
        (∀ i, ∀ p∈P i, Nat.Prime p ∧ N i≤p ∧ p≤2*N i) →
        S⊆Fintype.piFinset P → (∀ f∈S, ‖w f‖≤1) → (∀ f∈S, X/2≤(productIndex f : ℝ)) →
        (1/X)*(∫ x in Icc X (2*X), ‖window X Y ε a T S w x‖^2) ≤
          windowConstant * Y^2/(Real.log X)^4 := by
  filter_upwards [eventually_full_height,
    eventually_ge_atTop (Real.exp 1)] with X hm hX
  refine ⟨hX,?_⟩
  intro N hN P S w Y ε a T hY hYX hε hT hTX hP hS hw hprod
  have hσ : 1≤1+1/Real.log X := by
    have : 0<Real.log X := Real.log_pos hm.1
    have : 0≤1/Real.log X := by positivity
    linarith
  have he := hm.2 N hN P S w a T (1+1/Real.log X) hT hTX hσ hP hS hw hprod
  have ht := smoothed_window_bound MellinSmoothingFunction.smoothing
    MellinSmoothingFunction.differentiable MellinSmoothingFunction.support
    MellinSmoothingFunction.nonnegative MellinSmoothingFunction.mass_one
    X Y ε a (a+T) hX hY hYX hε (polynomial S w (1+1/Real.log X))
    (polynomial_continuous S w _)
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
        0<Y → Y<X → ε∈Ioo 0 1 → 0≤T → T≤2*X →
        (∀ i, ∀ p∈P i, Nat.Prime p ∧ N i≤p ∧ p≤2*N i) →
        S⊆Fintype.piFinset P → (∀ f∈S, ‖w f‖≤1) → (∀ f∈S, X/2≤(productIndex f : ℝ)) →
        (1/X)*(∫ x in Icc X (2*X), ‖window X Y ε a T S w x‖) ≤
          Real.sqrt windowConstant * Y/(Real.log X)^2 := by
  filter_upwards [eventually_window_square, eventually_gt_atTop (1:ℝ)] with X hm hX
  refine ⟨hm.1,?_⟩
  intro N hN P S w Y ε a T hY hYX hε hT hTX hP hS hw hprod
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
  have hsq := hm.2 N hN P S w Y ε a T hY.le hYX hε hT hTX hP hS hw hprod
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

#print axioms block_bound_four
run_cmd do
  for decl in [``block_bound_four, ``eventually_full_height, ``eventually_window_square,
      ``windowConstant_pos, ``eventually_window_first_mean] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end MaskedPrimeFullHeightWork
