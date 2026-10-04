import PrimeTupleSharpApproximationWork
import MaskedPrimeFullHeightWork

/-! Local sharp prime-tuple counts, retaining the explicit Perron error.
The tuple set is fixed; all correlated source restrictions are allowed. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace PrimeTupleSharpMeanWork
open PrimeTupleSharpApproximationWork DirichletPowerCoefficients
open MaskedPrimeWindowTransferWork

theorem count_integrable (S : Finset (Fin 4 → ℕ)) (X δ : ℝ) :
    IntegrableOn (fun x => count S (x-x*δ) x) (Icc X (2*X)) := by
  have he (x : ℝ) : count S (x-x*δ) x =
      ∑ f∈S, if x-x*δ<(productIndex f : ℝ) ∧ (productIndex f : ℝ)≤x then (1:ℝ) else 0 := by
    simp only [count, Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter,
      Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  simp_rw [he]
  apply integrable_finsetSum
  intro f hf
  have hm : MeasurableSet {x : ℝ | x-x*δ<(productIndex f : ℝ) ∧ (productIndex f : ℝ)≤x} :=
    ((isOpen_lt (by fun_prop : Continuous (fun x : ℝ => x-x*δ))
      (continuous_const : Continuous (fun _ : ℝ => (productIndex f : ℝ)))).measurableSet).inter
      (isClosed_le (continuous_const : Continuous (fun _ : ℝ => (productIndex f : ℝ))) continuous_id).measurableSet
  have hi := ((continuous_const : Continuous (fun _ : ℝ => (1:ℝ))).integrableOn_Icc
    (μ := volume) (a := X) (b := 2*X)).indicator hm
  apply hi.congr
  apply Filter.Eventually.of_forall
  intro x
  simp only [Set.indicator_apply, Set.mem_setOf_eq]

theorem eventual_sharp_mean :
    ∀ᶠ X : ℝ in atTop, 1<X ∧ ∀ (N : Fin 4 → ℕ),
      (∀ i, X^(57/250 : ℝ)≤(N i : ℝ)) →
      ∀ (P : Fin 4 → Finset ℕ) (S : Finset (Fin 4 → ℕ)) (Y : ℝ),
        0<Y → Y≤X/2 →
        (∀ i, ∀ p∈P i, Nat.Prime p ∧ N i≤p ∧ p≤2*N i) →
        S⊆Fintype.piFinset P →
        (∀ f∈S, X/2≤(productIndex f : ℝ) ∧ (productIndex f : ℝ)≤2*X) →
        (1/X)*(∫ x in Icc X (2*X), count S (x-x*(Y/X)) x) ≤
          Real.sqrt MaskedPrimeFullHeightWork.windowConstant * Y/(Real.log X)^2 +
            2*X^(2/25 : ℝ) := by
  filter_upwards [PrimeTupleSharpApproximationWork.eventual_approximation,
    MaskedPrimeFullHeightWork.eventually_window_first_mean,
    eventually_gt_atTop (1:ℝ)] with X ha hm hX
  refine ⟨hX,?_⟩
  intro N hN P S Y hY hYX hP hS hprod
  have hXp : 0<X := by linarith
  have hYlt : Y<X := by linarith
  have hδ : Y/X∈Icc 0 (1/2) :=
    ⟨div_nonneg hY.le hXp.le,(div_le_iff₀ hXp).mpr (by linarith)⟩
  have hε : X^(-19/20 : ℝ)∈Ioo 0 1 :=
    ⟨Real.rpow_pos_of_pos hXp _,Real.rpow_lt_one_of_one_lt_of_neg hX (by norm_num)⟩
  let F := window X Y (X^(-19/20 : ℝ)) (-X) (2*X) S (fun _ => 1)
  have hc : ContinuousOn F (Ioi 0) :=
    SmoothedWindowRegularity.continuousOn_transform (polynomial S (fun _ => 1) (1+1/Real.log X))
      MellinSmoothingFunction.smoothing _ _ _ _ _ (polynomial_continuous S _ _) hε
      (by have := Real.log_pos hX; positivity) ((div_lt_one hXp).mpr hYlt)
      MellinSmoothingFunction.differentiable MellinSmoothingFunction.nonnegative
      MellinSmoothingFunction.support MellinSmoothingFunction.mass_one
  have hi : IntegrableOn (fun x => ‖F x‖) (Icc X (2*X)) :=
    (hc.norm.mono (fun x hx => hXp.trans_le hx.1)).integrableOn_compact isCompact_Icc
  have hb (x : ℝ) (hx : x∈Icc X (2*X)) :
      count S (x-x*(Y/X)) x ≤ ‖F x‖ + 2*X^(2/25 : ℝ) := by
    have happ := ha.2 S (by
      intro f hf
      exact ⟨fun i => (hP i _ (Fintype.mem_piFinset.mp (hS hf) i)).1,(hprod f hf).2⟩)
      x (Y/X) hx hδ
    have hend : -X+2*X=X := by ring
    change ‖(count S (x-x*(Y/X)) x : ℂ) - ((1/(2*Real.pi) : ℝ) : ℂ) *
      SmoothedWindowTransfer.transform _ _ _ _ _ _ _ x‖ ≤ _ at happ
    have heF : F x = SmoothedWindowTransfer.transform
        (polynomial S (fun _ => 1) (1+1/Real.log X)) MellinSmoothingFunction.smoothing
        (X^(-19/20 : ℝ)) (-X) X (1+1/Real.log X) (Y/X) x := by
      dsimp [F,window]
      rw [hend]
    rw [← heF] at happ
    have hnorm := norm_le_norm_sub_add ((count S (x-x*(Y/X)) x : ℝ) : ℂ)
      (((1/(2*Real.pi) : ℝ) : ℂ)*F x)
    have hn : 0≤count S (x-x*(Y/X)) x := Nat.cast_nonneg _
    have hpi : 0≤1/(2*Real.pi) := by positivity
    have hpi1 : 1/(2*Real.pi)≤1 := (div_le_one (by positivity)).mpr (by linarith [Real.pi_gt_three])
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hn,
      norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hpi] at hnorm
    have hh := mul_le_mul_of_nonneg_right hpi1 (norm_nonneg (F x))
    linarith
  have hiC : IntegrableOn (fun _ : ℝ => 2*X^(2/25 : ℝ)) (Icc X (2*X)) :=
    continuous_const.integrableOn_Icc
  have hint := setIntegral_mono_on (count_integrable S X (Y/X)) (hi.add hiC)
    measurableSet_Icc hb
  simp only [Pi.add_apply] at hint
  rw [integral_add hi hiC, setIntegral_const,
    Real.volume_real_Icc_of_le (by linarith : X≤2*X), smul_eq_mul] at hint
  have hmean := hm.2 N hN P S (fun _ => 1) Y (X^(-19/20 : ℝ)) (-X) (2*X)
    hY hYlt hε (by positivity) le_rfl hP hS (by simp) (fun f hf => (hprod f hf).1)
  have hh := mul_le_mul_of_nonneg_left hint (by positivity : 0≤1/X)
  have he : (1/X)*((∫ x in Icc X (2*X), ‖F x‖)+(2*X-X)*(2*X^(2/25 : ℝ))) =
      (1/X)*(∫ x in Icc X (2*X), ‖F x‖)+2*X^(2/25 : ℝ) := by field_simp; ring
  rw [he] at hh
  exact hh.trans (add_le_add hmean le_rfl)

theorem eventual_error_log (A : ℕ) :
    ∀ᶠ X : ℝ in atTop, 1<X ∧ 2*X^(2/25 : ℝ) ≤
      PositiveSharpPowerWindow.halfWidth X (101/1000)/(Real.log X)^A := by
  filter_upwards [PolynomialLogEnvelope.eventually_bound 4 A (21/1000) (by norm_num) (by norm_num),
    eventually_gt_atTop (1:ℝ)] with X hh hX
  refine ⟨hX,?_⟩
  have hXp : 0<X := by linarith
  have hl : 0<Real.log X := Real.log_pos hX
  have hlog : 4*(Real.log X)^A≤X^(21/1000 : ℝ) := by
    apply le_trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hl.le (by linarith : Real.log X≤1+Real.log X) A) (by norm_num)) hh.2
  have hp : X^(2/25 : ℝ)*X^(21/1000 : ℝ)=X^(101/1000 : ℝ) := by
    rw [← Real.rpow_add hXp]
    norm_num
  apply (le_div_iff₀ (pow_pos hl A)).mpr
  unfold PositiveSharpPowerWindow.halfWidth
  have he := mul_le_mul_of_nonneg_left hlog (Real.rpow_pos_of_pos hXp (2/25 : ℝ)).le
  rw [hp] at he
  nlinarith

theorem eventually_point101_sharp_mean :
    ∀ᶠ X : ℝ in atTop, 1<X ∧ ∀ (N : Fin 4 → ℕ),
      (∀ i, X^(57/250 : ℝ)≤(N i : ℝ)) →
      ∀ (P : Fin 4 → Finset ℕ) (S : Finset (Fin 4 → ℕ)),
        (∀ i, ∀ p∈P i, Nat.Prime p ∧ N i≤p ∧ p≤2*N i) →
        S⊆Fintype.piFinset P →
        (∀ f∈S, X/2≤(productIndex f : ℝ) ∧ (productIndex f : ℝ)≤2*X) →
        let Y := PositiveSharpPowerWindow.halfWidth X (101/1000)
        (1/X)*(∫ x in Icc X (2*X), count S (x-x*(Y/X)) x) ≤
          (Real.sqrt MaskedPrimeFullHeightWork.windowConstant+1)*Y/(Real.log X)^2 := by
  filter_upwards [eventual_sharp_mean, eventual_error_log 2,
    PositiveSharpPowerWindow.halfWidth_eventually (101/1000) (by norm_num)] with X hm he hY
  refine ⟨hm.1,?_⟩
  intro N hN P S hP hS hprod
  dsimp only
  have hh := hm.2 N hN P S (PositiveSharpPowerWindow.halfWidth X (101/1000))
    hY.1 (by linarith [hY.2,hm.1]) hP hS hprod
  exact (hh.trans (add_le_add le_rfl he.2)).trans_eq (by ring)

#print axioms eventual_sharp_mean
run_cmd do
  for decl in [``count_integrable, ``eventual_sharp_mean, ``eventual_error_log,
      ``eventually_point101_sharp_mean] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end PrimeTupleSharpMeanWork
