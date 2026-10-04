import OuterPairFourthWork
import OuterLocalizedGeometryWork
import PolynomialLogEnvelope

/-! The correlated pair fourth moment applies at the actual localized scales. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators
namespace OuterPairFourthScaleWork
open OuterActiveDyadicWork OuterSmoothSupportGeometryWork OuterSourceReindexWork
open OuterModeUnitCapWork

theorem scale_of_large_witness (X : ℝ) (n r N : ℕ) (hX : 1≤X)
    (hc : 4≤X^(1/500:ℝ)) (hn : X^(229/1000:ℝ)<(n:ℝ))
    (hnr : n<2*r) (hrN : r≤2*N) : X^(227/1000:ℝ)≤(N:ℝ) := by
  have hx : 0<X := by linarith
  have hh := mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hx.le (227/1000))
  rw [←Real.rpow_add hx] at hh
  norm_num at hh
  have hnrR : (n:ℝ)<2*r := by exact_mod_cast hnr
  have hrNR : (r:ℝ)≤2*N := by exact_mod_cast hrN
  linarith

theorem eventually_actual_pair_scales :
    ∀ᶠ X : ℝ in atTop, 2≤X ∧ ∀ (s : ℝ) (i j : ℕ)
      (r : LongerTupleEncoding.Representation), r∈localizedSource X s i j →
      ∀ Na Nb : ℕ, (drop r).2.1≤2*Na → (drop r).2.2≤2*Nb →
        X^(227/1000:ℝ)≤(Na:ℝ) ∧ X^(227/1000:ℝ)≤(Nb:ℝ) := by
  filter_upwards [eventually_ge_atTop (2:ℝ),
    PolynomialLogEnvelope.eventually_constant_bound 4 (1/500)
      (by norm_num) (by norm_num)] with X hX hc
  refine ⟨hX,?_⟩
  intro s i j r hr Na Nb hra hrb
  obtain ⟨q,hq,he⟩ := localized_witness X s i j r hr
  have hd := active_data X s i j q hq
  have hqa := OuterSmoothErrorSupportWork.ambient_data X hX q hd.1
  have hra' := OuterSmoothErrorSupportWork.ambient_data X hX r
    (localized_subset X s i j hr)
  have ht := hd.2.1
  rcases ht with ⟨_,_,_,_,_,hbL,haL,_,_⟩
  simp only [blockKey,Prod.mk.injEq] at he
  have ha := same_log2_ratio (drop q).2.1 (drop r).2.1
    hqa.2.2.2.2.2.1 hra'.2.2.2.2.2.1 he.2.2.1
  have hb := same_log2_ratio (drop q).2.2 (drop r).2.2
    hqa.2.2.2.2.2.2 hra'.2.2.2.2.2.2 he.2.2.2
  exact ⟨scale_of_large_witness X _ _ Na (by linarith) hc.2 haL ha.1 hra,
    scale_of_large_witness X _ _ Nb (by linarith) hc.2 hbL hb.1 hrb⟩

def pairConstant : ℝ := FourPrimeMomentWork.momentConstant/(227/1000:ℝ)^4

theorem eventually_fourth :
    ∀ᶠ X : ℝ in atTop, 1<X ∧ ∀ (Na Nb : ℕ),
      X^(227/1000:ℝ)≤(Na:ℝ) → X^(227/1000:ℝ)≤(Nb:ℝ) →
      ∀ (A B : Finset ℕ) (q : ℕ→ℕ→ℂ) (a T σ u v : ℝ),
        0≤T → T≤X^(1124/1250:ℝ) → 1≤σ →
        (∀p∈A,p.Prime ∧ Na≤p ∧ p≤2*Na) →
        (∀p∈B,p.Prime ∧ Nb≤p ∧ p≤2*Nb) →
        (∀p∈A,∀r∈B,‖q p r‖≤1) →
        (∫t in Icc a (a+T),‖pairPolynomial A B q σ (t-u) (t-v)‖^4)≤
          pairConstant/(Real.log X)^4 := by
  obtain ⟨W,hW,hm⟩ := OuterPairFourthWork.eventual_fourth_bound
  filter_upwards [eventually_gt_atTop (1:ℝ),
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<227/1000)).eventually
      (eventually_ge_atTop W)] with X hX hWX
  refine ⟨hX,?_⟩
  intro Na Nb hNa hNb A B q a T σ u v hT hTX hσ hA hB hq
  have hx : 0<X := by linarith
  have hlog (N : ℕ) (hN : X^(227/1000:ℝ)≤(N:ℝ)) :
      (227/1000:ℝ)*Real.log X≤Real.log N := by
    have hh := Real.log_le_log (Real.rpow_pos_of_pos hx _) hN
    rwa [Real.log_rpow hx] at hh
  have hprod : X^(227/500:ℝ)≤(Na:ℝ)*Nb := by
    have hh := mul_le_mul hNa hNb (Real.rpow_nonneg hx.le _)
      ((Real.rpow_nonneg hx.le _).trans hNa)
    rw [←Real.rpow_add hx] at hh
    norm_num at hh
    exact hh
  have hlen : T≤(16*(Na*Nb)^2:ℕ) := by
    have hh := pow_le_pow_left₀ (Real.rpow_nonneg hx.le _) hprod 2
    rw [←Real.rpow_mul_natCast hx.le] at hh
    norm_num at hh
    have he : X^(1124/1250:ℝ)≤X^(227/250:ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hX.le (by norm_num)
    push_cast
    nlinarith [hTX.trans (he.trans hh),sq_nonneg ((Na:ℝ)*Nb)]
  have hh := hm Na Nb (hWX.trans hNa) (hWX.trans hNb) A B q a T σ
    ((227/1000:ℝ)*Real.log X) u v hT hσ
    (mul_pos (by norm_num) (Real.log_pos hX)) (hlog Na hNa) (hlog Nb hNb)
    hlen hA hB hq
  apply hh.trans_eq
  rw [mul_pow]
  unfold pairConstant
  ring

run_cmd do
  for decl in [``scale_of_large_witness, ``eventually_actual_pair_scales,
      ``eventually_fourth] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end OuterPairFourthScaleWork
