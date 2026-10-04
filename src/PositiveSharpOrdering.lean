import PositiveInteriorOrdering
import PositiveInteriorModelClosed

/-! Actual dyadic/product-window coordinates imply the strict ordering and
cubic cutoff inequalities. No primality, counting asymptotic, or discrepancy
estimate is assumed or concluded. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open Real
namespace PositiveSharpOrdering
open PositiveInteriorModel PositiveInteriorCells PositiveInteriorOrdering

theorem scale_pos (m : ℕ) : 0 < scale m := by unfold scale; positivity

theorem dyadic_log_bounds (X p : ℝ) (m : ℕ) (hX : 1 < X)
    (hp : scale m < p ∧ p ≤ 2*scale m) :
    (m:ℝ)*mesh X ≤ log p/log X ∧
      log p/log X ≤ (m:ℝ)*mesh X+mesh X := by
  have hL := log_pos hX
  have hp0 : 0 < p := (scale_pos m).trans hp.1
  have hlo := log_le_log (scale_pos m) hp.1.le
  have hhi := log_le_log hp0 hp.2
  rw [log_scale_identity X hX m] at hlo
  rw [log_mul (by norm_num) (scale_pos m).ne', log_scale_identity X hX m] at hhi
  have hm := mesh_mul_log X hX
  exact ⟨(le_div_iff₀ hL).mpr hlo, (div_le_iff₀ hL).mpr (by nlinarith)⟩

theorem product_log_bounds (X p r q : ℝ) (hX : 1 < X)
    (hp : 0 < p) (hr : 0 < r) (hq : 0 < q)
    (hw : X/2 < p*r*q ∧ p*r*q ≤ 2*X) :
    1-mesh X ≤ (log p+log r+log q)/log X ∧
      (log p+log r+log q)/log X ≤ 1+mesh X := by
  have hX0 : 0 < X := by linarith
  have hL := log_pos hX
  have hlo := log_le_log (by positivity : 0 < X/2) hw.1.le
  have hhi := log_le_log (mul_pos (mul_pos hp hr) hq) hw.2
  rw [log_div hX0.ne' (by norm_num),
    log_mul (mul_pos hp hr).ne' hq.ne', log_mul hp.ne' hr.ne'] at hlo
  rw [log_mul (mul_pos hp hr).ne' hq.ne', log_mul hp.ne' hr.ne',
    log_mul (by norm_num) hX0.ne'] at hhi
  have hm := mesh_mul_log X hX
  exact ⟨(le_div_iff₀ hL).mpr (by nlinarith),
    (div_le_iff₀ hL).mpr (by nlinarith)⟩

theorem window_product_bounds (X x y p r q : ℝ)
    (hx : X ≤ x ∧ x ≤ 2*X) (hy : y ≤ X/2)
    (hw : x-y < p*r*q ∧ p*r*q ≤ x) :
    X/2 < p*r*q ∧ p*r*q ≤ 2*X := by
  constructor <;> linarith

theorem actual_ordering (X x y s : ℝ) (j : ℕ × ℕ) (p r q : ℕ)
    (hX : 1 < X) (hx : X ≤ x ∧ x ≤ 2*X) (hy : 0 < y ∧ y ≤ X/2)
    (hj : j ∈ boxes (mesh X)) (hmesh : mesh X ≤ 1/3200) (hs : 0 ≤ s)
    (hp : scale j.1 < (p:ℝ) ∧ (p:ℝ) ≤ 2*scale j.1)
    (hr : scale j.2 < (r:ℝ) ∧ (r:ℝ) ≤ 2*scale j.2)
    (hw : x-y < (p:ℝ)*(r:ℝ)*(q:ℝ) ∧ (p:ℝ)*(r:ℝ)*(q:ℝ) ≤ x) :
    X^(9/35:ℝ) < (p:ℝ) ∧ (p:ℝ) < sqrt X ∧ q < p ∧ q < r ∧
      (X^(1-3*s)/(p:ℝ))^(1/3:ℝ) < (q:ℝ) := by
  have hX0 : 0 < X := by linarith
  have hL := log_pos hX
  have hp0 : 0 < (p:ℝ) := (scale_pos j.1).trans hp.1
  have hr0 : 0 < (r:ℝ) := (scale_pos j.2).trans hr.1
  have hprod := window_product_bounds X x y p r q hx hy.2 hw
  have hq0 : 0 < (q:ℝ) := by
    by_contra hn
    have he : q=0 := by
      exact_mod_cast le_antisymm (le_of_not_gt hn) (Nat.cast_nonneg q : (0:ℝ) ≤ q)
    simp only [he, Nat.cast_zero, mul_zero] at hprod
    linarith [hprod.1]
  have hpLog := dyadic_log_bounds X p j.1 hX hp
  have hrLog := dyadic_log_bounds X r j.2 hX hr
  have htLog := product_log_bounds X p r q hX hp0 hr0 hq0 hprod
  have hi := box_interior (mesh X) (mesh_pos X hX) j hj
  have hc : -mesh X ≤ log (p:ℝ)/log X+log (r:ℝ)/log X+log (q:ℝ)/log X-1 ∧
      log (p:ℝ)/log X+log (r:ℝ)/log X+log (q:ℝ)/log X-1 ≤ mesh X := by
    rw [add_div, add_div] at htLog
    constructor <;> linarith
  have ho := dyadic_level_order ((j.1:ℝ)*mesh X) ((j.2:ℝ)*mesh X)
    (log (p:ℝ)/log X-(j.1:ℝ)*mesh X)
    (log (r:ℝ)/log X-(j.2:ℝ)*mesh X)
    (log (p:ℝ)/log X+log (r:ℝ)/log X+log (q:ℝ)/log X-1)
    (mesh X) s hi hmesh (by constructor <;> linarith [hpLog.1,hpLog.2])
    (by constructor <;> linarith [hrLog.1,hrLog.2]) hc hs
  dsimp only [third] at ho
  have hqp : log (q:ℝ)/log X < log (p:ℝ)/log X := by linarith [ho.1]
  have hqr : log (q:ℝ)/log X < log (r:ℝ)/log X := by linarith [ho.2.1]
  have hcube : (1-3*s-log (p:ℝ)/log X)/3 < log (q:ℝ)/log X := by
    linarith [ho.2.2.1]
  have hsq : log (p:ℝ)/log X < (1/2:ℝ) := by linarith [ho.2.2.2.1]
  have hpLower : (9/35:ℝ) < log (p:ℝ)/log X := by linarith [ho.2.2.2.2]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · apply (log_lt_log_iff (rpow_pos_of_pos hX0 _) hp0).mp
    rw [log_rpow hX0]
    exact (lt_div_iff₀ hL).mp hpLower
  · apply (log_lt_log_iff hp0 (sqrt_pos.2 hX0)).mp
    rw [log_sqrt hX0.le]
    have hh := (div_lt_iff₀ hL).mp hsq
    linarith
  · have hh := (log_lt_log_iff hq0 hp0).mp ((div_lt_div_iff_of_pos_right hL).mp hqp)
    exact_mod_cast hh
  · have hh := (log_lt_log_iff hq0 hr0).mp ((div_lt_div_iff_of_pos_right hL).mp hqr)
    exact_mod_cast hh
  · have hbase : 0 < X^(1-3*s)/(p:ℝ) := div_pos (rpow_pos_of_pos hX0 _) hp0
    apply (log_lt_log_iff (rpow_pos_of_pos hbase _) hq0).mp
    rw [log_rpow hbase, log_div (rpow_pos_of_pos hX0 _).ne' hp0.ne', log_rpow hX0]
    have hh := mul_lt_mul_of_pos_right hcube hL
    have hpCancel : (log (p:ℝ)/log X)*log X=log (p:ℝ) := div_mul_cancel₀ _ hL.ne'
    have hqCancel : (log (q:ℝ)/log X)*log X=log (q:ℝ) := div_mul_cancel₀ _ hL.ne'
    nlinarith

theorem actual_third_range (X x y : ℝ) (j : ℕ × ℕ) (p r q : ℕ)
    (_hX : 0 < X) (hx : X ≤ x ∧ x ≤ 2*X) (hy : y ≤ X/2)
    (hp : scale j.1 < (p:ℝ) ∧ (p:ℝ) ≤ 2*scale j.1)
    (hr : scale j.2 < (r:ℝ) ∧ (r:ℝ) ≤ 2*scale j.2)
    (hw : x-y < (p:ℝ)*(r:ℝ)*(q:ℝ) ∧ (p:ℝ)*(r:ℝ)*(q:ℝ) ≤ x) :
    thirdScale X j/8 < (q:ℝ) ∧ (q:ℝ) < 2*thirdScale X j := by
  have hP := scale_pos j.1
  have hR := scale_pos j.2
  have hp0 : 0 < (p:ℝ) := hP.trans hp.1
  have hr0 : 0 < (r:ℝ) := hR.trans hr.1
  have hprod := window_product_bounds X x y p r q hx hy hw
  have hq0 : 0 < (q:ℝ) := by
    by_contra hn
    have he : q=0 := by
      exact_mod_cast le_antisymm (le_of_not_gt hn) (Nat.cast_nonneg q : (0:ℝ) ≤ q)
    simp only [he, Nat.cast_zero, mul_zero] at hprod
    linarith [hprod.1, _hX]
  have hlo : scale j.1*scale j.2 < (p:ℝ)*(r:ℝ) :=
    mul_lt_mul hp.1 hr.1.le hR hp0.le
  have hhi : (p:ℝ)*(r:ℝ) ≤ (2*scale j.1)*(2*scale j.2) :=
    mul_le_mul hp.2 hr.2 hr0.le (by positivity)
  have hlq := mul_lt_mul_of_pos_right hlo hq0
  have hhq := mul_le_mul_of_nonneg_right hhi hq0.le
  unfold thirdScale
  constructor
  · rw [div_div]
    apply (div_lt_iff₀ (by positivity : 0 < scale j.1*scale j.2*8)).mpr
    nlinarith [hprod.1]
  · rw [← mul_div_assoc]
    apply (lt_div_iff₀ (mul_pos hP hR)).mpr
    nlinarith [hprod.2]

theorem actual_log_bounds (X x y : ℝ) (j : ℕ × ℕ) (p r q : ℕ)
    (hX : 0 < X) (hx : X ≤ x ∧ x ≤ 2*X) (hy : y ≤ X/2)
    (hp : scale j.1 < (p:ℝ) ∧ (p:ℝ) ≤ 2*scale j.1)
    (hr : scale j.2 < (r:ℝ) ∧ (r:ℝ) ≤ 2*scale j.2)
    (hw : x-y < (p:ℝ)*(r:ℝ)*(q:ℝ) ∧ (p:ℝ)*(r:ℝ)*(q:ℝ) ≤ x) :
    log (p:ℝ) ≤ log (2*scale j.1) ∧ log (r:ℝ) ≤ log (2*scale j.2) ∧
      log (q:ℝ) < log (8*thirdScale X j) := by
  have hL : 0 < thirdScale X j := div_pos hX (mul_pos (scale_pos j.1) (scale_pos j.2))
  have hq := actual_third_range X x y j p r q hX hx hy hp hr hw
  exact ⟨log_le_log ((scale_pos j.1).trans hp.1) hp.2,
    log_le_log ((scale_pos j.2).trans hr.1) hr.2,
    log_lt_log (by linarith [hq.1]) (by linarith [hq.2])⟩

theorem dyadic_unique (p : ℝ) (m n : ℕ)
    (hm : scale m < p ∧ p ≤ 2*scale m)
    (hn : scale n < p ∧ p ≤ 2*scale n) : m=n := by
  have hstep (a b : ℕ) (hab : a < b) : 2*scale a ≤ scale b := by
    unfold scale
    calc
      2*(2:ℝ)^a = (2:ℝ)^(a+1) := by rw [pow_succ]; ring
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) (Nat.succ_le_of_lt hab)
  rcases lt_trichotomy m n with h | h | h
  · have hh := hstep m n h
    linarith [hm.2,hn.1]
  · exact h
  · have hh := hstep n m h
    linarith [hn.2,hm.1]

theorem dyadic_pair_unique (p r : ℝ) (j k : ℕ × ℕ)
    (hjp : scale j.1 < p ∧ p ≤ 2*scale j.1)
    (hjr : scale j.2 < r ∧ r ≤ 2*scale j.2)
    (hkp : scale k.1 < p ∧ p ≤ 2*scale k.1)
    (hkr : scale k.2 < r ∧ r ≤ 2*scale k.2) : j=k := by
  exact Prod.ext (dyadic_unique p j.1 k.1 hjp hkp) (dyadic_unique r j.2 k.2 hjr hkr)

run_cmd do
  for decl in [``scale_pos, ``dyadic_log_bounds, ``product_log_bounds,
      ``window_product_bounds, ``actual_ordering, ``actual_third_range,
      ``actual_log_bounds, ``dyadic_unique, ``dyadic_pair_unique] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ACTUAL DYADIC PRODUCT-WINDOW ORDERING AND UNIQUENESS; NO COUNT ESTIMATE"
end PositiveSharpOrdering
end
