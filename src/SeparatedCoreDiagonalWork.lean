import SeparatedCoreCorrelationWork

/-! The diagonal of the complete signed physical correlation has a power
saving at the .101 window. Off-diagonal cancellation remains separate. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators
namespace SeparatedCoreDiagonalWork
open SeparatedCoreGlobalPerronWork LongPairSeparatedCoreWork
open MovingWindowCorrelationWork PositiveSharpPowerWindow

def diagonal (X s Y : ℝ) : ℝ := ∑ n∈physicalSupport X,
  (physicalCoefficient X s n)^2 * overlap X (Y/X) n n

theorem overlap_diagonal_le (X Y n : ℝ) (hX : 0<X) (hY : 0≤Y) (hYX : Y<X) :
    overlap X (Y/X) n n≤2*Y := by
  have hδ : 0≤Y/X := div_nonneg hY hX.le
  have hδ1 : Y/X<1 := (div_lt_one hX).mpr hYX
  have hu : min (2*X) (n/(1-Y/X))≤n/(1-Y/X) := min_le_right _ _
  have hh := (le_div_iff₀ (by linarith : 0<1-Y/X)).mp hu
  have hw := mul_le_mul_of_nonneg_right (min_le_left (2*X) (n/(1-Y/X))) hδ
  have he : (2*X)*(Y/X)=2*Y := by field_simp
  rw [he] at hw
  unfold overlap
  rw [min_self, max_self]
  apply max_le
  · nlinarith [le_max_right X n]
  · linarith

theorem physicalSupport_card (X : ℝ) (hX : 0≤X) :
    ((physicalSupport X).card : ℝ)≤2*X := by
  simp only [physicalSupport,FiniteSieveWindow.window,Nat.floor_zero,Nat.card_Ioc,Nat.sub_zero]
  exact Nat.floor_le (by positivity)

theorem eventual_coefficient_cap (s : ℝ) (hs : 0<s) (hs1 : s≤1/1000) :
    ∀ᶠ X : ℝ in atTop, 1<X ∧ 1000≤Real.log X ∧
      ∀ n∈physicalSupport X, |physicalCoefficient X s n|≤X^(1/200 : ℝ) := by
  have htwo := (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/400)).eventually
    (eventually_ge_atTop (2:ℝ))
  filter_upwards [LongerTupleCollection.eventually_divisor_cap (1/400) (by norm_num),
    htwo,Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1000:ℝ)),
    eventually_ge_atTop (2:ℝ)] with X hd htwo hl hXtwo
  have hX : 1<X := by linarith
  have hXp : 0<X := by linarith
  refine ⟨hX,hl,?_⟩
  intro n hn
  have hmem := (SieveDivisorWindow.mem_window_iff 0 (2*X) (by norm_num) (by positivity) n).mp hn
  have hpos : 0<n := by exact_mod_cast hmem.1
  have hnX : (n:ℝ)≤X^2 := hmem.2.trans (by nlinarith)
  calc
    _ ≤ 2*(n.divisors.card : ℝ) := physicalCoefficient_bound X s hX hs hs1 hl n hpos
    _ ≤ X^(1/400 : ℝ)*X^(1/400 : ℝ) := mul_le_mul htwo (hd.2 n hnX)
      (Nat.cast_nonneg _) (Real.rpow_nonneg hXp.le _)
    _ = _ := by rw [← Real.rpow_add hXp]; norm_num

theorem diagonal_nonneg (X s Y : ℝ) : 0≤diagonal X s Y :=
  Finset.sum_nonneg (fun n _ => mul_nonneg (sq_nonneg _) (overlap_nonneg _ _ _ _))

theorem diagonal_bound (X s Y : ℝ) (hX : 0<X) (hY : 0≤Y) (hYX : Y<X)
    (hcap : ∀ n∈physicalSupport X, |physicalCoefficient X s n|≤X^(1/200 : ℝ)) :
    (1/X)*diagonal X s Y≤4*Y*X^(1/100 : ℝ) := by
  have hsquare (n : ℕ) (hn : n∈physicalSupport X) :
      (physicalCoefficient X s n)^2≤X^(1/100 : ℝ) := by
    have hh := pow_le_pow_left₀ (abs_nonneg _) (hcap n hn) 2
    rw [sq_abs, ← Real.rpow_mul_natCast hX.le] at hh
    convert hh using 1 <;> norm_num
  have hD : diagonal X s Y≤4*X*Y*X^(1/100 : ℝ) := by
    calc
      _ ≤ ∑ _n∈physicalSupport X, X^(1/100 : ℝ)*(2*Y) :=
        Finset.sum_le_sum (fun n hn => mul_le_mul (hsquare n hn)
          (overlap_diagonal_le X Y n hX hY hYX) (overlap_nonneg _ _ _ _) (Real.rpow_nonneg hX.le _))
      _ = ((physicalSupport X).card : ℝ)*(X^(1/100 : ℝ)*(2*Y)) := by simp
      _ ≤ (2*X)*(X^(1/100 : ℝ)*(2*Y)) := mul_le_mul_of_nonneg_right
        (physicalSupport_card X hX.le) (by positivity)
      _ = _ := by ring
  exact (mul_le_mul_of_nonneg_left hD (by positivity : 0≤1/X)).trans_eq (by field_simp)

theorem eventually_diagonal_log (s : ℝ) (A : ℕ) (hs : 0<s) (hs1 : s≤1/1000) :
    ∀ᶠ X : ℝ in atTop, 1<X ∧ 1000≤Real.log X ∧
      let Y := halfWidth X (101/1000)
      (1/X)*diagonal X s Y≤Y^2/(Real.log X)^A := by
  filter_upwards [eventual_coefficient_cap s hs hs1,
    halfWidth_eventually (101/1000) (by norm_num),
    PolynomialLogEnvelope.eventually_bound 8 A (91/1000) (by norm_num) (by norm_num)]
      with X hc hY hlog
  refine ⟨hc.1,hc.2.1,?_⟩
  dsimp only
  let Y := halfWidth X (101/1000)
  have hXp : 0<X := by linarith [hc.1]
  have hl : 0<Real.log X := Real.log_pos hc.1
  have hL : 8*(Real.log X)^A≤X^(91/1000 : ℝ) :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hl.le
      (by linarith : Real.log X≤1+Real.log X) A) (by norm_num)).trans hlog.2
  have he := mul_le_mul_of_nonneg_left hL (Real.rpow_pos_of_pos hXp (1/100 : ℝ)).le
  have hp : X^(1/100 : ℝ)*X^(91/1000 : ℝ)=X^(101/1000 : ℝ) := by
    rw [← Real.rpow_add hXp]
    norm_num
  rw [hp] at he
  have hsmall : 4*X^(1/100 : ℝ)*(Real.log X)^A≤Y := by
    dsimp [Y,halfWidth]
    nlinarith
  apply (diagonal_bound X s Y hXp hY.1.le (by linarith [hY.2]) hc.2.2).trans
  apply (le_div_iff₀ (pow_pos hl A)).mpr
  have hh := mul_le_mul_of_nonneg_left hsmall hY.1.le
  nlinarith

#print axioms eventually_diagonal_log
run_cmd do
  for decl in [``overlap_diagonal_le, ``physicalSupport_card, ``eventual_coefficient_cap,
      ``diagonal_nonneg, ``diagonal_bound, ``eventually_diagonal_log] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end SeparatedCoreDiagonalWork
