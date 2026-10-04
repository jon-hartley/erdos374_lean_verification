import Item1UniformLogArithmetic
import SourceAbelLow

/-! UNCOMPILED. Actual support geometry and uniform local arithmetic.
All supports are the original [P,2P), [R,2R), (L/8,4L] supports.
No independently chosen prime interval and no caller-supplied PNT error occur
in the eventual endpoints. Width budgets use (log X)^K, not (1+log X)^K. -/
set_option autoImplicit false
set_option maxHeartbeats 24000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators
namespace Item1SourceLocalArithmetic
open Item1UniformLogArithmetic SourceLiteralMoments SourceLiteralMass SourceAbelLow
open PositiveInteriorModel PositiveInteriorCells

def lowCut (X : ℝ) (K : ℕ) : ℝ := (Real.log X)^K

def errorBudget (X : ℝ) (K : ℕ) : ℝ :=
  1/((1+Real.log X)^20*(lowCut X K)^2)

def badMass (X : ℝ) (j : ℕ×ℕ) (i : Fin 3) : ℝ :=
  ∑ n ∈ (support X j i).filter (fun n => ¬ n.Prime),
    ArithmeticFunction.vonMangoldt n/(n:ℝ)

theorem badMass_nonneg (X : ℝ) (j : ℕ×ℕ) (i : Fin 3) : 0 ≤ badMass X j i :=
  Finset.sum_nonneg (fun n _ => div_nonneg ArithmeticFunction.vonMangoldt_nonneg
    (Nat.cast_nonneg _))

/-- The factor-eight endpoint loss is paid uniformly before choosing a cell. -/
theorem ideal_eighth_lower (X : ℝ) (j : ℕ×ℕ) (i : Fin 3)
    (hX : 2≤X) (hlog : 1000000≤Real.log X) (hj : j∈boxes (mesh X)) :
    X^((1:ℝ)/7) ≤ ideal X j i/8 := by
  have hXp : 0<X := by linarith
  have hi := ideal_positive X j hXp i
  have he := (exponent_bounds X j (by linarith) hj i).1
  have hlog2 : Real.log 2≤1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    linarith
  have hlog8 : Real.log 8≤3 := by
    rw [show (8:ℝ)=2^3 by norm_num, Real.log_pow]
    norm_num
    linarith
  apply (Real.log_le_log_iff (Real.rpow_pos_of_pos hXp _) (by positivity)).mp
  rw [Real.log_rpow hXp, Real.log_div hi.ne' (by norm_num),
    ideal_log X j (by linarith) i]
  have hh := mul_le_mul_of_nonneg_right he (show 0≤Real.log X by linarith)
  nlinarith

/-- Coarse bounds preserve the exact membership test, including floor endpoints. -/
theorem support_local_bounds (X : ℝ) (j : ℕ×ℕ) (i : Fin 3) (n : ℕ)
    (hX : 0<X) (hn : n∈support X j i) :
    ideal X j i/8 ≤ (n:ℝ) ∧ (n:ℝ) ≤ 4*ideal X j i := by
  have hi := ideal_positive X j hX i
  fin_cases i
  · have hm := Finset.mem_Ico.mp hn
    have hlo : scale j.1≤(n:ℝ) := by
      simpa [scale] using (show (((2:ℕ)^j.1:ℕ):ℝ)≤n by exact_mod_cast hm.1)
    have hhi : (n:ℝ)≤2*scale j.1 := by
      simpa [scale] using (show (n:ℝ)≤(2*(2:ℕ)^j.1:ℕ) by exact_mod_cast hm.2.le)
    change scale j.1/8≤(n:ℝ) ∧ (n:ℝ)≤4*scale j.1
    change 0<scale j.1 at hi
    constructor <;> linarith
  · have hm := Finset.mem_Ico.mp hn
    have hlo : scale j.2≤(n:ℝ) := by
      simpa [scale] using (show (((2:ℕ)^j.2:ℕ):ℝ)≤n by exact_mod_cast hm.1)
    have hhi : (n:ℝ)≤2*scale j.2 := by
      simpa [scale] using (show (n:ℝ)≤(2*(2:ℕ)^j.2:ℕ) by exact_mod_cast hm.2.le)
    change scale j.2/8≤(n:ℝ) ∧ (n:ℝ)≤4*scale j.2
    change 0<scale j.2 at hi
    constructor <;> linarith
  · have hm := Finset.mem_Ioc.mp hn
    change thirdScale X j/8≤(n:ℝ) ∧ (n:ℝ)≤4*thirdScale X j
    change 0<thirdScale X j at hi
    have hfloor := Nat.lt_floor_add_one (thirdScale X j/8)
    have hlo : (⌊thirdScale X j/8⌋₊:ℝ)+1≤(n:ℝ) := by
      exact_mod_cast (show ⌊thirdScale X j/8⌋₊+1≤n by omega)
    have hhi : (n:ℝ)≤(⌊4*thirdScale X j⌋₊:ℝ) := by exact_mod_cast hm.2
    exact ⟨by linarith, hhi.trans (Nat.floor_le (by positivity))⟩

/-- A reciprocal bad-factor mass is paid by the exact psi-theta prefix. -/
theorem badMass_le_gap (X : ℝ) (j : ℕ×ℕ) (i : Fin 3) (hX : 0<X) :
    badMass X j i ≤ (8/ideal X j i)*
      |Chebyshev.psi (4*ideal X j i)-Chebyshev.theta (4*ideal X j i)| := by
  classical
  let Z := ideal X j i
  have hZ : 0<Z := ideal_positive X j hX i
  have hsub : (support X j i).filter (fun n => ¬ n.Prime) ⊆
      (Finset.Ioc 0 ⌊4*Z⌋₊).filter (fun n => ¬ n.Prime) := by
    intro n hn
    obtain ⟨hnS, hnp⟩ := Finset.mem_filter.mp hn
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr
      ⟨support_pos X j i n hnS, Nat.le_floor (support_local_bounds X j i n hX hnS).2⟩, hnp⟩
  have hraw := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun n _ _ => ArithmeticFunction.vonMangoldt_nonneg (n:=n))
  have hgap0 : 0≤Chebyshev.psi (4*Z)-Chebyshev.theta (4*Z) :=
    sub_nonneg.mpr (Chebyshev.theta_le_psi _)
  rw [← Chebyshev.psi_sub_theta_eq_sum_not_prime] at hraw
  calc
    badMass X j i ≤ ∑ n ∈ (support X j i).filter (fun n => ¬ n.Prime),
        (8/Z)*ArithmeticFunction.vonMangoldt n := by
      apply Finset.sum_le_sum
      intro n hn
      have hnS := (Finset.mem_filter.mp hn).1
      have hn0 : (0:ℝ)<n := by exact_mod_cast support_pos X j i n hnS
      have hb := (support_local_bounds X j i n hX hnS).1
      have hinv : 1/(n:ℝ)≤8/Z := by
        apply (div_le_div_iff₀ hn0 hZ).mpr
        nlinarith
      simpa only [div_eq_mul_inv, one_mul, mul_comm, mul_left_comm, mul_assoc] using
        mul_le_mul_of_nonneg_left hinv
          (ArithmeticFunction.vonMangoldt_nonneg (n:=n))
    _ = (8/Z)*(∑ n ∈ (support X j i).filter (fun n => ¬ n.Prime),
        ArithmeticFunction.vonMangoldt n) := (Finset.mul_sum _ _ _).symm
    _ ≤ (8/Z)*(Chebyshev.psi (4*Z)-Chebyshev.theta (4*Z)) :=
      mul_le_mul_of_nonneg_left hraw (by positivity)
    _ = _ := by rw [abs_of_nonneg hgap0]

/-- Uniform actual-cell bad masses; all three factors and all cells share X0. -/
theorem eventually_badMass_weighted (m : ℕ) (eps : ℝ) (heps : 0<eps) :
    ∀ᶠ X : ℝ in atTop, ∀ j∈boxes (mesh X), ∀ i : Fin 3,
      badMass X j i*(1+Real.log X)^m ≤ eps := by
  have hgap := uniform_prime_power_gap m (eps/32) (by positivity)
  have hlog := Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1000000:ℝ))
  filter_upwards [hgap, hlog, eventually_ge_atTop (2:ℝ)] with X hg hl hX
  intro j hj i
  let Z := ideal X j i
  have hZ : 0<Z := ideal_positive X j (by linarith) i
  have hlo := ideal_eighth_lower X j i hX hl hj
  have he := hg (4*Z) (hlo.trans (by dsimp [Z]; linarith))
  have hb := mul_le_mul_of_nonneg_right (badMass_le_gap X j i (by linarith))
    (pow_nonneg (show 0≤1+Real.log X by linarith) m)
  have hm := mul_le_mul_of_nonneg_left he (show 0≤8/Z by positivity)
  have hid : (8/Z)*((eps/32)*(4*Z))=eps := by field_simp [ne_of_gt hZ] <;> ring
  rw [hid] at hm
  exact hb.trans (by simpa only [mul_assoc] using hm)

/-- Converting a polynomial log-weight into the precise low-cutoff budget. -/
theorem budget_weight_le (X : ℝ) (K : ℕ) (hlog : 1≤Real.log X) :
    (1+Real.log X)^20*(lowCut X K)^2 ≤ (1+Real.log X)^(20+2*K) := by
  have hh := pow_le_pow_left₀ (show 0≤Real.log X by linarith)
    (show Real.log X≤1+Real.log X by linarith) (2*K)
  have hm := mul_le_mul_of_nonneg_left hh
    (pow_nonneg (show 0≤1+Real.log X by linarith) 20)
  simpa only [lowCut, ← pow_mul, pow_add, Nat.mul_comm K 2] using hm

theorem budget_pos (X : ℝ) (K : ℕ) (hlog : 1≤Real.log X) : 0<errorBudget X K := by
  have hLp : 0<Real.log X := by linarith
  unfold errorBudget lowCut
  positivity

theorem lowCut_ge_one (X : ℝ) (K : ℕ) (hlog : 1≤Real.log X) : 1≤lowCut X K := by
  simpa only [one_pow, lowCut] using pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1) hlog K

/-- Supplies, rather than assumes, the exact local input consumed by v8. -/
theorem eventually_localPsi (K : ℕ) :
    ∀ᶠ X : ℝ in atTop, ∀ j∈boxes (mesh X),
      LocalPsiError X j (errorBudget X K) := by
  have hpsi := uniform_psi (20+2*K) 1 (by norm_num)
  have hlog := Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1000000:ℝ))
  filter_upwards [hpsi, hlog, eventually_ge_atTop (2:ℝ)] with X hp hl hX
  intro j hj u hu
  have huX : X^((1:ℝ)/7)≤u :=
    (ideal_eighth_lower X j 2 hX hl hj).trans hu.1
  have hpu := hp u huX
  simp only [one_mul] at hpu
  have hb := mul_le_mul_of_nonneg_left
    (budget_weight_le X K (by linarith)) (abs_nonneg (Chebyshev.psi u-u))
  have hW : 0<(1+Real.log X)^20*(lowCut X K)^2 := by
    have hLp : 0<Real.log X := by linarith
    unfold lowCut
    positivity
  have hh := (le_div_iff₀ hW).mpr (hb.trans hpu)
  simpa only [errorBudget, div_eq_mul_inv, mul_comm, one_mul] using hh

/-- Supplies all three uniform bad-factor mass budgets with no spectral assumption. -/
theorem eventually_badMass_budget (K : ℕ) :
    ∀ᶠ X : ℝ in atTop, ∀ j∈boxes (mesh X), ∀ i : Fin 3,
      badMass X j i ≤ errorBudget X K := by
  have hbad := eventually_badMass_weighted (20+2*K) 1 (by norm_num)
  have hlog := Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))
  filter_upwards [hbad, hlog] with X hb hl
  intro j hj i
  have hw := mul_le_mul_of_nonneg_left (budget_weight_le X K hl)
    (badMass_nonneg X j i)
  have hW : 0<(1+Real.log X)^20*(lowCut X K)^2 := by
    have hLp : 0<Real.log X := by linarith
    unfold lowCut
    positivity
  exact (le_div_iff₀ hW).mpr (hw.trans (hb j hj i))

run_cmd do
  for target in [``badMass_nonneg, ``ideal_eighth_lower, ``support_local_bounds, ``badMass_le_gap, ``eventually_badMass_weighted, ``budget_weight_le, ``budget_pos, ``lowCut_ge_one, ``eventually_localPsi, ``eventually_badMass_budget] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "Item1SourceLocalArithmetic: 10 original theorem guards passed."

end Item1SourceLocalArithmetic
