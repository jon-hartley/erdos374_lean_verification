import LongPairCofactorSwitchWork
import SignedFiniteWindowApproximation
import PrimeTupleSharpMeanWork

/-! A single fixed signed polynomial for the entire separated core.
All completed cofactors and the original main mass are retained globally. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace SeparatedCoreGlobalPerronWork
open LongPairSeparatedCoreWork LongPairCloseDistinctMeanWork
open Erdos374.HarmanGram152

def physicalSupport (X : ℝ) : Finset ℕ := FiniteSieveWindow.window 0 (2*X)
def physicalCoefficient (X s : ℝ) (n : ℕ) : ℝ :=
  SieveDivisorWindow.evaluation (coreSupport X s) (coreCoefficient X s) n

def mainMass (X s : ℝ) : ℝ :=
  HarmanDivisorWindow.reciprocalMass (coreSupport X s) (coreCoefficient X s)

def polynomial (X s σ t : ℝ) : ℂ :=
  verticalDirichlet152 (physicalSupport X) (fun n => (physicalCoefficient X s n : ℂ)) σ t

def centeredTransform (X s Y x : ℝ) : ℂ :=
  ((1/(2*Real.pi) : ℝ) : ℂ) *
    SmoothedWindowTransfer.transform (polynomial X s (1+1/Real.log X))
      MellinSmoothingFunction.smoothing (X^(-19/20 : ℝ)) (-X) X
      (1+1/Real.log X) (Y/X) x - ((x*(Y/X)*mainMass X s : ℝ) : ℂ)

theorem physicalCoefficient_bound (X s : ℝ) (hX : 1<X) (hs : 0<s)
    (hs1 : s≤1/1000) (hlog : 1000≤Real.log X) (n : ℕ) (hn : 0<n) :
    |physicalCoefficient X s n|≤2*(n.divisors.card : ℝ) := by
  have hsub : (coreSupport X s).filter (fun d => d∣n) ⊆ n.divisors := by
    intro d hd
    exact Nat.mem_divisors.mpr ⟨(Finset.mem_filter.mp hd).2,by omega⟩
  unfold physicalCoefficient SieveDivisorWindow.evaluation
  rw [← Finset.sum_filter]
  calc
    _ ≤ ∑ d∈(coreSupport X s).filter (fun d => d∣n), |coreCoefficient X s d| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d∈(coreSupport X s).filter (fun d => d∣n), (2:ℝ) :=
      Finset.sum_le_sum (fun d _ => coreCoefficient_abs_le_two X s hX hs hs1 hlog d)
    _ ≤ _ := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      have hc : (((coreSupport X s).filter (fun d => d∣n)).card : ℝ)≤n.divisors.card :=
        by exact_mod_cast Finset.card_le_card hsub
      nlinarith

theorem sharp_difference (X s L R : ℝ) (hL : 0≤L) (hLR : L≤R) (hR : R≤2*X) :
    SmoothedCountBoundary.sharp (physicalSupport X) (physicalCoefficient X s) R -
      SmoothedCountBoundary.sharp (physicalSupport X) (physicalCoefficient X s) L =
        ∑ n∈FiniteSieveWindow.window L R, physicalCoefficient X s n := by
  have hfilter : (physicalSupport X).filter (fun n : ℕ => L<(n:ℝ) ∧ (n:ℝ)≤R) =
      FiniteSieveWindow.window L R := by
    ext n
    rw [Finset.mem_filter, SieveDivisorWindow.mem_window_iff L R hL hLR]
    constructor
    · exact fun h => h.2
    · intro hn
      refine ⟨?_,hn⟩
      exact (SieveDivisorWindow.mem_window_iff 0 (2*X) (by norm_num)
        (hL.trans (hLR.trans hR)) n).mpr ⟨hL.trans_lt hn.1,hn.2.trans hR⟩
  rw [← hfilter, Finset.sum_filter]
  unfold SmoothedCountBoundary.sharp
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  split_ifs <;> simp_all <;> linarith

theorem remainder_eq_sharp (X s L R : ℝ)
    (hi : ∀ m∈coreSupport X s, 0<m) (hL : 0≤L) (hLR : L≤R) (hR : R≤2*X) :
    separatedRemainder X s L R =
      SmoothedCountBoundary.sharp (physicalSupport X) (physicalCoefficient X s) R -
        SmoothedCountBoundary.sharp (physicalSupport X) (physicalCoefficient X s) L -
          (R-L)*mainMass X s := by
  rw [sharp_difference X s L R hL hLR hR, coreRemainder_eq_collected]
  have hh := SieveDivisorWindow.sum_evaluation_eq_main_add_remainder
    (coreSupport X s) (coreCoefficient X s) L R hi hL hLR
  change (∑ n∈FiniteSieveWindow.window L R, physicalCoefficient X s n) =
    (R-L)*mainMass X s + HarmanDivisorWindow.remainder (coreSupport X s) (coreCoefficient X s) L R at hh
  linarith

theorem eventual_approximation (s : ℝ) (hs : 0<s) (hs1 : s≤1/1000) :
    ∀ᶠ X : ℝ in atTop, 1<X ∧ 1000≤Real.log X ∧
      ∀ Y : ℝ, 0≤Y → Y≤X/2 → ∀ x∈Icc X (2*X),
        ‖(separatedRemainder X s (x-x*(Y/X)) x : ℂ) - centeredTransform X s Y x‖ ≤
          4*X^(2/25 : ℝ) := by
  have htwo := (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/400)).eventually
    (eventually_ge_atTop (2:ℝ))
  filter_upwards [SignedFiniteWindowApproximation.eventual_approximation,
    LongerTupleCollection.eventually_divisor_cap (1/400) (by norm_num), htwo,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1000:ℝ)),
    eventually_ge_atTop (2:ℝ)] with X ha hd htwo hl hXtwo
  have hX : 1<X := by linarith
  have hXp : 0<X := by linarith
  refine ⟨hX,hl,?_⟩
  intro Y hY hYX x hx
  have hδ : Y/X∈Icc 0 (1/2) :=
    ⟨div_nonneg hY hXp.le,(div_le_iff₀ hXp).mpr (by linarith)⟩
  have hB : 1≤⌊2*X⌋₊ := (Nat.le_floor_iff (by positivity)).mpr (by norm_num; linarith)
  have hBX : (⌊2*X⌋₊ : ℝ)≤X^2 := (Nat.floor_le (by positivity)).trans (by nlinarith)
  have hS : ∀ n∈physicalSupport X, 0<n ∧ n≤⌊2*X⌋₊ := by
    intro n hn
    simpa [physicalSupport,FiniteSieveWindow.window] using Finset.mem_Ioc.mp hn
  have hw : ∀ n∈physicalSupport X, |physicalCoefficient X s n|≤X^(1/200 : ℝ) := by
    intro n hn
    have hnX : (n:ℝ)≤X^2 := (by exact_mod_cast (hS n hn).2 : (n:ℝ)≤⌊2*X⌋₊).trans hBX
    calc
      _ ≤ 2*(n.divisors.card : ℝ) := physicalCoefficient_bound X s hX hs hs1 hl n (hS n hn).1
      _ ≤ X^(1/400 : ℝ)*X^(1/400 : ℝ) := mul_le_mul htwo (hd.2 n hnX)
        (Nat.cast_nonneg _) (Real.rpow_nonneg hXp.le _)
      _ = _ := by rw [← Real.rpow_add hXp]; norm_num
  have hh := ha.2 (physicalSupport X) (physicalCoefficient X s) ⌊2*X⌋₊ x (Y/X)
    hB hBX hS hw hx hδ
  have hi : ∀ m∈coreSupport X s, 0<m := by
    intro m hm
    have hg := support_geometry X s hX hs hs1 hl m hm
    exact_mod_cast (Real.rpow_pos_of_pos hXp (26/35 : ℝ)).trans hg.1
  have hleft : 0≤x-x*(Y/X) := by
    have hh := mul_le_mul_of_nonneg_left hδ.2 (hXp.trans_le hx.1).le
    linarith [hx.1]
  rw [remainder_eq_sharp X s _ _ hi hleft
    (by nlinarith [mul_nonneg (hXp.trans_le hx.1).le hδ.1]) hx.2]
  unfold centeredTransform polynomial SignedFiniteWindowApproximation.error at *
  convert hh using 1
  congr 1
  push_cast
  ring

#print axioms eventual_approximation
run_cmd do
  for decl in [``physicalCoefficient_bound, ``sharp_difference, ``remainder_eq_sharp,
      ``eventual_approximation] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end SeparatedCoreGlobalPerronWork
