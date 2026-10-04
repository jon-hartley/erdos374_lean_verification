import CancellationTransferEndpointMean
import PositiveSharpCellMean

/-! Exact reciprocal-mass centering correction for the source dyadic
intervals [2^j,2^(j+1)) and the actual intervals (2^j,2^(j+1)]. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators
namespace CancellationTransferCenter
open PositiveInteriorModel PositiveInteriorCells PositiveInteriorRectangles
open PositiveSharpCounts PositiveSharpResidual PositiveSharpMovingWindow
open CancellationTransferEndpoints CancellationTransferEndpointMean

def sourceMass (m : ℕ) : ℝ :=
  ∑ n∈Finset.Ico (2^m) (2*2^m),ArithmeticFunction.vonMangoldt n/(n:ℝ)

def centerCell (X : ℝ) (j : ℕ×ℕ) : ℝ :=
  (sourceMass j.1*sourceMass j.2-
    reciprocalMass (scale j.1)*reciprocalMass (scale j.2))/denominator X j

def centerTotal (X : ℝ) : ℝ := ∑ j∈boxes (mesh X),centerCell X j

def sourceResidual (X : ℝ) (j : ℕ×ℕ) (x y : ℝ) : ℝ :=
  (sourceCount X j x y-y*sourceMass j.1*sourceMass j.2)/(y*denominator X j)

def sourceResidualAbs (X x y : ℝ) : ℝ :=
  ∑ j∈boxes (mesh X),|sourceResidual X j x y|

theorem sourceMass_nonneg (m : ℕ) : 0≤sourceMass m := by
  exact Finset.sum_nonneg (fun n _ => div_nonneg ArithmeticFunction.vonMangoldt_nonneg
    (Nat.cast_nonneg n))

theorem actualMass_nonneg (m : ℕ) : 0≤reciprocalMass (scale m) := by
  exact Finset.sum_nonneg (fun n _ => div_nonneg ArithmeticFunction.vonMangoldt_nonneg
    (Nat.cast_nonneg n))

theorem sourceMass_eq (m : ℕ) (hm : 1≤m) :
    sourceMass m=reciprocalMass (scale m)+Real.log 2/(2*scale m) := by
  have hle : (2:ℕ)^m≤2*2^m := by omega
  have hs := (Finset.sum_Ico_add_eq_sum_Icc
    (f := fun n:ℕ => ArithmeticFunction.vonMangoldt n/(n:ℝ)) hle).trans
      (Finset.add_sum_Ioc_eq_sum_Icc (f := fun n:ℕ => ArithmeticFunction.vonMangoldt n/(n:ℝ)) hle).symm
  have hb : ArithmeticFunction.vonMangoldt ((2:ℕ)^m)=Real.log 2 := by
    rw [ArithmeticFunction.vonMangoldt_apply_pow (by omega),
      ArithmeticFunction.vonMangoldt_apply_prime (by decide : Nat.Prime 2)]
    norm_num
  have ht : ArithmeticFunction.vonMangoldt (2*(2:ℕ)^m)=Real.log 2 := by
    rw [show 2*(2:ℕ)^m=2^(m+1) by ring,
      ArithmeticFunction.vonMangoldt_apply_pow (by omega),
      ArithmeticFunction.vonMangoldt_apply_prime (by decide : Nat.Prime 2)]
    norm_num
  have hM : reciprocalMass (scale m)=
      ∑ n∈Finset.Ioc (2^m) (2*2^m),ArithmeticFunction.vonMangoldt n/(n:ℝ) := by
    simp only [reciprocalMass,floor_scale,floor_twice_scale]
  rw [hb,ht,←hM] at hs
  push_cast at hs
  change sourceMass m+Real.log 2/(2*scale m)=Real.log 2/scale m+reciprocalMass (scale m) at hs
  have hp : scale m≠0 := by unfold scale; positivity
  have he : Real.log 2/scale m=2*(Real.log 2/(2*scale m)) := by field_simp
  rw [he] at hs
  linarith

theorem dyadic_mass_le (m : ℕ) (ell : ℝ) (hl : Real.log (2*scale m)≤ell)
    (hell : 0≤ell) : sourceMass m≤ell ∧ reciprocalMass (scale m)≤ell := by
  have hp : 0<scale m := by unfold scale; positivity
  have hpN : 0<(2:ℕ)^m := by positivity
  have hb (S : Finset ℕ) (hS : ∀n∈S,(2:ℕ)^m≤n ∧ n≤2*2^m)
      (hc : S.card≤(2:ℕ)^m) :
      (∑ n∈S,ArithmeticFunction.vonMangoldt n/(n:ℝ))≤ell := by
    have ht (n : ℕ) (hn : n∈S) : ArithmeticFunction.vonMangoldt n/(n:ℝ)≤ell/scale m := by
      have hh := hS n hn
      have hn0 : 0<n := hpN.trans_le hh.1
      have hp' : scale m≤(n:ℝ) := by dsimp [scale]; exact_mod_cast hh.1
      have hn' : (n:ℝ)≤2*scale m := by dsimp [scale]; exact_mod_cast hh.2
      have hl' := ArithmeticFunction.vonMangoldt_le_log.trans
        ((Real.log_le_log (by exact_mod_cast hn0) hn').trans hl)
      exact (div_le_div_of_nonneg_right hl' (Nat.cast_nonneg n)).trans
        (div_le_div_of_nonneg_left hell hp hp')
    calc
      _ ≤ ∑ _n∈S,ell/scale m := Finset.sum_le_sum ht
      _ = (S.card:ℝ)*(ell/scale m) := by simp
      _ ≤ scale m*(ell/scale m) := mul_le_mul_of_nonneg_right (by dsimp [scale]; exact_mod_cast hc)
        (div_nonneg hell hp.le)
      _ = ell := by field_simp
  constructor
  · apply hb
    · intro n hn
      obtain ⟨h1,h2⟩ := Finset.mem_Ico.mp hn
      exact ⟨h1,h2.le⟩
    · rw [Nat.card_Ico]
      omega
  · simp only [reciprocalMass,floor_scale,floor_twice_scale]
    apply hb
    · intro n hn
      obtain ⟨h1,h2⟩ := Finset.mem_Ioc.mp hn
      exact ⟨h1.le,h2⟩
    · rw [Nat.card_Ioc]
      omega

theorem centerCell_nonneg (X : ℝ) (hX : 1<X) (hm : mesh X≤1/8)
    (j : ℕ×ℕ) (hj : j∈boxes (mesh X)) : 0≤centerCell X j := by
  have hi := indices_two X hX hm j hj
  have hP : 0<scale j.1 := by unfold scale; positivity
  have hR : 0<scale j.2 := by unfold scale; positivity
  have hl : 0<Real.log X := Real.log_pos hX
  have hd : 0<denominator X j := (by positivity : 0<(Real.log X)^3/96).trans_le
    (denominator_lower X hX j hj)
  unfold centerCell
  apply div_nonneg _ hd.le
  rw [sourceMass_eq j.1 (by omega),sourceMass_eq j.2 (by omega)]
  have hmP := actualMass_nonneg j.1
  have hmR := actualMass_nonneg j.2
  have h2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hcP : 0≤Real.log 2/(2*scale j.1) := by positivity
  have hcR : 0≤Real.log 2/(2*scale j.2) := by positivity
  apply sub_nonneg.mpr
  exact mul_le_mul (le_add_of_nonneg_right hcP) (le_add_of_nonneg_right hcR)
    hmR (add_nonneg hmP hcP)

theorem centerCell_le (X : ℝ) (hX : 1<X) (hm : mesh X≤1/8)
    (j : ℕ×ℕ) (hj : j∈boxes (mesh X)) :
    centerCell X j≤192/(PositiveSharpDeletionMass.shortestScale X*Real.log X) := by
  have hXp : 0<X := by linarith
  have hell : 0<Real.log X := Real.log_pos hX
  have hP : 0<scale j.1 := by unfold scale; positivity
  have hR : 0<scale j.2 := by unfold scale; positivity
  have hS : 0<PositiveSharpDeletionMass.shortestScale X := Real.rpow_pos_of_pos hXp _
  have hi := indices_two X hX hm j hj
  have hs := PositiveSharpDeletionMass.scales_ge_shortest X hX j hj
  have hu := PositiveSharpDeletionMass.upper_endpoints_le X hX hm j hj
  have hpm := dyadic_mass_le j.1 (Real.log X)
    (Real.log_le_log (by positivity) hu.1) hell.le
  have hrm := dyadic_mass_le j.2 (Real.log X)
    (Real.log_le_log (by positivity) hu.2.1) hell.le
  have hlog2 : Real.log 2≤Real.log X := by
    have h1 : (1:ℝ)≤scale j.1 := by unfold scale; exact one_le_pow₀ (by norm_num)
    exact Real.log_le_log (by norm_num) (by linarith [hu.1])
  have h2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hc (m : ℕ) (hsp : PositiveSharpDeletionMass.shortestScale X≤scale m) :
      Real.log 2/(2*scale m)≤Real.log X/PositiveSharpDeletionMass.shortestScale X := by
    have hp : 0<scale m := hS.trans_le hsp
    apply (div_le_div_of_nonneg_right hlog2 (by positivity : 0≤2*scale m)).trans
    exact div_le_div_of_nonneg_left hell.le hS (by linarith)
  have hcP := hc j.1 hs.1
  have hcR := hc j.2 hs.2.1
  have hprod : sourceMass j.1*sourceMass j.2-
      reciprocalMass (scale j.1)*reciprocalMass (scale j.2)≤
      2*(Real.log X)^2/PositiveSharpDeletionMass.shortestScale X := by
    calc
      _ = (Real.log 2/(2*scale j.1))*sourceMass j.2+
          reciprocalMass (scale j.1)*(Real.log 2/(2*scale j.2)) := by
        rw [sourceMass_eq j.1 (by omega),sourceMass_eq j.2 (by omega)]
        ring
      _ ≤ (Real.log X/PositiveSharpDeletionMass.shortestScale X)*Real.log X+
          Real.log X*(Real.log X/PositiveSharpDeletionMass.shortestScale X) :=
        add_le_add (mul_le_mul hcP hrm.1 (sourceMass_nonneg j.2) (by positivity))
          (mul_le_mul hpm.2 hcR (by positivity) hell.le)
      _ = _ := by ring
  have hd := denominator_lower X hX j hj
  have hdp : 0<denominator X j := (by positivity : 0<(Real.log X)^3/96).trans_le hd
  unfold centerCell
  calc
    _ ≤ (2*(Real.log X)^2/PositiveSharpDeletionMass.shortestScale X)/denominator X j :=
      div_le_div_of_nonneg_right hprod hdp.le
    _ ≤ (2*(Real.log X)^2/PositiveSharpDeletionMass.shortestScale X)/((Real.log X)^3/96) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hd
    _ = _ := by field_simp; ring

theorem centerTotal_le (X : ℝ) (hX : 1<X) (hm : mesh X≤1/1000000) :
    centerTotal X≤5*Real.log X/X^((1:ℝ)/6) := by
  have hell : 0<Real.log X := Real.log_pos hX
  have hS : 0<PositiveSharpDeletionMass.shortestScale X :=
    Real.rpow_pos_of_pos (by linarith : 0<X) _
  calc
    _ ≤ ∑ _j∈boxes (mesh X),192/(PositiveSharpDeletionMass.shortestScale X*Real.log X) :=
      Finset.sum_le_sum (fun j hj => centerCell_le X hX (by linarith) j hj)
    _ = (((boxes (mesh X)).card:ℝ)/(Real.log X)^2)*
        (192*Real.log X/PositiveSharpDeletionMass.shortestScale X) := by simp; field_simp
    _ ≤ (1/45)*(192*Real.log X/PositiveSharpDeletionMass.shortestScale X) :=
      mul_le_mul_of_nonneg_right (cell_card_normalized_bound X hX hm) (by positivity)
    _ ≤ _ := by
      change (1/45)*(192*Real.log X/X^((1:ℝ)/6))≤_
      have hp : 0≤Real.log X/X^((1:ℝ)/6) := by positivity
      convert mul_le_mul_of_nonneg_right (by norm_num : (192/45:ℝ)≤5) hp using 1 <;> ring

theorem sourceResidual_eq (X x y : ℝ) (hy : y≠0) (j : ℕ×ℕ) :
    sourceResidual X j x y=cellResidual X j x y+endpointCell X j x y-centerCell X j := by
  unfold sourceResidual cellResidual endpointCell centerCell
  field_simp
  ring

run_cmd do
  for decl in [``sourceMass_nonneg,``actualMass_nonneg,``sourceMass_eq,``dyadic_mass_le,
      ``centerCell_nonneg,``centerCell_le,``centerTotal_le,``sourceResidual_eq] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "EXACT DYADIC RECIPROCAL CENTER CORRECTION; ACTUAL SMALL CENTER BUDGET"
end CancellationTransferCenter
end
