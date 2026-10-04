import OuterBlockMassBudgetWork
import OuterBlockCofactorScaleWork
import HarmanDivisorWindow
import OuterNormalizedModeWork

/-! Exact finite completion of the literal block remainder. The discrete
cofactor interval is the same one used by the continuous main-term identity. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open Set
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace OuterBlockSharpCompletionWork
open OuterBlockMainTermWork OuterBlockCofactorWork OuterActiveDyadicWork
open OuterRectangularBlocksWork LongerTupleEncoding MellinWindowFactor
open Erdos374.HarmanGram152

def completedCount (X s L R : ℝ) (i j : ℕ) (k : BlockKey) (ω : Fin 9→ℝ) : ℂ :=
  ∑r∈blockSource X k,∑n∈Finset.Ioc (lower X k) (upper X k),
    if L<((index r*n:ℕ):ℝ) ∧ ((index r*n:ℕ):ℝ)≤R then modeWeight X s i j ω r else 0

def completedPolynomial (X s σ t : ℝ) (i j : ℕ) (k : BlockKey) (ω : Fin 9→ℝ) : ℂ :=
  ∑r∈blockSource X k,∑n∈Finset.Ioc (lower X k) (upper X k),
    modeWeight X s i j ω r*((index r*n:ℕ):ℂ)^(-line σ t)

theorem polynomial_factorization (X s σ t : ℝ) (i j : ℕ) (k : BlockKey) (ω : Fin 9→ℝ) :
    completedPolynomial X s σ t i j k ω = modePolynomial X s i j k ω σ t *
      verticalDirichlet152 (Finset.Ioc (lower X k) (upper X k)) (fun _ => 1) σ t := by
  unfold completedPolynomial modePolynomial verticalDirichlet152
  simp only [Finset.sum_mul,Finset.mul_sum,one_mul,OuterNormalizedModeWork.nat_mul_cpow]
  rw [Finset.sum_comm (s:=Finset.Ioc (lower X k) (upper X k)) (t:=blockSource X k)]
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro n hn
  dsimp only [line]
  ring

theorem floor_coverage (X x δ : ℝ) (k : BlockKey) (m : ℕ)
    (hX : 0<X) (hx : x∈Icc X (2*X)) (hδ : δ∈Icc 0 (1/2))
    (hm : scale k≤m ∧ m≤16*scale k) :
    lower X k≤⌊(x-x*δ)/(m:ℝ)⌋₊ ∧ ⌊x/(m:ℝ)⌋₊≤upper X k := by
  have hxp : 0<x := hX.trans_le hx.1
  have hleft : 0<x-x*δ := by
    have := (DyadicDivisorWindow.window_bounds X x δ hX hx hδ).1
    linarith
  have hmp : (0:ℝ)<m := by exact_mod_cast (scale_pos k).trans_le hm.1
  have hg := margins X x δ (1/8) k m hX hx hδ (by constructor <;> norm_num) hm
  have hl2 : 0≤Real.log 2 := Real.log_nonneg (by norm_num)
  constructor
  · apply (Nat.le_floor_iff (by positivity : 0≤(x-x*δ)/(m:ℝ))).mpr
    apply (le_div_iff₀ hmp).mpr
    have hh : (m:ℝ)*lower X k/(x-x*δ)≤1 := by linarith [hg.2.1]
    have hh' := (div_le_one hleft).mp hh
    nlinarith
  · have hh : 1≤(m:ℝ)*upper X k/x := by linarith [hg.2.2.1]
    have hh' := (le_div_iff₀ hxp).mp hh
    have hu : x/(m:ℝ)≤upper X k := (div_le_iff₀ hmp).mpr (by nlinarith)
    exact_mod_cast (Nat.floor_le (by positivity : 0≤x/(m:ℝ))).trans hu

theorem blockModeSum_eq_completed (X s x δ : ℝ) (i j : ℕ) (k : BlockKey) (ω : Fin 9→ℝ)
    (hX : 2≤X) (hx : x∈Icc X (2*X)) (hδ : δ∈Icc 0 (1/2)) :
    OuterBlockIntegralWork.blockModeSum X s (x-x*δ) x i j k ω =
      completedCount X s (x-x*δ) x i j k ω-((x*δ:ℝ):ℂ)*mainMass X s i j k ω := by
  rw [blockModeSum_centering]
  have hleft : 0≤x-x*δ := by
    have := (DyadicDivisorWindow.window_bounds X x δ (by linarith) hx hδ).1
    linarith
  have hleftx : x-x*δ≤x := by
    have hxp : 0<x := by linarith [hx.1]
    nlinarith [hδ.1]
  have hsum : (∑r∈blockSource X k,modeWeight X s i j ω r*
      (((⌊x/(index r:ℝ)⌋₊:ℝ)-(⌊(x-x*δ)/(index r:ℝ)⌋₊:ℝ)):ℂ)) =
      completedCount X s (x-x*δ) x i j k ω := by
    apply Finset.sum_congr rfl
    intro r hr
    have hm := index_range X hX k r hr
    have hf := floor_coverage X x δ k (index r) (by linarith) hx hδ ⟨hm.1,hm.2.le⟩
    have hc := HarmanDivisorWindow.cofactor_count (index r) (lower X k) (upper X k)
      (x-x*δ) x 1 ((scale_pos k).trans_le hm.1) hleft hleftx hf.1 hf.2
    have hcC := congrArg (fun z : ℝ => (z:ℂ)) hc
    simp only [one_mul,Complex.ofReal_sum,Complex.ofReal_sub,Complex.ofReal_natCast,
      apply_ite,Complex.ofReal_one,Complex.ofReal_zero] at hcC
    simp only [Complex.ofReal_sub,Complex.ofReal_natCast]
    rw [hcC,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    split_ifs <;> simp
  rw [hsum,show x-(x-x*δ)=x*δ by ring]

theorem centered_completion_error (X s x δ ε σ C : ℝ) (i j : ℕ) (k : BlockKey) (ω : Fin 9→ℝ)
    (hX : 2≤X) (hx : x∈Icc X (2*X)) (hδ : δ∈Icc 0 (1/2))
    (hε : ε∈Ioo 0 (1/4)) (hσ : 1<σ) (hσ2 : σ≤2) (hscale : 256*(scale k:ℝ)≤X)
    (hclose : ‖mellin (fun y => (Smooth1 MellinSmoothingFunction.smoothing ε y:ℂ)) 1-1‖≤C*ε) :
    ‖OuterBlockIntegralWork.blockModeSum X s (x-x*δ) x i j k ω-
      (completedCount X s (x-x*δ) x i j k ω-continuousContour X s x δ ε σ i j k ω)‖≤C*ε*(x*δ) := by
  rw [blockModeSum_eq_completed X s x δ i j k ω hX hx hδ]
  have he (a b c : ℂ) : a-b-(a-c)=c-b := by ring
  rw [he]
  exact OuterBlockMassBudgetWork.smoothing_error X s x δ ε σ C i j k ω
    hX hx hδ hε hσ hσ2 hscale hclose

run_cmd do
  for decl in [``polynomial_factorization, ``floor_coverage, ``blockModeSum_eq_completed,
      ``centered_completion_error] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end OuterBlockSharpCompletionWork
