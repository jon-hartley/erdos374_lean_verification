import OuterBlockCofactorWork
import OuterBlockIntegralWork
import CofactorMainTermBudget
import LongerTupleCollection

/-! Exact continuous main-mass normalization for the literal source modes
inside rectangular blocks. All signed atoms, masks and Fourier phases remain. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace OuterBlockMainTermWork
open OuterBlockCofactorWork OuterActiveDyadicWork OuterRectangularBlocksWork
open OuterSourceReindexWork OuterSmoothCoreWork OuterSeparatedFourierModeWork
open LongerTupleEncoding MellinWindowFactor ContinuousCofactorMellin
open Erdos374.HarmanGram152 MellinSmoothingFunction

def modeWeight (X s : ℝ) (i j : ℕ) (ω : Fin 9→ℝ) (r : Representation) : ℂ :=
  (atomMultiplier X s i j r:ℂ)*sourceMode X s i j (drop r).1 r.1 (drop r).2.1 (drop r).2.2 ω

def modePolynomial (X s : ℝ) (i j : ℕ) (k : BlockKey) (ω : Fin 9→ℝ) (σ t : ℝ) : ℂ :=
  ∑r∈blockSource X k, modeWeight X s i j ω r*(index r:ℂ)^(-line σ t)

def mainMass (X s : ℝ) (i j : ℕ) (k : BlockKey) (ω : Fin 9→ℝ) : ℂ :=
  ∑r∈blockSource X k, modeWeight X s i j ω r/(index r:ℂ)

def continuousContour (X s x δ ε σ : ℝ) (i j : ℕ) (k : BlockKey) (ω : Fin 9→ℝ) : ℂ :=
  ((1/(2*Real.pi):ℝ):ℂ)*∫t : ℝ, modePolynomial X s i j k ω σ t *
    cofactor (lower X k) (upper X k) (line σ t) *
    mellin (fun y => (Smooth1 smoothing ε y:ℂ)) (line σ t) *
    ((x:ℂ)^line σ t-((x-x*δ:ℝ):ℂ)^line σ t)

theorem finite_contour_eq (X x δ ε σ : ℝ) (k : BlockKey)
    (S : Finset ℕ) (c : ℕ→ℂ) (hX : 0<X) (hx : x∈Icc X (2*X))
    (hδ : δ∈Icc 0 (1/2)) (hε : ε∈Ioo 0 (1/4)) (hσ : 1<σ) (hσ2 : σ≤2)
    (hlo : 1≤lower X k) (hS : ∀m∈S,scale k≤m ∧ m≤16*scale k) :
    ((1/(2*Real.pi):ℝ):ℂ)*(∫t : ℝ, verticalDirichlet152 S c σ t *
      cofactor (lower X k) (upper X k) (line σ t) *
      mellin (fun y => (Smooth1 smoothing ε y:ℂ)) (line σ t) *
      ((x:ℂ)^line σ t-((x-x*δ:ℝ):ℂ)^line σ t)) =
    ((x*δ:ℝ):ℂ)*mellin (fun y => (Smooth1 smoothing ε y:ℂ)) 1 *
      (∑m∈S,c m/(m:ℂ)) := by
  have hxp : 0<x := hX.trans_le hx.1
  have hleft : 0<x-x*δ := by
    have := (DyadicDivisorWindow.window_bounds X x δ hX hx hδ).1
    linarith
  have hlow : (0:ℝ)<lower X k := by exact_mod_cast (show 0<lower X k by omega)
  have hlu : (lower X k:ℝ)≤upper X k := by exact_mod_cast lower_le_upper X k hX
  have hpos : ∀m∈S,0<m := fun m hm => (scale_pos k).trans_le (hS m hm).1
  have hε1 : ε∈Ioo (0:ℝ) 1 := ⟨hε.1,by linarith [hε.2]⟩
  have hm (m : ℕ) (h : m∈S) := margins X x δ ε k m hX hx hδ hε (hS m h)
  have hmain := finite_continuous_main_term S c smoothing ε x (x-x*δ)
    (lower X k) (upper X k) hxp hleft hlow hlu hpos hε1 differentiable
    nonnegative support mass_one (fun m h => (hm m h).1) (fun m h => (hm m h).2.1)
    (fun m h => (hm m h).2.2.1) (fun m h => (hm m h).2.2.2)
  rw [finite_short_window_integrand S c smoothing ε σ x (x-x*δ)
    (lower X k) (upper X k) hxp hleft hlow hlu hpos hσ hσ2 hε1
    differentiable nonnegative support mass_one] at hmain
  simpa only [show x-(x-x*δ)=x*δ by ring] using hmain

theorem polynomial_collected (X s σ t : ℝ) (i j : ℕ) (k : BlockKey) (ω : Fin 9→ℝ) :
    modePolynomial X s i j k ω σ t =
      verticalDirichlet152 (LongerTupleCollection.support (blockSource X k) index)
        (LongerTupleCollection.coefficient (blockSource X k) index (modeWeight X s i j ω)) σ t := by
  exact (LongerTupleCollection.grouped_sum (blockSource X k) index (modeWeight X s i j ω)
    (fun n => (n:ℂ)^(-line σ t))).symm

theorem mass_collected (X s : ℝ) (i j : ℕ) (k : BlockKey) (ω : Fin 9→ℝ) :
    (∑n∈LongerTupleCollection.support (blockSource X k) index,
      LongerTupleCollection.coefficient (blockSource X k) index (modeWeight X s i j ω) n/(n:ℂ)) =
      mainMass X s i j k ω := by
  simpa only [mainMass,div_eq_mul_inv] using
    LongerTupleCollection.grouped_sum (blockSource X k) index (modeWeight X s i j ω)
      (fun n => (n:ℂ)⁻¹)

theorem continuousContour_eq (X s x δ ε σ : ℝ) (i j : ℕ) (k : BlockKey) (ω : Fin 9→ℝ)
    (hX : 2≤X) (hx : x∈Icc X (2*X)) (hδ : δ∈Icc 0 (1/2))
    (hε : ε∈Ioo 0 (1/4)) (hσ : 1<σ) (hσ2 : σ≤2) (hscale : 256*(scale k:ℝ)≤X) :
    continuousContour X s x δ ε σ i j k ω =
      ((x*δ:ℝ):ℂ)*mellin (fun y => (Smooth1 smoothing ε y:ℂ)) 1 * mainMass X s i j k ω := by
  unfold continuousContour
  simp_rw [polynomial_collected]
  rw [finite_contour_eq X x δ ε σ k _ _ (by linarith) hx hδ hε hσ hσ2
    (lower_pos X k hscale) (by
      intro m hm
      obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hm
      exact ⟨(index_range X hX k r hr).1,(index_range X hX k r hr).2.le⟩),mass_collected]

theorem blockModeSum_centering (X s L R : ℝ) (i j : ℕ) (k : BlockKey) (ω : Fin 9→ℝ) :
    OuterBlockIntegralWork.blockModeSum X s L R i j k ω =
      (∑r∈blockSource X k, modeWeight X s i j ω r *
        (((⌊R/(index r:ℝ)⌋₊:ℝ)-(⌊L/(index r:ℝ)⌋₊:ℝ)):ℂ)) -
        ((R-L:ℝ):ℂ)*mainMass X s i j k ω := by
  unfold OuterBlockIntegralWork.blockModeSum mainMass
  rw [Finset.mul_sum,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  simp only [UpperAfter545Remaining.floorKernel,Complex.ofReal_mul,Complex.ofReal_sub,
    Complex.ofReal_div,Complex.ofReal_natCast,modeWeight]
  ring

run_cmd do
  for decl in [``finite_contour_eq, ``polynomial_collected, ``mass_collected,
      ``continuousContour_eq, ``blockModeSum_centering] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end OuterBlockMainTermWork
