import SourceAbelLow
import Mathlib.Tactic

/-! Exact half-integer Abel endpoints for the literal Ico block.
This file proves finite identities and a conditional LOCAL psi-to-twist bound.
It neither supplies nor assumes a polynomial-height prime cap. -/
set_option autoImplicit false
set_option maxHeartbeats 18000000
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Item1ExactFirstBlock
open SourceAbelLow SourceReferenceSigmaOne SourceMassDischarge
open MellinWindowFactor ContinuousCofactorMellin
open Erdos374.HarmanGram152 Erdos374.PositiveInteriorMass
open Erdos374.WeightedPrimeSampling151

def left (N : ℕ) : ℝ := (N:ℝ)-1/2
def right (N : ℕ) : ℝ := 2*(N:ℝ)-1/2
def block (N : ℕ) (t : ℝ) : ℂ :=
  verticalDirichlet152 (Finset.Ico N (2*N)) mangoldt 1 t

theorem floor_half_pred (N : ℕ) (hN : 1≤N) :
    ⌊(N:ℝ)-(1:ℝ)/2⌋₊=N-1 := by
  have hNr : (1:ℝ)≤N := by exact_mod_cast hN
  have hnon : 0≤(N:ℝ)-(1:ℝ)/2 := by linarith
  have hl : N-1≤⌊(N:ℝ)-(1:ℝ)/2⌋₊ := Nat.le_floor (by
    rw [Nat.cast_sub hN]
    norm_num
    linarith)
  have hu : ⌊(N:ℝ)-(1:ℝ)/2⌋₊<N := by
    by_contra hc
    have hcR : (N:ℝ)≤(⌊(N:ℝ)-(1:ℝ)/2⌋₊:ℝ) := by
      exact_mod_cast (le_of_not_gt hc)
    have hh := Nat.floor_le hnon
    linarith
  omega

/-- No endpoint Mangoldt weights are thrown away. -/
theorem exact_support (N : ℕ) (hN : 1≤N) :
    Finset.Ioc ⌊left N⌋₊ ⌊right N⌋₊=Finset.Ico N (2*N) := by
  have h2 : 1≤2*N := by omega
  have ha : ⌊left N⌋₊=N-1 := floor_half_pred N hN
  have hb : ⌊right N⌋₊=2*N-1 := by
    simpa [right, Nat.cast_mul] using floor_half_pred (2*N) h2
  rw [ha,hb]
  ext n
  simp only [Finset.mem_Ioc, Finset.mem_Ico]
  omega

theorem endpoint_geometry (N : ℕ) (hN : 1≤N) :
    0<left N ∧ left N≤right N ∧ 1≤right N/left N ∧ right N/left N≤4 := by
  have hNr : (1:ℝ)≤N := by exact_mod_cast hN
  have ha : 0<left N := by dsimp [left]; linarith
  have hab : left N≤right N := by dsimp [left,right]; linarith
  refine ⟨ha,hab,?_,?_⟩
  · exact (one_le_div ha).mpr hab
  · apply (div_le_iff₀ ha).mpr
    dsimp [left,right]
    linarith

theorem log_ratio_bounds (N : ℕ) (hN : 1≤N) :
    0≤Real.log (right N/left N) ∧ Real.log (right N/left N)≤2 := by
  obtain ⟨ha,hab,hlo,hhi⟩ := endpoint_geometry N hN
  have hlog4 : Real.log (4:ℝ)≤2 := by
    have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    rw [show (4:ℝ)=2^2 by norm_num, Real.log_pow]
    norm_num at *
    linarith
  exact ⟨Real.log_nonneg hlo,
    (Real.log_le_log (by linarith : 0<right N/left N) hhi).trans hlog4⟩

/-- The exact Ico polynomial, expressed in the form consumed by relative_abel. -/
theorem abel_sum_eq_block (N : ℕ) (hN : 1≤N) (t : ℝ) :
    (∑ n∈Finset.Ioc ⌊left N⌋₊ ⌊right N⌋₊,
      test t n*mangoldtComplex n)=block N t := by
  rw [exact_support N hN]
  unfold block verticalDirichlet152
  apply Finset.sum_congr rfl
  intro n _
  unfold test mangoldtComplex mangoldt line
  push_cast
  ring

/-- Compact reference integral used solely in the Abel estimate.
This is not a change to the physical source's centering reference. -/
theorem abel_reference_eq (N : ℕ) (hN : 1≤N) (t : ℝ) :
    (∫ u in left N..right N, test t u)=cofactor (left N) (right N) (line 1 t) := by
  have hab := (endpoint_geometry N hN).2.1
  rw [intervalIntegral.integral_of_le hab, ←integral_Icc_eq_integral_Ioc]
  rfl

theorem block_norm_of_local_psi (N : ℕ) (hN : 1≤N) (t eps : ℝ)
    (heps : 0≤eps) (ht : t≠0)
    (hpsi : ∀ u∈Icc (left N) (right N), |Chebyshev.psi u-u|≤eps*u) :
    ‖block N t‖≤2/|t|+4*eps*(1+|t|) := by
  obtain ⟨ha,hab,_hlo,_hhi⟩ := endpoint_geometry N hN
  have haberr := relative_abel (left N) (right N) t eps ha hab heps hpsi
  rw [abel_sum_eq_block N hN t, abel_reference_eq N hN t] at haberr
  obtain ⟨hl0,hl2⟩ := log_ratio_bounds N hN
  have hl := mul_le_mul (line_norm_le t) hl2 hl0
    (show 0≤1+|t| by positivity)
  have herr : ‖block N t-cofactor (left N) (right N) (line 1 t)‖≤
      4*eps*(1+|t|) := by
    apply haberr.trans
    have hh : 2+‖line 1 t‖*Real.log (right N/left N)≤4*(1+|t|) := by
      nlinarith [abs_nonneg t]
    nlinarith [mul_le_mul_of_nonneg_left hh heps]
  have href := SourceReferenceSigmaOne.norm_le (left N) (right N) t ha hab ht
  have hh := norm_add_le (block N t-cofactor (left N) (right N) (line 1 t))
    (cofactor (left N) (right N) (line 1 t))
  rw [sub_add_cancel] at hh
  linarith

end Item1ExactFirstBlock

-- ROOT SOURCE RECURSIVE AUDIT: exact original declarations.
run_cmd do
  for target in [
    ``Item1ExactFirstBlock.floor_half_pred,
    ``Item1ExactFirstBlock.exact_support,
    ``Item1ExactFirstBlock.endpoint_geometry,
    ``Item1ExactFirstBlock.log_ratio_bounds,
    ``Item1ExactFirstBlock.abel_sum_eq_block,
    ``Item1ExactFirstBlock.abel_reference_eq,
    ``Item1ExactFirstBlock.block_norm_of_local_psi] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "Item1ExactFirstBlock: 7 original theorem guards passed."
