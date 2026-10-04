import Item1SubsetSourceMoments
import Item1AllFrequencyMerge
import SourceFirstFactorSaving

/-! UNCOMPILED. A fully supplied cap-to-middle draft from available source.
It uses the retained 16-region certificate and log^18 moments. Its stronger
UNNORMALIZED first-prime cap is (1+log X)^(-26000), not the newer normalized
1024 cap. The newer 1024 route remains valid at its recorded conditional status.
No moment/certificate/prime-middle estimate is taken as a theorem parameter.
-/
set_option autoImplicit false
set_option maxHeartbeats 24000000
set_option exponentiation.threshold 512
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators
namespace Item1RetainedMomentMiddle
open Item1SubsetSourceMoments Item1PrimeLowSpectrum SourceLiteralMiddle
open SourceMassDischarge Item1AllFrequencyMerge Item1SourceLocalArithmetic
open Item1PhysicalDeletion PositiveInteriorModel PositiveInteriorCells
open PositiveSharpMovingWindow

/-- Explicit remaining pointwise condition for this alternative route. -/
def StrongFirstCap (X : ℝ) (K : ℕ) : Prop :=
  ∀ j ∈ boxes (mesh X), ∀ t ∈ middle X (lowCut X K),
    ‖primeFactor X j 0 t‖ ≤ (1+Real.log X)^(-26000:ℝ)

/-- One cap, three internally instantiated prime-support moments. -/
theorem cell_middle_of_cap (X T0 : ℝ) (j : ℕ × ℕ)
    (hX : 2 ≤ X) (hlog : 1000000 ≤ Real.log X) (hj : j ∈ boxes (mesh X))
    (hsmall : ∀ t ∈ middle X T0,
      ‖primeFactor X j 0 t‖ ≤ (1+Real.log X)^(-26000:ℝ)) :
    (∫ t in middle X T0, ‖primeProduct X j t‖^2) ≤
      3*commonConstant/(1+Real.log X)^34 := by
  obtain ⟨β,hβ,hS,hm⟩ := actual_prime_moments X j hX hlog hj
  let L := 1+Real.log X
  let μ : Measure ℝ := volume.restrict (middle X T0)
  let a : Fin 3 → ℝ → ℝ := fun i t => ‖primeFactor X j i t‖
  have hL : 1 ≤ L := by
    dsimp [L]
    linarith [Real.log_nonneg (show 1 ≤ X by linarith)]
  have hLp : 0 < L := by linarith
  have hsub := middle_subset X T0
  have hc (i : Fin 3) : Continuous (fun t => a i t^(β i)) :=
    (prime_continuous X j i).norm.rpow_const (fun _ => Or.inr (by linarith [hβ i]))
  have hi (i : Fin 3) : Integrable (fun t => a i t^(β i)) μ :=
    (hc i).integrableOn_Icc.mono_set hsub
  have hb (i : Fin 3) : (∫ t, a i t^(β i) ∂μ) ≤ commonConstant*L^18 := by
    have hh := setIntegral_mono_set (μ := volume) (hc i).integrableOn_Icc
      (Filter.Eventually.of_forall (fun t => Real.rpow_nonneg (norm_nonneg _) _))
      (Filter.Eventually.of_forall hsub)
    exact hh.trans (hm i)
  have hmeas : AEStronglyMeasurable (fun t => (a 0 t*a 1 t*a 2 t)^2) μ :=
    ((((prime_continuous X j 0).norm.mul (prime_continuous X j 1).norm).mul
      (prime_continuous X j 2).norm).pow 2).aestronglyMeasurable
  have hsmallAE : ∀ᵐ t ∂μ, a 0 t ≤ L^(-26000:ℝ) := by
    filter_upwards [ae_restrict_mem (middle_measurable X T0)] with t ht
    exact hsmall t ht
  have hcall := SourceFirstFactorSaving.integral_of_cap μ (a 0) (a 1) (a 2)
    (β 0) (β 1) (β 2) (L^(-26000:ℝ)) (commonConstant*L^18)
    (fun t => norm_nonneg _) (fun t => norm_nonneg _) (fun t => norm_nonneg _)
    (hβ 0) (hβ 1) (hβ 2) hS (cap_bounds L hL).1 (cap_bounds L hL).2
    hsmallAE (hi 0) (hi 1) (hi 2) hmeas (hb 0) (hb 1) (hb 2)
  rw [SourceFirstFactorSaving.log_budget L commonConstant hLp] at hcall
  simpa only [primeProduct,norm_mul,a,μ,L] using hcall

/-- This counts actual moving cells, never the 253 fixed hosts. -/
theorem prime_middle_rate (X : ℝ) (K : ℕ) (hX : 2 ≤ X)
    (hlog : 1000000 ≤ Real.log X) (hm : mesh X ≤ 1/1000000)
    (hcap : StrongFirstCap X K) :
    primeMiddle X K ≤ 3*commonConstant/(1+Real.log X)^32 := by
  have he : 0 < Real.log X := by linarith
  have hL : 0 < 1+Real.log X := by linarith
  have hsum := Finset.sum_le_sum (fun j hj =>
    cell_middle_of_cap X (lowCut X K) j hX hlog hj (hcap j hj))
  have hs : primeMiddle X K ≤ ((boxes (mesh X)).card:ℝ)*
      (3*commonConstant/(1+Real.log X)^34) := by
    simpa only [primeMiddle,Finset.sum_const,nsmul_eq_mul] using hsum
  have hcard0 := cell_card_normalized_bound X (by linarith) hm
  have hcard : ((boxes (mesh X)).card:ℝ) ≤ (1+Real.log X)^2 := by
    have hx := (div_le_iff₀ (sq_pos_of_pos he)).mp hcard0
    nlinarith [sq_nonneg (Real.log X)]
  have hc := commonConstant_nonneg
  calc
    _ ≤ ((boxes (mesh X)).card:ℝ)*(3*commonConstant/(1+Real.log X)^34) := hs
    _ ≤ (1+Real.log X)^2*(3*commonConstant/(1+Real.log X)^34) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = 3*commonConstant/(1+Real.log X)^32 := by
      field_simp <;> ring

/-- One crude common threshold absorbs the fixed, possibly enormous constant. -/
theorem retained_rate_small (L C : ℝ) (hL : 1 ≤ L) (hC : 0 ≤ C)
    (hlarge : 24576*C ≤ L) : 3*C/L^32 ≤ 1/8192 := by
  have hpow : L ≤ L^32 := by
    simpa only [pow_one] using pow_le_pow_right₀ hL (by norm_num : 1 ≤ 32)
  apply (div_le_div_iff₀ (by positivity : 0 < L^32)
    (by norm_num : (0:ℝ) < 8192)).mpr
  nlinarith

/-- Finite evaluation of the already-defined inherited constant. -/
theorem common_constant_le : commonConstant ≤ (2:ℝ)^278 := by
  norm_num [commonConstant, SourceLogMoment.momentConstant,
    SourceLogMoment.secondConstant, SourceLogMoment.quadraticConstant,
    SourceLogMoment.sexticConstant, SourceLogMoment.energyConstant,
    SourceLogMoment.cap, SourceLogMoment.zeta, Finset.sum_range_succ]

/-- Even the existing geometric guard absorbs the inherited fixed constant. -/
theorem rate_at_geometry_guard (L : ℝ) (hL : 1000000 ≤ L) :
    3*commonConstant/L^32 ≤ 1/8192 := by
  have hp : (1000000:ℝ)^32 ≤ L^32 := pow_le_pow_left₀ (by norm_num) hL 32
  have hc := common_constant_le
  have hn : (3:ℝ)*(2:ℝ)^278*8192 ≤ (1000000:ℝ)^32 := by norm_num
  apply (div_le_div_iff₀ (by positivity : 0 < L^32)
    (by norm_num : (0:ℝ) < 8192)).mpr
  calc
    3*commonConstant*8192 ≤ 3*(2:ℝ)^278*8192 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc (by norm_num)) (by norm_num)
    _ ≤ (1000000:ℝ)^32 := hn
    _ ≤ 1*L^32 := by simpa only [one_mul] using hp

/-- The quantitative prime-middle premise is proved FROM the explicit cap.
There is no presumed cap-to-middle implication supplied by the caller. -/
theorem prime_middle_budget_of_cap (K : ℕ)
    (hcap : ∀ᶠ X : ℝ in atTop, StrongFirstCap X K) : PrimeMiddleBudget K := by
  filter_upwards [hcap,eventually_geometry] with X hcap hg
  exact (prime_middle_rate X K hg.1 hg.2.1 hg.2.2 hcap).trans
    (rate_at_geometry_guard (1+Real.log X) (by linarith [hg.2.1]))


end Item1RetainedMomentMiddle

-- ROOT SOURCE RECURSIVE AUDIT: exact original declarations.
run_cmd do
  for target in [
    ``Item1RetainedMomentMiddle.cell_middle_of_cap,
    ``Item1RetainedMomentMiddle.prime_middle_rate,
    ``Item1RetainedMomentMiddle.retained_rate_small,
    ``Item1RetainedMomentMiddle.common_constant_le,
    ``Item1RetainedMomentMiddle.rate_at_geometry_guard,
    ``Item1RetainedMomentMiddle.prime_middle_budget_of_cap] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "Item1RetainedMomentMiddle: 6 original theorem guards passed."
