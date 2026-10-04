import OuterSharpContourWork
import OuterCompletedRemainderWork

/-! Frequency integrability of the completed sharp and smoothed counts. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace OuterSharpContourRegularityWork
open OuterSharpContourWork OuterCompletedCollectionWork OuterBlockMainTermWork
open OuterBlockSharpCompletionWork OuterSourceCubeIntegralWork OuterActiveDyadicWork
open OuterMainCorrectionWork OuterCompletedRemainderWork Erdos374.HarmanGram152
open MellinWindowFactor MellinSmoothingFunction

def singleKernel (x δ ε σ : ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  (n:ℂ)^(-line σ t)*mellin (fun u => (Smooth1 smoothing ε u:ℂ)) (line σ t)*
    ((x:ℂ)^line σ t-((x-x*δ:ℝ):ℂ)^line σ t)

theorem single_integrable (x δ ε σ : ℝ) (n : ℕ)
    (hx : 0<x) (hl : 0<x-x*δ) (hn : 0<n) (hσ : 1<σ) (hσ2 : σ≤2) (hε : ε∈Ioo 0 1) :
    Integrable (singleKernel x δ ε σ n) := by
  have hh := FiniteWindowFrequencySplit.integrable_kernel {n} (fun _ => 1)
    ε σ δ x hx hl (by simpa) hσ hσ2 hε
  unfold singleKernel
  simpa only [verticalDirichlet152,Finset.sum_singleton,Complex.ofReal_one,one_mul,line] using hh

theorem discrete_sum (X s x δ : ℝ) (i j : ℕ) (k : BlockKey) (ω : Fin 9→ℝ)
    (hX : Real.exp 1≤X) (hX2 : 2≤X) (hx : x∈Icc X (2*X)) (hδ : δ∈Icc 0 (1/2)) :
    discreteContour X s x δ i j k ω =
      ∑a∈entries X k,weights X s i j ω a*
        (((1/(2*Real.pi):ℝ):ℂ)*∫t in Icc (-X) X,
          singleKernel x δ (X^(-19/20:ℝ)) (1+1/Real.log X) (product a) t) := by
  have hXp : 0<X := (Real.exp_pos 1).trans_le hX
  have hxp : 0<x := hXp.trans_le hx.1
  have hl : 0<x-x*δ := by nlinarith [hδ.2]
  have hlog : 1≤Real.log X := by simpa using Real.log_le_log (Real.exp_pos 1) hX
  have hσ : 1<1+1/Real.log X := by
    have : 0<1/Real.log X := by positivity
    linarith
  have hσ2 : 1+1/Real.log X≤2 := by
    have := (div_le_one (by linarith : 0<Real.log X)).mpr hlog
    linarith
  have hε : X^(-19/20:ℝ)∈Ioo 0 1 := ⟨by positivity,
    Real.rpow_lt_one_of_one_lt_of_neg ((Real.one_lt_exp_iff.mpr (by norm_num)).trans_le hX) (by norm_num)⟩
  have hp (a : Entry) (ha : a∈entries X k) : 0<product a := by
    obtain ⟨hr,hn⟩ := Finset.mem_product.mp ha
    exact Nat.mul_pos
      (OuterAmbientSizeWork.ambient_index_pos X hX2 a.1 (Finset.mem_filter.mp hr).1)
      (by have := (Finset.mem_Ioc.mp hn).1; omega)
  have hi (a : Entry) (ha : a∈entries X k) : IntegrableOn
      (singleKernel x δ (X^(-19/20:ℝ)) (1+1/Real.log X) (product a)) (Icc (-X) X) :=
    (single_integrable x δ (X^(-19/20:ℝ)) (1+1/Real.log X) (product a) hxp hl (hp a ha) hσ hσ2 hε).integrableOn
  have he (t : ℝ) : completedPolynomial X s (1+1/Real.log X) t i j k ω *
      mellin (fun u => (Smooth1 smoothing (X^(-19/20:ℝ)) u:ℂ)) (line (1+1/Real.log X) t)*
      ((x:ℂ)^line (1+1/Real.log X) t-((x-x*δ:ℝ):ℂ)^line (1+1/Real.log X) t) =
      ∑a∈entries X k,weights X s i j ω a*singleKernel x δ (X^(-19/20:ℝ)) (1+1/Real.log X) (product a) t := by
    simp only [completedPolynomial,entries,Finset.sum_product,Finset.sum_mul,weights,product,singleKernel]
    apply Finset.sum_congr rfl
    intro r hr
    apply Finset.sum_congr rfl
    intro n hn
    ring
  unfold discreteContour SmoothedWindowTransfer.transform
  simp_rw [he]
  rw [integral_finsetSum _ (fun a ha => (hi a ha).const_mul _)]
  simp only [integral_const_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  ring

theorem density_discrete_integrable (X s x δ T : ℝ) (i j : ℕ) (k : BlockKey)
    (hX : Real.exp 1≤X) (hX2 : 2≤X) (hx : x∈Icc X (2*X)) (hδ : δ∈Icc 0 (1/2)) :
    Integrable (fun ω => density X s i j ω*discreteContour X s x δ i j k ω) (frequencyCube T) := by
  simp_rw [discrete_sum X s x δ i j k _ hX hX2 hx hδ,Finset.mul_sum]
  apply integrable_finsetSum
  intro a ha
  have hiw : Integrable (fun ω => density X s i j ω*weights X s i j ω a) (frequencyCube T) := by
    unfold weights modeWeight
    have hh := (mode_integrable X s T i j
      (OuterSmoothStepWork.signedGap (Real.log (a.1.1:ℝ))
        (OuterBufferedSourceWork.cutoffLogs X s (OuterSourceReindexWork.drop a.1) i j))).const_mul
        (OuterSmoothCoreWork.atomMultiplier X s i j a.1:ℂ)
    convert hh using 1
    funext ω
    simp only [OuterSeparatedFourierModeWork.sourceMode]
    ring
  simpa only [mul_assoc] using hiw.mul_const
    (((1/(2*Real.pi):ℝ):ℂ)*∫t in Icc (-X) X,
      singleKernel x δ (X^(-19/20:ℝ)) (1+1/Real.log X) (product a) t)

theorem density_count_integrable (X s x δ T : ℝ) (i j : ℕ) (k : BlockKey)
    (hX : 2≤X) (hx : x∈Icc X (2*X)) (hδ : δ∈Icc 0 (1/2)) :
    Integrable (fun ω => density X s i j ω*completedCount X s (x-x*δ) x i j k ω) (frequencyCube T) := by
  have he (ω : Fin 9→ℝ) : density X s i j ω*completedCount X s (x-x*δ) x i j k ω =
      density X s i j ω*OuterBlockIntegralWork.blockModeSum X s (x-x*δ) x i j k ω+
      ((x*δ:ℝ):ℂ)*(density X s i j ω*mainMass X s i j k ω) := by
    rw [blockModeSum_eq_completed X s x δ i j k ω hX hx hδ]
    ring
  simp_rw [he]
  exact (density_block_integrable X s (x-x*δ) x T i j k).add
    ((density_mass_integrable X s T i j k).const_mul _)

run_cmd do
  for decl in [``single_integrable, ``discrete_sum, ``density_discrete_integrable, ``density_count_integrable] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end OuterSharpContourRegularityWork
