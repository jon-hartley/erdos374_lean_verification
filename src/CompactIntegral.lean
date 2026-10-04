import Erdos374_Update152

/-!
Compact-interval integral helpers and a continuous analogue of the seed's
finite exponential mean-square expansion. These are used to prove the
Mellin mean-square transfer in the short-interval argument.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open MeasureTheory Set
open scoped ComplexConjugate

namespace CompactIntegral

theorem integral_swap {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (a b c d : ℝ) (f : ℝ → ℝ → E)
    (hf : Continuous f.uncurry) :
    (∫ x in Icc a b, ∫ y in Icc c d, f x y) =
      ∫ y in Icc c d, ∫ x in Icc a b, f x y := by
  apply integral_integral_swap
  rw [Measure.prod_restrict]
  exact hf.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)

theorem continuous_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (a b : ℝ) (f : ℝ → ℝ → E)
    (hf : Continuous f.uncurry) :
    Continuous (fun x => ∫ y in Icc a b, f x y) :=
  continuous_parametric_integral_of_continuous hf isCompact_Icc

def transform (K : ℝ → ℝ → ℂ) (g : ℝ → ℂ) (a b x : ℝ) : ℂ :=
  ∫ t in Icc a b, g t * K x t

def correlation (K : ℝ → ℝ → ℂ) (c d t u : ℝ) : ℂ :=
  ∫ x in Icc c d, K x t * conj (K x u)

theorem continuous_transform (K : ℝ → ℝ → ℂ) (g : ℝ → ℂ) (a b : ℝ)
    (hK : Continuous K.uncurry) (hg : Continuous g) :
    Continuous (transform K g a b) := by
  apply continuous_integral
  fun_prop

theorem continuous_correlation (K : ℝ → ℝ → ℂ) (c d : ℝ)
    (hK : Continuous K.uncurry) :
    Continuous (correlation K c d).uncurry := by
  exact continuous_parametric_integral_of_continuous (by fun_prop) isCompact_Icc

theorem norm_square_expansion (K : ℝ → ℝ → ℂ) (g : ℝ → ℂ) (a b x : ℝ) :
    ((‖transform K g a b x‖ ^ 2 : ℝ) : ℂ) =
      ∫ t in Icc a b, ∫ u in Icc a b,
        g t * conj (g u) * (K x t * conj (K x u)) := by
  rw [Complex.ofReal_pow, ← Complex.mul_conj']
  unfold transform
  rw [← integral_conj, ← integral_mul_const]
  apply integral_congr_ae
  filter_upwards with t
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with u
  simp only [map_mul]
  ring

theorem mean_square_expansion (K : ℝ → ℝ → ℂ) (g : ℝ → ℂ) (a b c d : ℝ)
    (hK : Continuous K.uncurry) (hg : Continuous g) :
    ((∫ x in Icc c d, ‖transform K g a b x‖ ^ 2 : ℝ) : ℂ) =
      ∫ t in Icc a b, ∫ u in Icc a b,
        g t * conj (g u) * correlation K c d t u := by
  rw [← integral_complex_ofReal]
  simp_rw [norm_square_expansion]
  rw [integral_swap c d a b
    (fun x t => ∫ u in Icc a b, g t * conj (g u) * (K x t * conj (K x u)))
    (continuous_parametric_integral_of_continuous (by fun_prop) isCompact_Icc)]
  apply integral_congr_ae
  filter_upwards with t
  rw [integral_swap c d a b
    (fun x u => g t * conj (g u) * (K x t * conj (K x u))) (by fun_prop)]
  apply integral_congr_ae
  filter_upwards with u
  exact integral_const_mul _ _

end CompactIntegral

#print axioms CompactIntegral.mean_square_expansion
run_cmd do
  for target in [``CompactIntegral.integral_swap,
      ``CompactIntegral.continuous_transform,
      ``CompactIntegral.continuous_correlation,
      ``CompactIntegral.norm_square_expansion,
      ``CompactIntegral.mean_square_expansion] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "COMPACT INTEGRAL PASSED"
