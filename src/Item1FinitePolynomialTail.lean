import Item1InheritedMeanSquare
import Item1CountableTail

/-!
UNCOMPILED PROOF-BODY DRAFT, October 2, 2026.
The mean-square inequality is CALLED from the retained original proof body.
It is not an assumption of the concluding infinite-tail theorem. Real
coefficients, rather than arbitrary complex coefficients, justify reflection.
The infinite assembly and its independent integrability are inherited from v8.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
noncomputable section
open MeasureTheory Set
open scoped BigOperators ComplexConjugate
namespace Item1FinitePolynomialTail
open Erdos374.HarmanAnalytic151MeanSquare Item1CountableTail

/-- The negative sign is the literal Mellin/Dirichlet convention. -/
def polynomial (s : Finset ℕ) (b : ℕ → ℝ) (t : ℝ) : ℂ :=
  exponentialSum151 s (fun n => (b n : ℂ)) (fun n => Real.log n) (-t)

def energy (s : Finset ℕ) (b : ℕ → ℝ) : ℝ := ∑ n ∈ s, (b n)^2

def rowCost (N : ℕ) : ℝ := 4*(N:ℝ)*(1+Real.log N)

theorem energy_nonneg (s : Finset ℕ) (b : ℕ → ℝ) : 0 ≤ energy s b :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem continuous_polynomial (s : Finset ℕ) (b : ℕ → ℝ) :
    Continuous (polynomial s b) :=
  (continuous_sum151 s (fun n => (b n : ℂ)) (fun n => Real.log n)).comp continuous_neg

theorem kernel_neg (w t : ℝ) :
    exponentialKernel151 w (-t) = conj (exponentialKernel151 w t) := by
  unfold exponentialKernel151
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.ofReal_neg]
  ring

theorem negative_eq_conj_positive (s : Finset ℕ) (b : ℕ → ℝ) (t : ℝ) :
    polynomial s b t =
      conj (exponentialSum151 s (fun n => (b n : ℂ)) (fun n => Real.log n) t) := by
  simp only [polynomial, exponentialSum151, map_sum, map_mul, kernel_neg,
    Complex.conj_ofReal]

theorem norm_eq_positive (s : Finset ℕ) (b : ℕ → ℝ) (t : ℝ) :
    ‖polynomial s b t‖ =
      ‖exponentialSum151 s (fun n => (b n : ℂ)) (fun n => Real.log n) t‖ := by
  rw [negative_eq_conj_positive, Complex.norm_conj]

theorem norm_even (s : Finset ℕ) (b : ℕ → ℝ) (t : ℝ) :
    ‖polynomial s b (-t)‖ = ‖polynomial s b t‖ := by
  rw [norm_eq_positive]
  rfl

theorem qualitative_cap (s : Finset ℕ) (b : ℕ → ℝ) (t : ℝ) :
    ‖polynomial s b t‖ ≤ ∑ n ∈ s, |b n| := by
  unfold polynomial exponentialSum151
  calc
    _ ≤ ∑ n ∈ s, ‖(b n : ℂ)*exponentialKernel151 (Real.log n) (-t)‖ := norm_sum_le _ _
    _ = _ := by simp only [norm_mul, norm_kernel151, mul_one,
      Complex.norm_real, Real.norm_eq_abs]

/-- Uses no prime-distribution estimate and retains all coefficient collisions. -/
theorem interval_mean_square (s : Finset ℕ) (b : ℕ → ℝ) (N : ℕ)
    (hs : ∀ n ∈ s, 1 ≤ n ∧ n ≤ N) (a c : ℝ) (hac : a ≤ c) :
    (∫ t in Ico a c, ‖polynomial s b t‖^2) ≤
      (c-a+rowCost N)*energy s b := by
  have h := dirichlet_mean_square_le151 s (fun n => (b n : ℂ)) N hs a c
  rw [intervalIntegral.integral_of_le hac, ← integral_Ico_eq_integral_Ioc] at h
  simpa only [norm_eq_positive, energy, rowCost, Complex.norm_real,
    Real.norm_eq_abs, sq_abs] using h

/-- Independent qualitative integrability; it is not obtained from the desired bound. -/
theorem weighted_integrable (s : Finset ℕ) (b : ℕ → ℝ) (H : ℝ) (hH : 1 ≤ H) :
    IntegrableOn (fun t => ‖polynomial s b t‖^2/t^2) (outside H) :=
  Item1CountableTail.weighted_integrable (polynomial s b) H
    (∑ n ∈ s, |b n|) hH (continuous_polynomial s b).measurable
    (fun t _ => qualitative_cap s b t)

theorem weighted_band (s : Finset ℕ) (b : ℕ → ℝ) (N : ℕ)
    (hs : ∀ n ∈ s, 1 ≤ n ∧ n ≤ N) (V : ℝ) (hV : 0 < V) :
    (∫ t in Ico V (2*V), ‖polynomial s b t‖^2/t^2) ≤
      energy s b/V + rowCost N*energy s b/V^2 := by
  have hi : IntegrableOn (fun t => ‖polynomial s b t‖^2) (Ico V (2*V)) :=
    ((continuous_polynomial s b).norm.pow 2).continuousOn.integrableOn_Icc.mono_set Ico_subset_Icc_self
  have hc : ContinuousOn (fun t : ℝ => ‖polynomial s b t‖^2/t^2) (Icc V (2*V)) := by
    apply ((continuous_polynomial s b).norm.pow 2).continuousOn.div
      (continuous_id.pow 2).continuousOn
    intro t ht
    exact pow_ne_zero 2 (ne_of_gt (hV.trans_le ht.1))
  have hw : IntegrableOn (fun t : ℝ => ‖polynomial s b t‖^2/t^2) (Ico V (2*V)) :=
    hc.integrableOn_Icc.mono_set Ico_subset_Icc_self
  have hm := setIntegral_mono_on hw (hi.div_const (V^2)) measurableSet_Ico (by
    intro t ht
    exact div_le_div_of_nonneg_left (sq_nonneg _) (sq_pos_of_pos hV)
      (pow_le_pow_left₀ hV.le ht.1 2))
  rw [integral_div] at hm
  have hb := div_le_div_of_nonneg_right
    (interval_mean_square s b N hs V (2*V) (by linarith)) (sq_nonneg V)
  calc
    _ ≤ (∫ t in Ico V (2*V), ‖polynomial s b t‖^2)/V^2 := hm
    _ ≤ (2*V-V+rowCost N)*energy s b/V^2 := hb
    _ = energy s b/V+rowCost N*energy s b/V^2 := by field_simp [ne_of_gt hV] <;> ring

/-- This is the full positive half-line, not a bounded frequency prefix. -/
theorem positive_tail (s : Finset ℕ) (b : ℕ → ℝ) (N : ℕ)
    (hs : ∀ n ∈ s, 1 ≤ n ∧ n ≤ N) (H : ℝ) (hH : 1 ≤ H) :
    (∫ t in Ioi H, ‖polynomial s b t‖^2/t^2) ≤
      2*energy s b/H+4*rowCost N*energy s b/(3*H^2) := by
  have hHp : 0 < H := by linarith
  have hi := weighted_integrable s b H hH
  have hip : IntegrableOn (fun t => ‖polynomial s b t‖^2/t^2) (Ici H) := by
    apply (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr
    apply hi.mono_set
    intro t ht
    change H < |t|
    rw [abs_of_pos (hHp.trans ht)]
    exact ht
  have h := integral_le_of_blocks (fun t => ‖polynomial s b t‖^2/t^2)
    H (energy s b) (rowCost N*energy s b) hHp hip (by
      intro k
      have hb := weighted_band s b N hs (scale H k) (scale_pos H hHp k)
      simpa only [block, scale_succ] using hb)
  convert h using 1 <;> ring

/-- No analytic hypothesis remains: the conclusion follows from the original
finite mean-square theorem, finite support, and real coefficients. -/
theorem two_sided_tail (s : Finset ℕ) (b : ℕ → ℝ) (N : ℕ)
    (hs : ∀ n ∈ s, 1 ≤ n ∧ n ≤ N) (H : ℝ) (hH : 1 ≤ H) :
    (∫ t in outside H, ‖polynomial s b t‖^2/t^2) ≤
      4*energy s b/H+8*rowCost N*energy s b/(3*H^2) := by
  have h := symmetric_of_even (fun t => ‖polynomial s b t‖^2/t^2) H
    (2*energy s b/H+4*rowCost N*energy s b/(3*H^2)) (by linarith)
    (weighted_integrable s b H hH)
    (fun t => by rw [norm_even, neg_sq]) (positive_tail s b N hs H hH)
  convert h using 1 <;> ring

end Item1FinitePolynomialTail

-- ROOT SOURCE RECURSIVE AUDIT: exact original declarations.
run_cmd do
  for target in [
    ``Item1FinitePolynomialTail.energy_nonneg,
    ``Item1FinitePolynomialTail.continuous_polynomial,
    ``Item1FinitePolynomialTail.kernel_neg,
    ``Item1FinitePolynomialTail.negative_eq_conj_positive,
    ``Item1FinitePolynomialTail.norm_eq_positive,
    ``Item1FinitePolynomialTail.norm_even,
    ``Item1FinitePolynomialTail.qualitative_cap,
    ``Item1FinitePolynomialTail.interval_mean_square,
    ``Item1FinitePolynomialTail.weighted_integrable,
    ``Item1FinitePolynomialTail.weighted_band,
    ``Item1FinitePolynomialTail.positive_tail,
    ``Item1FinitePolynomialTail.two_sided_tail] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "Item1FinitePolynomialTail: 12 original theorem guards passed."
