import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic

/-!
UNCOMPILED PROOF-BODY DRAFT, source-merge copy.
Adapted from the supplied physical-pruning atom lemma; not a new classical result. A finite nonnegative sharp-window first-mean
estimate, independent of Fourier analysis and prime distribution.
All measures are Lebesgue measure. Product collisions remain separate indices.
-/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Item1SharpAtomMean

/-- Exact endpoint convention: m ≤ x < m/(1-eta). -/
def atom (eta m w : ℝ) : ℝ → ℝ :=
  (Ico m (m/(1-eta))).indicator (fun x => w/(eta*x))

theorem window_iff (eta m x : ℝ) (heta : eta < 1) :
    ((1-eta)*x < m ∧ m ≤ x) ↔ x ∈ Ico m (m/(1-eta)) := by
  have hq : 0 < 1-eta := by linarith
  simp only [mem_Ico]
  constructor
  · rintro ⟨h₁,h₂⟩
    exact ⟨h₂, (lt_div_iff₀ hq).mpr (by simpa [mul_comm] using h₁)⟩
  · rintro ⟨h₁,h₂⟩
    exact ⟨by simpa [mul_comm] using (lt_div_iff₀ hq).mp h₂, h₁⟩

theorem atom_literal (eta m w x : ℝ) (heta : eta < 1) :
    atom eta m w x =
      if (1-eta)*x < m ∧ m ≤ x then w/(eta*x) else 0 := by
  classical
  simp only [atom, Set.indicator_apply, window_iff eta m x heta]

theorem atom_measurable (eta m w : ℝ) : Measurable (atom eta m w) := by
  unfold atom
  apply Measurable.indicator _ measurableSet_Ico
  fun_prop

theorem atom_nonneg (eta m w : ℝ) (heta : 0 < eta) (hm : 0 < m)
    (hw : 0 ≤ w) (x : ℝ) : 0 ≤ atom eta m w x := by
  classical
  unfold atom
  by_cases hx : x ∈ Ico m (m/(1-eta))
  · rw [Set.indicator_of_mem hx]
    exact div_nonneg hw (mul_nonneg heta.le (hm.le.trans hx.1))
  · simp only [Set.indicator_of_notMem hx, le_refl]

def majorant (eta m w : ℝ) : ℝ → ℝ :=
  (Ico m (m/(1-eta))).indicator (fun _ => w/(eta*m))

theorem atom_le_majorant (eta m w : ℝ) (heta : 0 < eta) (hm : 0 < m)
    (hw : 0 ≤ w) (x : ℝ) : atom eta m w x ≤ majorant eta m w x := by
  classical
  unfold atom majorant
  by_cases hx : x ∈ Ico m (m/(1-eta))
  · simp only [Set.indicator_of_mem hx]
    exact div_le_div_of_nonneg_left hw (mul_pos heta hm)
      (mul_le_mul_of_nonneg_left hx.1 heta.le)
  · simp only [Set.indicator_of_notMem hx, le_refl]

theorem majorant_nonneg (eta m w : ℝ) (heta : 0 < eta) (hm : 0 < m)
    (hw : 0 ≤ w) (x : ℝ) : 0 ≤ majorant eta m w x := by
  classical
  unfold majorant
  by_cases hx : x ∈ Ico m (m/(1-eta))
  · rw [Set.indicator_of_mem hx]
    positivity
  · simp only [Set.indicator_of_notMem hx, le_refl]

theorem majorant_integrable (eta m w : ℝ) : Integrable (majorant eta m w) := by
  have hc : IntegrableOn (fun _ : ℝ => w/(eta*m)) (Ico m (m/(1-eta))) := by
    exact integrable_const _
  exact hc.integrable_indicator measurableSet_Ico

/-- Qualitative integrability is proved separately; no default-zero integral trick. -/
theorem atom_integrable (eta m w : ℝ) (heta : 0 < eta) (hm : 0 < m)
    (hw : 0 ≤ w) : Integrable (atom eta m w) := by
  apply (majorant_integrable eta m w).mono'
    (atom_measurable eta m w).aestronglyMeasurable
  filter_upwards with x
  simpa only [Real.norm_eq_abs, abs_of_nonneg (atom_nonneg eta m w heta hm hw x)]
    using atom_le_majorant eta m w heta hm hw x

theorem majorant_integral (eta m w : ℝ) (heta : 0 < eta)
    (heta1 : eta < 1) (hm : 0 < m) :
    (∫ x : ℝ, majorant eta m w x) = w/(1-eta) := by
  have hq : 0 < 1-eta := by linarith
  have hml : m ≤ m/(1-eta) := by
    apply (le_div_iff₀ hq).mpr
    nlinarith [mul_nonneg hm.le heta.le]
  unfold majorant
  rw [integral_indicator_const _ measurableSet_Ico, Real.volume_real_Ico_of_le hml]
  simp only [smul_eq_mul]
  field_simp [ne_of_gt heta, ne_of_gt hm, ne_of_gt hq]
  <;> ring

/-- Uniform bound for an individual atom, including products outside [X,2X]. -/
theorem atom_first_mean (X eta m w : ℝ) (hX : 0 < X)
    (heta : 0 < eta) (heta2 : eta ≤ 1/2) (hm : 0 < m) (hw : 0 ≤ w) :
    (∫ x in Icc X (2*X), atom eta m w x)/X ≤ 4*w/m := by
  have heta1 : eta < 1 := by linarith
  have hq : 0 < 1-eta := by linarith
  by_cases hmX : m ≤ 2*X
  · have hcompare :
        (∫ x in Icc X (2*X), atom eta m w x) ≤ w/(1-eta) := by
      calc
        (∫ x in Icc X (2*X), atom eta m w x) ≤
            ∫ x in Icc X (2*X), majorant eta m w x := by
          apply setIntegral_mono_of_nonneg
          · intro x hx
            exact atom_nonneg eta m w heta hm hw x
          · intro x hx
            exact atom_le_majorant eta m w heta hm hw x
          · exact (majorant_integrable eta m w).integrableOn
        _ ≤ ∫ x : ℝ, majorant eta m w x :=
          setIntegral_le_integral (majorant_integrable eta m w)
            (Filter.Eventually.of_forall (majorant_nonneg eta m w heta hm hw))
        _ = w/(1-eta) := majorant_integral eta m w heta heta1 hm
    have hden : m ≤ 4*((1-eta)*X) := by nlinarith
    calc
      (∫ x in Icc X (2*X), atom eta m w x)/X ≤ (w/(1-eta))/X :=
        div_le_div_of_nonneg_right hcompare hX.le
      _ = w/((1-eta)*X) := by rw [div_div]
      _ ≤ 4*w/m := by
        apply (div_le_div_iff₀ (mul_pos hq hX) hm).mpr
        have hh := mul_le_mul_of_nonneg_left hden hw
        nlinarith
  · have hz : (∫ x in Icc X (2*X), atom eta m w x) = 0 := by
      apply setIntegral_eq_zero_of_forall_eq_zero
      intro x hx
      unfold atom
      apply Set.indicator_of_notMem
      intro hmemb
      exact hmX (hmemb.1.trans hx.2)
    rw [hz, zero_div]
    positivity

/-- Ordered representations can be the indexing type; repeated products are allowed. -/
theorem finite_first_mean {ι : Type*} (S : Finset ι) (m w : ι → ℝ)
    (X eta : ℝ) (hX : 0 < X) (heta : 0 < eta) (heta2 : eta ≤ 1/2)
    (hm : ∀ a ∈ S, 0 < m a) (hw : ∀ a ∈ S, 0 ≤ w a) :
    (∫ x in Icc X (2*X), ∑ a ∈ S, atom eta (m a) (w a) x)/X ≤
      4*∑ a ∈ S, w a/m a := by
  rw [integral_finsetSum S (fun a ha =>
    (atom_integrable eta (m a) (w a) heta (hm a ha) (hw a ha)).integrableOn)]
  rw [Finset.sum_div]
  calc
    (∑ a ∈ S, (∫ x in Icc X (2*X), atom eta (m a) (w a) x)/X) ≤
        ∑ a ∈ S, 4*w a/m a := by
      apply Finset.sum_le_sum
      intro a ha
      exact atom_first_mean X eta (m a) (w a) hX heta heta2 (hm a ha) (hw a ha)
    _ = 4*∑ a ∈ S, w a/m a := by simp only [Finset.mul_sum, mul_div_assoc]


end Item1SharpAtomMean

-- ROOT SOURCE RECURSIVE AUDIT: exact original declarations.
run_cmd do
  for target in [
    ``Item1SharpAtomMean.window_iff,
    ``Item1SharpAtomMean.atom_literal,
    ``Item1SharpAtomMean.atom_measurable,
    ``Item1SharpAtomMean.atom_nonneg,
    ``Item1SharpAtomMean.atom_le_majorant,
    ``Item1SharpAtomMean.majorant_nonneg,
    ``Item1SharpAtomMean.majorant_integrable,
    ``Item1SharpAtomMean.atom_integrable,
    ``Item1SharpAtomMean.majorant_integral,
    ``Item1SharpAtomMean.atom_first_mean,
    ``Item1SharpAtomMean.finite_first_mean] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "Item1SharpAtomMean: 11 original theorem guards passed."
