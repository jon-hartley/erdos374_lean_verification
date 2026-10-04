import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic

/-!
v8. Countable dyadic tail assembly with independently established integrability.
UNCOMPILED DRAFT. No execution of the recursive guards is claimed.
The generic integral lemma takes integrability explicitly. The weighted-tail
regularity lemma proves it from measurability and a qualitative amplitude cap;
no small mean or summability of the desired source integrals is assumed.
-/
set_option autoImplicit false
set_option maxHeartbeats 12000000
noncomputable section
open MeasureTheory Set Function
open scoped BigOperators
namespace Item1CountableTail

def scale (U : ℝ) (k : ℕ) : ℝ := (2:ℝ)^k*U

def block (U : ℝ) (k : ℕ) : Set ℝ := Ico (scale U k) (scale U (k+1))

def outside (U : ℝ) : Set ℝ := {t | U < |t|}

theorem scale_pos (U : ℝ) (hU : 0<U) (k : ℕ) : 0<scale U k := by
  unfold scale
  positivity

theorem scale_mono (U : ℝ) (hU : 0≤U) : Monotone (scale U) := by
  intro i j hij
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hij) hU

theorem scale_succ (U : ℝ) (k : ℕ) : scale U (k+1)=2*scale U k := by
  unfold scale
  rw [pow_succ]
  ring

theorem blocks_disjoint (U : ℝ) (hU : 0≤U) : Pairwise (Disjoint on block U) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hi hj
  rcases lt_or_gt_of_ne hij with hij | hji
  · have hh := scale_mono U hU (show i+1 ≤ j by omega)
    exact (not_lt_of_ge (hh.trans hj.1)) hi.2
  · have hh := scale_mono U hU (show j+1 ≤ i by omega)
    exact (not_lt_of_ge (hh.trans hi.1)) hj.2

theorem blocks_union (U : ℝ) (hU : 0<U) : (⋃ k : ℕ, block U k)=Ici U := by
  ext t
  constructor
  · intro ht
    obtain ⟨k,hk⟩ := mem_iUnion.mp ht
    have hh : U≤scale U k := by
      simpa only [scale,pow_zero,one_mul] using scale_mono U hU.le (Nat.zero_le k)
    exact hh.trans hk.1
  · intro ht
    have hratio : 1≤t/U := (le_div_iff₀ hU).mpr (by simpa using ht)
    obtain ⟨k,hk0,hk1⟩ := exists_nat_pow_near hratio (by norm_num : (1:ℝ)<2)
    apply mem_iUnion.mpr
    refine ⟨k,?_,?_⟩
    · exact (le_div_iff₀ hU).mp hk0
    · exact (div_lt_iff₀ hU).mp hk1

theorem budget_hasSum (U A B : ℝ) (hU : 0<U) :
    HasSum (fun k : ℕ => A/scale U k+B/(scale U k)^2)
      (2*A/U+4*B/(3*U^2)) := by
  have hhalf : HasSum (fun k : ℕ => (1/2:ℝ)^k) 2 := by
    convert hasSum_geometric_of_lt_one (by norm_num : (0:ℝ)≤1/2)
      (by norm_num : (1/2:ℝ)<1) using 1 <;> norm_num
  have hquarter : HasSum (fun k : ℕ => (1/4:ℝ)^k) (4/3:ℝ) := by
    convert hasSum_geometric_of_lt_one (by norm_num : (0:ℝ)≤1/4)
      (by norm_num : (1/4:ℝ)<1) using 1 <;> norm_num
  have hh := (hhalf.mul_left (A/U)).add (hquarter.mul_left (B/U^2))
  have hid (k : ℕ) : A/scale U k+B/(scale U k)^2 =
      (A/U)*(1/2:ℝ)^k+(B/U^2)*(1/4:ℝ)^k := by
    unfold scale
    rw [mul_pow,one_div_pow,one_div_pow]
    have hp : ((2:ℝ)^k)^2=(4:ℝ)^k := by
      rw [←pow_mul, Nat.mul_comm, pow_mul]
      norm_num
    rw [hp]
    field_simp <;> ring
  simpa only [hid,show (A/U)*2+(B/U^2)*(4/3)=2*A/U+4*B/(3*U^2) by ring] using hh

/-- Exact infinite summation, not a finite truncation with an unbounded remainder. -/
theorem integral_le_of_blocks (f : ℝ→ℝ) (U A B : ℝ) (hU : 0<U)
    (hfi : IntegrableOn f (Ici U))
    (hb : ∀ k : ℕ, (∫ t in block U k, f t)≤A/scale U k+B/(scale U k)^2) :
    (∫ t in Ioi U, f t)≤2*A/U+4*B/(3*U^2) := by
  have hsum := hasSum_integral_iUnion (s := block U) (f := f) (μ := volume)
    (fun k : ℕ => measurableSet_Ico)
    (blocks_disjoint U hU.le) (by simpa only [blocks_union U hU] using hfi)
  rw [blocks_union U hU,integral_Ici_eq_integral_Ioi] at hsum
  exact hasSum_le hb hsum (budget_hasSum U A B hU)

theorem outside_eq (U : ℝ) : outside U=Iio (-U)∪Ioi U := by
  ext t
  simp only [outside,mem_setOf_eq,mem_union,mem_Iio,mem_Ioi,lt_abs]
  constructor
  · rintro (h|h)
    · exact Or.inr h
    · exact Or.inl (by linarith)
  · rintro (h|h)
    · exact Or.inr (by linarith)
    · exact Or.inl h

theorem outside_measurable (U : ℝ) : MeasurableSet (outside U) := by
  rw [outside_eq]
  exact measurableSet_Iio.union measurableSet_Ioi

/-- Qualitative integrability is proved BEFORE using any source mean estimate.
The compact gap keeps the totalized value at t=0 irrelevant. -/
theorem weighted_integrable (F : ℝ→ℂ) (U B : ℝ) (hU : 1≤U)
    (hF : Measurable F) (hcap : ∀ t∈outside U, ‖F t‖≤B) :
    IntegrableOn (fun t => ‖F t‖^2/t^2) (outside U) := by
  let f : ℝ→ℝ := (outside U).indicator (fun t => ‖F t‖^2/t^2)
  have hf : Measurable f :=
    ((hF.norm.pow_const 2).div (measurable_id.pow_const 2)).indicator (outside_measurable U)
  have hm : Integrable (fun t : ℝ => 2*B^2*(1+t^2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul (2*B^2)
  have hi : Integrable f := by
    apply hm.mono' hf.aestronglyMeasurable
    filter_upwards with t
    by_cases ht : t∈outside U
    · have ht1 : 1 < |t| := hU.trans_lt ht
      have ht2 : 1≤t^2 := by nlinarith [sq_abs t]
      have htp : 0<t^2 := by linarith
      have hB : 0≤B := (norm_nonneg _).trans (hcap t ht)
      have hsq := pow_le_pow_left₀ (norm_nonneg (F t)) (hcap t ht) 2
      have hd : ‖F t‖^2/t^2≤2*B^2/(1+t^2) := by
        apply (div_le_div_iff₀ htp (by positivity : 0<1+t^2)).mpr
        nlinarith [mul_le_mul_of_nonneg_right hsq (show 0≤1+t^2 by positivity),
          mul_nonneg (sq_nonneg B) (show 0≤t^2-1 by linarith)]
      have hnn : 0 ≤ ‖F t‖^2/t^2 := by positivity
      simp only [f,Set.indicator_of_mem ht,Real.norm_eq_abs]
      rw [abs_of_nonneg hnn]
      simpa only [div_eq_mul_inv] using hd
    · simp only [f,Set.indicator_of_notMem ht,norm_zero]
      positivity
  exact (integrable_indicator_iff (outside_measurable U)).mp hi

/-- Reflect only the actual real-energy function; no assumption that arbitrary
complex coefficients obey conjugate symmetry is made. -/
theorem symmetric_of_even (f : ℝ→ℝ) (U B : ℝ) (hU : 0<U)
    (hf : IntegrableOn f (outside U)) (heven : ∀ t, f (-t)=f t)
    (hp : (∫ t in Ioi U, f t)≤B) :
    (∫ t in outside U, f t)≤2*B := by
  have hn : (∫ t in Iio (-U), f t)=(∫ t in Ioi U, f t) := by
    have hh := integral_comp_neg_Ioi U f
    simp only [heven,integral_Iic_eq_integral_Iio] at hh
    exact hh.symm
  have hd : Disjoint (Iio (-U)) (Ioi U) := by
    apply Set.disjoint_left.mpr
    intro t ht hn
    change t < -U at ht
    change U < t at hn
    linarith
  have hnI := hf.mono_set (by
    intro t ht
    rw [outside_eq]
    exact Or.inl ht)
  have hpI := hf.mono_set (by
    intro t ht
    rw [outside_eq]
    exact Or.inr ht)
  rw [outside_eq,setIntegral_union hd measurableSet_Ioi hnI hpI,hn]
  linarith

#print axioms integral_le_of_blocks
run_cmd do
  for n in [``scale_pos,``scale_mono,``scale_succ,``blocks_disjoint,``blocks_union,
      ``budget_hasSum,``integral_le_of_blocks,``outside_eq,``outside_measurable,
      ``weighted_integrable,``symmetric_of_even] do
    for ax in (← Lean.collectAxioms n) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {n}"
  Lean.logInfo "V8 COUNTABLE TAIL: VALID ONLY AFTER SUCCESSFUL COMPILATION"
end Item1CountableTail

-- ROOT SOURCE RECURSIVE AUDIT: exact original declarations.
run_cmd do
  for target in [
    ``Item1CountableTail.scale_pos,
    ``Item1CountableTail.scale_mono,
    ``Item1CountableTail.scale_succ,
    ``Item1CountableTail.blocks_disjoint,
    ``Item1CountableTail.blocks_union,
    ``Item1CountableTail.budget_hasSum,
    ``Item1CountableTail.integral_le_of_blocks,
    ``Item1CountableTail.outside_eq,
    ``Item1CountableTail.outside_measurable,
    ``Item1CountableTail.weighted_integrable,
    ``Item1CountableTail.symmetric_of_even] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "Item1CountableTail: 11 original theorem guards passed."
