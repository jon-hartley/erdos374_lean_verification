import SparseFloorMeanWork

/-! The sparse-family absolute mean with variable cardinality and modulus
exponents. Its saving is any fixed amount below their positive gap. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators

namespace SparseFloorVariableMeanWork
open UpperAfter545Remaining LongerTupleHigherMeanWork SparseFloorMeanWork

theorem eventually_sparse_absolute {α : Type*} (γ β c : ℝ)
    (hβ : β≤1) (_hc : 0<c) (hgap : c<β-γ) :
    ∀ᶠ X : ℝ in atTop,1<X ∧
      ∀ (S : Finset α) (index : α→ℕ) (w : α→ℝ) (Y : ℝ),
        (S.card:ℝ)≤X^γ →
        (∀ r∈S,X^β≤(index r:ℝ)) →
        (∀ r∈S,|w r|≤1) → 0≤Y → Y≤X/2 →
        (1/X)*(∫ x in Icc X (2*X),
          |∑ r∈S,w r*floorKernel (x-x*(Y/X)) x (index r)|)≤Y*X^(-c) := by
  filter_upwards [eventually_gt_atTop (1:ℝ),
    PolynomialLogEnvelope.eventually_constant_bound 6 (β-γ-c)
      (by norm_num) (by linarith)] with X hX hconstant
  refine ⟨hX,?_⟩
  intro S index w Y hcard hindex hw hY hYX
  have hXp : 0<X := by linarith
  have hm (r : α) (hr : r∈S) : 0 < index r := by
    exact_mod_cast (Real.rpow_pos_of_pos hXp β).trans_le (hindex r hr)
  have hunit (r : α) (hr : r∈S) :
      2*Y/X+4*Y/(index r:ℝ)≤6*Y*X^(-β) := by
    have hpow : X^β≤X := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hX.le hβ
    have hfirst := div_le_div_of_nonneg_left (by positivity : 0≤2*Y)
      (Real.rpow_pos_of_pos hXp β) hpow
    have hsecond := div_le_div_of_nonneg_left (by positivity : 0≤4*Y)
      (Real.rpow_pos_of_pos hXp β) (hindex r hr)
    rw [Real.rpow_neg hXp.le]
    convert add_le_add hfirst hsecond using 1
    simp only [div_eq_mul_inv]
    ring
  apply (absolute_sum_mean_le S
    (fun r x => w r*floorKernel (x-x*(Y/X)) x (index r)) X hXp
    (fun r _ => (kernel_integrable (index r) X Y).const_mul (w r))).trans
  calc
    _ ≤ ∑ r∈S,6*Y*X^(-β) := Finset.sum_le_sum (fun r hr =>
      (weighted_single_absolute_mean (index r) (w r) X Y (hw r hr) hXp hY hYX
        (hm r hr)).trans (hunit r hr))
    _ = (S.card:ℝ)*(6*Y*X^(-β)) := by simp
    _ ≤ X^γ*(6*Y*X^(-β)) := mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = Y*(6*X^(γ-β)) := by rw [sub_eq_add_neg,Real.rpow_add hXp]; ring
    _ ≤ Y*(X^(β-γ-c)*X^(γ-β)) := by gcongr; exact hconstant.2
    _ = Y*X^(-c) := by rw [←Real.rpow_add hXp]; congr 2; ring

#print axioms eventually_sparse_absolute
run_cmd do
  for ax in (←Lean.collectAxioms ``eventually_sparse_absolute) do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"

end SparseFloorVariableMeanWork
