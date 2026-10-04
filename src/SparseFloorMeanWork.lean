import CancellationDivisorBias
import LongerTupleHigherMeanWork

/-! Absolute first means for sparse signed families of large moduli.
Unlike a signed-bias estimate, the absolute value is INSIDE the integral.
The proof uses nonnegativity of the literal floor count and the proved
signed bias, followed by a finite triangle inequality. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators

namespace SparseFloorMeanWork
open UpperAfter545Remaining LongerTupleHigherMeanWork

theorem kernel_integrable (m : ℕ) (X Y : ℝ) :
    IntegrableOn (fun x => floorKernel (x-x*(Y/X)) x m) (Icc X (2*X)) := by
  have hi := TailRemainderBand.moving_remainder_integrable
    ({m}:Finset ℕ) (fun _ => (1:ℝ)) X Y
  simpa only [HarmanDivisorWindow.remainder_eq_sum,Finset.sum_singleton,
    one_mul,floorKernel,mul_div_assoc] using hi

theorem single_absolute_mean (m : ℕ) (X Y : ℝ) (hX : 0<X)
    (hY : 0≤Y) (hYX : Y≤X/2) (hm : 0<m) :
    (1/X)*(∫ x in Icc X (2*X),|floorKernel (x-x*(Y/X)) x m|)≤
      2*Y/X+4*Y/(m:ℝ) := by
  have hm0 : (0:ℝ)<m := by exact_mod_cast hm
  have hYlt : Y<X := by linarith
  have hratio : 0≤Y/X := div_nonneg hY hX.le
  have hratio1 : Y/X≤1 := (div_le_one hX).mpr (by linarith)
  have hi := kernel_integrable m X Y
  have hc : IntegrableOn (fun _ : ℝ => 4*Y/(m:ℝ)) (Icc X (2*X)) :=
    continuous_const.continuousOn.integrableOn_Icc
  have hpoint (x : ℝ) (hx : x∈Icc X (2*X)) :
      |floorKernel (x-x*(Y/X)) x m|≤floorKernel (x-x*(Y/X)) x m+4*Y/(m:ℝ) := by
    have hx0 : 0≤x := hX.le.trans hx.1
    have hl : 0≤x-x*(Y/X) := by nlinarith
    have hlx : x-x*(Y/X)≤x := by linarith [mul_nonneg hx0 hratio]
    have hfloor : (⌊(x-x*(Y/X))/(m:ℝ)⌋₊:ℝ)≤⌊x/(m:ℝ)⌋₊ := by
      exact_mod_cast Nat.floor_mono (div_le_div_of_nonneg_right hlx hm0.le)
    have hmain : (x-(x-x*(Y/X)))/(m:ℝ)≤2*Y/(m:ℝ) := by
      apply div_le_div_of_nonneg_right _ hm0.le
      have hh := mul_le_mul_of_nonneg_right hx.2 hratio
      have he : (2*X)*(Y/X)=2*Y := by field_simp
      rw [he] at hh
      linarith
    have hmnonneg : 0≤(x-(x-x*(Y/X)))/(m:ℝ) := by positivity
    unfold floorKernel
    rw [show 4*Y/(m:ℝ)=2*(2*Y/(m:ℝ)) by ring]
    have hpos : 0≤2*Y/(m:ℝ) := by positivity
    apply abs_le.mpr
    constructor <;> linarith
  have hbound := setIntegral_mono_on hi.abs (hi.add hc) measurableSet_Icc hpoint
  simp only [Pi.add_apply] at hbound
  rw [integral_add hi hc] at hbound
  have hb := CancellationDivisorBias.moving_remainder_integral_bias
    ({m}:Finset ℕ) (fun _ => (1:ℝ)) X Y hX hY hYlt
  simp only [HarmanDivisorWindow.remainder_eq_sum,Finset.sum_singleton,
    one_mul,mul_one,mul_div_assoc,abs_one] at hb
  have hsigned : (∫ x in Icc X (2*X),floorKernel (x-x*(Y/X)) x m)≤2*Y := by
    apply (le_abs_self _).trans
    simpa only [floorKernel] using hb
  have hconst : (∫ _x in Icc X (2*X),4*Y/(m:ℝ))=(4*Y/(m:ℝ))*X := by
    rw [integral_const,measureReal_restrict_apply_univ,
      Real.volume_real_Icc_of_le (by linarith : X≤2*X),smul_eq_mul]
    ring
  rw [hconst] at hbound
  have hfinal : (∫ x in Icc X (2*X),|floorKernel (x-x*(Y/X)) x m|)≤
      2*Y+(4*Y/(m:ℝ))*X := by linarith
  have hh := mul_le_mul_of_nonneg_left hfinal (one_div_nonneg.mpr hX.le)
  convert hh using 1; field_simp

theorem weighted_single_absolute_mean (m : ℕ) (w X Y : ℝ)
    (hw : |w|≤1) (hX : 0<X) (hY : 0≤Y) (hYX : Y≤X/2) (hm : 0<m) :
    (1/X)*(∫ x in Icc X (2*X),|w*floorKernel (x-x*(Y/X)) x m|)≤
      2*Y/X+4*Y/(m:ℝ) := by
  have hi := (kernel_integrable m X Y).abs
  have hh := setIntegral_mono_on (hi.const_mul |w|) hi measurableSet_Icc
    (fun x _ => mul_le_of_le_one_left (abs_nonneg _) hw)
  simp only [abs_mul] at *
  exact (mul_le_mul_of_nonneg_left hh (one_div_nonneg.mpr hX.le)).trans
    (single_absolute_mean m X Y hX hY hYX hm)

/-- A uniform sparse-family saving with signed unit weights. The natural
moduli may repeat: the cardinality bound is on the representation family. -/
theorem eventually_sparse_absolute {α : Type*} :
    ∀ᶠ X : ℝ in atTop, 1<X ∧
      ∀ (S : Finset α) (index : α→ℕ) (w : α→ℝ) (Y : ℝ),
        (S.card:ℝ)≤X^(3/5:ℝ) →
        (∀ r∈S,X^(26/35:ℝ)≤(index r:ℝ)) →
        (∀ r∈S,|w r|≤1) → 0≤Y → Y≤X/2 →
        (1/X)*(∫ x in Icc X (2*X),
          |∑ r∈S,w r*floorKernel (x-x*(Y/X)) x (index r)|)≤Y*X^(-1/10:ℝ) := by
  filter_upwards [eventually_gt_atTop (1:ℝ),
    PolynomialLogEnvelope.eventually_constant_bound 6 (3/70)
      (by norm_num) (by norm_num)] with X hX hc
  refine ⟨hX,?_⟩
  intro S index w Y hcard hindex hw hY hYX
  have hXp : 0<X := by linarith
  have hm (r : α) (hr : r∈S) : 0 < index r := by
    have hp := (Real.rpow_pos_of_pos hXp (26/35:ℝ)).trans_le (hindex r hr)
    exact_mod_cast hp
  have hunit (r : α) (hr : r∈S) :
      2*Y/X+4*Y/(index r:ℝ)≤6*Y*X^(-26/35:ℝ) := by
    have hpow : X^(26/35:ℝ)≤X := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hX.le
        (by norm_num : (26/35:ℝ)≤1)
    have hfirst := div_le_div_of_nonneg_left (by positivity : 0≤2*Y)
      (Real.rpow_pos_of_pos hXp _) hpow
    have hsecond := div_le_div_of_nonneg_left (by positivity : 0≤4*Y)
      (Real.rpow_pos_of_pos hXp _) (hindex r hr)
    rw [show (-26/35:ℝ)=-(26/35:ℝ) by ring,Real.rpow_neg hXp.le]
    convert add_le_add hfirst hsecond using 1; simp only [div_eq_mul_inv]; ring
  apply (absolute_sum_mean_le S
    (fun r x => w r*floorKernel (x-x*(Y/X)) x (index r)) X hXp
    (fun r _ => (kernel_integrable (index r) X Y).const_mul (w r))).trans
  calc
    _ ≤ ∑ r∈S,6*Y*X^(-26/35:ℝ) := Finset.sum_le_sum (fun r hr =>
      (weighted_single_absolute_mean (index r) (w r) X Y (hw r hr) hXp hY hYX
        (hm r hr)).trans (hunit r hr))
    _ = (S.card:ℝ)*(6*Y*X^(-26/35:ℝ)) := by simp
    _ ≤ X^(3/5:ℝ)*(6*Y*X^(-26/35:ℝ)) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = (6*Y)*(X^(3/5:ℝ)*X^(-26/35:ℝ)) := by ring
    _ = Y*(6*X^(-1/7:ℝ)) := by rw [←Real.rpow_add hXp]; norm_num; ring
    _ ≤ Y*(X^(3/70:ℝ)*X^(-1/7:ℝ)) := by gcongr; exact hc.2
    _ = Y*X^(-1/10:ℝ) := by rw [←Real.rpow_add hXp]; norm_num

#print axioms single_absolute_mean
#print axioms eventually_sparse_absolute
run_cmd do
  for decl in [``kernel_integrable, ``single_absolute_mean,
      ``weighted_single_absolute_mean, ``eventually_sparse_absolute] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"

end SparseFloorMeanWork
