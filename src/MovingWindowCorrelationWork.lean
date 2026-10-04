import SmoothedWindowRegularity
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Exact physical overlap kernel for relative short windows. This retains
signed correlations before taking absolute values or partitioning blocks. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open MeasureTheory Set
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace MovingWindowCorrelationWork

def atom (δ n x : ℝ) : ℝ := if n≤x ∧ x<n/(1-δ) then 1 else 0

def overlap (X δ n m : ℝ) : ℝ :=
  max (min (2*X) (min (n/(1-δ)) (m/(1-δ))) - max X (max n m)) 0

def firstMoment (X δ n : ℝ) : ℝ := ∫ x in Icc X (2*X), x*atom δ n x

def count (S : Finset ℕ) (w : ℕ → ℝ) (δ x : ℝ) : ℝ :=
  ∑ n∈S, w n * atom δ n x

def centered (S : Finset ℕ) (w : ℕ → ℝ) (δ M x : ℝ) : ℝ := count S w δ x - δ*x*M

theorem atom_eq_window (δ n x : ℝ) (hδ : δ<1) :
    atom δ n x = if x-x*δ<n ∧ n≤x then 1 else 0 := by
  have he : n≤x ∧ x<n/(1-δ) ↔ x-x*δ<n ∧ n≤x := by
    rw [lt_div_iff₀ (by linarith : 0<1-δ)]
    constructor <;> rintro ⟨ha,hb⟩ <;> constructor <;> nlinarith
  simp only [atom, he]

theorem atom_eq_indicator (δ n : ℝ) :
    atom δ n = (Ico n (n/(1-δ))).indicator (fun _ => (1:ℝ)) := by
  funext x
  simp only [atom, Set.indicator_apply, Set.mem_Ico]

theorem atom_product (δ n m : ℝ) :
    (fun x => atom δ n x * atom δ m x) =
      (Ico n (n/(1-δ)) ∩ Ico m (m/(1-δ))).indicator (fun _ => (1:ℝ)) := by
  funext x
  simp only [atom, Set.indicator_apply, Set.mem_inter_iff, Set.mem_Ico]
  split_ifs <;> norm_num <;> tauto

theorem atom_integrable (X δ n : ℝ) : IntegrableOn (atom δ n) (Icc X (2*X)) := by
  rw [atom_eq_indicator]
  exact ((continuous_const : Continuous (fun _ : ℝ => (1:ℝ))).integrableOn_Icc).indicator measurableSet_Ico

theorem product_integrable (X δ n m : ℝ) :
    IntegrableOn (fun x => atom δ n x * atom δ m x) (Icc X (2*X)) := by
  rw [atom_product]
  exact ((continuous_const : Continuous (fun _ : ℝ => (1:ℝ))).integrableOn_Icc).indicator
    (measurableSet_Ico.inter measurableSet_Ico)

theorem first_integrable (X δ n : ℝ) :
    IntegrableOn (fun x => x*atom δ n x) (Icc X (2*X)) := by
  have he : (fun x => x*atom δ n x) = (Ico n (n/(1-δ))).indicator (fun x : ℝ => x) := by
    funext x
    simp only [atom, Set.indicator_apply, Set.mem_Ico]
    split_ifs <;> simp
  rw [he]
  exact continuous_id.integrableOn_Icc.indicator measurableSet_Ico

theorem integral_atom_product (X δ n m : ℝ) :
    (∫ x in Icc X (2*X), atom δ n x * atom δ m x) = overlap X δ n m := by
  rw [atom_product, integral_Icc_eq_integral_Ico,
    setIntegral_indicator (measurableSet_Ico.inter measurableSet_Ico),
    setIntegral_const, smul_eq_mul, mul_one]
  simp only [Set.Ico_inter_Ico, Real.volume_real_Ico, overlap]

theorem overlap_nonneg (X δ n m : ℝ) : 0≤overlap X δ n m := le_max_right _ _

theorem overlap_symmetric (X δ n m : ℝ) : overlap X δ n m=overlap X δ m n := by
  simp only [overlap, min_comm (n/(1-δ)) (m/(1-δ)), max_comm n m]

theorem overlap_zero_of_separated (X Y n m : ℝ) (hX : 0<X)
    (hY : 0≤Y) (hYX : Y<X) (hgap : 2*Y≤|n-m|) : overlap X (Y/X) n m=0 := by
  rw [← integral_atom_product]
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro x hx
  rw [atom_eq_window _ _ _ ((div_lt_one hX).mpr hYX),
    atom_eq_window _ _ _ ((div_lt_one hX).mpr hYX)]
  split_ifs with hn hm
  · have hwidth : x*(Y/X)≤2*Y := by
      have hh := mul_le_mul_of_nonneg_right hx.2 (div_nonneg hY hX.le)
      have he : (2*X)*(Y/X)=2*Y := by field_simp
      rwa [he] at hh
    have hlt : |n-m|<2*Y := abs_lt.mpr ⟨by linarith [hn.1,hm.2],by linarith [hm.1,hn.2]⟩
    linarith
  all_goals simp

theorem square_expansion (S : Finset ℕ) (w : ℕ → ℝ) (δ x : ℝ) :
    (count S w δ x)^2 = ∑ n∈S, ∑ m∈S, (w n*w m)*(atom δ n x*atom δ m x) := by
  unfold count
  rw [pow_two, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  ring

theorem centered_square_integral (S : Finset ℕ) (w : ℕ → ℝ) (X δ M : ℝ) :
    (∫ x in Icc X (2*X), (centered S w δ M x)^2) =
      (∑ n∈S, ∑ m∈S, w n*w m*overlap X δ n m) -
        2*δ*M*(∑ n∈S, w n*firstMoment X δ n) +
          (δ*M)^2*(∫ x in Icc X (2*X), x^2) := by
  have hpt (x : ℝ) : (centered S w δ M x)^2 =
      (∑ n∈S, ∑ m∈S, (w n*w m)*(atom δ n x*atom δ m x)) -
        2*δ*M*(∑ n∈S, w n*(x*atom δ n x)) + (δ*M)^2*x^2 := by
    rw [← square_expansion]
    have he : (∑ n∈S, w n*(x*atom δ n x)) = x*count S w δ x := by
      unfold count
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      ring
    rw [he]
    unfold centered
    ring
  have hi1 : IntegrableOn (fun x => ∑ n∈S, ∑ m∈S,
      (w n*w m)*(atom δ n x*atom δ m x)) (Icc X (2*X)) :=
    integrable_finsetSum _ (fun n _ => integrable_finsetSum _ (fun m _ =>
      (product_integrable X δ n m).const_mul _))
  have hi2 : IntegrableOn (fun x => 2*δ*M*(∑ n∈S, w n*(x*atom δ n x))) (Icc X (2*X)) :=
    (integrable_finsetSum S (fun n _ => (first_integrable X δ n).const_mul (w n))).const_mul (2*δ*M)
  have hi3 : IntegrableOn (fun x : ℝ => (δ*M)^2*x^2) (Icc X (2*X)) :=
    (by fun_prop : Continuous (fun x : ℝ => (δ*M)^2*x^2)).integrableOn_Icc
  simp_rw [hpt]
  have hadd := integral_add (hi1.sub hi2) hi3
  have hsub := integral_sub hi1 hi2
  simp only [Pi.sub_apply, Pi.add_apply] at hadd hsub
  rw [hadd, hsub]
  simp_rw [integral_const_mul]
  rw [integral_finsetSum S (fun n _ => integrable_finsetSum S (fun m _ =>
    (product_integrable X δ n m).const_mul _))]
  simp_rw [integral_finsetSum S (fun m _ => (product_integrable X δ _ m).const_mul _),
    integral_const_mul, integral_atom_product]
  rw [integral_finsetSum S (fun n _ => (first_integrable X δ n).const_mul _)]
  simp only [integral_const_mul, firstMoment]

theorem firstMoment_eq (X δ n : ℝ) :
    firstMoment X δ n = if max X n≤min (2*X) (n/(1-δ)) then
      ((min (2*X) (n/(1-δ)))^2-(max X n)^2)/2 else 0 := by
  have he : (fun x => x*atom δ n x) = (Ico n (n/(1-δ))).indicator (fun x : ℝ => x) := by
    funext x
    simp only [atom, Set.indicator_apply, Set.mem_Ico]
    split_ifs <;> simp
  unfold firstMoment
  rw [he, integral_Icc_eq_integral_Ico, setIntegral_indicator measurableSet_Ico,
    Set.Ico_inter_Ico]
  by_cases hh : max X n≤min (2*X) (n/(1-δ))
  · rw [if_pos hh, integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le hh,
      integral_id]
  · rw [if_neg hh, Set.Ico_eq_empty_of_le (le_of_not_ge hh), setIntegral_empty]

theorem spatial_second_moment (X : ℝ) (hX : 0≤X) :
    (∫ x in Icc X (2*X), x^2) = (7/3 : ℝ)*X^3 := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith : X≤2*X),
    integral_pow]
  norm_num
  ring

def nearPairs (S : Finset ℕ) (Y : ℝ) : Finset (ℕ×ℕ) :=
  (S ×ˢ S).filter (fun p => |(p.1:ℝ)-p.2|<2*Y)

def energy (S : Finset ℕ) (w : ℕ → ℝ) (X Y M : ℝ) : ℝ :=
  (∑ p∈nearPairs S Y, w p.1*w p.2*overlap X (Y/X) p.1 p.2) -
    2*(Y/X)*M*(∑ n∈S, w n*firstMoment X (Y/X) n) +
      ((Y/X)*M)^2*((7/3 : ℝ)*X^3)

theorem centered_square_eq_energy (S : Finset ℕ) (w : ℕ → ℝ) (X Y M : ℝ)
    (hX : 0<X) (hY : 0≤Y) (hYX : Y<X) :
    (∫ x in Icc X (2*X), (centered S w (Y/X) M x)^2) = energy S w X Y M := by
  rw [centered_square_integral, spatial_second_moment X hX.le]
  have he : (∑ n∈S, ∑ m∈S, w n*w m*overlap X (Y/X) n m) =
      ∑ p∈nearPairs S Y, w p.1*w p.2*overlap X (Y/X) p.1 p.2 := by
    rw [← Finset.sum_product (f := fun p : ℕ×ℕ => w p.1*w p.2*overlap X (Y/X) p.1 p.2)]
    unfold nearPairs
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p hp
    by_cases hgap : |(p.1:ℝ)-p.2|<2*Y
    · rw [if_pos hgap]
    · rw [if_neg hgap, overlap_zero_of_separated X Y p.1 p.2 hX hY hYX (le_of_not_gt hgap)]
      ring
  rw [he]
  rfl

#print axioms centered_square_integral
run_cmd do
  for decl in [``atom_eq_window, ``atom_eq_indicator, ``atom_product, ``atom_integrable,
      ``product_integrable, ``first_integrable, ``integral_atom_product, ``overlap_nonneg,
      ``overlap_symmetric, ``overlap_zero_of_separated, ``square_expansion, ``centered_square_integral,
      ``firstMoment_eq, ``spatial_second_moment, ``centered_square_eq_energy] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end MovingWindowCorrelationWork
