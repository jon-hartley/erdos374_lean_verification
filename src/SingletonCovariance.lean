import SingletonCells
import SingletonResidueIntegral
import SingletonPeriodic

/-! From the finite CRT identity to actual real-floor covariance integrals. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set intervalIntegral
open scoped BigOperators

namespace SingletonCovariance
open SingletonDivisor

theorem bounded_intervalIntegrable (f : ℝ → ℝ) (hm : Measurable f)
    (hb : ∀x, |f x|≤1) (a b : ℝ) : IntervalIntegrable f volume a b := by
  have hi : IntegrableOn f (uIcc a b) := by
    apply Measure.integrableOn_of_bounded isCompact_uIcc.measure_lt_top.ne
      hm.aestronglyMeasurable (M:=1)
    exact Filter.Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hb x)
  exact hi.intervalIntegrable

theorem product_abs_le (m n : ℕ) (x h : ℝ) :
    |discrepancy m x h * discrepancy n x h|≤1 := by
  rw [abs_mul]
  exact (mul_le_mul (abs_discrepancy_le_one m x h) (abs_discrepancy_le_one n x h)
    (abs_nonneg _) (by norm_num)).trans_eq (one_mul 1)

theorem product_integrable (m n : ℕ) (h a b : ℝ) :
    IntervalIntegrable (fun x => discrepancy m x h * discrepancy n x h) volume a b :=
  bounded_intervalIntegrable _ ((measurable m h).mul (measurable n h))
    (fun x => product_abs_le m n x h) a b

theorem unit_cells (f : ℝ → ℝ) (hm : Measurable f) (hb : ∀x, |f x|≤1) (N : ℕ) :
    (∫v in (0:ℝ)..1, ∑q∈Finset.range N, f ((q:ℝ)+v)) = ∫x in (0:ℝ)..N, f x := by
  have hi : ∀q∈Finset.range N, IntervalIntegrable (fun v => f ((q:ℝ)+v)) volume 0 1 := by
    intro q _
    exact bounded_intervalIntegrable _ (hm.comp (by fun_prop)) (fun v => hb _) 0 1
  rw [integral_finsetSum hi]
  simp_rw [integral_comp_add_left]
  have hh := sum_integral_adjacent_intervals (a:=fun q:ℕ => (q:ℝ))
    (f:=f) (μ:=volume) (n:=N)
    (fun q _ => bounded_intervalIntegrable f hm hb (q:ℝ) ((q+1:ℕ):ℝ))
  simpa only [Nat.cast_zero, Nat.cast_add, Nat.cast_one, add_zero] using hh

theorem coprime_integral {a b : ℕ} (ha : 0<a) (hb : 0<b)
    (hab : a.Coprime b) (h : ℝ) :
    (∫x in (0:ℝ)..(a*b:ℕ), discrepancy a x h * discrepancy b x h) =
      Int.fract h * (1-Int.fract h) := by
  let k := ⌊h⌋
  let u := Int.fract h
  have hu : 0≤u ∧ u<1 := ⟨Int.fract_nonneg h, Int.fract_lt_one h⟩
  have hku : (k:ℝ)+u=h := Int.floor_add_fract h
  rw [←unit_cells (fun x => discrepancy a x h * discrepancy b x h)
    ((measurable a h).mul (measurable b h))
    (fun x => product_abs_le a b x h) (a*b)]
  calc
    _ = ∫v in (0:ℝ)..1, ∑q∈Finset.range (a*b),
        ((SingletonResidue.count a (if v<u then k+1 else k) q:ℝ)-((k:ℝ)+u)/a) *
        ((SingletonResidue.count b (if v<u then k+1 else k) q:ℝ)-((k:ℝ)+u)/b) := by
      apply integral_congr_Ioo_of_le (by norm_num)
      intro v hv
      apply Finset.sum_congr rfl
      intro q _
      rw [←hku, SingletonCells.discrepancy_cell a q k v u ⟨hv.1.le,hv.2⟩ hu,
        SingletonCells.discrepancy_cell b q k v u ⟨hv.1.le,hv.2⟩ hu]
    _ = u*(1-u) := SingletonResidue.integral_sum_centered_product ha hb hab hu.1 hu.2.le k

end SingletonCovariance
