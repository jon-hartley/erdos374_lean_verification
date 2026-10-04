import SeparatedCoreGlobalPerronWork
import MovingWindowCorrelationWork
import TripleFirstMean

/-! The entire literal core as one centered signed close-product correlation.
The identity has no dyadic partition or prime/composite mean assumptions. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace SeparatedCoreCorrelationWork
open SeparatedCoreGlobalPerronWork LongPairSeparatedCoreWork LongPairCloseDistinctMeanWork

theorem physicalCoefficient_eq_source (X s : ℝ) (n : ℕ) :
    physicalCoefficient X s n = ∑ r∈separatedSource X s,
      if LongerTupleEncoding.index r∣n then LongPairCofactorSwitchWork.realWeight X s r else 0 := by
  have hh := congrArg Complex.re (LongerTupleCollection.grouped_sum (separatedSource X s)
    LongerTupleEncoding.index (LongerTupleActualProfiles.originalWeight X s true)
    (fun m => if m∣n then (1:ℂ) else 0))
  simp only [mul_ite, mul_one, mul_zero, Complex.re_sum, apply_ite, Complex.zero_re] at hh
  exact hh

theorem count_eq_sharp_difference (S : Finset ℕ) (w : ℕ → ℝ) (δ x : ℝ)
    (hδ : δ<1) (hleft : x-x*δ≤x) :
    MovingWindowCorrelationWork.count S w δ x =
      SmoothedCountBoundary.sharp S w x - SmoothedCountBoundary.sharp S w (x-x*δ) := by
  unfold MovingWindowCorrelationWork.count SmoothedCountBoundary.sharp
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  rw [MovingWindowCorrelationWork.atom_eq_window _ _ _ hδ]
  split_ifs <;> simp_all <;> linarith

theorem remainder_eq_centered (X s Y : ℝ) (hX : 1<X) (hs : 0<s)
    (hs1 : s≤1/1000) (hlog : 1000≤Real.log X) (hY : 0≤Y) (hYX : Y<X)
    (x : ℝ) (hx : x∈Icc X (2*X)) :
    separatedRemainder X s (x-x*(Y/X)) x =
      MovingWindowCorrelationWork.centered (physicalSupport X) (physicalCoefficient X s)
        (Y/X) (mainMass X s) x := by
  have hXp : 0<X := by linarith
  have hxp : 0≤x := (hXp.trans_le hx.1).le
  have hδ : Y/X<1 := (div_lt_one hXp).mpr hYX
  have hδ0 : 0≤Y/X := div_nonneg hY hXp.le
  have hleft : x-x*(Y/X)≤x := by nlinarith [mul_nonneg hxp hδ0]
  have hi : ∀ m∈coreSupport X s, 0<m := by
    intro m hm
    exact_mod_cast (Real.rpow_pos_of_pos hXp (26/35 : ℝ)).trans
      (support_geometry X s hX hs hs1 hlog m hm).1
  rw [remainder_eq_sharp X s _ _ hi (by nlinarith) hleft hx.2]
  unfold MovingWindowCorrelationWork.centered
  rw [count_eq_sharp_difference _ _ _ _ hδ hleft]
  ring

def correlationEnergy (X s Y : ℝ) : ℝ :=
  MovingWindowCorrelationWork.energy (physicalSupport X) (physicalCoefficient X s) X Y (mainMass X s)

theorem square_integral_eq (X s Y : ℝ) (hX : 1<X) (hs : 0<s)
    (hs1 : s≤1/1000) (hlog : 1000≤Real.log X) (hY : 0≤Y) (hYX : Y<X) :
    (∫ x in Icc X (2*X), (separatedRemainder X s (x-x*(Y/X)) x)^2) =
      correlationEnergy X s Y := by
  have he : (∫ x in Icc X (2*X), (separatedRemainder X s (x-x*(Y/X)) x)^2) =
      ∫ x in Icc X (2*X), (MovingWindowCorrelationWork.centered
        (physicalSupport X) (physicalCoefficient X s) (Y/X) (mainMass X s) x)^2 := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro x hx
    dsimp only
    rw [remainder_eq_centered X s Y hX hs hs1 hlog hY hYX x hx]
  rw [he]
  exact MovingWindowCorrelationWork.centered_square_eq_energy _ _ X Y _ (by linarith) hY hYX

theorem correlationEnergy_nonneg (X s Y : ℝ) (hX : 1<X) (hs : 0<s)
    (hs1 : s≤1/1000) (hlog : 1000≤Real.log X) (hY : 0≤Y) (hYX : Y<X) :
    0≤correlationEnergy X s Y := by
  rw [← square_integral_eq X s Y hX hs hs1 hlog hY hYX]
  exact integral_nonneg (fun _ => sq_nonneg _)

/-- An explicit arithmetic correlation bound is sufficient for the needed
absolute mean. This theorem does not assume individual block estimates. -/
theorem absolute_mean_of_energy (X s Y B : ℝ) (hX : 1<X) (hs : 0<s)
    (hs1 : s≤1/1000) (hlog : 1000≤Real.log X) (hY : 0≤Y) (hYX : Y<X) (hB : 0<B)
    (henergy : correlationEnergy X s Y ≤ X*B^2) :
    (1/X)*(∫ x in Icc X (2*X), |separatedRemainder X s (x-x*(Y/X)) x|) ≤ B := by
  have hXp : 0<X := by linarith
  have hsq : (1/X)*(∫ x in Icc X (2*X), (separatedRemainder X s (x-x*(Y/X)) x)^2)≤B^2 := by
    rw [square_integral_eq X s Y hX hs hs1 hlog hY hYX]
    have hh := mul_le_mul_of_nonneg_left henergy (by positivity : 0≤1/X)
    exact hh.trans_eq (by field_simp)
  simp_rw [coreRemainder_eq_collected] at hsq ⊢
  exact TripleFirstMean.remainder_absolute_mean_le _ _ X Y B hXp hY hYX.le hB hsq

#print axioms square_integral_eq
#print axioms absolute_mean_of_energy
run_cmd do
  for decl in [``physicalCoefficient_eq_source, ``count_eq_sharp_difference,
      ``remainder_eq_centered, ``square_integral_eq, ``correlationEnergy_nonneg, ``absolute_mean_of_energy] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end SeparatedCoreCorrelationWork
