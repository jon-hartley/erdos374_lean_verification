import PositiveSharpBoxedCount
import PositiveSharpMovingWindow
import SignedDivisorRegularity

/-! Regularity of the literal all-length signed boxed remainder and a
Chebyshev implication from its actual second moment. No second-moment
saving is assumed in the regularity results or proved by the implication. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace PositiveSharpRemainderRegularity
open PositiveSharpBoxedCount SieveWeightedScalarBudget

theorem measurable_scaled_floor (a : ℝ) :
    Measurable (fun x : ℝ => (⌊a*x⌋₊ : ℝ)) := by
  have hf : Measurable (fun x : ℝ => (⌊x⌋₊ : ℝ)) := by
    simpa only [Nat.cast_one, div_one] using
      SignedDivisorRegularity.measurable_floor_quotient 1
  exact hf.comp (by fun_prop)

private theorem continuous_memLp (f : ℝ → ℝ) (X : ℝ) (hf : Continuous f) :
    MemLp f 2 (volume.restrict (Icc X (2*X))) := by
  apply (memLp_two_iff_integrable_sq hf.measurable.aestronglyMeasurable.restrict).mpr
  exact (hf.pow 2).continuousOn.integrableOn_compact isCompact_Icc

theorem scaled_floor_memLp (a X : ℝ) :
    MemLp (fun x : ℝ => (⌊a*x⌋₊ : ℝ)) 2 (volume.restrict (Icc X (2*X))) := by
  apply (continuous_memLp (fun x => a*x) X (by fun_prop)).of_le
    (measurable_scaled_floor a).aestronglyMeasurable.restrict
  exact Filter.Eventually.of_forall (fun x => by
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
    have hm : (⌊a*x⌋₊ : ℝ) ≤ (⌊|a*x|⌋₊ : ℝ) := by
      exact_mod_cast Nat.floor_mono (le_abs_self (a*x))
    exact hm.trans (Nat.floor_le (abs_nonneg (a*x))))

theorem measurable_scaled_remainder (S : Finset ℕ) (w : ℕ → ℝ) (a b : ℝ) :
    Measurable (fun x => HarmanDivisorWindow.remainder S w (a*x) (b*x)) := by
  unfold HarmanDivisorWindow.remainder HarmanDivisorWindow.divisorCount
  apply Measurable.sub ?_ (by fun_prop)
  apply Finset.measurable_fun_sum
  intro d _
  have ha : Measurable (fun x : ℝ => (⌊a*x/d⌋₊ : ℝ)) := by
    convert measurable_scaled_floor (a/d) using 1
    funext x
    congr 2
    ring
  have hb : Measurable (fun x : ℝ => (⌊b*x/d⌋₊ : ℝ)) := by
    convert measurable_scaled_floor (b/d) using 1
    funext x
    congr 2
    ring
  exact (hb.sub ha).const_mul _

theorem scaled_remainder_memLp (S : Finset ℕ) (w : ℕ → ℝ) (a b X : ℝ) :
    MemLp (fun x => HarmanDivisorWindow.remainder S w (a*x) (b*x))
      2 (volume.restrict (Icc X (2*X))) := by
  unfold HarmanDivisorWindow.remainder HarmanDivisorWindow.divisorCount
  apply MemLp.sub ?_ (continuous_memLp _ X (by fun_prop))
  apply memLp_finsetSum
  intro d _
  have ha : MemLp (fun x : ℝ => (⌊a*x/d⌋₊ : ℝ)) 2
      (volume.restrict (Icc X (2*X))) := by
    convert scaled_floor_memLp (a/d) X using 1
    funext x
    congr 2
    ring
  have hb : MemLp (fun x : ℝ => (⌊b*x/d⌋₊ : ℝ)) 2
      (volume.restrict (Icc X (2*X))) := by
    convert scaled_floor_memLp (b/d) X using 1
    funext x
    congr 2
    ring
  exact (hb.sub ha).const_mul _

theorem sourceRemainder_measurable (D s z X Y : ℝ) :
    Measurable (fun x => SieveBoxedWindow.sourceRemainder D s z (x-x*Y/X) x) := by
  have hh := (measurable_scaled_remainder (SieveBoxedWindow.support D s z)
    (SieveBoxedWindow.coefficient D s z) (1-Y/X) 1).neg
  convert hh using 1
  funext x
  unfold SieveBoxedWindow.sourceRemainder
  congr 2 <;> ring

theorem upperRemainder_measurable (D s z X Y p : ℝ) :
    Measurable (fun x => SieveUpperBoxWindow.remainder D s z ((x-x*Y/X)/p) (x/p)) := by
  have hh := measurable_scaled_remainder (SieveUpperBoxWindow.support D s z)
    (SieveUpperBoxWindow.coefficient D s z) ((1-Y/X)/p) (1/p)
  convert hh using 1
  funext x
  unfold SieveUpperBoxWindow.remainder
  congr 1 <;> ring

theorem signedRemainder_measurable (X s Y : ℝ) :
    Measurable (fun x => signedRemainder X s x (x*Y/X)) := by
  unfold signedRemainder upperRemainders
  apply Measurable.add
  · apply Measurable.add (sourceRemainder_measurable _ _ _ _ _)
    apply Finset.measurable_fun_sum
    intro p _
    exact upperRemainder_measurable _ _ _ _ _ _
  · apply Finset.measurable_fun_sum
    intro p _
    exact upperRemainder_measurable _ _ _ _ _ _

theorem sourceRemainder_memLp (D s z X Y : ℝ) :
    MemLp (fun x => SieveBoxedWindow.sourceRemainder D s z (x-x*Y/X) x)
      2 (volume.restrict (Icc X (2*X))) := by
  have hh := (scaled_remainder_memLp (SieveBoxedWindow.support D s z)
    (SieveBoxedWindow.coefficient D s z) (1-Y/X) 1 X).neg
  convert hh using 1
  funext x
  unfold SieveBoxedWindow.sourceRemainder
  congr 2 <;> ring

theorem upperRemainder_memLp (D s z X Y p : ℝ) :
    MemLp (fun x => SieveUpperBoxWindow.remainder D s z ((x-x*Y/X)/p) (x/p))
      2 (volume.restrict (Icc X (2*X))) := by
  have hh := scaled_remainder_memLp (SieveUpperBoxWindow.support D s z)
    (SieveUpperBoxWindow.coefficient D s z) ((1-Y/X)/p) (1/p) X
  convert hh using 1
  funext x
  unfold SieveUpperBoxWindow.remainder
  congr 1 <;> ring

theorem signedRemainder_memLp (X s Y : ℝ) :
    MemLp (fun x => signedRemainder X s x (x*Y/X))
      2 (volume.restrict (Icc X (2*X))) := by
  unfold signedRemainder upperRemainders
  apply MemLp.add
  · apply MemLp.add (sourceRemainder_memLp _ _ _ _ _)
    apply memLp_finsetSum
    intro p _
    exact upperRemainder_memLp _ _ _ _ _ _
  · apply memLp_finsetSum
    intro p _
    exact upperRemainder_memLp _ _ _ _ _ _

theorem signedRemainder_integrable (X s Y : ℝ) :
    IntegrableOn (fun x => signedRemainder X s x (x*Y/X)) (Icc X (2*X)) :=
  MemLp.integrable (by norm_num : (1:ENNReal)≤2) (signedRemainder_memLp X s Y)

theorem signedRemainder_square_integrable (X s Y : ℝ) :
    IntegrableOn (fun x => (signedRemainder X s x (x*Y/X))^2) (Icc X (2*X)) :=
  (memLp_two_iff_integrable_sq
    (signedRemainder_measurable X s Y).aestronglyMeasurable.restrict).mp
      (signedRemainder_memLp X s Y)

def harmfulSet (X s Y ε : ℝ) : Set ℝ :=
  {x | ε/Real.log X < signedRemainder X s x (x*Y/X)/(x*Y/X)} ∩ Icc X (2*X)

theorem harmfulSet_measurable (X s Y ε : ℝ) : MeasurableSet (harmfulSet X s Y ε) := by
  apply MeasurableSet.inter ?_ measurableSet_Icc
  exact measurableSet_lt measurable_const ((signedRemainder_measurable X s Y).div (by fun_prop))

theorem outside_harmfulSet (X s Y ε x : ℝ) (hx : x∈Icc X (2*X))
    (hgood : x∉harmfulSet X s Y ε) :
    signedRemainder X s x (x*Y/X)/(x*Y/X)≤ε/Real.log X := by
  by_contra hh
  exact hgood ⟨lt_of_not_ge hh,hx⟩

theorem harmfulSet_measure_le (X s Y ε : ℝ) (hX : 1<X) (hY : 0<Y) (hε : 0<ε) :
    volume.real (harmfulSet X s Y ε)≤(Real.log X/(ε*Y))^2*
      (∫ x in Icc X (2*X), (signedRemainder X s x (x*Y/X))^2) := by
  let c := ε*Y/Real.log X
  have hXp : 0<X := by linarith
  have hlog : 0<Real.log X := Real.log_pos hX
  have hc : 0<c := div_pos (mul_pos hε hY) hlog
  have hi := (signedRemainder_square_integrable X s Y).div_const (c^2)
  have hn : 0≤ᵐ[volume.restrict (Icc X (2*X))]
      (fun x => (signedRemainder X s x (x*Y/X))^2/c^2) :=
    Filter.Eventually.of_forall (fun _ => div_nonneg (sq_nonneg _) (sq_nonneg _))
  have hm := hi.measure_le_integral hn (s := harmfulSet X s Y ε) (by
    intro x hx
    have hy : 0<x*Y/X := div_pos (mul_pos (hXp.trans_le hx.2.1) hY) hXp
    have hyY := (PositiveSharpMovingWindow.window_size_bounds X Y x hXp hY.le hx.2).1
    have hr := (lt_div_iff₀ hy).mp hx.1
    have hcr : c≤signedRemainder X s x (x*Y/X) := by
      have hmul := mul_le_mul_of_nonneg_left hyY (div_pos hε hlog).le
      calc
        c = ε/Real.log X*Y := by dsimp [c]; ring
        _ ≤ ε/Real.log X*(x*Y/X) := hmul
        _ ≤ signedRemainder X s x (x*Y/X) := hr.le
    apply (le_div_iff₀ (sq_pos_of_pos hc)).mpr
    simpa only [one_mul] using pow_le_pow_left₀ hc.le hcr 2)
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hm
  rw [ENNReal.toReal_ofReal (integral_nonneg_of_ae hn)] at hr
  have he : (Real.log X/(ε*Y))^2=(c^2)⁻¹ := by
    dsimp [c]
    rw [← inv_pow, inv_div]
  rw [he]
  rw [integral_div] at hr
  simpa [Measure.real, Measure.restrict_apply' measurableSet_Icc, harmfulSet,
    inter_assoc, div_eq_mul_inv, mul_comm] using hr

/-- The second-moment bound is a hypothesis about the literal full signed
remainder. This theorem supplies no saving for that hypothesis. -/
theorem harmfulSet_measure_le_of_second_moment (X s Y ε B : ℝ)
    (hX : 1<X) (hY : 0<Y) (hε : 0<ε)
    (hmean : (∫ x in Icc X (2*X), (signedRemainder X s x (x*Y/X))^2)/X≤B) :
    volume.real (harmfulSet X s Y ε)≤X*(Real.log X/(ε*Y))^2*B := by
  have hXp : 0<X := by linarith
  have hh := (div_le_iff₀ hXp).mp hmean
  calc
    _ ≤ (Real.log X/(ε*Y))^2*
        (∫ x in Icc X (2*X), (signedRemainder X s x (x*Y/X))^2) :=
      harmfulSet_measure_le X s Y ε hX hY hε
    _ ≤ (Real.log X/(ε*Y))^2*(B*X) :=
      mul_le_mul_of_nonneg_left hh (sq_nonneg _)
    _ = _ := by ring

run_cmd do
  for decl in [``measurable_scaled_floor, ``scaled_floor_memLp,
      ``measurable_scaled_remainder, ``scaled_remainder_memLp,
      ``sourceRemainder_measurable, ``upperRemainder_measurable, ``signedRemainder_measurable,
      ``sourceRemainder_memLp, ``upperRemainder_memLp, ``signedRemainder_memLp,
      ``signedRemainder_integrable, ``signedRemainder_square_integrable,
      ``harmfulSet_measurable, ``outside_harmfulSet, ``harmfulSet_measure_le,
      ``harmfulSet_measure_le_of_second_moment] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ACTUAL FULL SIGNED REMAINDER REGULARITY AND CONDITIONAL SECOND-MOMENT CHEBYSHEV"
end PositiveSharpRemainderRegularity
end
