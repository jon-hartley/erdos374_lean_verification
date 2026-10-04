import Item1PhysicalDeletion

/-! UNCOMPILED, 2026-10-02. The prior low-frequency theorem is rewritten into
EXACTLY the normalized selected-source density. Its arithmetic and actual-cell
cardinality are supplied internally. The final outside-energy input remains an
explicit unresolved spectral proposition; it is not a proof of the prime cap. -/
set_option autoImplicit false
set_option maxHeartbeats 24000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators
namespace Item1LowEnergyMerge
open Item1SourceGlue Item1PhysicalDeletion Item1SelectedWindow Item1SelectedFourier
open Item1QuadraticAssembly Item1SourceLocalArithmetic
open PositiveInteriorModel PositiveInteriorCells CancellationTransferCenter
open PositiveSharpMovingWindow

def lowEnergy (X Y : ℝ) (K : ℕ) : ℝ :=
  ∑ j∈boxes (mesh X), ∫ t in Icc (-lowCut X K) (lowCut X K),
    density X Y j (primeTuples X j) t

def outsideEnergy (X Y : ℝ) (K : ℕ) : ℝ :=
  ∑ j∈boxes (mesh X), ∫ t in SourceDyadicTail.outside (lowCut X K),
    density X Y j (primeTuples X j) t

/-- All source bindings, including the normalized multiplier, precede the bound. -/
theorem eventually_low_sum_card (K : ℕ) :
    ∀ᶠ X : ℝ in atTop, ∀ Y : ℝ, 0<Y → Y≤X/2 →
      lowEnergy X Y K≤((boxes (mesh X)).card:ℝ)*40500000/
        ((1+Real.log X)^40*lowCut X K) := by
  filter_upwards [Item1OriginalCenterLow.eventually_actual_cell_low_sum K,
    eventually_ge_atTop (2:ℝ)] with X hb hX
  intro Y hY hYX
  have hXp : 0<X := by linarith
  have he : Y/X<1 := (div_lt_one hXp).mpr (by linarith)
  have hh := hb (Y/X) (div_pos hY hXp) he
  simpa only [lowEnergy,density_eq_low] using hh

/-- A coarse rate is enough and avoids changing the original cap exponent. -/
theorem eventually_low_sum_bound (K : ℕ) :
    ∀ᶠ X : ℝ in atTop, ∀ Y : ℝ, 0<Y → Y≤X/2 →
      lowEnergy X Y K≤900000/(Real.log X)^38 := by
  filter_upwards [eventually_geometry,eventually_low_sum_card K] with X hg hb
  obtain ⟨hX,hl,hm⟩ := hg
  have hLp : 0<Real.log X := by linarith
  have hT : 1≤lowCut X K := lowCut_ge_one X K (by linarith)
  have hpow : (Real.log X)^40≤(1+Real.log X)^40 :=
    pow_le_pow_left₀ hLp.le (by linarith) 40
  have hden : (Real.log X)^40≤(1+Real.log X)^40*lowCut X K :=
    hpow.trans (le_mul_of_one_le_right (by positivity) hT)
  have hc := cell_card_normalized_bound X (by linarith) hm
  intro Y hY hYX
  calc
    _ ≤ ((boxes (mesh X)).card:ℝ)*40500000/((1+Real.log X)^40*lowCut X K) := hb Y hY hYX
    _ ≤ ((boxes (mesh X)).card:ℝ)*40500000/(Real.log X)^40 :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    _ = (((boxes (mesh X)).card:ℝ)/(Real.log X)^2)*(40500000/(Real.log X)^38) := by
      field_simp <;> ring
    _ ≤ (1/45)*(40500000/(Real.log X)^38) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := by ring

theorem low_scalar_small (ell : ℝ) (hl : 1000000≤ell) :
    900000/ell^38≤1/4096 := by
  have hp : (1000000:ℝ)^2≤ell^2 := pow_le_pow_left₀ (by norm_num) hl 2
  have hpp : ell^2≤ell^38 := pow_le_pow_right₀ (by linarith) (by omega : 2≤38)
  apply (div_le_div_iff₀ (by positivity : 0<ell^38) (by norm_num : (0:ℝ)<4096)).mpr
  norm_num at hp
  linarith

/-- Constructed, uniform low-frequency budget in the exact final density. -/
theorem eventually_low_budget (K : ℕ) :
    ∀ᶠ X : ℝ in atTop, ∀ Y : ℝ, 0<Y → Y≤X/2 → lowEnergy X Y K≤1/4096 := by
  filter_upwards [eventually_geometry,eventually_low_sum_bound K] with X hg hb
  intro Y hY hYX
  exact (hb Y hY hYX).trans (low_scalar_small _ hg.2.1)

/-- Exact measurable split, with ±U assigned to the low interval, not both parts. -/
theorem low_compl (U : ℝ) : (Icc (-U) U)ᶜ=SourceDyadicTail.outside U := by
  ext t
  change ¬(-U ≤ t ∧ t ≤ U) ↔ U < |t|
  rw [←abs_le, not_le]

theorem totalEnergy_eq_low_add_outside (X Y : ℝ) (K : ℕ)
    (hX : 2≤X) (hlog : 1000000≤Real.log X) (hY : 0<Y) (hYX : Y≤X/2) :
    totalEnergy X Y=lowEnergy X Y K+outsideEnergy X Y K := by
  unfold totalEnergy lowEnergy outsideEnergy
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  have hi := density_integrable X Y j (primeTuples X j) hX hlog hj hY hYX
  have h := integral_add_compl (s:=Icc (-lowCut X K) (lowCut X K)) measurableSet_Icc hi
  rw [low_compl] at h
  exact h.symm

/-- This endpoint constructs the bad physical mean AND the low-frequency energy.
It leaves one precisely defined outside-frequency budget as a visible premise. -/
theorem eventually_literal_item1_of_outside (K : ℕ) :
    ∀ᶠ X : ℝ in atTop, ∀ Y : ℝ, 0<Y → Y≤X/2 →
      outsideEnergy X Y K≤1/2048 →
      (∫ x in Icc X (2*X), sourceResidualAbs X x (x*Y/X))/X≤1/(Real.log X)^2 := by
  filter_upwards [eventually_geometry,eventually_low_budget K,
    eventually_literal_item1_of_energy] with X hg hl he
  intro Y hY hYX hOutside
  apply he Y hY hYX
  rw [totalEnergy_eq_low_add_outside X Y K hg.1 hg.2.1 hY hYX]
  have hLow := hl Y hY hYX
  linarith

end Item1LowEnergyMerge

-- ROOT SOURCE RECURSIVE AUDIT: exact original declarations.
run_cmd do
  for target in [
    ``Item1LowEnergyMerge.eventually_low_sum_card,
    ``Item1LowEnergyMerge.eventually_low_sum_bound,
    ``Item1LowEnergyMerge.low_scalar_small,
    ``Item1LowEnergyMerge.eventually_low_budget,
    ``Item1LowEnergyMerge.low_compl,
    ``Item1LowEnergyMerge.totalEnergy_eq_low_add_outside,
    ``Item1LowEnergyMerge.eventually_literal_item1_of_outside] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "Item1LowEnergyMerge: 7 original theorem guards passed."
