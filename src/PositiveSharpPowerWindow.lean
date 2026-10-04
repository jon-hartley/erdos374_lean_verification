import PositiveSharpExceptionalInput
import PolynomialLogEnvelope

/-! The half-scale moving window fits the pointwise power window. Quantified
literal residual and signed-remainder mean estimates imply density zero for
the actual prime-free set. Neither analytic estimate is discharged here. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open Filter MeasureTheory Set
namespace PositiveSharpPowerWindow
open PositiveSharpExceptionalInput PositiveSharpResidual PositiveSharpBoxedCount

def halfWidth (X β : ℝ) : ℝ := X^β/2
def powerPrimeFree (X β : ℝ) : Set ℝ :=
  {x | ¬∃ p : ℕ, p.Prime ∧ x-x^β<(p:ℝ) ∧ (p:ℝ)≤x} ∩ Icc X (2*X)

theorem halfWidth_eventually (β : ℝ) (hβ : β<1) :
    ∀ᶠ X : ℝ in atTop, 0<halfWidth X β ∧ halfWidth X β≤X/4 := by
  have ht := tendsto_rpow_atTop (by linarith : 0<1-β)
  filter_upwards [ht.eventually (eventually_ge_atTop (2:ℝ)), eventually_gt_atTop (0:ℝ)]
    with X hpow hX
  have he : X^β*X^(1-β)=X := by
    rw [←Real.rpow_add hX, show β+(1-β)=(1:ℝ) by ring, Real.rpow_one]
  have hm := mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hX.le β)
  rw [he] at hm
  constructor
  · exact div_pos (Real.rpow_pos_of_pos hX β) (by norm_num)
  · dsimp [halfWidth]
    linarith

theorem halfWidth_fits_power (X x β : ℝ) (hX : 0<X) (hβ : 0≤β)
    (hx : x∈Icc X (2*X)) : x*halfWidth X β/X≤x^β := by
  have hY : 0≤halfWidth X β := div_nonneg (Real.rpow_nonneg hX.le β) (by norm_num)
  calc
    _ ≤ 2*halfWidth X β :=
      (PositiveSharpMovingWindow.window_size_bounds X _ x hX hY hx).2
    _ = X^β := by unfold halfWidth; ring
    _ ≤ x^β := Real.rpow_le_rpow hX.le hx.1 hβ

theorem powerPrimeFree_subset (X β : ℝ) (hX : 0<X) (hβ : 0≤β) :
    powerPrimeFree X β⊆primeFree X (halfWidth X β) := by
  intro x hx
  refine ⟨?_,hx.2⟩
  intro hp
  obtain ⟨p,hp,hleft,hright⟩ := hp
  apply hx.1
  refine ⟨p,hp,?_,hright⟩
  linarith [halfWidth_fits_power X x β hX hβ hx.2]

theorem powerPrimeFree_measure_le (X β : ℝ) (hX : 0<X) (hβ : 0≤β) :
    volume.real (powerPrimeFree X β)≤volume.real (primeFree X (halfWidth X β)) :=
  measureReal_mono (powerPrimeFree_subset X β hX hβ)
    (measure_ne_top_of_subset inter_subset_right isCompact_Icc.measure_lt_top.ne)

theorem budget_tendsto_zero (C_E C_R : ℝ) :
    Tendsto (fun X : ℝ => 2000*C_E/Real.log X+
      8192000*Real.log X/X^((1:ℝ)/12)+4000000*C_R/(Real.log X)^2)
      atTop (nhds 0) := by
  have hi : Tendsto (fun X : ℝ => (Real.log X)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
  have hp : Tendsto (fun X : ℝ => Real.log X/X^((1:ℝ)/12)) atTop (nhds 0) := by
    simpa only [Real.rpow_one] using
      Real.tendsto_pow_log_div_pow_atTop (1/12:ℝ) (1:ℝ) (by norm_num)
  have hh := ((hi.const_mul (2000*C_E)).add (hp.const_mul 8192000)).add
    ((hi.pow 2).const_mul (4000000*C_R))
  simpa only [mul_zero, zero_pow (by norm_num : (2:ℕ)≠0), zero_add,
    div_eq_mul_inv, inv_pow, mul_assoc] using hh

theorem eventually_power_primeFree_density_zero (β : ℝ) (hβ : 0≤β) (hβ1 : β<1) :
    ∃ s₀ : ℝ, 0<s₀ ∧ s₀≤1/1000 ∧ ∀ s : ℝ, 0<s → s<s₀ →
      ∀ C_E C_R : ℝ,
      (∀ᶠ X : ℝ in atTop,
        (∫ x in Icc X (2*X), residualAbs X x (x*halfWidth X β/X))/X≤C_E/(Real.log X)^2) →
      (∀ᶠ X : ℝ in atTop,
        (∫ x in Icc X (2*X), (signedRemainder X s x (x*halfWidth X β/X))^2)/X≤
          C_R*(halfWidth X β)^2/(Real.log X)^4) →
      Tendsto (fun X : ℝ => volume.real (powerPrimeFree X β)/X) atTop (nhds 0) := by
  obtain ⟨s₀,hs₀,hs1,hp⟩ := eventually_logarithmic_primeFree_bound
  refine ⟨s₀,hs₀,hs1,?_⟩
  intro s hs hss C_E C_R hE hR
  obtain ⟨X₀,hX₀,hbound⟩ := hp s hs hss
  have hn : ∀ᶠ X : ℝ in atTop, 0≤volume.real (powerPrimeFree X β)/X := by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with X hX
    exact div_nonneg ENNReal.toReal_nonneg hX.le
  have hu : ∀ᶠ X : ℝ in atTop, volume.real (powerPrimeFree X β)/X≤
      2000*C_E/Real.log X+8192000*Real.log X/X^((1:ℝ)/12)+
        4000000*C_R/(Real.log X)^2 := by
    filter_upwards [hE,hR,eventually_ge_atTop X₀,halfWidth_eventually β hβ1]
      with X hEX hRX hXX hY
    have hX : 0<X := by linarith [hX₀.trans hXX]
    exact (div_le_div_of_nonneg_right (powerPrimeFree_measure_le X β hX hβ) hX.le).trans
      (hbound X hXX (halfWidth X β) C_E C_R hY.1 hY.2 hEX hRX)
  exact squeeze_zero' hn hu (budget_tendsto_zero C_E C_R)

run_cmd do
  for decl in [``halfWidth_eventually, ``halfWidth_fits_power, ``powerPrimeFree_subset,
      ``powerPrimeFree_measure_le, ``budget_tendsto_zero,
      ``eventually_power_primeFree_density_zero] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "POWER-WINDOW PRIME-FREE DENSITY ZERO IF TWO LITERAL ANALYTIC MEAN ESTIMATES HOLD"
end PositiveSharpPowerWindow
end
