import OuterLocalizedMomentScaleWork
import PolynomialLogEnvelope

/-! Convert the individual completed cofactor range into the dyadic
scale needed by the new frequency estimates, retaining moment slack. -/
set_option autoImplicit false
noncomputable section
open Filter
namespace OuterModeCofactorScaleWork
open OuterActiveDyadicWork LongerTupleEncoding OuterLocalizedMomentScaleWork

theorem eventually_actual_flat_scale :
    ∀ᶠ X : ℝ in atTop, 2≤X ∧ ∀ (s : ℝ), 0≤s →
      ∀ (i j : ℕ) (r : Representation), r∈localizedSource X s i j →
        ∀ (k N : ℕ), 0<k → X/2≤(index r:ℝ)*k → (index r:ℝ)*k≤2*X →
          N≤k → k≤2*N → X^(113/500:ℝ)≤(N:ℝ) ∧ (N:ℝ)≤X := by
  filter_upwards [eventually_ge_atTop (2:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (10000:ℝ)),
    PolynomialLogEnvelope.eventually_constant_bound 2 (1/1000) (by norm_num) (by norm_num)]
    with X hX hlog hc
  refine ⟨hX,?_⟩
  intro s hs i j r hr k N hk hlo hhi hNk hkN
  have hx : 0<X := by linarith
  have hg := physical_cofactor_powers X s hX hs hlog i j r hr k hk hlo hhi
  have hNkR : (N:ℝ)≤k := by exact_mod_cast hNk
  have hkNR : (k:ℝ)≤2*(N:ℝ) := by exact_mod_cast hkN
  constructor
  · have he : X^(113/500:ℝ)*X^(1/1000:ℝ)=X^(227/1000:ℝ) := by
      rw [←Real.rpow_add hx]
      norm_num
    have hh := mul_le_mul_of_nonneg_left hc.2 (Real.rpow_nonneg hx.le (113/500))
    rw [he] at hh
    linarith [hg.1]
  · exact hNkR.trans (hg.2.le.trans (by
      simpa using Real.rpow_le_rpow_of_exponent_le (by linarith : 1≤X)
        (show (129/500:ℝ)≤1 by norm_num)))

theorem dyadic_eighth_length_saving (X T : ℝ) (N : ℕ) (hX : 1≤X)
    (hN : X^(113/500:ℝ)≤(N:ℝ)) (hT : T≤X^(1124/1250:ℝ)) :
    T≤(N:ℝ)^4*X^(-3/625:ℝ) := by
  have hx : 0<X := by linarith
  have hp : X^(113/125:ℝ)≤(N:ℝ)^4 := by
    have hh := pow_le_pow_left₀ (Real.rpow_nonneg hx.le _) hN 4
    rw [←Real.rpow_mul_natCast hx.le] at hh
    norm_num at hh
    exact hh
  calc
    T≤X^(1124/1250:ℝ) := hT
    _ = X^(113/125:ℝ)*X^(-3/625:ℝ) := by rw [←Real.rpow_add hx]; norm_num
    _ ≤ _ := mul_le_mul_of_nonneg_right hp (by positivity)

run_cmd do
  for decl in [``eventually_actual_flat_scale, ``dyadic_eighth_length_saving] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
end OuterModeCofactorScaleWork
