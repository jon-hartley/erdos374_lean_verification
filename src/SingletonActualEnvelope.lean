import SingletonActualCollection
import SingletonHarmonic

/-! A scalar power-saving envelope for the proposed generic singleton moment
bound. This module asserts no mean-square estimate. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Filter

namespace SingletonActualEnvelope

theorem harmonic_and_boundary (X : ℝ) (hX : 1<X) (Q : ℕ) (hQ : 1≤Q)
    (hQX : (Q:ℝ)≤X^(31/125:ℝ)) :
    SingletonHarmonic.harmonicSum Q≤1+Real.log X ∧ (Q:ℝ)^4/X≤1 := by
  have hXp : 0<X := by linarith
  have hQp : (0:ℝ)<Q := by exact_mod_cast (show 0<Q by omega)
  have hQ1 : (Q:ℝ)≤X := hQX.trans (by
    simpa using Real.rpow_le_rpow_of_exponent_le hX.le (by norm_num : (31/125:ℝ)≤1))
  constructor
  · exact (SingletonHarmonic.harmonicSum_le_one_add_log Q).trans
      (add_le_add le_rfl (Real.log_le_log hQp hQ1))
  · apply (div_le_one hXp).mpr
    calc
      (Q:ℝ)^4 ≤ (X^(31/125:ℝ))^4 := pow_le_pow_left₀ hQp.le hQX 4
      _ = X^(124/125:ℝ) := by
        rw [←Real.rpow_mul_natCast hXp.le]
        norm_num
      _ ≤ X := by
        simpa using Real.rpow_le_rpow_of_exponent_le hX.le (by norm_num : (124/125:ℝ)≤1)

theorem eventually_uniform_bound :
    ∀ᶠ X : ℝ in atTop, 1<X ∧ ∀Q:ℕ, 1≤Q → (Q:ℝ)≤X^(31/125:ℝ) →
      let Y:=PositiveSharpPowerWindow.halfWidth X (101/1000)
      48*Y*(SingletonHarmonic.harmonicSum Q^3+(Q:ℝ)^4/X) ≤
        Y^2*X^(-(1/20:ℝ)) := by
  filter_upwards [PolynomialLogEnvelope.eventually_bound 192 3 (51/1000)
    (by norm_num) (by norm_num),eventually_gt_atTop (1:ℝ)] with X hp hX
  refine ⟨hX,?_⟩
  intro Q hQ hQX
  have hXp : 0<X := by linarith
  have hlog : 0≤Real.log X := Real.log_nonneg hX.le
  let Y:=PositiveSharpPowerWindow.halfWidth X (101/1000)
  have hY : 0≤Y := by dsimp [Y,PositiveSharpPowerWindow.halfWidth]; positivity
  obtain ⟨hH,hbd⟩ := harmonic_and_boundary X hX Q hQ hQX
  have hcube : SingletonHarmonic.harmonicSum Q^3≤(1+Real.log X)^3 :=
    pow_le_pow_left₀ (SingletonHarmonic.harmonicSum_nonneg Q) hH 3
  have hc1 : 1≤(1+Real.log X)^3 := one_le_pow₀ (by linarith)
  have hYeq : Y*X^(-(1/20:ℝ))=X^(51/1000:ℝ)/2 := by
    dsimp [Y,PositiveSharpPowerWindow.halfWidth]
    rw [div_mul_eq_mul_div,←Real.rpow_add hXp]
    norm_num
  have henv : 96*(1+Real.log X)^3≤Y*X^(-(1/20:ℝ)) := by
    rw [hYeq]
    linarith [hp.2]
  calc
    48*Y*(SingletonHarmonic.harmonicSum Q^3+(Q:ℝ)^4/X)
        ≤48*Y*((1+Real.log X)^3+1) :=
      mul_le_mul_of_nonneg_left (add_le_add hcube hbd) (by positivity)
    _ ≤48*Y*(2*(1+Real.log X)^3) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = Y*(96*(1+Real.log X)^3) := by ring
    _ ≤Y*(Y*X^(-(1/20:ℝ))) := mul_le_mul_of_nonneg_left henv hY
    _ = Y^2*X^(-(1/20:ℝ)) := by ring

theorem eventually_bound :
    ∀ᶠ X : ℝ in atTop, 1<X ∧
      let Q:=⌊X^(31/125:ℝ)⌋₊
      let Y:=PositiveSharpPowerWindow.halfWidth X (101/1000)
      1≤Q ∧ 48*Y*(SingletonHarmonic.harmonicSum Q^3+(Q:ℝ)^4/X) ≤
        Y^2*X^(-(1/20:ℝ)) := by
  filter_upwards [eventually_uniform_bound] with X hX
  have hp : 0<X := by linarith [hX.1]
  have hQ : 1≤⌊X^(31/125:ℝ)⌋₊ := Nat.le_floor (by
    simpa using (Real.one_lt_rpow hX.1 (by norm_num : (0:ℝ)<31/125)).le)
  exact ⟨hX.1,hQ,hX.2 _ hQ (Nat.floor_le (Real.rpow_nonneg hp.le _))⟩

run_cmd do
  for decl in [``harmonic_and_boundary,``eventually_uniform_bound,``eventually_bound] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "SINGLETON SCALAR ENVELOPE SAVES X^(-1/20); NO MOMENT ESTIMATE ASSUMED"

end SingletonActualEnvelope
