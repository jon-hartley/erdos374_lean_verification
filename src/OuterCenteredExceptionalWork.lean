import OuterCenteredFlatWork
import OuterModeUnitCapWork

/-! A genuine bound for the translated near-zero band of a centered
factorized mode. High physical frequencies use the unshifted flat
cofactor; the complementary physical low band is handled by Euler
summation in OuterCenteredFlatWork. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Filter MeasureTheory Set
namespace OuterCenteredExceptionalWork
open OuterExceptionalFlatWork OuterCenteredFlatWork
open Erdos374.HarmanGram152

theorem energy_of_cap (X ρ a U C : ℝ) (hU : 0≤U) (_hC : 0≤C)
    (G : ℝ→ℂ) (hG : ∀t∈exceptional X ρ a U, ‖G t‖≤C) :
    (∫t in exceptional X ρ a U, ‖G t‖^2)≤2*U*C^2 := by
  have hf : volume (exceptional X ρ a U)<⊤ :=
    lt_of_le_of_lt (measure_mono (exceptional_subset X ρ a U)) isCompact_Icc.measure_lt_top
  have hh := norm_setIntegral_le_of_norm_le_const (μ := volume) hf
    (fun t ht => show ‖‖G t‖^2‖≤C^2 by
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hG t ht) 2)
  calc
    _ ≤ ‖∫t in exceptional X ρ a U, ‖G t‖^2‖ := le_abs_self _
    _ ≤ C^2*volume.real (exceptional X ρ a U) := hh
    _ ≤ C^2*(2*U) := mul_le_mul_of_nonneg_left
      (exceptional_volume X ρ a U hU) (sq_nonneg _)
    _ = _ := by ring

theorem eventually_centered_exceptional (ε ρ : ℝ) (hε : 0<ε)
    (hρ : 0<ρ) (hρ1 : ρ≤1) :
    ∃κ : ℝ, 0<κ ∧ κ≤ρ ∧ ∀ᶠ X : ℝ in atTop, 1≤X ∧
      ∀ (N lo hi : ℕ) (σ a U : ℝ) (F : ℝ→ℂ),
        X^ε≤(N:ℝ) → (N:ℝ)≤X → N≤lo → lo<hi → hi≤2*N → 1≤σ →
        0≤U → U≤X^κ →
        (∀t∈exceptional X ρ a U, ‖F t‖≤1) →
        (∫t in exceptional X ρ a U, ‖F t*centeredFlat lo hi σ t‖^2)
          ≤18*X^(-κ) := by
  obtain ⟨κ,hκ,hκρ,hcap⟩ := FlatPowerCap.eventually_bound ε ρ ρ hε hρ hρ1 hρ
  refine ⟨κ,hκ,hκρ,?_⟩
  filter_upwards [hcap] with X hcap
  refine ⟨hcap.1,?_⟩
  intro N lo hi σ a U F hN hNX hlo hhi hhiN hσ hU hUX hF
  have hx : 0<X := by linarith [hcap.1]
  have hN1 : 1≤N := by
    have hh := (Real.one_le_rpow hcap.1 hε.le).trans hN
    exact_mod_cast hh
  have hpoint (t : ℝ) (ht : t∈exceptional X ρ a U) :
      ‖F t*centeredFlat lo hi σ t‖≤3*X^(-κ) := by
    have ht0 : 0 < |t| := (Real.rpow_pos_of_pos hx ρ).trans_le ht.2.1
    have hc : ‖continuousFlat lo hi σ t‖≤2*X^(-κ) := by
      calc
        _ ≤ 2/|t| := continuousFlat_bound lo hi σ t (by omega) (by omega) hσ ht0
        _ ≤ 2/(X^ρ) := div_le_div_of_nonneg_left (by norm_num)
          (by positivity) ht.2.1
        _ = 2*X^(-ρ) := by rw [Real.rpow_neg hx.le,div_eq_mul_inv]
        _ ≤ 2*X^(-κ) := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hcap.1 (by linarith)) (by norm_num)
    have hk := hcap.2 N lo hi hN hNX hlo hhiN t σ ht.2.1 ht.2.2 hσ
    have hd : ‖centeredFlat lo hi σ t‖≤3*X^(-κ) :=
      (norm_sub_le _ _).trans (by linarith)
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right (hF t ht) (norm_nonneg _)).trans
      (by simpa using hd)
  apply (energy_of_cap X ρ a U (3*X^(-κ)) hU (by positivity)
    (fun t => F t*centeredFlat lo hi σ t) hpoint).trans
  calc
    _ ≤ 2*X^κ*(3*X^(-κ))^2 := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hUX (by norm_num)) (sq_nonneg _)
    _ = 18*X^(-κ) := by
      have he : X^κ*(X^(-κ))^2=X^(-κ) := by
        rw [←Real.rpow_mul_natCast hx.le,←Real.rpow_add hx]
        congr 1
        ring
      nlinarith [he]

run_cmd do
  for decl in [``energy_of_cap, ``eventually_centered_exceptional] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
end OuterCenteredExceptionalWork
