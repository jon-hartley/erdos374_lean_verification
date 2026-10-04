import FlatPowerCap
import OuterMaskShiftBoundsWork

/-! Shift-uniform control of the prime near-zero band when the physical
frequency is high. The flat cofactor is unshifted. No prime cap is assumed.
This is a frequency estimate; identification with the literal centered
moving remainder is still a separate obligation. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Filter MeasureTheory Set
namespace OuterExceptionalFlatWork
open Erdos374.HarmanGram152

def exceptional (X ρ a U : ℝ) : Set ℝ :=
  {t | |t+a| ≤ U ∧ X^ρ ≤ |t| ∧ |t| ≤ X}

theorem exceptional_subset (X ρ a U : ℝ) :
    exceptional X ρ a U ⊆ Icc (-a-U) (-a+U) := by
  intro t ht
  exact (OuterMaskShiftBoundsWork.translated_low_iff t a U).mp ht.1

theorem exceptional_volume (X ρ a U : ℝ) (hU : 0≤U) :
    volume.real (exceptional X ρ a U) ≤ 2*U := by
  have hh := measureReal_mono (μ := volume) (exceptional_subset X ρ a U)
    (isCompact_Icc.measure_lt_top.ne)
  rw [Real.volume_real_Icc_of_le (by linarith : -a-U≤-a+U)] at hh
  linarith

theorem energy_bound (X ρ a U κ : ℝ) (hX : 0<X) (hU : 0≤U)
    (F K : ℝ→ℂ)
    (hF : ∀t∈exceptional X ρ a U, ‖F t‖≤1)
    (hK : ∀t∈exceptional X ρ a U, ‖K t‖≤X^(-κ)) :
    (∫t in exceptional X ρ a U, ‖F t*K t‖^2) ≤
      2*U*X^(-2*κ) := by
  have hfinite : volume (exceptional X ρ a U)<⊤ :=
    lt_of_le_of_lt (measure_mono (exceptional_subset X ρ a U)) isCompact_Icc.measure_lt_top
  have hpoint (t : ℝ) (ht : t∈exceptional X ρ a U) :
      ‖‖F t*K t‖^2‖ ≤ X^(-2*κ) := by
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    have hh : ‖F t*K t‖≤X^(-κ) := by
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_right (hF t ht) (norm_nonneg _)).trans
        (by simpa using hK t ht)
    have hh2 := pow_le_pow_left₀ (norm_nonneg _) hh 2
    convert hh2 using 1
    rw [←Real.rpow_mul_natCast hX.le]
    congr 1
    ring
  have hh := norm_setIntegral_le_of_norm_le_const hfinite hpoint
  calc
    _ ≤ ‖∫t in exceptional X ρ a U, ‖F t*K t‖^2‖ := le_abs_self _
    _ ≤ X^(-2*κ)*volume.real (exceptional X ρ a U) := hh
    _ ≤ X^(-2*κ)*(2*U) := mul_le_mul_of_nonneg_left
      (exceptional_volume X ρ a U hU) (by positivity)
    _ = _ := by ring

theorem eventually_exceptional_energy (ε ρ : ℝ) (hε : 0<ε)
    (hρ : 0<ρ) (hρ1 : ρ≤1) :
    ∃κ : ℝ, 0<κ ∧ ∀ᶠ X : ℝ in atTop, 1≤X ∧
      ∀ (N lo hi : ℕ) (σ a U : ℝ) (F : ℝ→ℂ),
        X^ε≤(N:ℝ) → (N:ℝ)≤X → N≤lo → hi≤2*N → 1≤σ →
        0≤U → U≤X^κ →
        (∀t∈exceptional X ρ a U, ‖F t‖≤1) →
        (∫t in exceptional X ρ a U,
          ‖F t*verticalDirichlet152 (Finset.Ioc lo hi) (fun _ => 1) σ t‖^2)
          ≤ 2*X^(-κ) := by
  obtain ⟨κ,hκ,_,hcap⟩ := FlatPowerCap.eventually_bound ε ρ 1
    hε hρ hρ1 (by norm_num)
  refine ⟨κ,hκ,?_⟩
  filter_upwards [hcap] with X hcap
  refine ⟨hcap.1,?_⟩
  intro N lo hi σ a U F hN hNX hlo hhi hσ hU hUX hF
  have hx : 0<X := by linarith [hcap.1]
  have hh := energy_bound X ρ a U κ hx hU F
    (verticalDirichlet152 (Finset.Ioc lo hi) (fun _ => 1) σ) hF
    (fun t ht => hcap.2 N lo hi hN hNX hlo hhi t σ ht.2.1 ht.2.2 hσ)
  apply hh.trans
  calc
    _ ≤ 2*X^κ*X^(-2*κ) := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hUX (by norm_num)) (by positivity)
    _ = _ := by rw [mul_assoc,←Real.rpow_add hx]; congr 2; ring

run_cmd do
  for decl in [``exceptional_subset, ``exceptional_volume, ``energy_bound,
      ``eventually_exceptional_energy] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
end OuterExceptionalFlatWork
