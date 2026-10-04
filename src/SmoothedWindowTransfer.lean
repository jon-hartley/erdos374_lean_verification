import ShiftedMellinTransfer
import SmoothMellinMultiplier
import PolynomialLogEnvelope

/-!
Mean-square transfer for the actual smoothed short-window integral.
The smoothing multiplier is bounded uniformly for epsilon in (0,1).
Frequency intervals may be positive or negative and have length <=X.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Filter MeasureTheory Set

namespace SmoothedWindowTransfer
open MellinWindowFactor SmoothMellinMultiplier

def transform (F : ℝ → ℂ) (Ψ : ℝ → ℝ) (ε a b σ δ x : ℝ) : ℂ :=
  ∫ t in Icc a b, F t * mellin (fun u => (Smooth1 Ψ ε u : ℂ)) (line σ t) *
    ((x : ℂ) ^ line σ t - ((x - x * δ : ℝ) : ℂ) ^ line σ t)

theorem transform_eq (F : ℝ → ℂ) (Ψ : ℝ → ℝ) (ε a b σ δ x : ℝ) (hσ : 0 < σ) :
    transform F Ψ ε a b σ δ x =
      MellinWindowTransfer.transform (fun t => F t * multiplier Ψ ε σ t) a b σ δ x := by
  unfold transform MellinWindowTransfer.transform
  apply integral_congr_ae
  filter_upwards with t
  unfold multiplier
  field_simp [line_ne_zero σ t hσ]

theorem mean_square_bound (Ψ : ℝ → ℝ) (hdiff : ContDiff ℝ 1 Ψ)
    (hsupport : Function.support Ψ ⊆ Icc (1 / 2) 2)
    (hnonneg : ∀ x > 0, 0 ≤ Ψ x) (hmass : ∫ x in Ioi 0, Ψ x / x = 1)
    (X Y ε a b : ℝ) (hX : Real.exp 1 ≤ X) (hY : 0 ≤ Y) (hYX : Y < X)
    (hε : ε ∈ Ioo 0 1) (hab : a ≤ b) (hlen : b - a ≤ X)
    (F : ℝ → ℂ) (hF : Continuous F) :
    (1 / X) * (∫ x in Icc X (2 * X),
      ‖transform F Ψ ε a b (1 + 1 / Real.log X) (Y / X) x‖ ^ 2) ≤
        (8192 * Real.exp 2) * Y ^ 2 * Real.log X * ∫ t in Icc a b, ‖F t‖ ^ 2 := by
  have hXp : 0 < X := (Real.exp_pos 1).trans_le hX
  have hlog : 1 ≤ Real.log X := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hX
  let σ := 1 + 1 / Real.log X
  have hσ : 0 < σ := by dsimp [σ]; positivity
  have hσtwo : σ ≤ 2 := by
    have hh : 1 / Real.log X ≤ 1 := (div_le_one (by linarith)).mpr hlog
    dsimp [σ]
    linarith
  let g := fun t => F t * multiplier Ψ ε σ t
  have hg : Continuous g := hF.mul (continuous_multiplier Ψ ε σ hε hσ hdiff hnonneg hsupport hmass)
  have henergy : (∫ t in Icc a b, ‖g t‖ ^ 2) ≤ 16 * ∫ t in Icc a b, ‖F t‖ ^ 2 := by
    rw [← integral_const_mul]
    apply integral_mono (hg.norm.pow 2).integrableOn_Icc
      (by fun_prop : Continuous (fun t => 16 * ‖F t‖ ^ 2)).integrableOn_Icc
    intro t
    dsimp [g]
    rw [norm_mul, mul_pow, mul_comm (16 : ℝ)]
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    have hh := pow_le_pow_left₀ (norm_nonneg _)
      (norm_le_four Ψ ε σ t hε hσ hσtwo hdiff hnonneg hsupport hmass) 2
    norm_num at hh ⊢
    exact hh
  have hwindow := ShiftedMellinTransfer.window_bound X a b (Y / X) hX hab hlen
    (div_nonneg hY hXp.le) ((div_lt_one hXp).mpr hYX) g hg
  have heq : (∫ x in Icc X (2 * X), ‖transform F Ψ ε a b σ (Y / X) x‖ ^ 2) =
      ∫ x in Icc X (2 * X), ‖MellinWindowTransfer.transform g a b σ (Y / X) x‖ ^ 2 := by
    apply integral_congr_ae
    filter_upwards with x
    rw [transform_eq F Ψ ε a b σ (Y / X) x hσ]
  rw [heq]
  apply hwindow.trans
  apply (mul_le_mul_of_nonneg_left henergy (by positivity)).trans_eq
  field_simp
  ring

theorem eventually_bound (Ψ : ℝ → ℝ) (hdiff : ContDiff ℝ 1 Ψ)
    (hsupport : Function.support Ψ ⊆ Icc (1 / 2) 2)
    (hnonneg : ∀ x > 0, 0 ≤ Ψ x) (hmass : ∫ x in Ioi 0, Ψ x / x = 1)
    (c : ℝ) (hc : 0 < c) :
    ∀ᶠ X : ℝ in atTop, Real.exp 1 ≤ X ∧
      ∀ (Y ε a b : ℝ) (F : ℝ → ℂ),
        0 ≤ Y → Y < X → ε ∈ Ioo 0 1 → a ≤ b → b - a ≤ X → Continuous F →
        (∫ t in Icc a b, ‖F t‖ ^ 2) ≤ X ^ (-c) →
        (1 / X) * (∫ x in Icc X (2 * X),
          ‖transform F Ψ ε a b (1 + 1 / Real.log X) (Y / X) x‖ ^ 2) ≤
            Y ^ 2 * X ^ (-(c / 2)) := by
  filter_upwards [PolynomialLogEnvelope.eventually_bound (8192 * Real.exp 2) 1
    (c / 2) (by positivity) (by positivity), eventually_ge_atTop (Real.exp 1)]
    with X hX hlarge
  refine ⟨hlarge, ?_⟩
  intro Y ε a b F hY hYX hε hab hlen hF henergy
  have hXp : 0 < X := (Real.exp_pos 1).trans_le hlarge
  have hlog : 0 ≤ Real.log X := Real.log_nonneg hX.1
  have hfactor : (8192 * Real.exp 2) * Real.log X ≤ X ^ (c / 2) := by
    have hh := mul_le_mul_of_nonneg_left (show Real.log X ≤ 1 + Real.log X by linarith)
      (by positivity : 0 ≤ 8192 * Real.exp 2)
    exact hh.trans (by simpa only [pow_one] using hX.2)
  calc
    _ ≤ (8192 * Real.exp 2) * Y ^ 2 * Real.log X * ∫ t in Icc a b, ‖F t‖ ^ 2 :=
      mean_square_bound Ψ hdiff hsupport hnonneg hmass X Y ε a b hlarge hY hYX hε hab hlen F hF
    _ ≤ (8192 * Real.exp 2) * Y ^ 2 * Real.log X * X ^ (-c) :=
      mul_le_mul_of_nonneg_left henergy (by positivity)
    _ = Y ^ 2 * ((8192 * Real.exp 2) * Real.log X) * X ^ (-c) := by ring
    _ ≤ Y ^ 2 * X ^ (c / 2) * X ^ (-c) := by gcongr
    _ = Y ^ 2 * X ^ (-(c / 2)) := by
      rw [mul_assoc, ← Real.rpow_add hXp]
      congr 2
      ring

end SmoothedWindowTransfer

#print axioms SmoothedWindowTransfer.eventually_bound
run_cmd do
  for decl in [``SmoothedWindowTransfer.transform_eq, ``SmoothedWindowTransfer.eventually_bound] do
    let axioms ← Lean.collectAxioms decl
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "SMOOTHED WINDOW TRANSFER PASSED"
