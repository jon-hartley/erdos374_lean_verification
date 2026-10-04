import OuterCompletedEnergyWork
import FrequencyTailBudget
import SpatialErrorBudget

/-! Unconditional upper physical-frequency window bounds for actual
centered source modes. No prime cap or dyadic cofactor ratio is required. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Filter MeasureTheory Set
namespace OuterUpperFrequencyWork
open OuterCompletedEnergyWork OuterBlockCofactorWork OuterActiveDyadicWork

def band (X s Y ε a b : ℝ) (i j : ℕ) (k : BlockKey) (ω : Fin 9→ℝ) (x : ℝ) : ℂ :=
  ((1/(2*Real.pi):ℝ):ℂ)*SmoothedWindowTransfer.transform
    (centeredPolynomial X s (1+1/Real.log X) i j k ω)
    MellinSmoothingFunction.smoothing ε a b (1+1/Real.log X) (Y/X) x

theorem eventually_upper_square (θ κ : ℝ) (hκ : 0<κ) :
    ∀ᶠ X : ℝ in atTop, 256≤X ∧ ∀ (s Y ε a b H : ℝ) (i j : ℕ) (k : BlockKey) (ω : Fin 9→ℝ),
      256*(scale k:ℝ)≤X → X^θ≤Y → Y<X → ε∈Ioo 0 1 →
      X^(1-θ+κ)≤H → 1≤H → a≤b → b-a≤X → (∀t∈Icc a b,H≤|t|) →
      (1/X)*(∫x in Icc X (2*X),‖band X s Y ε a b i j k ω x‖^2)≤Y^2*X^(-κ) := by
  filter_upwards [eventually_centered_energy (κ/2) (by positivity),
    FrequencyTailBudget.eventually_separated θ κ hκ,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with X he ht hlog
  refine ⟨he.1,?_⟩
  intro s Y ε a b H i j k ω hscale hY hYX hε hH hH1 hab hlen haway
  have hX : 2≤X := by linarith [he.1]
  have hσ : 1<1+1/Real.log X := by
    have : 0<1/Real.log X := by positivity
    linarith
  have henergy := he.2 s (1+1/Real.log X) a b i j k ω hscale hσ hab hlen
    (fun t ht => hH1.trans (haway t ht))
  have hm := ht.2 Y ε a b H (centeredPolynomial X s (1+1/Real.log X) i j k ω)
    hY hYX hε hH hab hlen haway (centered_continuous X s _ i j k ω hX hσ hscale) henergy
  exact SpatialErrorBudget.normalize_mean_square _ X _ (by linarith [hX]) hm

theorem eventually_active_upper_square (s : ℝ) (hs : 0≤s) :
    ∀ᶠ X : ℝ in atTop, 256≤X ∧ ∀ (Y ε a b : ℝ) (i j : ℕ) (k : BlockKey) (ω : Fin 9→ℝ),
      k∈activeKeys X s i j → X^(1009/10000:ℝ)≤Y → Y<X → ε∈Ioo 0 1 →
      a≤b → b-a≤X → (∀t∈Icc a b,X^(1124/1250:ℝ)≤|t|) →
      (1/X)*(∫x in Icc X (2*X),‖band X s Y ε a b i j k ω x‖^2)≤Y^2*X^(-1/10000:ℝ) := by
  filter_upwards [eventually_upper_square (1009/10000) (1/10000) (by norm_num),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1000000:ℝ))] with X hh hlog
  refine ⟨hh.1,?_⟩
  intro Y ε a b i j k ω hk hY hYX hε hab hlen haway
  have hX : 2≤X := by linarith [hh.1]
  have hm := hh.2 s Y ε a b (X^(1124/1250:ℝ)) i j k ω
    (OuterBlockCofactorScaleWork.active_lower X s hX hs hlog i j k hk).1 hY hYX hε
    (by norm_num) (Real.one_le_rpow (by linarith : 1≤X) (by norm_num)) hab hlen haway
  convert hm using 1 <;> norm_num

theorem eventually_halfWidth_fits : ∀ᶠ X : ℝ in atTop,
    X^(1009/10000:ℝ)≤PositiveSharpPowerWindow.halfWidth X (101/1000) := by
  filter_upwards [(tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/10000)).eventually
    (eventually_ge_atTop (2:ℝ)),eventually_gt_atTop (0:ℝ)] with X hpow hX
  have hh := mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hX.le (1009/10000))
  have he : X^(1009/10000:ℝ)*X^(1/10000:ℝ)=X^(101/1000:ℝ) := by rw [←Real.rpow_add hX]; norm_num
  rw [he] at hh
  unfold PositiveSharpPowerWindow.halfWidth
  linarith

run_cmd do
  for decl in [``eventually_upper_square, ``eventually_active_upper_square, ``eventually_halfWidth_fits] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end OuterUpperFrequencyWork
