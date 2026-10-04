import CheckedSamplingTypeIAssembly

/-!
Discharge the seed's exact LargePhaseMangoldtCancellation obligation from
the proved Type I and Type II estimates. No cancellation premise remains.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open scoped BigOperators

namespace MangoldtCancellation
open Erdos374.Vaughan145 Erdos374.ReciprocalCharacter151
open DyadicVaughan

theorem mangoldt_fourier (γ : ℝ) (hγ : 0 < γ) (A : ℕ) :
    ∃ B P₀ : ℕ, ∀ P M b : ℕ, P₀ ≤ P → P ≤ M → M ≤ 2 * P →
      1 ≤ b → (b : ℝ) ^ γ ≤ (P : ℝ) → ∀ n m : ℤ,
        n.natAbs + m.natAbs ≤ ⌈Real.log (P : ℝ) ^ 6⌉₊ →
        Real.log (P : ℝ) ^ B < amplitude ((n : ℝ) * b) ((m : ℝ) * b) P →
        ‖phaseSum (Finset.Ioc P M)
          (fun k => character ((n : ℝ) * b) ((m : ℝ) * b) k) lam‖ ≤
          3 * (P : ℝ) / Real.log (P : ℝ) ^ A := by
  obtain ⟨BI, NI, hI⟩ := TypeIAssembly.typeI_fourier γ hγ A
  obtain ⟨BII, NII, hII⟩ := TypeIIAggregation.typeII_fourier γ hγ A
  obtain ⟨NL, hL⟩ :=
    Erdos374.RemainingAnalytic115.RemainingAnalytic127.eventually_log_ge127 1
  refine ⟨max BI BII, max 512 (max NI (max NII NL)), ?_⟩
  intro P M b hP hPM hM hb hbgamma n m hfreq hlarge
  have hlog := hL P (by omega)
  have hIlarge := (pow_le_pow_right₀ hlog (le_max_left BI BII)).trans_lt hlarge
  have hIIlarge := (pow_le_pow_right₀ hlog (le_max_right BI BII)).trans_lt hlarge
  have hi := hI P M b (by omega) hPM hM hb hbgamma n m hfreq hIlarge
  have hii := hII P M b (by omega) hM hb hbgamma n m hfreq hIIlarge
  have hid := Erdos374.VaughanBilinear152.vaughan_bilinear_identity
    (cutoff P) (cutoff P) P M
    (fun k => character ((n : ℝ) * b) ((m : ℝ) * b) k)
    (cutoff_properties P (by omega)).2.1
  rw [Erdos374.VaughanBilinear152.weighted_convolution_sum] at hii
  simp only [Nat.cast_mul] at hid hii
  rw [hid]
  apply (norm_add_le _ _).trans
  apply (add_le_add (norm_sub_le _ _) le_rfl).trans
  have hh := add_le_add (add_le_add hi.1 hi.2) hii
  convert hh using 1
  ring

/-- The exact analytic proposition that was an explicit premise in Update152. -/
theorem largePhaseMangoldtCancellation :
    Erdos374.MangoldtClosure152.LargePhaseMangoldtCancellation := by
  intro γ hγ
  obtain ⟨B, P₀, hc⟩ := mangoldt_fourier γ hγ 5
  refine ⟨B, 3, by norm_num, P₀, ?_⟩
  intro P b hP _hPtwo hb hbgamma n m _hnm hfreq hlarge M hPM hM
  have hh := hc P M b hP hPM hM hb hbgamma n m hfreq hlarge
  simpa only [Erdos374.PrimePowerRemoval151.mangoldtSum, phaseSum, lam,
    Erdos374.FourierLargePhase151.curveCharacter_eq_character] using hh

theorem largePhaseCharacterSampling :
    Erdos374.FourierLargePhase151.LargePhaseCharacterSampling :=
  Erdos374.MangoldtClosure152.large_phase_sampling_of_mangoldt
    largePhaseMangoldtCancellation

/-- The final density implication now has only the short-prime-interval premise. -/
theorem positive_lower_density
    (HF : Erdos374.HarmanDyadic151.RealBackwardDyadicExceptionalMeasure151) :
    Erdos374.PositiveLowerDensity Erdos374.D6 :=
  Erdos374.MangoldtClosure152.positive_lower_density152 HF
    largePhaseMangoldtCancellation

end MangoldtCancellation

#check MangoldtCancellation.largePhaseMangoldtCancellation
#print axioms MangoldtCancellation.largePhaseMangoldtCancellation
#print axioms MangoldtCancellation.positive_lower_density
run_cmd do
  for target in [``MangoldtCancellation.mangoldt_fourier,
      ``MangoldtCancellation.largePhaseMangoldtCancellation,
      ``MangoldtCancellation.largePhaseCharacterSampling,
      ``MangoldtCancellation.positive_lower_density] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "MANGOLDT CANCELLATION PASSED"

run_cmd do
  for target in [``MangoldtCancellation.mangoldt_fourier,
      ``MangoldtCancellation.largePhaseMangoldtCancellation,
      ``MangoldtCancellation.largePhaseCharacterSampling,
      ``MangoldtCancellation.positive_lower_density] do
    for ax in (← Lean.collectAxioms target) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "CHECKED SAMPLING PORT: ALL EXPORTED THEOREMS GUARDED"
