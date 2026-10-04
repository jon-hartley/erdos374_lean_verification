import CheckedSamplingPolynomialBandScales

/-!
Uniform polynomial-size coefficient applications of the proved Vaughan bands.
The starting scale grows once, before any band or coefficient is chosen.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open scoped BigOperators

namespace UniformVaughanBands
open PolynomialBandScales Erdos374.ReciprocalCharacter151
open Erdos374.Vaughan145 Erdos374.BilinearCorrelation152

structure ReadyBand (P D K cutoff exponent r S : ℕ) : Prop where
  outer_cutoff : cutoff ≤ D
  outer_two : 2 ≤ D
  inner_positive : 0 < K
  scale_two : 2 ≤ P
  log_one : 1 ≤ Real.log (P : ℝ)
  log_window : 16 * (2 : ℝ) ^ exponent ≤ Real.log (P : ℝ)
  log_saving : 24 * (4 : ℝ) ^ S ≤ Real.log (P : ℝ)
  near_scale : Real.log (D : ℝ) ^ (2 * S) ≤ (K : ℝ)
  frequency_budget : 32 * ((r + 3 : ℕ) : ℝ) * Real.log (P : ℝ) ^ 6 ≤ (P : ℝ)

theorem eventually_ready_band (cutoff exponent r S : ℕ) :
    ∃ P₀ : ℕ, ∀ P D K : ℕ, P₀ ≤ P → P ≤ D ^ 4 → P ≤ K ^ 4 →
      D * K ≤ 2 * P → ReadyBand P D K cutoff exponent r S := by
  obtain ⟨Nlog, hlog⟩ :=
    Erdos374.RemainingAnalytic115.RemainingAnalytic127.eventually_log_ge127
      (max 1 (max (16 * (2 : ℝ) ^ exponent) (24 * (4 : ℝ) ^ S)))
  obtain ⟨Ngrowth, hgrowth⟩ :=
    DifferenceParameters.eventually_const_mul_log_pow_le ((2 : ℝ) ^ (8 * S)) (8 * S)
  obtain ⟨Nfrequency, hfrequency⟩ :=
    DifferenceParameters.eventually_const_mul_log_pow_le (32 * ((r + 3 : ℕ) : ℝ)) 6
  refine ⟨max 16 (max (cutoff ^ 4) (max Nlog (max Ngrowth Nfrequency))), ?_⟩
  intro P D K hP hPD hPK hDK
  have hPtwo : 2 ≤ P := by omega
  have hDtwo : 2 ≤ D := cutoff_from_fourth_power 2 P D (by norm_num; omega) hPD
  have hKtwo : 2 ≤ K := cutoff_from_fourth_power 2 P K (by norm_num; omega) hPK
  have hlogs := band_log_bounds P D K hPtwo (by omega) (by omega) hPD hDK
  have hlogP := hlog P (by omega)
  refine ⟨cutoff_from_fourth_power cutoff P D (by omega) hPD, hDtwo,
    by omega, hPtwo, (le_max_left _ _).trans hlogP,
    (le_max_left _ _).trans ((le_max_right _ _).trans hlogP),
    (le_max_right _ _).trans ((le_max_right _ _).trans hlogP), ?_,
    hfrequency P (by omega)⟩
  exact near_scale_available S P D K
    (Real.log_nonneg (by exact_mod_cast (show 1 ≤ D by omega))) hlogs.2.1
    (hgrowth P (by omega)) hPK

theorem reciprocal_amplitude_bound (P u v : ℝ) (hP : 0 < P)
    (hv : |v| ≤ P * |u|) : amplitude u v P ≤ 2 * |u| / P := by
  unfold amplitude
  have hh : |v| / P ^ 2 ≤ |u| / P := by
    apply (div_le_div_iff₀ (by positivity) hP).mpr
    have := mul_le_mul_of_nonneg_right hv hP.le
    nlinarith only [this]
  calc
    _ ≤ |u| / P + |u| / P := add_le_add (le_refl _) hh
    _ = _ := by ring

theorem reciprocal_lower_window (exponent : ℕ) (P D K u v : ℝ)
    (hP : 0 < P)
    (hlogP : 0 < Real.log P) (hlogD : 0 ≤ Real.log D)
    (hDK : D * K ≤ 2 * P) (hlog : Real.log D ≤ 2 * Real.log P)
    (hwindow : 16 * (2 : ℝ) ^ exponent ≤ Real.log P)
    (hv : |v| ≤ P * |u|)
    (hlarge : Real.log P ^ (exponent + 1) < amplitude u v P) :
    4 * K * D * Real.log D ^ exponent ≤ |u| := by
  have hamp := hlarge.trans_le (reciprocal_amplitude_bound P u v hP hv)
  have hu : P * Real.log P ^ (exponent + 1) < 2 * |u| := by
    have hh := (lt_div_iff₀ hP).mp hamp
    nlinarith only [hh]
  have hp := pow_le_pow_left₀ hlogD hlog exponent
  rw [mul_pow] at hp
  have hprod := mul_le_mul hDK hp (pow_nonneg hlogD _) (by positivity : 0 ≤ 2 * P)
  have hsmall := mul_le_mul_of_nonneg_right hwindow
    (show 0 ≤ P * Real.log P ^ exponent by positivity)
  rw [pow_succ (Real.log P) exponent] at hu
  nlinarith only [hprod, hsmall, hu]

theorem square_lower_window (exponent : ℕ) (P D K v : ℝ)
    (hP : 0 < P) (hD : 0 ≤ D) (hK : 0 ≤ K)
    (hlogP : 0 < Real.log P) (hlogD : 0 ≤ Real.log D)
    (hDK : D * K ≤ 2 * P) (hlog : Real.log D ≤ 2 * Real.log P)
    (hwindow : 16 * (2 : ℝ) ^ exponent ≤ Real.log P)
    (hlarge : Real.log P ^ (exponent + 1) < amplitude 0 v P) :
    4 * K ^ 2 * D ^ 2 * Real.log D ^ exponent ≤ |v| := by
  have hv : P ^ 2 * Real.log P ^ (exponent + 1) < |v| := by
    simp only [amplitude, abs_zero, zero_div, zero_add] at hlarge
    have hh := (lt_div_iff₀ (by positivity : 0 < P ^ 2)).mp hlarge
    nlinarith only [hh]
  have hDKsq : D ^ 2 * K ^ 2 ≤ 4 * P ^ 2 := by
    have := pow_le_pow_left₀ (mul_nonneg hD hK) hDK 2
    nlinarith only [this]
  have hp := pow_le_pow_left₀ hlogD hlog exponent
  rw [mul_pow] at hp
  have hprod := mul_le_mul hDKsq hp (pow_nonneg hlogD _) (by positivity : 0 ≤ 4 * P ^ 2)
  have hsmall := mul_le_mul_of_nonneg_right hwindow
    (show 0 ≤ P ^ 2 * Real.log P ^ exponent by positivity)
  rw [pow_succ (Real.log P) exponent] at hv
  nlinarith only [hprod, hsmall, hv]

theorem reciprocal_uniform_band (J A : ℕ) :
    ∃ B P₀ : ℕ, ∀ P D E K M U V : ℕ, P₀ ≤ P →
      P ≤ D ^ 4 → P ≤ K ^ 4 → P ≤ 4 * (D * K) → D * K ≤ 2 * P → E ≤ 2 * D →
      ∀ u v : ℝ, u ≠ 0 → |u| ≤ (P : ℝ) ^ (J + 1) →
        |v| ≤ 2 * Real.log (P : ℝ) ^ 6 * |u| →
        Real.log (P : ℝ) ^ B < amplitude u v P →
        ‖∑ d ∈ Finset.Ioc D E, (high U muR d : ℂ) *
          ∑ k ∈ Finset.Ioc K (2 * K), (beta V k : ℂ) * bandCharacter P M u v d k‖ ≤
          (P : ℝ) / Real.log (P : ℝ) ^ A := by
  let r := 4 * (J + 1) + 1
  let S := A + 2
  obtain ⟨B, cutoff, hc⟩ := VaughanBands.reciprocal_band r S
  obtain ⟨P₀, hready⟩ := eventually_ready_band cutoff (B + 2 * S) r S
  refine ⟨B + 2 * S + 1, P₀, ?_⟩
  intro P D E K M U V hP hPD hPK hDKlo hDKhi hE u v hu huUpper hratio hlarge
  have ready := hready P D K hP hPD hPK hDKhi
  have hPr : (0 : ℝ) < P := by exact_mod_cast (show 0 < P by have := ready.scale_two; omega)
  have hlogP : 0 < Real.log (P : ℝ) := by linarith [ready.log_one]
  have hlogD : 0 < Real.log (D : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < D by have := ready.outer_two; omega))
  have hlogs := band_log_bounds P D K ready.scale_two
    (by have := ready.outer_two; omega) ready.inner_positive hPD hDKhi
  have hsmallFrequency : 2 * Real.log (P : ℝ) ^ 6 ≤ (P : ℝ) := by
    have hcoeff : (2 : ℝ) ≤ 32 * ((r + 3 : ℕ) : ℝ) := by
      push_cast
      linarith [Nat.cast_nonneg (α := ℝ) r]
    exact (mul_le_mul_of_nonneg_right hcoeff (by positivity)).trans ready.frequency_budget
  have hv : |v| ≤ (P : ℝ) * |u| :=
    hratio.trans (mul_le_mul_of_nonneg_right hsmallFrequency (abs_nonneg u))
  have hlow := reciprocal_lower_window (B + 2 * S) P D K u v hPr
    hlogP hlogD.le
    (by exact_mod_cast hDKhi) hlogs.2.1 ready.log_window hv hlarge
  have hupper := (polynomial_coefficient_upper J P D K u ready.outer_two
    (by have := ready.inner_positive; omega) hPD huUpper).1
  have hshape : 4 * ((r + 3 : ℕ) : ℝ) * |v| ≤ |u| * (D : ℝ) * (K : ℝ) := by
    have hband : (P : ℝ) ≤ 4 * ((D : ℝ) * (K : ℝ)) := by exact_mod_cast hDKlo
    have hfreq : 8 * ((r + 3 : ℕ) : ℝ) * Real.log (P : ℝ) ^ 6 ≤ (D : ℝ) * (K : ℝ) := by
      nlinarith only [ready.frequency_budget, hband]
    have hh := mul_le_mul_of_nonneg_right hfreq (abs_nonneg u)
    have hv' := mul_le_mul_of_nonneg_left hratio (show 0 ≤ 4 * ((r + 3 : ℕ) : ℝ) by positivity)
    nlinarith only [hh, hv']
  have hsum := hc D E K P M U V ready.outer_cutoff hE ready.near_scale
    u v hu hlow hupper hshape
  exact hsum.trans (band_saving A P D K (Nat.cast_nonneg P) hlogP hlogD
    (Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * K by have := ready.inner_positive; omega)))
    (by exact_mod_cast hDKhi) hlogs.1 hlogs.2.2 ready.log_saving)

theorem square_uniform_band (J A : ℕ) :
    ∃ B P₀ : ℕ, ∀ P D E K M U V : ℕ, P₀ ≤ P →
      P ≤ D ^ 4 → P ≤ K ^ 4 → D * K ≤ 2 * P → E ≤ 2 * D →
      ∀ v : ℝ, |v| ≤ (P : ℝ) ^ (J + 1) →
        Real.log (P : ℝ) ^ B < amplitude 0 v P →
        ‖∑ d ∈ Finset.Ioc D E, (high U muR d : ℂ) *
          ∑ k ∈ Finset.Ioc K (2 * K), (beta V k : ℂ) * bandCharacter P M 0 v d k‖ ≤
          (P : ℝ) / Real.log (P : ℝ) ^ A := by
  let r := 4 * (J + 1) + 1
  let S := A + 2
  obtain ⟨B, cutoff, hc⟩ := VaughanBands.square_band r S
  obtain ⟨P₀, hready⟩ := eventually_ready_band cutoff (B + 2 * S) r S
  refine ⟨B + 2 * S + 1, P₀, ?_⟩
  intro P D E K M U V hP hPD hPK hDKhi hE v hvUpper hlarge
  have ready := hready P D K hP hPD hPK hDKhi
  have hPr : (0 : ℝ) < P := by exact_mod_cast (show 0 < P by have := ready.scale_two; omega)
  have hlogP : 0 < Real.log (P : ℝ) := by linarith [ready.log_one]
  have hlogD : 0 < Real.log (D : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < D by have := ready.outer_two; omega))
  have hlogs := band_log_bounds P D K ready.scale_two
    (by have := ready.outer_two; omega) ready.inner_positive hPD hDKhi
  have hlow := square_lower_window (B + 2 * S) P D K v hPr
    (Nat.cast_nonneg D) (Nat.cast_nonneg K) hlogP hlogD.le
    (by exact_mod_cast hDKhi) hlogs.2.1 ready.log_window hlarge
  have hupper := (polynomial_coefficient_upper J P D K v ready.outer_two
    (by have := ready.inner_positive; omega) hPD hvUpper).2
  have hsum := hc D E K P M U V ready.outer_cutoff hE ready.near_scale v hlow hupper
  exact hsum.trans (band_saving A P D K (Nat.cast_nonneg P) hlogP hlogD
    (Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * K by have := ready.inner_positive; omega)))
    (by exact_mod_cast hDKhi) hlogs.1 hlogs.2.2 ready.log_saving)

end UniformVaughanBands

#print axioms UniformVaughanBands.reciprocal_uniform_band
#print axioms UniformVaughanBands.square_uniform_band
run_cmd do
  for target in [``UniformVaughanBands.reciprocal_uniform_band,
      ``UniformVaughanBands.square_uniform_band] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "UNIFORM VAUGHAN BANDS PASSED"

run_cmd do
  for target in [``UniformVaughanBands.eventually_ready_band,
      ``UniformVaughanBands.reciprocal_amplitude_bound,
      ``UniformVaughanBands.reciprocal_lower_window,
      ``UniformVaughanBands.square_lower_window,
      ``UniformVaughanBands.reciprocal_uniform_band,
      ``UniformVaughanBands.square_uniform_band] do
    for ax in (← Lean.collectAxioms target) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "CHECKED SAMPLING PORT: ALL EXPORTED THEOREMS GUARDED"
