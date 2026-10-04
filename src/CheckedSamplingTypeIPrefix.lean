import CheckedSamplingTypeIIAggregation

/-!
Prefix scales and coefficient windows for the Type I Vaughan terms.
The scale floor(P/d)+1 includes the possible final endpoint exactly.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open scoped BigOperators

namespace TypeIPrefix
open Erdos374.ReciprocalCharacter151

def prefixScale (P d : ℕ) : ℕ := P / d + 1

theorem prefix_scale_bounds (P d : ℕ) (hd : 0 < d) (hdP : d ≤ P) :
    P < d * prefixScale P d ∧ d * prefixScale P d ≤ 2 * P := by
  have hlo := (Nat.div_lt_iff_lt_mul hd).mp (show P / d < P / d + 1 by omega)
  have hhi := Nat.div_mul_le_self P d
  unfold prefixScale
  constructor <;> nlinarith

theorem prefix_length_le (P M d : ℕ) (hd : 0 < d) (hM : M ≤ 2 * P) :
    M / d - P / d ≤ prefixScale P d := by
  have hlo := (Nat.div_lt_iff_lt_mul hd).mp (show P / d < P / d + 1 by omega)
  have hMupper : M < (2 * (P / d + 1)) * d := by nlinarith
  have hh := (Nat.div_lt_iff_lt_mul hd).mpr hMupper
  unfold prefixScale
  omega

theorem prefix_fourth_power (P d : ℕ) (hP : 512 ≤ P)
    (hd : 0 < d) (hdU : d ≤ DyadicVaughan.cutoff P ^ 2) :
    P ≤ prefixScale P d ^ 4 := by
  have hc := DyadicVaughan.cutoff_properties P hP
  have hprod : DyadicVaughan.cutoff P * d ≤ P := by
    have hh := Nat.mul_le_mul_left (DyadicVaughan.cutoff P) hdU
    nlinarith only [hh, hc.2.2.1]
  have hdiv : DyadicVaughan.cutoff P ≤ P / d :=
    (Nat.le_div_iff_mul_le hd).mpr hprod
  exact hc.2.2.2.trans (Nat.pow_le_pow_left (show DyadicVaughan.cutoff P ≤ prefixScale P d by
    unfold prefixScale; omega) 4)

structure ReadyPrefix (P N cutoff exponent r S : ℕ) : Prop where
  cutoff_le : cutoff ≤ N
  scale_two : 2 ≤ P
  prefix_two : 2 ≤ N
  log_one : 1 ≤ Real.log (P : ℝ)
  log_window : 16 * (2 : ℝ) ^ exponent ≤ Real.log (P : ℝ)
  log_saving : 10 * (4 : ℝ) ^ S ≤ Real.log (P : ℝ)
  frequency_budget : 4 * ((r + 3 : ℕ) : ℝ) * Real.log (P : ℝ) ^ 6 ≤ (P : ℝ)

theorem eventually_ready_prefix (cutoff exponent r S : ℕ) :
    ∃ P₀ : ℕ, ∀ P N : ℕ, P₀ ≤ P → P ≤ N ^ 4 →
      ReadyPrefix P N cutoff exponent r S := by
  obtain ⟨Nlog, hlog⟩ :=
    Erdos374.RemainingAnalytic115.RemainingAnalytic127.eventually_log_ge127
      (max 1 (max (16 * (2 : ℝ) ^ exponent) (10 * (4 : ℝ) ^ S)))
  obtain ⟨Nfreq, hfreq⟩ := DifferenceParameters.eventually_const_mul_log_pow_le
    (4 * ((r + 3 : ℕ) : ℝ)) 6
  refine ⟨max 16 (max (cutoff ^ 4) (max Nlog Nfreq)), ?_⟩
  intro P N hP hPN
  have hlogP := hlog P (by omega)
  exact ⟨PolynomialBandScales.cutoff_from_fourth_power cutoff P N (by omega) hPN,
    by omega, PolynomialBandScales.cutoff_from_fourth_power 2 P N (by norm_num; omega) hPN,
    (le_max_left _ _).trans hlogP,
    (le_max_left _ _).trans ((le_max_right _ _).trans hlogP),
    (le_max_right _ _).trans ((le_max_right _ _).trans hlogP), hfreq P (by omega)⟩

theorem prefix_saving (A : ℕ) (P N : ℝ)
    (hN : 0 ≤ N) (hlogP : 0 < Real.log P) (hlogN : 0 < Real.log N)
    (hcompare : Real.log P ≤ 4 * Real.log N)
    (hlarge : 10 * (4 : ℝ) ^ (A + 1) ≤ Real.log P) :
    10 * N / Real.log N ^ (A + 1) ≤ N / Real.log P ^ A := by
  have hden : Real.log P ^ (A + 1) ≤ (4 : ℝ) ^ (A + 1) * Real.log N ^ (A + 1) := by
    simpa only [mul_pow] using pow_le_pow_left₀ hlogP.le hcompare (A + 1)
  have hinv : 1 / Real.log N ^ (A + 1) ≤ (4 : ℝ) ^ (A + 1) / Real.log P ^ (A + 1) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    simpa only [one_mul] using hden
  calc
    _ ≤ 10 * N * ((4 : ℝ) ^ (A + 1) / Real.log P ^ (A + 1)) := by
      simpa only [div_eq_mul_inv, one_mul] using
        mul_le_mul_of_nonneg_left hinv (show 0 ≤ 10 * N by positivity)
    _ = (10 * (4 : ℝ) ^ (A + 1) / Real.log P) * (N / Real.log P ^ A) := by
      rw [pow_succ (Real.log P) A]; field_simp
    _ ≤ 1 * (N / Real.log P ^ A) :=
      mul_le_mul_of_nonneg_right ((div_le_one hlogP).mpr hlarge) (by positivity)
    _ = _ := one_mul _

theorem reciprocal_prefix (J A : ℕ) :
    ∃ B P₀ : ℕ, ∀ P N T d : ℕ, P₀ ≤ P → P ≤ N ^ 4 →
      P ≤ d * N → d * N ≤ 2 * P → 0 < d → T ≤ N →
      ∀ u v : ℝ, u ≠ 0 → |u| ≤ (P : ℝ) ^ (J + 1) →
        |v| ≤ 2 * Real.log (P : ℝ) ^ 6 * |u| →
        Real.log (P : ℝ) ^ B < amplitude u v P →
        ‖∑ n ∈ Finset.range T, Erdos374.KusminLandau151.e
          (Erdos374.ReciprocalPhaseShape152.sequencePhase (N : ℝ)
            (u / d) (v / (d : ℝ) ^ 2) n)‖ ≤ (N : ℝ) / Real.log (P : ℝ) ^ A := by
  let r := 4 * (J + 1) + 1
  obtain ⟨B, cutoff, hc⟩ := ReciprocalCancellation.reciprocal_cancellation r (A + 1)
  obtain ⟨P₀, hready⟩ := eventually_ready_prefix cutoff B r (A + 1)
  refine ⟨B + 1, P₀, ?_⟩
  intro P N T d hP hPN hprodLow hprodHigh hd hT u v _hu huUpper hratio hlarge
  have ready := hready P N hP hPN
  have hPr : (0 : ℝ) < P := by exact_mod_cast (show 0 < P by have := ready.scale_two; omega)
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by have := ready.prefix_two; omega)
  have hdr : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hlogP : 0 < Real.log (P : ℝ) := by linarith [ready.log_one]
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos
    (by exact_mod_cast (show 1 < N by have := ready.prefix_two; omega))
  have hlogs := PolynomialBandScales.band_log_bounds P N d ready.scale_two
    (by have := ready.prefix_two; omega) hd hPN (by simpa only [Nat.mul_comm] using hprodHigh)
  have hsmall : 2 * Real.log (P : ℝ) ^ 6 ≤ (P : ℝ) := by
    have hh : (2 : ℝ) ≤ 4 * ((r + 3 : ℕ) : ℝ) := by push_cast; linarith [Nat.cast_nonneg (α := ℝ) r]
    exact (mul_le_mul_of_nonneg_right hh (by positivity)).trans ready.frequency_budget
  have hvP : |v| ≤ (P : ℝ) * |u| :=
    hratio.trans (mul_le_mul_of_nonneg_right hsmall (abs_nonneg u))
  have hlow := UniformVaughanBands.reciprocal_lower_window B P N d u v hPr
    hlogP hlogN.le (by exact_mod_cast (show N * d ≤ 2 * P by simpa only [Nat.mul_comm] using hprodHigh))
    hlogs.2.1 ready.log_window hvP hlarge
  have hupper := (PolynomialBandScales.polynomial_coefficient_upper J P N d u
    ready.prefix_two (by omega) hPN huUpper).1
  have hlowerDiv : (N : ℝ) * Real.log (N : ℝ) ^ B ≤ |u / d| := by
    rw [abs_div, abs_of_pos hdr]
    apply (le_div_iff₀ hdr).mpr
    nlinarith [show 0 ≤ (d : ℝ) * (N : ℝ) * Real.log (N : ℝ) ^ B by positivity]
  have hupperDiv : |u / d| ≤ (N : ℝ) ^ r := by
    rw [abs_div, abs_of_pos hdr]
    apply (div_le_iff₀ hdr).mpr
    nlinarith [abs_nonneg u]
  have hshape : 2 * ((r + 3 : ℕ) : ℝ) * |v / (d : ℝ) ^ 2| ≤ |u / d| * (N : ℝ) := by
    have hprodR : (P : ℝ) ≤ (d : ℝ) * (N : ℝ) := by exact_mod_cast hprodLow
    have hh := mul_le_mul_of_nonneg_right ready.frequency_budget (abs_nonneg u)
    have hh' := mul_le_mul_of_nonneg_left hratio
      (show 0 ≤ 2 * ((r + 3 : ℕ) : ℝ) by positivity)
    have hdom : 2 * ((r + 3 : ℕ) : ℝ) * |v| ≤ |u| * (d : ℝ) * (N : ℝ) := by
      have hp := mul_le_mul_of_nonneg_right hprodR (abs_nonneg u)
      nlinarith only [hh, hh', hp]
    rw [abs_div, abs_div, abs_of_pos hdr, abs_of_pos (by positivity : 0 < (d : ℝ) ^ 2)]
    rw [← mul_div_assoc, div_mul_eq_mul_div]
    apply (div_le_div_iff₀ (by positivity : 0 < (d : ℝ) ^ 2) hdr).mpr
    nlinarith [mul_le_mul_of_nonneg_right hdom hdr.le]
  have hsum := hc N T ready.cutoff_le hT N (u / d) (v / (d : ℝ) ^ 2)
    (by rfl) (by linarith) hlowerDiv hupperDiv hshape
  exact hsum.trans (prefix_saving A P N hNr.le hlogP hlogN hlogs.1 ready.log_saving)

theorem square_prefix (J A : ℕ) :
    ∃ B P₀ : ℕ, ∀ P N T d : ℕ, P₀ ≤ P → P ≤ N ^ 4 →
      d * N ≤ 2 * P → 0 < d → T ≤ N →
      ∀ v : ℝ, |v| ≤ (P : ℝ) ^ (J + 1) →
        Real.log (P : ℝ) ^ B < amplitude 0 v P →
        ‖∑ n ∈ Finset.range T, Erdos374.KusminLandau151.e
          (Erdos374.ReciprocalPhaseShape152.sequencePhase (N : ℝ)
            0 (v / (d : ℝ) ^ 2) n)‖ ≤ (N : ℝ) / Real.log (P : ℝ) ^ A := by
  let r := 4 * (J + 1) + 1
  obtain ⟨B, cutoff, hc⟩ := SquareCancellation.square_cancellation r (A + 1)
  obtain ⟨P₀, hready⟩ := eventually_ready_prefix cutoff B r (A + 1)
  refine ⟨B + 1, P₀, ?_⟩
  intro P N T d hP hPN hprodHigh hd hT v hvUpper hlarge
  have ready := hready P N hP hPN
  have hPr : (0 : ℝ) < P := by exact_mod_cast (show 0 < P by have := ready.scale_two; omega)
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by have := ready.prefix_two; omega)
  have hdr : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hlogP : 0 < Real.log (P : ℝ) := by linarith [ready.log_one]
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos
    (by exact_mod_cast (show 1 < N by have := ready.prefix_two; omega))
  have hprod : N * d ≤ 2 * P := by simpa only [Nat.mul_comm] using hprodHigh
  have hlogs := PolynomialBandScales.band_log_bounds P N d ready.scale_two
    (by have := ready.prefix_two; omega) hd hPN hprod
  have hlow := UniformVaughanBands.square_lower_window B P N d v hPr
    hNr.le hdr.le hlogP hlogN.le (by exact_mod_cast hprod) hlogs.2.1 ready.log_window hlarge
  have hupper : 4 * |v| ≤ (d : ℝ) ^ 2 * (N : ℝ) ^ (r + 1) := by
    simpa only [r, Nat.add_assoc] using
      (PolynomialBandScales.polynomial_coefficient_upper J P N d v
        ready.prefix_two (by omega) hPN hvUpper).2
  have hlowerDiv : (N : ℝ) ^ 2 * Real.log (N : ℝ) ^ B ≤ |v / (d : ℝ) ^ 2| := by
    rw [abs_div, abs_of_pos (by positivity : 0 < (d : ℝ) ^ 2)]
    apply (le_div_iff₀ (by positivity : 0 < (d : ℝ) ^ 2)).mpr
    nlinarith [show 0 ≤ (d : ℝ) ^ 2 * (N : ℝ) ^ 2 * Real.log (N : ℝ) ^ B by positivity]
  have hupperDiv : |v / (d : ℝ) ^ 2| ≤ (N : ℝ) ^ (r + 1) := by
    rw [abs_div, abs_of_pos (by positivity : 0 < (d : ℝ) ^ 2)]
    apply (div_le_iff₀ (by positivity : 0 < (d : ℝ) ^ 2)).mpr
    nlinarith [abs_nonneg v]
  have hsum := hc N T ready.cutoff_le hT N (v / (d : ℝ) ^ 2)
    (by rfl) (by linarith) hlowerDiv hupperDiv
  exact hsum.trans (prefix_saving A P N hNr.le hlogP hlogN hlogs.1 ready.log_saving)

end TypeIPrefix

#print axioms TypeIPrefix.reciprocal_prefix
run_cmd do
  for target in [``TypeIPrefix.prefix_scale_bounds, ``TypeIPrefix.prefix_length_le,
      ``TypeIPrefix.prefix_fourth_power, ``TypeIPrefix.reciprocal_prefix,
      ``TypeIPrefix.square_prefix] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "TYPE I PREFIX PASSED"

run_cmd do
  for target in [``TypeIPrefix.prefix_scale_bounds,
      ``TypeIPrefix.prefix_length_le,
      ``TypeIPrefix.prefix_fourth_power,
      ``TypeIPrefix.eventually_ready_prefix,
      ``TypeIPrefix.prefix_saving,
      ``TypeIPrefix.reciprocal_prefix,
      ``TypeIPrefix.square_prefix] do
    for ax in (← Lean.collectAxioms target) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "CHECKED SAMPLING PORT: ALL EXPORTED THEOREMS GUARDED"
