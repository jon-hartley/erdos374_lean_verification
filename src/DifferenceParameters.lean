import Erdos374_Update152

/-!
Construct shift parameters for the seed's higher finite difference bound.
This extends HigherDifferenceChoice152 rather than postulating a new
exponential-sum estimate. Names in this namespace are new project names.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Filter
open scoped BigOperators

namespace DifferenceParameters
open Erdos374.HigherDifference152
open Erdos374.HigherDifferenceChoice152

theorem balanced_scale_cancellation
    (r M N : ℕ) (f : ℕ → ℝ) (scale C ε : ℝ)
    (hN : 0 < N) (hM : M ≤ N) (hscale : 1 ≤ scale)
    (hC : 1 ≤ C) (hε : 0 < ε) (hεone : ε ≤ 1)
    (hscaleUpper : 4 * scale ≤ (N : ℝ) * ε ^ (2 ^ r))
    (hambient : 32 * C * (1 + Real.log ((N : ℝ) + 1)) ≤
      (N : ℝ) * ε ^ (2 ^ r))
    (hscaleLower :
      64 * C * (1 + Real.log ((N : ℝ) + 1)) * (4 : ℝ) ^ r ≤
        scale * (ε ^ (2 ^ r)) ^ (r + 2))
    (hd : ∀ n < M,
      scale ^ (r + 1) / (N : ℝ) ^ (r + 2) ≤
          difference (r + 2) f n ∧
      difference (r + 2) f n ≤
        C * (scale ^ (r + 1) / (N : ℝ) ^ (r + 2)))
    (hm : MonotoneOn (difference (r + 2) f) (Set.Iio M) ∨
      AntitoneOn (difference (r + 2) f) (Set.Iio M)) :
    ‖∑ n ∈ Finset.range M, Erdos374.KusminLandau151.e (f n)‖ ≤
      10 * ε * (N : ℝ) := by
  let d : ℝ := ε ^ (2 ^ r)
  let T : ℝ := (N : ℝ) / scale
  let K : ℝ := 1 / d
  let L : ℝ := scale ^ (r + 1) / (N : ℝ) ^ (r + 2)
  let B : ℝ := 32 * C * (1 + Real.log ((N : ℝ) + 1))
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hs : 0 < scale := by linarith
  have hdpos : 0 < d := pow_pos hε _
  have hdone : d ≤ 1 := pow_le_one₀ hε.le hεone
  have hKpos : 0 < K := by dsimp [K]; positivity
  have hlog : 0 ≤ Real.log ((N : ℝ) + 1) :=
    Real.log_nonneg (by linarith)
  have hBpos : 0 < B := by dsimp [B]; positivity
  have hKone : 1 ≤ K := by
    dsimp [K]
    exact (le_div_iff₀ hdpos).mpr (by simpa using hdone)
  have hTK : 4 * K ≤ T := by
    dsimp [K, T]
    apply (le_div_iff₀ hs).mpr
    rw [show 4 * (1 / d) * scale = (4 * scale) / d by ring]
    apply (div_le_iff₀ hdpos).mpr
    exact hscaleUpper
  have hTN : T ≤ (N : ℝ) := by
    dsimp [T]
    exact div_le_self hNr.le hscale
  have hdiag : 2 / T ≤ d := by
    dsimp [T]
    rw [div_div_eq_mul_div]
    apply (div_le_iff₀ hNr).mpr
    dsimp [d]
    nlinarith
  have hdiscard : 1 / K ≤ d := by simp [K]
  have hfirst : (N : ℝ) ^ 2 * (T ^ r * L) = scale := by
    dsimp [T, L]
    simp only [div_pow, pow_add, pow_one]
    field_simp
  have hsecond : 1 / ((T / (4 * K)) ^ r * L) =
      (4 * K) ^ r * (N : ℝ) ^ 2 / scale := by
    dsimp [T, L]
    simp only [div_pow, pow_add, pow_one]
    field_simp
  have hleft : B * scale ≤ d ^ 2 * (N : ℝ) ^ 2 / 2 := by
    have hBU : B ≤ (N : ℝ) * d := hambient
    have hsU : scale ≤ (N : ℝ) * d / 4 := by
      dsimp [d]
      linarith
    have hprod := mul_le_mul hBU hsU hs.le
      (mul_nonneg hNr.le hdpos.le)
    nlinarith [sq_nonneg ((N : ℝ) * d)]
  have hscaled : 2 * B * (4 * K) ^ r ≤ scale * d ^ 2 := by
    dsimp [K]
    rw [mul_one_div, div_pow]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (pow_pos hdpos r)).mpr
    have hh : 2 * B * (4 : ℝ) ^ r ≤ scale * d ^ (r + 2) := by
      dsimp [B, d]
      nlinarith [hscaleLower]
    convert hh using 1
    ring
  have hright : B * ((4 * K) ^ r * (N : ℝ) ^ 2 / scale) ≤
      d ^ 2 * (N : ℝ) ^ 2 / 2 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    have hh := mul_le_mul_of_nonneg_right hscaled (sq_nonneg (N : ℝ))
    calc
      _ = (2 * B * (4 * K) ^ r * (N : ℝ) ^ 2) / scale := by ring
      _ ≤ _ := (div_le_iff₀ hs).mpr (by nlinarith only [hh])
  apply cancellation_real_parameters_on_prefix r M N f L C ε T K
    hM (by dsimp [L]; positivity) hC hε hεone hKone hTK hTN
    hdiag hdiscard _ hd hm
  change B * ((N : ℝ) ^ 2 * (T ^ r * L) +
    1 / ((T / (4 * K)) ^ r * L)) ≤ _
  rw [hfirst, hsecond]
  have hbudget : ε ^ (2 ^ (r + 1)) = d ^ 2 := by
    dsimp [d]
    rw [← pow_mul, pow_succ]
  rw [hbudget]
  linarith

theorem eventually_const_mul_log_pow_le (coefficient : ℝ) (power : ℕ) :
    ∃ cutoff : ℕ, ∀ N : ℕ, cutoff ≤ N →
      coefficient * (Real.log (N : ℝ)) ^ power ≤ (N : ℝ) := by
  have hlimit : Tendsto
      (fun x : ℝ => coefficient * (Real.log x) ^ power / x)
      atTop (nhds 0) := by
    simpa only [Real.rpow_natCast, Real.rpow_one, mul_zero,
      mul_div_assoc] using
      (Real.tendsto_pow_log_div_pow_atTop 1 power (by norm_num)).const_mul
        coefficient
  obtain ⟨threshold, hthreshold⟩ := eventually_atTop.mp
    (hlimit.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)))
  obtain ⟨cutoff, hcutoff⟩ := exists_nat_ge (max threshold 1)
  refine ⟨cutoff, ?_⟩
  intro N hN
  have hNr : max threshold 1 ≤ (N : ℝ) :=
    hcutoff.trans (Nat.cast_le.mpr hN)
  have hpos : (0 : ℝ) < N := by
    have := (le_max_right threshold 1).trans hNr
    linarith
  have hb := hthreshold (N : ℝ) ((le_max_left _ _).trans hNr)
  have hlt : coefficient * (Real.log (N : ℝ)) ^ power < (N : ℝ) := by
    simpa only [one_mul] using (div_lt_iff₀ hpos).mp hb
  exact hlt.le

/-- A sufficient logarithmic amplitude threshold; no sharpness is claimed. -/
def logarithmicThresholdExponent (r A : ℕ) : ℕ :=
  (r + 1) * (A * 2 ^ r * (r + 2) + 2)

/-- Uniform cancellation over a full range of derivative sizes. All shift
choices and numerical window conditions are discharged. For r >= 1 this
range is eventually nonempty. The remaining hypotheses concern only the
actual finite differences of f and their monotonicity. -/
theorem cancellation_logarithmic_range (r A : ℕ) (C : ℝ) (hC : 1 ≤ C) :
    ∃ cutoff : ℕ, ∀ N M : ℕ, cutoff ≤ N → M ≤ N →
      ∀ L : ℝ,
        (Real.log (N : ℝ)) ^ logarithmicThresholdExponent r A /
            (N : ℝ) ^ (r + 2) ≤ L →
        L ≤ 1 / (N : ℝ) ^ 2 →
        ∀ f : ℕ → ℝ,
          (∀ n < M, L ≤ difference (r + 2) f n ∧
            difference (r + 2) f n ≤ C * L) →
          (MonotoneOn (difference (r + 2) f) (Set.Iio M) ∨
            AntitoneOn (difference (r + 2) f) (Set.Iio M)) →
          ‖∑ n ∈ Finset.range M, Erdos374.KusminLandau151.e (f n)‖ ≤
            10 * (N : ℝ) / (Real.log (N : ℝ)) ^ A := by
  let e := A * 2 ^ r
  let k := e * (r + 2) + 2
  obtain ⟨Nlog, hNlog⟩ :=
    Erdos374.RemainingAnalytic115.RemainingAnalytic127.eventually_log_ge127
      (max 1 (192 * C * (4 : ℝ) ^ r))
  obtain ⟨Nupper, hNupper⟩ :=
    eventually_const_mul_log_pow_le ((4 : ℝ) ^ (r + 1)) (e * (r + 1))
  obtain ⟨Nambient, hNambient⟩ :=
    eventually_const_mul_log_pow_le (96 * C) (e + 1)
  refine ⟨max 2 (max Nlog (max Nupper Nambient)), ?_⟩
  intro N M hN hM L hLlower hLupper f hd hm
  have hNtwo : 2 ≤ N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlogBound := hNlog N (by omega)
  have hlogOne : 1 ≤ Real.log (N : ℝ) :=
    (le_max_left _ _).trans hlogBound
  have hlogPos : 0 < Real.log (N : ℝ) := by linarith
  have hLpos : 0 < L := lt_of_lt_of_le (by positivity) hLlower
  let scale := ((N : ℝ) ^ (r + 2) * L) ^ (1 / ((r + 1 : ℕ) : ℝ))
  have hs : 0 < scale := Real.rpow_pos_of_pos (by positivity) _
  have hscalePow : scale ^ (r + 1) = (N : ℝ) ^ (r + 2) * L := by
    dsimp [scale]
    rw [← Real.rpow_mul_natCast (by positivity)]
    have heq : (1 / ((r + 1 : ℕ) : ℝ)) * ((r + 1 : ℕ) : ℝ) = 1 := by
      field_simp
    rw [heq, Real.rpow_one]
  have hscaleLower : (Real.log (N : ℝ)) ^ k ≤ scale := by
    apply (pow_le_pow_iff_left₀ (by positivity) hs.le (by omega : r + 1 ≠ 0)).mp
    rw [hscalePow, ← pow_mul]
    have hb := (div_le_iff₀ (pow_pos hNr (r + 2))).mp hLlower
    simpa only [logarithmicThresholdExponent, k, e, Nat.mul_comm,
      mul_comm L] using hb
  have hscaleOne : 1 ≤ scale :=
    (one_le_pow₀ hlogOne).trans hscaleLower
  have hscalePowUpper : scale ^ (r + 1) ≤ (N : ℝ) ^ r := by
    rw [hscalePow]
    calc
      _ ≤ (N : ℝ) ^ (r + 2) * (1 / (N : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hLupper (by positivity)
      _ = _ := by rw [pow_add]; field_simp
  have hupperLog := hNupper N (by omega)
  have hscaleUpper : 4 * scale * (Real.log (N : ℝ)) ^ e ≤ (N : ℝ) := by
    apply (pow_le_pow_iff_left₀ (by positivity) hNr.le (by omega : r + 1 ≠ 0)).mp
    calc
      _ = (4 : ℝ) ^ (r + 1) * scale ^ (r + 1) *
          (Real.log (N : ℝ)) ^ (e * (r + 1)) := by
        rw [mul_pow, mul_pow, ← pow_mul]
      _ ≤ (4 : ℝ) ^ (r + 1) * (N : ℝ) ^ r *
          (Real.log (N : ℝ)) ^ (e * (r + 1)) := by
        gcongr
      _ = (N : ℝ) ^ r * ((4 : ℝ) ^ (r + 1) *
          (Real.log (N : ℝ)) ^ (e * (r + 1))) := by ring
      _ ≤ (N : ℝ) ^ r * (N : ℝ) :=
        mul_le_mul_of_nonneg_left hupperLog (by positivity)
      _ = _ := (pow_succ _ _).symm
  have hlogNext : 1 + Real.log ((N : ℝ) + 1) ≤
      3 * Real.log (N : ℝ) := by
    have hNreal : (2 : ℝ) ≤ N := by exact_mod_cast hNtwo
    have hlogSquare := Real.log_le_log
      (by positivity : (0 : ℝ) < (N : ℝ) + 1)
      (show (N : ℝ) + 1 ≤ (N : ℝ) ^ 2 by nlinarith)
    rw [Real.log_pow] at hlogSquare
    norm_num at hlogSquare
    linarith
  let ε := 1 / (Real.log (N : ℝ)) ^ A
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεone : ε ≤ 1 := by
    dsimp [ε]
    exact (div_le_one (pow_pos hlogPos A)).mpr (one_le_pow₀ hlogOne)
  have hdIdentity : ε ^ (2 ^ r) = 1 / (Real.log (N : ℝ)) ^ e := by
    simp [ε, e, ← pow_mul]
  have hLidentity : scale ^ (r + 1) / (N : ℝ) ^ (r + 2) = L := by
    rw [hscalePow]
    field_simp
  have hsum := balanced_scale_cancellation r M N f scale C ε
    (by omega) hM hscaleOne hC hε hεone
    (by rw [hdIdentity, mul_one_div];
        exact (le_div_iff₀ (pow_pos hlogPos e)).mpr hscaleUpper)
    (by
      rw [hdIdentity, mul_one_div]
      apply (le_div_iff₀ (pow_pos hlogPos e)).mpr
      calc
        _ ≤ (32 * C * (3 * Real.log (N : ℝ))) *
            (Real.log (N : ℝ)) ^ e := by gcongr
        _ = 96 * C * (Real.log (N : ℝ)) ^ (e + 1) := by rw [pow_succ]; ring
        _ ≤ _ := hNambient N (by omega))
    (by
      rw [hdIdentity]
      have hthreshold : 192 * C * (4 : ℝ) ^ r ≤ Real.log (N : ℝ) :=
        (le_max_right _ _).trans hlogBound
      calc
        _ ≤ 192 * C * (4 : ℝ) ^ r * Real.log (N : ℝ) := by
          have hh := mul_le_mul_of_nonneg_left hlogNext
            (show 0 ≤ 64 * C * (4 : ℝ) ^ r by positivity)
          nlinarith only [hh]
        _ ≤ (Real.log (N : ℝ)) ^ 2 := by
          nlinarith [mul_le_mul_of_nonneg_right hthreshold hlogPos.le]
        _ = (Real.log (N : ℝ)) ^ k *
            (1 / (Real.log (N : ℝ)) ^ e) ^ (r + 2) := by
          dsimp [k]
          rw [div_pow, one_pow, ← pow_mul, pow_add]
          field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_right hscaleLower (by positivity))
    (by simpa only [hLidentity] using hd) hm
  convert hsum using 1
  dsimp [ε]
  ring

end DifferenceParameters

#print axioms DifferenceParameters.balanced_scale_cancellation
#print axioms DifferenceParameters.cancellation_logarithmic_range
run_cmd do
  for target in [``DifferenceParameters.balanced_scale_cancellation,
      ``DifferenceParameters.cancellation_logarithmic_range] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "DIFFERENCE PARAMETERS PASSED"
