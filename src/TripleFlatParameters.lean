import CofactorDoublingCoverage

/-! Uniform rational witnesses for the asymmetric flat-cofactor estimate.
The factor scales are arbitrary natural numbers in the stated region. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open Filter

namespace TripleFlatParameters
open MellinCofactorCoverage

def theta : ℝ := 1009 / 10000
def kappa : ℝ := 1 / 100000
def ell : ℝ := 9 / 35 - 1 / 10000
def eta : ℝ := 1 / 20000
def rho : ℝ := 1 / 20000
def upperExponent : ℝ := 562 / 625
def primeExponent : ℝ := 227 / 1000
def pairExponent : ℝ := 91 / 200

theorem theta_gt : 2 / 25 < theta := by norm_num [theta]
theorem ell_pos : 0 < ell := by norm_num [ell]
theorem eta_pos : 0 < eta := by norm_num [eta]
theorem rho_pos : 0 < rho := by norm_num [rho]
theorem rho_lt_one : rho < 1 := by norm_num [rho]
theorem kappa_pos : 0 < kappa := by norm_num [kappa]
theorem eta_eq_rho : eta = rho := rfl

structure Scales (X : ℝ) (M N : ℕ) : Prop where
  Mpos : 1 ≤ M
  Npos : 1 ≤ N
  Mupper : (M : ℝ) ≤ X
  Nupper : (N : ℝ) ≤ X
  Apos : (1 : ℝ) ≤ (M * N : ℕ)
  Aupper : ((M * N : ℕ) : ℝ) ≤ X
  cofactor_lower : X ^ ell ≤ (lowerCutoff X (M * N : ℕ) : ℝ)
  cofactor_pos : 1 ≤ lowerCutoff X (M * N : ℕ)
  cofactor_cover : upperCutoff X (M * N : ℕ) ≤
    2 ^ CofactorDoublingCoverage.blockCount * lowerCutoff X (M * N : ℕ)
  cofactor_upper : ((2 ^ CofactorDoublingCoverage.blockCount *
    lowerCutoff X (M * N : ℕ) : ℕ) : ℝ) ≤ X
  flat_length : X ^ eta * (X ^ upperExponent) ^ (2 / 7 : ℝ) ≤
    (lowerCutoff X (M * N : ℕ) : ℝ)
  Mlength : X ^ upperExponent ≤ (M : ℝ) ^ 4
  Nlength : X ^ upperExponent ≤ (N : ℝ) ^ 2
  frequency_lower : 2 * X ^ rho ≤ X ^ upperExponent
  frequency_upper : X ^ upperExponent ≤ X
  low_cofactor : X ^ rho ≤ (lowerCutoff X (M * N : ℕ) : ℝ) ^ (1 / 4 : ℝ)
  tail_lower : X ^ (1 - theta + kappa) ≤ X ^ upperExponent

theorem eventually_scales :
    ∀ᶠ X : ℝ in atTop, Real.exp 1 ≤ X ∧
      ∀ (M N : ℕ),
        X ^ primeExponent ≤ (M : ℝ) → X ^ pairExponent ≤ (N : ℝ) →
        ((M * N : ℕ) : ℝ) ≤ X ^ (26 / 35 : ℝ) → Scales X M N := by
  filter_upwards [CofactorDoublingCoverage.eventual_scales
      (341 / 500 : ℝ) ell (1 / 10000 : ℝ) (by norm_num) ell_pos (by norm_num),
    PolynomialLogEnvelope.eventually_constant_bound 2 (upperExponent - rho)
      (by norm_num) (by norm_num [upperExponent, rho]),
    eventually_ge_atTop (Real.exp 1)] with X hcover htwo hXexp
  refine ⟨hXexp, ?_⟩
  intro M N hM hN hA
  have hX : 1 ≤ X := by linarith [hcover.1]
  have hXp : 0 < X := by linarith
  have hMr : (1 : ℝ) ≤ M :=
    (Real.one_le_rpow hX (by norm_num [primeExponent])).trans hM
  have hNr : (1 : ℝ) ≤ N :=
    (Real.one_le_rpow hX (by norm_num [pairExponent])).trans hN
  have hMnat : 1 ≤ M := by exact_mod_cast hMr
  have hNnat : 1 ≤ N := by exact_mod_cast hNr
  have hAone : (1 : ℝ) ≤ (M * N : ℕ) := by push_cast; nlinarith
  have hAX : ((M * N : ℕ) : ℝ) ≤ X := hA.trans (by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hX (by norm_num : (26 / 35 : ℝ) ≤ 1))
  have hMX : (M : ℝ) ≤ X := by
    have hh : (M : ℝ) * N ≤ X := by simpa only [Nat.cast_mul] using hAX
    nlinarith
  have hNX : (N : ℝ) ≤ X := by
    have hh : (M : ℝ) * N ≤ X := by simpa only [Nat.cast_mul] using hAX
    nlinarith
  have hAlow : X ^ (341 / 500 : ℝ) ≤ ((M * N : ℕ) : ℝ) := by
    rw [Nat.cast_mul]
    calc
      _ = X ^ primeExponent * X ^ pairExponent := by
        rw [← Real.rpow_add hXp]
        norm_num [primeExponent, pairExponent]
      _ ≤ (M : ℝ) * N := mul_le_mul hM hN (by positivity) (by positivity)
  have hAhigh : ((M * N : ℕ) : ℝ) ≤ X ^ (1 - ell - 1 / 10000) := by
    convert hA using 1; norm_num [ell]
  obtain ⟨hlo, hlopos, hhi, hcap⟩ := hcover.2 ((M * N : ℕ) : ℝ) hAlow hAhigh
  have hflat : X ^ eta * (X ^ upperExponent) ^ (2 / 7 : ℝ) ≤
      (lowerCutoff X (M * N : ℕ) : ℝ) := by
    apply le_trans _ hlo
    rw [← Real.rpow_mul hXp.le, ← Real.rpow_add hXp]
    exact Real.rpow_le_rpow_of_exponent_le hX (by norm_num [eta, upperExponent, ell])
  have hUM : X ^ upperExponent ≤ (M : ℝ) ^ 4 := by
    calc
      _ ≤ (X ^ primeExponent) ^ (4 : ℕ) := by
        rw [← Real.rpow_mul_natCast hXp.le]
        exact Real.rpow_le_rpow_of_exponent_le hX
          (by norm_num [upperExponent, primeExponent])
      _ ≤ (M : ℝ) ^ 4 := pow_le_pow_left₀ (by positivity) hM 4
  have hUN : X ^ upperExponent ≤ (N : ℝ) ^ 2 := by
    calc
      _ ≤ (X ^ pairExponent) ^ (2 : ℕ) := by
        rw [← Real.rpow_mul_natCast hXp.le]
        exact Real.rpow_le_rpow_of_exponent_le hX
          (by norm_num [upperExponent, pairExponent])
      _ ≤ (N : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) hN 2
  have hHU : 2 * X ^ rho ≤ X ^ upperExponent := by
    calc
      _ ≤ X ^ (upperExponent - rho) * X ^ rho :=
        mul_le_mul_of_nonneg_right htwo.2 (by positivity)
      _ = _ := by rw [← Real.rpow_add hXp]; congr 1; ring
  have hUX : X ^ upperExponent ≤ X := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hX (by norm_num [upperExponent] : upperExponent ≤ 1)
  have hHK : X ^ rho ≤ (lowerCutoff X (M * N : ℕ) : ℝ) ^ (1 / 4 : ℝ) := by
    calc
      _ ≤ X ^ (ell * (1 / 4)) :=
        Real.rpow_le_rpow_of_exponent_le hX (by norm_num [rho, ell])
      _ = (X ^ ell) ^ (1 / 4 : ℝ) := Real.rpow_mul hXp.le _ _
      _ ≤ _ := Real.rpow_le_rpow (by positivity) hlo (by norm_num)
  have htail : X ^ (1 - theta + kappa) ≤ X ^ upperExponent :=
    Real.rpow_le_rpow_of_exponent_le hX (by norm_num [theta, kappa, upperExponent])
  exact ⟨hMnat, hNnat, hMX, hNX, hAone, hAX, hlo, hlopos, hhi, hcap,
    hflat, hUM, hUN, hHU, hUX, hHK, htail⟩

theorem eventually_half_width :
    ∀ᶠ X : ℝ in atTop,
      X ^ theta ≤ X ^ (101 / 1000 : ℝ) / 2 ∧ X ^ (101 / 1000 : ℝ) / 2 ≤ X / 2 := by
  filter_upwards [PolynomialLogEnvelope.eventually_constant_bound 2
      ((101 / 1000 : ℝ) - theta) (by norm_num) (by norm_num [theta])]
    with X hh
  have hXp : 0 < X := by linarith [hh.1]
  have hlow : 2 * X ^ theta ≤ X ^ (101 / 1000 : ℝ) := by
    calc
      _ ≤ X ^ ((101 / 1000 : ℝ) - theta) * X ^ theta :=
        mul_le_mul_of_nonneg_right hh.2 (by positivity)
      _ = _ := by rw [← Real.rpow_add hXp]; congr 1; ring
  have hu : X ^ (101 / 1000 : ℝ) ≤ X := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hh.1 (by norm_num : (101 / 1000 : ℝ) ≤ 1)
  constructor <;> linarith

run_cmd do
  for decl in [``theta_gt, ``ell_pos, ``eta_pos, ``rho_pos, ``rho_lt_one,
      ``kappa_pos, ``eta_eq_rho, ``eventually_scales, ``eventually_half_width] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"

end TripleFlatParameters
