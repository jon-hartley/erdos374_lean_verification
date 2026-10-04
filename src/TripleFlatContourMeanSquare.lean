import TripleFlatContour
import TripleFlatParameters
import FourfoldDivisorErrorBudget
import SignedDivisorPowerBudget

/-! A sharp floor-count estimate in the complete outer-triple scale region.
The remaining coefficient hypotheses are explicit energy and pointwise caps;
there is no analytic or prime-count premise. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators

namespace TripleFlatContourMeanSquare
open TripleFlatParameters FactoredDivisorWeights MellinCofactorCoverage HarmanDivisorWindow

def coefficientExponent : ℝ := FourfoldDivisorErrorBudget.coefficientExponent ell rho kappa

theorem coefficientExponent_pos : 0 < coefficientExponent :=
  FourfoldDivisorErrorBudget.coefficientExponent_pos ell rho kappa ell_pos rho_pos kappa_pos

theorem eventually_bound :
    ∃ c : ℝ, 0 < c ∧ ∃ ε : ℝ, 0 < ε ∧
      ∀ᶠ X : ℝ in atTop, Real.exp 1 ≤ X ∧
        ∀ (M N : ℕ) (sm sn : Finset ℕ) (am an : ℕ → ℝ) (Y : ℝ),
          X ^ primeExponent ≤ (M : ℝ) → X ^ pairExponent ≤ (N : ℝ) →
          ((M * N : ℕ) : ℝ) ≤ X ^ (26 / 35 : ℝ) →
          X ^ theta ≤ Y → Y ≤ X / 2 →
          (∀ n ∈ sm, M < n ∧ n ≤ 2 * M) →
          (∀ n ∈ sn, N < n ∧ n ≤ 2 * N) →
          (∑ n ∈ sm, (am n) ^ 2) ≤ X ^ ε * M →
          (∑ n ∈ sn, (an n) ^ 2) ≤ X ^ ε * N →
          (∀ d ∈ support sm sn, |coefficient sm sn am an d| ≤ X ^ coefficientExponent) →
          (1 / X) * (∫ x in Icc X (2 * X),
            remainder (support sm sn) (coefficient sm sn am an)
              (x - x * (Y / X)) x ^ 2) ≤ Y ^ 2 * X ^ (-c) := by
  obtain ⟨γ, hγ, ε, hε, hmiddle⟩ := TripleFlatContour.eventually_bound eta rho
    CofactorDoublingCoverage.blockCount eta_pos rho_pos rho_lt_one
  obtain ⟨c, hc, habsorb⟩ := SignedDivisorPowerBudget.six_power_absorption
    ((theta - 2 / 25) / 2) (ell / 4) (rho / 2) (1 / 2) γ kappa
    (by linarith [theta_gt]) (by have := ell_pos; positivity) (by have := rho_pos; positivity)
    (by norm_num) hγ kappa_pos
  refine ⟨c, hc, ε, hε, ?_⟩
  filter_upwards [TripleFlatParameters.eventually_scales,
    FourfoldDivisorErrorBudget.eventually_bound theta ell rho kappa
      theta_gt ell_pos rho_pos kappa_pos,
    hmiddle, habsorb, FourfoldSmoothingError.eventually_bound]
      with X hparameters hbudget hmid hab hsmooth
  refine ⟨hbudget.1, ?_⟩
  intro M N sm sn am an Y hMlow hNlow hAhigh hY hYX hsm hsn hem hen hweights
  have hp := hparameters.2 M N hMlow hNlow hAhigh
  have hXp : 0 < X := (Real.exp_pos 1).trans_le hbudget.1
  have hYpos : 0 ≤ Y := (Real.rpow_pos_of_pos hXp theta).le.trans hY
  have hYlt : Y < X := by linarith
  have hεs : X ^ (-19 / 20 : ℝ) ∈ Ioo 0 1 := by
    constructor <;> linarith [hsmooth.2.1.1, hsmooth.2.1.2]
  have hHpos : 0 < X ^ rho := Real.rpow_pos_of_pos hXp _
  have hHU : X ^ rho ≤ X ^ upperExponent := by linarith [hp.frequency_lower]
  have hmiddleBounds := hmid.2
    (lowerCutoff X (M * N : ℕ)) (upperCutoff X (M * N : ℕ))
    M N sm sn am an (X ^ upperExponent) Y (X ^ (-19 / 20 : ℝ))
    hp.cofactor_pos hp.cofactor_upper hp.cofactor_cover hp.flat_length
    hp.frequency_lower hp.frequency_upper hp.Mpos hp.Mupper hp.Mlength
    hp.Npos hp.Nupper hp.Nlength hYpos hYlt hεs
    (fun n hn => ⟨(hsm n hn).1.le, (hsm n hn).2⟩)
    (fun n hn => ⟨(hsn n hn).1.le, (hsn n hn).2⟩) hem hen
  have hcount := hbudget.2 ((M * N : ℕ) : ℝ) Y (X ^ rho) (X ^ upperExponent)
    (Y ^ 2 * X ^ (-γ)) (support sm sn) (coefficient sm sn am an)
    hp.Apos hp.Aupper (support_fourfold M N sm sn hp.Npos hsm hsn) hweights
    hp.cofactor_lower le_rfl hp.low_cofactor hHU hp.frequency_upper hp.tail_lower
    hY hYX hmiddleBounds.2 hmiddleBounds.1
  apply hcount.trans
  simpa only [neg_div, mul_assoc] using hab.2 Y

run_cmd do
  for decl in [``coefficientExponent_pos, ``eventually_bound] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"

end TripleFlatContourMeanSquare
