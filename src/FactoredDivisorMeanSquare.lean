import FourfoldDivisorErrorBudget
import FactoredCofactorTailWindow
import SignedDivisorPowerBudget
import StrictDyadicEnergy

/-!
A squared-mean remainder estimate for actual signed divisor counts with
two bounded factor weights. All analytic estimates are supplied by the
imported proofs. The length and frequency inequalities remain explicit.
-/

set_option autoImplicit false
set_option maxHeartbeats 7000000
noncomputable section
open Filter MeasureTheory Set

namespace FactoredDivisorMeanSquare
open FactoredDivisorWeights MellinCofactorCoverage HarmanDivisorWindow

theorem eventually_bound (θ ell nu e ρ η κ : ℝ) (k : ℕ)
    (hθ : 2 / 25 < θ) (hell : 0 < ell) (hnu : 0 < nu) (he : 0 < e)
    (hρ : 0 < ρ) (hρell : ρ ≤ ell) (hρone : ρ < 1)
    (hη : 0 < η) (hηρ : η ≤ ρ) (hκ : 0 < κ) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℝ in atTop, Real.exp 1 ≤ X ∧
      ∀ (M N : ℕ) (sm sn : Finset ℕ) (am an : ℕ → ℝ) (Y H U : ℝ),
        let A : ℝ := (M * N : ℕ)
        let lo := lowerCutoff X A
        let hi := upperCutoff X A
        1 ≤ M → 1 ≤ N → A ≤ X →
        X ^ ell ≤ (lo : ℝ) → hi ≤ 2 ^ k * lo →
        ((2 ^ k * lo : ℕ) : ℝ) ≤ X → X ^ nu ≤ (N : ℝ) →
        X ^ (e / 10) * U ^ (10 / 9 : ℝ) ≤ (lo * M * N : ℕ) →
        X ^ e * U ^ (6 / 7 : ℝ) ≤ max (lo * M : ℕ) (M * N : ℕ) →
        X ^ η ≤ H → H ≤ (lo : ℝ) ^ (1 / 4 : ℝ) → H ≤ U →
        2 * X ^ ρ ≤ U → U ≤ X → X ^ (1 - θ + κ) ≤ U →
        X ^ θ ≤ Y → Y ≤ X / 2 →
        (∀ n ∈ sm, M < n ∧ n ≤ 2 * M) →
        (∀ n ∈ sn, N < n ∧ n ≤ 2 * N) →
        (∀ n ∈ sm, |am n| ≤ 1) → (∀ n ∈ sn, |an n| ≤ 1) →
        (1 / X) * (∫ x in Icc X (2 * X),
          remainder (support sm sn) (coefficient sm sn am an)
            (x - x * (Y / X)) x ^ 2) ≤ Y ^ 2 * X ^ (-c) := by
  obtain ⟨γ, hγ, ε, hε, hmiddle⟩ := FactoredCofactorTailWindow.eventually_common_bound
    ell nu e ρ η k hell hnu he hρ hρell hρone hη hηρ
  obtain ⟨c, hc, habsorb⟩ := SignedDivisorPowerBudget.six_power_absorption
    ((θ - 2 / 25) / 2) (ell / 4) (η / 2) (1 / 2) γ κ
    (by linarith) (by positivity) (by positivity) (by norm_num) hγ hκ
  have hβ := FourfoldDivisorErrorBudget.coefficientExponent_pos ell η κ hell hη hκ
  refine ⟨c, hc, ?_⟩
  filter_upwards [FourfoldDivisorErrorBudget.eventually_bound θ ell η κ hθ hell hη hκ,
    hmiddle, habsorb,
    eventual_support_cap (FourfoldDivisorErrorBudget.coefficientExponent ell η κ) hβ,
    FourfoldSmoothingError.eventually_bound, eventually_ge_atTop (4 : ℝ)]
      with X hbudget hmid hab hcap hsmooth hXfour
  refine ⟨hbudget.1, ?_⟩
  intro M N sm sn am an Y H U
  dsimp only
  intro hM hN hAX hlo hhi hscale hNlow hproduct hpair hH hHK hHU hUlow hUX
    hUhigh hY hYX hsm hsn ham han
  let A : ℝ := (M * N : ℕ)
  have hXp : 0 < X := by linarith
  have hXone : 1 ≤ X := by linarith
  have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hAone : 1 ≤ A := by dsimp [A]; push_cast; nlinarith
  have hMX : (M : ℝ) ≤ X := by
    have hAX' : (M : ℝ) * N ≤ X := by simpa only [Nat.cast_mul] using hAX
    nlinarith
  have hNX : (N : ℝ) ≤ X := by
    have hAX' : (M : ℝ) * N ≤ X := by simpa only [Nat.cast_mul] using hAX
    nlinarith
  have hYpos : 0 ≤ Y := (Real.rpow_pos_of_pos hXp θ).le.trans hY
  have hYlt : Y < X := by linarith
  have hεs : X ^ (-19 / 20 : ℝ) ∈ Ioo 0 1 := by
    constructor <;> linarith [hsmooth.2.1.1, hsmooth.2.1.2]
  have henergyM : (∑ n ∈ sm, am n ^ 2) ≤ X ^ ε * M := by
    apply (StrictDyadicEnergy.bounded_real_energy M sm am hsm ham).trans
    have hone := Real.one_le_rpow hXone hε.le
    nlinarith
  have henergyN : (∑ n ∈ sn, an n ^ 2) ≤ X ^ ε * N := by
    apply (StrictDyadicEnergy.bounded_real_energy N sn an hsn han).trans
    have hone := Real.one_le_rpow hXone hε.le
    nlinarith
  have hmiddleBounds := hmid.2 M N sm sn am an H U Y (X ^ (-19 / 20 : ℝ))
    hlo hscale hhi hM hMX hN hNX hNlow hproduct hpair hH hHU hUlow hUX
    hYpos hYlt hεs hsm hsn henergyM henergyN
  have hproductCap : ((4 * M * N : ℕ) : ℝ) ≤ X ^ (2 : ℕ) := by
    have hh : (M : ℝ) * N ≤ X := by simpa only [Nat.cast_mul] using hAX
    push_cast
    nlinarith
  have hweights := hcap.2 M N sm sn am an hN hproductCap hsm hsn ham han
  have hcount := hbudget.2 A Y H U (Y ^ 2 * X ^ (-γ))
    (support sm sn) (coefficient sm sn am an) hAone hAX
    (support_fourfold M N sm sn hN hsm hsn) hweights
    hlo hH hHK hHU hUX hUhigh hY hYX hmiddleBounds.2 hmiddleBounds.1
  apply hcount.trans
  simpa only [neg_div, mul_assoc] using hab.2 Y

end FactoredDivisorMeanSquare

#print axioms FactoredDivisorMeanSquare.eventually_bound
run_cmd do
  let axioms ← Lean.collectAxioms ``FactoredDivisorMeanSquare.eventually_bound
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"
  Lean.logInfo "FACTORED DIVISOR MEAN SQUARE PASSED"
