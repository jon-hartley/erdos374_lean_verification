import FourfoldDivisorCoverage
import NormalizedSupportMeanSquare
import FrequencyTailBudget
import HarmanDivisorContour

/-!
The full grouped divisor polynomial above a high frequency cutoff.
Every factorization contributes to its signed coefficient. All energy
premises are derived from an explicit bound on the original weights.
-/

set_option autoImplicit false
set_option maxHeartbeats 7000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators

namespace FourfoldDivisorUpperTail
open HarmanDivisorWindow Erdos374.HarmanGram152 SmoothedWindowTransfer

def lowerSupport (X : ℝ) : ℕ := ⌊X / 16⌋₊
def upperSupport (X : ℝ) : ℕ := ⌈36 * X⌉₊
def support (X A : ℝ) (s : Finset ℕ) : Finset ℕ :=
  productSupport s (MellinCofactorCoverage.cofactors X A)
def coefficients (X A : ℝ) (s : Finset ℕ) (weight : ℕ → ℝ) (n : ℕ) : ℂ :=
  (coefficient s (MellinCofactorCoverage.cofactors X A) weight n : ℂ)
def polynomial (X A : ℝ) (s : Finset ℕ) (weight : ℕ → ℝ) (σ t : ℝ) : ℂ :=
  verticalDirichlet152 (support X A s) (coefficients X A s weight) σ t

theorem polynomial_eq (X A : ℝ) (s : Finset ℕ) (weight : ℕ → ℝ) (σ t : ℝ) :
    polynomial X A s weight σ t =
      verticalDirichlet152 s (fun d => (weight d : ℂ)) σ t *
        verticalDirichlet152 (MellinCofactorCoverage.cofactors X A) (fun _ => 1) σ t :=
  vertical_product_support s (MellinCofactorCoverage.cofactors X A) weight σ t

theorem support_bounds (X A : ℝ) (s : Finset ℕ)
    (hX : 0 < X) (hA : 0 < A) (hAX : A ≤ X)
    (hs : ∀ d ∈ s, A < (d : ℝ) ∧ (d : ℝ) ≤ 4 * A)
    (n : ℕ) (hn : n ∈ support X A s) :
    X / 16 < (n : ℝ) ∧ (n : ℝ) ≤ 36 * X := by
  have hupper := (FourfoldDivisorCoverage.product_support_bounds X A s
    hX.le hA hAX hs n hn).2
  have hlower := FourfoldDivisorCoverage.product_support_lower X A s
    hX hA (fun d hd => (hs d hd).1) n hn
  exact ⟨hlower, hupper⟩

theorem support_endpoints (X A : ℝ) (s : Finset ℕ)
    (hX : 0 < X) (hA : 0 < A) (hAX : A ≤ X)
    (hs : ∀ d ∈ s, A < (d : ℝ) ∧ (d : ℝ) ≤ 4 * A)
    (n : ℕ) (hn : n ∈ support X A s) :
    0 < n ∧ lowerSupport X ≤ n ∧ n ≤ upperSupport X := by
  have hb := support_bounds X A s hX hA hAX hs n hn
  have hnpos : 0 < n := by exact_mod_cast (by linarith [hb.1] : (0 : ℝ) < n)
  have hlo : (lowerSupport X : ℝ) ≤ n :=
    (Nat.floor_le (by positivity : 0 ≤ X / 16)).trans hb.1.le
  have hhi : (n : ℝ) ≤ upperSupport X := hb.2.trans (Nat.le_ceil _)
  exact ⟨hnpos, by exact_mod_cast hlo, by exact_mod_cast hhi⟩

theorem endpoint_bounds (X : ℝ) (hX : 32 ≤ X) :
    1 ≤ lowerSupport X ∧ 1 ≤ upperSupport X ∧
      X / 32 ≤ (lowerSupport X : ℝ) ∧
      (upperSupport X : ℝ) ≤ 1184 * lowerSupport X := by
  have hf := Nat.lt_floor_add_one (X / 16)
  have hlow : X / 32 ≤ (lowerSupport X : ℝ) := by
    change X / 32 ≤ (⌊X / 16⌋₊ : ℝ)
    linarith
  have hlo : 1 ≤ lowerSupport X := by
    have hh : (1 : ℝ) ≤ lowerSupport X := by linarith
    exact_mod_cast hh
  have hU : (upperSupport X : ℝ) ≤ 37 * X := by
    have hh := Nat.ceil_lt_add_one (show 0 ≤ 36 * X by linarith)
    change (⌈36 * X⌉₊ : ℝ) ≤ 37 * X
    linarith
  have hhi : 1 ≤ upperSupport X := by
    have hh : 0 < upperSupport X := Nat.ceil_pos.mpr (by linarith)
    omega
  exact ⟨hlo, hhi, hlow, by linarith⟩

theorem support_card (X A : ℝ) (s : Finset ℕ)
    (hX : 0 < X) (hA : 0 < A) (hAX : A ≤ X)
    (hs : ∀ d ∈ s, A < (d : ℝ) ∧ (d : ℝ) ≤ 4 * A) :
    ((support X A s).card : ℝ) ≤ upperSupport X := by
  have hsub : support X A s ⊆ Finset.Icc 1 (upperSupport X) := by
    intro n hn
    have hh := support_endpoints X A s hX hA hAX hs n hn
    exact Finset.mem_Icc.mpr ⟨hh.1, hh.2.2⟩
  have hc := Finset.card_le_card hsub
  rw [Nat.card_Icc] at hc
  have hh : (support X A s).card ≤ upperSupport X := by omega
  exact_mod_cast hh

theorem eventual_parameters (η : ℝ) (hη : 0 < η) :
    ∀ᶠ X : ℝ in atTop, 36 ≤ X ∧
      1 ≤ lowerSupport X ∧ 1 ≤ upperSupport X ∧
      X ^ (1 - η) ≤ (lowerSupport X : ℝ) ∧
      (upperSupport X : ℝ) ≤ X ^ (1 + η) ∧
      (upperSupport X : ℝ) ≤ 1184 * lowerSupport X ∧
      1184 ≤ X ^ (η / 2) := by
  filter_upwards [PolynomialLogEnvelope.eventually_constant_bound 37 η
    (by norm_num) hη,
    PolynomialLogEnvelope.eventually_constant_bound 1184 (η / 2)
      (by norm_num) (by linarith),
    eventually_ge_atTop (36 : ℝ)] with X hpow h1184 hX
  have hXp : 0 < X := by linarith
  have hb := endpoint_bounds X (by linarith)
  refine ⟨hX, hb.1, hb.2.1, ?_, ?_, hb.2.2.2, h1184.2⟩
  · apply le_trans _ hb.2.2.1
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 32)).mpr
    calc
      X ^ (1 - η) * 32 ≤ X ^ (1 - η) * X ^ η :=
        mul_le_mul_of_nonneg_left (by linarith [hpow.2]) (by positivity)
      _ = X := by rw [← Real.rpow_add hXp]; norm_num
  · have hU : (upperSupport X : ℝ) ≤ 37 * X := by
      have hh := Nat.ceil_lt_add_one (show 0 ≤ 36 * X by linarith)
      change (⌈36 * X⌉₊ : ℝ) ≤ 37 * X
      linarith
    calc
      _ ≤ 37 * X := hU
      _ ≤ X ^ η * X := mul_le_mul_of_nonneg_right (by linarith [hpow.2]) hXp.le
      _ = X ^ (1 + η) := by
        calc
          _ = X ^ η * X ^ (1 : ℝ) := by rw [Real.rpow_one]
          _ = X ^ (1 + η) := by
            rw [← Real.rpow_add hXp]
            congr 1
            ring

theorem eventual_energy (η : ℝ) (hη : 0 < η) :
    ∀ᶠ X : ℝ in atTop, 36 ≤ X ∧
      ∀ (A : ℝ) (s : Finset ℕ) (weight : ℕ → ℝ),
        1 ≤ A → A ≤ X →
        (∀ d ∈ s, A < (d : ℝ) ∧ (d : ℝ) ≤ 4 * A) →
        (∀ d ∈ s, |weight d| ≤ X ^ (η / 32)) →
        (∑ n ∈ support X A s, ‖coefficients X A s weight n‖ ^ 2) ≤
          X ^ η * lowerSupport X := by
  filter_upwards [eventual_parameters η hη,
    ProductCoefficientCap.eventually_bound (η / 4) (by linarith)]
    with X hp hc
  refine ⟨hp.1, ?_⟩
  intro A s weight hA hAX hs hw
  have hXp : 0 < X := by linarith [hp.1]
  have hAp : 0 < A := by linarith
  have hcap : ∀ n ∈ support X A s, ‖coefficients X A s weight n‖ ≤ X ^ (η / 4) := by
    intro n hn
    have hb := support_bounds X A s hXp hAp hAX hs n hn
    have hnpos := (support_endpoints X A s hXp hAp hAX hs n hn).1
    have hgroup := hc.2 s (MellinCofactorCoverage.cofactors X A)
      (fun d => (weight d : ℂ)) (fun _ => 1) n hnpos (by nlinarith [hp.1])
      (by
        intro d hd
        simpa only [Complex.norm_real, Real.norm_eq_abs,
          show η / 4 / 8 = η / 32 by ring] using hw d hd)
      (by
        intro k hk
        simpa using Real.one_le_rpow hc.1 (by positivity : 0 ≤ η / 4 / 8))
    simpa only [coefficients, coefficient_cast] using hgroup
  have hsq : ∀ n ∈ support X A s,
      ‖coefficients X A s weight n‖ ^ 2 ≤ X ^ (η / 2) := by
    intro n hn
    have hh := pow_le_pow_left₀ (norm_nonneg _) (hcap n hn) 2
    rw [← Real.rpow_mul_natCast hXp.le] at hh
    simpa only [Nat.cast_ofNat, show η / 4 * 2 = η / 2 by ring] using hh
  calc
    _ ≤ ∑ _n ∈ support X A s, X ^ (η / 2) := Finset.sum_le_sum hsq
    _ = ((support X A s).card : ℝ) * X ^ (η / 2) := by simp
    _ ≤ (upperSupport X : ℝ) * X ^ (η / 2) :=
      mul_le_mul_of_nonneg_right (support_card X A s hXp hAp hAX hs) (by positivity)
    _ ≤ (1184 * (lowerSupport X : ℝ)) * X ^ (η / 2) :=
      mul_le_mul_of_nonneg_right hp.2.2.2.2.2.1 (by positivity)
    _ ≤ (X ^ (η / 2) * (lowerSupport X : ℝ)) * X ^ (η / 2) := by
      gcongr
      exact hp.2.2.2.2.2.2
    _ = X ^ η * lowerSupport X := by
      rw [mul_assoc, mul_comm (lowerSupport X : ℝ), ← mul_assoc, ← Real.rpow_add hXp]
      congr 2
      ring

theorem eventual_mean_square (η : ℝ) (hη : 0 < η) :
    ∀ᶠ X : ℝ in atTop, 36 ≤ X ∧
      ∀ (A : ℝ) (s : Finset ℕ) (weight : ℕ → ℝ) (a T σ : ℝ),
        1 ≤ A → A ≤ X →
        (∀ d ∈ s, A < (d : ℝ) ∧ (d : ℝ) ≤ 4 * A) →
        (∀ d ∈ s, |weight d| ≤ X ^ (η / 32)) →
        0 ≤ T → T ≤ X → 1 ≤ σ →
        (∫ t in Icc a (a + T), ‖polynomial X A s weight σ t‖ ^ 2) ≤
          X ^ (6 * η) := by
  filter_upwards [eventual_parameters η hη, eventual_energy η hη,
    NormalizedSupportMeanSquare.eventual_bound η hη] with X hp he hm
  refine ⟨hp.1, ?_⟩
  intro A s weight a T σ hA hAX hs hw hT hTX hσ
  have hXp : 0 < X := by linarith [hp.1]
  exact hm.2 (support X A s) (coefficients X A s weight)
    (lowerSupport X) (upperSupport X) a T σ hp.2.1 hp.2.2.1
    (fun n hn => (support_endpoints X A s hXp (by linarith) hAX hs n hn).2)
    hp.2.2.2.1 hp.2.2.2.2.1 hT hTX hσ (he.2 A s weight hA hAX hs hw)

theorem eventual_separated_tail (θ κ : ℝ) (hκ : 0 < κ) :
    ∀ᶠ X : ℝ in atTop, Real.exp 1 ≤ X ∧
      ∀ (A Y ε a b H : ℝ) (s : Finset ℕ) (weight : ℕ → ℝ),
        1 ≤ A → A ≤ X →
        (∀ d ∈ s, A < (d : ℝ) ∧ (d : ℝ) ≤ 4 * A) →
        (∀ d ∈ s, |weight d| ≤ X ^ (κ / 384)) →
        X ^ θ ≤ Y → Y < X → ε ∈ Ioo 0 1 →
        X ^ (1 - θ + κ) ≤ H → a ≤ b → b - a ≤ X →
        (∀ t ∈ Icc a b, H ≤ |t|) →
        (1 / X) * (∫ x in Icc X (2 * X),
          ‖HarmanDivisorContour.productTransform s weight
            (MellinCofactorCoverage.lowerCutoff X A)
            (MellinCofactorCoverage.upperCutoff X A)
            ε a b (1 + 1 / Real.log X) (Y / X) x‖ ^ 2) ≤
              Y ^ 2 * X ^ (-κ) := by
  filter_upwards [eventual_mean_square (κ / 12) (by linarith),
    FrequencyTailBudget.eventually_separated θ κ hκ] with X hm ht
  refine ⟨ht.1, ?_⟩
  intro A Y ε a b H s weight hA hAX hs hw hY hYX hε hH hab hlen hband
  have hXp : 0 < X := (Real.exp_pos 1).trans_le ht.1
  have hσ : 1 ≤ 1 + 1 / Real.log X := by
    have hh : 1 ≤ Real.log X := by
      simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) ht.1
    have hnonneg : 0 ≤ 1 / Real.log X := by positivity
    linarith
  have hcontinuous : Continuous (polynomial X A s weight (1 + 1 / Real.log X)) :=
    NormalizedMeanSquare.continuous_vertical _ _ _ (fun n hn =>
      (support_endpoints X A s hXp (by linarith) hAX hs n hn).1)
  have henergy := hm.2 A s weight a (b - a) (1 + 1 / Real.log X)
    hA hAX hs (by
      intro d hd
      simpa only [show κ / 12 / 32 = κ / 384 by ring] using hw d hd)
    (by linarith) hlen hσ
  have henergy' : (∫ t in Icc a b,
      ‖polynomial X A s weight (1 + 1 / Real.log X) t‖ ^ 2) ≤ X ^ (κ / 2) := by
    simpa only [show a + (b - a) = b by ring,
      show 6 * (κ / 12) = κ / 2 by ring] using henergy
  have htail := ht.2 Y ε a b H (polynomial X A s weight (1 + 1 / Real.log X))
    hY hYX hε hH hab hlen hband hcontinuous henergy'
  simpa only [HarmanDivisorContour.productTransform, transform, polynomial_eq,
    MellinCofactorCoverage.cofactors] using htail

theorem eventual_tail (θ κ : ℝ) (hκ : 0 < κ) :
    ∀ᶠ X : ℝ in atTop, Real.exp 1 ≤ X ∧
      ∀ (A Y ε H : ℝ) (s : Finset ℕ) (weight : ℕ → ℝ),
        1 ≤ A → A ≤ X →
        (∀ d ∈ s, A < (d : ℝ) ∧ (d : ℝ) ≤ 4 * A) →
        (∀ d ∈ s, |weight d| ≤ X ^ (κ / 384)) →
        X ^ θ ≤ Y → Y < X → ε ∈ Ioo 0 1 →
        X ^ (1 - θ + κ) ≤ H → H ≤ X →
        (1 / X) * (∫ x in Icc X (2 * X),
          ‖HarmanDivisorContour.productTransform s weight
            (MellinCofactorCoverage.lowerCutoff X A)
            (MellinCofactorCoverage.upperCutoff X A)
            ε H X (1 + 1 / Real.log X) (Y / X) x‖ ^ 2) ≤
              Y ^ 2 * X ^ (-κ) := by
  filter_upwards [eventual_separated_tail θ κ hκ] with X hh
  refine ⟨hh.1, ?_⟩
  intro A Y ε H s weight hA hAX hs hw hY hYX hε hH hHX
  have hXp : 0 < X := (Real.exp_pos 1).trans_le hh.1
  have hHp : 0 < H := (Real.rpow_pos_of_pos hXp _).trans_le hH
  exact hh.2 A Y ε H X H s weight hA hAX hs hw hY hYX hε hH hHX
    (by linarith) (fun t ht => ht.1.trans (le_abs_self t))

theorem eventual_negative_tail (θ κ : ℝ) (hκ : 0 < κ) :
    ∀ᶠ X : ℝ in atTop, Real.exp 1 ≤ X ∧
      ∀ (A Y ε H : ℝ) (s : Finset ℕ) (weight : ℕ → ℝ),
        1 ≤ A → A ≤ X →
        (∀ d ∈ s, A < (d : ℝ) ∧ (d : ℝ) ≤ 4 * A) →
        (∀ d ∈ s, |weight d| ≤ X ^ (κ / 384)) →
        X ^ θ ≤ Y → Y < X → ε ∈ Ioo 0 1 →
        X ^ (1 - θ + κ) ≤ H → H ≤ X →
        (1 / X) * (∫ x in Icc X (2 * X),
          ‖HarmanDivisorContour.productTransform s weight
            (MellinCofactorCoverage.lowerCutoff X A)
            (MellinCofactorCoverage.upperCutoff X A)
            ε (-X) (-H) (1 + 1 / Real.log X) (Y / X) x‖ ^ 2) ≤
              Y ^ 2 * X ^ (-κ) := by
  filter_upwards [eventual_separated_tail θ κ hκ] with X hh
  refine ⟨hh.1, ?_⟩
  intro A Y ε H s weight hA hAX hs hw hY hYX hε hH hHX
  have hXp : 0 < X := (Real.exp_pos 1).trans_le hh.1
  have hHp : 0 < H := (Real.rpow_pos_of_pos hXp _).trans_le hH
  apply hh.2 A Y ε (-X) (-H) H s weight hA hAX hs hw hY hYX hε hH
    (by linarith) (by linarith)
  intro t ht
  have hh := neg_le_abs t
  linarith [ht.2]

end FourfoldDivisorUpperTail

#print axioms FourfoldDivisorUpperTail.eventual_energy
#print axioms FourfoldDivisorUpperTail.eventual_tail
run_cmd do
  for target in [``FourfoldDivisorUpperTail.support_bounds,
      ``FourfoldDivisorUpperTail.eventual_parameters,
      ``FourfoldDivisorUpperTail.eventual_energy,
      ``FourfoldDivisorUpperTail.eventual_mean_square,
      ``FourfoldDivisorUpperTail.eventual_separated_tail,
      ``FourfoldDivisorUpperTail.eventual_negative_tail,
      ``FourfoldDivisorUpperTail.eventual_tail] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "FOURFOLD DIVISOR UPPER TAIL PASSED"
