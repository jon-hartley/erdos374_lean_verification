import MellinCofactorCoverage

/-!
The same common cofactor endpoints cover divisors in (A,4A], as arise
from multiplying two strict dyadic supports. Seed transition margins,
floor coverage, and product support bounds preserve the full family.
The lower oscillatory phase retains three quarters of log 2.
-/

set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Filter Set
open scoped BigOperators

namespace FourfoldDivisorCoverage
open HarmanDivisorWindow MellinCofactorCoverage

def divisorCutoff (A : ℝ) : ℕ := ⌊4 * A⌋₊

theorem divisor_bounds (A : ℝ) (d : ℕ) (hA : 0 < A)
    (hd : A < (d : ℝ) ∧ (d : ℝ) ≤ 4 * A) :
    0 < d ∧ d ≤ divisorCutoff A := by
  constructor
  · exact_mod_cast hA.trans hd.1
  · exact (Nat.le_floor_iff (by positivity : 0 ≤ 4 * A)).mpr hd.2

/-- Real margins before choosing integer endpoints. -/
theorem real_endpoint_margins (X A d L R lower upper : ℝ)
    (hX : 0 < X) (hA : 0 < A)
    (hd : A < d ∧ d ≤ 4 * A)
    (hL : X / 2 ≤ L) (hR : R ≤ 2 * X)
    (hlower : 0 ≤ lower ∧ lower ≤ X / (16 * A))
    (hupper : 8 * X / A ≤ upper) :
    d * lower ≤ L / 2 ∧ 4 * R ≤ d * upper := by
  have hl := (le_div_iff₀ (by positivity : 0 < 16 * A)).mp hlower.2
  have hu := (div_le_iff₀ hA).mp hupper
  have hup : 0 ≤ upper := (by positivity : 0 ≤ 8 * X / A).trans hupper
  have hdl := mul_le_mul_of_nonneg_right hd.2 hlower.1
  have hdu := mul_le_mul_of_nonneg_right hd.1.le hup
  constructor <;> nlinarith

theorem endpoint_margins (X A x δ : ℝ) (d : ℕ)
    (hX : 0 < X) (hA : 0 < A)
    (hd : A < (d : ℝ) ∧ (d : ℝ) ≤ 4 * A)
    (hx : x ∈ Icc X (2 * X)) (hδ : δ ∈ Icc 0 (1 / 2)) :
    (d : ℝ) * lowerCutoff X A ≤ (x - x * δ) / 2 ∧
      4 * x ≤ (d : ℝ) * upperCutoff X A := by
  exact real_endpoint_margins X A d (x - x * δ) x
    (lowerCutoff X A) (upperCutoff X A) hX hA hd
    (DyadicDivisorWindow.window_bounds X x δ hX hx hδ).1 hx.2
    ⟨Nat.cast_nonneg _, Nat.floor_le (by positivity)⟩ (Nat.le_ceil _)

theorem transition_margins (X A x δ ε : ℝ) (d : ℕ)
    (hX : 0 < X) (hA : 0 < A)
    (hd : A < (d : ℝ) ∧ (d : ℝ) ≤ 4 * A)
    (hx : x ∈ Icc X (2 * X)) (hδ : δ ∈ Icc 0 (1 / 2))
    (hε : ε ∈ Ioo 0 (1 / 4)) :
    (d : ℝ) * lowerCutoff X A / x ≤ 1 - Real.log 2 * ε ∧
      (d : ℝ) * lowerCutoff X A / (x - x * δ) ≤
        1 - Real.log 2 * ε ∧
      1 + 2 * Real.log 2 * ε ≤ (d : ℝ) * upperCutoff X A / x ∧
      1 + 2 * Real.log 2 * ε ≤
        (d : ℝ) * upperCutoff X A / (x - x * δ) := by
  have hxp : 0 < x := hX.trans_le hx.1
  have hw := DyadicDivisorWindow.window_bounds X x δ hX hx hδ
  have hleft : 0 < x - x * δ := by linarith [hw.1]
  have hm := endpoint_margins X A x δ d hX hA hd hx hδ
  have hlog : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hlogε : Real.log 2 * ε ≤ ε :=
    by simpa using mul_le_mul_of_nonneg_right hlog hε.1.le
  have hhalf : (1 / 2 : ℝ) ≤ 1 - Real.log 2 * ε := by linarith [hε.2]
  have htwo : 1 + 2 * Real.log 2 * ε ≤ (2 : ℝ) := by nlinarith [hε.2]
  have hloX : (d : ℝ) * lowerCutoff X A / x ≤ 1 / 2 := by
    apply (div_le_iff₀ hxp).mpr
    linarith [hm.1, hw.2]
  have hloLeft : (d : ℝ) * lowerCutoff X A / (x - x * δ) ≤ 1 / 2 := by
    apply (div_le_iff₀ hleft).mpr
    linarith [hm.1]
  have hhiX : (2 : ℝ) ≤ (d : ℝ) * upperCutoff X A / x := by
    apply (le_div_iff₀ hxp).mpr
    linarith [hm.2]
  have hhiLeft : (2 : ℝ) ≤
      (d : ℝ) * upperCutoff X A / (x - x * δ) := by
    apply (le_div_iff₀ hleft).mpr
    linarith [hm.2, hw.2]
  exact ⟨hloX.trans hhalf, hloLeft.trans hhalf,
    htwo.trans hhiX, htwo.trans hhiLeft⟩

theorem floor_coverage (X A x δ : ℝ) (d : ℕ)
    (hX : 0 < X) (hA : 0 < A)
    (hd : A < (d : ℝ) ∧ (d : ℝ) ≤ 4 * A)
    (hx : x ∈ Icc X (2 * X)) (hδ : δ ∈ Icc 0 (1 / 2)) :
    lowerCutoff X A ≤ ⌊(x - x * δ) / d⌋₊ ∧
      ⌊x / d⌋₊ ≤ upperCutoff X A := by
  have hdp : (0 : ℝ) < d := hA.trans hd.1
  have hw := DyadicDivisorWindow.window_bounds X x δ hX hx hδ
  have hleft : 0 ≤ x - x * δ := by linarith [hw.1]
  have hxp : 0 < x := hX.trans_le hx.1
  have hh := endpoint_margins X A x δ d hX hA hd hx hδ
  constructor
  · apply (Nat.le_floor_iff (by positivity : 0 ≤ (x - x * δ) / d)).mpr
    apply (le_div_iff₀ hdp).mpr
    nlinarith [hh.1]
  · have hxd : x / d ≤ (upperCutoff X A : ℝ) := by
      apply (div_le_iff₀ hdp).mpr
      nlinarith [hh.2, hx.1]
    exact_mod_cast (Nat.floor_le (by positivity : 0 ≤ x / d)).trans hxd

theorem product_budget (X A : ℝ) (hX : 0 ≤ X) (hA : 0 < A) (hAX : A ≤ X) :
    ((divisorCutoff A * upperCutoff X A : ℕ) : ℝ) ≤ 36 * X := by
  have hD : (divisorCutoff A : ℝ) ≤ 4 * A := Nat.floor_le (by positivity)
  have hU : (upperCutoff X A : ℝ) ≤ 8 * X / A + 1 :=
    (Nat.ceil_lt_add_one (by positivity : 0 ≤ 8 * X / A)).le
  have hupper := (le_div_iff₀ hA).mp
    (by linarith : (upperCutoff X A : ℝ) - 1 ≤ 8 * X / A)
  have hmul := mul_le_mul_of_nonneg_right hD (Nat.cast_nonneg (upperCutoff X A))
  rw [Nat.cast_mul]
  nlinarith

theorem product_support_bounds (X A : ℝ) (s : Finset ℕ)
    (hX : 0 ≤ X) (hA : 0 < A) (hAX : A ≤ X)
    (hs : ∀ d ∈ s, A < (d : ℝ) ∧ (d : ℝ) ≤ 4 * A)
    (n : ℕ) (hn : n ∈ productSupport s (cofactors X A)) :
    0 < n ∧ (n : ℝ) ≤ 36 * X := by
  have hd := fun d hd => divisor_bounds A d hA (hs d hd)
  have hp : 0 < n := productSupport_positive s (cofactors X A)
    (fun d hd' => (hd d hd').1)
    (fun k hk => by have hh := (Finset.mem_Ioc.mp hk).1; omega) n hn
  have hn' := productSupport_le s (cofactors X A) (divisorCutoff A)
    (upperCutoff X A) (fun d hd' => (hd d hd').2)
    (fun k hk => (Finset.mem_Ioc.mp hk).2) n hn
  exact ⟨hp, (by exact_mod_cast hn' : (n : ℝ) ≤
    (divisorCutoff A * upperCutoff X A : ℕ)).trans (product_budget X A hX hA hAX)⟩

theorem product_support_lower (X A : ℝ) (s : Finset ℕ)
    (hX : 0 < X) (hA : 0 < A)
    (hs : ∀ d ∈ s, A < (d : ℝ))
    (n : ℕ) (hn : n ∈ productSupport s (cofactors X A)) :
    X / 16 < (n : ℝ) := by
  obtain ⟨⟨d, k⟩, hp, rfl⟩ := Finset.mem_image.mp hn
  obtain ⟨hd, hk⟩ := Finset.mem_product.mp hp
  have hkfloor := (Finset.mem_Ioc.mp hk).1
  have hkR : X / (16 * A) < (k : ℝ) :=
    (Nat.floor_lt (by positivity : 0 ≤ X / (16 * A))).mp hkfloor
  have hkp : (0 : ℝ) < k := (by positivity : 0 < X / (16 * A)).trans hkR
  have hprod := (div_lt_iff₀ (by positivity : 0 < 16 * A)).mp hkR
  have hdk := mul_lt_mul_of_pos_right (hs d hd) hkp
  change X / 16 < ((d * k : ℕ) : ℝ)
  rw [Nat.cast_mul]
  nlinarith

theorem count_identity (X A x δ : ℝ) (s : Finset ℕ) (weight : ℕ → ℝ)
    (hX : 0 < X) (hA : 0 < A)
    (hs : ∀ d ∈ s, A < (d : ℝ) ∧ (d : ℝ) ≤ 4 * A)
    (hx : x ∈ Icc X (2 * X)) (hδ : δ ∈ Icc 0 (1 / 2)) :
    divisorCount s weight (x - x * δ) x =
      SmoothedCountBoundary.sharp (productSupport s (cofactors X A))
        (coefficient s (cofactors X A) weight) x -
      SmoothedCountBoundary.sharp (productSupport s (cofactors X A))
        (coefficient s (cofactors X A) weight) (x - x * δ) := by
  have hw := DyadicDivisorWindow.window_bounds X x δ hX hx hδ
  have hf := fun d hd => floor_coverage X A x δ d hX hA (hs d hd) hx hδ
  exact divisorCount_eq_sharp s weight (lowerCutoff X A) (upperCutoff X A)
    (x - x * δ) x (fun d hd => (divisor_bounds A d hA (hs d hd)).1)
    (by linarith) hw.2 (fun d hd => (hf d hd).1) (fun d hd => (hf d hd).2)

theorem smoothed_phase_bounds (X A x δ v ε y : ℝ) (d : ℕ)
    (hX : 0 < X) (hA : 0 < A)
    (hd : A < (d : ℝ) ∧ (d : ℝ) ≤ 4 * A)
    (hx : x ∈ Icc X (2 * X)) (hδ : δ ∈ Icc 0 (1 / 2))
    (hv : v ∈ Icc (1 / 2) 2) (hε : ε ∈ Icc 0 (1 / 4))
    (hy : y ∈ Icc (x - x * δ) x)
    (hlo : 1 ≤ lowerCutoff X A) (hhi : 1 ≤ upperCutoff X A) :
    (3 / 4 : ℝ) * Real.log 2 ≤
        Real.log (y * v ^ ε / ((d : ℝ) * lowerCutoff X A)) ∧
      Real.log 2 ≤ -Real.log (y * v ^ ε / ((d : ℝ) * upperCutoff X A)) := by
  have hw := DyadicDivisorWindow.window_bounds X x δ hX hx hδ
  have hyp : 0 < y := by linarith [hw.1, hy.1]
  have hvp : 0 < v := by linarith [hv.1]
  have hq : 0 < v ^ ε := Real.rpow_pos_of_pos hvp _
  have hdp : (0 : ℝ) < d := hA.trans hd.1
  have hlop : (0 : ℝ) < lowerCutoff X A := by exact_mod_cast (by omega : 0 < lowerCutoff X A)
  have hhip : (0 : ℝ) < upperCutoff X A := by exact_mod_cast (by omega : 0 < upperCutoff X A)
  have hm := endpoint_margins X A x δ d hX hA hd hx hδ
  have hbase : Real.log 2 ≤ Real.log (y / ((d : ℝ) * lowerCutoff X A)) := by
    apply Real.log_le_log (by norm_num)
    apply (le_div_iff₀ (mul_pos hdp hlop)).mpr
    linarith [hm.1, hy.1]
  have hlogv : -Real.log 2 ≤ Real.log v := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 2) hv.1
    simpa only [one_div, Real.log_inv] using hh
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hmul := mul_le_mul_of_nonneg_left hlogv hε.1
  have hquarter := mul_le_mul_of_nonneg_right hε.2 hlog2
  have hrewrite : Real.log (y * v ^ ε / ((d : ℝ) * lowerCutoff X A)) =
      Real.log (y / ((d : ℝ) * lowerCutoff X A)) + ε * Real.log v := by
    rw [Real.log_div (mul_pos hyp hq).ne' (mul_pos hdp hlop).ne',
      Real.log_mul hyp.ne' hq.ne', Real.log_rpow hvp,
      Real.log_div hyp.ne' (mul_pos hdp hlop).ne']
    ring
  constructor
  · rw [hrewrite]
    nlinarith
  · have hqhigh : v ^ ε ≤ 2 :=
      (smoothing_range v ε hv ⟨hε.1, by linarith [hε.2]⟩).2
    have hprod := mul_le_mul_of_nonneg_left hqhigh hyp.le
    have hratio : (2 : ℝ) ≤ (d : ℝ) * upperCutoff X A / (y * v ^ ε) := by
      apply (le_div_iff₀ (mul_pos hyp hq)).mpr
      nlinarith [hm.2, hy.2]
    have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hratio
    rw [Real.log_div (mul_pos hdp hhip).ne' (mul_pos hyp hq).ne'] at hlog
    rw [Real.log_div (mul_pos hyp hq).ne' (mul_pos hdp hhip).ne']
    linarith

end FourfoldDivisorCoverage

#print axioms FourfoldDivisorCoverage.smoothed_phase_bounds
run_cmd do
  for target in [``FourfoldDivisorCoverage.divisor_bounds,
      ``FourfoldDivisorCoverage.real_endpoint_margins,
      ``FourfoldDivisorCoverage.endpoint_margins,
      ``FourfoldDivisorCoverage.transition_margins,
      ``FourfoldDivisorCoverage.floor_coverage,
      ``FourfoldDivisorCoverage.product_budget,
      ``FourfoldDivisorCoverage.product_support_bounds,
      ``FourfoldDivisorCoverage.product_support_lower,
      ``FourfoldDivisorCoverage.count_identity,
      ``FourfoldDivisorCoverage.smoothed_phase_bounds] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "FOURFOLD DIVISOR COVERAGE PASSED"
