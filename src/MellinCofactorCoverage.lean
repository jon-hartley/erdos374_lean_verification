import DyadicDivisorWindow

/-!
Common cofactor endpoints with fixed multiplicative margins around every
smoothed window endpoint. These are coverage premises for a continuous
Mellin calculation; no main-term approximation is asserted here.
-/

set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Filter Set
open scoped BigOperators

namespace MellinCofactorCoverage
open HarmanDivisorWindow

def lowerCutoff (X A : ℝ) : ℕ := ⌊X / (16 * A)⌋₊
def upperCutoff (X A : ℝ) : ℕ := ⌈8 * X / A⌉₊
def cofactors (X A : ℝ) : Finset ℕ :=
  Finset.Ioc (lowerCutoff X A) (upperCutoff X A)

theorem smoothing_range (v ε : ℝ)
    (hv : v ∈ Icc (1 / 2) 2) (hε : ε ∈ Icc 0 1) :
    v ^ ε ∈ Icc (1 / 2) 2 := by
  constructor
  · calc
      (1 / 2 : ℝ) = (1 / 2 : ℝ) ^ (1 : ℝ) := by simp
      _ ≤ (1 / 2 : ℝ) ^ ε :=
        Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) hε.2
      _ ≤ v ^ ε := Real.rpow_le_rpow (by norm_num) hv.1 hε.1
  · calc
      v ^ ε ≤ (2 : ℝ) ^ ε :=
        Real.rpow_le_rpow (by linarith [hv.1]) hv.2 hε.1
      _ ≤ (2 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hε.2
      _ = 2 := by simp

/-- A real-endpoint statement, before choosing any integer rounding. -/
theorem real_endpoint_margins (X A d L R q lower upper : ℝ)
    (hX : 0 < X) (hA : 0 < A)
    (hd : A < d ∧ d ≤ 2 * A)
    (hL : X / 2 ≤ L) (hR : R ≤ 2 * X)
    (hq : q ∈ Icc (1 / 2) 2)
    (hlower : 0 ≤ lower ∧ lower ≤ X / (16 * A))
    (hupper : 8 * X / A ≤ upper) :
    d * lower ≤ L * q / 2 ∧ 2 * R * q ≤ d * upper := by
  have hdp : 0 < d := hA.trans hd.1
  have hLp : 0 ≤ L := by linarith
  have hqp : 0 ≤ q := by linarith [hq.1]
  have hl := (le_div_iff₀ (by positivity : 0 < 16 * A)).mp hlower.2
  have hu := (div_le_iff₀ hA).mp hupper
  have hup : 0 ≤ upper := (by positivity : 0 ≤ 8 * X / A).trans hupper
  have hdl := mul_le_mul_of_nonneg_right hd.2 hlower.1
  have hLq := mul_le_mul_of_nonneg_left hq.1 hLp
  have hdu := mul_le_mul_of_nonneg_right hd.1.le hup
  have hRq := mul_le_mul_of_nonneg_right hR hqp
  have hXq := mul_le_mul_of_nonneg_left hq.2 hX.le
  constructor <;> nlinarith

theorem smoothed_real_margins (X A d x δ v ε lower upper : ℝ)
    (hX : 0 < X) (hA : 0 < A)
    (hd : A < d ∧ d ≤ 2 * A)
    (hx : x ∈ Icc X (2 * X)) (hδ : δ ∈ Icc 0 (1 / 2))
    (hv : v ∈ Icc (1 / 2) 2) (hε : ε ∈ Icc 0 1)
    (hlower : 0 ≤ lower ∧ lower ≤ X / (16 * A))
    (hupper : 8 * X / A ≤ upper) :
    d * lower ≤ (x - x * δ) * v ^ ε / 2 ∧
      2 * x * v ^ ε ≤ d * upper :=
  real_endpoint_margins X A d (x - x * δ) x (v ^ ε) lower upper
    hX hA hd (DyadicDivisorWindow.window_bounds X x δ hX hx hδ).1
    hx.2 (smoothing_range v ε hv hε) hlower hupper

theorem endpoint_margins (X A x δ v ε : ℝ) (d : ℕ)
    (hX : 0 < X) (hA : 0 < A)
    (hd : A < (d : ℝ) ∧ (d : ℝ) ≤ 2 * A)
    (hx : x ∈ Icc X (2 * X)) (hδ : δ ∈ Icc 0 (1 / 2))
    (hv : v ∈ Icc (1 / 2) 2) (hε : ε ∈ Icc 0 1) :
    (d : ℝ) * lowerCutoff X A ≤ (x - x * δ) * v ^ ε / 2 ∧
      2 * x * v ^ ε ≤ (d : ℝ) * upperCutoff X A := by
  exact smoothed_real_margins X A d x δ v ε (lowerCutoff X A)
    (upperCutoff X A) hX hA hd hx hδ hv hε
    ⟨Nat.cast_nonneg _, Nat.floor_le (by positivity)⟩ (Nat.le_ceil _)

theorem floor_coverage (X A x δ : ℝ) (d : ℕ)
    (hX : 0 < X) (hA : 0 < A)
    (hd : A < (d : ℝ) ∧ (d : ℝ) ≤ 2 * A)
    (hx : x ∈ Icc X (2 * X)) (hδ : δ ∈ Icc 0 (1 / 2)) :
    lowerCutoff X A ≤ ⌊(x - x * δ) / d⌋₊ ∧
      ⌊x / d⌋₊ ≤ upperCutoff X A := by
  have hdp : (0 : ℝ) < d := hA.trans hd.1
  have hw := DyadicDivisorWindow.window_bounds X x δ hX hx hδ
  have hleft : 0 ≤ x - x * δ := by linarith [hw.1]
  have hxp : 0 < x := hX.trans_le hx.1
  have hh := endpoint_margins X A x δ 1 0 d hX hA hd hx hδ
    (by constructor <;> norm_num) (by constructor <;> norm_num)
  simp only [Real.rpow_zero, mul_one] at hh
  constructor
  · apply (Nat.le_floor_iff (by positivity : 0 ≤ (x - x * δ) / d)).mpr
    apply (le_div_iff₀ hdp).mpr
    nlinarith [hh.1]
  · have hxd : x / d ≤ (upperCutoff X A : ℝ) := by
      apply (div_le_iff₀ hdp).mpr
      nlinarith [hh.2, hx.1]
    exact_mod_cast (Nat.floor_le (by positivity : 0 ≤ x / d)).trans hxd

theorem cutoff_strict (X A : ℝ) (hX : 0 < X) (hA : 0 < A) :
    lowerCutoff X A < upperCutoff X A := by
  have hl : (lowerCutoff X A : ℝ) ≤ X / (16 * A) :=
    Nat.floor_le (by positivity)
  have hu : 8 * X / A ≤ (upperCutoff X A : ℝ) := Nat.le_ceil _
  have hquot : X / (16 * A) < 8 * X / A := by
    apply (div_lt_div_iff₀ (by positivity : 0 < 16 * A) hA).mpr
    nlinarith [mul_pos hX hA]
  exact_mod_cast hl.trans_lt (hquot.trans_le hu)

theorem lowerCutoff_scale (X A : ℝ) (hA : 0 < A) (hscale : 32 * A ≤ X) :
    X / (32 * A) ≤ (lowerCutoff X A : ℝ) := by
  have hq : (2 : ℝ) ≤ X / (16 * A) :=
    (le_div_iff₀ (by positivity : 0 < 16 * A)).mpr (by nlinarith)
  have hf := Nat.lt_floor_add_one (X / (16 * A))
  have heq : X / (32 * A) = (X / (16 * A)) / 2 := by ring
  rw [heq]
  change (X / (16 * A)) / 2 ≤ (⌊X / (16 * A)⌋₊ : ℝ)
  linarith

theorem product_budget (X A : ℝ) (hX : 0 ≤ X) (hA : 0 < A) (hAX : A ≤ X) :
    ((DyadicDivisorWindow.divisorCutoff A * upperCutoff X A : ℕ) : ℝ) ≤ 18 * X := by
  have hD : (DyadicDivisorWindow.divisorCutoff A : ℝ) ≤ 2 * A :=
    Nat.floor_le (by positivity)
  have hU : (upperCutoff X A : ℝ) ≤ 8 * X / A + 1 :=
    (Nat.ceil_lt_add_one (by positivity : 0 ≤ 8 * X / A)).le
  have hupper := (le_div_iff₀ hA).mp (by linarith : (upperCutoff X A : ℝ) - 1 ≤ 8 * X / A)
  have hmul := mul_le_mul_of_nonneg_right hD (Nat.cast_nonneg (upperCutoff X A))
  rw [Nat.cast_mul]
  nlinarith

theorem product_support_bounds (X A : ℝ) (s : Finset ℕ)
    (hX : 0 ≤ X) (hA : 0 < A) (hAX : A ≤ X)
    (hs : ∀ d ∈ s, A < (d : ℝ) ∧ (d : ℝ) ≤ 2 * A)
    (n : ℕ) (hn : n ∈ productSupport s (cofactors X A)) :
    0 < n ∧ (n : ℝ) ≤ 18 * X := by
  have hd := fun d hd => DyadicDivisorWindow.divisor_bounds A d hA (hs d hd)
  have hp : 0 < n := productSupport_positive s (cofactors X A)
    (fun d hd' => (hd d hd').1)
    (fun k hk => by have hh := (Finset.mem_Ioc.mp hk).1; omega) n hn
  have hn' := productSupport_le s (cofactors X A) (DyadicDivisorWindow.divisorCutoff A)
    (upperCutoff X A) (fun d hd' => (hd d hd').2)
    (fun k hk => (Finset.mem_Ioc.mp hk).2) n hn
  exact ⟨hp, (by exact_mod_cast hn' : (n : ℝ) ≤
    (DyadicDivisorWindow.divisorCutoff A * upperCutoff X A : ℕ)).trans
      (product_budget X A hX hA hAX)⟩

/-- Phase ratios are separated from one by a fixed logarithmic margin. -/
theorem log_phase_bounds (y q d lower upper : ℝ)
    (hy : 0 < y) (hq : 0 < q) (hd : 0 < d)
    (hlower : 0 < lower) (hupper : 0 < upper)
    (hl : d * lower ≤ y * q / 2) (hu : 2 * y * q ≤ d * upper) :
    Real.log 2 ≤ Real.log (y * q / (d * lower)) ∧
      Real.log 2 ≤ -Real.log (y * q / (d * upper)) := by
  constructor
  · apply Real.log_le_log (by norm_num)
    apply (le_div_iff₀ (mul_pos hd hlower)).mpr
    linarith
  · have hh : (2 : ℝ) ≤ d * upper / (y * q) :=
      (le_div_iff₀ (mul_pos hy hq)).mpr (by nlinarith [hu])
    have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hh
    rw [Real.log_div (mul_pos hd hupper).ne' (mul_pos hy hq).ne'] at hlog
    rw [Real.log_div (mul_pos hy hq).ne' (mul_pos hd hupper).ne']
    linarith

theorem smoothed_phase_bounds (X A x δ v ε y : ℝ) (d : ℕ)
    (hX : 0 < X) (hA : 0 < A)
    (hd : A < (d : ℝ) ∧ (d : ℝ) ≤ 2 * A)
    (hx : x ∈ Icc X (2 * X)) (hδ : δ ∈ Icc 0 (1 / 2))
    (hv : v ∈ Icc (1 / 2) 2) (hε : ε ∈ Icc 0 1)
    (hy : y ∈ Icc (x - x * δ) x)
    (hlo : 1 ≤ lowerCutoff X A) (hhi : 1 ≤ upperCutoff X A) :
    Real.log 2 ≤ Real.log (y * v ^ ε / ((d : ℝ) * lowerCutoff X A)) ∧
      Real.log 2 ≤ -Real.log (y * v ^ ε / ((d : ℝ) * upperCutoff X A)) := by
  have hw := DyadicDivisorWindow.window_bounds X x δ hX hx hδ
  have hyp : 0 < y := by linarith [hw.1, hy.1]
  have hq : 0 < v ^ ε := Real.rpow_pos_of_pos (by linarith [hv.1]) _
  have hm := endpoint_margins X A x δ v ε d hX hA hd hx hδ hv hε
  apply log_phase_bounds y (v ^ ε) d (lowerCutoff X A) (upperCutoff X A)
    hyp hq (hA.trans hd.1)
    (by exact_mod_cast (show 0 < lowerCutoff X A by omega))
    (by exact_mod_cast (show 0 < upperCutoff X A by omega))
  · have hmul := mul_le_mul_of_nonneg_right hy.1 hq.le
    linarith [hm.1]
  · have hmul := mul_le_mul_of_nonneg_right hy.2 hq.le
    nlinarith [hm.2]

theorem eventually_lower_scale (e : ℝ) (he : 0 < e) :
    ∀ᶠ X : ℝ in atTop, 18 ≤ X ∧
      ∀ A : ℝ, 1 ≤ A → A ≤ X ^ (1 - e) →
        X ^ (e / 2) ≤ (lowerCutoff X A : ℝ) ∧
        1 ≤ lowerCutoff X A ∧ 1 ≤ upperCutoff X A ∧
        ((DyadicDivisorWindow.divisorCutoff A * upperCutoff X A : ℕ) : ℝ) ≤ X ^ (2 : ℕ) := by
  filter_upwards [PolynomialLogEnvelope.eventually_constant_bound 32 (e / 2)
    (by norm_num) (by linarith), eventually_ge_atTop (18 : ℝ)] with X hh hX
  refine ⟨hX, ?_⟩
  intro A hA hAX
  have hXp : 0 < X := by linarith
  have hAp : 0 < A := by linarith
  have hXhalf : (0 : ℝ) ≤ X ^ (e / 2) := by positivity
  have hpow : X ^ (e / 2) * X ^ (e / 2) = X ^ e := by
    rw [← Real.rpow_add hXp]
    congr 1
    ring
  have h32 : (32 : ℝ) ≤ X ^ e := by nlinarith [hh.2]
  have hscale : 32 * A ≤ X := by
    calc
      32 * A ≤ 32 * X ^ (1 - e) := mul_le_mul_of_nonneg_left hAX (by norm_num)
      _ ≤ X ^ e * X ^ (1 - e) :=
        mul_le_mul_of_nonneg_right h32 (by positivity)
      _ = X := by rw [← Real.rpow_add hXp]; norm_num
  have hlower := lowerCutoff_scale X A hAp hscale
  have henergy : 32 * X ^ (e / 2) ≤ X ^ e := by nlinarith [hh.2]
  have hratio : X ^ (e / 2) ≤ X / (32 * A) := by
    apply (le_div_iff₀ (by positivity : 0 < 32 * A)).mpr
    calc
      X ^ (e / 2) * (32 * A) = (32 * X ^ (e / 2)) * A := by ring
      _ ≤ X ^ e * X ^ (1 - e) :=
        mul_le_mul henergy hAX (by positivity) (by positivity)
      _ = X := by rw [← Real.rpow_add hXp]; norm_num
  have hlo : 1 ≤ lowerCutoff X A := by
    have hreal : (1 : ℝ) ≤ lowerCutoff X A := by
      linarith [hratio.trans hlower, hh.2]
    exact_mod_cast hreal
  have hhi : 1 ≤ upperCutoff X A := by
    have hh' : 0 < upperCutoff X A := Nat.ceil_pos.mpr (by positivity)
    omega
  refine ⟨hratio.trans hlower, hlo, hhi, ?_⟩
  exact (product_budget X A hXp.le hAp (by linarith)).trans (by nlinarith)

end MellinCofactorCoverage

#print axioms MellinCofactorCoverage.endpoint_margins
#print axioms MellinCofactorCoverage.eventually_lower_scale
run_cmd do
  for target in [``MellinCofactorCoverage.real_endpoint_margins,
      ``MellinCofactorCoverage.endpoint_margins,
      ``MellinCofactorCoverage.floor_coverage,
      ``MellinCofactorCoverage.cutoff_strict,
      ``MellinCofactorCoverage.product_support_bounds,
      ``MellinCofactorCoverage.log_phase_bounds,
      ``MellinCofactorCoverage.smoothed_phase_bounds,
      ``MellinCofactorCoverage.eventually_lower_scale] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "MELLIN COFACTOR COVERAGE PASSED"
