import ShortPairProfileMeanWork
import TripleFirstMean
import PositiveSharpPowerWindow

/-! Regularity and absolute first means of literal short-pair profiles. No mean
estimate or integrability condition is assumed for the actual profile. -/
set_option autoImplicit false
set_option maxHeartbeats 9000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators

namespace ShortPairProfileFirstMeanWork
open LongerTupleActualProfiles LongerTupleCollection ShortPairProfilesWork
open ShortPairProfileMeanWork UpperAfter545Remaining PositiveSharpPowerWindow

def divisorSupport (X s : ℝ) (P : Finset ℕ) (z : ℝ → ℝ)
    (second : Bool) (js : List ℕ) : Finset ℕ :=
  support (pairSource X s P z second js) LongerTupleEncoding.index

def divisorCoefficient (X s : ℝ) (P : Finset ℕ) (z : ℝ → ℝ)
    (second : Bool) (js : List ℕ) (m : ℕ) : ℝ :=
  (coefficient (pairSource X s P z second js) LongerTupleEncoding.index
    (originalWeight X s true) m).re

theorem profile_eq_remainder (X s : ℝ) (P : Finset ℕ) (z : ℝ → ℝ)
    (second : Bool) (js : List ℕ) (L R : ℝ) :
    pairKernel X s P z second js (floorKernel L R) =
      HarmanDivisorWindow.remainder (divisorSupport X s P z second js)
        (divisorCoefficient X s P z second js) L R := by
  have hh := congrArg Complex.re
    ((pairKernel_eq_source X s P z second js (floorKernel L R)).trans
      (grouped_sum (pairSource X s P z second js) LongerTupleEncoding.index
        (originalWeight X s true) (fun m => (floorKernel L R m : ℂ))).symm)
  rw [HarmanDivisorWindow.remainder_eq_sum]
  simpa only [divisorSupport, divisorCoefficient, floorKernel, Complex.ofReal_re,
    Complex.re_sum, Complex.mul_re, Complex.ofReal_im, mul_zero, sub_zero] using hh

theorem eventually_pair_absolute_power (s : ℝ) (hs : 0 < s) (hs1 : s ≤ 1/1000)
    :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℝ in atTop, 1 < X ∧ 1000 ≤ Real.log X ∧
      ∀ (P : Finset ℕ) (z : ℝ → ℝ) (second : Bool) (js : List ℕ),
        js.length = 2 → BandGeometry X s P z →
        let Y : ℝ := halfWidth X (101/1000)
        (1/X)*(∫ x in Icc X (2*X),
          |pairKernel X s P z second js (floorKernel (x-x*(Y/X)) x)|) ≤ Y*X^(-c) := by
  obtain ⟨c,hc,hmean⟩ := eventually_pair_square s hs hs1
  refine ⟨c/2,by positivity,?_⟩
  filter_upwards [hmean, halfWidth_eventually (101/1000) (by norm_num)] with X hm hY
  refine ⟨hm.1,hm.2.1,?_⟩
  intro P z second js hlen hg
  dsimp only
  have hXp : 0 < X := by linarith [hm.1]
  let Y := halfWidth X (101/1000)
  have hYX : Y ≤ X := by have hh := hY.2; linarith
  have hsq : (1/X)*(∫ x in Icc X (2*X),
      pairKernel X s P z second js (floorKernel (x-x*(Y/X)) x)^2) ≤
      (Y*X^(-(c/2)))^2 := by
    have he : (Y*X^(-(c/2)))^2 = Y^2*X^(-c) := by
      rw [mul_pow, ←Real.rpow_mul_natCast hXp.le]
      congr 2
      norm_num
    rw [he]
    exact hm.2.2 P z second js hlen hg
  simp_rw [profile_eq_remainder] at hsq ⊢
  exact TripleFirstMean.remainder_absolute_mean_le _ _ X Y
    (Y*X^(-(c/2))) hXp hY.1.le hYX
    (mul_pos hY.1 (Real.rpow_pos_of_pos hXp _)) hsq

theorem eventually_pair_absolute_log (s : ℝ) (A : ℕ)
    (hs : 0 < s) (hs1 : s ≤ 1/1000) :
    ∀ᶠ X : ℝ in atTop, 1 < X ∧ 1000 ≤ Real.log X ∧
      ∀ (P : Finset ℕ) (z : ℝ → ℝ) (second : Bool) (js : List ℕ),
        js.length = 2 → BandGeometry X s P z →
        let Y : ℝ := halfWidth X (101/1000)
        (1/X)*(∫ x in Icc X (2*X),
          |pairKernel X s P z second js (floorKernel (x-x*(Y/X)) x)|) ≤
          Y/(Real.log X)^A := by
  obtain ⟨c,hc,hpower⟩ := eventually_pair_absolute_power s hs hs1
  filter_upwards [hpower, PolynomialLogEnvelope.eventually_bound 1 A c (by norm_num) hc,
    halfWidth_eventually (101/1000) (by norm_num)] with X hb he hY
  refine ⟨hb.1,hb.2.1,?_⟩
  intro P z second js hlen hg
  dsimp only
  have hXp : 0 < X := by linarith [hb.1]
  have hl : 0 < Real.log X := Real.log_pos hb.1
  have hlog : (Real.log X)^A ≤ X^c := by
    apply le_trans _ he.2
    simp only [one_mul]
    exact pow_le_pow_left₀ hl.le (by linarith) A
  have hunit : X^(-c)*(Real.log X)^A ≤ 1 := by
    calc
      _ ≤ X^(-c)*X^c := mul_le_mul_of_nonneg_left hlog (by positivity)
      _ = 1 := by rw [←Real.rpow_add hXp]; simp
  apply (hb.2.2 P z second js hlen hg).trans
  apply (le_div_iff₀ (pow_pos hl A)).mpr
  have hh := mul_le_mul_of_nonneg_left hunit hY.1.le
  nlinarith

#print axioms eventually_pair_absolute_log
run_cmd do
  for decl in [``profile_eq_remainder, ``eventually_pair_absolute_power,
      ``eventually_pair_absolute_log] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "LITERAL SHORT PAIR PROFILE EVERY FIXED LOG FIRST MEAN PASSED"

end ShortPairProfileFirstMeanWork
