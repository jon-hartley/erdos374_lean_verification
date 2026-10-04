import Mathlib.Tactic

/-!
Exact continuous-reference window geometry and rational error-budget algebra.
STATUS: NEW UNCOMPILED DRAFT. No Mellin/Plancherel or prime theorem is proved
by this file. Those analytic steps are in the accompanying candidate proof.
-/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open scoped BigOperators
namespace SourceWindowGeometry

def referenceLength (a b lo hi : ℝ) : ℝ := max 0 (min b hi-max a lo)

/-- The continuous reference window is wholly inside the literal third
source interval. The stronger upper bound 2L leaves room below 4L. -/
theorem reference_containment (P R L p r x δ : ℝ)
    (hP : 0 < P) (hR : 0 < R) (hL : 0 < L)
    (hp : P ≤ p ∧ p < 2*P) (hr : R ≤ r ∧ r < 2*R)
    (hx : P*R*L ≤ x ∧ x ≤ 2*(P*R*L))
    (hδ : 0 ≤ δ ∧ δ ≤ 1/2) :
    L/8 ≤ (1-δ)*x/(p*r) ∧ x/(p*r) ≤ 2*L := by
  have hpp : 0 < p := hP.trans_le hp.1
  have hrp : 0 < r := hR.trans_le hr.1
  have hpr : 0 < p*r := mul_pos hpp hrp
  have hPR : 0 < P*R := mul_pos hP hR
  have hxpos : 0 < x := (mul_pos hPR hL).trans_le hx.1
  have hlo : P*R ≤ p*r := mul_le_mul hp.1 hr.1 hR.le hpp.le
  have hhi : p*r ≤ 4*(P*R) := by
    have hh := mul_le_mul hp.2.le hr.2.le hrp.le (by positivity : 0 ≤ 2*P)
    nlinarith
  constructor
  · apply (le_div_iff₀ hpr).mpr
    have hh := mul_le_mul_of_nonneg_left hhi hL.le
    have hd := mul_le_mul_of_nonneg_right (show (1/2:ℝ) ≤ 1-δ by linarith) hxpos.le
    nlinarith [hx.1]
  · apply (div_le_iff₀ hpr).mpr
    have hh := mul_le_mul_of_nonneg_left hlo hL.le
    nlinarith [hx.2]

theorem reference_length_exact (P R L p r x δ : ℝ)
    (hP : 0 < P) (hR : 0 < R) (hL : 0 < L)
    (hp : P ≤ p ∧ p < 2*P) (hr : R ≤ r ∧ r < 2*R)
    (hx : P*R*L ≤ x ∧ x ≤ 2*(P*R*L))
    (hδ : 0 ≤ δ ∧ δ ≤ 1/2) :
    referenceLength (L/8) (4*L) ((1-δ)*x/(p*r)) (x/(p*r)) = δ*x/(p*r) := by
  obtain ⟨hlo,hhi⟩ := reference_containment P R L p r x δ hP hR hL hp hr hx hδ
  have hpr : 0 < p*r := mul_pos (hP.trans_le hp.1) (hR.trans_le hr.1)
  have hxpos : 0 < x := (mul_pos (mul_pos hP hR) hL).trans_le hx.1
  have horder : (1-δ)*x/(p*r) ≤ x/(p*r) := by
    apply div_le_div_of_nonneg_right _ hpr.le
    nlinarith [mul_nonneg hδ.1 hxpos.le]
  have htop : x/(p*r) ≤ 4*L := by linarith
  unfold referenceLength
  rw [min_eq_right htop, max_eq_right hlo, max_eq_right (sub_nonneg.mpr horder)]
  ring

/-- Exact reciprocal masses, with arbitrary finite supports and weights.
No approximation of either mass by log 2 is used. -/
theorem reference_sum (S T : Finset ℕ) (a b : ℕ → ℝ) (δ x : ℝ) :
    (∑ p ∈ S, ∑ r ∈ T, a p*b r*(δ*x/((p:ℝ)*(r:ℝ)))) =
      δ*x*(∑ p ∈ S, a p/(p:ℝ))*(∑ r ∈ T, b r/(r:ℝ)) := by
  calc
    _ = ∑ p ∈ S, (δ*x*(a p/(p:ℝ)))*(∑ r ∈ T, b r/(r:ℝ)) := by
      apply Finset.sum_congr rfl
      intro p _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ = _ := by rw [←Finset.sum_mul, ←Finset.mul_sum]

/-- The moment threshold balances its small-value contribution exactly. -/
theorem fractional_threshold_exponents (h p : ℝ) (hp : p ≠ 6) :
    1+(p-2)/(6-p) = 4/(6-p) ∧
      -h-2*h*(p-2)/(6-p) = -h*(p+2)/(6-p) := by
  have hd : 6-p ≠ 0 := sub_ne_zero.mpr (Ne.symm hp)
  constructor <;> field_simp <;> ring

/-- A uniform reciprocal-moment surplus gives a uniform extracted power. -/
theorem extracted_power_lower (S η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1)
    (hS : 1+η ≤ S) : η ≤ 2-2/S := by
  have hSp : 0 < S := by linarith
  have hh : 0 ≤ η*(1-η) := mul_nonneg hη.le (by linarith)
  have hm := mul_le_mul_of_nonneg_right hS (show 0 ≤ 2-η by linarith)
  have hmul : 2 ≤ (2-η)*S := by nlinarith
  have hdiv : 2/S ≤ 2-η := (div_le_iff₀ hSp).mpr hmul
  linarith

theorem parameter_margins :
    4*((8993/10000:ℝ)-562/625)=1/2500 ∧
    2*(101/1000:ℝ)+562/625-1=253/2500 ∧
    2*(101/1000:ℝ)+2*(562/625)-2=1/2500 ∧
    (100000:ℝ)*(1/2000)-17=33 := by norm_num

#print axioms reference_length_exact
#print axioms reference_sum
run_cmd do
  for target in [``reference_containment, ``reference_length_exact, ``reference_sum,
      ``fractional_threshold_exponents, ``extracted_power_lower, ``parameter_margins] do
    for ax in (←Lean.collectAxioms target) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "SOURCE WINDOW ALGEBRA — ONLY VALID IF THIS FILE COMPILES"
end SourceWindowGeometry
