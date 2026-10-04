import SourceLiteralMass
import MomentResidualEven

/-! v7. Mixed source coefficients, preserving all product collisions.
UNCOMPILED DRAFT. Three different supports are used; they are not replaced
by the cube of one restricted polynomial. The log^3 cap is proved using the
Mangoldt divisor identity. The second energy uses reciprocal mass once,
rather than squaring the pointwise cap. -/
set_option autoImplicit false
set_option maxHeartbeats 16000000
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace SourceMixedCoefficient
open MomentResidualConvolution MomentResidualInterval MomentResidualEven
open SourceLiteralMoments SourceLiteralMass SourceMassDischarge
open PositiveInteriorCells PositiveInteriorModel Erdos374.HarmanGram152

def array (S : Finset ℕ) : ArithmeticFunction ℂ :=
  ⟨fun n => restricted S n, by simp [restricted, mangoldt]⟩

@[simp] theorem array_apply (S : Finset ℕ) (n : ℕ) :
    array S n = restricted S n := rfl

theorem array_majorant (S : Finset ℕ) (n : ℕ) :
    ‖array S n‖ ≤ ArithmeticFunction.vonMangoldt n := restricted_majorant S n

theorem array_mem (S : Finset ℕ) (n : ℕ) (hn : array S n ≠ 0) : n ∈ S := by
  by_contra h
  exact hn (by simp [array, restricted, h])

/-- One Mangoldt-dominated factor times any logarithmically bounded factor. -/
theorem mul_log_bound (a b : ArithmeticFunction ℂ) (h : ℕ)
    (ha : ∀ n, ‖a n‖ ≤ ArithmeticFunction.vonMangoldt n)
    (hb : ∀ n, ‖b n‖ ≤ (Real.log (n:ℝ))^h) (n : ℕ) :
    ‖(a*b) n‖ ≤ (Real.log (n:ℝ))^(h+1) := by
  by_cases hn : n = 0
  · simp [hn]
  rw [ArithmeticFunction.mul_apply]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ uv ∈ n.divisorsAntidiagonal,
        ArithmeticFunction.vonMangoldt uv.1 * (Real.log (n:ℝ))^h := by
      apply Finset.sum_le_sum
      intro uv huv
      have hu : 1 ≤ uv.1 := Nat.one_le_iff_ne_zero.mpr
        (Nat.left_ne_zero_of_mem_divisorsAntidiagonal huv)
      have hv : 1 ≤ uv.2 := Nat.one_le_iff_ne_zero.mpr
        (Nat.right_ne_zero_of_mem_divisorsAntidiagonal huv)
      have hvn : uv.2 ≤ n := by
        calc
          _ = 1*uv.2 := by simp
          _ ≤ uv.1*uv.2 := Nat.mul_le_mul_right _ hu
          _ = _ := (Nat.mem_divisorsAntidiagonal.mp huv).1
      have hvr : (1:ℝ) ≤ uv.2 := by exact_mod_cast hv
      have hvrn : (uv.2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hvn
      have hp := pow_le_pow_left₀ (Real.log_nonneg hvr)
        (Real.log_le_log (by linarith) hvrn) h
      rw [norm_mul]
      exact mul_le_mul (ha _) ((hb _).trans hp) (norm_nonneg _)
        ArithmeticFunction.vonMangoldt_nonneg
    _ = (∑ uv ∈ n.divisorsAntidiagonal, ArithmeticFunction.vonMangoldt uv.1) *
        (Real.log (n:ℝ))^h := (Finset.sum_mul _ _ _).symm
    _ = _ := by
      rw [Nat.sum_divisorsAntidiagonal (fun d _ => ArithmeticFunction.vonMangoldt d),
        ArithmeticFunction.vonMangoldt_sum, pow_succ]
      ring

def coefficient (X : ℝ) (j : ℕ × ℕ) : ArithmeticFunction ℂ :=
  array (support X j 0) * (array (support X j 1) * array (support X j 2))

theorem coefficient_log_cap (X : ℝ) (j : ℕ × ℕ) (n : ℕ) :
    ‖coefficient X j n‖ ≤ (Real.log (n:ℝ))^3 := by
  apply mul_log_bound _ _ 2 (array_majorant _) _ n
  intro m
  apply mul_log_bound _ _ 1 (array_majorant _) _ m
  intro r
  simpa only [pow_one] using (array_majorant (support X j 2) r).trans
    ArithmeticFunction.vonMangoldt_le_log

def top (X : ℝ) (j : ℕ × ℕ) : Fin 3 → ℕ :=
  ![2*2^j.1, 2*2^j.2, ⌊4*thirdScale X j⌋₊]

def totalTop (X : ℝ) (j : ℕ × ℕ) : ℕ := top X j 0 * (top X j 1 * top X j 2)

theorem support_le_top (X : ℝ) (j : ℕ × ℕ) (i : Fin 3) (n : ℕ)
    (hn : n ∈ support X j i) : n ≤ top X j i := by
  fin_cases i
  · exact (Finset.mem_Ico.mp hn).2.le
  · exact (Finset.mem_Ico.mp hn).2.le
  · exact (Finset.mem_Ioc.mp hn).2

theorem array_vanishes (X : ℝ) (j : ℕ × ℕ) (i : Fin 3) (n : ℕ)
    (hn : top X j i < n) : array (support X j i) n = 0 := by
  by_contra h
  exact (not_le_of_gt hn) (support_le_top X j i n (array_mem _ _ h))

theorem mul_vanishes (a b : ArithmeticFunction ℂ) (N M : ℕ)
    (ha : ∀ n, N < n → a n = 0) (hb : ∀ n, M < n → b n = 0)
    (n : ℕ) (hn : N*M < n) : (a*b) n = 0 := by
  rw [ArithmeticFunction.mul_apply]
  apply Finset.sum_eq_zero
  intro uv huv
  by_cases hu : N < uv.1
  · rw [ha _ hu, zero_mul]
  · have hv : M < uv.2 := by
      have he := (Nat.mem_divisorsAntidiagonal.mp huv).1
      by_contra hv
      have hh := Nat.mul_le_mul (Nat.le_of_not_gt hu) (Nat.le_of_not_gt hv)
      rw [he] at hh
      omega
    rw [hb _ hv, mul_zero]

theorem top_pos (X : ℝ) (j : ℕ × ℕ) (i : Fin 3)
    (hX : 2 ≤ X) (hlog : 1000000 ≤ Real.log X) (hj : j ∈ boxes (mesh X)) :
    1 ≤ top X j i := by
  fin_cases i
  · dsimp [top]
    have hp : 0 < (2:ℕ)^j.1 := by positivity
    omega
  · dsimp [top]
    have hp : 0 < (2:ℕ)^j.2 := by positivity
    omega
  · have h := (large_ideal X j (by linarith) hlog hj 2).1
    apply Nat.le_floor
    norm_num only [Nat.cast_one]
    change 16 ≤ thirdScale X j at h
    linarith

theorem array_mass (X : ℝ) (j : ℕ × ℕ) (i : Fin 3) :
    (∑ n ∈ Finset.Ioc 0 (top X j i), ‖array (support X j i) n‖/(n:ℝ)) =
      SourceLiteralMass.reciprocalMass X j i := by
  have hsub : support X j i ⊆ Finset.Ioc 0 (top X j i) := by
    intro n hn
    exact Finset.mem_Ioc.mpr ⟨support_pos X j i n hn, support_le_top X j i n hn⟩
  calc
    _ = ∑ n ∈ support X j i, ‖array (support X j i) n‖/(n:ℝ) := by
      symm
      apply Finset.sum_subset hsub
      intro n _ hn
      simp [array, restricted, hn]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n hn
      simp [array, restricted, hn, mangoldt, Complex.norm_real,
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]

theorem coefficient_mass (X : ℝ) (j : ℕ × ℕ)
    (hX : 2 ≤ X) (hlog : 1000000 ≤ Real.log X) (hj : j ∈ boxes (mesh X)) :
    (∑ n ∈ Finset.Ioc 0 (totalTop X j), ‖coefficient X j n‖/(n:ℝ)) ≤ 3375 := by
  let a := array (support X j 0)
  let b := array (support X j 1)
  let c := array (support X j 2)
  let N := top X j 0
  let M := top X j 1
  let L := top X j 2
  have hN := top_pos X j 0 hX hlog hj
  have hM := top_pos X j 1 hX hlog hj
  have hL := top_pos X j 2 hX hlog hj
  have hbc := finite_reciprocal_mass_mul_le M L hM hL b c
    (array_vanishes X j 1) (array_vanishes X j 2)
  have habc := finite_reciprocal_mass_mul_le N (M*L) hN (by nlinarith) a (b*c)
    (array_vanishes X j 0)
    (mul_vanishes b c M L (array_vanishes X j 1) (array_vanishes X j 2))
  have hfirst : (∑ n ∈ Finset.Ioc 0 N, ‖a n‖/(n:ℝ)) ≤ 15 := by
    rw [array_mass]
    exact mass_le_fifteen X j 0 hX hlog hj
  have hsecond : (∑ n ∈ Finset.Ioc 0 M, ‖b n‖/(n:ℝ)) ≤ 15 := by
    rw [array_mass]
    exact mass_le_fifteen X j 1 hX hlog hj
  have hthird : (∑ n ∈ Finset.Ioc 0 L, ‖c n‖/(n:ℝ)) ≤ 15 := by
    rw [array_mass]
    exact mass_le_fifteen X j 2 hX hlog hj
  have hbc' : (∑ n ∈ Finset.Ioc 0 (M*L), ‖(b*c) n‖/(n:ℝ)) ≤ 225 := by
    exact hbc.trans ((mul_le_mul hsecond hthird
      (Finset.sum_nonneg (fun _ _ => by positivity)) (by norm_num)).trans_eq (by norm_num))
  exact habc.trans ((mul_le_mul hfirst hbc'
    (Finset.sum_nonneg (fun _ _ => by positivity)) (by norm_num)).trans_eq (by norm_num))

/-- Weighted energy pays only one log^3 coefficient cap. -/
theorem energy_from_mass (S : Finset ℕ) (a : ℕ → ℂ) (X H B : ℝ)
    (hX : 0 < X) (hH : 0 ≤ H)
    (hlower : ∀ n ∈ S, a n ≠ 0 → X/8 ≤ (n:ℝ))
    (hcap : ∀ n ∈ S, ‖a n‖ ≤ H)
    (hmass : (∑ n ∈ S, ‖a n‖/(n:ℝ)) ≤ B) :
    (∑ n ∈ S, ‖a n‖^2/(n:ℝ)^2) ≤ (8*H/X)*B := by
  have hpoint (n : ℕ) (hn : n ∈ S) :
      ‖a n‖^2/(n:ℝ)^2 ≤ (8*H/X)*(‖a n‖/(n:ℝ)) := by
    by_cases hz : a n = 0
    · simp [hz]
    have hlo := hlower n hn hz
    have hnp : (0:ℝ) < n := by linarith
    have hratio : ‖a n‖/(n:ℝ) ≤ 8*H/X := by
      apply (div_le_iff₀ hnp).mpr
      have hh := mul_le_mul_of_nonneg_left hlo (show 0 ≤ 8*H/X by positivity)
      have he : (8*H/X)*(X/8)=H := by field_simp <;> ring
      rw [he] at hh
      exact (hcap n hn).trans hh
    calc
      ‖a n‖^2/(n:ℝ)^2 = (‖a n‖/(n:ℝ))*(‖a n‖/(n:ℝ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hratio
        (by positivity : 0 ≤ ‖a n‖/(n:ℝ))
  calc
    _ ≤ ∑ n ∈ S, (8*H/X)*(‖a n‖/(n:ℝ)) := Finset.sum_le_sum hpoint
    _ = (8*H/X)*(∑ n ∈ S, ‖a n‖/(n:ℝ)) := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hmass (by positivity)

#print axioms coefficient_log_cap
#print axioms coefficient_mass
#print axioms energy_from_mass
run_cmd do
  for n in [``array_apply, ``array_majorant, ``array_mem, ``mul_log_bound, ``coefficient_log_cap,
      ``support_le_top, ``array_vanishes, ``mul_vanishes, ``top_pos,
      ``array_mass, ``coefficient_mass, ``energy_from_mass] do
    for ax in (← Lean.collectAxioms n) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {n}"
  Lean.logInfo "V7 MIXED COEFFICIENT ENERGY: VALID ONLY AFTER COMPILATION"
end SourceMixedCoefficient
