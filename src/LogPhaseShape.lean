import DifferenceParameters

/-!
Logarithmic phase shapes for ordinary Dirichlet polynomials. This follows
the seed's ReciprocalAllOrderShape152 proof and reuses its derivative
chain after the first derivative. Namespace and definitions are new.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Set
open scoped BigOperators

namespace LogPhaseShape
open Erdos374.ReciprocalPhase147 Erdos374.ReciprocalPhaseShape152
open Erdos374.HigherDifference152

def phase (u x : ℝ) : ℝ := u * Real.log x

def derivativeChain (u : ℝ) : ℕ → ℝ → ℝ
  | 0 => phase u
  | j + 1 => derivativeFormula j u 0

theorem derivativeChain_hasDerivAt (j : ℕ) (u x : ℝ) (hx : x ≠ 0) :
    HasDerivAt (derivativeChain u j) (derivativeChain u (j + 1) x) x := by
  cases j with
  | zero =>
    change HasDerivAt (fun y => u * Real.log y) (derivativeFormula 0 u 0 x) x
    convert (Real.hasDerivAt_log hx).const_mul u using 1
    simp [derivativeFormula, div_eq_mul_inv]
  | succ j => exact derivativeFormula_hasDerivAt j u 0 x hx

theorem oriented_derivative (r : ℕ) (u x : ℝ) (hx : x ≠ 0) :
    derivativeChain ((-1 : ℝ) ^ r * u) (r + 1) x =
      (r.factorial : ℝ) * u / x ^ (r + 1) := by
  have h := derivativeFormula_oriented r u 0 x hx
  simpa [derivativeChain, normalized, div_mul_eq_mul_div] using h

theorem oriented_derivative_antitone (r : ℕ) (a u : ℝ)
    (ha : 0 < a) (hu : 0 ≤ u) :
    AntitoneOn (derivativeChain ((-1 : ℝ) ^ r * u) (r + 1)) (Ici a) := by
  intro x hx y hy hxy
  rw [oriented_derivative r u y (ha.trans_le hy).ne',
    oriented_derivative r u x (ha.trans_le hx).ne']
  exact div_le_div_of_nonneg_left (by positivity)
    (pow_pos (ha.trans_le hx) _) (pow_le_pow_left₀ (ha.trans_le hx).le hxy _)

theorem oriented_difference_antitone (r : ℕ) (a u : ℝ)
    (ha : 0 < a) (hu : 0 ≤ u) :
    Antitone (difference (r + 1)
      (fun n => phase ((-1 : ℝ) ^ r * u) (a + n))) := by
  have hm := realDifference_antitone (r + 1)
    (derivativeChain ((-1 : ℝ) ^ r * u))
    (fun j t ht => derivativeChain_hasDerivAt j _ t (ha.trans_le ht).ne')
    (oriented_derivative_antitone r a u ha hu)
  intro m n hmn
  rw [difference_sequence_eq_real, difference_sequence_eq_real]
  exact hm (by change a ≤ a + m; linarith [Nat.cast_nonneg (α := ℝ) m])
    (by change a ≤ a + n; linarith [Nat.cast_nonneg (α := ℝ) n])
    (add_le_add (le_refl a) (Nat.cast_le.mpr hmn))

theorem oriented_difference_bounds (r N n : ℕ) (a u : ℝ)
    (ha : 0 < a) (hu : 0 ≤ u) (hn : n < N) :
    (r.factorial : ℝ) * u / (a + (N : ℝ) + (r + 1 : ℕ)) ^ (r + 1) ≤
        difference (r + 1)
          (fun k => phase ((-1 : ℝ) ^ r * u) (a + k)) n ∧
      difference (r + 1)
          (fun k => phase ((-1 : ℝ) ^ r * u) (a + k)) n ≤
        (r.factorial : ℝ) * u / a ^ (r + 1) := by
  obtain ⟨z, hz, hez⟩ := exists_realDifference_eq (r + 1)
    (derivativeChain ((-1 : ℝ) ^ r * u))
    (fun j t ht => derivativeChain_hasDerivAt j _ t (ha.trans_le ht).ne')
    (show a ≤ a + n by linarith [Nat.cast_nonneg (α := ℝ) n])
  have haz : a ≤ z := by linarith [hz.1, Nat.cast_nonneg (α := ℝ) n]
  have hz0 : 0 < z := ha.trans_le haz
  have hzN : z ≤ a + (N : ℝ) + (r + 1 : ℕ) := by
    have hnR : (n : ℝ) ≤ N := by exact_mod_cast hn.le
    linarith [hz.2]
  rw [difference_sequence_eq_real]
  change realDifference (r + 1) (phase _) _ = _ at hez
  rw [hez, oriented_derivative r u z hz0.ne']
  exact ⟨div_le_div_of_nonneg_left (by positivity) (pow_pos hz0 _)
      (pow_le_pow_left₀ hz0.le hzN _),
    div_le_div_of_nonneg_left (by positivity) (pow_pos ha _)
      (pow_le_pow_left₀ ha.le haz _)⟩

theorem norm_sum_neg (M : ℕ) (a u : ℝ) :
    ‖∑ n ∈ Finset.range M,
      Erdos374.KusminLandau151.e (phase (-u) (a + n))‖ =
    ‖∑ n ∈ Finset.range M,
      Erdos374.KusminLandau151.e (phase u (a + n))‖ := by
  simpa [phase] using Erdos374.ReciprocalPhaseShape152.norm_sum_e_neg M
    (fun n => phase u (a + n))

theorem norm_sum_oriented (r M : ℕ) (a u : ℝ) :
    ‖∑ n ∈ Finset.range M,
      Erdos374.KusminLandau151.e (phase ((-1 : ℝ) ^ r * u) (a + n))‖ =
    ‖∑ n ∈ Finset.range M,
      Erdos374.KusminLandau151.e (phase u (a + n))‖ := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [pow_succ, show (-1 : ℝ) ^ r * -1 * u = -((-1 : ℝ) ^ r * u) by ring,
      norm_sum_neg, ih]

end LogPhaseShape

#print axioms LogPhaseShape.oriented_difference_bounds
run_cmd do
  for target in [``LogPhaseShape.derivativeChain_hasDerivAt,
      ``LogPhaseShape.oriented_difference_antitone,
      ``LogPhaseShape.oriented_difference_bounds,
      ``LogPhaseShape.norm_sum_oriented] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "LOG PHASE SHAPE PASSED"
