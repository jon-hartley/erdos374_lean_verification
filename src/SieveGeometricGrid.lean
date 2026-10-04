import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Nat.Find
import Mathlib.Tactic

/-! Actual half-open boxes for the source grid with eta = s^9.
Every real point between D^(s^2) and D has a unique box.  The finite
index cutoff depends only on s, independently of D and the point.
No tuple selection or boxed sieve inequality is asserted here. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace SieveGeometricGrid

def ratio (s : ℝ) : ℝ := 1 + s^9
def exponent (s : ℝ) (n : ℕ) : ℝ := s^2 * ratio s ^ n
def scale (D s : ℝ) (n : ℕ) : ℝ := D ^ exponent s n
def InBox (D s p : ℝ) (n : ℕ) : Prop :=
  scale D s n ≤ p ∧ p < scale D s (n+1)
def cutoff (s : ℝ) : ℕ := ⌊Real.log (1 / s^2) / Real.log (ratio s)⌋₊

theorem one_lt_ratio (s : ℝ) (hs : 0 < s) : 1 < ratio s := by
  have hp : 0 < s^9 := by positivity
  dsimp [ratio]
  linarith

theorem scale_zero (D s : ℝ) : scale D s 0 = D ^ (s^2) := by
  simp [scale, exponent]

theorem scale_succ (D s : ℝ) (hD : 0 ≤ D) (n : ℕ) :
    scale D s (n+1) = (scale D s n) ^ ratio s := by
  simp only [scale, exponent, pow_succ]
  rw [← mul_assoc, Real.rpow_mul hD]

theorem scale_strictMono (D s : ℝ) (hD : 1 < D) (hs : 0 < s) :
    StrictMono (scale D s) := by
  intro n m hnm
  apply (Real.rpow_lt_rpow_left_iff hD).mpr
  exact mul_lt_mul_of_pos_left (pow_lt_pow_right₀ (one_lt_ratio s hs) hnm)
    (sq_pos_of_pos hs)

theorem exists_scale_above_base (D s : ℝ) (hD : 1 < D) (hs : 0 < s) :
    ∃ n : ℕ, D < scale D s n := by
  have hs2 : 0 < s^2 := sq_pos_of_pos hs
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (1 / s^2) (one_lt_ratio s hs)
  refine ⟨n, ?_⟩
  have hexp : 1 < exponent s n := by
    have hmul := (div_lt_iff₀ hs2).mp hn
    dsimp [exponent]
    nlinarith
  have hh := (Real.rpow_lt_rpow_left_iff hD).mpr hexp
  simpa only [Real.rpow_one, scale] using hh

theorem exists_box (D s p : ℝ) (hD : 1 < D) (hs : 0 < s)
    (hlo : D^(s^2) ≤ p) (hhi : p < D) : ∃ n : ℕ, InBox D s p n := by
  classical
  obtain ⟨j, hj⟩ := exists_scale_above_base D s hD hs
  have hex : ∃ i : ℕ, p < scale D s i := ⟨j, hhi.trans hj⟩
  have hzero : Nat.find hex ≠ 0 := by
    intro he
    have hh := Nat.find_spec hex
    rw [he, scale_zero] at hh
    exact (not_lt_of_ge hlo) hh
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hzero
  refine ⟨n, ?_, ?_⟩
  · by_contra hnot
    have hnsmall := Nat.find_min' hex (lt_of_not_ge hnot)
    omega
  · simpa only [hn, Nat.succ_eq_add_one] using Nat.find_spec hex

theorem box_unique (D s p : ℝ) (hD : 1 < D) (hs : 0 < s)
    (n m : ℕ) (hn : InBox D s p n) (hm : InBox D s p m) : n = m := by
  have hmono := (scale_strictMono D s hD hs).monotone
  rcases lt_trichotomy n m with hlt | heq | hgt
  · have hh := hmono (Nat.succ_le_of_lt hlt)
    exact False.elim ((not_lt_of_ge hm.1) (hn.2.trans_le hh))
  · exact heq
  · have hh := hmono (Nat.succ_le_of_lt hgt)
    exact False.elim ((not_lt_of_ge hn.1) (hm.2.trans_le hh))

theorem index_le_cutoff (D s p : ℝ) (hD : 1 < D) (hs : 0 < s)
    (hhi : p < D) (n : ℕ) (hn : InBox D s p n) : n ≤ cutoff s := by
  have hs2 : 0 < s^2 := sq_pos_of_pos hs
  have hr := one_lt_ratio s hs
  have hexp : exponent s n < 1 := by
    apply (Real.rpow_lt_rpow_left_iff hD).mp
    simpa only [Real.rpow_one, scale] using hn.1.trans_lt hhi
  have hpow : ratio s ^ n < 1 / s^2 := by
    apply (lt_div_iff₀ hs2).mpr
    simpa only [exponent, mul_comm] using hexp
  have hlog := Real.log_lt_log (pow_pos (lt_trans zero_lt_one hr) n) hpow
  rw [Real.log_pow] at hlog
  apply Nat.le_floor
  exact ((lt_div_iff₀ (Real.log_pos hr)).mpr hlog).le

theorem existsUnique_bounded_box (D s p : ℝ) (hD : 1 < D)
    (hs : 0 < s) (hlo : D^(s^2) ≤ p) (hhi : p < D) :
    ∃! n : ℕ, n ≤ cutoff s ∧ InBox D s p n := by
  obtain ⟨n, hn⟩ := exists_box D s p hD hs hlo hhi
  refine ⟨n, ⟨index_le_cutoff D s p hD hs hhi n hn, hn⟩, ?_⟩
  intro m hm
  exact box_unique D s p hD hs m n hm.2 hn

theorem boxes_disjoint (D s : ℝ) (hD : 1 < D) (hs : 0 < s)
    (n m : ℕ) (hne : n ≠ m) :
    Disjoint (Set.Ico (scale D s n) (scale D s (n+1)))
      (Set.Ico (scale D s m) (scale D s (m+1))) := by
  apply Set.disjoint_left.mpr
  intro p hn hm
  exact hne (box_unique D s p hD hs n m hn hm)

#print axioms existsUnique_bounded_box
run_cmd do
  for decl in [``one_lt_ratio, ``scale_zero, ``scale_succ, ``scale_strictMono,
      ``exists_scale_above_base, ``exists_box, ``box_unique, ``index_le_cutoff,
      ``existsUnique_bounded_box, ``boxes_disjoint] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end SieveGeometricGrid
end
