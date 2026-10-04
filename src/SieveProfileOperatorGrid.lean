import SieveProfileOperatorCumulative
import SieveStoppingArithmeticContraction
import SieveStoppingForcing

/-! Finite inverse-logarithmic rectangle transfer for the actual two-step
operator. Every finite coefficient is rational when the grid data are rational. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Real
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace SieveProfileOperatorGrid
open SieveStoppingExpansion PrimeEulerLogBounds PrimeEulerProfileIntervals
open SieveProfileOperatorCumulative

def edge (h : ℝ) (k : ℕ) : ℝ := 1+(k:ℝ)*h

def cumulative (T z c : ℝ) : ℝ :=
  ∑ p ∈ SieveSmallWeights.pool z,
    (PrimeEulerMass.weight p/primeEuler z)*innerMass (T/(p:ℝ)) p c

def binInner (r c l u e : ℝ) : ℝ :=
  (shape c (r*l-1)+e*u*(c+1)^2)*(1+3*e*u)

def gridBound (r c h : ℝ) (N : ℕ) (e : ℝ) : ℝ :=
  ∑ k ∈ Finset.range N,
    binInner r c (edge h k) (edge h (k+1)) e *
      ((edge h (k+1)-edge h k)+e*(edge h (k+1))^2)*(1+e*edge h k)

theorem edge_ge_one (h : ℝ) (k : ℕ) (hh : 0 ≤ h) : 1 ≤ edge h k := by
  unfold edge
  have hp := mul_nonneg (Nat.cast_nonneg k : (0:ℝ) ≤ k) hh
  linarith

theorem edge_mono (h : ℝ) (i j : ℕ) (hh : 0 ≤ h) (hij : i ≤ j) : edge h i ≤ edge h j := by
  unfold edge
  have hij' : (i:ℝ) ≤ j := by exact_mod_cast hij
  linarith [mul_le_mul_of_nonneg_right hij' hh]

theorem weighted_interval_split (a b d : ℝ) (g : ℕ → ℝ) (hab : a ≤ b) (hbd : b ≤ d) :
    (∑ p ∈ intervalPrimes a d, g p) =
      (∑ p ∈ intervalPrimes a b, g p)+(∑ p ∈ intervalPrimes b d, g p) := by
  have hs : intervalPrimes a d = intervalPrimes a b ∪ intervalPrimes b d := by
    ext p
    simp only [Finset.mem_union, mem_intervalPrimes]
    constructor
    · rintro ⟨hp, hpd, hap⟩
      by_cases hpb : (p:ℝ) < b
      · exact Or.inl ⟨hp, hpb, hap⟩
      · exact Or.inr ⟨hp, hpd, le_of_not_gt hpb⟩
    · rintro (⟨hp, hpb, hap⟩ | ⟨hp, hpd, hbp⟩)
      · exact ⟨hp, hpb.trans_le hbd, hap⟩
      · exact ⟨hp, hpd, hab.trans hbp⟩
  have hd : Disjoint (intervalPrimes a b) (intervalPrimes b d) := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    have hp' := (mem_intervalPrimes a b p).mp hp
    have hq' := (mem_intervalPrimes b d p).mp hq
    linarith
  rw [hs, Finset.sum_union hd]

theorem weighted_grid_partition (z h : ℝ) (N : ℕ) (g : ℕ → ℝ)
    (hz : 1 ≤ z) (hh : 0 ≤ h) :
    (∑ p ∈ intervalPrimes (cut z (edge h N)) z, g p) =
      ∑ k ∈ Finset.range N, ∑ p ∈ intervalPrimes
        (cut z (edge h (k+1))) (cut z (edge h k)), g p := by
  induction N with
  | zero =>
    simp only [edge, Nat.cast_zero, zero_mul, add_zero, cut, div_one,
      exp_log (by linarith : 0 < z), Finset.range_zero, Finset.sum_empty]
    apply Finset.sum_eq_zero
    intro p hp
    have hp' := (mem_intervalPrimes z z p).mp hp
    linarith
  | succ N ih =>
    have he0 : 0 < edge h N := by linarith [edge_ge_one h N hh]
    have hab := cut_mono z (edge h N) (edge h (N+1)) hz he0
      (edge_mono h N (N+1) hh (by omega))
    have hbz := cut_le z (edge h N) hz (edge_ge_one h N hh)
    rw [weighted_interval_split _ _ _ g hab hbz, ih, Finset.sum_range_succ]
    ring

theorem inverse_bin_parameters (z l u : ℝ) (p : ℕ) (_hz : 2 ≤ z)
    (hl : 1 ≤ l) (hlu : l ≤ u)
    (hp : p ∈ intervalPrimes (cut z u) (cut z l)) :
    l ≤ log z/log (p:ℝ) ∧ log z/log (p:ℝ) ≤ u := by
  obtain ⟨hpprime, hpu, hlp⟩ := (mem_intervalPrimes _ _ p).mp hp
  have hp1 : (1:ℝ) < p := by exact_mod_cast hpprime.one_lt
  have hp0 : (0:ℝ) < p := by linarith
  have hlp0 : 0 < log (p:ℝ) := log_pos hp1
  have hl0 : 0 < l := by linarith
  have hu0 : 0 < u := by linarith
  have hleft := log_le_log (exp_pos _) hlp
  have hright := log_le_log hp0 hpu.le
  rw [log_exp] at hleft
  rw [log_cut] at hright
  constructor
  · apply (le_div_iff₀ hlp0).mpr
    have hh := (le_div_iff₀ hl0).mp hright
    nlinarith
  · apply (div_le_iff₀ hlp0).mpr
    have hh := (div_le_iff₀ hu0).mp hleft
    nlinarith

theorem parent_level (T z : ℝ) (p : ℕ) (hz : 2 ≤ z) (hT : z^2 ≤ T)
    (hp : p ∈ SieveSmallWeights.pool z) : z ≤ T/(p:ℝ) ∧ (p:ℝ) ≤ T/(p:ℝ) := by
  obtain ⟨hpp, hpz⟩ := (SieveSmallWeights.mem_pool z p).mp hp
  have hp0 : (0:ℝ) < p := by exact_mod_cast hpp.pos
  have hz0 : 0 < z := by linarith
  have hh : z ≤ T/(p:ℝ) := (le_div_iff₀ hp0).mpr (by nlinarith)
  exact ⟨hh, hpz.le.trans hh⟩

theorem child_parameter_eq (T : ℝ) (p : ℕ) (hT : 0 < T) (hp : Nat.Prime p) :
    log (T/(p:ℝ))/log (p:ℝ) = log T/log (p:ℝ)-1 := by
  have hp0 : (0:ℝ) < p := by exact_mod_cast hp.pos
  have hlp : log (p:ℝ) ≠ 0 := (log_pos (by exact_mod_cast hp.one_lt)).ne'
  rw [log_div hT.ne' hp0.ne']
  field_simp

theorem cumulative_truncated (T z c r h : ℝ) (N : ℕ)
    (hz : 2 ≤ z) (hT : z^2 ≤ T) (hc : 2 ≤ c) (hr : 2 ≤ r) (hh : 0 ≤ h)
    (hparam : r ≤ log T/log z) (hcover : c+2 ≤ r*edge h N) :
    cumulative T z c = ∑ p ∈ intervalPrimes (cut z (edge h N)) z,
      (PrimeEulerMass.weight p/primeEuler z)*innerMass (T/(p:ℝ)) p c := by
  rw [SieveStoppingForcing.interval_eq_filter, Finset.sum_filter]
  unfold cumulative
  apply Finset.sum_congr rfl
  intro p hp
  split_ifs with ha
  · rfl
  · obtain ⟨hpp, hpz⟩ := (SieveSmallWeights.mem_pool z p).mp hp
    have hp2 : (2:ℝ) ≤ p := by exact_mod_cast hpp.two_le
    have hp0 : (0:ℝ) < p := by linarith
    have hlp : 0 < log (p:ℝ) := log_pos (by linarith)
    have hlz : 0 < log z := log_pos (by linarith)
    have hT0 : 0 < T := by nlinarith
    have he0 : 0 < edge h N := by linarith [edge_ge_one h N hh]
    have hpl := log_le_log hp0 (le_of_not_ge ha)
    rw [log_cut] at hpl
    have hpl' := (le_div_iff₀ he0).mp hpl
    have hTl := (le_div_iff₀ hlz).mp hparam
    have hcp : (c+2)*log (p:ℝ) ≤ log T := calc
      _ ≤ (r*edge h N)*log (p:ℝ) := mul_le_mul_of_nonneg_right hcover hlp.le
      _ = r*(log (p:ℝ)*edge h N) := by ring
      _ ≤ r*log z := mul_le_mul_of_nonneg_left hpl' (by linarith)
      _ ≤ _ := hTl
    have hs : c+1 ≤ log (T/(p:ℝ))/log (p:ℝ) := by
      rw [child_parameter_eq T p hT0 hpp]
      have hh := (le_div_iff₀ hlp).mpr hcp
      linarith
    rw [innerMass_zero (T/(p:ℝ)) p c hp2 (parent_level T z p hz hT hp).2 hc hs,
      mul_zero]

theorem inner_bin_bound (T z c r l u : ℝ) (p : ℕ)
    (hz : 2 ≤ z) (hT : z^2 ≤ T) (hc : 2 ≤ c) (hr : 2 ≤ r)
    (hl : 1 ≤ l) (hlu : l ≤ u) (hparam : r ≤ log T/log z)
    (hcut : 2 ≤ lowerCut z c)
    (hp : p ∈ intervalPrimes (cut z u) (cut z l)) :
    innerMass (T/(p:ℝ)) p c ≤ binInner r c l u (epsilon z) := by
  obtain ⟨hpp, hpU, hpL⟩ := (mem_intervalPrimes _ _ p).mp hp
  have hpz : (p:ℝ) < z := hpU.trans_le (cut_le z l (by linarith) hl)
  have hpool : p ∈ SieveSmallWeights.pool z := (SieveSmallWeights.mem_pool z p).mpr ⟨hpp, hpz⟩
  have hp2 : (2:ℝ) ≤ p := by exact_mod_cast hpp.two_le
  have hp0 : (0:ℝ) < p := by linarith
  have hT0 : 0 < T := by nlinarith
  have hz0 : 0 < z := by linarith
  have hlz : 0 < log z := log_pos (by linarith)
  have hlp : 0 < log (p:ℝ) := log_pos (by linarith)
  have hTp := parent_level T z p hz hT hpool
  have ha : 2 ≤ lowerCut (T/(p:ℝ)) c := hcut.trans (exp_le_exp.mpr
    (div_le_div_of_nonneg_right (log_le_log hz0 hTp.1) (by linarith)))
  have hb := innerMass_bound (T/(p:ℝ)) p c hp2 hTp.2 hc ha
  obtain ⟨hxL, hxU⟩ := inverse_bin_parameters z l u p hz hl hlu hp
  have hid : (log T/log z)*(log z/log (p:ℝ)) = log T/log (p:ℝ) := by field_simp
  have hs : r*l-1 ≤ log (T/(p:ℝ))/log (p:ℝ) := by
    rw [child_parameter_eq T p hT0 hpp]
    have hh := mul_le_mul hparam hxL (by linarith : 0 ≤ l)
      (div_nonneg (log_pos (by nlinarith : 1 < T)).le hlz.le)
    rw [hid] at hh
    linarith
  have hs0 : 0 < r*l-1 := by nlinarith
  have hshape := shape_antitone c (r*l-1) _ hc hs0 hs
  have he0 : 0 ≤ epsilon z := div_nonneg PrimeEulerDimensionOne.errorConstant_pos.le hlz.le
  have heP0 : 0 ≤ epsilon (p:ℝ) := div_nonneg PrimeEulerDimensionOne.errorConstant_pos.le hlp.le
  have heid : epsilon (p:ℝ) = epsilon z*(log z/log (p:ℝ)) := by
    unfold epsilon
    field_simp
  have heP : epsilon (p:ℝ) ≤ epsilon z*u := by
    rw [heid]
    exact mul_le_mul_of_nonneg_left hxU he0
  have hu0 : 0 ≤ u := by linarith
  unfold binInner
  exact hb.trans (mul_le_mul
    (add_le_add hshape (mul_le_mul_of_nonneg_right heP (sq_nonneg _)))
    (by nlinarith)
    (by positivity : 0 ≤ 1+3*epsilon (p:ℝ))
    (add_nonneg (shape_nonneg _ _) (by positivity)))

theorem operator_indicator_eq (T z c : ℝ) :
    SieveStoppingTwoStep.operator (fun T z => if log T/log z ≤ c then 1 else 0) T z =
      cumulative T z c := by
  unfold SieveStoppingTwoStep.operator cumulative
  apply Finset.sum_congr rfl
  intro p hp
  unfold innerMass PrimeEulerAcceptedInner.acceptedPrimes
  rw [Finset.sum_filter, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  dsimp only
  by_cases hg : (q:ℝ)^3 < T/(p:ℝ)
  · simp only [hg, ite_true]
    by_cases hs : log ((T/(p:ℝ))/(q:ℝ))/log (q:ℝ) ≤ c
    · simp only [hs, ite_true, mul_one]
      unfold PrimeEulerMass.weight
      have hp0 := (SieveEulerRatio.euler_pos (p:ℝ)).ne'
      field_simp
    · simp only [hs, ite_false, mul_zero]
  · simp only [hg, ite_false, mul_zero]

/-- Explicit arithmetic rectangle bound for the actual cumulative operator. -/
theorem cumulative_grid_bound (T z c r h : ℝ) (N : ℕ)
    (hz : 2 ≤ z) (hT : z^2 ≤ T) (hc : 2 ≤ c) (hr : 2 ≤ r) (hh : 0 ≤ h)
    (hparam : r ≤ log T/log z) (hcover : c+2 ≤ r*edge h N)
    (hcut : 2 ≤ lowerCut z c) (hgrid : 2 ≤ cut z (edge h N)) :
    cumulative T z c ≤ gridBound r c h N (epsilon z) := by
  have he0 : 0 ≤ epsilon z := div_nonneg PrimeEulerDimensionOne.errorConstant_pos.le
    (log_pos (by linarith : 1 < z)).le
  rw [cumulative_truncated T z c r h N hz hT hc hr hh hparam hcover,
    weighted_grid_partition z h N _ (by linarith) hh]
  unfold gridBound
  apply Finset.sum_le_sum
  intro k hk
  have hkN : k+1 ≤ N := by have hk' := Finset.mem_range.mp hk; omega
  have hl : 1 ≤ edge h k := edge_ge_one h k hh
  have hlu : edge h k ≤ edge h (k+1) := edge_mono h k (k+1) hh (by omega)
  have huN : edge h (k+1) ≤ edge h N := edge_mono h (k+1) N hh hkN
  have ha : 2 ≤ cut z (edge h (k+1)) := hgrid.trans (cut_mono z _ _
    (by linarith) (by linarith) huN)
  have hbin0 : 0 ≤ binInner r c (edge h k) (edge h (k+1)) (epsilon z) := by
    unfold binInner
    have hu0 : 0 ≤ edge h (k+1) := by linarith
    exact mul_nonneg (add_nonneg (shape_nonneg _ _) (by positivity)) (by positivity)
  calc
    _ ≤ ∑ p ∈ intervalPrimes (cut z (edge h (k+1))) (cut z (edge h k)),
        (PrimeEulerMass.weight p/primeEuler z)*
          binInner r c (edge h k) (edge h (k+1)) (epsilon z) := by
      apply Finset.sum_le_sum
      intro p hp
      exact mul_le_mul_of_nonneg_left
        (inner_bin_bound T z c r _ _ p hz hT hc hr hl hlu hparam hcut hp)
        (div_nonneg (PrimeEulerMass.weight_nonneg p) (SieveEulerRatio.euler_pos z).le)
    _ = binInner r c (edge h k) (edge h (k+1)) (epsilon z)*
        mass (cut z (edge h (k+1))) (cut z (edge h k)) z := by
      rw [mass, ← Finset.sum_mul, mul_comm]
    _ ≤ binInner r c (edge h k) (edge h (k+1)) (epsilon z)*
        (((edge h (k+1)-edge h k)+epsilon z*(edge h (k+1))^2)*
          (1+epsilon z*edge h k)) :=
      mul_le_mul_of_nonneg_left (inverse_bin_bound z _ _ hz hl hlu ha) hbin0
    _ = _ := by ring

theorem gridBound_zero (r c h : ℝ) (N : ℕ) :
    gridBound r c h N 0 = h*∑ k ∈ Finset.range N, shape c (r*edge h k-1) := by
  unfold gridBound binInner
  simp only [zero_mul, add_zero, mul_one]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  unfold edge
  push_cast
  ring

run_cmd do
  for decl in [``edge, ``cumulative, ``binInner, ``gridBound, ``edge_ge_one,
    ``edge_mono, ``weighted_interval_split, ``weighted_grid_partition,
    ``inverse_bin_parameters, ``parent_level, ``child_parameter_eq,
    ``cumulative_truncated, ``inner_bin_bound, ``operator_indicator_eq,
    ``cumulative_grid_bound, ``gridBound_zero] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ACTUAL CUMULATIVE PROFILE GRID INGREDIENTS PASSED"
end SieveProfileOperatorGrid
end
