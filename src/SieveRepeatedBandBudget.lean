import SieveBoundaryEuler

/-! Scalar and actual Euler-product budgets for deleting one coordinate of
a repeated-band pair. The two retained coordinate labels cost the square of
the length cap. This module makes no positivity assertion about a reference
sieve sum. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open Real SieveStoppingExpansion

namespace SieveRepeatedBandBudget

def eta (D s : ℝ) : ℝ := s^9 + 10/(s^2*log D)
def budget (D s : ℝ) : ℝ := (25/4)*s + (125/2)/(s^10*log D)

theorem eta_nonneg (D s : ℝ) (hD : 1 < D) (hs : 0 < s) :
    0 ≤ eta D s := by
  have hl : 0 < log D := log_pos hD
  unfold eta
  positivity

theorem budget_nonneg (D s : ℝ) (hD : 1 < D) (hs : 0 < s) :
    0 ≤ budget D s := by
  have hl : 0 < log D := log_pos hD
  unfold budget
  positivity

/-- Both real quantities require nonnegativity before their caps can be
squared. Actual tuple lengths and Euler ratios satisfy these conditions. -/
theorem normalization_le (D s L R : ℝ) (hD : 1 < D) (hs : 0 < s)
    (hL0 : 0 ≤ L) (hL : L ≤ 5/(4*s^2))
    (hR0 : 0 ≤ R) (hR : R ≤ 2/s^2) :
    L^2*eta D s*R^2 ≤ budget D s := by
  have hη := eta_nonneg D s hD hs
  have hL2 : L^2 ≤ (5/(4*s^2))^2 := pow_le_pow_left₀ hL0 hL 2
  have hR2 : R^2 ≤ (2/s^2)^2 := pow_le_pow_left₀ hR0 hR 2
  have hs0 : s ≠ 0 := hs.ne'
  have hl0 : log D ≠ 0 := (log_pos hD).ne'
  calc
    _ ≤ (5/(4*s^2))^2*eta D s*R^2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hL2 hη) (sq_nonneg R)
    _ ≤ (5/(4*s^2))^2*eta D s*(2/s^2)^2 :=
      mul_le_mul_of_nonneg_left hR2 (by positivity)
    _ = budget D s := by
      unfold eta budget
      field_simp
      ring

theorem cutoff_normalization_le (D s R : ℝ) (hD : 1 < D) (hs : 0 < s)
    (hsHalf : s ≤ 1/2) (hR0 : 0 ≤ R) (hR : R ≤ 2/s^2) :
    (SieveBoxLength.cutoff s : ℝ)^2*eta D s*R^2 ≤ budget D s :=
  normalization_le D s _ R hD hs (Nat.cast_nonneg _)
    (SieveBoundaryBudget.cutoff_le s hs hsHalf) hR0 hR

theorem eventually_budget_le (ε s : ℝ) (hε : 0 < ε) (hs : 0 < s)
    (hsmall : (25/4)*s ≤ ε/2) :
    ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D : ℝ, D₀ ≤ D → budget D s ≤ ε := by
  have hs10 : 0 < s^10 := pow_pos hs 10
  let D₀ := exp (125/(ε*s^10))
  have hD₀ : 1 < D₀ := by
    dsimp [D₀]
    exact one_lt_exp_iff.mpr (by positivity)
  refine ⟨D₀, hD₀, ?_⟩
  intro D hD
  have hlD : 0 < log D := log_pos (hD₀.trans_le hD)
  have hlog : 125/(ε*s^10) ≤ log D := by
    have hh := log_le_log (exp_pos (125/(ε*s^10))) hD
    simpa only [D₀, log_exp] using hh
  have hm : 125 ≤ log D*(ε*s^10) :=
    (div_le_iff₀ (mul_pos hε hs10)).mp hlog
  have htail : (125/2)/(s^10*log D) ≤ ε/2 := by
    apply (div_le_iff₀ (mul_pos hs10 hlD)).mpr
    nlinarith
  unfold budget
  linarith

/-- Choose the small parameter first and then a level threshold for each
fixed parameter. The upper prime cutoff does not enter this threshold. -/
theorem uniformly_small_budget (ε : ℝ) (hε : 0 < ε) :
    ∃ s₀ : ℝ, 0 < s₀ ∧ s₀ ≤ 1/2 ∧ ∀ s : ℝ, 0 < s → s ≤ s₀ →
      ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D : ℝ, D₀ ≤ D → budget D s ≤ ε := by
  refine ⟨min (1/2) (2*ε/25), lt_min (by norm_num) (by positivity),
    min_le_left _ _, ?_⟩
  intro s hs hss
  apply eventually_budget_le ε s hε hs
  have hh := hss.trans (min_le_right (1/2) (2*ε/25))
  nlinarith

theorem euler_amplification (D s z : ℝ) (hD : 1 < D) (hs : 0 < s)
    (hsHalf : s ≤ 1/2) (hu : D^(s^2) ≤ z) (hz : z ≤ D)
    (h2 : 2 ≤ D^(s^2))
    (hK : PrimeEulerDimensionOne.errorConstant ≤ log (D^(s^2))) :
    primeEuler (D^(s^2)) *
      ((SieveBoxLength.cutoff s : ℝ)^2*eta D s*SieveBoundaryEuler.subsetProduct D s z)
      ≤ budget D s * primeEuler z := by
  let R := primeEuler (D^(s^2))/primeEuler z
  have hR0 : 0 ≤ R := SieveEulerRatio.ratio_nonneg D s z
  have hR : R ≤ 2/s^2 := SieveNormalizedStoppingLoss.euler_ratio_le D s z hD hs hu hz h2 hK
  have hη := eta_nonneg D s hD hs
  have hV : 0 < primeEuler z := SieveEulerRatio.euler_pos z
  have hnorm := cutoff_normalization_le D s R hD hs hsHalf hR0 hR
  calc
    _ ≤ primeEuler (D^(s^2)) * ((SieveBoxLength.cutoff s : ℝ)^2*eta D s*R) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (SieveBoundaryEuler.subsetProduct_le_ratio D s z hu)
          (by positivity)) (SieveEulerRatio.euler_pos _).le
    _ = ((SieveBoxLength.cutoff s : ℝ)^2*eta D s*R^2)*primeEuler z := by
      dsimp [R]
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hnorm hV.le

theorem uniformly_small_amplification (ε : ℝ) (hε : 0 < ε) :
    ∃ s₀ : ℝ, 0 < s₀ ∧ s₀ ≤ 1/2 ∧ ∀ s : ℝ, 0 < s → s ≤ s₀ →
      ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D : ℝ, D₀ ≤ D → ∀ z : ℝ,
        D^(s^2) ≤ z → z ≤ D →
          primeEuler (D^(s^2)) *
            ((SieveBoxLength.cutoff s : ℝ)^2*eta D s*SieveBoundaryEuler.subsetProduct D s z)
            ≤ ε*primeEuler z := by
  obtain ⟨s₀, hs₀, hsHalf, hb⟩ := uniformly_small_budget ε hε
  refine ⟨s₀, hs₀, hsHalf, ?_⟩
  intro s hs hss
  obtain ⟨DB, hDB, hbudget⟩ := hb s hs hss
  obtain ⟨DE, _, heuler⟩ := SieveBoundaryEuler.eventually_euler_inputs s hs
  refine ⟨max DB DE, hDB.trans_le (le_max_left _ _), ?_⟩
  intro D hD z hu hz
  have hD1 : 1 < D := hDB.trans_le ((le_max_left _ _).trans hD)
  obtain ⟨h2, hK⟩ := heuler D ((le_max_right _ _).trans hD)
  exact (euler_amplification D s z hD1 hs (hss.trans hsHalf) hu hz h2 hK).trans
    (mul_le_mul_of_nonneg_right (hbudget D ((le_max_left _ _).trans hD))
      (SieveEulerRatio.euler_pos z).le)

run_cmd do
  for decl in [``eta_nonneg, ``budget_nonneg, ``normalization_le,
    ``cutoff_normalization_le, ``eventually_budget_le, ``uniformly_small_budget,
    ``euler_amplification, ``uniformly_small_amplification] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "REPEATED-BAND BUDGET AND ACTUAL EULER AMPLIFICATION PASSED"

end SieveRepeatedBandBudget
end
