import SieveBoundaryBudget
import SieveThinPrimeInterval
import SieveNormalizedStoppingLoss

/-! The actual squarefree subset mass costs only one Euler ratio. Together
with normalization by V(z), two marked strips have a vanishing budget. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open scoped BigOperators Topology
open Real Set Filter SieveStoppingExpansion

namespace SieveBoundaryEuler

def subsetProduct (D s z : ℝ) : ℝ :=
  ∏ p ∈ SieveBoxedFamily.pool D s z, (1+(p:ℝ)⁻¹)

theorem subsetProduct_nonneg (D s z : ℝ) : 0 ≤ subsetProduct D s z := by
  unfold subsetProduct
  exact Finset.prod_nonneg (fun p _ => by positivity)

theorem subsetProduct_le_ratio (D s z : ℝ) (hu : D^(s^2) ≤ z) :
    subsetProduct D s z ≤ primeEuler (D^(s^2))/primeEuler z := by
  rw [SieveEulerRatio.ratio_eq_product_inverse D s z hu]
  unfold subsetProduct
  apply Finset.prod_le_prod₀
  · intro p hp
    positivity
  · intro p hp
    have hp1 : (1:ℝ) < p := by
      exact_mod_cast ((SieveBoxedFamily.mem_pool D s z p).mp hp).1.one_lt
    have hi : (p:ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp1
    apply (le_div_iff₀ (by linarith : 0 < 1-(p:ℝ)⁻¹)).mpr
    nlinarith [sq_nonneg ((p:ℝ)⁻¹)]

theorem euler_amplification (D s z : ℝ) (hD : 1 < D) (hs : 0 < s)
    (hsHalf : s ≤ 1/2) (hu : D^(s^2) ≤ z) (hz : z ≤ D)
    (h2 : 2 ≤ D^(s^2))
    (hK : PrimeEulerDimensionOne.errorConstant ≤ log (D^(s^2))) :
    primeEuler (D^(s^2)) *
      (2*(SieveBoxLength.cutoff s : ℝ)*SieveThinPrimeInterval.delta D s*subsetProduct D s z)
      ≤ SieveBoundaryBudget.budget D s * primeEuler z := by
  let R := primeEuler (D^(s^2))/primeEuler z
  have hR0 : 0 ≤ R := SieveEulerRatio.ratio_nonneg D s z
  have hR : R ≤ 2/s^2 := SieveNormalizedStoppingLoss.euler_ratio_le D s z hD hs hu hz h2 hK
  have hδ := SieveThinPrimeInterval.delta_nonneg D s hD hs
  have hV : 0 < primeEuler z := SieveEulerRatio.euler_pos z
  have hnorm : 2*(SieveBoxLength.cutoff s : ℝ)*SieveThinPrimeInterval.delta D s*R^2 ≤
      SieveBoundaryBudget.budget D s :=
    SieveBoundaryBudget.cutoff_normalization_le D s R hD hs hsHalf hR0 hR
  calc
    _ ≤ primeEuler (D^(s^2)) *
        (2*(SieveBoxLength.cutoff s : ℝ)*SieveThinPrimeInterval.delta D s*R) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (subsetProduct_le_ratio D s z hu) (by positivity))
        (SieveEulerRatio.euler_pos _).le
    _ = (2*(SieveBoxLength.cutoff s : ℝ)*SieveThinPrimeInterval.delta D s*R^2)*primeEuler z := by
      dsimp [R]
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hnorm hV.le

theorem eventually_euler_inputs (s : ℝ) (hs : 0 < s) :
    ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D : ℝ, D₀ ≤ D →
      2 ≤ D^(s^2) ∧ PrimeEulerDimensionOne.errorConstant ≤ log (D^(s^2)) := by
  have hu : Tendsto (fun D : ℝ => D^(s^2)) atTop atTop :=
    tendsto_rpow_atTop (sq_pos_of_pos hs)
  have hl := Real.tendsto_log_atTop.comp hu
  have he : ∀ᶠ D : ℝ in atTop, 2 ≤ D ∧ 2 ≤ D^(s^2) ∧
      PrimeEulerDimensionOne.errorConstant ≤ log (D^(s^2)) :=
    (eventually_ge_atTop 2).and ((hu.eventually_ge_atTop 2).and
      (hl.eventually_ge_atTop PrimeEulerDimensionOne.errorConstant))
  obtain ⟨D₁, hD₁⟩ := eventually_atTop.1 he
  refine ⟨max 2 D₁, by linarith [le_max_left (2:ℝ) D₁], ?_⟩
  intro D hD
  exact (hD₁ D ((le_max_right _ _).trans hD)).2

theorem uniformly_small_amplification (ε : ℝ) (hε : 0 < ε) :
    ∃ s₀ : ℝ, 0 < s₀ ∧ s₀ ≤ 1/2 ∧ ∀ s : ℝ, 0 < s → s ≤ s₀ →
      ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D : ℝ, D₀ ≤ D → ∀ z : ℝ,
        D^(s^2) ≤ z → z ≤ D →
          primeEuler (D^(s^2)) *
            (2*(SieveBoxLength.cutoff s : ℝ)*SieveThinPrimeInterval.delta D s*subsetProduct D s z)
            ≤ ε*primeEuler z := by
  obtain ⟨s₀, hs₀, hsHalf, hb⟩ := SieveBoundaryBudget.uniformly_small_budget ε hε
  refine ⟨s₀, hs₀, hsHalf, ?_⟩
  intro s hs hss
  obtain ⟨DB, hDB, hbudget⟩ := hb s hs hss
  obtain ⟨DE, hDE, heuler⟩ := eventually_euler_inputs s hs
  refine ⟨max DB DE, hDB.trans_le (le_max_left _ _), ?_⟩
  intro D hD z hu hz
  have hD1 : 1 < D := hDB.trans_le ((le_max_left _ _).trans hD)
  obtain ⟨h2, hK⟩ := heuler D ((le_max_right _ _).trans hD)
  exact (euler_amplification D s z hD1 hs (hss.trans hsHalf) hu hz h2 hK).trans
    (mul_le_mul_of_nonneg_right (hbudget D ((le_max_left _ _).trans hD))
      (SieveEulerRatio.euler_pos z).le)

run_cmd do
  for decl in [``subsetProduct_nonneg, ``subsetProduct_le_ratio, ``euler_amplification,
    ``eventually_euler_inputs, ``uniformly_small_amplification] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ACTUAL EULER AMPLIFICATION OF MARKED STRIP BUDGET PASSED"
end SieveBoundaryEuler
end
