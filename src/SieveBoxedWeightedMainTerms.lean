import SieveCappedUpperMainTerms
import SieveUpperBoxApproximation

/-! Actual weighted boxed upper main terms at the source's varying cutoffs.
The fourth cutoff is capped at its outer prime. Frozen dyadic weights and
all signed arithmetic remainders remain separate from this main-term bound. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open Real Filter
open scoped BigOperators Topology
namespace SieveBoxedWeightedMainTerms
open SieveWeightedScalarBudget SieveWeightedCutoffs SieveWeightedMainTerms
open SieveCappedUpperMainTerms (cappedFourth)
open SieveStoppingExpansion

def boxedMass (X s : ℝ) (S : Finset ℕ) (w : ℝ → ℝ) : ℝ :=
  ∑ p ∈ S, (p:ℝ)⁻¹*SieveUpperBoxWindow.mainTerm (level X s/(p:ℝ)) s (w p)

theorem euler_le_fullUpper (T z : ℝ) :
    primeEuler z ≤ SieveFullCutoffTransfer.fullUpper T z := by
  rw [SieveFullCutoffTransfer.fullUpper_eq_mass]
  exact (SieveReciprocalModel.mass_bounds (SieveRosser.cubicGate T) 1 _
    (SieveSmallWeights.primes_nodup z) (SieveSmallWeights.primes_prime z)).2

/-- All boxed-level conditions follow uniformly from the common lower
cutoff and the cubic level inequality. -/
theorem level_geometry (X s p z : ℝ) (hX : 1 < X)
    (hs : 0 ≤ s) (hs1 : s ≤ 1/1000) (hp : 1 ≤ p)
    (hzlo : X^(1/7:ℝ) ≤ z) (hz2 : 2 ≤ z) (hcube : z^3 ≤ level X s/p) :
    X^(3/7:ℝ) ≤ level X s/p ∧ level X s/p ≤ X ∧
      (level X s/p)^(s^2) ≤ z ∧ z ≤ level X s/p := by
  have hX0 : 0 < X := by linarith
  have hp0 : 0 < p := by linarith
  have hlevel : 0 < level X s := rpow_pos_of_pos hX0 _
  have hT0 : 0 ≤ level X s/p := (div_pos hlevel hp0).le
  have hlevX : level X s ≤ X := by
    simpa only [level, rpow_one] using
      (rpow_le_rpow_of_exponent_le hX.le (show 1-3*s ≤ (1:ℝ) by linarith))
  have hTX : level X s/p ≤ X := by
    apply le_trans _ hlevX
    apply (div_le_iff₀ hp0).mpr
    nlinarith [mul_nonneg hlevel.le (show 0 ≤ p-1 by linarith)]
  have hlow : X^(3/7:ℝ) ≤ level X s/p := by
    have hh := (pow_le_pow_left₀ (rpow_pos_of_pos hX0 (1/7:ℝ)).le hzlo 3).trans hcube
    have heq : (X^(1/7:ℝ))^3 = X^(3/7:ℝ) := by
      rw [← rpow_natCast, ← rpow_mul hX0.le]
      norm_num
    rwa [heq] at hh
  have hs2 : s^2 ≤ (1/7:ℝ) := by
    have hh : s^2 ≤ (1/1000:ℝ)^2 := by gcongr
    norm_num at hh
    linarith
  have hsmall : (level X s/p)^(s^2) ≤ z :=
    (rpow_le_rpow hT0 hTX (sq_nonneg s)).trans
      ((rpow_le_rpow_of_exponent_le hX.le hs2).trans hzlo)
  have hzlevel : z ≤ level X s/p := by
    have hh := mul_nonneg (show 0 ≤ z by linarith) (show 0 ≤ z^2-1 by nlinarith)
    nlinarith
  exact ⟨hlow, hTX, hsmall, hzlevel⟩

/-- A proved uniform boxed comparison lifts to any finite weighted family.
The actual Euler lower bound for the ordinary upper selector absorbs the
additive boxing error multiplicatively. -/
theorem boxedMass_le_scaled (X s δ B : ℝ) (S : Finset ℕ) (w : ℝ → ℝ)
    (hX : 1 < X) (hs : 0 ≤ s) (hs1 : s ≤ 1/1000) (hlog : 1000 ≤ log X)
    (hδ : 0 ≤ δ) (hB : B ≤ X^(3/7:ℝ))
    (hbox : ∀ T : ℝ, B ≤ T → ∀ z : ℝ, T^(s^2) ≤ z → z ≤ T →
      SieveUpperBoxWindow.mainTerm T s z ≤ SieveFullCutoffTransfer.fullUpper T z+δ*primeEuler z)
    (hprime : ∀ p ∈ S, p.Prime)
    (hgeometry : ∀ p ∈ S, X^(1/7:ℝ) ≤ w p ∧ (w p)^3 ≤ level X s/(p:ℝ)) :
    boxedMass X s S w ≤ (1+δ)*mass X s S w := by
  unfold boxedMass mass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  have hp1 : (1:ℝ) ≤ (p:ℝ) := by exact_mod_cast (hprime p hp).one_le
  obtain ⟨hlo, _, hsmall, hzt⟩ := level_geometry X s p (w p) hX hs hs1 hp1
    (hgeometry p hp).1 ((two_le_floor_cutoff X hX hlog).trans (hgeometry p hp).1)
    (hgeometry p hp).2
  have hb := hbox _ (hB.trans hlo) _ hsmall hzt
  have hv := mul_le_mul_of_nonneg_left (euler_le_fullUpper (level X s/(p:ℝ)) (w p)) hδ
  have hm : SieveUpperBoxWindow.mainTerm (level X s/(p:ℝ)) s (w p) ≤
      (1+δ)*SieveFullCutoffTransfer.fullUpper (level X s/(p:ℝ)) (w p) := by nlinarith
  have hh := mul_le_mul_of_nonneg_left hm (show 0 ≤ (p:ℝ)⁻¹ by positivity)
  nlinarith

/-- The actual boxed negative terms have a positive uniform main-term gap.
The small parameter is fixed before the level threshold and prime families. -/
theorem eventually_negative_main_terms :
    ∃ s₀ : ℝ, 0 < s₀ ∧ s₀ ≤ 1/1000 ∧ ∀ s : ℝ, 0 < s → s < s₀ →
      ∃ X₀ : ℝ, 1 < X₀ ∧ ∀ X : ℝ, X₀ ≤ X → ∀ S₂ S₃ : Finset ℕ,
      (∀ p ∈ S₂, p.Prime ∧ X^(9/35:ℝ) ≤ (p:ℝ) ∧ (p:ℝ) ≤ sqrt (2*X)) →
      (∀ p ∈ S₃, p.Prime ∧ X^alpha s ≤ (p:ℝ) ∧ (p:ℝ) ≤ X^(9/35:ℝ)) →
      boxedMass X s S₂ (cutoffThree X s)+boxedMass X s S₃ (cappedFourth X s) ≤
        (1-1847/10710000:ℝ)*primeEuler (X^alpha s) := by
  let δ : ℝ := 1847/10710000
  have hδ : 0 < δ := by dsimp [δ]; norm_num
  obtain ⟨sU, A, hsU, hsU1, hA, hu⟩ :=
    SieveCappedUpperMainTerms.eventually_negative_main_terms
  obtain ⟨sB, hsB, _, hb⟩ := SieveUpperBoxApproximation.uniformly_le_fullUpper δ hδ
  refine ⟨min sU sB, lt_min hsU hsB, (min_le_left _ _).trans hsU1, ?_⟩
  intro s hs hss
  have hsU' : s < sU := hss.trans_le (min_le_left _ _)
  have hsB' : s < sB := hss.trans_le (min_le_right _ _)
  have hs1 : s ≤ 1/1000 := hsU'.le.trans hsU1
  obtain ⟨D₀, _, hbox⟩ := hb s hs hsB'
  obtain ⟨B, hB⟩ := eventually_atTop.mp
    ((tendsto_rpow_atTop (by norm_num : (0:ℝ) < 3/7)).eventually_ge_atTop D₀)
  refine ⟨max A (max B (exp 1000)), hA.trans_le (le_max_left _ _), ?_⟩
  intro X hX S₂ S₃ hS₂ hS₃
  have hXA : A ≤ X := (le_max_left _ _).trans hX
  have hX1 : 1 < X := hA.trans_le hXA
  have hXD : D₀ ≤ X^(3/7:ℝ) := hB X ((le_max_left _ _).trans ((le_max_right _ _).trans hX))
  have hlog : 1000 ≤ log X := by
    simpa only [log_exp] using log_le_log (exp_pos (1000:ℝ))
      ((le_max_right _ _).trans ((le_max_right _ _).trans hX))
  have h₂ := boxedMass_le_scaled X s δ D₀ S₂ (cutoffThree X s) hX1 hs.le hs1 hlog
    hδ.le hXD hbox (fun p hp => (hS₂ p hp).1) (fun p hp => by
      have hg := three_geometry X s p hX1 hs.le hs1 hlog (hS₂ p hp).2.1 (hS₂ p hp).2.2
      exact ⟨hg.1, hg.2.2⟩)
  have h₃ := boxedMass_le_scaled X s δ D₀ S₃ (cappedFourth X s) hX1 hs.le hs1 hlog
    hδ.le hXD hbox (fun p hp => (hS₃ p hp).1) (fun p hp => by
      have hg := SieveCappedUpperMainTerms.capped_geometry X s p hX1 hs.le hs1
        (hS₃ p hp).2.1 (hS₃ p hp).2.2
      exact ⟨hg.1, hg.2.2⟩)
  have hraw := hu s X hs.le hsU' hXA S₂ S₃ hS₂ hS₃
  have hscaled := mul_le_mul_of_nonneg_left hraw (show 0 ≤ 1+δ by positivity)
  have hV : 0 ≤ primeEuler (X^alpha s) := (SieveEulerRatio.euler_pos _).le
  have hconstant : (1+δ)*(1-1847/5355000:ℝ) ≤ 1-1847/10710000 := by
    dsimp [δ]
    norm_num
  have hend := mul_le_mul_of_nonneg_right hconstant hV
  calc
    _ ≤ (1+δ)*(mass X s S₂ (cutoffThree X s)+mass X s S₃ (cappedFourth X s)) := by
      simpa only [mul_add] using add_le_add h₂ h₃
    _ ≤ (1+δ)*((1-1847/5355000:ℝ)*primeEuler (X^alpha s)) := hscaled
    _ ≤ _ := by simpa only [mul_assoc] using hend

run_cmd do
  for decl in [``euler_le_fullUpper, ``level_geometry,
      ``boxedMass_le_scaled, ``eventually_negative_main_terms] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ACTUAL WEIGHTED BOXED NEGATIVE MAIN TERMS BELOW V; DYADIC AND REMAINDER TRANSFERS OPEN"
end SieveBoxedWeightedMainTerms
end
