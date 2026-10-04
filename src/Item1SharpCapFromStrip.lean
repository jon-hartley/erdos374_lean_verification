import Item1SharpCapEnvelope

/-!
Connected conditional theorem for the exact finite dyadic Mangoldt
polynomial. The ONLY substantive analytic premise is the genuine PositiveStrip
proposition inherited from the contour package. No cap or contour-budget
hypothesis is accepted. This file does not prove existence of PositiveStrip.
-/
set_option autoImplicit false
set_option maxHeartbeats 24000000
noncomputable section
open Filter
namespace Item1SharpCapFromStrip
open Item1SharpDyadicSmoothing Item1SharpCapEnvelope
open Item1ZetaContourGeometry Item1SmoothCapScalar

/-- A real logarithmic threshold is converted to one natural threshold BEFORE t. -/
theorem nat_log_threshold (L : ℝ) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → 0 < (N:ℝ) ∧ L ≤ Real.log (N:ℝ) := by
  let N₀ : ℕ := Nat.ceil (Real.exp L)+3
  refine ⟨N₀,by dsimp [N₀]; omega,?_⟩
  intro N hN
  have hpos : (0:ℝ)<N := by
    exact_mod_cast (show 0<N by dsimp [N₀] at hN; omega)
  refine ⟨hpos,?_⟩
  have hcut : Real.exp L ≤ (N:ℝ) := by
    have hle : Nat.ceil (Real.exp L) ≤ N := by dsimp [N₀] at hN; omega
    exact (Nat.le_ceil (Real.exp L)).trans (by exact_mod_cast hle)
  simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos L) hcut

/-- Exact sharp cap at every fixed log strength, conditional on the stronger strip.
All thresholds are chosen before the integer scale and the frequency. -/
theorem sharp_cap_of_positive_strip (B : ℕ) (a C T₀ : ℝ)
    (ha : 0<a) (ha1 : a≤1/2) (hC : 0<C) (hT : 4≤T₀)
    (hs : PositiveStrip a C T₀) :
    ∃ N₀ : ℕ, 3≤N₀ ∧ ∀ N : ℕ, N₀≤N → ∀ t : ℝ,
      (Real.log (N:ℝ))^(2*B+6)≤t → t≤(N:ℝ)^3 →
      ‖dyadic N t‖ ≤ 1/(Real.log (N:ℝ))^B := by
  obtain ⟨L₀,hL₀⟩ := (eventually_atTop.1 (eventually_budget_le_one B a C ha hC))
  let L := max L₀ (max 2 (max 8 (2*T₀)))
  obtain ⟨N₀,hN₀,hlog⟩ := nat_log_threshold L
  refine ⟨N₀,hN₀,?_⟩
  intro N hN t htlo hthi
  obtain ⟨hNp,hNL⟩ := hlog N hN
  have hN1 : 1≤N := by omega
  let ell := Real.log (N:ℝ)
  have heL : L≤ell := hNL
  have he0 : L₀≤ell := (le_max_left _ _).trans heL
  have he2 : 2≤ell := (le_max_left _ _).trans ((le_max_right _ _).trans heL)
  have he8 : 8≤ell := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans heL))
  have heT : 2*T₀≤ell := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans heL))
  have hep : 0<ell := by linarith
  have he1 : 1≤ell := by linarith
  have hpower : ell ≤ ell^(2*B+6) := by
    simpa only [pow_one] using pow_le_pow_right₀ he1 (show 1≤2*B+6 by omega)
  have het : ell≤t := hpower.trans htlo
  have ht8 : 8≤t := he8.trans het
  have htT : 2*T₀≤t := heT.trans het
  have htp : 0<t := by linarith
  obtain ⟨hδ,hδ1⟩ := smoothing_range B ell he2
  have hsharp := sharp_envelope N hN1 (smoothing B ell) a C T₀ t he2
    hδ hδ1 ha ha1 hC.le hT ht8 htT hs
  have hRu := height_log_upper (N:ℝ) t hNp he2 htp hthi
  have hR := heightLog_pos t ht8
  have hn := normalized_envelope B ell (N:ℝ) a C (heightLog t) t
    he2 (Real.exp_log hNp).symm ha.le hC.le hR hRu htlo
  have hnorm := (mul_le_mul_of_nonneg_right hsharp (pow_nonneg hep.le B)).trans hn
  have hsmall := hL₀ ell he0
  exact (le_div_iff₀ (pow_pos hep B)).mpr (hnorm.trans hsmall)

/-- The fixed exponent required by the available-source retained-middle branch. -/
theorem sharp_cap_26001 (a C T₀ : ℝ)
    (ha : 0<a) (ha1 : a≤1/2) (hC : 0<C) (hT : 4≤T₀)
    (hs : PositiveStrip a C T₀) :
    ∃ N₀ : ℕ, 3≤N₀ ∧ ∀ N : ℕ, N₀≤N → ∀ t : ℝ,
      (Real.log (N:ℝ))^52008≤t → t≤(N:ℝ)^3 →
      ‖dyadic N t‖ ≤ 1/(Real.log (N:ℝ))^26001 := by
  simpa using sharp_cap_of_positive_strip 26001 a C T₀ ha ha1 hC hT hs

end Item1SharpCapFromStrip

-- ROOT CAP RECURSIVE AUDIT: original declarations only.
run_cmd do
  for target in [
    ``Item1SharpCapFromStrip.nat_log_threshold,
    ``Item1SharpCapFromStrip.sharp_cap_of_positive_strip,
    ``Item1SharpCapFromStrip.sharp_cap_26001] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "Item1SharpCapFromStrip: 3 original theorem guards passed."
