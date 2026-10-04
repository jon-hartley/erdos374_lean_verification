import Item1PrimeMiddleSymmetry

/-! The arithmetic input below is EXPLICIT AND UNPROVED here.
It is a fixed dyadic high-frequency estimate, not the source mean and not an axiom.
The PNT fills every fixed logarithmic gap, so the ACTUAL source cutoff can be
fixed at (log X)^1024 independently of the input's lower-height exponent A.
This bridge is not a proof of the polynomial-height estimate itself. -/
set_option autoImplicit false
set_option maxHeartbeats 24000000
noncomputable section
open Filter Set
namespace Item1PolynomialCapBridge
open Item1ExactFirstBlock Item1LogarithmicFirstCap Item1PrimeMiddleSymmetry
open Item1SourceLocalArithmetic Item1PrimeLowSpectrum SourceLiteralMoments
open SourceLiteralMiddle PositiveInteriorModel PositiveInteriorCells

/-- Outstanding standard arithmetic input. Only the positive frequency side,
full literal [N,2N) block, fixed log saving, and cubic upper height are required. -/
def DyadicHighInput : Prop :=
  ∃ (A : ℕ) (C : ℝ) (N0 : ℕ), 0<C ∧ 3≤N0 ∧
    ∀ N : ℕ, N0≤N → ∀ t : ℝ, 0<t →
      (Real.log (N:ℝ))^A≤t → t≤(N:ℝ)^3 →
      ‖block N t‖≤C/(Real.log (N:ℝ))^1024

theorem first_log_bounds (X : ℝ) (j : ℕ×ℕ) (hX : 1<X)
    (hj : j∈boxes (mesh X)) :
    (447/1400:ℝ)*Real.log X≤Real.log (((2:ℕ)^j.1:ℕ):ℝ) ∧
      Real.log (((2:ℕ)^j.1:ℕ):ℝ)≤Real.log X := by
  have hh := SourceFractionalGeometryStrong.source_triangle X hX j hj
  have hid := ideal_log X j hX (0:Fin 3)
  have hl : 0≤Real.log X := (Real.log_pos hX).le
  have hid' : Real.log (((2:ℕ)^j.1:ℕ):ℝ)=
      ((j.1:ℝ)*mesh X)*Real.log X := by
    simpa [ideal,exponent,scale] using hid
  rw [hid']
  constructor
  · exact mul_le_mul_of_nonneg_right hh.1 hl
  · have hu := mul_le_mul_of_nonneg_right hh.2.1 hl
    nlinarith

theorem first_cubic_height (X : ℝ) (j : ℕ×ℕ) (hX : 1<X)
    (hj : j∈boxes (mesh X)) :
    height X≤((((2:ℕ)^j.1:ℕ):ℝ))^3 := by
  have hP : (0:ℝ)<(((2:ℕ)^j.1:ℕ):ℝ) := by positivity
  have hX0 : 0<X := by linarith
  have hbounds := first_log_bounds X j hX hj
  apply (Real.log_le_log_iff (Real.rpow_pos_of_pos hX0 _) (pow_pos hP 3)).mp
  rw [Real.log_rpow hX0,Real.log_pow]
  have hl : 0≤Real.log X := (Real.log_pos hX).le
  nlinarith [hbounds.1]

/-- The moving-cell cap, CONDITIONAL on the displayed standard arithmetic input.
No fixed numeric value for the external exponent A or its threshold is assumed. -/
theorem fixed_cutoff_positive_cap (hinput : DyadicHighInput) :
    ∀ᶠ X : ℝ in atTop, PositiveFirstCap X 1024 := by
  obtain ⟨A,C,N0,hC,hN0,hbound⟩ := hinput
  let D : ℕ := max A 1024
  have hlocal := eventually_logarithmic_first_cap D
  have hbad := eventually_badMass_weighted 1023 (1/2) (by norm_num)
  have hlog := Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1000000:ℝ))
  have hcutN := Real.tendsto_log_atTop.eventually
    (eventually_ge_atTop (4*((N0:ℝ)+1)))
  have hcutC := Real.tendsto_log_atTop.eventually
    (eventually_ge_atTop (2*C*(4:ℝ)^1024))
  filter_upwards [hlocal,hbad,hlog,hcutN,hcutC,eventually_ge_atTop (2:ℝ)]
    with X hlocal hb hl hNX hCX hX
  intro j hj t ht
  let ell := Real.log X
  let N : ℕ := 2^j.1
  have he : 0<ell := by dsimp [ell]; linarith only [hl]
  have he1 : 1≤ell := by dsimp [ell]; linarith only [hl]
  have ht0 : 0<t := (pow_pos he 1024).trans_le ht.1
  have htl : ell^1024≤|t| := by
    simpa only [lowCut,abs_of_pos ht0,ell] using ht.1
  by_cases hsmall : t≤ell^D
  · exact hlocal j hj t htl (by simpa only [abs_of_pos ht0] using hsmall)
  · have hlarge : ell^D<t := lt_of_not_ge hsmall
    have hlogs := first_log_bounds X j (by linarith only [hX]) hj
    have hNl : ell/4≤Real.log (N:ℝ) := by
      dsimp [N,ell]
      have hl0 : 0≤Real.log X := by linarith only [hl]
      nlinarith only [hlogs.1, hl0]
    have hNh : Real.log (N:ℝ)≤ell := hlogs.2
    have hNp : (0:ℝ)<N := by dsimp [N]; positivity
    have hlogN : 0<Real.log (N:ℝ) := (div_pos he (by norm_num : (0:ℝ)<4)).trans_le hNl
    have hN0p : (0:ℝ)<N0 := by exact_mod_cast (show 0<N0 by omega)
    have hN0log := Real.log_le_sub_one_of_pos hN0p
    have hNN0 : N0≤N := by
      have hh : (N0:ℝ)≤N := (Real.log_le_log_iff hN0p hNp).mp (by
        dsimp [ell] at hNl
        linarith only [hNl, hNX, hN0log])
      exact_mod_cast hh
    have hlower : (Real.log (N:ℝ))^A≤t := by
      have h1 := pow_le_pow_left₀ hlogN.le hNh A
      have h2 : ell^A≤ell^D := pow_le_pow_right₀ he1 (le_max_left A 1024)
      exact h1.trans (h2.trans hlarge.le)
    have hupper : t≤(N:ℝ)^3 := ht.2.trans
      (first_cubic_height X j (by linarith only [hX]) hj)
    have hfull := hbound N hNN0 t ht0 hlower hupper
    have hpow : (ell/4)^1024≤(Real.log (N:ℝ))^1024 :=
      pow_le_pow_left₀ (by positivity) hNl 1024
    have hconvert : C/(Real.log (N:ℝ))^1024≤C*(4:ℝ)^1024/ell^1024 := by
      have hh := div_le_div_of_nonneg_left hC.le (by positivity : 0<(ell/4)^1024) hpow
      have hid : C/(ell/4)^1024=C*(4:ℝ)^1024/ell^1024 := by
        rw [div_pow, div_div_eq_mul_div]
      exact hh.trans_eq hid
    have hfullsmall : ‖factor X j 0 t‖≤1/(2*ell^1023) := by
      rw [first_factor_eq]
      apply (hfull.trans hconvert).trans
      apply (div_le_div_iff₀ (pow_pos he 1024) (by positivity : 0<2*ell^1023)).mpr
      have hmul := mul_le_mul_of_nonneg_right hCX (pow_nonneg he.le 1023)
      calc
        C*4^1024*(2*ell^1023) = (2*C*4^1024)*ell^1023 := by
          generalize (4:ℝ)^1024 = a
          generalize ell^1023 = b
          ac_rfl
        _ ≤ ell*ell^1023 := hmul
        _ = 1*ell^1024 := by rw [one_mul, pow_succ]; exact mul_comm _ _
    have hb1 : badMass X j 0≤1/(2*ell^1023) := by
      have hp : ell^1023≤(1+ell)^1023 :=
        pow_le_pow_left₀ he.le (le_add_of_nonneg_left (by norm_num)) _
      have hmul := mul_le_mul_of_nonneg_left hp (badMass_nonneg X j 0)
      have hh : badMass X j 0*ell^1023≤1/2 := hmul.trans (hb j hj 0)
      apply (le_div_iff₀ (by positivity : 0<2*ell^1023)).mpr
      calc
        badMass X j 0*(2*ell^1023) = 2*(badMass X j 0*ell^1023) := by
          generalize ell^1023 = b
          ac_rfl
        _ ≤ 2*(1/2) := mul_le_mul_of_nonneg_left hh (by norm_num)
        _ = 1 := by norm_num
    have hpr := (prime_norm_le_full_bad X j t).trans (add_le_add hfullsmall hb1)
    rw [normalized_norm X j t he]
    have hh := div_le_div_of_nonneg_right hpr he.le
    have hid : (1/(2*ell^1023)+1/(2*ell^1023))/ell=1/ell^1024 := by
      rw [pow_succ]
      have hq : 0<ell^1023 := pow_pos he _
      generalize ell^1023 = q at hq ⊢
      field_simp [hq.ne', he.ne'] <;> ring
    exact hh.trans_eq hid

theorem fixed_cutoff_two_sided_cap (hinput : DyadicHighInput) :
    ∀ᶠ X : ℝ in atTop, TwoSidedFirstCap X 1024 := by
  filter_upwards [fixed_cutoff_positive_cap hinput] with X hX
  exact two_sided_cap_of_positive X 1024 hX

end Item1PolynomialCapBridge

-- ROOT SOURCE RECURSIVE AUDIT: exact original declarations.
run_cmd do
  for target in [
    ``Item1PolynomialCapBridge.first_log_bounds,
    ``Item1PolynomialCapBridge.first_cubic_height,
    ``Item1PolynomialCapBridge.fixed_cutoff_positive_cap,
    ``Item1PolynomialCapBridge.fixed_cutoff_two_sided_cap] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "Item1PolynomialCapBridge: 4 original theorem guards passed."
