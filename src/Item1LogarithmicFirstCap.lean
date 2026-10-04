import Item1ExactFirstBlock
import Item1PrimeLowSpectrum

/-! Actual first-factor cap up to EVERY FIXED log-power height.
The PNT proof and proper-power mass bounds are called in the theorem body.
This does not establish the cap at X^(562/625), and is not a replacement for
that remaining analytic theorem. D is fixed before the eventual threshold. -/
set_option autoImplicit false
set_option maxHeartbeats 24000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators
namespace Item1LogarithmicFirstCap
open Item1ExactFirstBlock Item1UniformLogArithmetic Item1SourceLocalArithmetic
open Item1PrimeLowSpectrum SourceLiteralMoments
open PositiveInteriorModel PositiveInteriorCells

def normalizedFirst (X : ℝ) (j : ℕ×ℕ) (t : ℝ) : ℂ :=
  primeFactor X j 0 t/(Real.log X:ℂ)

theorem first_factor_eq (X : ℝ) (j : ℕ×ℕ) (t : ℝ) :
    factor X j 0 t=block (2^j.1) t := rfl

theorem prime_norm_le_full_bad (X : ℝ) (j : ℕ×ℕ) (t : ℝ) :
    ‖primeFactor X j 0 t‖≤‖factor X j 0 t‖+badMass X j 0 := by
  have he : primeFactor X j 0 t=factor X j 0 t-badFactor X j 0 t := by
    rw [factor_partition]
    ring
  rw [he]
  exact (norm_sub_le _ _).trans (add_le_add le_rfl (bad_norm_le_mass X j 0 t))

theorem normalized_norm (X : ℝ) (j : ℕ×ℕ) (t : ℝ) (hlog : 0<Real.log X) :
    ‖normalizedFirst X j t‖=‖primeFactor X j 0 t‖/Real.log X := by
  rw [normalizedFirst,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hlog]

/-- Three explicitly allocated scalar errors, before the final division by ell. -/
theorem logarithmic_cap_scalar (ell u : ℝ) (D : ℕ)
    (hell : 4≤ell) (hu0 : ell^1024≤u) (hu1 : u≤ell^D) :
    (2/u + 4*(1/(32*(1+ell)^(D+1023)))*(1+u)
      + 1/(4*(1+ell)^1023))/ell ≤ 1/ell^1024 := by
  have he : 0<ell := by linarith only [hell]
  have hu : 0<u := (pow_pos he 1024).trans_le hu0
  let q := ell^1023
  let W := (1+ell)^(D+1023)
  have hq : 0<q := by dsimp [q]; positivity
  have hW : 0<W := by dsimp [W]; positivity
  have hd : 1≤ell^D := by
    simpa only [one_pow] using pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1)
      (show 1≤ell by linarith only [hell]) D
  have hp : ell^1024=q*ell := by dsimp [q]; rw [pow_succ]
  have h4q : 4*q≤u := by
    calc
      4*q = q*4 := mul_comm _ _
      _ ≤ q*ell := mul_le_mul_of_nonneg_left hell hq.le
      _ = ell^1024 := hp.symm
      _ ≤ u := hu0
  have href : 2/u≤1/(2*q) := by
    apply (div_le_div_iff₀ hu (by positivity : 0<2*q)).mpr
    calc
      2*(2*q) = 4*q := by ring
      _ ≤ u := h4q
      _ = 1*u := (one_mul _).symm
  have hpower : ell^D*q≤W := by
    dsimp [q,W]
    rw [←pow_add]
    exact pow_le_pow_left₀ he.le (le_add_of_nonneg_left (by norm_num)) _
  have hnum : 1+u≤2*ell^D := by simpa only [two_mul] using add_le_add hd hu1
  have herr : 4*(1/(32*W))*(1+u)≤1/(4*q) := by
    have hid : 4*(1/(32*W))*(1+u)=(1+u)/(8*W) := by
      generalize W = w at hW ⊢
      field_simp [hW.ne'] <;> ring
    rw [hid]
    apply (div_le_div_iff₀ (by positivity : 0<8*W) (by positivity : 0<4*q)).mpr
    have hh := mul_le_mul_of_nonneg_right hnum hq.le
    calc
      (1+u)*(4*q) = 4*((1+u)*q) := by ring
      _ ≤ 4*((2*ell^D)*q) := mul_le_mul_of_nonneg_left hh (by norm_num)
      _ = 8*(ell^D*q) := by ring
      _ ≤ 8*W := mul_le_mul_of_nonneg_left hpower (by norm_num)
      _ = 1*(8*W) := (one_mul _).symm
  have hqL : q≤(1+ell)^1023 :=
    pow_le_pow_left₀ he.le (le_add_of_nonneg_left (by norm_num)) _
  have hbad : 1/(4*(1+ell)^1023)≤1/(4*q) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    exact mul_le_mul_of_nonneg_left hqL (by norm_num)
  have hsum : 2/u+4*(1/(32*W))*(1+u)+1/(4*(1+ell)^1023)≤1/q := by
    have hid : 1/(2*q)+1/(4*q)+1/(4*q)=1/q := by
      generalize q = v at hq ⊢
      field_simp [hq.ne'] <;> ring
    exact (add_le_add (add_le_add href herr) hbad).trans_eq hid
  have hfinal := div_le_div_of_nonneg_right hsum he.le
  have hid : (1/q)/ell=1/ell^1024 := by
    rw [hp]
    exact div_div _ _ _
  simpa only [W,hid] using hfinal

/-- The shifted reference interval begins above the common PNT threshold.
It contains exactly the same integer support as [P,2P). -/
theorem first_left_above_root (X : ℝ) (j : ℕ×ℕ)
    (hX : 2≤X) (hlog : 1000000≤Real.log X) (hj : j∈boxes (mesh X)) :
    X^((1:ℝ)/7)≤left (2^j.1) := by
  have hi := large_ideal X j (by linarith) hlog hj (0:Fin 3)
  have hr := ideal_eighth_lower X j 0 hX hlog hj
  have hP : ideal X j 0=((2^j.1:ℕ):ℝ) := by simp [ideal,scale]
  rw [hP] at hi hr
  apply hr.trans
  dsimp [left]
  linarith [hi.1]

/-- Constructed from the retained PNT proof and elementary proper-power mass.
There is no local psi estimate or prime-cap hypothesis in this theorem type. -/
theorem eventually_logarithmic_first_cap (D : ℕ) :
    ∀ᶠ X : ℝ in atTop, ∀ j∈boxes (mesh X), ∀ t : ℝ,
      (Real.log X)^1024≤|t| → |t|≤(Real.log X)^D →
      ‖normalizedFirst X j t‖≤1/(Real.log X)^1024 := by
  have hpsi := uniform_psi (D+1023) (1/32) (by norm_num)
  have hbad := eventually_badMass_weighted 1023 (1/4) (by norm_num)
  have hlog := Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1000000:ℝ))
  filter_upwards [hpsi,hbad,hlog,eventually_ge_atTop (2:ℝ)] with X hp hb hl hX
  intro j hj t ht0 ht1
  let ell := Real.log X
  let N : ℕ := 2^j.1
  let W := (1+ell)^(D+1023)
  let eps := 1/(32*W)
  have hell : 4≤ell := by dsimp [ell]; linarith
  have hellp : 0<ell := by linarith
  have hN : 1≤N := by change 0<N; dsimp [N]; positivity
  have hW : 0<W := by dsimp [W]; positivity
  have ht : t≠0 := by
    intro hz
    simp only [hz,abs_zero] at ht0
    have hpow : 0<(Real.log X)^1024 := pow_pos hellp _
    linarith
  have hlocal : ∀ u∈Icc (left N) (right N), |Chebyshev.psi u-u|≤eps*u := by
    intro u hu
    have hroot := first_left_above_root X j hX hl hj
    have hh := hp u (hroot.trans hu.1)
    have hdiv := (le_div_iff₀ hW).mpr hh
    apply hdiv.trans_eq
    change (1/32)*u/W=(1/(32*W))*u
    generalize W = w at hW ⊢
    field_simp [hW.ne'] <;> ring
  have hfull := block_norm_of_local_psi N hN t eps (by dsimp [eps]; positivity) ht hlocal
  have hfull' : ‖factor X j 0 t‖≤2/|t|+4*eps*(1+|t|) := by
    simpa only [first_factor_eq,N] using hfull
  have hbad' : badMass X j 0≤1/(4*(1+ell)^1023) := by
    have hh := (le_div_iff₀ (show 0<(1+ell)^1023 by positivity)).mpr (hb j hj 0)
    exact hh.trans_eq (div_div 1 4 ((1+ell)^1023))
  have hpr := (prime_norm_le_full_bad X j t).trans (add_le_add hfull' hbad')
  rw [normalized_norm X j t hellp]
  apply (div_le_div_of_nonneg_right hpr hellp.le).trans
  simpa only [eps,W,ell] using logarithmic_cap_scalar ell |t| D hell ht0 ht1

end Item1LogarithmicFirstCap

-- ROOT SOURCE RECURSIVE AUDIT: exact original declarations.
run_cmd do
  for target in [
    ``Item1LogarithmicFirstCap.first_factor_eq,
    ``Item1LogarithmicFirstCap.prime_norm_le_full_bad,
    ``Item1LogarithmicFirstCap.normalized_norm,
    ``Item1LogarithmicFirstCap.logarithmic_cap_scalar,
    ``Item1LogarithmicFirstCap.first_left_above_root,
    ``Item1LogarithmicFirstCap.eventually_logarithmic_first_cap] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "Item1LogarithmicFirstCap: 6 original theorem guards passed."
