import Item1RetainedMomentMiddle
import Item1PolynomialCapBridge

/-! UNCOMPILED. The only unproved arithmetic proposition is named below.
This is a fixed-power specialization of a polynomial-height Mangoldt estimate,
NOT a claimed proof of the Vinogradov--Korobov theorem. The available moment
route uses a stronger fixed logarithmic saving than the unavailable 1024 route.
The cutoff K is chosen once from A before X and the changing cell. LowFrequency
and SourceMerge already allow every such fixed K. The physical source is unchanged.
-/
set_option autoImplicit false
set_option maxHeartbeats 32000000
noncomputable section
open Filter Set
namespace Item1RetainedPolynomialCap
open Item1RetainedMomentMiddle Item1PolynomialCapBridge
open Item1ExactFirstBlock Item1LogarithmicFirstCap Item1PrimeMiddleSymmetry
open Item1SourceLocalArithmetic Item1PrimeLowSpectrum SourceLiteralMoments
open SourceLiteralMiddle PositiveInteriorModel PositiveInteriorCells

/-- UNPROVED HERE. The extra logarithmic power absorbs all fixed scale constants.
Full [N,2N) Mangoldt block, positive frequencies, cubic height; not a source mean. -/
def PolynomialHeightInput : Prop :=
  ∃ (A : ℕ) (C : ℝ) (N0 : ℕ), 0 < C ∧ 3 ≤ N0 ∧
    ∀ N : ℕ, N0 ≤ N → ∀ t : ℝ, 0 < t →
      (Real.log (N:ℝ))^A ≤ t → t ≤ (N:ℝ)^3 →
      ‖block N t‖ ≤ C/(Real.log (N:ℝ))^26001

/-- Explicit scalar conversion between local and global logarithms. -/
theorem high_input_scalar (ell s C : ℝ) (hell : 1 ≤ ell) (hC : 0 ≤ C)
    (hs : ell/4 ≤ s)
    (hlarge : 2*C*(4:ℝ)^26001*(2:ℝ)^26000 ≤ ell) :
    C/s^26001 ≤ 1/(2*(1+ell)^26000) := by
  have he : 0 < ell := by linarith only [hell]
  have hs0 : 0 < s := by linarith only [hs, he]
  have hpow : (ell/4)^26001 ≤ s^26001 :=
    pow_le_pow_left₀ (by positivity) hs _
  have hconvert : C/s^26001 ≤ C*(4:ℝ)^26001/ell^26001 := by
    have hh := div_le_div_of_nonneg_left hC (by positivity : 0 < (ell/4)^26001) hpow
    have hid : C/(ell/4)^26001 = C*(4:ℝ)^26001/ell^26001 := by
      rw [div_pow, div_div_eq_mul_div]
    exact hh.trans_eq hid
  apply hconvert.trans
  apply (div_le_div_iff₀ (pow_pos he _)
    (by positivity : 0 < 2*(1+ell)^26000)).mpr
  have hp : (1+ell)^26000 ≤ (2:ℝ)^26000*ell^26000 := by
    simpa only [mul_pow] using pow_le_pow_left₀
      (show 0 ≤ 1+ell by linarith only [hell]) (show 1+ell ≤ 2*ell by linarith only [hell]) 26000
  have hm := mul_le_mul_of_nonneg_left hp
    (show 0 ≤ 2*C*(4:ℝ)^26001 by positivity)
  have hn := mul_le_mul_of_nonneg_right hlarge (pow_nonneg he.le 26000)
  have hsucc : ell^26001 = ell^26000*ell := pow_succ ell 26000
  generalize (4:ℝ)^26001 = a at *
  generalize (2:ℝ)^26000 = b at *
  generalize ell^26000 = q at *
  generalize (1+ell)^26000 = p at *
  calc
    C*a*(2*p) = (2*C*a)*p := by ring
    _ ≤ (2*C*a)*(b*q) := hm
    _ = (2*C*a*b)*q := by ring
    _ ≤ ell*q := hn
    _ = 1*ell^26001 := by rw [one_mul,hsucc]; exact mul_comm _ _

theorem norm_first_abs (X : ℝ) (j : ℕ×ℕ) (t : ℝ) :
    ‖primeFactor X j 0 |t|‖ = ‖primeFactor X j 0 t‖ := by
  by_cases ht : 0 ≤ t
  · rw [abs_of_nonneg ht]
  · rw [abs_of_neg (lt_of_not_ge ht),primeFactor_neg,Complex.norm_conj]

/-- One fixed K works for all eventual X and all actual cells. -/
theorem eventually_strong_first_cap (hinput : PolynomialHeightInput) :
    ∃ K : ℕ, 20 ≤ K ∧ ∀ᶠ X : ℝ in atTop, StrongFirstCap X K := by
  obtain ⟨A,C,N0,hC,hN0,hbound⟩ := hinput
  let K : ℕ := max A 20
  refine ⟨K,le_max_right A 20,?_⟩
  have hbad := eventually_badMass_weighted 26000 (1/2) (by norm_num)
  have hcutN := Real.tendsto_log_atTop.eventually
    (eventually_ge_atTop (4*((N0:ℝ)+1)))
  have hcutC := Real.tendsto_log_atTop.eventually
    (eventually_ge_atTop (2*C*(4:ℝ)^26001*(2:ℝ)^26000))
  filter_upwards [hbad,hcutN,hcutC,Item1PhysicalDeletion.eventually_geometry]
    with X hb hNX hCX hg
  intro j hj t ht
  let ell := Real.log X
  let N : ℕ := 2^j.1
  have he : 0 < ell := by dsimp [ell]; linarith only [hg.2.1]
  have he1 : 1 ≤ ell := by dsimp [ell]; linarith only [hg.2.1]
  have htlo : ell^K ≤ |t| := ht.2
  have hthi : |t| ≤ height X := abs_le.mpr ht.1
  have ht0 : 0 < |t| := (pow_pos he K).trans_le htlo
  have hlogs := first_log_bounds X j (by linarith only [hg.1]) hj
  have hNl : ell/4 ≤ Real.log (N:ℝ) := by
    dsimp [N,ell]
    have hl0 : 0 ≤ Real.log X := by linarith only [hg.2.1]
    nlinarith only [hlogs.1,hl0]
  have hNh : Real.log (N:ℝ) ≤ ell := hlogs.2
  have hNp : (0:ℝ) < N := by dsimp [N]; positivity
  have hlogN : 0 < Real.log (N:ℝ) := by linarith only [hNl,he]
  have hN0p : (0:ℝ) < N0 := by exact_mod_cast (show 0 < N0 by omega)
  have hN0log := Real.log_le_sub_one_of_pos hN0p
  have hNN0 : N0 ≤ N := by
    have hh : (N0:ℝ) ≤ N := (Real.log_le_log_iff hN0p hNp).mp (by
      dsimp [ell] at hNl
      linarith only [hNX,hNl,hN0log])
    exact_mod_cast hh
  have hlower : (Real.log (N:ℝ))^A ≤ |t| :=
    (pow_le_pow_left₀ hlogN.le hNh A).trans
      ((pow_le_pow_right₀ he1 (le_max_left A 20)).trans htlo)
  have hupper : |t| ≤ (N:ℝ)^3 := hthi.trans
    (first_cubic_height X j (by linarith only [hg.1]) hj)
  have hf := (hbound N hNN0 |t| ht0 hlower hupper).trans
    (high_input_scalar ell (Real.log (N:ℝ)) C he1 hC.le hNl hCX)
  have hfull : ‖factor X j 0 |t|‖ ≤ 1/(2*(1+ell)^26000) := by
    simpa only [first_factor_eq,N] using hf
  have hL : 0 < 1+ell := by linarith only [he]
  have hbm : badMass X j 0 ≤ 1/(2*(1+ell)^26000) := by
    have hh := hb j hj (0:Fin 3)
    apply (le_div_iff₀ (by positivity : 0 < 2*(1+ell)^26000)).mpr
    calc
      badMass X j 0*(2*(1+ell)^26000) =
          2*(badMass X j 0*(1+ell)^26000) := mul_left_comm _ _ _
      _ ≤ 2*(1/2) := mul_le_mul_of_nonneg_left hh (by norm_num)
      _ = 1 := by norm_num
  have hpr := (prime_norm_le_full_bad X j |t|).trans (add_le_add hfull hbm)
  have hid : 1/(2*(1+ell)^26000)+1/(2*(1+ell)^26000) =
      (1+ell)^(-26000:ℝ) := by
    rw [Real.rpow_neg hL.le]
    simp only [Real.rpow_natCast,Real.rpow_ofNat,inv_eq_one_div]
    generalize (1+ell)^26000 = z
    ring
  rw [norm_first_abs] at hpr
  exact hpr.trans_eq hid

end Item1RetainedPolynomialCap

-- ROOT SOURCE RECURSIVE AUDIT: exact original declarations.
run_cmd do
  for target in [
    ``Item1RetainedPolynomialCap.high_input_scalar,
    ``Item1RetainedPolynomialCap.norm_first_abs,
    ``Item1RetainedPolynomialCap.eventually_strong_first_cap] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "Item1RetainedPolynomialCap: 3 original theorem guards passed."
