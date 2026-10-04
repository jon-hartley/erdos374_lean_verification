import PositiveInteriorModelClosed
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Actual nonprime-coordinate mass on the new 253-cell geometry.
Generic finite union/square-root proofs are freshly checked here;
no earlier tent-window or v18 geometry object is imported. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open scoped BigOperators
open Filter
namespace PositiveSharpDeletionMass
open PositiveInteriorModel PositiveInteriorCells PositiveInteriorRectangles

abbrev Triple := ℕ × (ℕ × ℕ)
def allPrime (k : Triple) : Prop := k.1.Prime ∧ k.2.1.Prime ∧ k.2.2.Prime
instance (k : Triple) : Decidable (allPrime k) := by unfold allPrime; infer_instance

def rawMass (S : Finset ℕ) : ℝ := ∑ n ∈ S, ArithmeticFunction.vonMangoldt n
def nonprimeMass (S : Finset ℕ) : ℝ :=
  ∑ n ∈ S with ¬n.Prime, ArithmeticFunction.vonMangoldt n
def tripleMass (k : Triple) : ℝ := ArithmeticFunction.vonMangoldt k.1 *
  ArithmeticFunction.vonMangoldt k.2.1 * ArithmeticFunction.vonMangoldt k.2.2
def badTripleMass (S T U : Finset ℕ) : ℝ :=
  ∑ k ∈ (S ×ˢ (T ×ˢ U)).filter (fun k => ¬allPrime k), tripleMass k

theorem rawMass_nonneg (S : Finset ℕ) : 0 ≤ rawMass S := by
  exact Finset.sum_nonneg (fun _ _ => ArithmeticFunction.vonMangoldt_nonneg)
theorem nonprimeMass_nonneg (S : Finset ℕ) : 0 ≤ nonprimeMass S := by
  exact Finset.sum_nonneg (fun _ _ => ArithmeticFunction.vonMangoldt_nonneg)

theorem rawMass_le_psi (a b : ℝ) : rawMass (Finset.Ioc ⌊a⌋₊ ⌊b⌋₊) ≤ Chebyshev.psi b := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn
    have hh := Finset.mem_Ioc.mp hn
    exact Finset.mem_Ioc.mpr ⟨by omega, hh.2⟩
  · intro _ _ _
    exact ArithmeticFunction.vonMangoldt_nonneg

theorem nonprimeMass_le_sqrt (a b : ℝ) (hb : 1 ≤ b) :
    nonprimeMass (Finset.Ioc ⌊a⌋₊ ⌊b⌋₊) ≤ 2*Real.sqrt b*Real.log b := by
  apply le_trans _ (Chebyshev.psi_sub_theta_le hb)
  rw [Chebyshev.psi_sub_theta_eq_sum_not_prime]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn
    obtain ⟨hn, hp⟩ := Finset.mem_filter.mp hn
    have hh := Finset.mem_Ioc.mp hn
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨by omega, hh.2⟩, hp⟩
  · intro _ _ _
    exact ArithmeticFunction.vonMangoldt_nonneg

theorem badTripleMass_union_bound (S T U : Finset ℕ) :
    badTripleMass S T U ≤ nonprimeMass S*rawMass T*rawMass U +
      rawMass S*nonprimeMass T*rawMass U + rawMass S*rawMass T*nonprimeMass U := by
  have hp (k : Triple) : (if ¬allPrime k then tripleMass k else 0) ≤
      (if ¬k.1.Prime then ArithmeticFunction.vonMangoldt k.1 else 0) *
        ArithmeticFunction.vonMangoldt k.2.1*ArithmeticFunction.vonMangoldt k.2.2 +
      ArithmeticFunction.vonMangoldt k.1 *
        (if ¬k.2.1.Prime then ArithmeticFunction.vonMangoldt k.2.1 else 0) *
          ArithmeticFunction.vonMangoldt k.2.2 +
      ArithmeticFunction.vonMangoldt k.1*ArithmeticFunction.vonMangoldt k.2.1 *
        (if ¬k.2.2.Prime then ArithmeticFunction.vonMangoldt k.2.2 else 0) := by
    have ha : 0 ≤ ArithmeticFunction.vonMangoldt k.1 := ArithmeticFunction.vonMangoldt_nonneg
    have hb : 0 ≤ ArithmeticFunction.vonMangoldt k.2.1 := ArithmeticFunction.vonMangoldt_nonneg
    have hc : 0 ≤ ArithmeticFunction.vonMangoldt k.2.2 := ArithmeticFunction.vonMangoldt_nonneg
    by_cases h1 : k.1.Prime <;> by_cases h2 : k.2.1.Prime <;>
      by_cases h3 : k.2.2.Prime <;>
      simp [allPrime, tripleMass, h1, h2, h3] <;> positivity
  unfold badTripleMass
  rw [Finset.sum_filter]
  refine (Finset.sum_le_sum (fun k _ => hp k)).trans_eq ?_
  simp only [Finset.sum_product, Finset.sum_add_distrib,
    rawMass, nonprimeMass, Finset.sum_filter]
  simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
  simp_rw [← Finset.mul_sum, ← Finset.sum_mul]

theorem nonprimeMass_le_ratio (a b Y ell : ℝ) (hb : 1 ≤ b)
    (hY : 0 < Y) (hYb : Y ≤ b) (hell : Real.log b ≤ ell) :
    nonprimeMass (Finset.Ioc ⌊a⌋₊ ⌊b⌋₊) ≤ 2*b*ell/Real.sqrt Y := by
  have hb0 : 0 ≤ b := by linarith
  have hsY := Real.sqrt_pos.2 hY
  have hsB := Real.sqrt_nonneg b
  have hlog : 0 ≤ Real.log b := Real.log_nonneg hb
  have hell0 : 0 ≤ ell := hlog.trans hell
  have hs : Real.sqrt Y ≤ Real.sqrt b := Real.sqrt_le_sqrt hYb
  have hmul : Real.sqrt b*Real.sqrt Y ≤ b := by
    have hh := mul_le_mul_of_nonneg_left hs hsB
    nlinarith [Real.sq_sqrt hb0]
  apply (nonprimeMass_le_sqrt a b hb).trans
  apply (le_div_iff₀ hsY).mpr
  calc
    _ = 2*(Real.sqrt b*Real.sqrt Y)*Real.log b := by ring
    _ ≤ 2*b*Real.log b := by nlinarith
    _ ≤ 2*b*ell := by nlinarith

theorem badTripleMass_interval_bound (a b c d e f Y ell : ℝ)
    (hb : 1 ≤ b) (hd : 1 ≤ d) (hf : 1 ≤ f) (hY : 0 < Y)
    (hYb : Y ≤ b) (hYd : Y ≤ d) (hYf : Y ≤ f)
    (hlb : Real.log b ≤ ell) (hld : Real.log d ≤ ell) (hlf : Real.log f ≤ ell)
    (hpb : Chebyshev.psi b ≤ 2*b) (hpd : Chebyshev.psi d ≤ 2*d)
    (hpf : Chebyshev.psi f ≤ 2*f) :
    badTripleMass (Finset.Ioc ⌊a⌋₊ ⌊b⌋₊) (Finset.Ioc ⌊c⌋₊ ⌊d⌋₊)
      (Finset.Ioc ⌊e⌋₊ ⌊f⌋₊) ≤ 24*(b*d*f)*ell/Real.sqrt Y := by
  have h0 : 0 ≤ ell := (Real.log_nonneg hb).trans hlb
  have hm1 := (rawMass_le_psi a b).trans hpb
  have hm2 := (rawMass_le_psi c d).trans hpd
  have hm3 := (rawMass_le_psi e f).trans hpf
  have hn1 := nonprimeMass_le_ratio a b Y ell hb hY hYb hlb
  have hn2 := nonprimeMass_le_ratio c d Y ell hd hY hYd hld
  have hn3 := nonprimeMass_le_ratio e f Y ell hf hY hYf hlf
  calc
    _ ≤ nonprimeMass (Finset.Ioc ⌊a⌋₊ ⌊b⌋₊)*rawMass (Finset.Ioc ⌊c⌋₊ ⌊d⌋₊)*
          rawMass (Finset.Ioc ⌊e⌋₊ ⌊f⌋₊) +
        rawMass (Finset.Ioc ⌊a⌋₊ ⌊b⌋₊)*nonprimeMass (Finset.Ioc ⌊c⌋₊ ⌊d⌋₊)*
          rawMass (Finset.Ioc ⌊e⌋₊ ⌊f⌋₊) +
        rawMass (Finset.Ioc ⌊a⌋₊ ⌊b⌋₊)*rawMass (Finset.Ioc ⌊c⌋₊ ⌊d⌋₊)*
          nonprimeMass (Finset.Ioc ⌊e⌋₊ ⌊f⌋₊) := badTripleMass_union_bound _ _ _
    _ ≤ (2*b*ell/Real.sqrt Y)*(2*d)*(2*f) +
        (2*b)*(2*d*ell/Real.sqrt Y)*(2*f) +
        (2*b)*(2*d)*(2*f*ell/Real.sqrt Y) := by
      have hmn1 := rawMass_nonneg (Finset.Ioc ⌊a⌋₊ ⌊b⌋₊)
      have hmn2 := rawMass_nonneg (Finset.Ioc ⌊c⌋₊ ⌊d⌋₊)
      have hmn3 := rawMass_nonneg (Finset.Ioc ⌊e⌋₊ ⌊f⌋₊)
      have hnn1 := nonprimeMass_nonneg (Finset.Ioc ⌊a⌋₊ ⌊b⌋₊)
      have hnn2 := nonprimeMass_nonneg (Finset.Ioc ⌊c⌋₊ ⌊d⌋₊)
      have hnn3 := nonprimeMass_nonneg (Finset.Ioc ⌊e⌋₊ ⌊f⌋₊)
      gcongr
    _ = _ := by ring

def shortestScale (X : ℝ) : ℝ := X^((1:ℝ)/6)

def cellBadMass (X : ℝ) (j : ℕ × ℕ) : ℝ :=
  badTripleMass (Finset.Ioc ⌊scale j.1⌋₊ ⌊2*scale j.1⌋₊)
    (Finset.Ioc ⌊scale j.2⌋₊ ⌊2*scale j.2⌋₊)
    (Finset.Ioc ⌊thirdScale X j/8⌋₊ ⌊4*thirdScale X j⌋₊)

theorem cellBadMass_nonneg (X : ℝ) (j : ℕ × ℕ) : 0 ≤ cellBadMass X j := by
  unfold cellBadMass badTripleMass tripleMass
  exact Finset.sum_nonneg (fun _ _ => by positivity)

theorem third_log_identity (X : ℝ) (hX : 1 < X) (j : ℕ × ℕ) :
    Real.log (thirdScale X j)=
      (1-(j.1:ℝ)*mesh X-(j.2:ℝ)*mesh X)*Real.log X := by
  have hp : 0 < scale j.1 := by unfold scale; positivity
  have hr : 0 < scale j.2 := by unfold scale; positivity
  rw [thirdScale, Real.log_div (by linarith : X ≠ 0) (mul_pos hp hr).ne',
    Real.log_mul hp.ne' hr.ne', log_scale_identity X hX, log_scale_identity X hX]
  ring

theorem scales_ge_shortest (X : ℝ) (hX : 1 < X)
    (j : ℕ × ℕ) (hj : j ∈ boxes (mesh X)) :
    shortestScale X ≤ scale j.1 ∧ shortestScale X ≤ scale j.2 ∧
      shortestScale X ≤ thirdScale X j := by
  have hXp : 0 < X := by linarith
  have hl : 0 < Real.log X := Real.log_pos hX
  have hc := component_bounds _ _ (box_interior (mesh X) (mesh_pos X hX) j hj)
  have hs : 0 < shortestScale X := Real.rpow_pos_of_pos hXp _
  have hscale (m : ℕ) (hm : (1/6:ℝ) ≤ (m:ℝ)*mesh X) :
      shortestScale X ≤ scale m := by
    have hp : 0 < scale m := by unfold scale; positivity
    apply (Real.log_le_log_iff hs hp).mp
    rw [shortestScale, Real.log_rpow hXp, log_scale_identity X hX m]
    exact mul_le_mul_of_nonneg_right hm hl.le
  have hp : 0 < scale j.1 := by unfold scale; positivity
  have hr : 0 < scale j.2 := by unfold scale; positivity
  have hL : 0 < thirdScale X j := div_pos hXp (mul_pos hp hr)
  refine ⟨hscale j.1 (by linarith [hc.1]), hscale j.2 (by linarith [hc.2.1]), ?_⟩
  apply (Real.log_le_log_iff hs hL).mp
  rw [shortestScale, Real.log_rpow hXp, third_log_identity X hX j]
  exact mul_le_mul_of_nonneg_right hc.2.2 hl.le

theorem upper_endpoints_le (X : ℝ) (hX : 1 < X) (hm : mesh X ≤ 1/8)
    (j : ℕ × ℕ) (hj : j ∈ boxes (mesh X)) :
    2*scale j.1 ≤ X ∧ 2*scale j.2 ≤ X ∧ 4*thirdScale X j ≤ X := by
  have hXp : 0 < X := by linarith
  have hl : 0 < Real.log X := Real.log_pos hX
  have hc := component_bounds _ _ (box_interior (mesh X) (mesh_pos X hX) j hj)
  have hp : 0 < scale j.1 := by unfold scale; positivity
  have hr : 0 < scale j.2 := by unfold scale; positivity
  have hL : 0 < thirdScale X j := div_pos hXp (mul_pos hp hr)
  have h2 : Real.log (2:ℝ)=mesh X*Real.log X := (mesh_mul_log X hX).symm
  have h4 : Real.log (4:ℝ)=2*Real.log 2 := by
    rw [show (4:ℝ)=(2:ℝ)^2 by norm_num, Real.log_pow]
    norm_num
  have hcoeff₁ : (j.1:ℝ)*mesh X+mesh X ≤ 1 := by linarith [hc.1,hc.2.1,hc.2.2]
  have hcoeff₂ : (j.2:ℝ)*mesh X+mesh X ≤ 1 := by linarith [hc.1,hc.2.1,hc.2.2]
  have hcoeff₃ : 1-(j.1:ℝ)*mesh X-(j.2:ℝ)*mesh X+2*mesh X ≤ 1 := by
    linarith [hc.1,hc.2.1]
  refine ⟨?_,?_,?_⟩
  · apply (Real.log_le_log_iff (by positivity) hXp).mp
    rw [Real.log_mul (by norm_num) hp.ne', log_scale_identity X hX, h2]
    nlinarith [mul_le_mul_of_nonneg_right hcoeff₁ hl.le]
  · apply (Real.log_le_log_iff (by positivity) hXp).mp
    rw [Real.log_mul (by norm_num) hr.ne', log_scale_identity X hX, h2]
    nlinarith [mul_le_mul_of_nonneg_right hcoeff₂ hl.le]
  · apply (Real.log_le_log_iff (by positivity) hXp).mp
    rw [Real.log_mul (by norm_num) hL.ne', third_log_identity X hX, h4, h2]
    nlinarith [mul_le_mul_of_nonneg_right hcoeff₃ hl.le]

theorem upper_endpoints_product (X : ℝ) (j : ℕ × ℕ) :
    (2*scale j.1)*(2*scale j.2)*(4*thirdScale X j)=16*X := by
  have hp : scale j.1 ≠ 0 := by unfold scale; positivity
  have hr : scale j.2 ≠ 0 := by unfold scale; positivity
  unfold thirdScale
  field_simp
  ring

theorem psi_le_twice_eventually : ∀ᶠ x : ℝ in atTop, Chebyshev.psi x ≤ 2*x := by
  filter_upwards [Erdos374.PositiveInteriorMass.psi_error_eventually 1 (by norm_num)] with x hx
  have hh := (abs_le.mp hx).2
  linarith

theorem actual_badTripleMass_bound :
    ∃ X0 : ℝ, 2 ≤ X0 ∧ ∀ X ≥ X0, ∀ j ∈ boxes (mesh X),
      cellBadMass X j ≤ 384*X*Real.log X/Real.sqrt (shortestScale X) := by
  obtain ⟨Y,hY⟩ := eventually_atTop.mp psi_le_twice_eventually
  obtain ⟨B,hB⟩ := eventually_atTop.mp
    ((tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1/6)).eventually_ge_atTop (max 1 Y))
  refine ⟨max 2 (max B (Real.exp (8*Real.log 2))), le_max_left _ _, ?_⟩
  intro X hX j hj
  have hX2 : 2 ≤ X := (le_max_left _ _).trans hX
  have hX1 : 1 < X := by linarith
  have hXB : B ≤ X := (le_max_left _ _).trans ((le_max_right _ _).trans hX)
  have hsmall : max 1 Y ≤ shortestScale X := hB X hXB
  have hlog : 8*Real.log 2 ≤ Real.log X := by
    have hh := Real.log_le_log (Real.exp_pos (8*Real.log 2))
      ((le_max_right _ _).trans ((le_max_right _ _).trans hX))
    simpa only [Real.log_exp] using hh
  have hm : mesh X ≤ 1/8 := by
    unfold mesh
    apply (div_le_iff₀ (Real.log_pos hX1)).mpr
    linarith
  have hs := scales_ge_shortest X hX1 j hj
  have hu := upper_endpoints_le X hX1 hm j hj
  have hp : 1 ≤ scale j.1 := (le_max_left _ _).trans (hsmall.trans hs.1)
  have hr : 1 ≤ scale j.2 := (le_max_left _ _).trans (hsmall.trans hs.2.1)
  have hL : 1 ≤ thirdScale X j := (le_max_left _ _).trans (hsmall.trans hs.2.2)
  have hYp : Y ≤ scale j.1 := (le_max_right _ _).trans (hsmall.trans hs.1)
  have hYr : Y ≤ scale j.2 := (le_max_right _ _).trans (hsmall.trans hs.2.1)
  have hYL : Y ≤ thirdScale X j := (le_max_right _ _).trans (hsmall.trans hs.2.2)
  have hh := badTripleMass_interval_bound (scale j.1) (2*scale j.1)
    (scale j.2) (2*scale j.2) (thirdScale X j/8) (4*thirdScale X j)
    (shortestScale X) (Real.log X) (by linarith) (by linarith) (by linarith)
    (Real.rpow_pos_of_pos (by linarith : 0 < X) _)
    (by linarith [hs.1]) (by linarith [hs.2.1]) (by linarith [hs.2.2])
    (Real.log_le_log (by linarith) hu.1)
    (Real.log_le_log (by linarith) hu.2.1)
    (Real.log_le_log (by linarith) hu.2.2)
    (hY _ (by linarith)) (hY _ (by linarith)) (hY _ (by linarith))
  rw [upper_endpoints_product] at hh
  change badTripleMass _ _ _ ≤ _
  convert hh using 1
  ring

theorem sqrt_shortest (X : ℝ) (hX : 0 ≤ X) :
    Real.sqrt (shortestScale X)=X^((1:ℝ)/12) := by
  rw [Real.sqrt_eq_rpow, shortestScale, ← Real.rpow_mul hX]
  norm_num

run_cmd do
  for decl in [``rawMass_nonneg, ``nonprimeMass_nonneg, ``rawMass_le_psi,
      ``nonprimeMass_le_sqrt, ``badTripleMass_union_bound, ``nonprimeMass_le_ratio,
      ``badTripleMass_interval_bound, ``cellBadMass_nonneg, ``third_log_identity,
      ``scales_ge_shortest, ``upper_endpoints_le, ``upper_endpoints_product,
      ``psi_le_twice_eventually, ``actual_badTripleMass_bound, ``sqrt_shortest] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ACTUAL NEW-CELL PRIME-POWER DELETION MASS: FIFTEEN STANDARD-THREE GUARDS"
end PositiveSharpDeletionMass
end

