import ShortSingletonFourier
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.NumberTheory.Harmonic.Bounds

/-! Harmonic absolute-coefficient control for the exact prefix expansion. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open scoped BigOperators

namespace ShortSingletonFourier

theorem character_norm (Q : ℕ) (k : ZMod (2*Q+1)) :
    ‖ZMod.stdAddChar k‖ = 1 := by
  simp [ZMod.stdAddChar_apply]

theorem character_pow (Q : ℕ) (k : ZMod (2*Q+1)) (r : ℕ) :
    (ZMod.stdAddChar (-k))^r = ZMod.stdAddChar (-(k*(r : ZMod (2*Q+1)))) := by
  rw [← AddChar.map_nsmul_eq_pow]
  congr 1
  simp [nsmul_eq_mul, mul_comm]

theorem coefficient_mul (Q : ℕ) (k : ZMod (2*Q+1)) :
    coefficient Q k * (1-ZMod.stdAddChar (-k)) =
      ((2*Q+1 : ℕ) : ℂ)⁻¹ *
        (1-ZMod.stdAddChar (-(k*((Q+1 : ℕ) : ZMod (2*Q+1))))) := by
  have hg := geom_sum_mul_neg (ZMod.stdAddChar (-k)) (Q+1)
  simp_rw [character_pow] at hg
  unfold coefficient
  rw [mul_assoc, hg]

theorem coefficient_product_norm_le (Q : ℕ) (k : ZMod (2*Q+1)) :
    ‖coefficient Q k‖ * ‖1-ZMod.stdAddChar (-k)‖ ≤ 2 / (2*Q+1 : ℕ) := by
  rw [← norm_mul, coefficient_mul, norm_mul, norm_inv, Complex.norm_natCast]
  have hn := norm_sub_le (1 : ℂ)
    (ZMod.stdAddChar (-(k*((Q+1 : ℕ) : ZMod (2*Q+1)))))
  rw [norm_one, character_norm] at hn
  calc
    _ ≤ ((2*Q+1 : ℕ) : ℝ)⁻¹ * (1+1) :=
      mul_le_mul_of_nonneg_left hn (by positivity)
    _ = _ := by ring

theorem coefficient_conj (Q : ℕ) (k : ZMod (2*Q+1)) :
    coefficient Q (-k) = starRingEnd ℂ (coefficient Q k) := by
  simp only [coefficient, map_mul, map_inv₀, map_natCast, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  rw [show -((-k)*(r : ZMod (2*Q+1))) = -(-(k*(r : ZMod (2*Q+1)))) by ring]
  exact AddChar.map_neg_eq_conj _ _

theorem coefficient_norm_neg (Q : ℕ) (k : ZMod (2*Q+1)) :
    ‖coefficient Q (-k)‖ = ‖coefficient Q k‖ := by
  rw [coefficient_conj, Complex.norm_conj]

theorem coefficient_zero (Q : ℕ) :
    coefficient Q 0 = ((Q+1 : ℕ) : ℂ) / ((2*Q+1 : ℕ) : ℂ) := by
  simp [coefficient, div_eq_mul_inv, mul_comm]

theorem coefficient_zero_norm_le (Q : ℕ) : ‖coefficient Q 0‖ ≤ 1 := by
  rw [coefficient_zero, norm_div, Complex.norm_natCast, Complex.norm_natCast]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < (2*Q+1 : ℕ))).mpr
  push_cast
  nlinarith

theorem character_exp (Q : ℕ) (k : ZMod (2*Q+1)) :
    ZMod.stdAddChar k = Complex.exp
      (Complex.I * ((2*Real.pi*(k.val:ℝ)/((2*Q+1 : ℕ):ℝ) : ℝ) : ℂ)) := by
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply]
  congr 1
  push_cast
  ring

theorem character_gap (Q : ℕ) (k : ZMod (2*Q+1)) (hk : k.val ≤ Q) :
    4*(k.val:ℝ)/((2*Q+1 : ℕ):ℝ) ≤ ‖1-ZMod.stdAddChar (-k)‖ := by
  have hden : (0 : ℝ) < (2*Q+1 : ℕ) := by positivity
  have hkn : (0 : ℝ) ≤ k.val := Nat.cast_nonneg _
  have hhalf : Real.pi*(k.val:ℝ)/((2*Q+1 : ℕ):ℝ) ≤ Real.pi/2 := by
    apply (div_le_iff₀ hden).mpr
    have h : (2:ℝ)*k.val ≤ (2*Q+1 : ℕ) := by exact_mod_cast (by omega : 2*k.val ≤ 2*Q+1)
    nlinarith [Real.pi_pos]
  have hs := Real.mul_le_sin (by positivity :
      0 ≤ Real.pi*(k.val:ℝ)/((2*Q+1 : ℕ):ℝ)) hhalf
  have hsin : 2*(k.val:ℝ)/((2*Q+1 : ℕ):ℝ) ≤
      Real.sin (Real.pi*(k.val:ℝ)/((2*Q+1 : ℕ):ℝ)) := by
    convert hs using 1; field_simp
  have hneg : ‖1-ZMod.stdAddChar (-k)‖ = ‖1-ZMod.stdAddChar k‖ := by
    rw [AddChar.map_neg_eq_conj]
    simpa using (Complex.norm_conj (1-ZMod.stdAddChar k))
  rw [hneg, norm_sub_rev, character_exp, Complex.norm_exp_I_mul_ofReal_sub_one]
  have hang : (2*Real.pi*(k.val:ℝ)/((2*Q+1 : ℕ):ℝ))/2 =
      Real.pi*(k.val:ℝ)/((2*Q+1 : ℕ):ℝ) := by ring
  rw [hang]
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0:ℝ)<2)]
  have hab := le_abs_self (Real.sin (Real.pi*(k.val:ℝ)/((2*Q+1 : ℕ):ℝ)))
  calc
    _ = 2*(2*(k.val:ℝ)/((2*Q+1 : ℕ):ℝ)) := by ring
    _ ≤ 2*Real.sin (Real.pi*(k.val:ℝ)/((2*Q+1 : ℕ):ℝ)) :=
      mul_le_mul_of_nonneg_left hsin (by norm_num)
    _ ≤ _ := mul_le_mul_of_nonneg_left hab (by norm_num)

theorem coefficient_small_mode_le (Q : ℕ) (k : ZMod (2*Q+1))
    (hk0 : 0 < k.val) (hk : k.val ≤ Q) :
    ‖coefficient Q k‖ ≤ 1/(2*(k.val:ℝ)) := by
  have hden : (0 : ℝ) < (2*Q+1 : ℕ) := by positivity
  have hkp : (0 : ℝ) < k.val := by exact_mod_cast hk0
  have hprod := coefficient_product_norm_le Q k
  have hgap := character_gap Q k hk
  have hmul := mul_le_mul_of_nonneg_left hgap (norm_nonneg (coefficient Q k))
  apply (le_div_iff₀ (by positivity : 0 < 2*(k.val:ℝ))).mpr
  have h := hmul.trans hprod
  have hh : (‖coefficient Q k‖ * (4*(k.val:ℝ))) / ((2*Q+1 : ℕ):ℝ) ≤
      2 / ((2*Q+1 : ℕ):ℝ) := by convert h using 1; ring
  have hh' := (div_le_div_iff_of_pos_right hden).mp hh
  nlinarith

run_cmd do
  for decl in [``character_norm, ``character_pow, ``coefficient_mul,
      ``coefficient_product_norm_le, ``coefficient_conj, ``coefficient_norm_neg,
      ``coefficient_zero, ``coefficient_zero_norm_le, ``character_exp,
      ``character_gap, ``coefficient_small_mode_le] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "FINITE FOURIER COEFFICIENT POINTWISE BOUNDS PASSED"

end ShortSingletonFourier
