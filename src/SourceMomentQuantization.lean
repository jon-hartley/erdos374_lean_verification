import Mathlib.Tactic

/-!
Finite rational moment orders for the v5 source argument.
STATUS: UNCOMPILED DRAFT. The guards below have not been executed.
This file proves rounding algebra, not an analytic moment estimate.
Rounding UP preserves each length guard. A strengthened 1/1000 surplus
leaves at least 1/2000 after rounding three orders to multiples of 1/1000.
-/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
namespace SourceMomentQuantization

def index (b : ℝ) : ℕ := Nat.ceil (1000*b)
def rounded (b : ℝ) : ℝ := (index b : ℝ)/1000

theorem rounded_bounds (b : ℝ) (hb : 0 ≤ b) :
    b ≤ rounded b ∧ rounded b < b+1/1000 := by
  have hlo : 1000*b ≤ (index b : ℝ) := Nat.le_ceil _
  have hhi : (index b : ℝ) < 1000*b+1 :=
    Nat.ceil_lt_add_one (by positivity : 0 ≤ 1000*b)
  unfold rounded
  constructor <;> linarith

/-- A positive lower bound on both moment orders bounds the reciprocal loss. -/
theorem reciprocal_loss (b c e : ℝ) (hb : 4 ≤ b) (hbc : b ≤ c)
    (he : 0 ≤ e) (hce : c ≤ b+e) : 2/b-e/8 ≤ 2/c := by
  have hbp : 0 < b := by linarith
  have hcp : 0 < c := by linarith
  have hb4 : 0 ≤ b-4 := by linarith
  have hc4 : 0 ≤ c-4 := by linarith
  have hprod : 16 ≤ b*c := by nlinarith [mul_nonneg hb4 hc4]
  have hmul := mul_le_mul_of_nonneg_left hprod he
  apply (le_div_iff₀ hcp).mpr
  apply (mul_le_mul_iff_left₀ hbp).mp
  have hid : ((2/b-e/8)*c)*b = 2*c-e*b*c/8 := by field_simp
  rw [hid]
  nlinarith

theorem rounded_reciprocal (b : ℝ) (hb : 4 ≤ b) :
    2/b-1/8000 ≤ 2/rounded b := by
  have hh := rounded_bounds b (by linarith)
  convert reciprocal_loss b (rounded b) (1/1000) hb hh.1
    (by norm_num) hh.2.le using 1 <;> norm_num

/-- The required three-factor margin survives quantization. -/
theorem surplus_survives (a b c : ℝ) (ha : 4 ≤ a) (hb : 4 ≤ b) (hc : 4 ≤ c)
    (hs : (1001/1000 : ℝ) ≤ 2/a+2/b+2/c) :
    (1601/1600 : ℝ) ≤ 2/rounded a+2/rounded b+2/rounded c := by
  linarith [rounded_reciprocal a ha, rounded_reciprocal b hb,
    rounded_reciprocal c hc]

theorem required_surplus (a b c : ℝ) (ha : 4 ≤ a) (hb : 4 ≤ b) (hc : 4 ≤ c)
    (hs : (1001/1000 : ℝ) ≤ 2/a+2/b+2/c) :
    (2001/2000 : ℝ) ≤ 2/rounded a+2/rounded b+2/rounded c := by
  have hh := surplus_survives a b c ha hb hc hs
  linarith

/-- Only 2001 integer orders occur for any fixed convolution order h. -/
theorem finite_order (h : ℕ) (b : ℝ) (hh : 2 ≤ h)
    (hlo : 2*(h:ℝ) ≤ b) (hhi : b ≤ 2*(h:ℝ)+2) :
    2000*h ≤ index b ∧ index b ≤ 2000*h+2000 ∧
    2*(h:ℝ) ≤ rounded b ∧ rounded b ≤ 2*(h:ℝ)+2 := by
  have hhr : (2:ℝ) ≤ h := by exact_mod_cast hh
  have hb : 0 ≤ b := by linarith
  have hceil := (rounded_bounds b hb).1
  have hmono : index b ≤ Nat.ceil (1000*(2*(h:ℝ)+2)) :=
    Nat.ceil_mono (by linarith)
  have hid : 1000*(2*(h:ℝ)+2) = ((2000*h+2000:ℕ):ℝ) := by push_cast; ring
  rw [hid, Nat.ceil_natCast] at hmono
  have hmonoR : (index b:ℝ) ≤ ((2000*h+2000:ℕ):ℝ) := by exact_mod_cast hmono
  have hilo : (2000*h:ℕ) ≤ index b := by
    have hh' : ((2000*h:ℕ):ℝ) ≤ (index b:ℝ) := by
      dsimp [rounded] at hceil
      push_cast
      linarith
    exact_mod_cast hh'
  refine ⟨hilo,hmono,hlo.trans hceil,?_⟩
  dsimp [rounded]
  push_cast at hmonoR
  linarith

theorem fractional_order_bounds (h : ℕ) (b : ℝ) (hh : 2 ≤ h)
    (hlo : 2*(h:ℝ) ≤ b) (hhi : b ≤ 2*(h:ℝ)+2) :
    2 ≤ rounded b/(h:ℝ) ∧ rounded b/(h:ℝ) ≤ 3 := by
  have hr : (2:ℝ) ≤ h := by exact_mod_cast hh
  have hp : (0:ℝ) < h := by linarith
  have hg := finite_order h b hh hlo hhi
  constructor
  · exact (le_div_iff₀ hp).mpr hg.2.2.1
  · exact (div_le_iff₀ hp).mpr (by linarith [hg.2.2.2])

/-- Increasing the moment order can only improve the power-length guard. -/
theorem length_guard_preserved (x b h nu : ℝ) (hx : 0 ≤ x) (hb : 0 ≤ b)
    (hguard : 4*nu ≤ x*(b+2*h)) :
    4*nu ≤ x*(rounded b+2*h) := by
  have hh := mul_le_mul_of_nonneg_left (rounded_bounds b hb).1 hx
  nlinarith

#print axioms surplus_survives
run_cmd do
  for t in [``rounded_bounds, ``reciprocal_loss, ``rounded_reciprocal,
      ``surplus_survives, ``required_surplus, ``finite_order,
      ``fractional_order_bounds, ``length_guard_preserved] do
    for ax in (← Lean.collectAxioms t) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {t}"
  Lean.logInfo "SOURCE MOMENT QUANTIZATION: VALID ONLY AFTER SUCCESSFUL COMPILATION"
end SourceMomentQuantization
