import Item1ActualTailData
import Item1PhysicalDeletion
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! UNCOMPILED, 2026-10-02. Fixed source width/height, actual tail instantiation,
and elementary scalar decay. No pointwise prime cap or high-tail budget is an
argument of the eventual high-tail theorem. The inherited finite mean square
and countable-tail bodies must still compile in the maintained project. -/
set_option autoImplicit false
set_option maxHeartbeats 32000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators
namespace Item1TailScalarMerge
open Item1ActualTailData Item1PhysicalDeletion Item1SourceLocalArithmetic
open Item1SelectedWindow Item1SelectedFourier
open PositiveInteriorModel PositiveInteriorCells
open PositiveSharpMovingWindow

def width (X : ℝ) : ℝ := X^((101:ℝ)/1000)/2
def height (X : ℝ) : ℝ := X^((562:ℝ)/625)

def highEnergy (X : ℝ) : ℝ :=
  ∑ j∈boxes (mesh X), ∫ t in SourceDyadicTail.outside (height X),
    density X (width X) j (primeTuples X j) t

theorem width_bounds (X : ℝ) (hX : 1≤X) : 0<width X ∧ width X≤X/2 := by
  have hXp : 0<X := by linarith
  constructor
  · unfold width; positivity
  · unfold width
    apply div_le_div_of_nonneg_right _ (by norm_num)
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hX (by norm_num : (101/1000:ℝ)≤1)

theorem height_ge_one (X : ℝ) (hX : 1≤X) : 1≤height X := by
  unfold height
  exact Real.one_le_rpow hX (by norm_num)

theorem eta_eq (X : ℝ) (hX : 0<X) : width X/X=(1/2)*X^((-899:ℝ)/1000) := by
  have hp := Real.rpow_sub hX (101/1000:ℝ) 1
  norm_num only [Real.rpow_one,show (101/1000:ℝ)-1=(-899/1000:ℝ) by norm_num] at hp
  unfold width
  rw [show X^(101/1000:ℝ)/2/X=(1/2)*(X^(101/1000:ℝ)/X) by ring,←hp]
  simp only [neg_div]

theorem eta_sq (X : ℝ) (hX : 0<X) : (width X/X)^2=(1/4)*X^((-899:ℝ)/500) := by
  rw [eta_eq X hX,mul_pow,←Real.rpow_mul_natCast hX.le]
  norm_num

theorem reciprocal_scales (X : ℝ) (hX : 0<X) :
    1/((width X/X)^2*X*height X)=4*X^((-253:ℝ)/2500) ∧
    1/((width X/X)^2*(height X)^2)=4*X^((-1:ℝ)/2500) ∧
    1/((width X/X)^2*(height X)^3)=4*X^((-2249:ℝ)/2500) := by
  have h1 : (width X/X)^2*X*height X=(1/4)*X^((253:ℝ)/2500) := by
    rw [eta_sq X hX]
    unfold height
    calc
      _ = (1/4)*(X^((-899:ℝ)/500)*X^(1:ℝ)*X^((562:ℝ)/625)) := by rw [Real.rpow_one]; ring
      _ = (1/4)*X^((-899:ℝ)/500+1+562/625) := by rw [Real.rpow_add hX,Real.rpow_add hX]
      _ = _ := by norm_num
  have h2 : (width X/X)^2*(height X)^2=(1/4)*X^((1:ℝ)/2500) := by
    rw [eta_sq X hX]
    unfold height
    rw [←Real.rpow_mul_natCast hX.le]
    calc
      _ = (1/4)*(X^((-899:ℝ)/500)*X^((562:ℝ)/625*(2:ℕ))) := by ring
      _ = (1/4)*X^((-899:ℝ)/500+(562:ℝ)/625*(2:ℕ)) := by rw [Real.rpow_add hX]
      _ = _ := by norm_num
  have h3 : (width X/X)^2*(height X)^3=(1/4)*X^((2249:ℝ)/2500) := by
    rw [eta_sq X hX]
    unfold height
    rw [←Real.rpow_mul_natCast hX.le]
    calc
      _ = (1/4)*(X^((-899:ℝ)/500)*X^((562:ℝ)/625*(3:ℕ))) := by ring
      _ = (1/4)*X^((-899:ℝ)/500+(562:ℝ)/625*(3:ℕ)) := by rw [Real.rpow_add hX]
      _ = _ := by norm_num
  constructor
  · rw [h1]
    rw [show (-253:ℝ)/2500= -(253/2500:ℝ) by ring,Real.rpow_neg hX.le]
    ring
  constructor
  · rw [h2]
    rw [show (-1:ℝ)/2500= -(1/2500:ℝ) by ring,Real.rpow_neg hX.le]
    ring
  · rw [h3]
    rw [show (-2249:ℝ)/2500= -(2249/2500:ℝ) by ring,Real.rpow_neg hX.le]
    ring

theorem rowCost_bound (X : ℝ) (hX : 2≤X) (hl : 1≤Real.log X) :
    Item1FinitePolynomialTail.rowCost (cutoff X)≤384*X*Real.log X := by
  have hXp : 0<X := by linarith
  have hN1 : 1≤cutoff X := Nat.le_floor (by
    norm_num only [Nat.cast_one]
    linarith)
  have hNp : (0:ℝ)<cutoff X := by exact_mod_cast (show 0<cutoff X by omega)
  have hN := Nat.floor_le (show 0≤16*X by positivity)
  change (cutoff X:ℝ)≤16*X at hN
  have hlogs := Real.log_le_log hNp hN
  rw [Real.log_mul (by norm_num : (16:ℝ)≠0) hXp.ne'] at hlogs
  have hlog16 : Real.log 16≤4 := by
    rw [show (16:ℝ)=2^4 by norm_num,Real.log_pow]
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at hh ⊢
    linarith
  have hsmall : 1+Real.log (cutoff X)≤6*Real.log X := by linarith
  have hNN : 0≤1+Real.log (cutoff X) := by
    have hh := Real.log_nonneg (show (1:ℝ)≤cutoff X by exact_mod_cast hN1)
    linarith
  have hm := mul_le_mul hN hsmall hNN (by positivity : 0≤16*X)
  unfold Item1FinitePolynomialTail.rowCost
  nlinarith

/-- Three exact decay exponents, with a deliberately coarse common constant. -/
theorem actual_cell_tail_power (X : ℝ) (j : ℕ×ℕ)
    (hX : 2≤X) (hlog : 1000000≤Real.log X) (hj : j∈boxes (mesh X)) :
    (∫ t in SourceDyadicTail.outside (height X),
      density X (width X) j (primeTuples X j) t)≤
      67108864*(Real.log X)^7*X^((-1:ℝ)/2500) := by
  have hXp : 0<X := by linarith
  have hl : 1≤Real.log X := by linarith
  obtain ⟨hY,hYX⟩ := width_bounds X (by linarith)
  have hH := height_ge_one X (by linarith)
  have he0 : 0<width X/X := div_pos hY hXp
  have hHp : 0<height X := by linarith
  have hh := actual_cell_tail X (width X) (height X) j hX hlog hj hY hYX hH
  have hrow := mul_le_mul_of_nonneg_right (rowCost_bound X hX hl)
    (show 0≤98304*(Real.log X)^6/(3*(width X/X)^2*X*(height X)^2) by positivity)
  have hrow' : 98304*Item1FinitePolynomialTail.rowCost (cutoff X)*(Real.log X)^6/
      (3*(width X/X)^2*X*(height X)^2) ≤
      12582912*(Real.log X)^7/((width X/X)^2*(height X)^2) := by
    convert hrow using 1 <;> field_simp <;> ring
  obtain ⟨h1,h2,h3⟩ := reciprocal_scales X hXp
  have hh' : (∫ t in SourceDyadicTail.outside (height X),
      density X (width X) j (primeTuples X j) t) ≤
      196608*(Real.log X)^6*X^((-253:ℝ)/2500)+
      50331648*(Real.log X)^7*X^((-1:ℝ)/2500)+
      (256/3)*(Real.log X)^4*X^((-2249:ℝ)/2500) := by
    calc
      _ ≤ 49152*(Real.log X)^6/((width X/X)^2*X*height X)+
          12582912*(Real.log X)^7/((width X/X)^2*(height X)^2)+
          64*(Real.log X)^4/(3*(width X/X)^2*(height X)^3) := by linarith
      _ = 49152*(Real.log X)^6*(1/((width X/X)^2*X*height X))+
          12582912*(Real.log X)^7*(1/((width X/X)^2*(height X)^2))+
          (64/3)*(Real.log X)^4*(1/((width X/X)^2*(height X)^3)) := by ring
      _ = _ := by rw [h1,h2,h3]; ring
  have h6 : (Real.log X)^6≤(Real.log X)^7 := pow_le_pow_right₀ hl (by omega)
  have h4 : (Real.log X)^4≤(Real.log X)^7 := pow_le_pow_right₀ hl (by omega)
  have hp1 : X^((-253:ℝ)/2500)≤X^((-1:ℝ)/2500) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have hp3 : X^((-2249:ℝ)/2500)≤X^((-1:ℝ)/2500) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have hA := mul_le_mul h6 hp1 (Real.rpow_nonneg hXp.le _) (by positivity)
  have hB := mul_le_mul h4 hp3 (Real.rpow_nonneg hXp.le _) (by positivity)
  have hnon : 0≤(Real.log X)^7*X^((-1:ℝ)/2500) := by positivity
  have hA' := mul_le_mul_of_nonneg_left hA (by norm_num : (0:ℝ)≤196608)
  have hB' := mul_le_mul_of_nonneg_left hB (by norm_num : (0:ℝ)≤256/3)
  calc
    _ ≤ _ := hh'
    _ ≤ (196608+50331648+256/3)*((Real.log X)^7*X^((-1:ℝ)/2500)) := by
      simpa only [add_mul, mul_assoc] using
        add_le_add (add_le_add hA' (le_refl (50331648*((Real.log X)^7*X^((-1:ℝ)/2500))))) hB'
    _ ≤ 67108864*((Real.log X)^7*X^((-1:ℝ)/2500)) :=
      mul_le_mul_of_nonneg_right (by norm_num) hnon
    _ = _ := by rw [mul_assoc]

theorem actual_high_sum (X : ℝ) (hX : 2≤X) (hlog : 1000000≤Real.log X)
    (hm : mesh X≤1/1000000) :
    highEnergy X≤67108864*(Real.log X)^9*X^((-1:ℝ)/2500) := by
  have hl : 0<Real.log X := by linarith
  have hs := Finset.sum_le_sum (fun j hj => actual_cell_tail_power X j hX hlog hj)
  simp only [Finset.sum_const,nsmul_eq_mul] at hs
  have hc := cell_card_normalized_bound X (by linarith) hm
  have hc' : ((boxes (mesh X)).card:ℝ)≤(Real.log X)^2 := by
    have hh := (div_le_iff₀ (by positivity : 0<(Real.log X)^2)).mp hc
    nlinarith [sq_nonneg (Real.log X)]
  have hp := mul_le_mul_of_nonneg_right hc'
    (show 0≤67108864*(Real.log X)^7*X^((-1:ℝ)/2500) by positivity)
  unfold highEnergy
  exact hs.trans (by convert hp using 1 <;> ring)

/-- A purely elementary envelope for the log-power: no asymptotic prime input. -/
theorem log_power_envelope (X : ℝ) (hX : 1≤X) :
    (Real.log X)^9*X^((-1:ℝ)/2500)≤(45000:ℝ)^9/X^((1:ℝ)/5000) := by
  have hXp : 0<X := by linarith
  have hh := Real.log_le_rpow_div hXp.le (by norm_num : (0:ℝ)<1/45000)
  have hp := pow_le_pow_left₀ (Real.log_nonneg hX) hh 9
  have hm := mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg hXp.le ((-1:ℝ)/2500))
  calc
    _ ≤ (X^((1:ℝ)/45000)/(1/45000))^9*X^((-1:ℝ)/2500) := hm
    _ = (45000:ℝ)^9*(X^((1:ℝ)/45000))^9*X^((-1:ℝ)/2500) := by ring
    _ = (45000:ℝ)^9*X^((1:ℝ)/5000)*X^((-1:ℝ)/2500) := by
      rw [←Real.rpow_mul_natCast hXp.le]
      norm_num
    _ = (45000:ℝ)^9*X^((-1:ℝ)/5000) := by
      rw [mul_assoc,←Real.rpow_add hXp]
      norm_num
    _ = _ := by
      rw [show (-1:ℝ)/5000= -(1/5000:ℝ) by ring,Real.rpow_neg hXp.le]
      ring

/-- A full actual-source high-frequency budget with no high-energy premise. -/
theorem eventually_high_budget :
    ∀ᶠ X : ℝ in atTop, highEnergy X≤1/4096 := by
  let A : ℝ := 67108864*(45000:ℝ)^9*4096
  have hcut := (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/5000)).eventually
    (eventually_ge_atTop A)
  filter_upwards [eventually_geometry,hcut] with X hg hx
  have hXp : 0<X := by linarith [hg.1]
  have hp := mul_le_mul_of_nonneg_left (log_power_envelope X (by linarith [hg.1]))
    (by norm_num : (0:ℝ)≤67108864)
  calc
    _ ≤ 67108864*(Real.log X)^9*X^((-1:ℝ)/2500) :=
      actual_high_sum X hg.1 hg.2.1 hg.2.2
    _ ≤ 67108864*((45000:ℝ)^9/X^((1:ℝ)/5000)) := by simpa only [mul_assoc] using hp
    _ = (67108864*(45000:ℝ)^9)/X^((1:ℝ)/5000) := by ring
    _ ≤ 1/4096 := by
      apply (div_le_div_iff₀ (Real.rpow_pos_of_pos hXp _)
        (by norm_num : (0:ℝ)<4096)).mpr
      simpa only [A,one_mul] using hx

end Item1TailScalarMerge

-- ROOT SOURCE RECURSIVE AUDIT: exact original declarations.
run_cmd do
  for target in [
    ``Item1TailScalarMerge.width_bounds,
    ``Item1TailScalarMerge.height_ge_one,
    ``Item1TailScalarMerge.eta_eq,
    ``Item1TailScalarMerge.eta_sq,
    ``Item1TailScalarMerge.reciprocal_scales,
    ``Item1TailScalarMerge.rowCost_bound,
    ``Item1TailScalarMerge.actual_cell_tail_power,
    ``Item1TailScalarMerge.actual_high_sum,
    ``Item1TailScalarMerge.log_power_envelope,
    ``Item1TailScalarMerge.eventually_high_budget] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "Item1TailScalarMerge: 10 original theorem guards passed."
