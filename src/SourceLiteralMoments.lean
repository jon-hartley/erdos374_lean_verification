import SourceMassDischarge
import SourceSelectedOrders
import CancellationTransferEndpoints

/-! v6: the actual source intervals satisfy the logarithmic moment theorem.
This file constructs all support, mass, order, rounding,
and height hypotheses. It does not prove pointwise prime cancellation or
Plancherel. The source remains [P,2P), [R,2R), (floor(L/8),floor(4L)]. -/
set_option autoImplicit false
set_option maxHeartbeats 16000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators
namespace SourceLiteralMoments
open PositiveInteriorModel PositiveInteriorCells CancellationTransferEndpoints
open SourceMassDischarge SourceSelectedOrders SourceFractionalGeometryStrong
open Erdos374.HarmanGram152

def ideal (X : ℝ) (j : ℕ × ℕ) : Fin 3 → ℝ :=
  ![scale j.1,scale j.2,thirdScale X j]

def exponent (X : ℝ) (j : ℕ × ℕ) : Fin 3 → ℝ :=
  ![(j.1:ℝ)*mesh X,(j.2:ℝ)*mesh X,1-(j.1:ℝ)*mesh X-(j.2:ℝ)*mesh X]

def support (X : ℝ) (j : ℕ × ℕ) : Fin 3 → Finset ℕ :=
  ![Finset.Ico (2^j.1) (2*2^j.1),Finset.Ico (2^j.2) (2*2^j.2),
    Finset.Ioc ⌊thirdScale X j/8⌋₊ ⌊4*thirdScale X j⌋₊]

def base (X : ℝ) (j : ℕ × ℕ) : Fin 3 → ℕ :=
  ![⌊scale j.1/2⌋₊,⌊scale j.2/2⌋₊,⌊thirdScale X j/8⌋₊]

def factor (X : ℝ) (j : ℕ × ℕ) (i : Fin 3) (t : ℝ) : ℂ :=
  verticalDirichlet152 (support X j i) mangoldt 1 t

theorem sourceCoordinates_eq (X : ℝ) (j : ℕ × ℕ) :
    sourceCoordinates X j = support X j 0 ×ˢ (support X j 1 ×ˢ support X j 2) := rfl

theorem ideal_positive (X : ℝ) (j : ℕ × ℕ) (hX : 0 < X) (i : Fin 3) :
    0 < ideal X j i := by
  fin_cases i <;> dsimp [ideal,scale,thirdScale] <;> positivity

theorem ideal_log (X : ℝ) (j : ℕ × ℕ) (hX : 1 < X) (i : Fin 3) :
    Real.log (ideal X j i) = exponent X j i*Real.log X := by
  have hP : 0 < scale j.1 := by unfold scale; positivity
  have hR : 0 < scale j.2 := by unfold scale; positivity
  have hm := mesh_mul_log X hX
  fin_cases i
  · change Real.log (scale j.1) = ((j.1:ℝ)*mesh X)*Real.log X
    rw [scale,Real.log_pow]
    nlinarith [congrArg (fun x : ℝ => (j.1:ℝ)*x) hm]
  · change Real.log (scale j.2) = ((j.2:ℝ)*mesh X)*Real.log X
    rw [scale,Real.log_pow]
    nlinarith [congrArg (fun x : ℝ => (j.2:ℝ)*x) hm]
  · change Real.log (thirdScale X j) =
      (1-(j.1:ℝ)*mesh X-(j.2:ℝ)*mesh X)*Real.log X
    rw [thirdScale,Real.log_div (by linarith : X ≠ 0) (mul_pos hP hR).ne',
      Real.log_mul hP.ne' hR.ne']
    simp only [scale,Real.log_pow]
    nlinarith [congrArg (fun x : ℝ => (j.1:ℝ)*x) hm,
      congrArg (fun x : ℝ => (j.2:ℝ)*x) hm]

theorem ideal_eq_power (X : ℝ) (j : ℕ × ℕ) (hX : 1 < X) (i : Fin 3) :
    ideal X j i = X^(exponent X j i) := by
  have hp := ideal_positive X j (by linarith) i
  have hq := Real.rpow_pos_of_pos (show 0 < X by linarith) (exponent X j i)
  have he : Real.log (ideal X j i) = Real.log (X^(exponent X j i)) := by
    rw [ideal_log X j hX i,Real.log_rpow (show 0 < X by linarith)]
  exact le_antisymm ((Real.log_le_log_iff hp hq).mp he.le)
    ((Real.log_le_log_iff hq hp).mp he.symm.le)

theorem exponent_bounds (X : ℝ) (j : ℕ × ℕ) (hX : 1 < X)
    (hj : j ∈ boxes (mesh X)) (i : Fin 3) :
    1/6 ≤ exponent X j i ∧ exponent X j i ≤ 1/2 := by
  have hc := triangle_coordinate_bounds _ _ (source_triangle X hX j hj)
  fin_cases i
  · exact hc.1
  · exact hc.2.1
  · exact hc.2.2

theorem large_ideal (X : ℝ) (j : ℕ × ℕ) (hX : 1 < X)
    (hlog : 1000000 ≤ Real.log X) (hj : j ∈ boxes (mesh X)) (i : Fin 3) :
    16 ≤ ideal X j i ∧ ideal X j i ≤ X := by
  have hx := exponent_bounds X j hX hj i
  have hl2 : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
    linarith
  have hl16 : Real.log 16 = 4*Real.log 2 := by
    rw [show (16:ℝ)=2^4 by norm_num,Real.log_pow]; norm_num
  constructor
  · apply (Real.log_le_log_iff (by norm_num) (ideal_positive X j (by linarith) i)).mp
    rw [hl16,ideal_log X j hX i]
    nlinarith [mul_le_mul_of_nonneg_right hx.1 (show 0 ≤ Real.log X by linarith)]
  · rw [ideal_eq_power X j hX i]
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hX.le
      (hx.2.trans (by norm_num : (1/2:ℝ) ≤ 1))

/-- Integer rounding loses at most a factor two in the selected lower scale. -/
theorem floor_data (z d : ℝ) (hz : 16 ≤ z) (hd : d=2 ∨ d=8) :
    1 ≤ ⌊z/d⌋₊ ∧ z/16 ≤ (⌊z/d⌋₊:ℝ) ∧
      (⌊z/d⌋₊:ℝ) ≤ z/d ∧ (⌊z/d⌋₊:ℝ) ≤ z := by
  have hd0 : 0 < d := by rcases hd with rfl | rfl <;> norm_num
  have hdiv : 2 ≤ z/d := by
    rcases hd with rfl | rfl <;> linarith
  have hfl := Nat.lt_floor_add_one (z/d)
  have hle := Nat.floor_le (show 0 ≤ z/d by linarith)
  have hnat : 1 ≤ ⌊z/d⌋₊ := Nat.le_floor (by
    simpa only [Nat.cast_one] using (show (1:ℝ) ≤ z/d by linarith))
  refine ⟨hnat,?_,hle,?_⟩
  · rcases hd with rfl | rfl <;> linarith
  · rcases hd with rfl | rfl <;> linarith

theorem support_embedded (X : ℝ) (j : ℕ × ℕ) (hX : 1 < X)
    (hlog : 1000000 ≤ Real.log X) (hj : j ∈ boxes (mesh X)) (i : Fin 3) :
    1 ≤ base X j i ∧ (base X j i:ℝ) ≤ X ∧
      X^(exponent X j i)/16 ≤ (base X j i:ℝ) ∧
      support X j i ⊆ Finset.Ioc (base X j i) (SourceMomentFinite.upper (base X j i)) := by
  have hi := large_ideal X j hX hlog hj i
  have hd : 1 ≤ base X j i ∧ ideal X j i/16 ≤ (base X j i:ℝ) ∧
      (base X j i:ℝ) ≤ ideal X j i/(![2,2,8] i) ∧
      (base X j i:ℝ) ≤ ideal X j i := by
    fin_cases i
    · exact floor_data _ 2 (large_ideal X j hX hlog hj 0).1 (Or.inl rfl)
    · exact floor_data _ 2 (large_ideal X j hX hlog hj 1).1 (Or.inl rfl)
    · exact floor_data _ 8 (large_ideal X j hX hlog hj 2).1 (Or.inr rfl)
  refine ⟨hd.1,hd.2.2.2.trans hi.2,?_,?_⟩
  · simpa only [ideal_eq_power X j hX i] using hd.2.1
  · intro n hn
    fin_cases i
    · have hn' := Finset.mem_Ico.mp hn
      have hlo : (scale j.1:ℝ) ≤ n := by simpa [scale] using
        (show (((2:ℕ)^j.1:ℕ):ℝ) ≤ n by exact_mod_cast hn'.1)
      have hhi : (n:ℝ) ≤ 2*scale j.1 := by simpa [scale] using
        (show (n:ℝ) ≤ (2*(2:ℕ)^j.1:ℕ) by exact_mod_cast hn'.2.le)
      apply Finset.mem_Ioc.mpr
      constructor
      · have hh : (base X j 0:ℝ) < n := by
          have hu : (base X j 0:ℝ) ≤ scale j.1/2 := hd.2.2.1
          have hscale : 0 < scale j.1 := by unfold scale; positivity
          linarith
        exact_mod_cast hh
      · have hh : (n:ℝ) ≤ 64*(base X j 0:ℝ) := by
          have hl : scale j.1/16 ≤ (base X j 0:ℝ) := hd.2.1
          linarith
        simpa [SourceMomentFinite.upper] using (show n ≤ 64*base X j 0 by exact_mod_cast hh)
    · have hn' := Finset.mem_Ico.mp hn
      have hlo : (scale j.2:ℝ) ≤ n := by simpa [scale] using
        (show (((2:ℕ)^j.2:ℕ):ℝ) ≤ n by exact_mod_cast hn'.1)
      have hhi : (n:ℝ) ≤ 2*scale j.2 := by simpa [scale] using
        (show (n:ℝ) ≤ (2*(2:ℕ)^j.2:ℕ) by exact_mod_cast hn'.2.le)
      apply Finset.mem_Ioc.mpr
      constructor
      · have hh : (base X j 1:ℝ) < n := by
          have hu : (base X j 1:ℝ) ≤ scale j.2/2 := hd.2.2.1
          have hscale : 0 < scale j.2 := by unfold scale; positivity
          linarith
        exact_mod_cast hh
      · have hh : (n:ℝ) ≤ 64*(base X j 1:ℝ) := by
          have hl : scale j.2/16 ≤ (base X j 1:ℝ) := hd.2.1
          linarith
        simpa [SourceMomentFinite.upper] using (show n ≤ 64*base X j 1 by exact_mod_cast hh)
    · have hn' := Finset.mem_Ioc.mp hn
      refine Finset.mem_Ioc.mpr ⟨hn'.1,?_⟩
      have hthird : 0 < thirdScale X j := ideal_positive X j (by linarith) 2
      have hhi : (n:ℝ) ≤ 4*thirdScale X j :=
        (show (n:ℝ) ≤ (⌊4*thirdScale X j⌋₊:ℝ) by exact_mod_cast hn'.2).trans
          (Nat.floor_le (by positivity))
      have hh : (n:ℝ) ≤ 64*(base X j 2:ℝ) := by
        have hl : thirdScale X j/16 ≤ (base X j 2:ℝ) := hd.2.1
        linarith
      simpa [SourceMomentFinite.upper] using (show n ≤ 64*base X j 2 by exact_mod_cast hh)

theorem factor_continuous (X : ℝ) (j : ℕ × ℕ) (i : Fin 3) :
    Continuous (factor X j i) := by
  apply NormalizedMeanSquare.continuous_vertical
  intro n hn
  fin_cases i
  · have hh := (Finset.mem_Ico.mp hn).1
    exact (show 0 < (2:ℕ)^j.1 by positivity).trans_le hh
  · have hh := (Finset.mem_Ico.mp hn).1
    exact (show 0 < (2:ℕ)^j.2 by positivity).trans_le hh
  · have hh := (Finset.mem_Ioc.mp hn).1
    omega

/-- Actual-cell moment choices and estimates. All three polynomials are literal.
No prime cap, mass premise, fractional moment, or physical mean is assumed. -/
theorem actual_cell_moments (X : ℝ) (j : ℕ × ℕ) (hX : 2 ≤ X)
    (hlog : 1000000 ≤ Real.log X) (hj : j ∈ boxes (mesh X)) :
    ∃ β : Fin 3 → ℝ,
      (∀ i, 4 ≤ β i) ∧ (2001/2000:ℝ) ≤ 2/β 0+2/β 1+2/β 2 ∧
      ∀ i, (∫ t in Icc (-X^(562/625:ℝ)) (X^(562/625:ℝ)),
        ‖factor X j i t‖^(β i)) ≤ commonConstant*(1+Real.log X)^18 := by
  have hX1 : 1 < X := by linarith
  obtain ⟨h,β,hdata,hguard,hS⟩ := choose ((j.1:ℝ)*mesh X) ((j.2:ℝ)*mesh X)
    (source_triangle X hX1 j hj)
  refine ⟨β,?_,hS,?_⟩
  · intro i
    have hh : (2:ℝ) ≤ h i := by exact_mod_cast (hdata i).1
    linarith [(hdata i).2.2.1]
  · intro i
    obtain ⟨hD,hDX,hDx,hsub⟩ := support_embedded X j hX1 hlog hj i
    have hl := physical_length_guard X (exponent X j i) (β i) (base X j i) (h i)
      hX hlog hD hDx (hdata i).1 (hdata i).2.1 (hdata i).2.2.1
      (hdata i).2.2.2 (hguard i)
    have hU1 : 1 ≤ X^(562/625:ℝ) := Real.one_le_rpow hX1.le (by norm_num)
    have hUX : X^(562/625:ℝ) ≤ X := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hX1.le
        (by norm_num : (562/625:ℝ) ≤ 1)
    have hhr : (2:ℝ) ≤ h i := by exact_mod_cast (hdata i).1
    have hm := supported_moment (base X j i) (h i) (support X j i) X
      (-X^(562/625:ℝ)) (2*X^(562/625:ℝ)) (β i) hD (hdata i).1 (hdata i).2.1
      hX hDX (by linarith) (by linarith) (hdata i).2.2.1
      (by linarith [(hdata i).2.2.2]) hsub hl
    simpa only [show -X^(562/625:ℝ)+2*X^(562/625:ℝ)=X^(562/625:ℝ) by ring,
      factor] using hm

#check actual_cell_moments
#print axioms actual_cell_moments
run_cmd do
  for n in [``sourceCoordinates_eq,``ideal_positive,``ideal_log,``ideal_eq_power,
      ``exponent_bounds,``large_ideal,``floor_data,``support_embedded,
      ``factor_continuous,``actual_cell_moments] do
    for ax in (← Lean.collectAxioms n) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {n}"
  Lean.logInfo "LITERAL SOURCE CELL MOMENTS: VALID ONLY AFTER SUCCESSFUL COMPILATION"
end SourceLiteralMoments
