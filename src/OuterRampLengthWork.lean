import OuterMaskFrequencyWork
import OuterRampAverageWork

/-! Explicit O(log X) compactification lengths for every actual source
cutoff on the enlarged ambient family. No unproved input-size hypothesis
is imposed on the source. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace OuterRampLengthWork
open OuterMaskFrequencyWork OuterSmoothStepWork OuterRampAverageWork
open OuterBufferedSourceWork OuterSourceReindexWork OuterBoundaryExtensionWork
open OuterSmoothErrorSupportWork LongerTupleEncoding

def slopeMass (s : ℝ) (i j : ℕ) (n : Fin 9) : ℝ :=
  |constantSlope s n|+|primeSlope n|+|divisorSlope n|+
    |firstSlope s i n|+|secondSlope s j n|
def cutoffLength (X s : ℝ) (i j : ℕ) (n : Fin 9) : ℝ :=
  slopeMass s i j n*Real.log X+1

theorem slopeMass_nonneg (s : ℝ) (i j : ℕ) (n : Fin 9) : 0 ≤ slopeMass s i j n := by
  unfold slopeMass
  positivity

theorem log_nat_bound (X : ℝ) (n : ℕ) (hn : 0 < n) (hnX : (n:ℝ) ≤ X) :
    |Real.log (n:ℝ)| ≤ Real.log X := by
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  rw [abs_of_nonneg (Real.log_nonneg hn1)]
  exact Real.log_le_log (by positivity) hnX

theorem candidate_factor_bounds (X : ℝ) (hX : 1 ≤ X) (u : Slice)
    (hu : u ∈ candidateSlices X) :
    (u.1:ℝ) ≤ X ∧ (u.2.1:ℝ) ≤ X ∧ (u.2.2:ℝ) ≤ X := by
  have hb (n : ℕ) (e : ℝ) (he : e ≤ 1) (hn : n ≤ ⌊X^e⌋₊) : (n:ℝ) ≤ X := by
    calc
      _ ≤ (⌊X^e⌋₊:ℝ) := by exact_mod_cast hn
      _ ≤ X^e := Nat.floor_le (Real.rpow_nonneg (by linarith) _)
      _ ≤ X := by simpa using Real.rpow_le_rpow_of_exponent_le hX he
  simp only [candidateSlices,Finset.mem_product,Finset.mem_Ioc] at hu
  exact ⟨hb _ _ (by norm_num) hu.1.2,hb _ _ (by norm_num) hu.2.1.2,
    hb _ _ (by norm_num) hu.2.2.2⟩

theorem ambient_gap_bound (X s : ℝ) (hX : 2 ≤ X) (r : Representation)
    (hr : r ∈ ambient X) (i j : ℕ) (n : Fin 9) :
    |signedGap (Real.log (r.1:ℝ)) (cutoffLogs X s (drop r) i j) n| ≤
      slopeMass s i j n*Real.log X := by
  have hd := ambient_data X hX r hr
  have hb := candidate_factor_bounds X (by linarith) (drop r) hd.2.1
  have hp := log_nat_bound X r.1 hd.2.2.1 hd.2.2.2.1
  have h1 := log_nat_bound X (drop r).1 hd.2.2.2.2.1 hb.1
  have h2 := log_nat_bound X (drop r).2.1 hd.2.2.2.2.2.1 hb.2.1
  have h3 := log_nat_bound X (drop r).2.2 hd.2.2.2.2.2.2 hb.2.2
  have hl : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
  rw [gap_affine]
  calc
    _ ≤ |constantSlope s n*Real.log X|+|primeSlope n*Real.log (r.1:ℝ)|+
        |divisorSlope n*Real.log ((drop r).1:ℝ)|+
        |firstSlope s i n*Real.log ((drop r).2.1:ℝ)|+
        |secondSlope s j n*Real.log ((drop r).2.2:ℝ)| := by
      exact (abs_add_le _ _).trans (add_le_add
        ((abs_add_le _ _).trans (add_le_add
          ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)) le_rfl)
    _ ≤ slopeMass s i j n*Real.log X := by
      simp only [abs_mul,abs_of_nonneg hl]
      have h1' := mul_le_mul_of_nonneg_left hp (abs_nonneg (primeSlope n))
      have h2' := mul_le_mul_of_nonneg_left h1 (abs_nonneg (divisorSlope n))
      have h3' := mul_le_mul_of_nonneg_left h2 (abs_nonneg (firstSlope s i n))
      have h4' := mul_le_mul_of_nonneg_left h3 (abs_nonneg (secondSlope s j n))
      unfold slopeMass
      nlinarith

theorem ambient_compactRamp_eq (X s : ℝ) (hX : 2 ≤ X) (r : Representation)
    (hr : r ∈ ambient X) (i j : ℕ) (n : Fin 9) :
    compactRamp (width X) (cutoffLength X s i j n)
      (signedGap (Real.log (r.1:ℝ)) (cutoffLogs X s (drop r) i j) n) =
    transition (width X)
      (signedGap (Real.log (r.1:ℝ)) (cutoffLogs X s (drop r) i j) n) := by
  have hw : 0 < width X := by unfold width; positivity
  have hw1 : width X ≤ 1 := by
    unfold width
    apply (div_le_one (by positivity)).mpr
    linarith
  apply compactRamp_eq_transition _ _ _ hw
  have hh := (le_abs_self _).trans (ambient_gap_bound X s hX r hr i j n)
  unfold cutoffLength
  linarith

run_cmd do
  for decl in [``slopeMass_nonneg, ``log_nat_bound, ``candidate_factor_bounds,
      ``ambient_gap_bound, ``ambient_compactRamp_eq] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end OuterRampLengthWork
