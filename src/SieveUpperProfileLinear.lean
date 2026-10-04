import SieveUpperProfileCumulative

/-! Exact one-prime linearity and the actual finite-staircase transfer.
All cumulative arithmetic inputs are proved for the actual primes. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Real Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace SieveUpperProfileLinear
open SieveUpperProfileCumulative

def staircase {ι : Type*} (S : Finset ι) (d c : ι → ℝ) (r : ℝ) : ℝ :=
  ∑ i ∈ S, d i*(if r ≤ c i then 1 else 0)

def area {ι : Type*} (S : Finset ι) (d c : ι → ℝ) : ℝ := ∑ i ∈ S, d i*(c i-2)

theorem onePrime_add (f g : ℝ → ℝ → ℝ) (T z : ℝ) :
    onePrime (fun T z => f T z+g T z) T z = onePrime f T z+onePrime g T z := by
  unfold onePrime
  simp only [mul_add, Finset.sum_add_distrib]

theorem onePrime_const_mul (a : ℝ) (f : ℝ → ℝ → ℝ) (T z : ℝ) :
    onePrime (fun T z => a*f T z) T z = a*onePrime f T z := by
  unfold onePrime
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  ring

theorem onePrime_sum {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (f : ι → ℝ → ℝ → ℝ) (T z : ℝ) :
    onePrime (fun T z => ∑ i ∈ S, f i T z) T z = ∑ i ∈ S, onePrime (f i) T z := by
  induction S using Finset.induction_on with
  | empty => simp [onePrime]
  | @insert i S hi ih =>
    simp only [Finset.sum_insert hi]
    rw [onePrime_add, ih]

theorem staircase_nonneg {ι : Type*} (S : Finset ι) (d c : ι → ℝ)
    (hd : ∀ i ∈ S, 0 ≤ d i) (r : ℝ) : 0 ≤ staircase S d c r := by
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg (hd i hi) (by split_ifs <;> norm_num)

theorem onePrime_staircase_eq {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (d c : ι → ℝ) (T z : ℝ) :
    onePrime (fun T z => staircase S d c (log T/log z)) T z =
      ∑ i ∈ S, d i*onePrime (fun T z => if log T/log z ≤ c i then 1 else 0) T z := by
  dsimp only [staircase]
  rw [onePrime_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact onePrime_const_mul _ _ _ _

/-- The finite staircase contributes its area divided by three, with any
positive arithmetic allowance. One common threshold serves every summand. -/
theorem eventually_staircase {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (d c : ι → ℝ)
    (hd : ∀ i ∈ S, 0 ≤ d i) (hc : ∀ i ∈ S, 2 ≤ c i)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ Z : ℝ, 2 ≤ Z ∧ ∀ z T : ℝ, Z ≤ z → z^3 ≤ T →
      onePrime (fun T z => staircase S d c (log T/log z)) T z ≤ area S d c/3+δ := by
  let D : ℝ := ∑ i ∈ S, d i
  have hD : 0 ≤ D := Finset.sum_nonneg hd
  let η : ℝ := δ/(1+D)
  have hη : 0 < η := div_pos hδ (by linarith)
  have he : ∀ᶠ z : ℝ in atTop, ∀ i ∈ S, ∀ T : ℝ, z^3 ≤ T →
      onePrime (fun T z => if log T/log z ≤ c i then 1 else 0) T z ≤ (c i-2)/3+η := by
    apply (eventually_all_finset S).mpr
    intro i hi
    obtain ⟨Z, hZ, hb⟩ := eventually_cumulative (c i) (hc i hi) η hη
    filter_upwards [eventually_ge_atTop Z] with z hz
    intro T hT
    exact (hb z T hz hT).trans (add_le_add
      (cumulative_le_area (c i) (log T/log z) (hc i hi)
        (parameter_ge_three T z (hZ.trans hz) hT)) le_rfl)
  obtain ⟨Z₀, hZ₀⟩ := eventually_atTop.mp he
  refine ⟨max 2 Z₀, le_max_left _ _, ?_⟩
  intro z T hz hT
  have hb := hZ₀ z ((le_max_right _ _).trans hz)
  have herr : η*D ≤ δ := by
    calc
      _ ≤ η*(1+D) := mul_le_mul_of_nonneg_left (by linarith) hη.le
      _ = δ := by dsimp [η]; field_simp
  rw [onePrime_staircase_eq]
  calc
    _ ≤ ∑ i ∈ S, d i*((c i-2)/3+η) := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (hb i hi T hT) (hd i hi)
    _ = area S d c/3+η*D := by
      dsimp only [area, D]
      rw [Finset.sum_div, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ ≤ _ := add_le_add le_rfl herr

run_cmd do
  for decl in [``onePrime_add, ``onePrime_const_mul, ``onePrime_sum,
      ``staircase_nonneg, ``onePrime_staircase_eq, ``eventually_staircase] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ACTUAL ONE-PRIME FINITE STAIRCASE TRANSFER BY ITS AREA"
end SieveUpperProfileLinear
end
