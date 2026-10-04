import PositiveInteriorModel

/-! Literal sharp-window Mangoldt and prime-coordinate sums on the checked
dyadic cells. These are finite identities and a logarithmic minorant only;
no estimate of the count-minus-model residual is asserted. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open scoped BigOperators
namespace PositiveSharpCounts
open PositiveInteriorModel PositiveInteriorCells

abbrev Triple := ℕ × (ℕ × ℕ)

def coordinates (X : ℝ) (j : ℕ × ℕ) : Finset Triple :=
  Finset.Ioc ⌊scale j.1⌋₊ ⌊2*scale j.1⌋₊ ×ˢ
    (Finset.Ioc ⌊scale j.2⌋₊ ⌊2*scale j.2⌋₊ ×ˢ
      Finset.Ioc ⌊thirdScale X j/8⌋₊ ⌊4*thirdScale X j⌋₊)

def allPrime (k : Triple) : Prop := k.1.Prime ∧ k.2.1.Prime ∧ k.2.2.Prime
instance (k : Triple) : Decidable (allPrime k) := by unfold allPrime; infer_instance

def natProduct (k : Triple) : ℕ := k.1*k.2.1*k.2.2
def tripleProduct (k : Triple) : ℝ := (k.1:ℝ)*(k.2.1:ℝ)*(k.2.2:ℝ)
def inWindow (x y : ℝ) (k : Triple) : Prop := x-y<tripleProduct k ∧ tripleProduct k≤x
instance (x y : ℝ) (k : Triple) : Decidable (inWindow x y k) := by
  unfold inWindow
  infer_instance

def windowTuples (X : ℝ) (j : ℕ × ℕ) (x y : ℝ) : Finset Triple :=
  (coordinates X j).filter (inWindow x y)
def tripleWeight (k : Triple) : ℝ := ArithmeticFunction.vonMangoldt k.1 *
  ArithmeticFunction.vonMangoldt k.2.1 * ArithmeticFunction.vonMangoldt k.2.2
def weightedCount (X : ℝ) (j : ℕ × ℕ) (x y : ℝ) : ℝ :=
  ∑ k ∈ windowTuples X j x y, tripleWeight k
def deletionCount (X : ℝ) (j : ℕ × ℕ) (x y : ℝ) : ℝ :=
  ∑ k ∈ (windowTuples X j x y).filter (fun k => ¬allPrime k), tripleWeight k
def primeWeightedCount (X : ℝ) (j : ℕ × ℕ) (x y : ℝ) : ℝ :=
  ∑ k ∈ (windowTuples X j x y).filter allPrime, tripleWeight k
def primeCount (X : ℝ) (j : ℕ × ℕ) (x y : ℝ) : ℕ :=
  ((windowTuples X j x y).filter allPrime).card

theorem natProduct_cast (k : Triple) : (natProduct k:ℝ)=tripleProduct k := by
  simp only [natProduct, tripleProduct, Nat.cast_mul]

theorem coordinates_positive (X : ℝ) (j : ℕ × ℕ) (k : Triple)
    (hk : k ∈ coordinates X j) : 0<k.1 ∧ 0<k.2.1 ∧ 0<k.2.2 := by
  obtain ⟨hp,hrq⟩ := Finset.mem_product.mp hk
  obtain ⟨hr,hq⟩ := Finset.mem_product.mp hrq
  have hp' := (Finset.mem_Ioc.mp hp).1
  have hr' := (Finset.mem_Ioc.mp hr).1
  have hq' := (Finset.mem_Ioc.mp hq).1
  omega

theorem tripleWeight_nonneg (k : Triple) : 0≤tripleWeight k := by
  unfold tripleWeight
  positivity

theorem weightedCount_nonneg (X x y : ℝ) (j : ℕ × ℕ) :
    0≤weightedCount X j x y := Finset.sum_nonneg (fun k _ => tripleWeight_nonneg k)

theorem deletionCount_nonneg (X x y : ℝ) (j : ℕ × ℕ) :
    0≤deletionCount X j x y := Finset.sum_nonneg (fun k _ => tripleWeight_nonneg k)

theorem primeWeightedCount_nonneg (X x y : ℝ) (j : ℕ × ℕ) :
    0≤primeWeightedCount X j x y := Finset.sum_nonneg (fun k _ => tripleWeight_nonneg k)

theorem exact_prime_coordinate_deletion (X x y : ℝ) (j : ℕ × ℕ) :
    weightedCount X j x y-deletionCount X j x y=primeWeightedCount X j x y := by
  have hh := Finset.sum_filter_add_sum_filter_not (windowTuples X j x y) allPrime tripleWeight
  change primeWeightedCount X j x y+deletionCount X j x y=weightedCount X j x y at hh
  linarith

theorem prime_weight_eq (k : Triple) (hk : allPrime k) :
    tripleWeight k=Real.log (k.1:ℝ)*Real.log (k.2.1:ℝ)*Real.log (k.2.2:ℝ) := by
  unfold tripleWeight
  rw [ArithmeticFunction.vonMangoldt_apply_prime hk.1,
    ArithmeticFunction.vonMangoldt_apply_prime hk.2.1,
    ArithmeticFunction.vonMangoldt_apply_prime hk.2.2]

theorem coordinates_bounds (X : ℝ) (hX : 0<X) (j : ℕ × ℕ) (k : Triple)
    (hk : k ∈ coordinates X j) :
    (scale j.1<(k.1:ℝ) ∧ (k.1:ℝ)≤2*scale j.1) ∧
    (scale j.2<(k.2.1:ℝ) ∧ (k.2.1:ℝ)≤2*scale j.2) ∧
    (thirdScale X j/8<(k.2.2:ℝ) ∧ (k.2.2:ℝ)≤4*thirdScale X j) := by
  have hp : 0<scale j.1 := by unfold scale; positivity
  have hr : 0<scale j.2 := by unfold scale; positivity
  have hL : 0<thirdScale X j := div_pos hX (mul_pos hp hr)
  obtain ⟨hpk,hrq⟩ := Finset.mem_product.mp hk
  obtain ⟨hrk,hqk⟩ := Finset.mem_product.mp hrq
  have hpk' := Finset.mem_Ioc.mp hpk
  have hrk' := Finset.mem_Ioc.mp hrk
  have hqk' := Finset.mem_Ioc.mp hqk
  exact ⟨⟨(Nat.floor_lt hp.le).mp hpk'.1,
      (Nat.le_floor_iff (by positivity)).mp hpk'.2⟩,
    ⟨(Nat.floor_lt hr.le).mp hrk'.1,
      (Nat.le_floor_iff (by positivity)).mp hrk'.2⟩,
    ⟨(Nat.floor_lt (by positivity)).mp hqk'.1,
      (Nat.le_floor_iff (by positivity)).mp hqk'.2⟩⟩

theorem prime_weight_le_denominator (X : ℝ) (hX : 0<X)
    (j : ℕ × ℕ) (k : Triple) (hk : k ∈ coordinates X j) (hprime : allPrime k) :
    tripleWeight k≤denominator X j := by
  obtain ⟨hp,hr,hq⟩ := coordinates_bounds X hX j k hk
  have hL : 0<thirdScale X j := by unfold thirdScale scale; positivity
  have hp0 : (0:ℝ)<k.1 := by exact_mod_cast hprime.1.pos
  have hr0 : (0:ℝ)<k.2.1 := by exact_mod_cast hprime.2.1.pos
  have hq0 : (0:ℝ)<k.2.2 := by exact_mod_cast hprime.2.2.pos
  have hp1 : (1:ℝ)≤k.1 := by exact_mod_cast hprime.1.one_le
  have hr1 : (1:ℝ)≤k.2.1 := by exact_mod_cast hprime.2.1.one_le
  have hq1 : (1:ℝ)≤k.2.2 := by exact_mod_cast hprime.2.2.one_le
  have hlp := Real.log_le_log hp0 hp.2
  have hlr := Real.log_le_log hr0 hr.2
  have hlq := Real.log_le_log hq0 (show (k.2.2:ℝ)≤8*thirdScale X j by linarith)
  have hlp0 := Real.log_nonneg hp1
  have hlr0 := Real.log_nonneg hr1
  have hlq0 := Real.log_nonneg hq1
  rw [prime_weight_eq k hprime]
  exact mul_le_mul (mul_le_mul hlp hlr hlr0 (hlp0.trans hlp)) hlq hlq0
    (mul_nonneg (hlp0.trans hlp) (hlr0.trans hlr))

theorem primeWeightedCount_le (X x y : ℝ) (hX : 0<X) (j : ℕ × ℕ) :
    primeWeightedCount X j x y≤(primeCount X j x y:ℝ)*denominator X j := by
  have hb := Finset.sum_le_sum (s := (windowTuples X j x y).filter allPrime)
    (f := tripleWeight) (g := fun _ => denominator X j) (fun k hk =>
      prime_weight_le_denominator X hX j k
        (Finset.mem_filter.mp (Finset.mem_filter.mp hk).1).1 (Finset.mem_filter.mp hk).2)
  simpa only [primeWeightedCount, primeCount, Finset.sum_const, nsmul_eq_mul] using hb

theorem prime_count_minorant (X x y : ℝ) (hX : 1<X) (hs : mesh X≤1/1000000)
    (j : ℕ × ℕ) (hj : j ∈ boxes (mesh X)) :
    0≤(weightedCount X j x y-deletionCount X j x y)/denominator X j ∧
      (weightedCount X j x y-deletionCount X j x y)/denominator X j≤
        (primeCount X j x y:ℝ) := by
  have hd := (denominator_bounds X hX hs j hj).1
  rw [exact_prime_coordinate_deletion]
  exact ⟨div_nonneg (primeWeightedCount_nonneg X x y j) hd.le,
    (div_le_iff₀ hd).mpr (primeWeightedCount_le X x y (by linarith) j)⟩

run_cmd do
  for decl in [``natProduct_cast, ``coordinates_positive, ``tripleWeight_nonneg,
      ``weightedCount_nonneg, ``deletionCount_nonneg, ``primeWeightedCount_nonneg,
      ``exact_prime_coordinate_deletion, ``prime_weight_eq, ``coordinates_bounds,
      ``prime_weight_le_denominator, ``primeWeightedCount_le, ``prime_count_minorant] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ACTUAL SHARP-WINDOW COUNTS AND LOGARITHMIC PRIME MINORANT; NO RESIDUAL SAVING"
end PositiveSharpCounts
end
