import FrontierSmallBracket

/-! Exact separation of a complete signed profile into the high and low
small-divisor ranges. The low part is a literal finite tuple sum, so signs,
unit divisors, and repeated product representations are retained. This module
proves identities only; it does not estimate the low contribution. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace FrontierSmallBracketSplit
open SieveBoxGrouping FourPrimeScaleBudget

/-- The strict complement of the high small-divisor support. -/
def lowSupport (X s : ℝ) : Finset ℕ :=
  (SieveUpperBoxWindow.smallCarrier (SieveWeightedCutoffs.level X s) s).filter
    (fun d => (d : ℝ) < X ^ lowerExponent s)

/-- The exact low-divisor kernel, retaining every tuple representation. -/
def lowKernel (X s z : ℝ) (upper : Bool) (h : List ℕ)
    (f : ℕ → ℝ) : ℝ :=
  ∑ d ∈ lowSupport X s,
    ∑ t ∈ fibre (SieveWeightedCutoffs.level X s) s z h,
      FrontierSmallBracket.smallWeight X s upper d * f (d * t.prod)

/-- Floors are cast before subtraction, as in HarmanDivisorWindow. -/
def windowKernel (L R : ℝ) (m : ℕ) : ℝ :=
  (⌊R / m⌋₊ : ℝ) - (⌊L / m⌋₊ : ℝ) - (R - L) / m

def lowRemainder (X s z : ℝ) (upper : Bool) (h : List ℕ)
    (L R : ℝ) : ℝ :=
  lowKernel X s z upper h (windowKernel L R)

theorem mem_lowSupport (X s : ℝ) (d : ℕ) :
    d ∈ lowSupport X s ↔
      d ∈ SieveUpperBoxWindow.smallCarrier (SieveWeightedCutoffs.level X s) s ∧
        (d : ℝ) < X ^ lowerExponent s := by
  simp only [lowSupport, Finset.mem_filter]

theorem high_low_disjoint (X s : ℝ) :
    Disjoint (FrontierSmallBracket.rightSupport X s) (lowSupport X s) := by
  apply Finset.disjoint_left.mpr
  intro d hd hl
  exact (not_lt_of_ge (Finset.mem_filter.mp hd).2) (Finset.mem_filter.mp hl).2

theorem high_low_union (X s : ℝ) :
    FrontierSmallBracket.rightSupport X s ∪ lowSupport X s =
      SieveUpperBoxWindow.smallCarrier (SieveWeightedCutoffs.level X s) s := by
  ext d
  simp only [FrontierSmallBracket.rightSupport, lowSupport,
    Finset.mem_union, Finset.mem_filter]
  constructor
  · rintro (h | h)
    · exact h.1
    · exact h.1
  · intro hd
    by_cases hh : X ^ lowerExponent s ≤ (d : ℝ)
    · exact Or.inl ⟨hd, hh⟩
    · exact Or.inr ⟨hd, lt_of_not_ge hh⟩

theorem carrier_sum_split (X s : ℝ) (f : ℕ → ℝ) :
    (∑ d ∈ SieveUpperBoxWindow.smallCarrier (SieveWeightedCutoffs.level X s) s,
      f d) =
      (∑ d ∈ FrontierSmallBracket.rightSupport X s, f d) +
        ∑ d ∈ lowSupport X s, f d := by
  rw [← high_low_union X s, Finset.sum_union (high_low_disjoint X s)]

/-- An arbitrary old cut gives the same full profile before the d-split. -/
theorem profile_kernel_split (X s z : ℝ) (upper : Bool)
    (cut : List ℕ → ℕ) (h : List ℕ) (f : ℕ → ℝ) :
    (∑ m ∈ MomentRemainderProfileSplit.splitSupport
        (SieveUpperBoxWindow.smallCarrier (SieveWeightedCutoffs.level X s) s)
        (SieveWeightedCutoffs.level X s) s z (h.take (cut h)) (h.drop (cut h)),
      MomentRemainderProfileSplit.splitCoefficient
        (SieveUpperBoxWindow.smallCarrier (SieveWeightedCutoffs.level X s) s)
        (FrontierSmallBracket.smallWeight X s upper)
        (SieveWeightedCutoffs.level X s) s z (h.take (cut h)) (h.drop (cut h)) m * f m) =
      (∑ m ∈ FrontierSmallBracket.support X s z h,
        FrontierSmallBracket.coefficient X s z upper h m * f m) +
          lowKernel X s z upper h f := by
  rw [MomentRemainderProfileSplit.split_kernel, List.take_append_drop,
    FrontierSmallBracket.kernel]
  exact carrier_sum_split X s (fun d =>
    ∑ t ∈ fibre (SieveWeightedCutoffs.level X s) s z h,
      FrontierSmallBracket.smallWeight X s upper d * f (d * t.prod))

theorem profile_remainder_split (X s z : ℝ) (upper : Bool)
    (cut : List ℕ → ℕ) (h : List ℕ) (L R : ℝ) :
    MomentRemainderProfileSplit.profileRemainder
        (SieveWeightedCutoffs.level X s) s z upper cut h L R =
      FrontierSmallBracket.remainder X s z upper h L R +
        lowRemainder X s z upper h L R := by
  unfold MomentRemainderProfileSplit.profileRemainder FrontierSmallBracket.remainder
  simp only [HarmanDivisorWindow.remainder_eq_sum]
  exact profile_kernel_split X s z upper cut h (windowKernel L R)

theorem snoc_remainder_split (X s z : ℝ) (upper : Bool)
    (g : List ℕ) (j : ℕ) (L R : ℝ) :
    TailSieveProfileBasics.remainder
        (SieveWeightedCutoffs.level X s) s z upper g j L R =
      FrontierSmallBracket.remainder X s z upper (g ++ [j]) L R +
        lowRemainder X s z upper (g ++ [j]) L R := by
  rw [TailSieveProfileBasics.remainder_eq_profile]
  exact profile_remainder_split X s z upper (fun _ => g.length) (g ++ [j]) L R

run_cmd do
  for decl in [``mem_lowSupport, ``high_low_disjoint, ``high_low_union,
      ``carrier_sum_split, ``profile_kernel_split, ``profile_remainder_split,
      ``snoc_remainder_split] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "EXACT FULL PROFILE HIGH-LOW SMALL-BRACKET SPLIT PASSED"

end FrontierSmallBracketSplit
end
