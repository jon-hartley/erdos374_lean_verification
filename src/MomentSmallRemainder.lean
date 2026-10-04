import PositiveSharpRemainderSupport
import PolynomialLogEnvelope
import SignedDivisorRegularity

/-! An exact split of the entire collected signed remainder, and an
unconditional estimate for its small physical divisor indices. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators

namespace MomentSmallRemainder

def lowSupport (X s a : ℝ) : Finset ℕ :=
  (PositiveSharpRemainderAnalysisPhysical.support X s).filter (fun m => (m:ℝ) ≤ X^a)

def highSupport (X s a : ℝ) : Finset ℕ :=
  (PositiveSharpRemainderAnalysisPhysical.support X s).filter (fun m => ¬ (m:ℝ) ≤ X^a)

def low (X s a x y : ℝ) : ℝ :=
  HarmanDivisorWindow.remainder (lowSupport X s a)
    (PositiveSharpRemainderAnalysisPhysical.coefficient X s) (x-y) x

def high (X s a x y : ℝ) : ℝ :=
  HarmanDivisorWindow.remainder (highSupport X s a)
    (PositiveSharpRemainderAnalysisPhysical.coefficient X s) (x-y) x

theorem split (X s a x y : ℝ) :
    PositiveSharpBoxedCount.signedRemainder X s x y = low X s a x y + high X s a x y := by
  rw [PositiveSharpRemainderAnalysisPhysical.signedRemainder_eq]
  unfold low high lowSupport highSupport
  simp only [HarmanDivisorWindow.remainder_eq_sum]
  exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm

theorem floor_error_le_one (d : ℕ) (L R : ℝ) (hd : 0<d)
    (hL : 0≤L) (hR : 0≤R) :
    |(⌊R/d⌋₊:ℝ) - (⌊L/d⌋₊:ℝ) - (R-L)/d| ≤ 1 := by
  have hdp : (0:ℝ)<d := by exact_mod_cast hd
  have h1 := Nat.floor_le (div_nonneg hL hdp.le)
  have h2 := Nat.floor_le (div_nonneg hR hdp.le)
  have h3 := Nat.sub_one_lt_floor (L/(d:ℝ))
  have h4 := Nat.sub_one_lt_floor (R/(d:ℝ))
  rw [sub_div]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem remainder_le_card (S : Finset ℕ) (w : ℕ→ℝ) (L R B : ℝ)
    (hpos : ∀d∈S, 0<d) (hL : 0≤L) (hR : 0≤R)
    (hcap : ∀d∈S, |w d|≤B) :
    |HarmanDivisorWindow.remainder S w L R| ≤ S.card * B := by
  rw [HarmanDivisorWindow.remainder_eq_sum]
  calc
    _ ≤ ∑d∈S, |w d * ((⌊R/d⌋₊:ℝ)-(⌊L/d⌋₊:ℝ)-(R-L)/d)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑d∈S, B := by
      apply Finset.sum_le_sum
      intro d hd
      rw [abs_mul]
      exact (mul_le_of_le_one_right (abs_nonneg _) (floor_error_le_one d L R (hpos d hd) hL hR)).trans (hcap d hd)
    _ = _ := by simp

theorem low_card_le (X s a : ℝ) (hX : 0<X)
    (hpos : ∀m∈PositiveSharpRemainderAnalysisPhysical.support X s, 0<m) :
    ((lowSupport X s a).card:ℝ) ≤ X^a := by
  have hsub : lowSupport X s a ⊆ Finset.Ioc 0 ⌊X^a⌋₊ := by
    intro m hm
    obtain ⟨hm, hbound⟩ := Finset.mem_filter.mp hm
    exact Finset.mem_Ioc.mpr ⟨hpos m hm, Nat.le_floor hbound⟩
  have hc := Finset.card_le_card hsub
  have hc' : ((lowSupport X s a).card:ℝ) ≤ (⌊X^a⌋₊:ℝ) := by
    exact_mod_cast (by simpa using hc : (lowSupport X s a).card ≤ ⌊X^a⌋₊)
  exact hc'.trans (Nat.floor_le (Real.rpow_pos_of_pos hX a).le)

theorem low_bound (X s a ε x y : ℝ) (hX : 0<X) (hx : 0≤x) (hyx : y≤x)
    (hpos : ∀m∈PositiveSharpRemainderAnalysisPhysical.support X s, 0<m)
    (hcap : ∀m∈PositiveSharpRemainderAnalysisPhysical.support X s,
      |PositiveSharpRemainderAnalysisPhysical.coefficient X s m|≤X^ε) :
    |low X s a x y| ≤ X^(a+ε) := by
  have hh := remainder_le_card (lowSupport X s a)
    (PositiveSharpRemainderAnalysisPhysical.coefficient X s) (x-y) x (X^ε)
    (fun m hm => hpos m (Finset.mem_filter.mp hm).1) (sub_nonneg.mpr hyx) hx
    (fun m hm => hcap m (Finset.mem_filter.mp hm).1)
  change |low X s a x y| ≤ _ at hh
  calc
    _ ≤ (lowSupport X s a).card * X^ε := hh
    _ ≤ X^a * X^ε := mul_le_mul_of_nonneg_right (low_card_le X s a hX hpos) (by positivity)
    _ = _ := (Real.rpow_add hX a ε).symm

theorem eventually_low_bound (s a ε : ℝ) (hs : 0<s) (hs1 : s≤1/1000) (hε : 0<ε) :
    ∀ᶠ X:ℝ in atTop, 1<X ∧ ∀x y:ℝ, 0≤x → y≤x → |low X s a x y|≤X^(a+ε) := by
  filter_upwards [PositiveSharpRemainderSupport.eventually_support_coefficient_cap s ε hs hs1 hε]
    with X hX
  refine ⟨hX.1, fun x y hx hyx => low_bound X s a ε x y (by linarith [hX.1]) hx hyx
    (fun m hm => (hX.2 m hm).1) (fun m hm => (hX.2 m hm).2.2)⟩

run_cmd do
  for decl in [``split, ``floor_error_le_one, ``remainder_le_card, ``low_card_le,
      ``low_bound, ``eventually_low_bound] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "SMALL PHYSICAL DIVISOR REMAINDER BOUND PASSED"

end MomentSmallRemainder
