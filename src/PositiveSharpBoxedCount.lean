import PositiveSharpSieveDecomposition
import PositiveSharpDivisorAdapter
import SieveBoxedWeightedMainTerms

/-! The actual physical prime count is bounded below by the signed boxed
main terms and positive Buchstab contribution, minus a literal signed
floor remainder. No estimate of that remainder is asserted. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open scoped BigOperators
namespace PositiveSharpBoxedCount
open Real Erdos374.HarmanAnalytic151
open PositiveSharpSieveDecomposition PositiveSharpBuchstab
open SieveWeightedScalarBudget SieveWeightedCutoffs SieveBoxedWeightedMainTerms
open SieveCappedUpperMainTerms (cappedFourth)

def largePrimes (X : ℝ) : Finset ℕ := primeBand (firstCutoff X) (upperCutoff X)
def smallPrimes (X s : ℝ) : Finset ℕ := primeBand (lowerCutoff X s) (firstCutoff X)
def upperRemainders (X s L R : ℝ) (S : Finset ℕ) (w : ℝ → ℝ) : ℝ :=
  ∑ p∈S, SieveUpperBoxWindow.remainder (level X s/(p:ℝ)) s (w p) (L/(p:ℝ)) (R/(p:ℝ))
def signedRemainder (X s x y : ℝ) : ℝ :=
  SieveBoxedWindow.sourceRemainder (level X s) s (X^alpha s) (x-y) x+
    upperRemainders X s (x-y) x (largePrimes X) (cutoffThree X s)+
    upperRemainders X s (x-y) x (smallPrimes X s) (cappedFourth X s)
def signedMainTerm (X s : ℝ) : ℝ :=
  SieveBoxedWindow.mainTerm (level X s) s (X^alpha s)-
    boxedMass X s (largePrimes X) (cutoffThree X s)-
    boxedMass X s (smallPrimes X s) (cappedFourth X s)

theorem negative_sum_le_boxed (X s L R : ℝ) (hs : 0<s) (hL : 0≤L) (hLR : L≤R)
    (S : Finset ℕ) (w : ℝ → ℝ)
    (hg : ∀ p∈S, p.Prime ∧ w p≤(p:ℝ) ∧ 1<level X s/(p:ℝ) ∧
      w p≤level X s/(p:ℝ) ∧ (level X s/(p:ℝ))^(s^2)≤w p) :
    (∑ p∈S, ((sifted (divisorSlice (FiniteSieveWindow.window L R) p) ⌈w p⌉₊).card:ℝ)) ≤
      (R-L)*boxedMass X s S w+upperRemainders X s L R S w := by
  unfold boxedMass upperRemainders
  rw [Finset.mul_sum, ←Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro p hp
  obtain ⟨hpp,hwp,hT,hwT,hsmall⟩ := hg p hp
  have hp0 : 0<(p:ℝ) := by exact_mod_cast hpp.pos
  rw [PositiveSharpDivisorAdapter.sifted_divisorSlice_card L R (w p) p hL hLR hpp hwp]
  have hh := SieveUpperBoxWindow.sifted_count_le (level X s/(p:ℝ)) s (w p)
    hT hs hwT hsmall (L/(p:ℝ)) (R/(p:ℝ)) (div_nonneg hL hp0.le)
    (div_le_div_of_nonneg_right hLR hp0.le)
  convert hh using 1; ring

theorem first_geometry (X s : ℝ) (hX : 1<X) (hs : 0≤s) (hs1 : s≤1/1000) :
    1<level X s ∧ X^alpha s≤level X s ∧ (level X s)^(s^2)≤X^alpha s := by
  have he : 0<1-3*s := by linarith
  have ha := (exponent_geometry s hs hs1).1
  have hs2 : s^2≤(1/1000:ℝ)^2 := by gcongr
  refine ⟨one_lt_rpow hX he,?_,?_⟩
  · apply rpow_le_rpow_of_exponent_le hX.le
    unfold alpha
    linarith
  · rw [level, ←rpow_mul (by linarith : 0≤X)]
    apply rpow_le_rpow_of_exponent_le hX.le
    have hb := mul_le_mul_of_nonneg_right (show 1-3*s≤(1:ℝ) by linarith) (sq_nonneg s)
    nlinarith

theorem upper_geometry (X s p z : ℝ) (hX : 1<X) (hs : 0≤s) (hs1 : s≤1/1000)
    (hlog : 1000≤log X) (hp : 1≤p) (hz : X^(1/7:ℝ)≤z) (hc : z^3≤level X s/p) :
    1<level X s/p ∧ z≤level X s/p ∧ (level X s/p)^(s^2)≤z := by
  have hg := level_geometry X s p z hX hs hs1 hp hz
    ((two_le_floor_cutoff X hX hlog).trans hz) hc
  exact ⟨(one_lt_rpow hX (by norm_num : (0:ℝ)<3/7)).trans_le hg.1,hg.2.2.2,hg.2.2.1⟩

theorem first_lower (X s x y : ℝ) (hX : 1<X) (hs : 0<s) (hs1 : s≤1/1000)
    (hx : 0≤x-y) (hy : 0≤y) :
    y*SieveBoxedWindow.mainTerm (level X s) s (X^alpha s)-
      SieveBoxedWindow.sourceRemainder (level X s) s (X^alpha s) (x-y) x ≤
        firstSifted X s x y := by
  have hg := first_geometry X s hX hs.le hs1
  have hh := SieveBoxedWindow.source_main_sub_remainder_le_count (level X s) s (X^alpha s)
    hg.1 hs hg.2.1 hg.2.2 (x-y) x hx (by linarith)
  rw [←PositiveSharpDivisorAdapter.sifted_window_eq] at hh
  simpa only [firstSifted, lowerCutoff, window, FiniteSieveWindow.window, sub_sub_cancel] using hh

theorem large_negative_upper (X s x y : ℝ) (hX : 1<X) (hs : 0<s) (hs1 : s≤1/1000)
    (hlog : 1000≤log X) (hx : 0≤x-y) (hy : 0≤y) :
    largeNegative X s x y ≤ y*boxedMass X s (largePrimes X) (cutoffThree X s)+
      upperRemainders X s (x-y) x (largePrimes X) (cutoffThree X s) := by
  have hh := negative_sum_le_boxed X s (x-y) x hs hx (by linarith)
    (largePrimes X) (cutoffThree X s) (by
      intro p hp
      have hb := large_band_bounds X p hp
      have hg := three_geometry X s p hX hs.le hs1 hlog hb.2.1 hb.2.2
      have hu := upper_geometry X s p (cutoffThree X s p) hX hs.le hs1 hlog
        (by exact_mod_cast hb.1.one_le) hg.1 hg.2.2
      exact ⟨hb.1,SieveCappedUpperMainTerms.three_le_prime X s p hX hs.le hb.2.1,hu⟩)
  simpa only [largeNegative,largePrimes,innerCutoff,cutoffThree,level,sub_sub_cancel,window,
    FiniteSieveWindow.window] using hh

theorem small_negative_upper (X s x y : ℝ) (hX : 1<X) (hs : 0<s) (hs1 : s≤1/1000)
    (hlog : 1000≤log X) (hx : 0≤x-y) (hy : 0≤y) :
    smallNegative X s x y ≤ y*boxedMass X s (smallPrimes X s) (cappedFourth X s)+
      upperRemainders X s (x-y) x (smallPrimes X s) (cappedFourth X s) := by
  have hh := negative_sum_le_boxed X s (x-y) x hs hx (by linarith)
    (smallPrimes X s) (cappedFourth X s) (by
      intro p hp
      have hb := small_band_bounds X s p hp
      have hg := SieveCappedUpperMainTerms.capped_geometry X s p hX hs.le hs1 hb.2.1 hb.2.2.le
      have hu := upper_geometry X s p (cappedFourth X s p) hX hs.le hs1 hlog
        (by exact_mod_cast hb.1.one_le) hg.1 hg.2.2
      exact ⟨hb.1,hg.2.1,hu⟩)
  simpa only [smallNegative,smallPrimes,sub_sub_cancel,window,FiniteSieveWindow.window] using hh

theorem prime_count_lower (X s x y : ℝ) (hX : 8≤X) (hs : 0<s) (hs1 : s≤1/1000)
    (hlog : 1000≤log X) (hx : X≤x ∧ x≤2*X) (hy : 0<y ∧ y≤X/2) :
    y*signedMainTerm X s+(sourceTerm X s x y:ℝ)-signedRemainder X s x y ≤
      ((FiniteSieveWindow.primeWindow (x-y) x).card:ℝ) := by
  have hX1 : 1<X := by linarith
  have hl : 0≤x-y := by linarith [hx.1,hy.2]
  have hf := first_lower X s x y hX1 hs hs1 hl hy.1.le
  have hlarge := large_negative_upper X s x y hX1 hs hs1 hlog hl hy.1.le
  have hsmall := small_negative_upper X s x y hX1 hs hs1 hlog hl hy.1.le
  have hcount := PositiveSharpSieveDecomposition.prime_count_lower X s x y hX hs.le hx hy
  unfold signedMainTerm signedRemainder
  nlinarith

run_cmd do
  for decl in [``negative_sum_le_boxed, ``first_geometry, ``upper_geometry,
      ``first_lower, ``large_negative_upper, ``small_negative_upper, ``prime_count_lower] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ACTUAL PRIME COUNT >= SIGNED BOXED MAIN TERMS + SOURCE - EXACT SIGNED REMAINDER"
end PositiveSharpBoxedCount
end
