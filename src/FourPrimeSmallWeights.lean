import SieveSmallWeights
import FourPrimeSourceBlock

/-! A constructed small-prime coefficient in the four-prime analytic block.
The bands are half-open with exponent 1+s^9, as in Iwaniec (1980), rather
than silently replacing them by the closed 1+s^7 bands in a later source.
The analytic adapter enlarges only its upper bound, keeping the actual finite
support unchanged. This does not prove the full sign-sensitive boxing sieve
inequality, or the main-term comparison for the complete family. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace FourPrimeSmallWeights

def band (a b z : ℝ) : Finset ℕ :=
  (SieveSmallWeights.pool b).filter (fun p => a ≤ (p : ℝ) ∧ (p : ℝ) < z)

theorem mem_band (a b z : ℝ) (p : ℕ) :
    p ∈ band a b z ↔ p.Prime ∧ a ≤ (p : ℝ) ∧ (p : ℝ) < b ∧ (p : ℝ) < z := by
  simp only [band, Finset.mem_filter, SieveSmallWeights.mem_pool]
  tauto

/-- Elementary outer restrictions; an inner-admissible strictly ordered
Iwaniec box satisfies these too. No analytic conclusion is a field. -/
structure Box (s X : ℝ) where
  D1 : ℝ
  D2 : ℝ
  D3 : ℝ
  D4 : ℝ
  scale_one : 1 ≤ D4
  order43 : D4 ≤ D3
  order32 : D3 ≤ D2
  order21 : D2 ≤ D1
  first_prefix : D1 * D2^3 ≤ X ^ (1-3*s)
  last_prefix : D1 * D2 * D3 * D4^3 ≤ X ^ (1-3*s)
  last_scale_lower : (X ^ (1-3*s)) ^ (s^2) ≤ D4

theorem enlargement_le (s a : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1) (ha : 1 ≤ a) :
    a ^ (1+s^9) ≤ a ^ (1+s^7) := by
  apply Real.rpow_le_rpow_of_exponent_le ha
  linarith [pow_le_pow_of_le_one hs hs1 (by decide : 7 ≤ 9)]

theorem inner_cutoff_le (D s : ℝ) (hD : 1 ≤ D) (hs : 0 ≤ s) :
    D ^ (1 / (1+s^9)) ≤ D := by
  have he : 1 / (1+s^9) ≤ (1 : ℝ) := by
    simpa only [one_div] using inv_le_one_of_one_le₀
      (show (1 : ℝ) ≤ 1+s^9 by linarith [pow_nonneg hs 9])
  simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hD he

/-- Direct construction from the stronger, strictly ordered inner-box tests.
The separate grid-enumeration/boxing inequality is not hidden in this adapter. -/
def innerBox (s X a1 a2 a3 a4 : ℝ) (hs : 0 < s) (hs1 : s < 1/100) (hX : 1 < X)
    (h43 : a4 < a3) (h32 : a3 < a2) (h21 : a2 < a1)
    (hsmall : (X^(1-3*s))^(s^2) ≤ a4)
    (hfirst : a1*a2^3 < (X^(1-3*s))^(1/(1+s^9)))
    (hlast : a1*a2*a3*a4^3 < (X^(1-3*s))^(1/(1+s^9))) : Box s X := by
  have hD : 1 < X^(1-3*s) := Real.one_lt_rpow hX (by linarith)
  have hu : 1 < (X^(1-3*s))^(s^2) := Real.one_lt_rpow hD (sq_pos_of_pos hs)
  exact {
    D1 := a1
    D2 := a2
    D3 := a3
    D4 := a4
    scale_one := hu.le.trans hsmall
    order43 := h43.le
    order32 := h32.le
    order21 := h21.le
    first_prefix := hfirst.le.trans (inner_cutoff_le _ s hD.le hs.le)
    last_prefix := hlast.le.trans (inner_cutoff_le _ s hD.le hs.le)
    last_scale_lower := hsmall }

def data (s X z : ℝ) (hs : 0 < s) (hs1 : s < 1/100) (hX : 1 < X)
    (B : Box s X) : FourPrimeSourceBlock.Data s X where
  S0 := SieveSmallWeights.support ((X^(1-3*s))^s) ((X^(1-3*s))^(s^2)) false
  S1 := band B.D1 (B.D1^(1+s^9)) z
  S2 := band B.D2 (B.D2^(1+s^9)) z
  S3 := band B.D3 (B.D3^(1+s^9)) z
  S4 := band B.D4 (B.D4^(1+s^9)) z
  C := SieveSmallWeights.lowerErrorCoefficient (X^(1-3*s)) s
  D1 := B.D1
  D2 := B.D2
  D3 := B.D3
  D4 := B.D4
  coefficient_bound := by
    intro m hm
    simpa [SieveSmallWeights.lowerErrorCoefficient] using
      SieveSmallWeights.weight_abs_le_one ((X^(1-3*s))^s) ((X^(1-3*s))^(s^2)) false m
  nu_positive := SieveSmallWeights.support_positive _ _ _
  primes1 := fun p hp => ((mem_band _ _ _ p).mp hp).1
  primes2 := fun p hp => ((mem_band _ _ _ p).mp hp).1
  primes3 := fun p hp => ((mem_band _ _ _ p).mp hp).1
  primes4 := fun p hp => ((mem_band _ _ _ p).mp hp).1
  scale_one := B.scale_one
  order43 := B.order43
  order32 := B.order32
  order21 := B.order21
  cubic_product := B.last_prefix
  last_scale_lower := B.last_scale_lower
  nu_upper := by
    obtain ⟨hT, hz⟩ := SieveSmallWeights.power_parameters (X^(1-3*s)) s
      (Real.one_lt_rpow hX (by linarith)) hs (by linarith)
    exact fun m hm => (SieveSmallWeights.support_lt _ _ _ hT hz m hm).le
  prime_upper1 := by
    intro p hp
    exact (((mem_band _ _ _ p).mp hp).2.2.1).le.trans
      (enlargement_le s B.D1 hs.le (by linarith)
        (B.scale_one.trans (B.order43.trans (B.order32.trans B.order21))))
  prime_upper2 := by
    intro p hp
    exact (((mem_band _ _ _ p).mp hp).2.2.1).le.trans
      (enlargement_le s B.D2 hs.le (by linarith)
        (B.scale_one.trans (B.order43.trans B.order32)))
  prime_upper3 := by
    intro p hp
    exact (((mem_band _ _ _ p).mp hp).2.2.1).le.trans
      (enlargement_le s B.D3 hs.le (by linarith) (B.scale_one.trans B.order43))
  prime_upper4 := by
    intro p hp
    exact (((mem_band _ _ _ p).mp hp).2.2.1).le.trans
      (enlargement_le s B.D4 hs.le (by linarith) B.scale_one)
  prime_lower4 := fun p hp => ((mem_band _ _ _ p).mp hp).2.1

theorem data_coefficient (s X z : ℝ) (hs : 0 < s) (hs1 : s < 1/100) (hX : 1 < X)
    (B : Box s X) (m : ℕ) :
    (data s X z hs hs1 hX B).C m =
      -SieveSmallWeights.weight ((X^(1-3*s))^s) ((X^(1-3*s))^(s^2)) false m := rfl

theorem data_nu_dvd (s X z : ℝ) (hs : 0 < s) (hs1 : s < 1/100) (hX : 1 < X)
    (B : Box s X) (m : ℕ) (hm : m ∈ (data s X z hs hs1 hX B).S0) :
    m ∣ SieveSmallWeights.primorial ((X^(1-3*s))^(s^2)) :=
  SieveSmallWeights.support_dvd_primorial _ _ _ m hm

/-- Uniform mean square for the literal constructed coefficient and bands.
All data are fixed during the x integral. Identification of the whole boxed
lower sieve remains a separate finite theorem. -/
theorem eventually_bound (s : ℝ) (hs : 0 < s) (hs1 : s < 1/100) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℝ in atTop, ∃ hX : 1 < X,
      ∀ (z : ℝ) (B : Box s X),
        let Y := FactoredDivisorVariableWindow.sourceWindow s X
        (1/X) * (∫ x in Icc X (2*X),
          FourPrimeSourceBlock.remainder (data s X z hs hs1 hX B)
            (x-x*(Y/X)) x ^ 2) ≤ Y^2 * X^(-c) := by
  obtain ⟨c, hc, he⟩ := FourPrimeSourceBlock.eventually_bound s hs hs1
  refine ⟨c, hc, ?_⟩
  filter_upwards [he, eventually_gt_atTop (1 : ℝ)] with X hh hX
  exact ⟨hX, fun z B => hh.2 (data s X z hs hs1 hX B)⟩

run_cmd do
  for decl in [``mem_band, ``enlargement_le, ``inner_cutoff_le, ``innerBox, ``data,
      ``data_coefficient, ``data_nu_dvd, ``eventually_bound] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "CONSTRUCTED SMALL-WEIGHT FOUR-PRIME BLOCK PASSED; FULL BOXING AND POSITIVITY OPEN"

end FourPrimeSmallWeights
end
