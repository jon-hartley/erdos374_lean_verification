import PositiveSharpRemainderAnalysisPhysical

/-! Complete physical signed coefficients have fixed divisor-power growth.
The p-dependent upper families retain all their coefficients: only primes
dividing the physical index can contribute, and multiplication by p>0 has
one-point fibres. This is not a spatial mean-square or support-scale bound. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace PositiveSharpRemainderAnalysisCap
open PositiveSharpRemainderAnalysisPhysical PositiveSharpRemainderAnalysisBoxed
open PositiveSharpBoxedCount SieveWeightedCutoffs SieveWeightedScalarBudget
open SieveCappedUpperMainTerms (cappedFourth)

theorem inflatedCoefficient_eq_sum (p : ℕ) (S : Finset ℕ) (w : ℕ → ℝ) (m : ℕ) :
    inflatedCoefficient p S w m = ∑ k ∈ S.filter (fun k => p*k=m), w k := by
  unfold inflatedCoefficient FactoredDivisorWeights.coefficient
  rw [Finset.sum_filter, Finset.sum_product]
  simp only [Finset.sum_singleton, DirichletProductCoefficients.productIndex, one_mul]
  rw [Finset.sum_filter]

theorem inflatedSupport_dvd (p : ℕ) (S : Finset ℕ) (m : ℕ)
    (hm : m ∈ inflatedSupport p S) : p ∣ m := by
  obtain ⟨a, ha, he⟩ := Finset.mem_image.mp hm
  have hp := Finset.mem_singleton.mp (Finset.mem_product.mp ha).1
  refine ⟨a.2, ?_⟩
  simpa only [DirichletProductCoefficients.productIndex, hp] using he.symm

theorem inflatedCoefficient_abs_le (p : ℕ) (hp : 0<p) (S : Finset ℕ)
    (w : ℕ → ℝ) (m : ℕ) (B : ℝ) (hB : 0≤B)
    (hw : ∀ k ∈ S, p*k=m → |w k|≤B) : |inflatedCoefficient p S w m|≤B := by
  have hc : (S.filter (fun k => p*k=m)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    exact Nat.eq_of_mul_eq_mul_left hp
      ((Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm)
  rw [inflatedCoefficient_eq_sum]
  calc
    _ ≤ ∑ k ∈ S.filter (fun k => p*k=m), |w k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ S.filter (fun k => p*k=m), B := Finset.sum_le_sum
      (fun k hk => hw k (Finset.mem_filter.mp hk).1 (Finset.mem_filter.mp hk).2)
    _ = ((S.filter (fun k => p*k=m)).card : ℝ)*B := by simp
    _ ≤ 1*B := mul_le_mul_of_nonneg_right (by exact_mod_cast hc) hB
    _ = B := one_mul B

theorem upperCoefficient_abs_le_divisors (X s : ℝ) (P : Finset ℕ) (w : ℝ → ℝ)
    (m : ℕ) (hm : m≠0) (B : ℝ) (hB : 0≤B) (hp : ∀ p∈P, 0<p)
    (hc : ∀ p∈P, ∀ k∈SieveUpperBoxWindow.support (level X s/p) s (w p),
      p*k=m → |SieveUpperBoxWindow.coefficient (level X s/p) s (w p) k|≤B) :
    |upperCoefficient X s P w m| ≤ (m.divisors.card : ℝ)*B := by
  let F := P.filter (fun p => m ∈ inflatedSupport p
    (SieveUpperBoxWindow.support (level X s/p) s (w p)))
  have hsub : F ⊆ m.divisors := by
    intro p hpF
    exact Nat.mem_divisors.mpr ⟨inflatedSupport_dvd p _ m (Finset.mem_filter.mp hpF).2, hm⟩
  have he : upperCoefficient X s P w m = ∑ p∈F,
      inflatedCoefficient p (SieveUpperBoxWindow.support (level X s/p) s (w p))
        (SieveUpperBoxWindow.coefficient (level X s/p) s (w p)) m := by
    simp only [upperCoefficient, FiniteDivisorFamily.coefficient, F, Finset.sum_filter]
  rw [he]
  calc
    _ ≤ ∑ p∈F, |inflatedCoefficient p
        (SieveUpperBoxWindow.support (level X s/p) s (w p))
        (SieveUpperBoxWindow.coefficient (level X s/p) s (w p)) m| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _p∈F, B := by
      apply Finset.sum_le_sum
      intro p hpF
      have hpP := (Finset.mem_filter.mp hpF).1
      exact inflatedCoefficient_abs_le p (hp p hpP) _ _ m B hB (hc p hpP)
    _ = (F.card : ℝ)*B := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_card hsub) hB

theorem actual_upperCoefficient_abs_le (X s : ℝ) (P : Finset ℕ) (w : ℝ → ℝ)
    (m : ℕ) (hm : m≠0) (hp : ∀ p∈P, 0<p) :
    |upperCoefficient X s P w m| ≤
      2 * ((SieveBoxLength.cutoff s+2 : ℕ) : ℝ) *
        (m.divisors.card : ℝ)^(SieveBoxLength.cutoff s+2) := by
  have hh := upperCoefficient_abs_le_divisors X s P w m hm
    (2*((SieveBoxLength.cutoff s+2 : ℕ) : ℝ) *
      (m.divisors.card : ℝ)^(SieveBoxLength.cutoff s+1)) (by positivity) hp (by
      intro p _ k _ he
      have hk : k≠0 := by intro hk; simp only [hk, mul_zero] at he; exact hm he.symm
      have hdiv : k∣m := ⟨p, by simpa only [mul_comm] using he.symm⟩
      have hτ : (k.divisors.card : ℝ) ≤ m.divisors.card := by
        exact_mod_cast Finset.card_le_card (Nat.divisors_subset_of_dvd hm hdiv)
      exact (upper_coefficient_abs_le _ s _ k hk).trans
        (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (Nat.cast_nonneg _) hτ _) (by positivity)))
  convert hh using 1
  ring

theorem coefficient_abs_le_components (X s : ℝ) (m : ℕ) :
    |coefficient X s m| ≤
      |SieveBoxedWindow.coefficient (level X s) s (X^alpha s) m| +
      |upperCoefficient X s (largePrimes X) (cutoffThree X s) m| +
      |upperCoefficient X s (smallPrimes X s) (cappedFourth X s) m| := by
  calc
    _ ≤ ∑ i : Fin 3, |if m∈componentSupports X s i then componentCoefficients X s i m else 0| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin 3, |componentCoefficients X s i m| := by
      apply Finset.sum_le_sum
      intro i _
      split_ifs <;> simp
    _ = _ := by
      simp only [componentCoefficients, Fin.sum_univ_succ, Matrix.cons_val_zero,
        Matrix.cons_val_succ, Fin.sum_univ_zero, add_zero, abs_neg]
      ring

/-- This is the coefficient of the COMPLETE physical signed remainder. -/
theorem coefficient_abs_le (X s : ℝ) (m : ℕ) (hm : m≠0) :
    |coefficient X s m| ≤ 6*((SieveBoxLength.cutoff s+2 : ℕ) : ℝ) *
      (m.divisors.card : ℝ)^(SieveBoxLength.cutoff s+2) := by
  have hl := lower_coefficient_abs_le (level X s) s (X^alpha s) m hm
  have h1 := actual_upperCoefficient_abs_le X s (largePrimes X) (cutoffThree X s) m hm
    (fun p hp => (PositiveSharpSieveDecomposition.large_band_bounds X p hp).1.pos)
  have h2 := actual_upperCoefficient_abs_le X s (smallPrimes X s) (cappedFourth X s) m hm
    (fun p hp => (PositiveSharpSieveDecomposition.small_band_bounds X s p hp).1.pos)
  have ht : (1 : ℝ) ≤ m.divisors.card := by
    exact_mod_cast Finset.one_le_card.mpr ⟨1, Nat.one_mem_divisors.mpr hm⟩
  have hpow : (m.divisors.card : ℝ)^(SieveBoxLength.cutoff s+1) ≤
      (m.divisors.card : ℝ)^(SieveBoxLength.cutoff s+2) :=
    pow_le_pow_right₀ ht (by omega)
  have hl' := hl.trans (mul_le_mul_of_nonneg_left hpow
    (by positivity : 0≤2*((SieveBoxLength.cutoff s+2 : ℕ) : ℝ)))
  have hsum := coefficient_abs_le_components X s m
  linarith

theorem coefficient_power_bound (s ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ (X : ℝ) (m : ℕ), m≠0 → |coefficient X s m|≤C*(m : ℝ)^ε := by
  let K := SieveBoxLength.cutoff s+2
  have hk : (0 : ℝ)<K := by dsimp [K]; positivity
  obtain ⟨D, hD, hbound⟩ := DivisorPowerBound.divisor_count_bound (ε/K) (div_pos hε hk)
  refine ⟨6*(K : ℝ)*D^K, by positivity, ?_⟩
  intro X m hm
  have hp := pow_le_pow_left₀ (by positivity : (0 : ℝ)≤m.divisors.card) (hbound m) K
  have he : ((m : ℝ)^(ε/K))^K=(m : ℝ)^ε := by
    rw [←Real.rpow_mul_natCast (Nat.cast_nonneg m)]
    congr 1
    exact div_mul_cancel₀ ε hk.ne'
  rw [mul_pow, he] at hp
  calc
    _ ≤ 6*(K : ℝ)*(m.divisors.card : ℝ)^K := coefficient_abs_le X s m hm
    _ ≤ 6*(K : ℝ)*(D^K*(m : ℝ)^ε) := mul_le_mul_of_nonneg_left hp (by positivity)
    _ = _ := by ring

/-- Fixed s precedes the threshold; all physical indices up to X^2 are covered.
Membership of the whole physical support in that range is not asserted. -/
theorem eventually_complete_coefficient_cap (s ε : ℝ) (hε : 0<ε) :
    ∀ᶠ X : ℝ in Filter.atTop, 1≤X ∧ ∀ m : ℕ,
      m≠0 → (m : ℝ)≤X^(2 : ℕ) → |coefficient X s m|≤X^ε := by
  obtain ⟨C, hC, hb⟩ := coefficient_power_bound s (ε/4) (by positivity)
  filter_upwards [PolynomialLogEnvelope.eventually_constant_bound C (ε/2)
    hC.le (by positivity)] with X hX
  refine ⟨hX.1, ?_⟩
  intro m hm hmX
  have hXp : 0<X := by linarith [hX.1]
  have hp : (m : ℝ)^(ε/4)≤X^(ε/2) := by
    calc
      _ ≤ (X^(2 : ℕ))^(ε/4) := Real.rpow_le_rpow (Nat.cast_nonneg m) hmX (by positivity)
      _ = _ := by rw [←Real.rpow_natCast_mul hXp.le]; congr 1; ring
  calc
    _ ≤ C*(m : ℝ)^(ε/4) := hb X m hm
    _ ≤ X^(ε/2)*X^(ε/2) := mul_le_mul hX.2 hp (by positivity) (by positivity)
    _ = _ := by rw [←Real.rpow_add hXp]; congr 1; ring

run_cmd do
  for decl in [``inflatedCoefficient_eq_sum, ``inflatedSupport_dvd,
      ``inflatedCoefficient_abs_le, ``upperCoefficient_abs_le_divisors,
      ``actual_upperCoefficient_abs_le, ``coefficient_abs_le_components,
      ``coefficient_abs_le, ``coefficient_power_bound, ``eventually_complete_coefficient_cap] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "COMPLETE SIGNED REMAINDER COEFFICIENT GROWTH PASSED"

end PositiveSharpRemainderAnalysisCap
