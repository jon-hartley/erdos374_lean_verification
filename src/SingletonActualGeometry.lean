import FrontierResidual

/-! Arithmetic geometry for the actual low-small-divisor outer singleton.
The prime may be paired with the unit divisor. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace SingletonActualGeometry
open SieveBoxGrouping FourPrimeScaleBudget

theorem prime_product_unique (c : ℝ) (d e p q : ℕ)
    (_hd : 0 < d) (he : 0 < e) (hp : p.Prime) (hq : q.Prime)
    (_hdc : (d : ℝ) < c) (hec : (e : ℝ) < c)
    (hcp : c ≤ (p : ℝ)) (_hcq : c ≤ (q : ℝ))
    (h : d*p=e*q) : d=e ∧ p=q := by
  have hpdvd : p ∣ e*q := h ▸ Nat.dvd_mul_left p d
  have hpq : p=q := by
    rcases hp.dvd_mul.mp hpdvd with hpe | hpq
    · have hle : p ≤ e := Nat.le_of_dvd he hpe
      have hler : (p : ℝ) ≤ e := by exact_mod_cast hle
      linarith
    · exact (Nat.prime_dvd_prime_iff_eq hp hq).mp hpq
  refine ⟨?_,hpq⟩
  rw [hpq] at h
  exact Nat.eq_of_mul_eq_mul_right hq.pos h

theorem level_small_threshold (X s : ℝ) (hX : 0 ≤ X) :
    (SieveWeightedCutoffs.level X s)^(s^2)=X^lowerExponent s := by
  rw [SieveWeightedCutoffs.level, ←Real.rpow_mul hX]
  rfl

theorem low_positive (X s : ℝ) (d : ℕ)
    (hd : d ∈ FrontierSmallBracketSplit.lowSupport X s) : 0 < d := by
  exact SieveVectorConvolution.carrier_positive _ _ _
    (SieveSmallWeights.primes_prime _) d ((FrontierSmallBracketSplit.mem_lowSupport X s d).mp hd).1

theorem band_lower (X s z : ℝ) (hX : 1<X) (hs : 0<s) (hs1 : s≤1/1000)
    (j p : ℕ) (hp : p∈primeBand (SieveWeightedCutoffs.level X s) s z j) :
    X^lowerExponent s ≤ (p:ℝ) := by
  have hD : 1<SieveWeightedCutoffs.level X s := Real.one_lt_rpow hX (by linarith)
  have hscale := (SieveGeometricGrid.scale_strictMono _ s hD hs).monotone (Nat.zero_le j)
  rw [SieveGeometricGrid.scale_zero,level_small_threshold X s (by linarith)] at hscale
  exact hscale.trans ((mem_primeBand _ _ _ _ _).mp hp).2.2.1

theorem singleton_index_unique (X s z : ℝ) (hX : 1<X) (hs : 0<s)
    (hs1 : s≤1/1000) (hz : z≤SieveWeightedCutoffs.level X s)
    (j k d e p q : ℕ)
    (hd : d∈FrontierSmallBracketSplit.lowSupport X s)
    (he : e∈FrontierSmallBracketSplit.lowSupport X s)
    (hp : p∈primeBand (SieveWeightedCutoffs.level X s) s z j)
    (hq : q∈primeBand (SieveWeightedCutoffs.level X s) s z k)
    (h : d*p=e*q) : j=k ∧ d=e ∧ p=q := by
  obtain ⟨hde,hpq⟩ := prime_product_unique (X^lowerExponent s) d e p q
    (low_positive X s d hd) (low_positive X s e he)
    ((mem_primeBand _ _ _ _ _).mp hp).1 ((mem_primeBand _ _ _ _ _).mp hq).1
    ((FrontierSmallBracketSplit.mem_lowSupport X s d).mp hd).2
    ((FrontierSmallBracketSplit.mem_lowSupport X s e).mp he).2
    (band_lower X s z hX hs hs1 j p hp) (band_lower X s z hX hs hs1 k q hq) h
  have hD : 1<SieveWeightedCutoffs.level X s := Real.one_lt_rpow hX (by linarith)
  have hj := ((mem_primeBand_iff_index _ _ _ hD hs hz j p).mp hp).2
  have hk := ((mem_primeBand_iff_index _ _ _ hD hs hz k q).mp hq).2
  exact ⟨hj.symm.trans (hpq ▸ hk),hde,hpq⟩

theorem exponent_lt (s : ℝ) (hs : 0≤s) (hs1 : s≤1/1000) :
    lowerExponent s + SieveWeightedScalarBudget.alpha s < (31/125:ℝ) := by
  have hsq : s^2≤(1/1000000:ℝ) := by nlinarith
  have hlow : lowerExponent s ≤ s^2 := by
    unfold lowerExponent
    nlinarith [sq_nonneg s, mul_nonneg hs (sq_nonneg s)]
  unfold SieveWeightedScalarBudget.alpha
  linarith

theorem product_lt (X s z : ℝ) (hX : 1<X) (hs : 0<s) (hs1 : s≤1/1000)
    (hz : z≤X^(SieveWeightedScalarBudget.alpha s)) (j d p : ℕ)
    (hd : d∈FrontierSmallBracketSplit.lowSupport X s)
    (hp : p∈primeBand (SieveWeightedCutoffs.level X s) s z j) :
    (d*p:ℕ) < X^(31/125:ℝ) := by
  have hX0 : 0<X := by linarith
  have hdlt := ((FrontierSmallBracketSplit.mem_lowSupport X s d).mp hd).2
  have hpband := (mem_primeBand _ _ _ _ _).mp hp
  have hp0 : 0<(p:ℝ) := by exact_mod_cast hpband.1.pos
  have hprod : (d:ℝ)*p < X^lowerExponent s * X^(SieveWeightedScalarBudget.alpha s) :=
    mul_lt_mul hdlt (hpband.2.1.trans_le hz).le hp0 (Real.rpow_pos_of_pos hX0 _).le
  push_cast
  exact hprod.trans (by rw [←Real.rpow_add hX0]; exact Real.rpow_lt_rpow_of_exponent_lt hX (exponent_lt s hs.le hs1))

theorem fibre_singleton (D s z : ℝ) (j : ℕ) :
    fibre D s z [j] = (primeBand D s z j).image (fun p => [p]) := by
  ext t
  cases t with
  | nil => simp [mem_fibre]
  | cons p t =>
    cases t <;> simp [mem_fibre]

theorem low_singleton_kernel (X s z : ℝ) (j : ℕ) (f : ℕ→ℝ) :
    FrontierSmallBracketSplit.lowKernel X s z true [j] f =
      ∑d∈FrontierSmallBracketSplit.lowSupport X s,
        ∑p∈primeBand (SieveWeightedCutoffs.level X s) s z j,
          FrontierSmallBracket.smallWeight X s true d * f (d*p) := by
  unfold FrontierSmallBracketSplit.lowKernel
  rw [fibre_singleton]
  apply Finset.sum_congr rfl
  intro d _
  rw [Finset.sum_image (by intro a _ b _ h; simpa using h)]
  simp

run_cmd do
  for decl in [``prime_product_unique,``level_small_threshold,``low_positive,
      ``band_lower,``singleton_index_unique,``exponent_lt,``product_lt,
      ``fibre_singleton,``low_singleton_kernel] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ACTUAL LOW-D SINGLETON UNIQUENESS AND SUPPORT GEOMETRY PASSED"

end SingletonActualGeometry
