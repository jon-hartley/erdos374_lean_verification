import PositiveSharpRemainderSupport

/-! A strictly sublinear bound for the complete physical remainder support.
All actual boxed families, signs and multiplicities are unchanged. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace MomentRemainderSupport
open PositiveSharpRemainderAnalysisPhysical PositiveSharpRemainderSupportGeometry
open PositiveSharpBoxedCount PositiveSharpSieveDecomposition
open SieveWeightedCutoffs SieveWeightedScalarBudget
open SieveCappedUpperMainTerms (cappedFourth)

def boxedExponent (s : ℝ) : ℝ := s+SieveGeometricGrid.ratio s

theorem boxedExponent_ge_one (s : ℝ) (hs : 0≤s) : 1≤boxedExponent s := by
  unfold boxedExponent SieveGeometricGrid.ratio
  linarith [pow_nonneg hs 9]

theorem exponent_saving (s : ℝ) (hs : 0≤s) (hs1 : s≤1/3) :
    (1-3*s)*boxedExponent s≤1-2*s := by
  have h9 : s^9≤s^2 := pow_le_pow_of_le_one hs (by linarith) (by decide)
  have hh := mul_le_mul_of_nonneg_left h9 (show 0≤1-3*s by linarith)
  unfold boxedExponent SieveGeometricGrid.ratio
  have hnon : 0≤s^3 := by positivity
  nlinarith

theorem signed_support_lt_power (D s : ℝ) (hD : 1<D) (hs : 0<s) (hs1 : s≤1)
    (I O : Finset (List ℕ))
    (ht : ∀t∈I∪O, (t.prod:ℝ)≤D^(SieveGeometricGrid.ratio s))
    (m : ℕ) (hm : m∈SieveTupleConvolution.signedSupport
      (SieveUpperBoxWindow.smallCarrier D s) I O) : (m:ℝ)<D^(boxedExponent s) := by
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hm
  obtain ⟨ha,hb⟩ := Finset.mem_product.mp ha
  obtain ⟨t,ht',he⟩ := (SieveTupleConvolution.mem_tupleSupport _ _).mp hb
  have hsmall := smallCarrier_lt D s hD hs hs1 a.1 ha
  have hlarge : (a.2:ℝ)≤D^(SieveGeometricGrid.ratio s) := by
    simpa only [he] using ht t ht'
  calc
    _ = (a.1:ℝ)*(a.2:ℝ) := by simp [DirichletProductCoefficients.productIndex]
    _ ≤ (a.1:ℝ)*D^(SieveGeometricGrid.ratio s) :=
      mul_le_mul_of_nonneg_left hlarge (Nat.cast_nonneg _)
    _ < D^s*D^(SieveGeometricGrid.ratio s) :=
      mul_lt_mul_of_pos_right hsmall (Real.rpow_pos_of_pos (by linarith) _)
    _ = D^(boxedExponent s) := (Real.rpow_add (by linarith) _ _).symm

theorem lower_support_lt_power (D s z : ℝ) (hD : 1<D) (hs : 0<s)
    (hs1 : s≤1) (hz : z≤D) (m : ℕ) (hm : m∈SieveBoxedWindow.support D s z) :
    (m:ℝ)<D^(boxedExponent s) :=
  signed_support_lt_power D s hD hs hs1 _ _ (lower_tuple_product_le D s z hD hs hz) m hm

theorem upper_support_lt_power (D s z : ℝ) (hD : 1<D) (hs : 0<s)
    (hs1 : s≤1) (hz : z≤D) (m : ℕ) (hm : m∈SieveUpperBoxWindow.support D s z) :
    (m:ℝ)<D^(boxedExponent s) :=
  signed_support_lt_power D s hD hs hs1 _ _ (upper_tuple_product_le D s z hD hs hz) m hm

theorem level_power_le (X s : ℝ) (hX : 1≤X) (hs : 0≤s) (hs1 : s≤1/3) :
    (level X s)^(boxedExponent s)≤X^(1-2*s) := by
  rw [level, ←Real.rpow_mul (by linarith : 0≤X)]
  exact Real.rpow_le_rpow_of_exponent_le hX (exponent_saving s hs hs1)

theorem prime_factor_power_le (D p b : ℝ) (hD : 0≤D) (hp : 1≤p) (hb : 1≤b) :
    p*(D/p)^b≤D^b := by
  have hp0 : 0<p := by linarith
  calc
    _ ≤ p^b*(D/p)^b := mul_le_mul_of_nonneg_right
      (Real.self_le_rpow_of_one_le hp hb) (Real.rpow_nonneg (div_nonneg hD hp0.le) _)
    _ = (p*(D/p))^b := (Real.mul_rpow hp0.le (div_nonneg hD hp0.le)).symm
    _ = D^b := by rw [mul_div_cancel₀ D hp0.ne']

theorem upper_physical_lt_power (X s : ℝ) (P : Finset ℕ) (w : ℝ→ℝ)
    (hX : 1<X) (hs : 0<s) (hs1 : s≤1/3)
    (hp : ∀p∈P, 0<p)
    (hg : ∀p∈P, 1<level X s/(p:ℝ) ∧ w p≤level X s/(p:ℝ))
    (m : ℕ) (hm : m∈upperSupport X s P w) : (m:ℝ)<X^(1-2*s) := by
  obtain ⟨p,hpP,hm⟩ := Finset.mem_biUnion.mp hm
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hm
  obtain ⟨hap,hak⟩ := Finset.mem_product.mp ha
  have hap' : a.1=p := Finset.mem_singleton.mp hap
  have hp0 : 0<(p:ℝ) := by exact_mod_cast hp p hpP
  have hp1 : 1≤(p:ℝ) := by exact_mod_cast hp p hpP
  have hgeom := hg p hpP
  have hk := upper_support_lt_power _ _ _ hgeom.1 hs (by linarith) hgeom.2 a.2 hak
  calc
    _ = (p:ℝ)*(a.2:ℝ) := by
      simp only [DirichletProductCoefficients.productIndex, Nat.cast_mul, hap']
    _ < (p:ℝ)*(level X s/(p:ℝ))^(boxedExponent s) := mul_lt_mul_of_pos_left hk hp0
    _ ≤ (level X s)^(boxedExponent s) := prime_factor_power_le _ _ _
      (Real.rpow_nonneg (by linarith) _) hp1 (boxedExponent_ge_one s hs.le)
    _ ≤ X^(1-2*s) := level_power_le X s hX.le hs.le hs1

theorem large_support_lt_power (X s : ℝ) (hX : 1<X) (hs : 0<s)
    (hs1 : s≤1/1000) (hlog : 1000≤Real.log X)
    (m : ℕ) (hm : m∈upperSupport X s (largePrimes X) (cutoffThree X s)) :
    (m:ℝ)<X^(1-2*s) := by
  apply upper_physical_lt_power X s _ _ hX hs (by linarith)
    (fun p hp => (large_band_bounds X p hp).1.pos) _ m hm
  intro p hp
  have hb := large_band_bounds X p hp
  have hg := three_geometry X s p hX hs.le hs1 hlog hb.2.1 hb.2.2
  have hu := upper_geometry X s p (cutoffThree X s p) hX hs.le hs1 hlog
    (by exact_mod_cast hb.1.one_le) hg.1 hg.2.2
  exact ⟨hu.1,hu.2.1⟩

theorem small_support_lt_power (X s : ℝ) (hX : 1<X) (hs : 0<s)
    (hs1 : s≤1/1000) (hlog : 1000≤Real.log X)
    (m : ℕ) (hm : m∈upperSupport X s (smallPrimes X s) (cappedFourth X s)) :
    (m:ℝ)<X^(1-2*s) := by
  apply upper_physical_lt_power X s _ _ hX hs (by linarith)
    (fun p hp => (small_band_bounds X s p hp).1.pos) _ m hm
  intro p hp
  have hb := small_band_bounds X s p hp
  have hg := SieveCappedUpperMainTerms.capped_geometry X s p hX hs.le hs1 hb.2.1 hb.2.2.le
  have hu := upper_geometry X s p (cappedFourth X s p) hX hs.le hs1 hlog
    (by exact_mod_cast hb.1.one_le) hg.1 hg.2.2
  exact ⟨hu.1,hu.2.1⟩

/-- No support member is omitted, and the cofactor prime remains part of
the physical index. The upper power is strictly below X for fixed s>0. -/
theorem support_lt_power (X s : ℝ) (hX : 1<X) (hs : 0<s)
    (hs1 : s≤1/1000) (hlog : 1000≤Real.log X)
    (m : ℕ) (hm : m∈PositiveSharpRemainderAnalysisPhysical.support X s) :
    0<m ∧ (m:ℝ)<X^(1-2*s) := by
  refine ⟨(PositiveSharpRemainderSupport.support_bounds X s hX hs hs1 hlog m hm).1,?_⟩
  obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hm
  fin_cases i
  · change m∈SieveBoxedWindow.support (level X s) s (X^alpha s) at hi
    have hg := first_geometry X s hX hs.le hs1
    exact (lower_support_lt_power _ _ _ hg.1 hs (by linarith) hg.2.1 m hi).trans_le
      (level_power_le X s hX.le hs.le (by linarith))
  · exact large_support_lt_power X s hX hs hs1 hlog m hi
  · exact small_support_lt_power X s hX hs hs1 hlog m hi

theorem support_lt_X (X s : ℝ) (hX : 1<X) (hs : 0<s)
    (hs1 : s≤1/1000) (hlog : 1000≤Real.log X)
    (m : ℕ) (hm : m∈PositiveSharpRemainderAnalysisPhysical.support X s) : (m:ℝ)<X := by
  exact (support_lt_power X s hX hs hs1 hlog m hm).2.trans_le
    (Real.rpow_le_self_of_one_le hX.le (by linarith))

theorem eventually_support_and_coefficient (s ε : ℝ) (hs : 0<s)
    (hs1 : s≤1/1000) (hε : 0<ε) :
    ∀ᶠ X : ℝ in Filter.atTop, 1<X ∧ ∀m∈PositiveSharpRemainderAnalysisPhysical.support X s,
      0<m ∧ (m:ℝ)<X^(1-2*s) ∧ |PositiveSharpRemainderAnalysisPhysical.coefficient X s m|≤X^ε := by
  filter_upwards [PositiveSharpRemainderSupport.eventually_support_coefficient_cap s ε hs hs1 hε,
    Real.tendsto_log_atTop.eventually (Filter.eventually_ge_atTop 1000)] with X hcap hlog
  refine ⟨hcap.1,?_⟩
  intro m hm
  have hb := support_lt_power X s hcap.1 hs hs1 hlog m hm
  exact ⟨hb.1,hb.2,(hcap.2 m hm).2.2⟩

run_cmd do
  for decl in [``boxedExponent_ge_one, ``exponent_saving, ``signed_support_lt_power,
      ``lower_support_lt_power, ``upper_support_lt_power, ``level_power_le,
      ``prime_factor_power_le, ``upper_physical_lt_power, ``large_support_lt_power,
      ``small_support_lt_power, ``support_lt_power, ``support_lt_X,
      ``eventually_support_and_coefficient] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "STRICTLY SUB-X COMPLETE PHYSICAL SUPPORT PASSED"

end MomentRemainderSupport
