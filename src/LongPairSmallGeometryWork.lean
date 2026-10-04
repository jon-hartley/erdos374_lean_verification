import LongerTupleActualProfilesWork
import LongerTupleSectorWork
import TripleFlatParameters

/-! Literal length-two small-band geometry, including the actual small
divisor. This supplies support bounds, not a separable mean estimate. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Filter

namespace LongPairSmallGeometryWork
open SieveWeightedCutoffs SieveCappedUpperMainTerms SieveBoxedFamily
open LongerTupleActualProfiles LongerTupleSector PositiveSharpBoxedCount

theorem cutoffFour_sq (X s p : ℝ) (hX : 0<X) (hp : 0<p) :
    cutoffFour X s p ^ 2 = X^(SieveWeightedScalarBudget.upperExponent s)/p := by
  unfold cutoffFour
  rw [←Real.rpow_mul_natCast (by positivity : 0≤X^(SieveWeightedScalarBudget.upperExponent s)/p)]
  norm_num

theorem pair_product_lt (X s : ℝ) (p a b : ℕ) (hX : 0<X) (hp : 0<p)
    (ha : (a:ℝ)<cappedFourth X s p) (hb : (b:ℝ)<cappedFourth X s p)
    (hap : 0<a) (hbp : 0<b) :
    ((p*a*b:ℕ):ℝ)<X^(26/35-2*s:ℝ) := by
  have hp0 : (0:ℝ)<p := by exact_mod_cast hp
  have ha0 : (0:ℝ)<a := by exact_mod_cast hap
  have hb0 : (0:ℝ)<b := by exact_mod_cast hbp
  have haf : (a:ℝ)<cutoffFour X s p := ha.trans_le (min_le_right _ _)
  have hbf : (b:ℝ)<cutoffFour X s p := hb.trans_le (min_le_right _ _)
  have hab : (a:ℝ)*b < cutoffFour X s p ^ 2 := by
    nlinarith [mul_lt_mul haf hbf.le hb0 (four_pos X s p hX hp0).le]
  have hh := mul_lt_mul_of_pos_left hab hp0
  rw [cutoffFour_sq X s p hX hp0] at hh
  have he : (p:ℝ)*(X^(SieveWeightedScalarBudget.upperExponent s)/p) =
      X^(26/35-2*s:ℝ) := by
    unfold SieveWeightedScalarBudget.upperExponent
    field_simp
  simpa only [Nat.cast_mul,mul_assoc,he] using hh

theorem physical_pair_lt (X s : ℝ) (p d a b : ℕ) (hX : 1<X)
    (hs : 0<s) (hs1 : s≤1/1000) (hp : 0<p) (hD : 1<level X s/p)
    (hd : d∈SieveUpperBoxWindow.smallCarrier (level X s/p) s)
    (ht : [a,b]∈SieveUpperBoxing.outerFamily (level X s/p) s (cappedFourth X s p)) :
    ((p*d*a*b:ℕ):ℝ)<X^(26/35-s:ℝ) := by
  have hX0 : 0<X := by linarith
  have hp1 : (1:ℝ)≤p := by exact_mod_cast hp
  have hDX : level X s/p≤X :=
    (div_le_self (Real.rpow_nonneg hX0.le _) hp1).trans
      (PositiveSharpRemainderSupport.level_le_X X s hX.le hs.le)
  have hd0 : (0:ℝ)<d := by
    exact_mod_cast UpperAfter545Geometry.smallCarrier_pos _ _ d hd
  have hds : (d:ℝ)<X^s :=
    (PositiveSharpRemainderSupportGeometry.smallCarrier_lt _ s hD hs
      (by linarith) d hd).trans_le
        (Real.rpow_le_rpow (by linarith) hDX hs.le)
  have hpool := (LongerTupleGeometry.family_data _ s _ hD hs [a,b] (Or.inl ht)).1
  have ha := (mem_pool _ s _ a).mp (hpool a (by simp))
  have hb := (mem_pool _ s _ b).mp (hpool b (by simp))
  have hab := pair_product_lt X s p a b hX0 hp ha.2.1 hb.2.1 ha.1.pos hb.1.pos
  calc
    ((p*d*a*b:ℕ):ℝ) = (d:ℝ)*((p*a*b:ℕ):ℝ) := by push_cast; ring
    _ < (d:ℝ)*X^(26/35-2*s:ℝ) := mul_lt_mul_of_pos_left hab hd0
    _ ≤ X^s*X^(26/35-2*s:ℝ) := mul_le_mul_of_nonneg_right hds.le (by positivity)
    _ = X^(26/35-s:ℝ) := by rw [←Real.rpow_add hX0]; congr 1; ring

/-- Actual grouping is (p*d)*(a*b). Both factors have strict slack over
the flat theorem's lower scale exponents, before dyadic rounding. -/
theorem factor_lower (X s : ℝ) (p d a b : ℕ) (hX : 1<X)
    (hs : 0<s) (hs1 : s≤1/1000) (hp : p∈smallPrimes X s)
    (hd : 0<d) (hl : allLong X [a,b]) :
    X^(246/1000:ℝ)≤((p*d:ℕ):ℝ) ∧ X^(16/35:ℝ)<((a*b:ℕ):ℝ) := by
  have hX0 : 0<X := by linarith
  have hpband := PositiveSharpSieveDecomposition.small_band_bounds X s p hp
  have hp0 : (0:ℝ)<p := by exact_mod_cast hpband.1.pos
  have hd1 : (1:ℝ)≤d := by exact_mod_cast hd
  constructor
  · have halpha : (246/1000:ℝ)≤SieveWeightedScalarBudget.alpha s := by
      unfold SieveWeightedScalarBudget.alpha
      linarith
    calc
      _ ≤ X^(SieveWeightedScalarBudget.alpha s) :=
        Real.rpow_le_rpow_of_exponent_le hX.le halpha
      _ ≤ (p:ℝ) := hpband.2.1
      _ ≤ ((p*d:ℕ):ℝ) := by rw [Nat.cast_mul]; nlinarith
  · have ha := hl a (by simp)
    have hb := hl b (by simp)
    have hh := mul_lt_mul ha hb.le (Real.rpow_pos_of_pos hX0 _)
      (Nat.cast_nonneg a)
    rw [←Real.rpow_add hX0] at hh
    norm_num at hh
    simpa only [Nat.cast_mul] using hh

theorem small_band_physical_pair_lt (X s : ℝ) (p d a b : ℕ)
    (hX : 1<X) (hs : 0<s) (hs1 : s≤1/1000) (hlog : 1000≤Real.log X)
    (hp : p∈smallPrimes X s)
    (hd : d∈SieveUpperBoxWindow.smallCarrier (level X s/p) s)
    (ht : [a,b]∈SieveUpperBoxing.outerFamily (level X s/p) s (cappedFourth X s p)) :
    ((p*d*a*b:ℕ):ℝ)<X^(26/35-s:ℝ) ∧ ((p*d*a*b:ℕ):ℝ)<X^(26/35:ℝ) := by
  have hg := small_band_geometry X s hX hs hs1 hlog p hp
  have hh := physical_pair_lt X s p d a b hX hs hs1 (by omega) hg.2.2.1 hd ht
  exact ⟨hh,hh.trans_le (Real.rpow_le_rpow_of_exponent_le hX.le (by linarith))⟩

#print axioms small_band_physical_pair_lt
run_cmd do
  for decl in [``cutoffFour_sq, ``pair_product_lt, ``physical_pair_lt,
      ``factor_lower, ``small_band_physical_pair_lt] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"

end LongPairSmallGeometryWork
