import PositiveSharpRemainderSupport

/-! Physical support geometry for two literal upper-tuple sectors.  The
prime-dependent level and every divisor in its small carrier are retained. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open scoped BigOperators

namespace UpperAfter545Geometry
open SieveWeightedCutoffs SieveUpperBoxing PositiveSharpBoxedCount
open PositiveSharpSieveDecomposition PositiveSharpRemainderSupportGeometry
open SieveCappedUpperMainTerms (cappedFourth)

theorem singleton_product_lt (X s p d q : ℝ) (hX : 1 < X)
    (hs : 0 < s) (hs1 : s ≤ 1/1000) (hp : 0 < p) (hd : 0 < d)
    (hq : 0 < q) (hsmall : d < (level X s/p)^s)
    (hcube : q^3 < level X s/p) (hshort : X^(8/35:ℝ) ≤ q) :
    p*d*q < X^(19/35:ℝ) := by
  have hX0 : 0 < X := by linarith
  have hD : 0 < level X s/p := div_pos (Real.rpow_pos_of_pos hX0 _) hp
  have hlogd := Real.log_lt_log hd hsmall
  rw [Real.log_rpow hD, level, Real.log_div (Real.rpow_pos_of_pos hX0 _).ne' hp.ne',
    Real.log_rpow hX0] at hlogd
  have hlogq := Real.log_lt_log (pow_pos hq 3) hcube
  rw [Real.log_pow, level, Real.log_div (Real.rpow_pos_of_pos hX0 _).ne' hp.ne',
    Real.log_rpow hX0] at hlogq
  have hlogshort := Real.log_le_log (Real.rpow_pos_of_pos hX0 _) hshort
  rw [Real.log_rpow hX0] at hlogshort
  have hweighted := mul_lt_mul_of_pos_left hlogq (show 0 < 1-s by linarith)
  have hweightedshort := mul_le_mul_of_nonneg_left hlogshort
    (show 0 ≤ 2-3*s by linarith)
  have hsL := mul_pos hs (Real.log_pos hX)
  apply (Real.log_lt_log_iff (mul_pos (mul_pos hp hd) hq)
    (Real.rpow_pos_of_pos hX0 _)).mp
  rw [Real.log_mul (mul_pos hp hd).ne' hq.ne', Real.log_mul hp.ne' hd.ne',
    Real.log_rpow hX0]
  push_cast at hweighted
  nlinarith

theorem empty_product_lt (X s p d : ℝ) (hX : 1 < X)
    (hs : 0 < s) (hs1 : s ≤ 1/1000) (hlog : 1000 ≤ Real.log X)
    (hp : 1 ≤ p) (hptop : p ≤ Real.sqrt (2*X)) (hd : 0 < d)
    (hsmall : d < (level X s/p)^s) : p*d < X^(19/35:ℝ) := by
  have hX0 : 0 < X := by linarith
  have hp0 : 0 < p := by linarith
  have hD : 0 < level X s/p := div_pos (Real.rpow_pos_of_pos hX0 _) hp0
  have hlogd := Real.log_lt_log hd hsmall
  rw [Real.log_rpow hD, level, Real.log_div (Real.rpow_pos_of_pos hX0 _).ne' hp0.ne',
    Real.log_rpow hX0] at hlogd
  have hlogp := Real.log_le_log hp0 hptop
  rw [Real.log_sqrt (by positivity), Real.log_mul (by norm_num) hX0.ne'] at hlogp
  have hlog2 := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num)
  have hlogp0 := Real.log_nonneg hp
  have hL := (Real.log_pos hX).le
  have hsLp := mul_nonneg hs.le hlogp0
  have hssL := mul_nonneg (sq_nonneg s) hL
  have hsL := mul_le_mul_of_nonneg_right hs1 hL
  apply (Real.log_lt_log_iff (mul_pos hp0 hd) (Real.rpow_pos_of_pos hX0 _)).mp
  rw [Real.log_mul hp0.ne' hd.ne', Real.log_rpow hX0]
  nlinarith

theorem smallCarrier_pos (D s : ℝ) (d : ℕ)
    (hd : d ∈ SieveUpperBoxWindow.smallCarrier D s) : 0 < d :=
  SieveVectorConvolution.carrier_positive _ _ _ (SieveSmallWeights.primes_prime _) d hd

theorem inner_singleton_cube (D s z : ℝ) (hD : 1 < D) (hs : 0 < s)
    (hz : z ≤ D) (q : ℕ) (ht : [q] ∈ innerFamily D s z) : (q:ℝ)^3 < D := by
  have ha := SieveUpperBoxFamily.inner_accepts D s z (SieveBoxLength.cutoff s)
    hD hs hz [q] ht
  simpa [SievePrefix.accepts, SieveRosser.cubicGate] using ha

/-- Every small divisor of the actual prime-dependent level is included. -/
theorem inner_singleton_physical_lt (X s z : ℝ) (p d q : ℕ)
    (hX : 1 < X) (hs : 0 < s) (hs1 : s ≤ 1/1000) (hp : 0 < p)
    (hD : 1 < level X s/p) (hz : z ≤ level X s/p)
    (hd : d ∈ SieveUpperBoxWindow.smallCarrier (level X s/p) s)
    (ht : [q] ∈ innerFamily (level X s/p) s z) (hshort : X^(8/35:ℝ) ≤ (q:ℝ)) :
    ((p*d*[q].prod : ℕ):ℝ) < X^(19/35:ℝ) := by
  have hqpool := ((mem_innerFamily _ _ _ hD hs [q]).mp ht).1 q (by simp)
  have hq := ((SieveBoxedFamily.mem_pool _ _ _ q).mp hqpool).1.pos
  have hdp := smallCarrier_pos _ _ d hd
  have hsmall := smallCarrier_lt _ _ hD hs (by linarith) d hd
  simpa using singleton_product_lt X s p d q hX hs hs1
    (by exact_mod_cast hp) (by exact_mod_cast hdp) (by exact_mod_cast hq)
    hsmall (inner_singleton_cube _ _ _ hD hs hz q ht) hshort

theorem empty_physical_lt (X s : ℝ) (p d : ℕ)
    (hX : 1 < X) (hs : 0 < s) (hs1 : s ≤ 1/1000) (hlog : 1000 ≤ Real.log X)
    (hp : 0 < p) (hptop : (p:ℝ) ≤ Real.sqrt (2*X)) (hD : 1 < level X s/p)
    (hd : d ∈ SieveUpperBoxWindow.smallCarrier (level X s/p) s) :
    ((p*d*([].prod:ℕ):ℕ):ℝ) < X^(19/35:ℝ) := by
  have hdp := smallCarrier_pos _ _ d hd
  simpa using empty_product_lt X s p d hX hs hs1 hlog
    (by exact_mod_cast hp) hptop (by exact_mod_cast hdp)
    (smallCarrier_lt _ _ hD hs (by linarith) d hd)

theorem large_geometry (X s : ℝ) (p : ℕ) (hX : 1 < X) (hs : 0 < s)
    (hs1 : s ≤ 1/1000) (hlog : 1000 ≤ Real.log X) (hp : p ∈ largePrimes X) :
    0 < p ∧ (p:ℝ) ≤ Real.sqrt (2*X) ∧ 1 < level X s/p ∧
      cutoffThree X s p ≤ level X s/p := by
  have hb := large_band_bounds X p hp
  have hg := three_geometry X s p hX hs.le hs1 hlog hb.2.1 hb.2.2
  have hu := upper_geometry X s p (cutoffThree X s p) hX hs.le hs1 hlog
    (by exact_mod_cast hb.1.one_le) hg.1 hg.2.2
  exact ⟨hb.1.pos,hb.2.2,hu.1,hu.2.1⟩

theorem small_geometry (X s : ℝ) (p : ℕ) (hX : 1 < X) (hs : 0 < s)
    (hs1 : s ≤ 1/1000) (hlog : 1000 ≤ Real.log X) (hp : p ∈ smallPrimes X s) :
    0 < p ∧ (p:ℝ) ≤ Real.sqrt (2*X) ∧ 1 < level X s/p ∧
      cappedFourth X s p ≤ level X s/p := by
  have hb := small_band_bounds X s p hp
  have hg := SieveCappedUpperMainTerms.capped_geometry X s p hX hs.le hs1 hb.2.1 hb.2.2.le
  have hu := upper_geometry X s p (cappedFourth X s p) hX hs.le hs1 hlog
    (by exact_mod_cast hb.1.one_le) hg.1 hg.2.2
  refine ⟨hb.1.pos,?_,hu.1,hu.2.1⟩
  calc
    (p:ℝ) ≤ X^(9/35:ℝ) := hb.2.2.le
    _ ≤ X^(1/2:ℝ) := Real.rpow_le_rpow_of_exponent_le hX.le (by norm_num)
    _ = Real.sqrt X := (Real.sqrt_eq_rpow X).symm
    _ ≤ Real.sqrt (2*X) := Real.sqrt_le_sqrt (by linarith)

theorem large_empty_physical_lt (X s : ℝ) (p d : ℕ)
    (hX : 1 < X) (hs : 0 < s) (hs1 : s ≤ 1/1000) (hlog : 1000 ≤ Real.log X)
    (hp : p ∈ largePrimes X) (hd : d ∈ SieveUpperBoxWindow.smallCarrier (level X s/p) s) :
    ((p*d*([].prod:ℕ):ℕ):ℝ) < X^(19/35:ℝ) := by
  have hg := large_geometry X s p hX hs hs1 hlog hp
  exact empty_physical_lt X s p d hX hs hs1 hlog hg.1 hg.2.1 hg.2.2.1 hd

theorem small_empty_physical_lt (X s : ℝ) (p d : ℕ)
    (hX : 1 < X) (hs : 0 < s) (hs1 : s ≤ 1/1000) (hlog : 1000 ≤ Real.log X)
    (hp : p ∈ smallPrimes X s) (hd : d ∈ SieveUpperBoxWindow.smallCarrier (level X s/p) s) :
    ((p*d*([].prod:ℕ):ℕ):ℝ) < X^(19/35:ℝ) := by
  have hg := small_geometry X s p hX hs hs1 hlog hp
  exact empty_physical_lt X s p d hX hs hs1 hlog hg.1 hg.2.1 hg.2.2.1 hd

theorem large_singleton_physical_lt (X s : ℝ) (p d q : ℕ)
    (hX : 1 < X) (hs : 0 < s) (hs1 : s ≤ 1/1000) (hlog : 1000 ≤ Real.log X)
    (hp : p ∈ largePrimes X) (hd : d ∈ SieveUpperBoxWindow.smallCarrier (level X s/p) s)
    (ht : [q] ∈ innerFamily (level X s/p) s (cutoffThree X s p))
    (hshort : X^(8/35:ℝ) ≤ (q:ℝ)) :
    ((p*d*[q].prod:ℕ):ℝ) < X^(19/35:ℝ) := by
  have hg := large_geometry X s p hX hs hs1 hlog hp
  exact inner_singleton_physical_lt X s _ p d q hX hs hs1 hg.1 hg.2.2.1 hg.2.2.2 hd ht hshort

theorem small_singleton_physical_lt (X s : ℝ) (p d q : ℕ)
    (hX : 1 < X) (hs : 0 < s) (hs1 : s ≤ 1/1000) (hlog : 1000 ≤ Real.log X)
    (hp : p ∈ smallPrimes X s) (hd : d ∈ SieveUpperBoxWindow.smallCarrier (level X s/p) s)
    (ht : [q] ∈ innerFamily (level X s/p) s (cappedFourth X s p))
    (hshort : X^(8/35:ℝ) ≤ (q:ℝ)) :
    ((p*d*[q].prod:ℕ):ℝ) < X^(19/35:ℝ) := by
  have hg := small_geometry X s p hX hs hs1 hlog hp
  exact inner_singleton_physical_lt X s _ p d q hX hs hs1 hg.1 hg.2.2.1 hg.2.2.2 hd ht hshort

theorem physical_le_545 (X : ℝ) (m : ℕ) (hX : 1 ≤ X) (hm : (m:ℝ) < X^(19/35:ℝ)) :
    (m:ℝ) ≤ X^(109/200:ℝ) :=
  hm.le.trans (Real.rpow_le_rpow_of_exponent_le hX (by norm_num))

run_cmd do
  for decl in [``singleton_product_lt, ``empty_product_lt, ``smallCarrier_pos,
      ``inner_singleton_cube, ``inner_singleton_physical_lt, ``empty_physical_lt,
      ``large_geometry, ``small_geometry, ``large_empty_physical_lt,
      ``small_empty_physical_lt, ``large_singleton_physical_lt,
      ``small_singleton_physical_lt, ``physical_le_545] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "UPPER EMPTY AND NO-SHORT SINGLETON PHYSICAL GEOMETRY PASSED"

end UpperAfter545Geometry
