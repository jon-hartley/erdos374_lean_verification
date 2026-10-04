import UpperAfter545Geometry

/-! The fourth-cutoff branch puts every small-prime singleton, including
ones with a short tuple prime, strictly below the physical square root. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section

namespace UpperAfter545SmallSingleton
open SieveWeightedCutoffs SieveUpperBoxing PositiveSharpBoxedCount
open SieveWeightedScalarBudget UpperAfter545Geometry
open SieveCappedUpperMainTerms (cappedFourth)

theorem fourth_singleton_product_lt (X s p d q : ℝ) (hX : 1 < X)
    (hs : 0 < s) (hs1 : s ≤ 1/1000) (hp : 0 < p) (hd : 0 < d)
    (hq : 0 < q) (hsmall : d < (level X s/p)^s)
    (hfour : q < cutoffFour X s p) (hptop : p ≤ X^(9/35:ℝ)) :
    p*d*q < X^(1/2:ℝ) := by
  have hX0 : 0 < X := by linarith
  have hD : 0 < level X s/p := div_pos (Real.rpow_pos_of_pos hX0 _) hp
  have hlogd := Real.log_lt_log hd hsmall
  rw [Real.log_rpow hD, level, Real.log_div (Real.rpow_pos_of_pos hX0 _).ne' hp.ne',
    Real.log_rpow hX0] at hlogd
  have hlogq := Real.log_lt_log hq hfour
  rw [log_four X s p hX0 hp, upperExponent] at hlogq
  have hlogp := Real.log_le_log hp hptop
  rw [Real.log_rpow hX0] at hlogp
  have hweighted := mul_le_mul_of_nonneg_left hlogp (show 0 ≤ 1/2-s by linarith)
  have hsL := mul_pos hs (Real.log_pos hX)
  have hssL := mul_nonneg (sq_nonneg s) (Real.log_pos hX).le
  apply (Real.log_lt_log_iff (mul_pos (mul_pos hp hd) hq)
    (Real.rpow_pos_of_pos hX0 _)).mp
  rw [Real.log_mul (mul_pos hp hd).ne' hq.ne', Real.log_mul hp.ne' hd.ne',
    Real.log_rpow hX0]
  nlinarith

theorem small_singleton_physical_lt_sqrt (X s : ℝ) (p d q : ℕ)
    (hX : 1 < X) (hs : 0 < s) (hs1 : s ≤ 1/1000) (hlog : 1000 ≤ Real.log X)
    (hp : p ∈ smallPrimes X s) (hd : d ∈ SieveUpperBoxWindow.smallCarrier (level X s/p) s)
    (ht : [q] ∈ innerFamily (level X s/p) s (cappedFourth X s p)) :
    ((p*d*[q].prod:ℕ):ℝ) < X^(1/2:ℝ) := by
  have hg := small_geometry X s p hX hs hs1 hlog hp
  have hb := PositiveSharpSieveDecomposition.small_band_bounds X s p hp
  have hqpool := ((mem_innerFamily _ _ _ hg.2.2.1 hs [q]).mp ht).1 q (by simp)
  have hqp := (SieveBoxedFamily.mem_pool _ _ _ q).mp hqpool
  have hdp := smallCarrier_pos _ _ d hd
  have hsmall := PositiveSharpRemainderSupportGeometry.smallCarrier_lt
    _ _ hg.2.2.1 hs (by linarith) d hd
  have hfour : (q:ℝ) < cutoffFour X s p :=
    hqp.2.1.trans_le (min_le_right _ _)
  simpa using fourth_singleton_product_lt X s p d q hX hs hs1
    (by exact_mod_cast hg.1) (by exact_mod_cast hdp) (by exact_mod_cast hqp.1.pos)
    hsmall hfour hb.2.2.le

theorem small_singleton_physical_le_545 (X s : ℝ) (p d q : ℕ)
    (hX : 1 < X) (hs : 0 < s) (hs1 : s ≤ 1/1000) (hlog : 1000 ≤ Real.log X)
    (hp : p ∈ smallPrimes X s) (hd : d ∈ SieveUpperBoxWindow.smallCarrier (level X s/p) s)
    (ht : [q] ∈ innerFamily (level X s/p) s (cappedFourth X s p)) :
    ((p*d*[q].prod:ℕ):ℝ) ≤ X^(109/200:ℝ) :=
  (small_singleton_physical_lt_sqrt X s p d q hX hs hs1 hlog hp hd ht).le.trans
    (Real.rpow_le_rpow_of_exponent_le hX.le (by norm_num))

run_cmd do
  for decl in [``fourth_singleton_product_lt, ``small_singleton_physical_lt_sqrt,
      ``small_singleton_physical_le_545] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ALL SMALL-PRIME SINGLETONS BELOW THE PHYSICAL SQUARE ROOT PASSED"

end UpperAfter545SmallSingleton
