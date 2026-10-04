import UpperAfter545Geometry

/-! Geometry for the literal surviving large-prime upper singleton. The
grouped factor is p*d with every d in the actual prime-dependent carrier.
The rectangle bounds apply to all cross-pairs in the global factor ranges. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section

namespace ShortSingletonGeometry
open SieveWeightedCutoffs PositiveSharpBoxedCount PositiveSharpSieveDecomposition
open UpperAfter545Geometry

theorem sqrt_two_mul_le (X : ℝ) (hX : 1 < X) (hlog : 1000 ≤ Real.log X) :
    Real.sqrt (2*X) ≤ X^(1001/2000:ℝ) := by
  have hX0 : 0 < X := by linarith
  apply (Real.log_le_log_iff (Real.sqrt_pos.mpr (by positivity))
    (Real.rpow_pos_of_pos hX0 _)).mp
  rw [Real.log_sqrt (by positivity), Real.log_mul (by norm_num) hX0.ne', Real.log_rpow hX0]
  have ht := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num)
  linarith

theorem actual_small_divisor_bound (X s : ℝ) (p d : ℕ)
    (hX : 1 < X) (hs : 0 < s) (hs1 : s ≤ 1/1000) (hlog : 1000 ≤ Real.log X)
    (hp : p ∈ largePrimes X) (hd : d ∈ SieveUpperBoxWindow.smallCarrier (level X s/p) s) :
    0 < d ∧ (d:ℝ) < X^(1/1000:ℝ) := by
  have hg := large_geometry X s p hX hs hs1 hlog hp
  have hp1 : (1:ℝ) ≤ p := by exact_mod_cast hg.1
  have hX0 : 0 < X := by linarith
  have hDX : level X s/p ≤ X :=
    (div_le_self (Real.rpow_nonneg hX0.le _) hp1).trans
      (PositiveSharpRemainderSupport.level_le_X X s hX.le hs.le)
  refine ⟨smallCarrier_pos _ _ d hd,?_⟩
  calc
    (d:ℝ) < (level X s/p)^s :=
      PositiveSharpRemainderSupportGeometry.smallCarrier_lt _ _ hg.2.2.1 hs (by linarith) d hd
    _ ≤ X^s := Real.rpow_le_rpow (by linarith [hg.2.2.1]) hDX hs.le
    _ ≤ X^(1/1000:ℝ) := Real.rpow_le_rpow_of_exponent_le hX.le hs1

theorem actual_grouped_bounds (X s : ℝ) (p d : ℕ)
    (hX : 1 < X) (hs : 0 < s) (hs1 : s ≤ 1/1000) (hlog : 1000 ≤ Real.log X)
    (hp : p ∈ largePrimes X) (hd : d ∈ SieveUpperBoxWindow.smallCarrier (level X s/p) s) :
    X^(9/35:ℝ) ≤ ((p*d:ℕ):ℝ) ∧ ((p*d:ℕ):ℝ) < X^(1003/2000:ℝ) := by
  have hb := large_band_bounds X p hp
  have hd' := actual_small_divisor_bound X s p d hX hs hs1 hlog hp hd
  have hp0 : (0:ℝ) < p := by exact_mod_cast hb.1.pos
  have hd1 : (1:ℝ) ≤ d := by exact_mod_cast hd'.1
  have hX0 : 0 < X := by linarith
  constructor
  · simpa only [Nat.cast_mul] using hb.2.1.trans (le_mul_of_one_le_right hp0.le hd1)
  · calc
      ((p*d:ℕ):ℝ) = (p:ℝ)*(d:ℝ) := by norm_cast
      _ < (p:ℝ)*X^(1/1000:ℝ) := mul_lt_mul_of_pos_left hd'.2 hp0
      _ ≤ X^(1001/2000:ℝ)*X^(1/1000:ℝ) :=
        mul_le_mul_of_nonneg_right (hb.2.2.trans (sqrt_two_mul_le X hX hlog)) (by positivity)
      _ = X^(1003/2000:ℝ) := by rw [←Real.rpow_add hX0]; norm_num

theorem high_implies_short_lower (X s : ℝ) (p d q : ℕ)
    (hX : 1 < X) (hs : 0 < s) (hs1 : s ≤ 1/1000) (hlog : 1000 ≤ Real.log X)
    (hp : p ∈ largePrimes X) (hd : d ∈ SieveUpperBoxWindow.smallCarrier (level X s/p) s)
    (hhigh : X^(109/200:ℝ) < ((p*d*q:ℕ):ℝ)) : X^(1/25:ℝ) < (q:ℝ) := by
  have hX0 : 0 < X := by linarith
  have hm := (actual_grouped_bounds X s p d hX hs hs1 hlog hp hd).2
  by_contra hq
  have hq' : (q:ℝ) ≤ X^(1/25:ℝ) := le_of_not_gt hq
  have hb : ((p*d*q:ℕ):ℝ) ≤ X^(109/200:ℝ) := by
    calc
      ((p*d*q:ℕ):ℝ) = ((p*d:ℕ):ℝ)*(q:ℝ) := by norm_cast
      _ ≤ ((p*d:ℕ):ℝ)*X^(1/25:ℝ) :=
        mul_le_mul_of_nonneg_left hq' (Nat.cast_nonneg _)
      _ ≤ X^(1003/2000:ℝ)*X^(1/25:ℝ) := mul_le_mul_of_nonneg_right hm.le (by positivity)
      _ = X^(1083/2000:ℝ) := by rw [←Real.rpow_add hX0]; norm_num
      _ ≤ X^(109/200:ℝ) := Real.rpow_le_rpow_of_exponent_le hX.le (by norm_num)
  exact (not_lt_of_ge hb) hhigh

/-- Uniform on all cross-pairs from the global factor ranges. -/
theorem full_rectangle_product_lt (X m q : ℝ) (hX : 1 < X) (hm0 : 0 ≤ m)
    (hm : m < X^(1003/2000:ℝ)) (hq : q ≤ X^(8/35:ℝ)) : m*q < X^(731/1000:ℝ) := by
  have hX0 : 0 < X := by linarith
  calc
    m*q ≤ m*X^(8/35:ℝ) := mul_le_mul_of_nonneg_left hq hm0
    _ < X^(1003/2000:ℝ)*X^(8/35:ℝ) :=
      mul_lt_mul_of_pos_right hm (Real.rpow_pos_of_pos hX0 _)
    _ = X^((1003/2000:ℝ)+8/35) := (Real.rpow_add hX0 _ _).symm
    _ ≤ X^(731/1000:ℝ) := Real.rpow_le_rpow_of_exponent_le hX.le (by norm_num)

theorem actual_surviving_bounds (X s : ℝ) (p d q : ℕ)
    (hX : 1 < X) (hs : 0 < s) (hs1 : s ≤ 1/1000) (hlog : 1000 ≤ Real.log X)
    (hp : p ∈ largePrimes X) (hd : d ∈ SieveUpperBoxWindow.smallCarrier (level X s/p) s)
    (ht : [q] ∈ SieveUpperBoxing.innerFamily (level X s/p) s (cutoffThree X s p))
    (hshort : (q:ℝ) ≤ X^(8/35:ℝ)) (hhigh : X^(109/200:ℝ) < ((p*d*q:ℕ):ℝ)) :
    q.Prime ∧ X^(1/25:ℝ) < (q:ℝ) ∧
      X^(9/35:ℝ) ≤ ((p*d:ℕ):ℝ) ∧ ((p*d:ℕ):ℝ) < X^(1003/2000:ℝ) ∧
      ((p*d*q:ℕ):ℝ) < X^(731/1000:ℝ) := by
  have hg := large_geometry X s p hX hs hs1 hlog hp
  have hqpool := ((SieveUpperBoxing.mem_innerFamily _ _ _ hg.2.2.1 hs [q]).mp ht).1 q (by simp)
  have hqprime := ((SieveBoxedFamily.mem_pool _ _ _ q).mp hqpool).1
  have hm := actual_grouped_bounds X s p d hX hs hs1 hlog hp hd
  refine ⟨hqprime,high_implies_short_lower X s p d q hX hs hs1 hlog hp hd hhigh,hm.1,hm.2,?_⟩
  simpa only [Nat.cast_mul] using
    full_rectangle_product_lt X ((p*d:ℕ):ℝ) q hX (Nat.cast_nonneg _) hm.2 hshort

theorem two_le_small_power (X : ℝ) (hX : 1 < X) (hlog : 1000 ≤ Real.log X) :
    2 ≤ X^(1/1000:ℝ) := by
  apply (Real.log_le_log_iff (by norm_num) (Real.rpow_pos_of_pos (by linarith) _)).mp
  rw [Real.log_rpow (by linarith)]
  have ht := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num)
  linarith

theorem four_le_product_gap (X : ℝ) (hX : 1 < X) (hlog : 1000 ≤ Real.log X) :
    4 ≤ X^(3/1400:ℝ) := by
  apply (Real.log_le_log_iff (by norm_num) (Real.rpow_pos_of_pos (by linarith) _)).mp
  rw [Real.log_rpow (by linarith)]
  have ht := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num)
  have he : Real.log 4 = 2*Real.log 2 := by
    have he := Real.log_pow (2:ℝ) 2
    rw [show (2:ℝ)^2 = 4 by norm_num] at he
    exact he
  rw [he]
  linarith

/-- Dyadic scales are bounded for arbitrary representatives in the global
ranges. No original p/q mask is assumed for the expanded rectangle. -/
theorem dyadic_rectangle_bounds (X M N m q : ℝ) (hX : 1 < X)
    (hlog : 1000 ≤ Real.log X) (hmlo : X^(9/35:ℝ) ≤ m) (hmhi : m < X^(1003/2000:ℝ))
    (hqlo : X^(1/25:ℝ) < q) (hqhi : q ≤ X^(8/35:ℝ))
    (hMm : M < m) (hmM : m ≤ 2*M) (hNq : N < q) (hqN : q ≤ 2*N) :
    X^(59/200:ℝ) ≤ M*N ∧ M*N ≤ X^(731/1000:ℝ) ∧
      X^(39/1000:ℝ) ≤ N ∧ N ≤ X^(8/35:ℝ) ∧ 1 ≤ M ∧ 1 ≤ N := by
  have hX0 : 0 < X := by linarith
  have hm0 : 0 ≤ m := (Real.rpow_pos_of_pos hX0 _).le.trans hmlo
  have hq0 : 0 ≤ q := (Real.rpow_pos_of_pos hX0 _).le.trans hqlo.le
  have hM0 : 0 ≤ M := by linarith
  have hN0 : 0 ≤ N := by linarith
  have htwo := two_le_small_power X hX hlog
  have hNlower : X^(39/1000:ℝ) ≤ N := by
    have hh : 2*X^(39/1000:ℝ) ≤ X^(1/25:ℝ) := by
      calc
        _ ≤ X^(1/1000:ℝ)*X^(39/1000:ℝ) := mul_le_mul_of_nonneg_right htwo (by positivity)
        _ = _ := by rw [←Real.rpow_add hX0]; norm_num
    linarith
  have hMone : 1 ≤ M := by
    have hh : 2 ≤ X^(9/35:ℝ) := htwo.trans
      (Real.rpow_le_rpow_of_exponent_le hX.le (by norm_num))
    linarith
  have hNtop : N ≤ X^(8/35:ℝ) := hNq.le.trans hqhi
  refine ⟨?_,?_,hNlower,hNtop,hMone,?_⟩
  · have hprodlo := mul_le_mul hmlo hqlo.le (Real.rpow_nonneg hX0.le _) hm0
    have hprodhi := mul_le_mul hmM hqN hq0 (by positivity : 0 ≤ 2*M)
    have hh : 4*X^(59/200:ℝ) ≤ X^(9/35:ℝ)*X^(1/25:ℝ) := by
      calc
        _ ≤ X^(3/1400:ℝ)*X^(59/200:ℝ) :=
          mul_le_mul_of_nonneg_right (four_le_product_gap X hX hlog) (by positivity)
        _ = _ := by rw [←Real.rpow_add hX0, ←Real.rpow_add hX0]; norm_num
    nlinarith
  · calc
      M*N ≤ X^(1003/2000:ℝ)*X^(8/35:ℝ) :=
        mul_le_mul (hMm.le.trans hmhi.le) hNtop hN0 (by positivity)
      _ = X^((1003/2000:ℝ)+8/35) := (Real.rpow_add hX0 _ _).symm
      _ ≤ X^(731/1000:ℝ) := Real.rpow_le_rpow_of_exponent_le hX.le (by norm_num)
  · exact (Real.one_le_rpow hX.le (by norm_num : (0:ℝ) ≤ 39/1000)).trans hNlower

run_cmd do
  for decl in [``sqrt_two_mul_le, ``actual_small_divisor_bound, ``actual_grouped_bounds,
      ``high_implies_short_lower, ``full_rectangle_product_lt, ``actual_surviving_bounds,
      ``two_le_small_power, ``four_le_product_gap, ``dyadic_rectangle_bounds] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ACTUAL SHORT SINGLETON PHYSICAL AND FULL RECTANGLE GEOMETRY PASSED"

end ShortSingletonGeometry
