import SieveStoppingForcing
import RosserKernelContraction

/-! A parameter-sensitive bound for the actual rejected second-gate forcing.
The rejected outer prime exceeds T^(1/4); every rejected inner prime is at
least (T/z)^(1/3). Both estimates use actual normalized Euler prime masses. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
open Real SieveStoppingExpansion SieveStoppingTwoStep SieveStoppingForcing PrimeEulerLogBounds

namespace SieveStoppingSharpForcing

theorem root_le_of_le_pow (b x : ℝ) (n : ℕ) (hn : 0 < n)
    (hb : 0 < b) (hx : 0 < x) (hxb : x ≤ b^n) : root x n ≤ b := by
  have hlog := log_le_log hx hxb
  rw [log_pow] at hlog
  unfold root
  rw [← exp_log hb]
  apply exp_le_exp.mpr
  apply (div_le_iff₀ (by exact_mod_cast hn : (0:ℝ) < n)).mpr
  nlinarith

theorem parameter_bounds (T z : ℝ) (hz : 1 < z) (hT : z^2 ≤ T) (hT4 : T ≤ z^4) :
    2 ≤ log T/log z ∧ log T/log z ≤ 4 := by
  have hz0 : 0 < z := by linarith
  have hT0 : 0 < T := (pow_pos hz0 2).trans_le hT
  have hlo := log_le_log (pow_pos hz0 2) hT
  have hhi := log_le_log hT0 hT4
  simp only [log_pow, Nat.cast_ofNat] at hlo hhi
  exact ⟨(le_div_iff₀ (log_pos hz)).mpr hlo, (div_le_iff₀ (log_pos hz)).mpr hhi⟩

theorem rejected_outer_root (T p q : ℝ) (hT : 0 < T) (hp : 0 < p)
    (hq : 0 ≤ q) (hqp : q < p) (hf : ¬q^3 < T/p) : root T 4 < p := by
  have hh := log_lt_log hT (rejected_level_lt_fourth T p q hp hq hqp hf)
  simp only [log_pow, Nat.cast_ofNat] at hh
  unfold root
  rw [← exp_log hp]
  apply exp_lt_exp.mpr
  norm_num
  linarith

theorem rejected_inner_root (T z p q : ℝ) (hT : 0 < T) (hz : 0 < z)
    (hp : 0 < p) (hpz : p ≤ z) (hq : 0 < q) (hf : ¬q^3 < T/p) :
    root (T/z) 3 ≤ q := by
  have hh : T/z ≤ q^3 :=
    (div_le_div_of_nonneg_left hT.le hp hpz).trans (le_of_not_gt hf)
  have hl := log_le_log (div_pos hT hz) hh
  simp only [log_pow, Nat.cast_ofNat] at hl
  unfold root
  rw [← exp_log hq]
  apply exp_le_exp.mpr
  norm_num
  linarith

theorem innerRejected_le_interval (T z : ℝ) (p : ℕ) (hT : 0 < T)
    (hz : 0 < z) (hp : 0 < (p:ℝ)) (hpz : (p:ℝ) ≤ z) :
    innerRejected T p ≤ ∑ q ∈ intervalPrimes (root (T/z) 3) (p:ℝ),
      PrimeEulerMass.weight q / primeEuler (p:ℝ) := by
  rw [interval_eq_filter, Finset.sum_filter]
  unfold innerRejected
  apply Finset.sum_le_sum
  intro q hq
  have hq0 : (0:ℝ) < q := by
    exact_mod_cast ((SieveSmallWeights.mem_pool (p:ℝ) q).mp hq).1.pos
  by_cases hf : (q:ℝ)^3 < T/(p:ℝ)
  · simp only [hf, ite_true]
    split_ifs
    · exact normalized_weight_nonneg q _
    · exact le_rfl
  · have hs := rejected_inner_root T z p q hT hz hp hpz hq0 hf
    simp only [hf, hs, ite_false, ite_true, le_refl]

theorem innerRejected_zero_below (T z : ℝ) (p : ℕ) (hT : 0 < T)
    (hp : p ∈ SieveSmallWeights.pool z) (ha : (p:ℝ) < root T 4) :
    innerRejected T p = 0 := by
  unfold innerRejected
  apply Finset.sum_eq_zero
  intro q hq
  have hp0 : (0:ℝ) < p := by exact_mod_cast ((SieveSmallWeights.mem_pool z p).mp hp).1.pos
  have hqp := ((SieveSmallWeights.mem_pool (p:ℝ) q).mp hq).2
  have hg : (q:ℝ)^3 < T/(p:ℝ) := by
    by_contra hf
    have hh := rejected_outer_root T p q hT hp0 (Nat.cast_nonneg q) hqp hf
    linarith
  simp only [hg, ite_true]

theorem inner_uniform_bound (T z : ℝ) (p : ℕ) (hz : 64 ≤ z)
    (hT : z^2 ≤ T) (hT4 : T ≤ z^4) (hp : p ∈ SieveSmallWeights.pool z) :
    innerRejected T p ≤ (4-log T/log z)/(log T/log z-1)+9*epsilon z := by
  have hz0 : 0 < z := by linarith
  have hlz : 0 < log z := log_pos (by linarith)
  have hT0 : 0 < T := (pow_pos hz0 2).trans_le hT
  obtain ⟨hr2, hr4⟩ := parameter_bounds T z (by linarith) hT hT4
  have he0 : 0 ≤ epsilon z := div_nonneg PrimeEulerDimensionOne.errorConstant_pos.le hlz.le
  have hC0 : 0 ≤ (4-log T/log z)/(log T/log z-1)+9*epsilon z :=
    add_nonneg (div_nonneg (by linarith) (by linarith)) (by positivity)
  have hp0 : (0:ℝ) < p := by exact_mod_cast ((SieveSmallWeights.mem_pool z p).mp hp).1.pos
  have hpz := ((SieveSmallWeights.mem_pool z p).mp hp).2
  have hc2 : 2 ≤ root (T/z) 3 := by
    apply root_lower 2 (T/z) 3 (by norm_num) (by norm_num)
    apply (le_div_iff₀ hz0).mpr
    nlinarith
  by_cases hcp : root (T/z) 3 ≤ (p:ℝ)
  · have hlc : 0 < log (root (T/z) 3) := log_pos (by linarith)
    have hlp := log_le_log hp0 hpz.le
    have hraw := (innerRejected_le_interval T z p hT0 hz0 hp0 hpz.le).trans
      (PrimeEulerMass.normalized_interval_bound _ _ hc2 hcp)
    have hmono : log (p:ℝ)/log (root (T/z) 3)-1+
        PrimeEulerDimensionOne.errorConstant*log (p:ℝ)/(log (root (T/z) 3))^2 ≤
        log z/log (root (T/z) 3)-1+
          PrimeEulerDimensionOne.errorConstant*log z/(log (root (T/z) 3))^2 := by
      apply add_le_add
      · exact sub_le_sub_right (div_le_div_of_nonneg_right hlp hlc.le) 1
      · exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hlp PrimeEulerDimensionOne.errorConstant_pos.le) (sq_nonneg _)
    have hr1 : log T/log z-1 ≠ 0 := by linarith
    have hiden : log z/log (root (T/z) 3)-1+
        PrimeEulerDimensionOne.errorConstant*log z/(log (root (T/z) 3))^2 =
        (4-log T/log z)/(log T/log z-1)+9*epsilon z/(log T/log z-1)^2 := by
      have hlcEq : log (root (T/z) 3) = (log T/log z-1)*log z/3 := by
        simp only [root, log_exp, Nat.cast_ofNat, log_div hT0.ne' hz0.ne']
        field_simp
      rw [hlcEq]
      unfold epsilon
      have hid (r l K : ℝ) (hr : r-1 ≠ 0) (hl : l ≠ 0) :
          l/((r-1)*l/3)-1+K*l/((r-1)*l/3)^2 =
            (4-r)/(r-1)+9*(K/l)/(r-1)^2 := by
        field_simp
        ring
      exact hid _ _ _ hr1 hlz.ne'
    have hden : 1 ≤ (log T/log z-1)^2 := by nlinarith
    have herr : 9*epsilon z/(log T/log z-1)^2 ≤ 9*epsilon z := by
      exact div_le_self (by positivity) hden
    exact (hraw.trans hmono).trans (hiden.le.trans (add_le_add (le_refl _) herr))
  · have hzsum : innerRejected T p = 0 := by
      unfold innerRejected
      apply Finset.sum_eq_zero
      intro q hq
      have hq0 : (0:ℝ) < q := by exact_mod_cast ((SieveSmallWeights.mem_pool (p:ℝ) q).mp hq).1.pos
      have hqp := ((SieveSmallWeights.mem_pool (p:ℝ) q).mp hq).2
      have hg : (q:ℝ)^3 < T/(p:ℝ) := by
        by_contra hf
        have hh := rejected_inner_root T z p q hT0 hz0 hp0 hpz.le hq0 hf
        linarith
      simp only [hg, ite_true]
    rw [hzsum]
    exact hC0

theorem outer_interval_bound (T z : ℝ) (hz : 64 ≤ z) (hT : z^2 ≤ T) (hT4 : T ≤ z^4) :
    (∑ p ∈ intervalPrimes (root T 4) z, PrimeEulerMass.weight p / primeEuler z) ≤
      (4-log T/log z)/(log T/log z)+4*epsilon z := by
  have hz0 : 0 < z := by linarith
  have hlz : 0 < log z := log_pos (by linarith)
  have hT0 : 0 < T := (pow_pos hz0 2).trans_le hT
  obtain ⟨hr2, _⟩ := parameter_bounds T z (by linarith) hT hT4
  have hr0 : log T/log z ≠ 0 := by linarith
  have ha2 : 2 ≤ root T 4 := root_lower 2 T 4 (by norm_num) (by norm_num) (by nlinarith)
  have haz : root T 4 ≤ z := root_le_of_le_pow z T 4 (by norm_num) hz0 hT0 hT4
  have hraw := PrimeEulerMass.normalized_interval_bound _ _ ha2 haz
  have hiden : log z/log (root T 4)-1+
      PrimeEulerDimensionOne.errorConstant*log z/(log (root T 4))^2 =
      (4-log T/log z)/(log T/log z)+16*epsilon z/(log T/log z)^2 := by
    simp only [root, log_exp, Nat.cast_ofNat, epsilon]
    have hlT : log T ≠ 0 := (log_pos (by nlinarith : 1 < T)).ne'
    field_simp
    ring
  have he0 : 0 ≤ epsilon z := div_nonneg PrimeEulerDimensionOne.errorConstant_pos.le hlz.le
  have hden : 4 ≤ (log T/log z)^2 := by nlinarith
  have herr : 16*epsilon z/(log T/log z)^2 ≤ 4*epsilon z := by
    apply (div_le_iff₀ (by nlinarith : 0 < (log T/log z)^2)).mpr
    nlinarith
  exact hraw.trans (hiden.le.trans (add_le_add (le_refl _) herr))

theorem forcing_product_bound (T z : ℝ) (hz : 64 ≤ z) (hT : z^2 ≤ T) (hT4 : T ≤ z^4) :
    forcing T z ≤
      ((4-log T/log z)/(log T/log z-1)+9*epsilon z)*
        ((4-log T/log z)/(log T/log z)+4*epsilon z) := by
  have hz0 : 0 < z := by linarith
  have hT0 : 0 < T := (pow_pos hz0 2).trans_le hT
  obtain ⟨hr2, hr4⟩ := parameter_bounds T z (by linarith) hT hT4
  have he0 : 0 ≤ epsilon z := div_nonneg PrimeEulerDimensionOne.errorConstant_pos.le
    (log_pos (by linarith)).le
  have hC0 : 0 ≤ (4-log T/log z)/(log T/log z-1)+9*epsilon z :=
    add_nonneg (div_nonneg (by linarith) (by linarith)) (by positivity)
  rw [forcing_factored]
  calc
    _ ≤ ∑ p ∈ SieveSmallWeights.pool z, if root T 4 ≤ (p:ℝ) then
        (PrimeEulerMass.weight p/primeEuler z)*
          ((4-log T/log z)/(log T/log z-1)+9*epsilon z) else 0 := by
      apply Finset.sum_le_sum
      intro p hp
      split_ifs with ha
      · exact mul_le_mul_of_nonneg_left (inner_uniform_bound T z p hz hT hT4 hp)
          (normalized_weight_nonneg p z)
      · rw [innerRejected_zero_below T z p hT0 hp (lt_of_not_ge ha), mul_zero]
    _ = (∑ p ∈ intervalPrimes (root T 4) z, PrimeEulerMass.weight p/primeEuler z)*
        ((4-log T/log z)/(log T/log z-1)+9*epsilon z) := by
      rw [interval_eq_filter, Finset.sum_mul, Finset.sum_filter]
    _ ≤ ((4-log T/log z)/(log T/log z)+4*epsilon z)*
        ((4-log T/log z)/(log T/log z-1)+9*epsilon z) :=
      mul_le_mul_of_nonneg_right (outer_interval_bound T z hz hT hT4) hC0
    _ = _ := mul_comm _ _

theorem product_le_shape (r e : ℝ) (hr2 : 2 ≤ r) (_hr4 : r ≤ 4) (he : 0 ≤ e) :
    ((4-r)/(r-1)+9*e)*((4-r)/r+4*e) ≤ (4-r)^2/(r*(r-1))+17*e+36*e^2 := by
  have hr0 : 0 < r := by linarith
  have hr1 : 0 < r-1 := by linarith
  have hA : (4-r)/(r-1) ≤ 2 := (div_le_iff₀ hr1).mpr (by linarith)
  have hB : (4-r)/r ≤ 1 := (div_le_iff₀ hr0).mpr (by linarith)
  have hcross := mul_le_mul_of_nonneg_right (show 4*((4-r)/(r-1))+9*((4-r)/r) ≤ 17 by linarith) he
  have hid : ((4-r)/(r-1))*((4-r)/r) = (4-r)^2/(r*(r-1)) := by
    field_simp
  nlinarith

theorem shape_le_exponential (r : ℝ) (hr2 : 2 ≤ r) (hr4 : r ≤ 4) :
    (4-r)^2/(r*(r-1)) ≤ 2*exp (2-r) := by
  have hexp : (4-r)/2 ≤ exp ((2-r)/2) := by
    have hh := add_one_le_exp ((2-r)/2)
    linarith
  have hsq := pow_le_pow_left₀ (by linarith : 0 ≤ (4-r)/2) hexp 2
  have heq : (exp ((2-r)/2))^2 = exp (2-r) := by
    rw [pow_two, ← exp_add]
    congr 1
    ring
  rw [heq] at hsq
  have hd : 2 ≤ r*(r-1) := by nlinarith
  apply (div_le_iff₀ (by nlinarith : 0 < r*(r-1))).mpr
  have hm := mul_le_mul_of_nonneg_left hd (exp_pos (2-r)).le
  nlinarith

theorem exponential_coefficient_le (e : ℝ) (he0 : 0 ≤ e) (he : e ≤ 1/100000) :
    2*exp 2+exp 4*(17*e+36*e^2) ≤ 15 := by
  have he2 : exp 2 ≤ (4624/625:ℝ) := by
    have hh := mul_le_mul RosserKernelContraction.exp_one_le RosserKernelContraction.exp_one_le
      (exp_pos 1).le (by norm_num : (0:ℝ) ≤ 68/25)
    rw [← exp_add] at hh
    norm_num at hh ⊢
    exact hh
  have he4 : exp 4 ≤ (225/4:ℝ) := by
    have hh := mul_le_mul RosserKernelContraction.exp_two_le RosserKernelContraction.exp_two_le
      (exp_pos 2).le (by norm_num : (0:ℝ) ≤ 15/2)
    rw [← exp_add] at hh
    norm_num at hh ⊢
    exact hh
  have hesq := pow_le_pow_left₀ he0 he 2
  have herr : 17*e+36*e^2 ≤ 17*(1/100000:ℝ)+36*(1/100000:ℝ)^2 := by nlinarith
  have hm := mul_le_mul he4 herr (by positivity : 0 ≤ 17*e+36*e^2)
    (by norm_num : (0:ℝ) ≤ 225/4)
  nlinarith

theorem product_le_fifteen_exp (r e : ℝ) (hr2 : 2 ≤ r) (hr4 : r ≤ 4)
    (he0 : 0 ≤ e) (he : e ≤ 1/100000) :
    ((4-r)/(r-1)+9*e)*((4-r)/r+4*e) ≤ 15*exp (-r) := by
  have hg := shape_le_exponential r hr2 hr4
  have hshape := product_le_shape r e hr2 hr4 he0
  have herr0 : 0 ≤ 17*e+36*e^2 := by positivity
  have heone : 1 ≤ exp (4-r) := one_le_exp_iff.mpr (by linarith)
  have herr := mul_le_mul_of_nonneg_left heone herr0
  calc
    _ ≤ 2*exp (2-r)+(17*e+36*e^2) := by linarith
    _ ≤ 2*exp (2-r)+(17*e+36*e^2)*exp (4-r) := by linarith
    _ = (2*exp 2+exp 4*(17*e+36*e^2))*exp (-r) := by
      simp only [sub_eq_add_neg, exp_add]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (exponential_coefficient_le e he0 he) (exp_pos _).le

/-- The actual forcing constant is 15 once the same arithmetic threshold
used by the two-step contraction holds. -/
theorem forcing_exponential (T z : ℝ) (hz : 64 ≤ z) (hT : z^2 ≤ T)
    (hlog : 100000*PrimeEulerDimensionOne.errorConstant ≤ log z) :
    forcing T z ≤ 15*exp (-(log T/log z)) := by
  by_cases hT4 : z^4 ≤ T
  · rw [forcing_eq_zero T z hT4]
    positivity
  · have hlz : 0 < log z := log_pos (by linarith)
    have he0 : 0 ≤ epsilon z := div_nonneg PrimeEulerDimensionOne.errorConstant_pos.le hlz.le
    have he : epsilon z ≤ 1/100000 := by
      unfold epsilon
      apply (div_le_iff₀ hlz).mpr
      linarith
    obtain ⟨hr2, hr4⟩ := parameter_bounds T z (by linarith) hT (le_of_not_ge hT4)
    exact (forcing_product_bound T z hz hT (le_of_not_ge hT4)).trans
      (product_le_fifteen_exp _ _ hr2 hr4 he0 he)

run_cmd do
  for decl in [``root_le_of_le_pow, ``parameter_bounds, ``rejected_outer_root,
    ``rejected_inner_root, ``innerRejected_le_interval, ``innerRejected_zero_below,
    ``inner_uniform_bound, ``outer_interval_bound, ``forcing_product_bound,
    ``product_le_shape, ``shape_le_exponential, ``exponential_coefficient_le,
    ``product_le_fifteen_exp, ``forcing_exponential] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ACTUAL STOPPING FORCING IS AT MOST 15 TIMES THE EXPONENTIAL WEIGHT"

end SieveStoppingSharpForcing
end
