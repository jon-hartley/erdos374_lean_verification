import Item1ParameterCore
import Mathlib.Analysis.Complex.ExponentialBounds

/-! Uniform absorption of the full explicit logarithmic loss in the
one-third parameter construction. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section

namespace Item1ParameterLoss
open Item1ParameterCore

/-- A coarse logarithmic bound for the actual expanded loss. -/
theorem rawLoss_le_log_bound (d : ℕ) (L m lam : ℝ)
    (hL : 1600 ≤ L) (hlog : 1 ≤ Real.log L) (hm : 1 ≤ m)
    (hlam : 1 ≤ lam) (hLm : lam*m = L)
    (hd : 5 ≤ d) (hdlam : (d:ℝ) ≤ 6*lam) :
    rawLoss d m ≤ 125000*lam^3*Real.log L := by
  have hLpos : 0 < L := by linarith
  have hm0 : 0 ≤ m := by linarith
  have hlam0 : 0 ≤ lam := by linarith
  have hlog0 : 0 ≤ Real.log L := by linarith
  have hd5 : (5:ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0:ℝ) < d := by linarith
  have hd0 : (0:ℝ) ≤ d := hdpos.le
  have hlamL : lam ≤ L := by
    calc lam = lam*1 := by ring
      _ ≤ lam*m := mul_le_mul_of_nonneg_left hm hlam0
      _ = L := hLm
  have hdL : (d:ℝ) ≤ 6*L := hdlam.trans (by linarith)
  have hlog6 : Real.log 6 ≤ Real.log L :=
    Real.log_le_log (by norm_num) (by linarith)
  have hlogd : Real.log (d:ℝ) ≤ 3*Real.log L := by
    have h := Real.log_le_log hdpos hdL
    rw [Real.log_mul (by norm_num) hLpos.ne'] at h
    linarith
  have hlog1600 : Real.log 1600 ≤ Real.log L :=
    Real.log_le_log (by norm_num) hL
  have hlog8 : Real.log 8 ≤ Real.log L :=
    Real.log_le_log (by norm_num) (by linarith)
  have hlog15 : Real.log 15 ≤ Real.log L :=
    Real.log_le_log (by norm_num) (by linarith)
  have hlogpow : Real.log (8*(d:ℝ)^2) ≤ 7*Real.log L := by
    rw [Real.log_mul (by norm_num) (pow_ne_zero 2 hdpos.ne'), Real.log_pow]
    norm_num
    linarith
  have hlogpow0 : 0 ≤ Real.log (8*(d:ℝ)^2) :=
    Real.log_nonneg (by nlinarith)
  have hdm : (d:ℝ)*m ≤ 6*L := by
    calc (d:ℝ)*m ≤ (6*lam)*m := mul_le_mul_of_nonneg_right hdlam hm0
      _ = 6*L := by rw [← hLm]; ring
  have hargpos : 0 < 1+Real.log (8*(d:ℝ)^2)+(d:ℝ)*m := by positivity
  have harg : 1+Real.log (8*(d:ℝ)^2)+(d:ℝ)*m ≤ 15*L := by
    have hself := Real.log_le_self hLpos.le
    linarith
  have hlogarg : Real.log (1+Real.log (8*(d:ℝ)^2)+(d:ℝ)*m) ≤
      2*Real.log L := by
    have h := Real.log_le_log hargpos harg
    rw [Real.log_mul (by norm_num) hLpos.ne'] at h
    linarith
  have hlamcube : lam ≤ lam^3 := by
    have hsq : 1 ≤ lam^2 := one_le_pow₀ hlam
    have h := mul_le_mul_of_nonneg_left hsq hlam0
    nlinarith only [h]
  have hlamsq : lam^2 ≤ lam^3 := by
    have h := mul_le_mul_of_nonneg_left hlam (sq_nonneg lam)
    nlinarith only [h]
  have hmain : 192*(d:ℝ)^3*Real.log (d:ℝ) ≤ 124416*lam^3*Real.log L := by
    calc
      _ ≤ 192*(d:ℝ)^3*(3*Real.log L) :=
        mul_le_mul_of_nonneg_left hlogd (by positivity)
      _ ≤ 192*(6*lam)^3*(3*Real.log L) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hd0 hdlam 3) (by norm_num))
          (by positivity)
      _ = _ := by ring
  have hsmall : (d:ℝ)*Real.log 1600 + 5*(d:ℝ)*Real.log (d:ℝ) +
      (d:ℝ)*Real.log (1+Real.log (8*(d:ℝ)^2)+(d:ℝ)*m) ≤
      162*lam^3*Real.log L := by
    have h1 := mul_le_mul_of_nonneg_left hlog1600 hd0
    have h2 := mul_le_mul_of_nonneg_left hlogd (show 0 ≤ 5*(d:ℝ) by positivity)
    have h3 := mul_le_mul_of_nonneg_left hlogarg hd0
    calc
      _ ≤ 27*(d:ℝ)*Real.log L := by nlinarith only [h1, h2, h3, mul_nonneg hd0 hlog0]
      _ ≤ 27*(6*lam)*Real.log L := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hdlam (by norm_num)) hlog0
      _ = 162*lam*Real.log L := by ring
      _ ≤ 162*lam^3*Real.log L :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hlamcube (by norm_num)) hlog0
  have htwo : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
    linarith
  have hdp : (d:ℝ)+1 ≤ 7*lam := by linarith
  have hquadratic : (3/2:ℝ)*(d:ℝ)*((d:ℝ)+1)*Real.log 2 ≤
      63*lam^3*Real.log L := by
    have hprod := mul_le_mul hdlam hdp (show (0:ℝ) ≤ (d:ℝ)+1 by positivity)
      (show 0 ≤ 6*lam by positivity)
    calc
      _ ≤ (3/2:ℝ)*(d:ℝ)*((d:ℝ)+1)*1 :=
        mul_le_mul_of_nonneg_left htwo (by positivity)
      _ ≤ (3/2:ℝ)*((6*lam)*(7*lam)) := by
        convert mul_le_mul_of_nonneg_left hprod (show (0:ℝ) ≤ 3/2 by norm_num) using 1 <;> ring
      _ = 63*lam^2 := by ring
      _ ≤ 63*lam^3 := mul_le_mul_of_nonneg_left hlamsq (by norm_num)
      _ ≤ 63*lam^3*Real.log L := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hlog
          (show 0 ≤ 63*lam^3 by positivity)
  unfold rawLoss
  nlinarith only [hmain, hsmall, hquadratic, mul_nonneg (pow_nonneg hlam0 3) hlog0]

/-- The original lower cutoff gives enough square growth to absorb the
entire logarithmic loss, with one fixed explicit threshold. -/
theorem cutoff_square_bound (L m : ℝ) (hL : (10:ℝ)^21 ≤ L)
    (hm : 6*L^(2/3:ℝ)*Real.log L < m) :
    1 ≤ m ∧ 1 ≤ Real.log L ∧ 10000000*L*Real.log L ≤ m^2 := by
  have hLpos : 0 < L := by nlinarith
  have hL1 : 1 ≤ L := by nlinarith
  have hlog : 1 ≤ Real.log L := by
    have hexp : Real.exp 1 ≤ L := Real.exp_one_lt_three.le.trans (by nlinarith)
    have h := Real.log_le_log (Real.exp_pos 1) hexp
    simpa only [Real.log_exp] using h
  have hlog0 : 0 ≤ Real.log L := by linarith
  have hpow1 : 1 ≤ L^(2/3:ℝ) := Real.one_le_rpow hL1 (by norm_num)
  have hprod1 : 1 ≤ L^(2/3:ℝ)*Real.log L := by
    simpa only [one_mul] using mul_le_mul hpow1 hlog (by norm_num : (0:ℝ) ≤ 1)
      (by positivity : 0 ≤ L^(2/3:ℝ))
  have hm1 : 1 ≤ m := by nlinarith
  let q := L^(1/3:ℝ)
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hq2 : q^2 = L^(2/3:ℝ) := by
    dsimp [q]
    rw [← Real.rpow_mul_natCast hLpos.le (1/3:ℝ) 2]
    norm_num
  have hq3 : q^3 = L := by
    dsimp [q]
    rw [← Real.rpow_mul_natCast hLpos.le (1/3:ℝ) 3]
    norm_num
  have hqbig : 10000000 ≤ q := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (3:ℕ) ≠ 0) hq0
    rw [hq3]
    convert hL using 1 <;> norm_num
  have hsq : 36*L*q*(Real.log L)^2 ≤ m^2 := by
    calc
      _ = (6*L^(2/3:ℝ)*Real.log L)^2 := by rw [← hq2, ← hq3]; ring
      _ ≤ m^2 := pow_le_pow_left₀ (by positivity) hm.le 2
  have hqlog : 10000000 ≤ q*Real.log L := by
    simpa only [mul_one] using mul_le_mul hqbig hlog (by norm_num : (0:ℝ) ≤ 1) hq0
  have hlarge : 10000000 ≤ 36*q*Real.log L := by nlinarith only [hqlog]
  have hscalar : 10000000*L*Real.log L ≤ m^2 := by
    calc
      _ ≤ 36*L*q*(Real.log L)^2 := by
        convert mul_le_mul_of_nonneg_right hlarge (mul_nonneg hLpos.le hlog0) using 1 <;> ring
      _ ≤ m^2 := hsq
  exact ⟨hm1, hlog, hscalar⟩

/-- Full loss absorption under the original intermediate lower cutoff.
No upper bound for rawLoss is supplied as a hypothesis. -/
theorem rawLoss_le_cutoff (d : ℕ) (L m : ℝ) (hL : (10:ℝ)^21 ≤ L)
    (hm : 6*L^(2/3:ℝ)*Real.log L < m) (hlam : 1 ≤ L/m)
    (hd : 5 ≤ d) (hdlam : (d:ℝ) ≤ 6*(L/m)) :
    rawLoss d m ≤ (L/m)^2*m/80 := by
  obtain ⟨hm1, hlog, hscalar⟩ := cutoff_square_bound L m hL hm
  have hmpos : 0 < m := by linarith
  have hLm : (L/m)*m = L := div_mul_cancel₀ L hmpos.ne'
  have hraw := rawLoss_le_log_bound d L m (L/m) (by nlinarith) hlog hm1 hlam hLm hd hdlam
  have hmloss : 10000000*(L/m)*Real.log L ≤ m := by
    apply (mul_le_mul_iff_right₀ hmpos).mp
    calc
      _ = 10000000*((L/m)*m)*Real.log L := by ring
      _ = 10000000*L*Real.log L := by rw [hLm]
      _ ≤ m^2 := hscalar
      _ = m*m := by ring
  refine hraw.trans ?_
  apply (le_div_iff₀ (by norm_num : (0:ℝ) < 80)).mpr
  convert mul_le_mul_of_nonneg_left hmloss (sq_nonneg (L/m)) using 1 <;> ring

end Item1ParameterLoss

run_cmd do
  for target in [``Item1ParameterLoss.rawLoss_le_log_bound,
      ``Item1ParameterLoss.cutoff_square_bound,
      ``Item1ParameterLoss.rawLoss_le_cutoff] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "PARAMETER LOSS: 3 standard-axiom theorem guards passed."
