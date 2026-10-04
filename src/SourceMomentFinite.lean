import MomentResidualEven
import DyadicLevelParameters
import MomentThreshold
import NormalizedMeanSquare

/-!
Actual Mangoldt-dominated interval powers -> explicit fractional moment.
The level measure and the lower even moment are CONSTRUCTED from the
inherited theorems, not assumed. Coefficient hypotheses are the literal
Mangoldt majorant and a reciprocal mass bound. Prime powers are retained.
The logarithmic simplification is separated from this finite analytic step.
-/
set_option autoImplicit false
set_option maxHeartbeats 12000000
noncomputable section
open MeasureTheory Set
open scoped BigOperators ComplexConjugate ENNReal
namespace SourceMomentFinite
open MomentResidualConvolution MomentResidualInterval MomentResidualEven
open Erdos374.HarmanGram152 Erdos374.HarmanAnalytic151MeanSquare
open DirichletLargeValueMeasure DyadicLevelParameters SupremumMoment

def upper (D : ℕ) : ℕ := 2^6*D

def polynomial (D : ℕ) (a : ℕ → ℂ) (t : ℝ) : ℂ :=
  verticalDirichlet152 (Finset.Ioc D (upper D)) a 1 t

def powerCoeff (D h : ℕ) (a : ℕ → ℂ) : ArithmeticFunction ℂ :=
  intervalCoefficients D (upper D) a ^ h

def weighted (D h : ℕ) (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  conj (powerCoeff D h a n / (n:ℂ))

def mass (D : ℕ) (a : ℕ → ℂ) : ℝ :=
  ∑ n ∈ Finset.Ioc D (upper D), ‖a n‖/(n:ℝ)

def energy (D h : ℕ) : ℝ :=
  ((1+Real.log (((upper D)^h:ℕ):ℝ))^h * (64:ℝ)^h)/((D^h:ℕ):ℝ)

def secondBudget (D h : ℕ) (T : ℝ) : ℝ :=
  (T+4*(((upper D)^h:ℕ):ℝ)*(1+Real.log (((upper D)^h:ℕ):ℝ)))*energy D h

def quadraticBudget (D h : ℕ) (T : ℝ) : ℝ :=
  quadratic (D^h) (6*h) T (energy D h)

def sexticBudget (D h : ℕ) (T : ℝ) : ℝ :=
  sextic (D^h) (6*h) T (energy D h)

theorem upper_ge (D : ℕ) : D ≤ upper D := by
  unfold upper
  omega

theorem upper_power (D h : ℕ) : (upper D)^h = 2^(6*h)*D^h := by
  unfold upper
  rw [mul_pow, ←pow_mul]

theorem energy_positive (D h : ℕ) (hD : 1 ≤ D) : 0 < energy D h := by
  have hN : 1 ≤ (upper D)^h := one_le_pow₀ (hD.trans (upper_ge D))
  have hlog : 0 ≤ Real.log (((upper D)^h:ℕ):ℝ) :=
    Real.log_nonneg (by exact_mod_cast hN)
  have hQ : (0:ℝ) < ((D^h:ℕ):ℝ) := by
    exact_mod_cast (pow_pos (by omega : 0 < D) h)
  unfold energy
  positivity

/-- Strict lower support is proved for the full convolution, including powers
of the same prime. No squarefree-support simplification is used. -/
theorem power_support_strict (D h n : ℕ) (a : ℕ → ℂ)
    (hD : 1 ≤ D) (hh : 1 ≤ h) (hne : powerCoeff D h a n ≠ 0) :
    D^h < n ∧ n ≤ (upper D)^h := by
  cases h with
  | zero => omega
  | succ h =>
    have hs (m : ℕ) (hm : intervalCoefficients D (upper D) a m ≠ 0) :
        D ≤ m ∧ m ≤ upper D := by
      have hb := intervalCoefficients_support D (upper D) a m hm
      exact ⟨hb.1.le,hb.2⟩
    change ((intervalCoefficients D (upper D) a)^(h+1)) n ≠ 0 at hne
    rw [pow_succ, ArithmeticFunction.mul_apply] at hne
    obtain ⟨uv,huv,hnz⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    have he := (Nat.mem_divisorsAntidiagonal.mp huv).1
    have hleft := power_support (intervalCoefficients D (upper D) a)
      D (upper D) hs h uv.1 (mul_ne_zero_iff.mp hnz).1
    have hright := intervalCoefficients_support D (upper D) a uv.2
      (mul_ne_zero_iff.mp hnz).2
    constructor
    · rw [pow_succ, ←he]
      exact (Nat.mul_lt_mul_of_pos_left hright.1 (pow_pos (by omega) h)).trans_le
        (Nat.mul_le_mul_right uv.2 hleft.1)
    · rw [pow_succ, ←he]
      exact Nat.mul_le_mul hleft.2 hright.2

theorem full_weighted_energy (D h : ℕ) (a : ℕ → ℂ) (hD : 1 ≤ D)
    (ha : ∀ n ∈ Finset.Ioc D (upper D), ‖a n‖ ≤ ArithmeticFunction.vonMangoldt n)
    (hm : mass D a ≤ 64) :
    (∑ n ∈ Finset.Ioc 0 ((upper D)^h),
      ‖powerCoeff D h a n‖^2/(n:ℝ)^2) ≤ energy D h := by
  have he := interval_power_weighted_energy D (upper D) hD (upper_ge D) a ha h
  have hN : 1 ≤ (upper D)^h := one_le_pow₀ (hD.trans (upper_ge D))
  have hl : 0 ≤ Real.log (((upper D)^h:ℕ):ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  have hm0 : 0 ≤ mass D a := Finset.sum_nonneg (fun n _ => by positivity)
  have hmass := pow_le_pow_left₀ hm0 hm h
  have hlog := pow_le_pow_left₀ hl (show Real.log (((upper D)^h:ℕ):ℝ) ≤
    1+Real.log (((upper D)^h:ℕ):ℝ) by linarith) h
  change (∑ n ∈ Finset.Ioc 0 ((upper D)^h),
    ‖(intervalCoefficients D (upper D) a ^ h) n‖^2/(n:ℝ)^2) ≤ _
  apply he.trans
  change (Real.log (((upper D)^h:ℕ):ℝ))^h/((D^h:ℕ):ℝ)*(mass D a)^h ≤ _
  calc
    _ ≤ ((1+Real.log (((upper D)^h:ℕ):ℝ))^h/((D^h:ℕ):ℝ))*(64:ℝ)^h := by
      gcongr
    _ = energy D h := by unfold energy; ring

theorem weighted_energy (D h : ℕ) (a : ℕ → ℂ) (hD : 1 ≤ D)
    (ha : ∀ n ∈ Finset.Ioc D (upper D), ‖a n‖ ≤ ArithmeticFunction.vonMangoldt n)
    (hm : mass D a ≤ 64) :
    (∑ n ∈ Finset.Ioc (D^h) ((upper D)^h), ‖weighted D h a n‖^2) ≤ energy D h := by
  have he := full_weighted_energy D h a hD ha hm
  simp only [weighted, RCLike.norm_conj, norm_div, Complex.norm_natCast, div_pow]
  exact (Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.Ioc_subset_Ioc (Nat.zero_le _) le_rfl)
    (fun _ _ _ => by positivity)).trans he

theorem power_identity (D h : ℕ) (a : ℕ → ℂ) (hD : 1 ≤ D) (hh : 1 ≤ h) (t : ℝ) :
    polynomial D a t ^ h = verticalDirichlet152
      (Finset.Ioc (D^h) ((upper D)^h)) (powerCoeff D h a) 1 t := by
  unfold polynomial
  rw [interval_vertical_power D (upper D) (hD.trans (upper_ge D)) a h 1 t]
  change verticalDirichlet152 (Finset.Ioc 0 ((upper D)^h)) (powerCoeff D h a) 1 t = _
  unfold verticalDirichlet152
  symm
  apply Finset.sum_subset (Finset.Ioc_subset_Ioc (Nat.zero_le _) le_rfl)
  intro n hn hnot
  have hz : powerCoeff D h a n = 0 := by
    by_contra hne
    have hs := power_support_strict D h n a hD hh hne
    exact hnot (Finset.mem_Ioc.mpr hs)
  rw [hz, zero_mul]

theorem power_norm_expansion (D h : ℕ) (a : ℕ → ℂ) (hD : 1 ≤ D) (hh : 1 ≤ h) (t : ℝ) :
    ‖polynomial D a t ^ h‖ = ‖exponentialSum151
      (Finset.Ioc (D^h) ((upper D)^h)) (weighted D h a) (fun n => Real.log n) t‖ := by
  rw [power_identity D h a hD hh t,
    verticalDirichlet_norm152 _ _ 1 t (by intro n hn; have := Finset.mem_Ioc.mp hn; omega)]
  simp only [normalizedCoefficients152, Real.rpow_one, Complex.ofReal_natCast]
  rfl

theorem polynomial_mass_bound (D : ℕ) (a : ℕ → ℂ) (t : ℝ) :
    ‖polynomial D a t‖ ≤ mass D a := by
  have hp : ∀ n ∈ Finset.Ioc D (upper D), 0 < n := by
    intro n hn
    have := Finset.mem_Ioc.mp hn
    omega
  unfold polynomial
  rw [verticalDirichlet_eq_exponential152 _ _ 1 t hp]
  unfold exponentialSum151
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro n hn
  simp only [norm_mul, norm_kernel151, mul_one, normalizedCoefficients152,
    Real.rpow_one, Complex.ofReal_natCast, norm_div, Complex.norm_natCast, le_refl]

/-- The actual second moment is supplied by the inherited mean-value theorem. -/
theorem lower_moment (D h : ℕ) (a : ℕ → ℂ) (hD : 1 ≤ D)
    (ha : ∀ n ∈ Finset.Ioc D (upper D), ‖a n‖ ≤ ArithmeticFunction.vonMangoldt n)
    (hm : mass D a ≤ 64) (a0 T : ℝ) (hT : 0 ≤ T) :
    (∫ t in Icc a0 (a0+T), ‖polynomial D a t ^ h‖^2) ≤ secondBudget D h T := by
  have hN : 1 ≤ (upper D)^h := one_le_pow₀ (hD.trans (upper_ge D))
  have he := full_weighted_energy D h a hD ha hm
  have hb := weighted_normalized_mean_square (Finset.Ioc 0 ((upper D)^h))
    (powerCoeff D h a) ((upper D)^h) hN
    (by intro n hn; have := Finset.mem_Ioc.mp hn; exact ⟨by omega,this.2⟩)
    1 (by norm_num) (energy D h) he a0 (a0+T) (by linarith)
  have hid (t : ℝ) : polynomial D a t ^ h = verticalDirichlet152
      (Finset.Ioc 0 ((upper D)^h)) (powerCoeff D h a) 1 t :=
    interval_vertical_power D (upper D) (hD.trans (upper_ge D)) a h 1 t
  simp only [←hid] at hb
  simpa only [secondBudget, add_sub_cancel_left] using hb

/-- The level-set bound is constructed for the genuine convolution coefficients. -/
theorem level_bound (D h : ℕ) (a : ℕ → ℂ) (hD : 1 ≤ D) (hh : 1 ≤ h)
    (ha : ∀ n ∈ Finset.Ioc D (upper D), ‖a n‖ ≤ ArithmeticFunction.vonMangoldt n)
    (hm : mass D a ≤ 64) (a0 T V : ℝ) (hT : 0 ≤ T) (hV : 0 < V) :
    volume (levelSet (fun t => polynomial D a t ^ h) a0 T V) ≤
      ENNReal.ofReal (quadraticBudget D h T/V^2+sexticBudget D h T/V^6) := by
  have he := weighted_energy D h a hD ha hm
  rw [upper_power] at he
  have hb := DyadicLevelParameters.measure_bound (D^h) (6*h) (weighted D h a)
    a0 T (energy D h) V (one_le_pow₀ hD) (by omega) hT
    (energy_positive D h hD) hV he
  have hset : levelSet (fun t => polynomial D a t ^ h) a0 T V =
      levelSet (exponentialSum151 (Finset.Ioc (D^h) (2^(6*h)*D^h))
        (weighted D h a) (fun n => Real.log n)) a0 T V := by
    ext t
    simp only [levelSet, mem_inter_iff, mem_ofPred_eq,
      power_norm_expansion D h a hD hh, upper_power]
  rw [hset]
  exact hb

/-- No mean estimate or level estimate is a premise of this finite theorem.
The amplitude cutoff v is arbitrary positive; the v5 note selects it explicitly. -/
theorem finite_fractional_moment (D h : ℕ) (a : ℕ → ℂ)
    (hD : 1 ≤ D) (hh : 1 ≤ h)
    (ha : ∀ n ∈ Finset.Ioc D (upper D), ‖a n‖ ≤ ArithmeticFunction.vonMangoldt n)
    (hm : mass D a ≤ 64) (a0 T v p : ℝ)
    (hT : 0 ≤ T) (hv : 0 < v) (hp : 2 ≤ p) (hp6 : p ≤ 6) :
    (∫ t in Icc a0 (a0+T), ‖polynomial D a t‖^((h:ℝ)*p)) ≤
      v^(p-2)*secondBudget D h T+
      bandCountBound v ((64:ℝ)^h)*(2:ℝ)^p*
        (quadraticBudget D h T*(2*(64:ℝ)^h)^(p-2)+
          sexticBudget D h T*v^(p-6)) := by
  let F : ℝ → ℂ := fun t => polynomial D a t ^ h
  have hF : Continuous F := (NormalizedMeanSquare.continuous_vertical
    (Finset.Ioc D (upper D)) a 1
    (by intro n hn; have := Finset.mem_Ioc.mp hn; omega)).pow h
  have hcap : ∀ t ∈ Icc a0 (a0+T), ‖F t‖ ≤ (64:ℝ)^h := by
    intro t _
    simpa only [F, norm_pow] using pow_le_pow_left₀ (norm_nonneg _)
      ((polynomial_mass_bound D a t).trans hm) h
  have he := energy_positive D h hD
  have hq : 0 ≤ quadraticBudget D h T :=
    quadratic_nonnegative (D^h) (6*h) T (energy D h) hT he.le
  have hs : 0 ≤ sexticBudget D h T := by
    by_cases ht : T = 0
    · simp [sexticBudget, sextic, ht]
    · have hTp : 0 < T := by
        rcases eq_or_lt_of_le hT with heq | hlt
        · exact (ht heq.symm).elim
        · exact hlt
      exact (sextic_positive (D^h) (6*h) T (energy D h)
        (one_le_pow₀ hD) (by omega) hTp he).le
  have hb := MomentThreshold.supremum_bound F a0 T v ((64:ℝ)^h) p
    (quadraticBudget D h T) (sexticBudget D h T) hF hv (by positivity)
    hp hp6 hq hs hcap (fun w hw => level_bound D h a hD hh ha hm a0 T w hT hw)
  have hlow := lower_moment D h a hD ha hm a0 T hT
  have hid (t : ℝ) : ‖F t‖^p = ‖polynomial D a t‖^((h:ℝ)*p) := by
    dsimp [F]
    rw [norm_pow, ←Real.rpow_natCast_mul (norm_nonneg _)]
  simp only [hid] at hb
  exact hb.trans (add_le_add
    (mul_le_mul_of_nonneg_left hlow (Real.rpow_nonneg hv.le _)) le_rfl)

#print axioms finite_fractional_moment
run_cmd do
  for t in [``upper_ge, ``upper_power, ``energy_positive, ``power_support_strict,
      ``full_weighted_energy, ``weighted_energy, ``power_identity,
      ``power_norm_expansion, ``polynomial_mass_bound, ``lower_moment,
      ``level_bound, ``finite_fractional_moment] do
    for ax in (← Lean.collectAxioms t) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {t}"
  Lean.logInfo "FINITE SOURCE MOMENT: VALID ONLY AFTER SUCCESSFUL COMPILATION"
end SourceMomentFinite
