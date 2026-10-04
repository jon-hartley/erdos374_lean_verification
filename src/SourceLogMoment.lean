import SourceMomentFinite
import SourceLogMomentEnvelope

/-!
Source-specific logarithmic fractional moments, with explicit fixed constants.
STATUS: UNCOMPILED DRAFT; no kernel verification is claimed.
This module constructs the numerical hypotheses of SourceLogMomentEnvelope
from the exact budgets of SourceMomentFinite. No source mean, fractional
moment bound, or level-set bound is assumed as a theorem parameter.
The cost is log^(3h+3), hence at most log^18 for the four source orders.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
noncomputable section
open MeasureTheory Set
namespace SourceLogMoment
open SourceMomentFinite SourceLogMomentEnvelope DyadicLevelParameters

def cap (h : ℕ) : ℝ := (64:ℝ)^h
def zeta (h : ℕ) : ℝ := 2+7*(h:ℝ)
def energyConstant (h : ℕ) : ℝ := cap h*(zeta h)^h
def quadraticConstant (h : ℕ) : ℝ := 1548*(6*(h:ℝ))^3*cap h*energyConstant h
def sexticConstant (h : ℕ) : ℝ :=
  1548*1024^2*(6*(h:ℝ))^7*cap h*(energyConstant h)^3*zeta h
def secondConstant (h : ℕ) : ℝ := energyConstant h*(1+4*cap h*zeta h)
def momentConstant (h : ℕ) : ℝ :=
  2*secondConstant h+8*(1+14*(h:ℝ))*(2*cap h*quadraticConstant h+sexticConstant h)

/-- Exact scale identities and logarithmic bounds; constants absorb the fixed
64-fold interval but do not introduce a positive power of X. -/
theorem scale_data (D h : ℕ) (X T : ℝ) (hD : 1 ≤ D)
    (hX : 2 ≤ X) (hDX : (D:ℝ) ≤ X) (hT : 1 ≤ T) (hTX : T ≤ 2*X) :
    let L := 1+Real.log X
    let Q : ℝ := (D^h:ℕ)
    let R : ℝ := ((upper D)^h:ℕ)
    1 ≤ L ∧ 1 ≤ Q ∧ 1 ≤ cap h ∧ R = cap h*Q ∧
      Real.log Q ≤ (h:ℝ)*L ∧ Real.log (cap h) ≤ 6*(h:ℝ) ∧
      1+Real.log R ≤ zeta h*L ∧
      1+Real.log (R+1) ≤ zeta h*L ∧
      1+Real.log (T+1) ≤ 3*L := by
  dsimp only
  have hXp : 0 < X := by linarith
  have hDp : (0:ℝ) < D := by exact_mod_cast (by omega : 0 < D)
  have hD1 : (1:ℝ) ≤ D := by exact_mod_cast hD
  have hlogX : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
  have hlog2 : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
    linarith
  have hlog3 : Real.log 3 ≤ 2 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 3)
    linarith
  have hlog64 : Real.log 64 ≤ 6 := by
    have hh : Real.log 64 = 6*Real.log 2 := by
      rw [show (64:ℝ) = 2^6 by norm_num, Real.log_pow]
      norm_num
    rw [hh]
    linarith
  have hcap : 1 ≤ cap h := one_le_pow₀ (by norm_num)
  have hQ : (1:ℝ) ≤ ((D^h:ℕ):ℝ) := by exact_mod_cast one_le_pow₀ hD
  have hR : (1:ℝ) ≤ (((upper D)^h:ℕ):ℝ) := by
    exact_mod_cast one_le_pow₀ (hD.trans (upper_ge D))
  have hRprod : (((upper D)^h:ℕ):ℝ) = cap h*((D^h:ℕ):ℝ) := by
    simp only [upper, cap, Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat, mul_pow]
    norm_num
  have hqlog : Real.log (((D^h:ℕ):ℝ)) ≤ (h:ℝ)*Real.log X := by
    rw [Nat.cast_pow, Real.log_pow]
    exact mul_le_mul_of_nonneg_left (Real.log_le_log hDp hDX) (Nat.cast_nonneg _)
  have hclog : Real.log (cap h) ≤ 6*(h:ℝ) := by
    unfold cap
    rw [Real.log_pow]
    nlinarith [mul_le_mul_of_nonneg_left hlog64 (Nat.cast_nonneg h : (0:ℝ) ≤ _)]
  have hrlog : Real.log (((upper D)^h:ℕ):ℝ) ≤ 6*(h:ℝ)+(h:ℝ)*Real.log X := by
    rw [hRprod, Real.log_mul (by linarith : cap h ≠ 0) (by linarith : ((D^h:ℕ):ℝ) ≠ 0)]
    exact add_le_add hclog hqlog
  have hrplus : Real.log ((((upper D)^h:ℕ):ℝ)+1) ≤
      1+6*(h:ℝ)+(h:ℝ)*Real.log X := by
    have hh := Real.log_le_log (by linarith : (0:ℝ) < (((upper D)^h:ℕ):ℝ)+1)
      (show (((upper D)^h:ℕ):ℝ)+1 ≤ 2*(((upper D)^h:ℕ):ℝ) by linarith)
    rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (by linarith : (((upper D)^h:ℕ):ℝ) ≠ 0)] at hh
    linarith
  have htplus : Real.log (T+1) ≤ 2+Real.log X := by
    have hh := Real.log_le_log (by linarith : 0 < T+1)
      (show T+1 ≤ 3*X by linarith)
    rw [Real.log_mul (by norm_num : (3:ℝ) ≠ 0) hXp.ne'] at hh
    linarith
  refine ⟨by linarith,hQ,hcap,hRprod,?_,hclog,?_,?_,?_⟩
  · nlinarith [(Nat.cast_nonneg h : (0:ℝ) ≤ h)]
  · unfold zeta
    nlinarith [mul_nonneg (Nat.cast_nonneg h : (0:ℝ) ≤ _) hlogX]
  · unfold zeta
    nlinarith [mul_nonneg (Nat.cast_nonneg h : (0:ℝ) ≤ _) hlogX]
  · linarith

/-- Relate the literal inherited finite budgets to explicit powers of log X. -/
theorem budget_bounds (D h : ℕ) (X T : ℝ) (hD : 1 ≤ D)
    (hX : 2 ≤ X) (hDX : (D:ℝ) ≤ X) (hT : 1 ≤ T) (hTX : T ≤ 2*X) :
    let L := 1+Real.log X
    let Q : ℝ := (D^h:ℕ)
    quadraticBudget D h T ≤ quadraticConstant h*L^(h+1) ∧
    sexticBudget D h T ≤ sexticConstant h*(T/Q^2)*L^(3*h+2) ∧
    secondBudget D h T ≤ secondConstant h*L^(h+1)*(1+T/Q) := by
  let L := 1+Real.log X
  let Q : ℝ := (D^h:ℕ)
  let R : ℝ := ((upper D)^h:ℕ)
  have hg := scale_data D h X T hD hX hDX hT hTX
  dsimp only at hg ⊢
  change 1 ≤ L ∧ 1 ≤ Q ∧ 1 ≤ cap h ∧ R = cap h*Q ∧
    Real.log Q ≤ (h:ℝ)*L ∧ Real.log (cap h) ≤ 6*(h:ℝ) ∧
    1+Real.log R ≤ zeta h*L ∧ 1+Real.log (R+1) ≤ zeta h*L ∧
    1+Real.log (T+1) ≤ 3*L at hg
  have hLp : 0 ≤ L := by linarith [hg.1]
  have hQp : 0 < Q := by linarith [hg.2.1]
  have hCp : 0 < cap h := zero_lt_one.trans_le hg.2.2.1
  have hRp : 0 < R := by rw [hg.2.2.2.1]; exact mul_pos hCp hQp
  have hz : 0 ≤ zeta h := by unfold zeta; positivity
  have hec : 0 ≤ energyConstant h := by unfold energyConstant cap zeta; positivity
  have he0 : 0 ≤ energy D h := (energy_positive D h hD).le
  have hR1 : 1 ≤ R := by rw [hg.2.2.2.1]; nlinarith [hg.2.1,hg.2.2.1]
  have hlogR0 : 0 ≤ 1+Real.log R := by linarith [Real.log_nonneg hR1]
  have hlogRp0 : 0 ≤ 1+Real.log (R+1) := by
    linarith [Real.log_nonneg (show 1 ≤ R+1 by linarith)]
  have hel : energy D h ≤ energyConstant h*L^h/Q := by
    change ((1+Real.log R)^h*(64:ℝ)^h)/Q ≤ _
    have hlog0 : 0 ≤ 1+Real.log R := by
      have hr1 : 1 ≤ R := by rw [hg.2.2.2.1]; nlinarith [hg.2.1,hg.2.2.1]
      linarith [Real.log_nonneg hr1]
    have hh := pow_le_pow_left₀ hlog0 hg.2.2.2.2.2.2.1 h
    have hm := mul_le_mul_of_nonneg_right hh (show 0 ≤ (64:ℝ)^h by positivity)
    have hd := div_le_div_of_nonneg_right hm hQp.le
    simpa only [energyConstant,cap,mul_pow,mul_assoc,mul_comm,mul_left_comm] using hd
  have hupper : ((2^(6*h)*D^h:ℕ):ℝ) = R := by
    dsimp [R]
    rw [upper_power]
  have hq : quadraticBudget D h T ≤ quadraticConstant h*L^(h+1) := by
    unfold quadraticBudget quadratic
    rw [hupper]
    push_cast
    calc
      _ ≤ 516*(6*(h:ℝ))^3*R*(3*L)*(energyConstant h*L^h/Q) := by
        gcongr <;> first | exact hel | exact hg.2.2.2.2.2.2.2.2 | positivity
      _ = quadraticConstant h*L^(h+1) := by
        rw [hg.2.2.2.1,pow_succ]
        unfold quadraticConstant
        field_simp [hQp.ne'] <;> ring
  have hs : sexticBudget D h T ≤ sexticConstant h*(T/Q^2)*L^(3*h+2) := by
    unfold sexticBudget sextic
    rw [hupper]
    push_cast
    calc
      _ ≤ 516*1024^2*(6*(h:ℝ))^7*R*(3*L)*T*
          (energyConstant h*L^h/Q)^3*(zeta h*L) := by
        gcongr <;> first
          | exact hel
          | exact hg.2.2.2.2.2.2.2.2
          | exact hg.2.2.2.2.2.2.2.1
          | positivity
      _ = sexticConstant h*(T/Q^2)*L^(3*h+2) := by
        have hpow : L^(3*h+2) = (L^h)^3*L^2 := by
          rw [show 3*h+2 = h*3+2 by omega, pow_add, pow_mul]
        rw [hg.2.2.2.1, hpow]
        unfold sexticConstant
        field_simp [hQp.ne'] <;> ring
  have hm : secondBudget D h T ≤ secondConstant h*L^(h+1)*(1+T/Q) := by
    have hTQ : 0 ≤ T/Q := by positivity
    have hCZ : 0 ≤ 4*cap h*zeta h := by positivity
    have ha : T/Q ≤ L*(1+T/Q) := by nlinarith [hg.1]
    have hb : 4*cap h*zeta h*L ≤ 4*cap h*zeta h*(L*(1+T/Q)) := by
      nlinarith [mul_nonneg (show 0 ≤ 4*cap h*zeta h*L by positivity) hTQ]
    have hc : T/Q+4*cap h*zeta h*L ≤ (1+4*cap h*zeta h)*L*(1+T/Q) := by
      nlinarith
    unfold secondBudget
    change (T+4*R*(1+Real.log R))*energy D h ≤ _
    calc
      _ ≤ (T+4*R*(zeta h*L))*(energyConstant h*L^h/Q) := by
        gcongr <;> first | exact hel | exact hg.2.2.2.2.2.2.1 | positivity
      _ = energyConstant h*L^h*(T/Q+4*cap h*zeta h*L) := by
        rw [hg.2.2.2.1]
        field_simp [hQp.ne'] <;> ring
      _ ≤ energyConstant h*L^h*((1+4*cap h*zeta h)*L*(1+T/Q)) :=
        mul_le_mul_of_nonneg_left hc (by positivity)
      _ = secondConstant h*L^(h+1)*(1+T/Q) := by
        unfold secondConstant
        rw [pow_succ]
        ring
  exact ⟨hq,hs,hm⟩

/-- The actual logarithmic moment estimate. Its hypotheses concern only
coefficients, lengths, and exponents. In particular it does not assume the
fractional moment, a source residual bound, or a prime-interval theorem. -/
theorem logarithmic_moment (D h : ℕ) (a : ℕ → ℂ) (X a0 T p : ℝ)
    (hD : 1 ≤ D) (hh : 1 ≤ h) (hX : 2 ≤ X) (hDX : (D:ℝ) ≤ X)
    (hT : 1 ≤ T) (hTX : T ≤ 2*X) (hp : 2 ≤ p) (hp3 : p ≤ 3)
    (ha : ∀ n ∈ Finset.Ioc D (upper D), ‖a n‖ ≤ ArithmeticFunction.vonMangoldt n)
    (hm : mass D a ≤ 64) (hlen : T^4 ≤ (((D^h:ℕ):ℝ))^(p+2)) :
    (∫ t in Icc a0 (a0+T), ‖polynomial D a t‖^((h:ℝ)*p)) ≤
      momentConstant h*(1+Real.log X)^(3*h+3) := by
  let Q : ℝ := (D^h:ℕ)
  let L := 1+Real.log X
  have hd := scale_data D h X T hD hX hDX hT hTX
  have hb := budget_bounds D h X T hD hX hDX hT hTX
  dsimp only at hd hb
  have hQ : 1 ≤ Q := hd.2.1
  have hTp : 0 < T := by linarith
  have hv : 0 < cut Q T p := MomentThreshold.cutoff_positive _ _ _ (by positivity) (by norm_num)
  have hfinite := finite_fractional_moment D h a hD hh ha hm a0 T (cut Q T p) p
    (by linarith) hv hp (by linarith)
  have he := energy_positive D h hD
  have hA : 0 ≤ quadraticBudget D h T := quadratic_nonnegative _ _ _ _ (by linarith) he.le
  have hB : 0 ≤ sexticBudget D h T :=
    (sextic_positive _ _ _ _ (one_le_pow₀ hD) (by omega) hTp he).le
  have hM : 0 ≤ secondBudget D h T := by
    have hN : (1:ℝ) ≤ (((upper D)^h:ℕ):ℝ) := by
      exact_mod_cast one_le_pow₀ (hD.trans (upper_ge D))
    have hlog := Real.log_nonneg hN
    unfold secondBudget
    positivity
  have henv := envelope Q T p L (cap h) (quadraticBudget D h T) (sexticBudget D h T)
    (secondBudget D h T) (quadraticConstant h) (sexticConstant h) (secondConstant h) h
    hQ hT hp hp3 hd.1 hd.2.2.1 hd.2.2.2.2.1 hd.2.2.2.2.2.1 hlen
    hA hB hM
    (by unfold quadraticConstant energyConstant cap zeta; positivity)
    (by unfold sexticConstant energyConstant cap zeta; positivity)
    (by unfold secondConstant energyConstant cap zeta; positivity)
    hb.1 hb.2.1 hb.2.2
  exact hfinite.trans henv

/-- The four convolution orders needed by the source cost at most log^18. -/
theorem source_order_moment (D h : ℕ) (a : ℕ → ℂ) (X a0 T p : ℝ)
    (hD : 1 ≤ D) (hh : 2 ≤ h) (hh5 : h ≤ 5)
    (hX : 2 ≤ X) (hDX : (D:ℝ) ≤ X) (hT : 1 ≤ T) (hTX : T ≤ 2*X)
    (hp : 2 ≤ p) (hp3 : p ≤ 3)
    (ha : ∀ n ∈ Finset.Ioc D (upper D), ‖a n‖ ≤ ArithmeticFunction.vonMangoldt n)
    (hm : mass D a ≤ 64) (hlen : T^4 ≤ (((D^h:ℕ):ℝ))^(p+2)) :
    (∫ t in Icc a0 (a0+T), ‖polynomial D a t‖^((h:ℝ)*p)) ≤
      momentConstant h*(1+Real.log X)^18 := by
  have hh1 : 1 ≤ h := by omega
  apply (logarithmic_moment D h a X a0 T p hD hh1 hX hDX hT hTX hp hp3 ha hm hlen).trans
  apply mul_le_mul_of_nonneg_left
  · exact pow_le_pow_right₀ (by linarith [Real.log_nonneg (show 1 ≤ X by linarith)]) (by omega)
  · unfold momentConstant secondConstant quadraticConstant sexticConstant energyConstant cap zeta
    positivity

#print axioms logarithmic_moment
#print axioms source_order_moment
run_cmd do
  for t in [``scale_data, ``budget_bounds, ``logarithmic_moment, ``source_order_moment] do
    for ax in (← Lean.collectAxioms t) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {t}"
  Lean.logInfo "ACTUAL SOURCE LOGARITHMIC MOMENT: VALID ONLY AFTER SUCCESSFUL COMPILATION"
end SourceLogMoment
