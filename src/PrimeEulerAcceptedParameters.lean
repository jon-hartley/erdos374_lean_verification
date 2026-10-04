import PrimeEulerAcceptedInner

/-! Parameter form of the actual accepted-prime exponential bound. The small
accepted-cutoff case is empty and is treated without any estimate below 2. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped BigOperators
open Real Set

namespace PrimeEulerAcceptedParameters
open PrimeEulerAcceptedInner SieveStoppingExpansion

def parameter (T z : ℝ) : ℝ := log T / log z
def beta (s : ℝ) : ℝ := min 1 (s/3)
def terminalParameter (s : ℝ) : ℝ := max 2 (s-1)

def upperEnvelope (s k : ℝ) : ℝ :=
  (1+k/beta s) * exp (-terminalParameter s) *
    (1/s+k*(1/(beta s)^2+2*(terminalParameter s+2)/s^2))

theorem parameter_ge_one (T z : ℝ) (hz : 2 ≤ z) (hT : z ≤ T) :
    1 ≤ parameter T z := by
  have hlog : 0 < log z := log_pos (by linarith)
  unfold parameter
  rw [le_div_iff₀ hlog, one_mul]
  exact log_le_log (by linarith) hT

theorem beta_pos (s : ℝ) (hs : 1 ≤ s) : 0 < beta s := by
  unfold beta
  exact lt_min (by norm_num) (div_pos (by linarith) (by norm_num))

theorem terminalParameter_eq (s : ℝ) (hs : 1 ≤ s) :
    s/beta s-1 = terminalParameter s := by
  have hs0 : s ≠ 0 := by linarith
  by_cases hs3 : s ≤ 3
  · have hb : beta s = s/3 := min_eq_right (by linarith)
    have hm : terminalParameter s = 2 := max_eq_left (by linarith)
    rw [hb, hm]
    field_simp
    ring
  · have hb : beta s = 1 := min_eq_left (by linarith)
    have hm : terminalParameter s = s-1 := max_eq_right (by linarith)
    rw [hb, hm]
    ring

theorem log_cutoff_beta (T z : ℝ) (hz : 2 ≤ z) :
    log (cutoff T z) = beta (parameter T z) * log z := by
  have hz0 : 0 < z := by linarith
  have hlog : 0 < log z := log_pos (by linarith)
  rw [log_cutoff T z hz0]
  unfold beta parameter
  rw [min_mul_of_nonneg 1 (log T / log z / 3) hlog.le]
  congr 1
  · ring
  · field_simp

theorem upperEnvelope_nonneg (s k : ℝ) (hs : 1 ≤ s) (hk : 0 ≤ k) :
    0 ≤ upperEnvelope s k := by
  have hb := beta_pos s hs
  have hs0 : 0 < s := by linarith
  have hm : 0 ≤ terminalParameter s+2 := by
    have hh : 2 ≤ terminalParameter s := le_max_left _ _
    linarith
  unfold upperEnvelope
  positivity

/-- Pure algebra converting the cutoff-level estimate into the normalized
parameter expression. Positivity here is analytic; no prime bound is assumed. -/
theorem parameter_expression_identity (s B K : ℝ) (hs : 1 ≤ s) (hB : 0 < B) :
    ((B / (beta s*B)) * (1+K/(beta s*B))) *
      (exp (1-(s*B)/(beta s*B)) *
        (1/((s*B)/(beta s*B)) + (K/(beta s*B)) *
          (1+2*((s*B)/(beta s*B)+1)/((s*B)/(beta s*B))^2))) =
      upperEnvelope s (K/B) := by
  have hb := beta_pos s hs
  have hs0 : s ≠ 0 := by linarith
  have hb0 : beta s ≠ 0 := hb.ne'
  have hB0 : B ≠ 0 := hB.ne'
  have hratio : (s*B)/(beta s*B) = s/beta s := by field_simp
  have he : 1-s/beta s = -terminalParameter s := by
    linarith [terminalParameter_eq s hs]
  rw [hratio, he]
  unfold upperEnvelope
  have hm : terminalParameter s = s/beta s-1 := (terminalParameter_eq s hs).symm
  rw [hm]
  field_simp
  ring

/-- The actual accepted-prime estimate, valid at every parent cutoff ≥2.
The complete smaller-prime pool and strict cubic acceptance are retained. -/
theorem accepted_exponential_bound (T z : ℝ) (hz : 2 ≤ z) (hT : z ≤ T) :
    acceptedExponentialMass T z ≤
      upperEnvelope (parameter T z) (PrimeEulerDimensionOne.errorConstant / log z) := by
  have hT1 : 1 < T := by linarith
  have hs := parameter_ge_one T z hz hT
  have hlog : 0 < log z := log_pos (by linarith)
  by_cases hc : cutoff T z ≤ 2
  · rw [acceptedExponentialMass_eq_zero T z (by linarith) hc]
    exact upperEnvelope_nonneg _ _ hs
      (div_nonneg PrimeEulerDimensionOne.errorConstant_pos.le hlog.le)
  · have hbound := accepted_exponential_bound_cutoff T z hT1 (le_of_not_ge hc)
    have hcut := log_cutoff_beta T z hz
    have hlevel : log T = parameter T z * log z := by
      unfold parameter
      field_simp
    apply hbound.trans_eq
    rw [hcut, hlevel]
    exact parameter_expression_identity (parameter T z) (log z)
      PrimeEulerDimensionOne.errorConstant hs hlog

run_cmd do
  for decl in [``parameter_ge_one, ``beta_pos, ``terminalParameter_eq,
    ``log_cutoff_beta, ``upperEnvelope_nonneg, ``parameter_expression_identity,
    ``accepted_exponential_bound] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ACTUAL ACCEPTED-PRIME PARAMETER BOUND PASSED"

end PrimeEulerAcceptedParameters
end
