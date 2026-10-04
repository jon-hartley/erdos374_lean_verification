import SieveSignedScalarBudget

/-! Stability of the changing-cutoff upper coefficient, including the
Euler-ratio factor and reciprocal-prime error terms. This is scalar
analysis; the separate actual weighted prime-sum transfer is not assumed
or concluded by this module. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open Real Filter
open scoped Topology
namespace SieveWeightedScalarBudget

def alpha (s : ℝ) : ℝ := (26/105)*(1-3*s)
def beta (s : ℝ) : ℝ := 26/105-(22/35)*s
def upperExponent (s : ℝ) : ℝ := 26/35-2*s
def topExponent (t : ℝ) : ℝ := 1/2+log 2*t/2
def integralCoefficient (k a b : ℝ) : ℝ := (1/k)*log (b*(k-a)/(a*(k-b)))

/-- t represents 1/log(X). The common comparison exponent beta accounts
for the fact that z4(p) can exceed z1 at positive s. -/
def aggregate (s t : ℝ) : ℝ :=
  (452/375)*beta s*exp (84*t)*
    (3*integralCoefficient (1-3*s) (9/35) (topExponent t)+
      2*integralCoefficient (upperExponent s) (alpha s) (9/35)+
      30*t/((9/35)*((1-3*s)-topExponent t))+
      20*t/(alpha s*(upperExponent s-9/35)))

theorem aggregate_at_zero : aggregate 0 0 = SieveSignedScalarBudget.negativeBudget (77/125) := by
  norm_num [aggregate, beta, integralCoefficient, upperExponent, alpha,
    topExponent, SieveSignedScalarBudget.negativeBudget]
  ring

theorem aggregate_continuous :
    ContinuousAt (fun p : ℝ × ℝ => aggregate p.1 p.2) (0, 0) := by
  unfold aggregate beta integralCoefficient upperExponent alpha topExponent
  fun_prop (disch := norm_num)

theorem aggregate_near_zero :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s t : ℝ, |s| < δ → |t| < δ →
      aggregate s t ≤ 1-(1847/2677500:ℝ) := by
  have hbase : aggregate 0 0 < 1-(1847/2677500:ℝ) := by
    rw [aggregate_at_zero]
    linarith [SieveSignedScalarBudget.negative_budget_gap (77/125) (by norm_num) (by norm_num)]
  have he := aggregate_continuous.eventually_lt_const hbase
  obtain ⟨δ, hδ, hb⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨δ, hδ, ?_⟩
  intro s t hs ht
  apply (hb (y := (s,t)) ?_).le
  simpa only [Prod.dist_eq, Real.dist_eq, sub_zero] using max_lt hs ht

theorem uniformly_large_X :
    ∃ δ X₀ : ℝ, 0 < δ ∧ 1 < X₀ ∧ ∀ s X : ℝ, |s| < δ → X₀ ≤ X →
      aggregate s (1/log X) ≤ 1-(1847/2677500:ℝ) := by
  obtain ⟨δ, hδ, hb⟩ := aggregate_near_zero
  have ht : Tendsto (fun X : ℝ => 1/log X) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_log_atTop
  have hta : Tendsto (fun X : ℝ => |1/log X|) atTop (𝓝 0) := by
    simpa only [abs_zero] using ht.abs
  have ha : ∀ᶠ X : ℝ in atTop, |1/log X| < δ := hta.eventually_lt_const hδ
  obtain ⟨A, hA⟩ := eventually_atTop.mp ha
  refine ⟨δ, max 2 A, hδ, lt_of_lt_of_le (by norm_num : (1:ℝ) < 2) (le_max_left _ _), ?_⟩
  intro s X hs hX
  exact hb s (1/log X) hs (hA X ((le_max_right _ _).trans hX))

run_cmd do
  for decl in [``aggregate_at_zero, ``aggregate_continuous,
      ``aggregate_near_zero, ``uniformly_large_X] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "CHANGING-CUTOFF SCALAR BUDGET STAYS BELOW ONE; ACTUAL SUM TRANSFER SEPARATE"
end SieveWeightedScalarBudget
end
