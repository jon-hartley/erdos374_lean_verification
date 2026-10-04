import OuterBandMeanWork

/-! A quantitative logarithmic energy-to-first-mean adapter for the actual
normalized smoothed window. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Filter MeasureTheory Set
namespace SmoothedWindowLogBudgetWork
open MellinSmoothingFunction

def window (X Y ε a b : ℝ) (F : ℝ→ℂ) (x : ℝ) : ℂ :=
  ((1/(2*Real.pi):ℝ):ℂ)*SmoothedWindowTransfer.transform F smoothing ε a b (1+1/Real.log X) (Y/X) x

theorem eventually_first (C : ℝ) (hC : 0≤C) (A : ℕ) :
    ∀ᶠ X : ℝ in atTop,Real.exp 1≤X ∧ ∀(Y ε a b : ℝ) (F : ℝ→ℂ),
      0<Y → Y<X → ε∈Ioo 0 1 → a≤b → b-a≤X → Continuous F →
      (∫t in Icc a b,‖F t‖^2)≤C/(Real.log X)^(2*A+2) →
      (1/X)*(∫x in Icc X (2*X),‖window X Y ε a b F x‖)≤Y/(Real.log X)^A := by
  filter_upwards [eventually_ge_atTop (Real.exp 1),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop ((8192*Real.exp 2)*C)),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with X hX hconst hlog
  refine ⟨hX,?_⟩
  intro Y ε a b F hY hYX hε hab hlen hF henergy
  have hXp : 0<X := (Real.exp_pos 1).trans_le hX
  have hl : 0<Real.log X := by linarith
  have hσ : 0<1+1/Real.log X := by positivity
  have hfactor : ((8192*Real.exp 2)*Real.log X)*(C/(Real.log X)^(2*A+2))≤1/(Real.log X)^(2*A) := by
    calc
      _ = ((8192*Real.exp 2)*C)*Real.log X/((Real.log X)^(2*A)*(Real.log X)^2) := by rw [pow_add]; ring
      _ ≤ Real.log X*Real.log X/((Real.log X)^(2*A)*(Real.log X)^2) := by gcongr
      _ = _ := by field_simp
  have ht := SmoothedWindowTransfer.mean_square_bound smoothing differentiable support nonnegative mass_one
    X Y ε a b hX hY.le hYX hε hab hlen F hF
  have hb : (1/X)*(∫x in Icc X (2*X),
      ‖SmoothedWindowTransfer.transform F smoothing ε a b (1+1/Real.log X) (Y/X) x‖^2)≤(Y/(Real.log X)^A)^2 := by
    apply ht.trans
    calc
      _ ≤ (8192*Real.exp 2)*Y^2*Real.log X*(C/(Real.log X)^(2*A+2)) :=
        mul_le_mul_of_nonneg_left henergy (by positivity)
      _ = Y^2*(((8192*Real.exp 2)*Real.log X)*(C/(Real.log X)^(2*A+2))) := by ring
      _ ≤ Y^2*(1/(Real.log X)^(2*A)) := mul_le_mul_of_nonneg_left hfactor (sq_nonneg _)
      _ = _ := by rw [div_pow,pow_mul]; ring
  have hn := SpatialErrorBudget.normalize_mean_square _ X _ hXp hb
  have hc : ContinuousOn (window X Y ε a b F) (Ioi 0) :=
    (SmoothedWindowRegularity.continuousOn_transform F smoothing ε a b _ _ hF hε hσ
      ((div_lt_one hXp).mpr hYX) differentiable nonnegative support mass_one).const_mul _
  have hc' := hc.mono (show Icc X (2*X)⊆Ioi 0 from fun x hx => hXp.trans_le hx.1)
  have hh := TripleFirstMean.absolute_mean_le (fun x => ‖window X Y ε a b F x‖) X (Y/(Real.log X)^A)
    hXp (by positivity) (hc'.norm.integrableOn_compact isCompact_Icc)
    ((hc'.norm.pow 2).integrableOn_compact isCompact_Icc) hn
  simpa only [abs_norm] using hh

run_cmd do
  for decl in [``eventually_first] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end SmoothedWindowLogBudgetWork
