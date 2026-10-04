import CancellationSignedMean
import PositiveSharpRemainderRegularity

/-! Exact one-sided first moments of the complete actual signed remainder.
The signed bias is proved; a saving for either one-sided moment remains open. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open Filter MeasureTheory Set
namespace TailRemainderMean
open PositiveSharpBoxedCount PositiveSharpRemainderRegularity

def positiveMean (X s Y : ℝ) : ℝ :=
  (∫x in Icc X (2*X), max (signedRemainder X s x (x*Y/X)) 0)/X

def negativeMean (X s Y : ℝ) : ℝ :=
  (∫x in Icc X (2*X), max (-signedRemainder X s x (x*Y/X)) 0)/X

def absoluteMean (X s Y : ℝ) : ℝ :=
  (∫x in Icc X (2*X), |signedRemainder X s x (x*Y/X)|)/X

theorem positiveMean_nonneg (X s Y : ℝ) (hX : 0≤X) : 0≤positiveMean X s Y := by
  apply div_nonneg _ hX
  exact integral_nonneg (fun x => le_max_right _ _)

theorem negativeMean_nonneg (X s Y : ℝ) (hX : 0≤X) : 0≤negativeMean X s Y := by
  apply div_nonneg _ hX
  exact integral_nonneg (fun x => le_max_right _ _)

theorem mean_balance (X s Y : ℝ) :
    positiveMean X s Y-negativeMean X s Y =
      (∫x in Icc X (2*X), signedRemainder X s x (x*Y/X))/X := by
  unfold positiveMean negativeMean
  rw [←sub_div,←integral_sub (signedRemainder_integrable X s Y).pos_part
    (signedRemainder_integrable X s Y).neg_part]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by
    dsimp
    rcases le_total 0 (signedRemainder X s x (x*Y/X)) with h|h
    · rw [max_eq_left h,max_eq_right (by linarith)]
      ring
    · rw [max_eq_right h,max_eq_left (by linarith)]
      ring)

theorem absoluteMean_eq (X s Y : ℝ) :
    absoluteMean X s Y=positiveMean X s Y+negativeMean X s Y := by
  unfold absoluteMean positiveMean negativeMean
  rw [←add_div,←integral_add (signedRemainder_integrable X s Y).pos_part
    (signedRemainder_integrable X s Y).neg_part]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by
    dsimp
    rcases le_total 0 (signedRemainder X s x (x*Y/X)) with h|h
    · rw [abs_of_nonneg h,max_eq_left h,max_eq_right (by linarith)]
      ring
    · rw [abs_of_nonpos h,max_eq_right h,max_eq_left (by linarith)]
      ring)

theorem eventually_tail_balance (s : ℝ) (A : ℕ) (hs : 0<s) (hs1 : s≤1/1000) :
    ∀ᶠ X:ℝ in atTop, 1<X ∧ ∀Y:ℝ, 0≤Y → Y<X →
      |positiveMean X s Y-negativeMean X s Y|≤Y/(Real.log X)^A := by
  filter_upwards [CancellationSignedMean.eventually_signed_mean_log s A hs hs1]
    with X hX
  exact ⟨hX.1,fun Y hY hYX => by rw [mean_balance]; exact hX.2 Y hY hYX⟩

theorem eventually_positive_of_negative (s C : ℝ) (A : ℕ)
    (hs : 0<s) (hs1 : s≤1/1000) :
    ∀ᶠ X:ℝ in atTop, 1<X ∧ ∀Y:ℝ, 0≤Y → Y<X →
      negativeMean X s Y≤C*Y/(Real.log X)^A →
      positiveMean X s Y≤(C+1)*Y/(Real.log X)^A ∧
      absoluteMean X s Y≤(2*C+1)*Y/(Real.log X)^A := by
  filter_upwards [eventually_tail_balance s A hs hs1] with X hX
  refine ⟨hX.1,?_⟩
  intro Y hY hYX hn
  have hb := (abs_le.mp (hX.2 Y hY hYX)).2
  have hp : positiveMean X s Y≤(C+1)*Y/(Real.log X)^A := by
    have he : (C+1)*Y/(Real.log X)^A=C*Y/(Real.log X)^A+Y/(Real.log X)^A := by ring
    rw [he]
    linarith
  refine ⟨hp,?_⟩
  rw [absoluteMean_eq]
  have he : (2*C+1)*Y/(Real.log X)^A=(C+1)*Y/(Real.log X)^A+C*Y/(Real.log X)^A := by ring
  rw [he]
  linarith

run_cmd do
  for decl in [``positiveMean,``negativeMean,``absoluteMean,``positiveMean_nonneg,
      ``negativeMean_nonneg,``mean_balance,``absoluteMean_eq,``eventually_tail_balance,
      ``eventually_positive_of_negative] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ACTUAL ONE-SIDED REMAINDER MEANS BALANCED BY PROVED SIGNED BIAS; TAIL SAVING OPEN"
end TailRemainderMean
end
