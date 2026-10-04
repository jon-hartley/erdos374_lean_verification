import MomentResidualEven
import PolynomialLogEnvelope

/-! Full-height mean square for complex coefficients supported at scale X.
An arbitrarily small coefficient power cap suffices for a subpower energy. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators
namespace CompletedBandEnergyWork
open Erdos374.HarmanGram152

def energyConstant : ℝ := 1033*129*256^2

theorem band_energy (X W σ a b : ℝ) (S : Finset ℕ) (c : ℕ→ℂ)
    (hX : 256≤X) (hW : 0≤W) (hσ : 1≤σ) (hab : a≤b) (hlen : b-a≤X)
    (hS : ∀n∈S,0<n ∧ X/256≤(n:ℝ) ∧ (n:ℝ)≤129*X)
    (hc : ∀n∈S,‖c n‖≤W) :
    (∫t in Icc a b,‖verticalDirichlet152 S c σ t‖^2)≤energyConstant*(1+Real.log X)*W^2 := by
  have hXp : 0<X := by linarith
  let N := ⌊129*X⌋₊
  have hN : 1≤N := (Nat.le_floor_iff (by positivity)).mpr (by norm_num only [Nat.cast_one]; linarith)
  have hNX : (N:ℝ)≤129*X := Nat.floor_le (by positivity)
  have hSN : ∀n∈S,1≤n ∧ n≤N := fun n hn => ⟨(hS n hn).1,Nat.le_floor (hS n hn).2.2⟩
  have hcard : (S.card:ℝ)≤129*X := by
    have hh : S⊆Finset.Ioc 0 N := fun n hn => Finset.mem_Ioc.mpr (hSN n hn)
    have hb : S.card≤N := by simpa using Finset.card_le_card hh
    exact (by exact_mod_cast hb : (S.card:ℝ)≤N).trans hNX
  have hE : (∑n∈S,‖c n‖^2/(n:ℝ)^2)≤129*X*W^2/(X/256)^2 := by
    calc
      _ ≤ ∑_n∈S,W^2/(X/256)^2 := by
        apply Finset.sum_le_sum
        intro n hn
        apply (div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hc n hn) 2) (sq_nonneg _)).trans
        exact div_le_div_of_nonneg_left (sq_nonneg W) (by positivity)
          (pow_le_pow_left₀ (by positivity : 0≤X/256) (hS n hn).2.1 2)
      _ = (S.card:ℝ)*W^2/(X/256)^2 := by simp [div_eq_mul_inv,mul_assoc]
      _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcard (sq_nonneg W)) (sq_nonneg _)
  have hlog : 0≤Real.log X := Real.log_nonneg (by linarith)
  have hlogN : 0≤Real.log (N:ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  have hlogNX : Real.log (N:ℝ)≤2*Real.log X := by
    have hp : (0:ℝ)<N := by exact_mod_cast hN
    calc
      _ ≤ Real.log (129*X) := Real.log_le_log hp hNX
      _ = Real.log 129+Real.log X := Real.log_mul (by norm_num) hXp.ne'
      _ ≤ _ := by have := Real.log_le_log (by norm_num : (0:ℝ)<129) (show 129≤X by linarith); linarith
  have hfactor : b-a+4*(N:ℝ)*(1+Real.log (N:ℝ))≤1033*X*(1+Real.log X) := by
    have hh := mul_le_mul hNX (show 1+Real.log (N:ℝ)≤2*(1+Real.log X) by linarith)
      (by linarith : 0≤1+Real.log (N:ℝ)) (by positivity : 0≤129*X)
    nlinarith
  have hm := MomentResidualEven.weighted_normalized_mean_square S c N hN hSN σ hσ _ hE a b hab
  apply hm.trans
  calc
    _ ≤ (1033*X*(1+Real.log X))*(129*X*W^2/(X/256)^2) :=
      mul_le_mul_of_nonneg_right hfactor (by positivity)
    _ = _ := by unfold energyConstant; field_simp

theorem eventually_band_energy (η : ℝ) (hη : 0<η) :
    ∀ᶠ X : ℝ in atTop, 256≤X ∧ ∀ (S : Finset ℕ) (c : ℕ→ℂ) (σ a b : ℝ),
      1≤σ → a≤b → b-a≤X →
      (∀n∈S,0<n ∧ X/256≤(n:ℝ) ∧ (n:ℝ)≤129*X) →
      (∀n∈S,‖c n‖≤X^(η/4)) →
      (∫t in Icc a b,‖verticalDirichlet152 S c σ t‖^2)≤X^η := by
  filter_upwards [PolynomialLogEnvelope.eventually_bound energyConstant 1 (η/2)
    (by unfold energyConstant; positivity) (by positivity),eventually_ge_atTop (256:ℝ)] with X hbudget hX
  refine ⟨hX,?_⟩
  intro S c σ a b hσ hab hlen hS hc
  have hXp : 0<X := by linarith
  apply (band_energy X (X^(η/4)) σ a b S c hX (by positivity) hσ hab hlen hS hc).trans
  have hh := mul_le_mul_of_nonneg_right hbudget.2 (sq_nonneg (X^(η/4)))
  simp only [pow_one] at hh
  apply hh.trans_eq
  rw [←Real.rpow_mul_natCast hXp.le,←Real.rpow_add hXp]
  congr 1
  norm_num
  ring

run_cmd do
  for decl in [``band_energy, ``eventually_band_energy] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end CompletedBandEnergyWork
