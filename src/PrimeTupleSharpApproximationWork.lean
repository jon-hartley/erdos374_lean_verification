import MaskedPrimeWindowTransferWork
import FiniteWindowApproximation

/-! Exact collection and sharp-window approximation for arbitrary finite
ordered four-prime tuple sets. Multiplicities are retained. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace PrimeTupleSharpApproximationWork
open DirichletPowerCoefficients LongerTupleCollection
open Erdos374.HarmanGram152

def multiplicity (S : Finset (Fin 4 → ℕ)) (n : ℕ) : ℝ :=
  ((S.filter (fun f => productIndex f=n)).card : ℝ)

def count (S : Finset (Fin 4 → ℕ)) (L R : ℝ) : ℝ :=
  ((S.filter (fun f => L<(productIndex f : ℝ) ∧ (productIndex f : ℝ)≤R)).card : ℝ)

theorem multiplicity_bound (S : Finset (Fin 4 → ℕ))
    (hS : ∀ f∈S, ∀ i, Nat.Prime (f i)) (n : ℕ) :
    0≤multiplicity S n ∧ multiplicity S n≤256 := by
  refine ⟨Nat.cast_nonneg _,?_⟩
  change ((S.filter (fun f => productIndex f=n)).card : ℝ)≤256
  have hh := MaskedPrimeTupleMeanWork.fiber_card_le 4 S hS n
  norm_num at hh
  exact_mod_cast hh

theorem coefficient_one (S : Finset (Fin 4 → ℕ)) (n : ℕ) :
    LongerTupleCollection.coefficient S productIndex (fun _ => 1) n = (multiplicity S n : ℂ) := by
  simp [LongerTupleCollection.coefficient,multiplicity]

theorem polynomial_eq (S : Finset (Fin 4 → ℕ)) (σ t : ℝ)
    (hS : ∀ f∈S, 0<productIndex f) :
    verticalDirichlet152 (support S productIndex) (fun n => (multiplicity S n : ℂ)) σ t =
      MaskedPrimeWindowTransferWork.polynomial S (fun _ => 1) σ t := by
  rw [MaskedPrimeWindowTransferWork.polynomial_eq_cpow S _ σ t hS]
  simp_rw [← coefficient_one S]
  exact LongerTupleCollection.grouped_sum S productIndex (fun _ => 1) _

theorem sharp_eq_sum (S : Finset (Fin 4 → ℕ)) (R : ℝ) :
    SmoothedCountBoundary.sharp (support S productIndex) (multiplicity S) R =
      ∑ f∈S, if (productIndex f : ℝ)≤R then (1:ℝ) else 0 := by
  have hh := Finset.sum_fiberwise_of_maps_to
    (fun f (hf : f∈S) => show productIndex f∈support S productIndex from
      Finset.mem_image.mpr ⟨f,hf,rfl⟩)
    (fun f => if (productIndex f : ℝ)≤R then (1:ℝ) else 0)
  rw [← hh]
  apply Finset.sum_congr rfl
  intro n hn
  calc
    _ = ∑ f∈S.filter (fun f => productIndex f=n), if (n:ℝ)≤R then (1:ℝ) else 0 := by
      split_ifs <;> simp [multiplicity]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro f hf
      rw [(Finset.mem_filter.mp hf).2]

theorem count_eq_difference (S : Finset (Fin 4 → ℕ)) (L R : ℝ) (hLR : L≤R) :
    count S L R = SmoothedCountBoundary.sharp (support S productIndex) (multiplicity S) R -
      SmoothedCountBoundary.sharp (support S productIndex) (multiplicity S) L := by
  rw [sharp_eq_sum, sharp_eq_sum, ← Finset.sum_sub_distrib]
  unfold count
  simp only [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro f hf
  split_ifs <;> simp_all <;> linarith

theorem eventual_approximation :
    ∀ᶠ X : ℝ in atTop, Real.exp 1≤X ∧
      ∀ (S : Finset (Fin 4 → ℕ)),
        (∀ f∈S, (∀ i, Nat.Prime (f i)) ∧ (productIndex f : ℝ)≤2*X) →
        ∀ x δ : ℝ, x∈Icc X (2*X) → δ∈Icc 0 (1/2) →
          ‖(count S (x-x*δ) x : ℂ) - ((1/(2*Real.pi) : ℝ) : ℂ) *
            SmoothedWindowTransfer.transform
              (MaskedPrimeWindowTransferWork.polynomial S (fun _ => 1) (1+1/Real.log X))
              MellinSmoothingFunction.smoothing (X^(-19/20 : ℝ))
              (-X) X (1+1/Real.log X) δ x‖ ≤ 2*X^(2/25 : ℝ) := by
  have hlarge := (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/200)).eventually
    (eventually_ge_atTop (256:ℝ))
  filter_upwards [FiniteWindowApproximation.eventual_approximation,
    hlarge, eventually_ge_atTop (2:ℝ)] with X hm hlarge htwo
  refine ⟨hm.1,?_⟩
  intro S hS x δ hx hδ
  have hXp : 0<X := by linarith
  have hpos : ∀ f∈S, 0<productIndex f := by
    intro f hf
    exact Finset.prod_pos (fun i _ => (hS f hf).1 i |>.pos)
  have hB : 1≤⌊2*X⌋₊ := (Nat.le_floor_iff (by positivity)).mpr (by norm_num; linarith)
  have hBX : (⌊2*X⌋₊ : ℝ)≤X^2 := (Nat.floor_le (by positivity)).trans (by nlinarith)
  have hh := hm.2 (support S productIndex) (multiplicity S) ⌊2*X⌋₊ x δ hB hBX (by
    intro n hn
    obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp hn
    exact ⟨hpos f hf,(Nat.le_floor_iff (by positivity)).mpr (hS f hf).2⟩) (by
    intro n hn
    have hb := multiplicity_bound S (fun f hf => (hS f hf).1) n
    exact ⟨hb.1,hb.2.trans hlarge⟩) hx hδ
  rw [← count_eq_difference S (x-x*δ) x (by nlinarith [mul_nonneg (hXp.trans_le hx.1).le hδ.1])] at hh
  have he : verticalDirichlet152 (support S productIndex) (fun n => (multiplicity S n : ℂ))
      (1+1/Real.log X) = MaskedPrimeWindowTransferWork.polynomial S (fun _ => 1) (1+1/Real.log X) :=
    funext (fun t => polynomial_eq S _ t hpos)
  rw [he] at hh
  exact hh

#print axioms eventual_approximation
run_cmd do
  for decl in [``multiplicity_bound, ``coefficient_one, ``polynomial_eq,
      ``sharp_eq_sum, ``count_eq_difference, ``eventual_approximation] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end PrimeTupleSharpApproximationWork
