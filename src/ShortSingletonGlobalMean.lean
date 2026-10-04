import ShortSingletonWeightedModes
import ShortSingletonDyadic
import ShortSingletonMaskedCollection
import ShortSingletonCosts

/-! A uniform positive-power mean-square saving for the complete finite
masked sum in the singleton factor ranges. Original pair representations,
arbitrary prime-dependent endpoints, and physical cutoff endpoints remain.
The grid is fixed before the eventual threshold; other data are uniform. -/

set_option autoImplicit false
set_option maxHeartbeats 9000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace ShortSingletonGlobalMean
open ShortSingletonMasks ShortSingletonMaskedCollection ShortSingletonComplex
open FourPrimePartition

/-- The grid family is fixed, while all finite supports, masks, and bounded
complex pair weights may vary with X. There is no Fourier-mode count loss. -/
theorem eventually_bound (J : Finset ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℝ in atTop, Real.exp 1 ≤ X ∧
      ∀ (S : Finset (ℕ × ℕ)) (B : Finset ℕ) (Q : ℕ)
        (w : ℕ × ℕ → ℂ) (lo hi : ℕ → ℕ → ℕ) (cut : ℕ → ℕ),
        let Y : ℝ := X ^ (101 / 1000 : ℝ) / 2
        (∀ m ∈ ShortSingletonCollection.support S,
          X ^ (9 / 35 : ℝ) ≤ (m : ℝ) ∧ (m : ℝ) < X ^ (1003 / 2000 : ℝ)) →
        (∀ q ∈ B, X ^ (1 / 25 : ℝ) < (q : ℝ) ∧ (q : ℝ) ≤ X ^ (8 / 35 : ℝ)) →
        (∀ q ∈ B, q ≤ Q) → (Q : ℝ) ≤ X →
        (∀ a ∈ S, ‖w a‖ ≤ 1) →
        (1 / X) * (∫ x in Icc X (2 * X),
          (∑ j ∈ J, maskedSum S B w (lo j) (hi j) cut
            (x - x * (Y / X)) x).re ^ 2) ≤ Y ^ 2 * X ^ (-c) := by
  obtain ⟨c, hc, hweighted⟩ := ShortSingletonWeightedModes.eventually_bound_varying.{0}
  refine ⟨c / 2, by positivity, ?_⟩
  filter_upwards [hweighted,
    eventual_modeCoefficient_cap (c / 16) (by positivity),
    ShortSingletonCosts.eventually_total_mass_cap (J.card : ℝ) (c / 16)
      (Nat.cast_nonneg _) (by positivity),
    ShortSingletonCosts.eventually_absorb_square_cost c hc,
    eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1000)]
    with X hmean hcoeff hmass habsorb hX hlog
  refine ⟨hmean.1, ?_⟩
  intro S B Q w lo hi cut
  dsimp only
  intro hS hB hBQ hQ hw
  let A : Finset ℕ := ShortSingletonCollection.support S
  let F : Finset (ℕ × ℕ) := family A B 1 1
    (FourPrimeGlobalPartition.k X) (FourPrimeGlobalPartition.k X)
  let I : Finset (ℕ × (Mode Q × (ℕ × ℕ))) := J ×ˢ ((Finset.univ : Finset (Mode Q)) ×ˢ F)
  let M : (ℕ × (Mode Q × (ℕ × ℕ))) → ℕ := fun i => scale 1 i.2.2.1
  let N : (ℕ × (Mode Q × (ℕ × ℕ))) → ℕ := fun i => scale 1 i.2.2.2
  let sm : (ℕ × (Mode Q × (ℕ × ℕ))) → Finset ℕ := fun i => block A 1 i.2.2.1
  let sn : (ℕ × (Mode Q × (ℕ × ℕ))) → Finset ℕ := fun i => block B 1 i.2.2.2
  let coeff : (ℕ × (Mode Q × (ℕ × ℕ))) → ℂ := fun i => scalar Q i.2.1
  let a : (ℕ × (Mode Q × (ℕ × ℕ))) → ℕ → ℂ := fun i =>
    modeCoefficient S Q i.2.1 w (lo i.1) (hi i.1) cut
  let b : (ℕ × (Mode Q × (ℕ × ℕ))) → ℕ → ℂ := fun i => rightPhase Q i.2.1
  let T : ℝ := X ^ (c / 16)
  let Y : ℝ := X ^ (101 / 1000 : ℝ) / 2
  have hXp : 0 < X := by linarith
  have hT : 0 < T := by positivity
  have hindex : ∀ i ∈ I, i.2.2 ∈ F := by
    intro i hiI
    exact (Finset.mem_product.mp (Finset.mem_product.mp hiI).2).2
  have hrect : ∀ i ∈ I,
      1 ≤ M i ∧ 1 ≤ N i ∧
      X ^ (59 / 200 : ℝ) ≤ ((M i * N i : ℕ) : ℝ) ∧
      ((M i * N i : ℕ) : ℝ) ≤ X ^ (731 / 1000 : ℝ) ∧
      X ^ (39 / 1000 : ℝ) ≤ (N i : ℝ) ∧ (N i : ℝ) ≤ X ^ (8 / 35 : ℝ) ∧
      (∀ n ∈ sm i, M i < n ∧ n ≤ 2 * M i) ∧
      (∀ n ∈ sn i, N i < n ∧ n ≤ 2 * N i) := by
    intro i hiI
    exact ShortSingletonDyadic.active_rectangle X A B hX hlog hS hB i.2.2 (hindex i hiI)
  have ha : ∀ i ∈ I, ∀ n ∈ sm i, ‖a i n‖ ≤ T := by
    intro i _ n hn
    have hnA : n ∈ A := ((mem_block A 1 i.2.2.1 n).mp hn).1
    have hnpos : 0 < n := by
      have hp := (Real.rpow_pos_of_pos hXp (9 / 35 : ℝ)).trans_le (hS n hnA).1
      exact_mod_cast hp
    have hnX : (n : ℝ) ≤ X ^ 2 := by
      apply (hS n hnA).2.le.trans
      simpa only [Real.rpow_two] using
        Real.rpow_le_rpow_of_exponent_le hX.le
          (by norm_num : (1003 / 2000 : ℝ) ≤ 2)
    exact hcoeff.2 S Q i.2.1 w (lo i.1) (hi i.1) cut n hnpos hnX hw
  have hb : ∀ i ∈ I, ∀ n ∈ sn i, ‖b i n‖ ≤ 1 := by
    intro i _ n _
    exact (rightPhase_norm Q i.2.1 n).le
  have hcall := hmean.2 (ℕ × (Mode Q × (ℕ × ℕ))) I M N sm sn coeff a b T hT
    (fun i hiI => (hrect i hiI).1)
    (fun i hiI => (hrect i hiI).2.1)
    (fun i hiI => (hrect i hiI).2.2.1)
    (fun i hiI => (hrect i hiI).2.2.2.1)
    (fun i hiI => (hrect i hiI).2.2.2.2.1)
    (fun i hiI => (hrect i hiI).2.2.2.2.2.1)
    (fun i hiI => (hrect i hiI).2.2.2.2.2.2.1)
    (fun i hiI => (hrect i hiI).2.2.2.2.2.2.2) ha hb
  have hmass_eq : (∑ i ∈ I, ‖coeff i‖) =
      (J.card : ℝ) * (F.card : ℝ) * (∑ t : Mode Q, ‖scalar Q t‖) := by
    simp only [I, coeff, Finset.sum_product, Finset.sum_const, nsmul_eq_mul,
      ← Finset.mul_sum]
    ring
  have hmass_cap : (∑ i ∈ I, ‖coeff i‖) ≤ X ^ (c / 16) := by
    rw [hmass_eq]
    exact hmass.2 A B Q hQ
  have hpoint (L R : ℝ) :
      (∑ j ∈ J, maskedSum S B w (lo j) (hi j) cut L R) =
      ∑ i ∈ I, coeff i * productSum (sm i) (sn i) (a i) (b i) L R := by
    simp only [I, coeff, sm, sn, a, b, Finset.sum_product]
    apply Finset.sum_congr rfl
    intro j _
    rw [maskedSum_expansion S B Q w (lo j) (hi j) cut L R hBQ]
    apply Finset.sum_congr rfl
    intro t _
    rw [ShortSingletonDyadic.productSum_eq_sum_family X A B
      (modeCoefficient S Q t w (lo j) (hi j) cut) (rightPhase Q t) L R hX hlog hS hB,
      Finset.mul_sum]
  have heq :
      (fun x : ℝ =>
        (∑ j ∈ J, maskedSum S B w (lo j) (hi j) cut (x - x * (Y / X)) x).re ^ 2) =
      (fun x =>
        (∑ i ∈ I, coeff i * productSum (sm i) (sn i) (a i) (b i)
          (x - x * (Y / X)) x).re ^ 2) := by
    funext x
    exact congrArg (fun z : ℂ => z.re ^ 2) (hpoint _ _)
  have habs := habsorb.2 T (∑ i ∈ I, ‖coeff i‖) Y hT.le le_rfl
    (Finset.sum_nonneg (fun i _ => norm_nonneg _)) hmass_cap
  calc
    _ = (1 / X) * (∫ x in Icc X (2 * X),
        (∑ i ∈ I, coeff i * productSum (sm i) (sn i) (a i) (b i)
          (x - x * (Y / X)) x).re ^ 2) :=
      congrArg (fun f : ℝ → ℝ => (1 / X) * (∫ x in Icc X (2 * X), f x)) heq
    _ ≤ 4 * T ^ 2 * (∑ i ∈ I, ‖coeff i‖) ^ 2 * Y ^ 2 * X ^ (-c) := hcall
    _ ≤ Y ^ 2 * X ^ (-(c / 2)) := habs

#print axioms eventually_bound
run_cmd do
  for ax in (← Lean.collectAxioms ``eventually_bound) do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"
  Lean.logInfo "COMPLETE MASKED SINGLETON-RANGE POWER-SAVING MEAN SQUARE PASSED"

end ShortSingletonGlobalMean
