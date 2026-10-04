import LongPairEdgeWeightedModesWork
import LongPairEdgeDyadicWork
import LongerTupleJointExpansion
import ShortSingletonCosts

/-! A positive-power mean-square estimate for an original masked sum with
ordered representations and jointly active rectangles. The relation is
imposed before Fourier expansion. All representation collisions are kept.
Identifying a literal upper sector with these data remains a separate
obligation; this module does not assume its desired mean estimate. -/

set_option autoImplicit false
set_option maxHeartbeats 9000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace LongPairEdgeGlobalMeanWork
open ShortSingletonMasks ShortSingletonComplex FourPrimePartition
open LongerTupleCollection LongerTupleMaskedCollection LongerTupleDyadic

variable {α : Type*}

/-- The finite representation length is fixed before choosing the saving
and threshold. All actual finite data,
relations, masks, and unit weights are then uniform. -/
theorem eventually_bound (k : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℝ in atTop, Real.exp 1 ≤ X ∧
      ∀ (S : Finset α) (index : α → ℕ) (encode : α → Fin k → ℕ)
        (B : Finset ℕ) (relation : ℕ → ℕ → Prop) (Q : ℕ)
        (w : α → ℂ) (lo hi : α → ℕ) (cut : ℕ → ℕ),
        let Y : ℝ := X^(101/1000:ℝ)/2
        (∀ a ∈ S, index a = ∏ i, encode a i) →
        Set.InjOn encode (S : Set α) →
        (∀ m ∈ support S index, 2 ≤ m ∧ (m:ℝ) ≤ X) →
        (∀ q ∈ B, 2 ≤ q ∧ (q:ℝ) ≤ X) →
        (∀ q ∈ B, q ≤ Q) → (Q:ℝ) ≤ X →
        (∀ a ∈ S, ‖w a‖ ≤ 1) →
        (∀ m ∈ support S index, ∀ q ∈ B, relation m q →
          X^(545/1000:ℝ) ≤ (m:ℝ)*(q:ℝ) ∧ X^(8/35:ℝ) ≤ (q:ℝ) ∧
          (q:ℝ) ≤ X^(229/1000:ℝ) ∧ (m:ℝ)*(q:ℝ) ≤ X^(772/1000:ℝ)) →
        (∀ a ∈ S, ∀ q ∈ B, ¬relation (index a) q →
          (prefixIndicator (hi a) q-prefixIndicator (lo a) q) *
            (1-prefixIndicator (cut (index a)) q) = 0) →
        (1/X)*(∫ x in Icc X (2*X),
          (maskedSum S index B w lo hi cut (x-x*(Y/X)) x).re^2) ≤ Y^2*X^(-c) := by
  obtain ⟨c,hc,hweighted⟩ := LongPairEdgeWeightedModesWork.eventually_bound_varying.{0}
  refine ⟨c/2,by positivity,?_⟩
  filter_upwards [hweighted,
    eventual_modeCoefficient_cap (α := α) k (c/16) (by positivity),
    ShortSingletonCosts.eventually_total_mass_cap 1 (c/16) (by norm_num) (by positivity),
    ShortSingletonCosts.eventually_absorb_square_cost c hc,
    LongPairEdgeDyadicWork.eventually_data]
    with X hmean hcoeff hmass habsorb hdyadic
  refine ⟨hmean.1,?_⟩
  intro S index encode B relation Q w lo hi cut
  dsimp only
  intro hprod hinj hS hB hBQ hQ hw hrelation hzero
  let A : Finset ℕ := support S index
  let F : Finset (ℕ×ℕ) := jointFamily X A B relation
  let I : Finset ((ℕ×ℕ)×Mode Q) := F ×ˢ (Finset.univ : Finset (Mode Q))
  let M : (ℕ×ℕ)×Mode Q → ℕ := fun i => scale 1 i.1.1
  let N : (ℕ×ℕ)×Mode Q → ℕ := fun i => scale 1 i.1.2
  let sm : (ℕ×ℕ)×Mode Q → Finset ℕ := fun i => block A 1 i.1.1
  let sn : (ℕ×ℕ)×Mode Q → Finset ℕ := fun i => block B 1 i.1.2
  let coeff : (ℕ×ℕ)×Mode Q → ℂ := fun i => scalar Q i.2
  let a : (ℕ×ℕ)×Mode Q → ℕ → ℂ := fun i =>
    modeCoefficient S index Q i.2 w lo hi cut
  let b : (ℕ×ℕ)×Mode Q → ℕ → ℂ := fun i => rightPhase Q i.2
  let T : ℝ := X^(c/16)
  let Y : ℝ := X^(101/1000:ℝ)/2
  have hX : 1 ≤ X := hdyadic.1
  have hXp : 0 < X := by linarith
  have hT : 0 < T := by positivity
  have hindex : ∀ i ∈ I, i.1 ∈ F := fun i hiI => (Finset.mem_product.mp hiI).1
  have hrect : ∀ i ∈ I,
      1 ≤ M i ∧ 1 ≤ N i ∧
      X^(1/2:ℝ) ≤ ((M i*N i:ℕ):ℝ) ∧
      ((M i*N i:ℕ):ℝ) ≤ X^(772/1000:ℝ) ∧
      X^(1/5:ℝ) ≤ (N i:ℝ) ∧ (N i:ℝ) ≤ X^(229/1000:ℝ) ∧
      (∀ n ∈ sm i, M i < n ∧ n ≤ 2*M i) ∧
      (∀ n ∈ sn i, N i < n ∧ n ≤ 2*N i) := by
    intro i hiI
    exact (hdyadic.2 A B relation hrelation) i.1 (hindex i hiI)
  have ha : ∀ i ∈ I, ∀ n ∈ sm i, ‖a i n‖ ≤ T := by
    intro i _ n hn
    have hnA : n ∈ A := block_subset A 1 i.1.1 hn
    have hnpos : 0 < n := by have hh := (hS n hnA).1; omega
    have hnX : (n:ℝ) ≤ X^2 := (hS n hnA).2.trans (by nlinarith)
    exact hcoeff.2 S index encode hprod hinj Q i.2 w lo hi cut n hnpos hnX hw
  have hb : ∀ i ∈ I, ∀ n ∈ sn i, ‖b i n‖ ≤ 1 := by
    intro i _ n _
    exact (rightPhase_norm Q i.2 n).le
  have hcall := hmean.2 ((ℕ×ℕ)×Mode Q) I M N sm sn coeff a b T hT
    (fun i hiI => (hrect i hiI).1)
    (fun i hiI => (hrect i hiI).2.1)
    (fun i hiI => (hrect i hiI).2.2.1)
    (fun i hiI => (hrect i hiI).2.2.2.1)
    (fun i hiI => (hrect i hiI).2.2.2.2.1)
    (fun i hiI => (hrect i hiI).2.2.2.2.2.1)
    (fun i hiI => (hrect i hiI).2.2.2.2.2.2.1)
    (fun i hiI => (hrect i hiI).2.2.2.2.2.2.2) ha hb
  have hmass_eq : (∑ i ∈ I, ‖coeff i‖) =
      (F.card:ℝ)*(∑ t : Mode Q, ‖scalar Q t‖) := by
    simp only [I,coeff,Finset.sum_product,Finset.sum_const,nsmul_eq_mul]
  have hmass_cap : (∑ i ∈ I, ‖coeff i‖) ≤ X^(c/16) := by
    rw [hmass_eq]
    have hcard : (F.card:ℝ) ≤
        ((family A B 1 1 (FourPrimeGlobalPartition.k X)
          (FourPrimeGlobalPartition.k X)).card:ℝ) := by
      exact_mod_cast Finset.card_le_card (jointFamily_subset X A B relation)
    calc
      _ ≤ ((family A B 1 1 (FourPrimeGlobalPartition.k X)
          (FourPrimeGlobalPartition.k X)).card:ℝ)*(∑ t : Mode Q, ‖scalar Q t‖) :=
        mul_le_mul_of_nonneg_right hcard (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
      _ ≤ _ := by simpa only [one_mul] using hmass.2 A B Q hQ
  have hpoint (L R : ℝ) : maskedSum S index B w lo hi cut L R =
      ∑ i ∈ I, coeff i*productSum (sm i) (sn i) (a i) (b i) L R := by
    simpa only [I,coeff,sm,sn,a,b,Finset.sum_product] using
      LongerTupleJointExpansion.maskedSum_eq_joint_modes X S index B relation Q
        w lo hi cut L R hX hS hB hBQ hzero
  have heq :
      (fun x : ℝ => (maskedSum S index B w lo hi cut (x-x*(Y/X)) x).re^2) =
      (fun x => (∑ i ∈ I, coeff i*productSum (sm i) (sn i) (a i) (b i)
        (x-x*(Y/X)) x).re^2) := by
    funext x
    exact congrArg (fun z : ℂ => z.re^2) (hpoint _ _)
  have habs := habsorb.2 T (∑ i ∈ I, ‖coeff i‖) Y hT.le le_rfl
    (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) hmass_cap
  calc
    _ = (1/X)*(∫ x in Icc X (2*X),
        (∑ i ∈ I, coeff i*productSum (sm i) (sn i) (a i) (b i)
          (x-x*(Y/X)) x).re^2) :=
      congrArg (fun f : ℝ → ℝ => (1/X)*(∫ x in Icc X (2*X), f x)) heq
    _ ≤ 4*T^2*(∑ i ∈ I, ‖coeff i‖)^2*Y^2*X^(-c) := hcall
    _ ≤ Y^2*X^(-(c/2)) := habs

#print axioms eventually_bound
run_cmd do
  for ax in (←Lean.collectAxioms ``eventually_bound) do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"
  Lean.logInfo "JOINTLY ACTIVE MASKED HARMAN EDGE POWER-SAVING MEAN SQUARE PASSED"

end LongPairEdgeGlobalMeanWork
