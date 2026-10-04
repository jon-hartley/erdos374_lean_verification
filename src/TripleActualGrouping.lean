import PairActualResidual
import BoundedDyadicCoefficients

/-! Literal last-prime / low-small-divisor-prefix factorization. The prime
factor is first, as required by the asymmetric eighth/eighth/fourth bound.
All upper small weights and all ordered prefix representations are retained. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace TripleActualGrouping
open SieveBoxGrouping SieveTupleConvolution

def primeSupport (X s z : ℝ) (j : ℕ) : Finset ℕ :=
  primeBand (SieveWeightedCutoffs.level X s) s z j

def pairSupport (X s z : ℝ) (g : List ℕ) : Finset ℕ :=
  MomentRemainderProfileSplit.leftSupport (FrontierSmallBracketSplit.lowSupport X s)
    (SieveWeightedCutoffs.level X s) s z g

def pairCoefficient (X s z : ℝ) (upper : Bool) (g : List ℕ) : ℕ → ℝ :=
  MomentRemainderProfileSplit.leftCoefficient (FrontierSmallBracketSplit.lowSupport X s)
    (FrontierSmallBracket.smallWeight X s upper) (SieveWeightedCutoffs.level X s) s z g

def support (X s z : ℝ) (g : List ℕ) (j : ℕ) : Finset ℕ :=
  FactoredDivisorWeights.support (primeSupport X s z j) (pairSupport X s z g)

def coefficient (X s z : ℝ) (upper : Bool) (g : List ℕ) (j : ℕ) : ℕ → ℝ :=
  FactoredDivisorWeights.coefficient (primeSupport X s z j) (pairSupport X s z g)
    (fun _ => 1) (pairCoefficient X s z upper g)

def remainder (X s z : ℝ) (upper : Bool) (g : List ℕ) (j : ℕ) (L R : ℝ) : ℝ :=
  HarmanDivisorWindow.remainder (support X s z g j) (coefficient X s z upper g j) L R

theorem kernel (X s z : ℝ) (upper : Bool) (g : List ℕ) (j : ℕ) (f : ℕ → ℝ) :
    (∑m∈support X s z g j, coefficient X s z upper g j m * f m) =
      FrontierSmallBracketSplit.lowKernel X s z upper (g++[j]) f := by
  rw [support,coefficient,FactoredDivisorWeights.support,
    FactoredDivisorWeights.grouped_sum _ _ _ _ _ _
      (HarmanDivisorWindow.productSupport_contains _ _),Finset.sum_product]
  simp only [one_mul,DirichletProductCoefficients.productIndex]
  simp_rw [pairSupport,pairCoefficient,MomentRemainderProfileSplit.leftSupport,
    MomentRemainderProfileSplit.leftCoefficient,
    convolution_tuple_kernel _ _ _ _ (Finset.Subset.refl _)]
  rw [Finset.sum_comm]
  unfold FrontierSmallBracketSplit.lowKernel
  apply Finset.sum_congr rfl
  intro d _
  rw [Finset.sum_comm,MomentRemainderProfileSplit.fibre_sum_append
    (SieveWeightedCutoffs.level X s) s z g [j]
    (fun k => FrontierSmallBracket.smallWeight X s upper d * f (d*k))]
  apply Finset.sum_congr rfl
  intro t _
  rw [TailSieveProfileBasics.fibre_singleton_sum]
  apply Finset.sum_congr rfl
  intro p _
  simp only [List.prod_cons,List.prod_nil,mul_one]
  congr 2
  ac_rfl

theorem remainder_eq_low (X s z : ℝ) (upper : Bool) (g : List ℕ) (j : ℕ) (L R : ℝ) :
    remainder X s z upper g j L R =
      FrontierSmallBracketSplit.lowRemainder X s z upper (g++[j]) L R := by
  simp only [remainder,HarmanDivisorWindow.remainder_eq_sum,
    FrontierSmallBracketSplit.lowRemainder]
  exact kernel X s z upper g j _

theorem actual_remainder_eq_sum (X s z L R : ℝ) (hX : 1<X) (hs : 0<s)
    (hs1 : s≤1/1000) :
    PairActualResidual.remainder X s z L R =
      ∑a∈PairActualResidual.family X s, remainder X s z true a.2.1 a.2.2 L R := by
  rw [PairActualResidual.remainder_eq_outer X s z L R hX hs hs1]
  apply Finset.sum_congr rfl
  intro a _
  exact (remainder_eq_low X s z true a.2.1 a.2.2 L R).symm

theorem vertical_product (X s z : ℝ) (upper : Bool) (g : List ℕ) (j : ℕ) (σ t : ℝ) :
    Erdos374.HarmanGram152.verticalDirichlet152 (support X s z g j)
      (fun n => (coefficient X s z upper g j n : ℂ)) σ t =
    Erdos374.HarmanGram152.verticalDirichlet152 (primeSupport X s z j) (fun _ => 1) σ t *
      Erdos374.HarmanGram152.verticalDirichlet152 (pairSupport X s z g)
        (fun n => (pairCoefficient X s z upper g n : ℂ)) σ t := by
  simpa only [support,coefficient,Complex.ofReal_one] using
    FactoredDivisorWeights.vertical_product_support (primeSupport X s z j)
      (pairSupport X s z g) (fun _ => 1) (pairCoefficient X s z upper g) σ t

theorem eventually_pair_coefficient_cap (K : ℕ) (δ : ℝ) (hδ : 0<δ) :
    ∀ᶠ X:ℝ in atTop, 1≤X ∧ ∀(s z:ℝ)(upper:Bool)(g:List ℕ)(m:ℕ),
      g.length≤K → m≠0 → (m:ℝ)≤X^2 →
      |pairCoefficient X s z upper g m|≤X^δ := by
  filter_upwards [PositiveSharpRemainderAnalysis.eventually_signedCoefficient_cap K δ hδ]
    with X hh
  refine ⟨hh.1,?_⟩
  intro s z upper g m hg hm hmX
  have hlen : ∀t∈fibre (SieveWeightedCutoffs.level X s) s z g,t.length≤K := by
    intro t ht
    exact (((mem_fibre _ _ _ _ _).mp ht).length_eq).le.trans hg
  have hb := hh.2 (FrontierSmallBracketSplit.lowSupport X s)
    (FrontierSmallBracket.smallWeight X s upper) (fun _ => 0)
    (fibre (SieveWeightedCutoffs.level X s) s z g) ∅ m hm hmX hlen (by simp)
    (fun d _ => SieveSmallWeights.weight_abs_le_one _ _ _ d) (by simp)
  simpa only [signedCoefficient,tupleCarrier,Finset.union_empty,tupleCoefficient,
    FactoredDivisorWeights.coefficient,Finset.sum_empty,zero_mul,Finset.sum_const_zero,
    sub_zero,pairCoefficient,MomentRemainderProfileSplit.leftCoefficient] using hb

theorem eventually_pair_energy (K : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ X:ℝ in atTop, 2≤X ∧ ∀(s z:ℝ)(upper:Bool)(g:List ℕ)(N:ℕ)(S:Finset ℕ),
      g.length≤K → 1≤N → (N:ℝ)≤X →
      (∀n∈S,N≤n ∧ n≤2*N) →
      (∑n∈S,(pairCoefficient X s z upper g n)^2)≤X^ε*N := by
  filter_upwards [eventually_pair_coefficient_cap K (ε/4) (by positivity),
    PolynomialLogEnvelope.eventually_constant_bound 2 (ε/2) (by norm_num) (by positivity),
    eventually_ge_atTop (2:ℝ)] with X hcap hconst hX
  refine ⟨hX,?_⟩
  intro s z upper g N S hg hN hNX hS
  have hXp : 0<X := by linarith
  have hpoint : ∀n∈S,(pairCoefficient X s z upper g n)^2≤X^(ε/2) := by
    intro n hn
    have hn0 : n≠0 := by have := (hS n hn).1; omega
    have hnX : (n:ℝ)≤X^2 := by
      have hn2 : (n:ℝ)≤2*(N:ℝ) := by exact_mod_cast (hS n hn).2
      nlinarith
    have hh := pow_le_pow_left₀ (abs_nonneg _) (hcap.2 s z upper g n hg hn0 hnX) 2
    rw [sq_abs,←Real.rpow_mul_natCast hXp.le] at hh
    simpa only [Nat.cast_ofNat,show ε/4*(2:ℝ)=ε/2 by ring] using hh
  calc
    _ ≤ ∑n∈S,X^(ε/2) := Finset.sum_le_sum hpoint
    _ = (S.card:ℝ)*X^(ε/2) := by simp
    _ ≤ (2*N)*X^(ε/2) := mul_le_mul_of_nonneg_right
      (BoundedDyadicCoefficients.card_bound S N hN hS) (by positivity)
    _ ≤ (X^(ε/2)*N)*X^(ε/2) := by gcongr; exact hconst.2
    _ = X^ε*N := by
      rw [mul_right_comm,←Real.rpow_add hXp,show ε/2+ε/2=ε by ring]

run_cmd do
  for decl in [``kernel,``remainder_eq_low,``actual_remainder_eq_sum,``vertical_product,
      ``eventually_pair_coefficient_cap,``eventually_pair_energy] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ACTUAL LOW-D PREFIX GROUPING; SIGNS AND MULTIPLICITIES RETAINED"

end TripleActualGrouping
