import OuterCompletedEnergyWork
import OuterDivisorModeWork

/-! Exact factorization of the literal active-block polynomial. The prime
coefficient is the original signed divisor atom, and the two tuple variables
retain their full correlated mask. No analytic premise is used. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace OuterLiteralFactorizationWork
open OuterBlockMainTermWork OuterRectangularBlocksWork OuterActiveDyadicWork
open OuterSourceReindexWork OuterBoundaryExtensionWork OuterSmoothErrorSupportWork
open OuterSmoothCoreWork OuterBufferedSourceWork OuterDivisorModeWork OuterSeparatedLogMaskWork
open OuterNormalizedModeWork OuterModeUnitCapWork OuterDivisorIntervalWork
open LongerTupleEncoding PositiveSharpBoxedCount

def primeSet (X : ℝ) (k : BlockKey) : Finset ℕ := (largePrimes X).filter (fun p => p.log2=k.1)
def divisorSet (X : ℝ) (k : BlockKey) : Finset ℕ :=
  (Finset.Ioc 0 ⌊X^(1/1000:ℝ)⌋₊).filter (fun d => d.log2=k.2.1)
def firstSet (X : ℝ) (k : BlockKey) : Finset ℕ :=
  (Finset.Ioc 0 ⌊X^(31/125:ℝ)⌋₊).filter (fun a => a.log2=k.2.2.1)
def secondSet (X : ℝ) (k : BlockKey) : Finset ℕ :=
  (Finset.Ioc 0 ⌊X^(31/125:ℝ)⌋₊).filter (fun b => b.log2=k.2.2.2)
def pairWeight (X s : ℝ) (i j a b : ℕ) : ℂ :=
  if tupleMask X s a b i j then 1 else 0

def factors (X : ℝ) (k : BlockKey) : Finset (ℕ×ℕ×ℕ×ℕ) :=
  divisorSet X k ×ˢ (primeSet X k ×ˢ (firstSet X k ×ˢ secondSet X k))
def encode (z : ℕ×ℕ×ℕ×ℕ) : Representation := (z.2.1,z.1,[z.2.2.1,z.2.2.2])

theorem encode_injective : Function.Injective encode := by
  rintro ⟨d,p,a,b⟩ ⟨e,q,c,f⟩ he
  simpa [encode,and_assoc,and_left_comm,and_comm] using he

theorem block_eq_image (X : ℝ) (k : BlockKey) (hX : 2≤X) :
    blockSource X k=(factors X k).image encode := by
  ext r
  constructor
  · intro hr
    have hd := ambient_data X hX r (Finset.mem_filter.mp hr).1
    have he := rebuild_drop r hd.1
    have hm := (block_rectangular X k r.1 (drop r).1 (drop r).2.1 (drop r).2.2).mp (he ▸ hr)
    apply Finset.mem_image.mpr
    refine ⟨((drop r).1,r.1,(drop r).2.1,(drop r).2.2),?_,he⟩
    simp only [factors,primeSet,divisorSet,firstSet,secondSet,Finset.mem_product,Finset.mem_filter]
    tauto
  · intro hr
    obtain ⟨⟨d,p,a,b⟩,hz,rfl⟩ := Finset.mem_image.mp hr
    apply (block_rectangular X k p d a b).mpr
    simp only [factors,primeSet,divisorSet,firstSet,secondSet,Finset.mem_product,Finset.mem_filter] at hz
    tauto

theorem primeSet_pos (X : ℝ) (k : BlockKey) (p : ℕ) (hp : p∈primeSet X k) : 0<p :=
  (PositiveSharpSieveDecomposition.large_band_bounds X p (Finset.mem_filter.mp hp).1).1.pos

theorem mode_eq_source_sum (X s σ t : ℝ) (i j : ℕ) (k : BlockKey) (ω : Fin 9→ℝ) (hX : 2≤X) :
    modePolynomial X s i j k ω σ t=
      ∑d∈divisorSet X k, sourcePolynomial X s i j d ω (primeSet X k)
        (firstSet X k) (secondSet X k) {1} (pairWeight X s i j) σ t := by
  rw [modePolynomial,block_eq_image X k hX,Finset.sum_image (fun _ _ _ _ he => encode_injective he)]
  simp only [factors,Finset.sum_product,sourcePolynomial,Finset.sum_singleton]
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  change modeWeight X s i j ω (rebuild (d,a,b) p)*(index (rebuild (d,a,b) p):ℂ)^(-MellinWindowFactor.line σ t)=_
  simp only [modeWeight,atomMultiplier,
    drop_rebuild,index,List.prod_cons,List.prod_nil,Nat.mul_one,Complex.ofReal_mul]
  dsimp only [rebuild]
  simp only [List.prod_cons,List.prod_nil,mul_one,←Nat.mul_assoc]
  unfold pairWeight
  split_ifs <;> simp

theorem mode_factorization (X s σ t : ℝ) (i j : ℕ) (k : BlockKey) (ω : Fin 9→ℝ) (hX : 2≤X) :
    modePolynomial X s i j k ω σ t=
      divisorFactor X s i j ω (divisorSet X k) (primeSet X k) (firstSet X k) (secondSet X k)
        (fun _ => pairWeight X s i j) σ t := by
  rw [mode_eq_source_sum X s σ t i j k ω hX]
  have hh := source_sum_factorization X s i j ω (divisorSet X k) (primeSet X k)
    (firstSet X k) (secondSet X k) {1} (fun _ => pairWeight X s i j) σ t
    (fun d hd => (Finset.mem_Ioc.mp (Finset.mem_filter.mp hd).1).1)
    (primeSet_pos X k)
    (fun a ha => (Finset.mem_Ioc.mp (Finset.mem_filter.mp ha).1).1)
    (fun b hb => (Finset.mem_Ioc.mp (Finset.mem_filter.mp hb).1).1)
    (by intro n hn; obtain rfl := Finset.mem_singleton.mp hn; norm_num)
  simpa only [Erdos374.HarmanGram152.verticalDirichlet152,Finset.sum_singleton,
    Nat.cast_one,Complex.one_cpow,mul_one] using hh

theorem centered_factorization (X s σ t : ℝ) (i j : ℕ) (k : BlockKey) (ω : Fin 9→ℝ) (hX : 2≤X) :
    OuterCompletedEnergyWork.centeredPolynomial X s σ i j k ω t=
      divisorFactor X s i j ω (divisorSet X k) (primeSet X k) (firstSet X k) (secondSet X k)
        (fun _ => pairWeight X s i j) σ t *
          OuterCenteredFlatWork.centeredFlat (OuterBlockCofactorWork.lower X k) (OuterBlockCofactorWork.upper X k) σ t := by
  rw [OuterCompletedEnergyWork.centeredPolynomial,mode_factorization X s σ t i j k ω hX]

theorem pairWeight_norm (X s : ℝ) (i j a b : ℕ) : ‖pairWeight X s i j a b‖≤1 := by
  unfold pairWeight
  split_ifs <;> simp

run_cmd do
  for decl in [``encode_injective, ``block_eq_image, ``primeSet_pos, ``mode_eq_source_sum,
      ``mode_factorization, ``centered_factorization, ``pairWeight_norm] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end OuterLiteralFactorizationWork
