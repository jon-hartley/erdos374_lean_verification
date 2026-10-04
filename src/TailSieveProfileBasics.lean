import MomentRemainderProfileSplit
import MomentRemainderSupport

/-! Exact separation of the final prime from an arbitrary actual lower-sieve
box profile. The full small bracket and every prefix representation remain
in the left coefficient, including the small divisor 1. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace TailSieveProfileBasics
open SieveBoxGrouping SieveTupleConvolution SieveUpperBoxWindow

def leftSupport (D s z : ℝ) (g : List ℕ) : Finset ℕ :=
  MomentRemainderProfileSplit.leftSupport (smallCarrier D s) D s z g

def leftCoefficient (D s z : ℝ) (upper : Bool) (g : List ℕ) : ℕ→ℝ :=
  MomentRemainderProfileSplit.leftCoefficient (smallCarrier D s)
    (SieveSmallWeights.weight (D^s) (D^(s^2)) upper) D s z g

def support (D s z : ℝ) (g : List ℕ) (j : ℕ) : Finset ℕ :=
  FactoredDivisorWeights.support (leftSupport D s z g) (primeBand D s z j)

def coefficient (D s z : ℝ) (upper : Bool) (g : List ℕ) (j : ℕ) : ℕ→ℝ :=
  FactoredDivisorWeights.coefficient (leftSupport D s z g) (primeBand D s z j)
    (leftCoefficient D s z upper g) (fun _ => 1)

def remainder (D s z : ℝ) (upper : Bool) (g : List ℕ) (j : ℕ) (L R : ℝ) : ℝ :=
  HarmanDivisorWindow.remainder (support D s z g j) (coefficient D s z upper g j) L R

theorem fibre_singleton_sum (D s z : ℝ) (j : ℕ) (f : List ℕ→ℝ) :
    (∑t∈fibre D s z [j],f t)=∑p∈primeBand D s z j,f [p] := by
  simp only [fibre,Finset.image_singleton]
  rw [Finset.sum_biUnion]
  · simp
  · intro p _ q _ hpq
    exact Finset.disjoint_singleton.mpr (by simpa using hpq)

theorem kernel (D s z : ℝ) (upper : Bool) (g : List ℕ) (j : ℕ) (f : ℕ→ℝ) :
    (∑m∈support D s z g j, coefficient D s z upper g j m*f m)=
      ∑d∈smallCarrier D s,∑t∈fibre D s z (g++[j]),
        SieveSmallWeights.weight (D^s) (D^(s^2)) upper d*f (d*t.prod) := by
  rw [support,coefficient,FactoredDivisorWeights.support,
    FactoredDivisorWeights.grouped_sum _ _ _ _ _ _
      (HarmanDivisorWindow.productSupport_contains _ _),Finset.sum_product]
  simp only [mul_one,DirichletProductCoefficients.productIndex]
  rw [Finset.sum_comm]
  simp_rw [leftSupport,leftCoefficient,MomentRemainderProfileSplit.leftSupport,
    MomentRemainderProfileSplit.leftCoefficient,
    convolution_tuple_kernel _ _ _ _ (Finset.Subset.refl _)]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  rw [Finset.sum_comm,MomentRemainderProfileSplit.fibre_sum_append D s z g [j]
    (fun k => SieveSmallWeights.weight (D^s) (D^(s^2)) upper d*f (d*k))]
  apply Finset.sum_congr rfl
  intro t _
  rw [fibre_singleton_sum]
  simp only [List.prod_cons,List.prod_nil,mul_one,mul_assoc]

theorem remainder_eq_profile (D s z : ℝ) (upper : Bool) (g : List ℕ) (j : ℕ) (L R : ℝ) :
    remainder D s z upper g j L R =
      MomentRemainderProfileSplit.profileRemainder D s z upper
        (fun _ => g.length) (g++[j]) L R := by
  simp only [remainder,MomentRemainderProfileSplit.profileRemainder,
    HarmanDivisorWindow.remainder_eq_sum]
  rw [kernel,MomentRemainderProfileSplit.split_kernel,List.take_append_drop]

theorem left_positive (D s z : ℝ) (g : List ℕ) (hg : g≠[]) (m : ℕ)
    (hm : m∈leftSupport D s z g) : 2≤m := by
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hm
  obtain ⟨hd,ht⟩ := Finset.mem_product.mp ha
  obtain ⟨t,ht,he⟩ := (mem_tupleSupport _ _).mp ht
  have hlen := ((mem_fibre D s z g t).mp ht).length_eq
  have htnil : t≠[] := by
    intro he
    simp only [he,List.length_nil] at hlen
    exact hg (List.length_eq_zero_iff.mp hlen.symm)
  have hp : ∀p∈t,2≤p := by
    have hrel : List.Forall₂ (fun (p i:ℕ) => 2≤p ∧ True) t g :=
      List.Forall₂.imp (fun p i h => ⟨((mem_primeBand D s z i p).mp h).1.two_le,trivial⟩)
        ((mem_fibre D s z g t).mp ht)
    exact ((List.forall₂_and_left t g).mp hrel).1
  have hprod : 2≤t.prod := by
    obtain ⟨p,ps,rfl⟩ := List.exists_cons_of_ne_nil htnil
    have hp2 := hp p (by simp)
    have hps : 0<ps.prod := List.prod_pos (fun q hq => by have := hp q (by simp [hq]); omega)
    simp only [List.prod_cons]
    nlinarith
  have hd0 := SieveVectorConvolution.carrier_positive _ _ _
    (SieveSmallWeights.primes_prime _) a.1 hd
  change 2≤a.1*a.2
  rw [←he]
  nlinarith

theorem product_mem_boxed (positive : Bool) (D s z : ℝ) (hD : 1<D) (hs : 0<s)
    (hz : z≤D) (g : List ℕ) (j : ℕ) (hg : g++[j]∈profiles positive D s)
    (m : ℕ) (hm : m∈leftSupport D s z g) (n : ℕ) (hn : n∈primeBand D s z j) :
    m*n∈SieveBoxedWindow.support D s z := by
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hm
  obtain ⟨hd,ht⟩ := Finset.mem_product.mp ha
  obtain ⟨t,ht,he⟩ := (mem_tupleSupport _ _).mp ht
  have ht' : t++[n]∈fibre D s z (g++[j]) := by
    apply (mem_fibre _ _ _ _ _).mpr
    exact List.rel_append ((mem_fibre D s z g t).mp ht)
      (by simpa using hn)
  rw [fibre_eq_filter positive D s z hD hs hz _ hg] at ht'
  have hfamily := (Finset.mem_filter.mp ht').1
  have hunion : t++[n]∈SieveCompleteBoxing.innerFamily D s z ∪
      SieveCompleteBoxing.outerFamily D s z := by
    cases positive
    · exact Finset.mem_union_right _ hfamily
    · exact Finset.mem_union_left _ hfamily
  refine Finset.mem_image.mpr ⟨(a.1,t.prod*n),Finset.mem_product.mpr ⟨hd,?_⟩,?_⟩
  · exact (mem_tupleSupport _ _).mpr ⟨t++[n],hunion,by simp⟩
  · simp [DirichletProductCoefficients.productIndex,mul_assoc,←he]

theorem eventually_left_coefficient_cap (K : ℕ) (δ : ℝ) (hδ : 0<δ) :
    ∀ᶠ X:ℝ in atTop, 1≤X ∧ ∀(D s z:ℝ)(upper:Bool)(g:List ℕ)(m:ℕ),
      g.length≤K → m≠0 → (m:ℝ)≤X^2 →
      |leftCoefficient D s z upper g m|≤X^δ := by
  filter_upwards [PositiveSharpRemainderAnalysis.eventually_signedCoefficient_cap K δ hδ]
    with X hh
  refine ⟨hh.1,?_⟩
  intro D s z upper g m hg hm hmX
  have hlen : ∀t∈fibre D s z g,t.length≤K := by
    intro t ht
    exact (((mem_fibre D s z g t).mp ht).length_eq).le.trans hg
  have hb := hh.2 (smallCarrier D s)
    (SieveSmallWeights.weight (D^s) (D^(s^2)) upper) (fun _ => 0)
    (fibre D s z g) ∅ m hm hmX hlen (by simp)
    (fun d _ => SieveSmallWeights.weight_abs_le_one _ _ _ d) (by simp)
  simpa only [SieveTupleConvolution.signedCoefficient,SieveTupleConvolution.tupleCarrier,
    Finset.union_empty,SieveTupleConvolution.tupleCoefficient,
    FactoredDivisorWeights.coefficient,Finset.sum_empty,zero_mul,Finset.sum_const_zero,
    sub_zero,leftCoefficient,MomentRemainderProfileSplit.leftCoefficient] using hb

run_cmd do
  for decl in [``fibre_singleton_sum,``kernel,``remainder_eq_profile,``left_positive,
      ``product_mem_boxed,``eventually_left_coefficient_cap] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ARBITRARY-LENGTH ACTUAL FINAL-PRIME SEPARATION PASSED"

end TailSieveProfileBasics
