import SingletonActualResidual

/-! The actual remaining inner-two sector, before any analytic estimate.
Its tuple union preserves every ordered representation. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace PairActualGeometry
open SieveBoxGrouping

def sector (X s : ℝ) : Finset TailSieveCovered.Index :=
  (SingletonActualResidual.family X s).filter (fun a => a.1=true ∧ a.2.1.length=1)

def tuples (X s z : ℝ) : Finset (List ℕ) :=
  (sector X s).biUnion (fun a =>
    fibre (SieveWeightedCutoffs.level X s) s z (a.2.1++[a.2.2]))

theorem sector_subset (X s : ℝ) : sector X s ⊆ SingletonActualResidual.family X s :=
  Finset.filter_subset _ _

theorem sector_profile (X s : ℝ) (a : TailSieveCovered.Index) (ha : a∈sector X s) :
    a.2.1++[a.2.2]∈profiles true (SieveWeightedCutoffs.level X s) s := by
  obtain ⟨ha,hb,_⟩ := Finset.mem_filter.mp ha
  have he := (Finset.mem_sdiff.mp ha).1
  have hall := (Finset.mem_sdiff.mp he).1
  simpa only [hb] using (FrontierSieveEnumeration.mem_allFamily_iff X s a).mp hall

theorem tuple_length (X s z : ℝ) (t : List ℕ) (ht : t∈tuples X s z) : t.length=2 := by
  obtain ⟨a,ha,ht⟩ := Finset.mem_biUnion.mp ht
  have hlen := ((mem_fibre _ _ _ _ _).mp ht).length_eq
  have ha1 := (Finset.mem_filter.mp ha).2.2
  simpa only [List.length_append,List.length_singleton,ha1] using hlen

theorem tuple_bands (X s z : ℝ) (t : List ℕ) (ht : t∈tuples X s z)
    (p : ℕ) (hp : p∈t) : ∃j,p∈primeBand (SieveWeightedCutoffs.level X s) s z j := by
  obtain ⟨a,_,ht⟩ := Finset.mem_biUnion.mp ht
  have hf := (mem_fibre _ _ _ _ _).mp ht
  have h : List.Forall₂ (fun (p j:ℕ) => (∃i,p∈primeBand (SieveWeightedCutoffs.level X s) s z i) ∧ True)
      t (a.2.1++[a.2.2]) := List.Forall₂.imp (fun p j h => ⟨⟨j,h⟩,trivial⟩) hf
  exact ((List.forall₂_and_left _ _).mp h).1 p hp

theorem tuple_positive (X s z : ℝ) (t : List ℕ) (ht : t∈tuples X s z) : 0<t.prod := by
  apply List.prod_pos
  intro p hp
  obtain ⟨j,hj⟩ := tuple_bands X s z t ht p hp
  exact ((mem_primeBand _ _ _ _ _).mp hj).1.pos

theorem fibres_disjoint (X s z : ℝ) (hX : 1<X) (hs : 0<s) (hs1 : s≤1/1000)
    (hz : z≤SieveWeightedCutoffs.level X s)
    (a : TailSieveCovered.Index) (ha : a∈sector X s)
    (b : TailSieveCovered.Index) (hb : b∈sector X s) (hab : a≠b) :
    Disjoint (fibre (SieveWeightedCutoffs.level X s) s z (a.2.1++[a.2.2]))
      (fibre (SieveWeightedCutoffs.level X s) s z (b.2.1++[b.2.2])) := by
  have hD : 1<SieveWeightedCutoffs.level X s := Real.one_lt_rpow hX (by linarith)
  apply Finset.disjoint_left.mpr
  intro t hta htb
  have hea := ((mem_fibre_iff_indices _ s z hD hs hz _ t).mp hta).2
  have heb := ((mem_fibre_iff_indices _ s z hD hs hz _ t).mp htb).2
  apply hab
  exact Prod.ext ((Finset.mem_filter.mp ha).2.1.trans (Finset.mem_filter.mp hb).2.1.symm)
    (TailSieveCovered.snoc_injective (hea.symm.trans heb))

theorem tuples_sum (X s z : ℝ) (hX : 1<X) (hs : 0<s) (hs1 : s≤1/1000)
    (hz : z≤SieveWeightedCutoffs.level X s) (f : List ℕ→ℝ) :
    (∑t∈tuples X s z,f t)=∑a∈sector X s,
      ∑t∈fibre (SieveWeightedCutoffs.level X s) s z (a.2.1++[a.2.2]),f t := by
  exact Finset.sum_biUnion (fibres_disjoint X s z hX hs hs1 hz)

theorem exponent_lt (s : ℝ) (hs : 0≤s) (hs1 : s≤1/1000) :
    FourPrimeScaleBudget.lowerExponent s+2*SieveWeightedScalarBudget.alpha s<(62/125:ℝ) := by
  have hsq : s^2≤(1/1000000:ℝ) := by nlinarith
  have hlow : FourPrimeScaleBudget.lowerExponent s≤s^2 := by
    unfold FourPrimeScaleBudget.lowerExponent
    nlinarith [sq_nonneg s,mul_nonneg hs (sq_nonneg s)]
  unfold SieveWeightedScalarBudget.alpha
  linarith

theorem product_lt (X s z : ℝ) (hX : 1<X) (hs : 0<s) (hs1 : s≤1/1000)
    (hz : z≤X^(SieveWeightedScalarBudget.alpha s)) (d : ℕ)
    (hd : d∈FrontierSmallBracketSplit.lowSupport X s)
    (t : List ℕ) (ht : t∈tuples X s z) : (d*t.prod:ℕ)<X^(62/125:ℝ) := by
  obtain ⟨p,q,rfl⟩ := List.length_eq_two.mp (tuple_length X s z t ht)
  obtain ⟨j,hj⟩ := tuple_bands X s z [p,q] ht p (by simp)
  obtain ⟨k,hk⟩ := tuple_bands X s z [p,q] ht q (by simp)
  have hXp : 0<X := by linarith
  have hp := (mem_primeBand _ _ _ _ _).mp hj
  have hq := (mem_primeBand _ _ _ _ _).mp hk
  have hp0 : 0<(p:ℝ) := by exact_mod_cast hp.1.pos
  have hq0 : 0<(q:ℝ) := by exact_mod_cast hq.1.pos
  have hdp := mul_lt_mul ((FrontierSmallBracketSplit.mem_lowSupport X s d).mp hd).2
    (hp.2.1.trans_le hz).le hp0 (Real.rpow_pos_of_pos hXp _).le
  have hdpq := mul_lt_mul hdp (hq.2.1.trans_le hz).le hq0
    (mul_nonneg (Real.rpow_pos_of_pos hXp _).le (Real.rpow_pos_of_pos hXp _).le)
  simp only [List.prod_cons,List.prod_nil,mul_one,Nat.cast_mul] at ⊢
  calc
    (d:ℝ)*(p*q) < X^FourPrimeScaleBudget.lowerExponent s *
        X^(SieveWeightedScalarBudget.alpha s)*X^(SieveWeightedScalarBudget.alpha s) := by
      simpa only [mul_assoc] using hdpq
    _ = X^(FourPrimeScaleBudget.lowerExponent s+2*SieveWeightedScalarBudget.alpha s) := by
      rw [←Real.rpow_add hXp,←Real.rpow_add hXp]
      congr 1
      ring
    _ < _ := Real.rpow_lt_rpow_of_exponent_lt hX (exponent_lt s hs.le hs1)

run_cmd do
  for decl in [``sector_subset,``sector_profile,``tuple_length,``tuple_bands,``tuple_positive,
      ``fibres_disjoint,``tuples_sum,``exponent_lt,``product_lt] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ACTUAL INNER-PAIR GEOMETRY AND DISJOINT TUPLE UNION PASSED"

end PairActualGeometry
