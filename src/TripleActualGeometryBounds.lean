import TripleActualGeometry

/-! Size bounds for the two literal factor supports of each remaining outer
profile. These are bounds on every support member, including zero-weight ones. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace TripleActualGeometry
open SieveBoxGrouping SieveTupleConvolution TripleActualGrouping

theorem prime_support_bounds (X s z : ℝ) (hX : 1<X) (hs : 0<s) (hs1 : s≤1/1000)
    (hz : z≤X^(SieveWeightedScalarBudget.alpha s))
    (a : TailSieveCovered.Index) (ha : a∈PairActualResidual.family X s)
    (m : ℕ) (hm : m∈primeSupport X s z a.2.2) :
    2≤m ∧ X^(57/250:ℝ)<(m:ℝ) ∧ (m:ℝ)≤X := by
  have hp := (mem_primeBand _ _ _ _ _).mp hm
  refine ⟨hp.1.two_le,prime_lower X s z hX hs hs1 a ha a.2.2 m (by simp) hm,?_⟩
  apply (hp.2.1.trans_le hz).le.trans
  calc
    X^(SieveWeightedScalarBudget.alpha s) ≤ X^(1:ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hX.le (by unfold SieveWeightedScalarBudget.alpha; linarith)
    _ = X := Real.rpow_one X

theorem pair_support_representation (X s z : ℝ) (g : List ℕ) (n : ℕ)
    (hn : n∈pairSupport X s z g) :
    ∃d∈FrontierSmallBracketSplit.lowSupport X s,
      ∃t∈fibre (SieveWeightedCutoffs.level X s) s z g,n=d*t.prod := by
  obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hn
  obtain ⟨hd,ht⟩ := Finset.mem_product.mp hb
  obtain ⟨t,ht,he⟩ := (mem_tupleSupport _ _).mp ht
  exact ⟨b.1,hd,t,ht,by dsimp [DirichletProductCoefficients.productIndex]; rw [←he]⟩

theorem pair_support_lower (X s z : ℝ) (hX : 1<X) (hs : 0<s) (hs1 : s≤1/1000)
    (a : TailSieveCovered.Index) (ha : a∈PairActualResidual.family X s)
    (n : ℕ) (hn : n∈pairSupport X s z a.2.1) : X^(57/125:ℝ)<(n:ℝ) := by
  obtain ⟨d,hd,t,ht,rfl⟩ := pair_support_representation X s z a.2.1 n hn
  have hlen : t.length=2 :=
    ((mem_fibre _ _ _ _ _).mp ht).length_eq.trans
      (PairActualResidual.remaining_cases X s hX hs hs1 a ha).2.1
  obtain ⟨p,q,rfl⟩ := List.length_eq_two.mp hlen
  obtain ⟨i,hi,hpi⟩ := fibre_coordinate _ s z _ [p,q] ht p (by simp)
  obtain ⟨j,hj,hqj⟩ := fibre_coordinate _ s z _ [p,q] ht q (by simp)
  have hp := prime_lower X s z hX hs hs1 a ha i p (by simp [hi]) hpi
  have hq := prime_lower X s z hX hs hs1 a ha j q (by simp [hj]) hqj
  have hd1 : (1:ℝ)≤d := by
    have hh : 1≤d := SingletonActualGeometry.low_positive X s d hd
    exact_mod_cast hh
  have hXp : 0<X := by linarith
  simp only [List.prod_cons,List.prod_nil,mul_one,Nat.cast_mul]
  calc
    X^(57/125:ℝ) = X^(57/250:ℝ)*X^(57/250:ℝ) := by rw [←Real.rpow_add hXp]; norm_num
    _ < (p:ℝ)*q := mul_lt_mul hp hq.le (Real.rpow_pos_of_pos hXp _) (Nat.cast_nonneg p)
    _ ≤ (d:ℝ)*(p*q) := le_mul_of_one_le_left (by positivity) hd1

theorem pair_support_upper (X s z : ℝ) (hX : 1<X) (hs : 0<s) (hs1 : s≤1/1000)
    (hz : z≤X^(SieveWeightedScalarBudget.alpha s))
    (a : TailSieveCovered.Index) (ha : a∈PairActualResidual.family X s)
    (n : ℕ) (hn : n∈pairSupport X s z a.2.1) : (n:ℝ)≤X := by
  obtain ⟨d,hd,t,ht,rfl⟩ := pair_support_representation X s z a.2.1 n hn
  have hlen : t.length=2 :=
    ((mem_fibre _ _ _ _ _).mp ht).length_eq.trans
      (PairActualResidual.remaining_cases X s hX hs hs1 a ha).2.1
  obtain ⟨p,q,rfl⟩ := List.length_eq_two.mp hlen
  obtain ⟨i,_,hpi⟩ := fibre_coordinate _ s z _ [p,q] ht p (by simp)
  obtain ⟨j,_,hqj⟩ := fibre_coordinate _ s z _ [p,q] ht q (by simp)
  have hp := (mem_primeBand _ _ _ _ _).mp hpi
  have hq := (mem_primeBand _ _ _ _ _).mp hqj
  have hp0 : 0<(p:ℝ) := by exact_mod_cast hp.1.pos
  have hq0 : 0<(q:ℝ) := by exact_mod_cast hq.1.pos
  have hXp : 0<X := by linarith
  have hdp := mul_lt_mul ((FrontierSmallBracketSplit.mem_lowSupport X s d).mp hd).2
    (hp.2.1.trans_le hz).le hp0 (Real.rpow_pos_of_pos hXp _).le
  have hdpq := mul_lt_mul hdp (hq.2.1.trans_le hz).le hq0
    (mul_nonneg (Real.rpow_pos_of_pos hXp _).le (Real.rpow_pos_of_pos hXp _).le)
  simp only [List.prod_cons,List.prod_nil,mul_one,Nat.cast_mul]
  calc
    (d:ℝ)*(p*q) ≤ X^FourPrimeScaleBudget.lowerExponent s *
        X^(SieveWeightedScalarBudget.alpha s)*X^(SieveWeightedScalarBudget.alpha s) := by
      simpa only [mul_assoc] using hdpq.le
    _ = X^(FourPrimeScaleBudget.lowerExponent s+2*SieveWeightedScalarBudget.alpha s) := by
      rw [←Real.rpow_add hXp,←Real.rpow_add hXp]
      congr 1
      ring
    _ ≤ X^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le hX.le
      (le_trans (PairActualGeometry.exponent_lt s hs.le hs1).le (by norm_num))
    _ = X := Real.rpow_one X

theorem pair_support_bounds (X s z : ℝ) (hX : 1<X) (hs : 0<s) (hs1 : s≤1/1000)
    (hz : z≤X^(SieveWeightedScalarBudget.alpha s))
    (a : TailSieveCovered.Index) (ha : a∈PairActualResidual.family X s)
    (n : ℕ) (hn : n∈pairSupport X s z a.2.1) :
    2≤n ∧ X^(57/125:ℝ)<(n:ℝ) ∧ (n:ℝ)≤X := by
  have hl := pair_support_lower X s z hX hs hs1 a ha n hn
  have hn1 : 1<n := by
    have hh := (Real.one_lt_rpow hX (by norm_num : (0:ℝ)<57/125)).trans hl
    exact_mod_cast hh
  exact ⟨hn1,hl,pair_support_upper X s z hX hs hs1 hz a ha n hn⟩

theorem cross_product_lt (X s z : ℝ) (hX : 1<X) (hs : 0<s) (hs1 : s≤1/1000)
    (hz : z≤X^(SieveWeightedScalarBudget.alpha s))
    (a : TailSieveCovered.Index) (ha : a∈PairActualResidual.family X s)
    (m : ℕ) (hm : m∈primeSupport X s z a.2.2)
    (n : ℕ) (hn : n∈pairSupport X s z a.2.1) : (m*n:ℕ)<X^(26/35:ℝ) := by
  obtain ⟨d,hd,t,ht,rfl⟩ := pair_support_representation X s z a.2.1 n hn
  have hfull : t++[m]∈fibre (SieveWeightedCutoffs.level X s) s z (a.2.1++[a.2.2]) := by
    apply (mem_fibre _ _ _ _ _).mpr
    exact List.rel_append ((mem_fibre _ _ _ _ _).mp ht) (List.Forall₂.cons hm List.Forall₂.nil)
  have hh := product_lt X s z hX hs hs1 hz a ha d hd (t++[m]) hfull
  simpa only [List.prod_append,List.prod_cons,List.prod_nil,mul_one,mul_left_comm,mul_comm] using hh

run_cmd do
  for decl in [``prime_support_bounds,``pair_support_representation,``pair_support_lower,
      ``pair_support_upper,``pair_support_bounds,``cross_product_lt] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ACTUAL ONE-PRIME AND LOW-D TWO-PRIME SUPPORT SIZE BOUNDS"

end TripleActualGeometry
