import TripleActualGrouping

/-! Actual outer-triple geometry at the first cutoff. The final band's upper
endpoint is converted to a valid lower bound for every prime coordinate. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace TripleActualGeometry
open SieveBoxGrouping SieveGeometricGrid TripleActualGrouping

theorem family_profile (X s : ℝ) (hX : 1<X) (hs : 0<s) (hs1 : s≤1/1000)
    (a : TailSieveCovered.Index) (ha : a∈PairActualResidual.family X s) :
    a.2.1++[a.2.2]∈profiles false (SieveWeightedCutoffs.level X s) s := by
  have hb := (PairActualResidual.remaining_cases X s hX hs hs1 a ha).1
  have h1 := (Finset.mem_sdiff.mp ha).1
  have h2 := (Finset.mem_sdiff.mp h1).1
  have h3 := (Finset.mem_sdiff.mp h2).1
  simpa only [hb] using (FrontierSieveEnumeration.mem_allFamily_iff X s a).mp h3

theorem index_ge_last (X s : ℝ) (hX : 1<X) (hs : 0<s) (hs1 : s≤1/1000)
    (a : TailSieveCovered.Index) (ha : a∈PairActualResidual.family X s)
    (i : ℕ) (hi : i ∈ a.2.1 ++ [a.2.2]) : a.2.2 ≤ i := by
  have hp := ((mem_profiles false _ s _).mp (family_profile X s hX hs hs1 a ha)).2.2
  have hw : (a.2.1++[a.2.2]).Pairwise (fun i j : ℕ => i ≥ j) := hp.2.1
  rcases List.mem_append.mp hi with hi | hi
  · exact (List.pairwise_append.mp hw).2.2 i hi a.2.2 (by simp)
  · exact (List.mem_singleton.mp hi).symm.le

theorem ratio_le (s : ℝ) (hs : 0≤s) (hs1 : s≤1/1000) : ratio s≤1001/1000 := by
  have hp := pow_le_pow_left₀ hs hs1 9
  norm_num at hp
  unfold ratio
  linarith

theorem final_scale_lower (X s : ℝ) (hX : 1<X) (hs : 0<s) (hs1 : s≤1/1000)
    (a : TailSieveCovered.Index) (ha : a∈PairActualResidual.family X s) :
    X^(57/250:ℝ)<scale (SieveWeightedCutoffs.level X s) s a.2.2 := by
  have hD : 1<SieveWeightedCutoffs.level X s := Real.one_lt_rpow hX (by linarith)
  have hu := (PairActualResidual.remaining_cases X s hX hs hs1 a ha).2.2
  by_contra hn
  have hl := le_of_not_gt hn
  have he : (57/250:ℝ)*ratio s≤8/35 := by
    have hr := ratio_le s hs.le hs1
    linarith
  have hpow := Real.rpow_le_rpow (Real.rpow_nonneg (by linarith : 0≤SieveWeightedCutoffs.level X s) _)
    hl (le_trans zero_le_one (one_lt_ratio s hs).le)
  change (scale (SieveWeightedCutoffs.level X s) s a.2.2)^ratio s ≤
    (X^(57/250:ℝ))^ratio s at hpow
  rw [←scale_succ _ _ (by linarith) _,←Real.rpow_mul (by linarith : 0≤X)] at hpow
  exact (not_lt_of_ge (hpow.trans
    (Real.rpow_le_rpow_of_exponent_le hX.le he))) hu

theorem prime_lower (X s z : ℝ) (hX : 1<X) (hs : 0<s) (hs1 : s≤1/1000)
    (a : TailSieveCovered.Index) (ha : a∈PairActualResidual.family X s)
    (i p : ℕ) (hi : i∈a.2.1++[a.2.2])
    (hp : p∈primeBand (SieveWeightedCutoffs.level X s) s z i) :
    X^(57/250:ℝ)<(p:ℝ) := by
  have hD : 1<SieveWeightedCutoffs.level X s := Real.one_lt_rpow hX (by linarith)
  exact (final_scale_lower X s hX hs hs1 a ha).trans_le
    (((scale_strictMono _ s hD hs).monotone (index_ge_last X s hX hs hs1 a ha i hi)).trans
      ((mem_primeBand _ _ _ _ _).mp hp).2.2.1)

theorem fibre_coordinate (D s z : ℝ) (g t : List ℕ)
    (ht : t∈fibre D s z g) (p : ℕ) (hp : p∈t) :
    ∃i∈g,p∈primeBand D s z i := by
  have hf := (mem_fibre D s z g t).mp ht
  induction hf with
  | nil => simp at hp
  | @cons q i ts is hq htail ih =>
    rcases List.mem_cons.mp hp with hp | hp
    · subst p
      exact ⟨i,by simp,hq⟩
    · obtain ⟨j,hj,hpj⟩ := ih ((mem_fibre _ _ _ _ _).mpr htail) hp
      exact ⟨j,by simp [hj],hpj⟩

theorem tuple_prime_lower (X s z : ℝ) (hX : 1<X) (hs : 0<s) (hs1 : s≤1/1000)
    (a : TailSieveCovered.Index) (ha : a∈PairActualResidual.family X s)
    (t : List ℕ) (ht : t∈fibre (SieveWeightedCutoffs.level X s) s z (a.2.1++[a.2.2]))
    (p : ℕ) (hp : p∈t) : X^(57/250:ℝ)<(p:ℝ) := by
  obtain ⟨i,hi,hpi⟩ := fibre_coordinate _ s z _ t ht p hp
  exact prime_lower X s z hX hs hs1 a ha i p hi hpi

theorem exponent_le (s : ℝ) (hs : 0≤s) (hs1 : s≤1/1000) :
    FourPrimeScaleBudget.lowerExponent s+3*SieveWeightedScalarBudget.alpha s≤(26/35:ℝ) := by
  have hsq : s^2≤s := by nlinarith
  have hcub : 0≤s*s^2 := mul_nonneg hs (sq_nonneg s)
  unfold FourPrimeScaleBudget.lowerExponent SieveWeightedScalarBudget.alpha
  nlinarith

theorem product_lt (X s z : ℝ) (hX : 1<X) (hs : 0<s) (hs1 : s≤1/1000)
    (hz : z≤X^(SieveWeightedScalarBudget.alpha s))
    (a : TailSieveCovered.Index) (ha : a∈PairActualResidual.family X s)
    (d : ℕ) (hd : d∈FrontierSmallBracketSplit.lowSupport X s)
    (t : List ℕ) (ht : t∈fibre (SieveWeightedCutoffs.level X s) s z (a.2.1++[a.2.2])) :
    (d*t.prod:ℕ)<X^(26/35:ℝ) := by
  have hlen : t.length=3 := by
    have hh := ((mem_fibre _ _ _ _ _).mp ht).length_eq
    simpa only [List.length_append,List.length_singleton,
      (PairActualResidual.remaining_cases X s hX hs hs1 a ha).2.1] using hh
  obtain ⟨p,q,r,rfl⟩ := List.length_eq_three.mp hlen
  obtain ⟨i,_,hi⟩ := fibre_coordinate _ s z _ [p,q,r] ht p (by simp)
  obtain ⟨j,_,hj⟩ := fibre_coordinate _ s z _ [p,q,r] ht q (by simp)
  obtain ⟨k,_,hk⟩ := fibre_coordinate _ s z _ [p,q,r] ht r (by simp)
  have hp := (mem_primeBand _ _ _ _ _).mp hi
  have hq := (mem_primeBand _ _ _ _ _).mp hj
  have hr := (mem_primeBand _ _ _ _ _).mp hk
  have hp0 : 0<(p:ℝ) := by exact_mod_cast hp.1.pos
  have hq0 : 0<(q:ℝ) := by exact_mod_cast hq.1.pos
  have hr0 : 0<(r:ℝ) := by exact_mod_cast hr.1.pos
  have hXp : 0<X := by linarith
  have hdp := mul_lt_mul ((FrontierSmallBracketSplit.mem_lowSupport X s d).mp hd).2
    (hp.2.1.trans_le hz).le hp0 (Real.rpow_pos_of_pos hXp _).le
  have hdpq := mul_lt_mul hdp (hq.2.1.trans_le hz).le hq0
    (mul_nonneg (Real.rpow_pos_of_pos hXp _).le (Real.rpow_pos_of_pos hXp _).le)
  have hdpqr := mul_lt_mul hdpq (hr.2.1.trans_le hz).le hr0
    (mul_nonneg (mul_nonneg (Real.rpow_pos_of_pos hXp _).le
      (Real.rpow_pos_of_pos hXp _).le) (Real.rpow_pos_of_pos hXp _).le)
  simp only [List.prod_cons,List.prod_nil,mul_one,Nat.cast_mul] at ⊢
  calc
    _ < X^FourPrimeScaleBudget.lowerExponent s * X^(SieveWeightedScalarBudget.alpha s) *
      X^(SieveWeightedScalarBudget.alpha s) * X^(SieveWeightedScalarBudget.alpha s) := by
      simpa only [mul_assoc] using hdpqr
    _ = X^(FourPrimeScaleBudget.lowerExponent s+3*SieveWeightedScalarBudget.alpha s) := by
      rw [←Real.rpow_add hXp,←Real.rpow_add hXp,←Real.rpow_add hXp]
      congr 1
      ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hX.le (exponent_le s hs.le hs1)

run_cmd do
  for decl in [``family_profile,``index_ge_last,``ratio_le,``final_scale_lower,``prime_lower,
      ``fibre_coordinate,``tuple_prime_lower,``exponent_le,``product_lt] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ACTUAL OUTER-TRIPLE PRIME LOWER AND PHYSICAL PRODUCT UPPER BOUNDS"

end TripleActualGeometry
