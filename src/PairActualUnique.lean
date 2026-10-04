import PairActualGeometry

/-! The actual inner-pair bands are strictly ordered. Together with the low-d
threshold this makes their physical representation unique, including d=1. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace PairActualUnique
open SieveBoxGrouping PairActualGeometry

theorem tuple_order (X s z : ℝ) (hX : 1<X) (hs : 0<s) (hs1 : s≤1/1000)
    (p q : ℕ) (ht : [p,q]∈tuples X s z) : q<p := by
  obtain ⟨a,ha,ht⟩ := Finset.mem_biUnion.mp ht
  obtain ⟨b,g,j⟩ := a
  obtain ⟨i,hg⟩ := List.length_eq_one_iff.mp (Finset.mem_filter.mp ha).2.2
  change g=[i] at hg
  subst g
  have hprofile := sector_profile X s (b,[i],j) ha
  have htest := ((mem_profiles _ _ _ _).mp hprofile).2.2
  have hji : j + 1 ≤ i := by
    have horder : i > j := by simpa [profileTest] using htest.2.1
    omega
  have hf := (mem_fibre _ _ _ _ _).mp ht
  have hbands : p∈primeBand (SieveWeightedCutoffs.level X s) s z i ∧
      q∈primeBand (SieveWeightedCutoffs.level X s) s z j := by simpa using hf
  have hp := ((mem_primeBand _ _ _ _ _).mp hbands.1).2.2.1
  have hq := ((mem_primeBand _ _ _ _ _).mp hbands.2).2.2.2
  have hD : 1<SieveWeightedCutoffs.level X s := Real.one_lt_rpow hX (by linarith)
  have hscale := (SieveGeometricGrid.scale_strictMono _ s hD hs).monotone hji
  have hqp : (q:ℝ)<p := hq.trans_le (hscale.trans hp)
  exact_mod_cast hqp

theorem prime_pair_product_unique (c : ℝ) (d e p q u v : ℕ)
    (hd : 0<d) (he : 0<e) (hp : p.Prime) (hq : q.Prime)
    (hu : u.Prime) (hv : v.Prime) (hqp : q<p) (hvu : v<u)
    (hdc : (d:ℝ)<c) (hec : (e:ℝ)<c)
    (hcp : c≤(p:ℝ)) (hcq : c≤(q:ℝ))
    (hcu : c≤(u:ℝ)) (hcv : c≤(v:ℝ))
    (h : d*(p*q)=e*(u*v)) : d=e ∧ p=u ∧ q=v := by
  have hpdvd : p∣e*(u*v) := h ▸ dvd_mul_of_dvd_right (Nat.dvd_mul_right p q) d
  have hpn : ¬p∣e := by
    intro hh
    have hle : (p:ℝ)≤e := by exact_mod_cast Nat.le_of_dvd he hh
    linarith
  have hpuv := (hp.dvd_mul.mp hpdvd).resolve_left hpn
  rcases hp.dvd_mul.mp hpuv with hpu | hpv
  · have hpu := (Nat.prime_dvd_prime_iff_eq hp hu).mp hpu
    subst u
    have hcancel : p*(d*q)=p*(e*v) := by
      simpa only [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using h
    have heq := Nat.eq_of_mul_eq_mul_left hp.pos hcancel
    obtain ⟨hde,hqv⟩ := SingletonActualGeometry.prime_product_unique c d e q v
      hd he hq hv hdc hec hcq hcv heq
    exact ⟨hde,rfl,hqv⟩
  · have hpv := (Nat.prime_dvd_prime_iff_eq hp hv).mp hpv
    have hqdvd : q∣e*(u*v) := h ▸ dvd_mul_of_dvd_right (Nat.dvd_mul_left q p) d
    have hqn : ¬q∣e := by
      intro hh
      have hle : (q:ℝ)≤e := by exact_mod_cast Nat.le_of_dvd he hh
      linarith
    have hquv := (hq.dvd_mul.mp hqdvd).resolve_left hqn
    rcases hq.dvd_mul.mp hquv with hqu | hqv
    · have hqu := (Nat.prime_dvd_prime_iff_eq hq hu).mp hqu
      omega
    · have hqv := (Nat.prime_dvd_prime_iff_eq hq hv).mp hqv
      omega

theorem representation_unique (X s z : ℝ) (hX : 1<X) (hs : 0<s) (hs1 : s≤1/1000)
    (d e : ℕ) (hd : d∈FrontierSmallBracketSplit.lowSupport X s)
    (he : e∈FrontierSmallBracketSplit.lowSupport X s)
    (t u : List ℕ) (ht : t∈tuples X s z) (hu : u∈tuples X s z)
    (h : d*t.prod=e*u.prod) : d=e ∧ t=u := by
  obtain ⟨p,q,rfl⟩ := List.length_eq_two.mp (tuple_length X s z t ht)
  obtain ⟨v,w,rfl⟩ := List.length_eq_two.mp (tuple_length X s z u hu)
  obtain ⟨j,hj⟩ := tuple_bands X s z [p,q] ht p (by simp)
  obtain ⟨k,hk⟩ := tuple_bands X s z [p,q] ht q (by simp)
  obtain ⟨l,hl⟩ := tuple_bands X s z [v,w] hu v (by simp)
  obtain ⟨r,hr⟩ := tuple_bands X s z [v,w] hu w (by simp)
  simp only [List.prod_cons,List.prod_nil,mul_one] at h
  obtain ⟨hde,hpv,hqw⟩ := prime_pair_product_unique (X^FourPrimeScaleBudget.lowerExponent s)
    d e p q v w (SingletonActualGeometry.low_positive X s d hd)
    (SingletonActualGeometry.low_positive X s e he)
    ((mem_primeBand _ _ _ _ _).mp hj).1 ((mem_primeBand _ _ _ _ _).mp hk).1
    ((mem_primeBand _ _ _ _ _).mp hl).1 ((mem_primeBand _ _ _ _ _).mp hr).1
    (tuple_order X s z hX hs hs1 p q ht) (tuple_order X s z hX hs hs1 v w hu)
    ((FrontierSmallBracketSplit.mem_lowSupport X s d).mp hd).2
    ((FrontierSmallBracketSplit.mem_lowSupport X s e).mp he).2
    (SingletonActualGeometry.band_lower X s z hX hs hs1 j p hj)
    (SingletonActualGeometry.band_lower X s z hX hs hs1 k q hk)
    (SingletonActualGeometry.band_lower X s z hX hs hs1 l v hl)
    (SingletonActualGeometry.band_lower X s z hX hs hs1 r w hr) h
  exact ⟨hde,by rw [hpv,hqw]⟩

run_cmd do
  for decl in [``tuple_order,``prime_pair_product_unique,``representation_unique] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ACTUAL STRICTLY ORDERED PAIR REPRESENTATION UNIQUENESS PASSED"

end PairActualUnique
