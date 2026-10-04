import LongPairDistinctCoreWork

/-! Elementary uniqueness of a product of separated large primes and a
small positive divisor. This does not assert a fluctuation estimate. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section

namespace LargePrimeRepresentationWork

theorem prime_head_eq (p p' u v : ℕ) (hp : p.Prime) (hp' : p'.Prime)
    (hnot : ¬p∣v) (he : p*u=p'*v) : p=p' := by
  have hd : p∣p'*v := he ▸ dvd_mul_right p u
  have hdp : p∣p' := (hp.dvd_mul.mp hd).resolve_right hnot
  exact (Nat.prime_dvd_prime_iff_eq hp hp').mp hdp

/-- A separated large prime and a second prime, with a small divisor,
give a unique ordered representation. -/
theorem pair_rigidity (p d q p' d' q' : ℕ)
    (hp : p.Prime) (hq : q.Prime) (hp' : p'.Prime) (hq' : q'.Prime)
    (hd' : 0<d') (hdp : d'<p) (hqp : q'<p) (hdq : d'<q)
    (he : p*d*q=p'*d'*q') : p=p' ∧ d=d' ∧ q=q' := by
  have hn : ¬p∣d'*q' := hp.not_dvd_mul
    (Nat.not_dvd_of_pos_of_lt hd' hdp) (Nat.not_dvd_of_pos_of_lt hq'.pos hqp)
  have hpp := prime_head_eq p p' (d*q) (d'*q') hp hp' hn
    (by simpa only [Nat.mul_assoc] using he)
  have hm : d*q=d'*q' := by
    apply mul_left_cancel₀ hp.ne_zero
    simpa only [hpp,Nat.mul_assoc] using he
  have hqd : q∣d'*q' := hm ▸ dvd_mul_left q d
  have hqq := (Nat.prime_dvd_prime_iff_eq hq hq').mp
    ((hq.dvd_mul.mp hqd).resolve_left (Nat.not_dvd_of_pos_of_lt hd' hdq))
  have hdd : d=d' := by
    apply mul_right_cancel₀ hq.ne_zero
    simpa only [hqq] using hm
  exact ⟨hpp,hdd,hqq⟩

/-- With two distinct middle primes, the only ambiguity is their swap.
The cross-representation inequalities are explicit; no presumed sorting
of the middle primes is used. -/
theorem triple_rigidity (p d a b p' d' a' b' : ℕ)
    (hp : p.Prime) (ha : a.Prime) (hb : b.Prime)
    (hp' : p'.Prime) (ha' : a'.Prime) (hb' : b'.Prime)
    (hd' : 0<d') (hdp : d'<p) (hap : a'<p) (hbp : b'<p)
    (hda : d'<a) (hdb : d'<b) (hab : a≠b)
    (he : p*d*a*b=p'*d'*a'*b') :
    p=p' ∧ d=d' ∧ ((a=a' ∧ b=b') ∨ (a=b' ∧ b=a')) := by
  have hn : ¬p∣d'*a'*b' := hp.not_dvd_mul
    (hp.not_dvd_mul (Nat.not_dvd_of_pos_of_lt hd' hdp)
      (Nat.not_dvd_of_pos_of_lt ha'.pos hap))
    (Nat.not_dvd_of_pos_of_lt hb'.pos hbp)
  have hpp := prime_head_eq p p' (d*a*b) (d'*a'*b') hp hp' hn
    (by simpa only [Nat.mul_assoc] using he)
  have hm : d*a*b=d'*a'*b' := by
    apply mul_left_cancel₀ hp.ne_zero
    simpa only [hpp,Nat.mul_assoc] using he
  have had : a∣d'*a'*b' := by
    rw [←hm]
    exact ⟨d*b,by ring⟩
  have hbd : b∣d'*a'*b' := hm ▸ dvd_mul_left b (d*a)
  have haeq : a=a' ∨ a=b' := by
    simpa only [ha.dvd_mul,Nat.not_dvd_of_pos_of_lt hd' hda,false_or,
      Nat.prime_dvd_prime_iff_eq ha ha',Nat.prime_dvd_prime_iff_eq ha hb'] using had
  have hbeq : b=a' ∨ b=b' := by
    simpa only [hb.dvd_mul,Nat.not_dvd_of_pos_of_lt hd' hdb,false_or,
      Nat.prime_dvd_prime_iff_eq hb ha',Nat.prime_dvd_prime_iff_eq hb hb'] using hbd
  have hpairs : (a=a' ∧ b=b') ∨ (a=b' ∧ b=a') := by
    rcases haeq with hA | hA <;> rcases hbeq with hB | hB
    · exact False.elim (hab (hA.trans hB.symm))
    · exact Or.inl ⟨hA,hB⟩
    · exact Or.inr ⟨hA,hB⟩
    · exact False.elim (hab (hA.trans hB.symm))
  have hprod : a*b=a'*b' := by
    rcases hpairs with ⟨hA,hB⟩ | ⟨hA,hB⟩
    · rw [hA,hB]
    · rw [hA,hB,Nat.mul_comm]
  have hdd : d=d' := by
    apply mul_right_cancel₀ (mul_ne_zero ha.ne_zero hb.ne_zero)
    simpa only [Nat.mul_assoc,←hprod] using hm
  exact ⟨hpp,hdd,hpairs⟩

#print axioms triple_rigidity
run_cmd do
  for decl in [``prime_head_eq, ``pair_rigidity, ``triple_rigidity] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"

end LargePrimeRepresentationWork
