import SieveStoppingExpansion

/-! The stopping expansion in its prime-tail form. The Euler factor is the
complete product over primes below the first rejected prime, not an arbitrary
subproduct. These exact identities do not yet bound the stopping sums. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace SieveStoppingExpansion

def lastPrime (v : Stop) : ℕ := v.1.reverse.headD 0

def primeEuler (z : ℝ) : ℝ :=
  SievePrefixLoss.euler (SieveSmallWeights.primes z) (fun p => (p:ℝ)⁻¹)

/-- Every recorded remainder is exactly the ambient suffix immediately
following the last selected prime. The earlier selected primes may skip entries. -/
theorem stop_split (gate : ℕ → ℕ → Prop) (upper : Bool) (d : ℕ)
    (ps : List ℕ) (v : Stop) (hv : v ∈ stops gate upper d ps) :
    ∃ before pre p, ps = before ++ p :: v.2 ∧ v.1 = pre ++ [p] ∧ pre.Sublist before := by
  induction ps generalizing upper d v with
  | nil => simp [stops] at hv
  | cons p ps ih =>
    simp only [stops, List.mem_append] at hv
    rcases hv with hv | hv
    · obtain ⟨before, pre, q, hps, hpre, hsub⟩ := ih upper d v hv
      exact ⟨p :: before, pre, q, by simp [hps], hpre, hsub.cons p⟩
    · split_ifs at hv with hg
      · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
        obtain ⟨before, pre, q, hps, hpre, hsub⟩ := ih (!upper) (d*p) w hw
        exact ⟨p :: before, p :: pre, q, by simp [hps], by simp [hpre], hsub.cons_cons p⟩
      · have heq : v = ([p], ps) := by simpa using hv
        subst v
        exact ⟨[], [], p, rfl, rfl, List.Sublist.refl _⟩

theorem lastPrime_append (pre : List ℕ) (p : ℕ) (tail : List ℕ) :
    lastPrime (pre ++ [p], tail) = p := by
  simp [lastPrime]

theorem lastPrime_mem (gate : ℕ → ℕ → Prop) (upper : Bool) (d : ℕ)
    (ps : List ℕ) (v : Stop) (hv : v ∈ stops gate upper d ps) : lastPrime v ∈ ps := by
  obtain ⟨before, pre, p, hps, hpre, _⟩ := stop_split gate upper d ps v hv
  have hp : lastPrime v = p := by simp [lastPrime, hpre]
  simp [hp, hps]

theorem tail_membership (before tail : List ℕ) (p q : ℕ)
    (hdesc : (before ++ p :: tail).Pairwise (· > ·)) :
    q ∈ tail ↔ q ∈ before ++ p :: tail ∧ q < p := by
  obtain ⟨_, hpt, hcross⟩ := List.pairwise_append.mp hdesc
  obtain ⟨hp, _⟩ := List.pairwise_cons.mp hpt
  constructor
  · intro hq
    exact ⟨by simp [hq], hp q hq⟩
  · rintro ⟨hq, hlt⟩
    simp only [List.mem_append, List.mem_cons] at hq
    rcases hq with hbefore | rfl | htail
    · exact False.elim ((not_lt_of_ge (hcross q hbefore p (by simp)).le) hlt)
    · exact False.elim (lt_irrefl _ hlt)
    · exact htail

theorem stop_tail_membership (gate : ℕ → ℕ → Prop) (upper : Bool) (d : ℕ)
    (ps : List ℕ) (hdesc : ps.Pairwise (· > ·)) (v : Stop)
    (hv : v ∈ stops gate upper d ps) (q : ℕ) :
    q ∈ v.2 ↔ q ∈ ps ∧ q < lastPrime v := by
  obtain ⟨before, pre, p, hps, hpre, _⟩ := stop_split gate upper d ps v hv
  have hp : lastPrime v = p := by simp [lastPrime, hpre]
  rw [hps] at hdesc ⊢
  rw [hp]
  exact tail_membership before v.2 p q hdesc

theorem small_tail_eq (T z : ℝ) (upper : Bool) (v : Stop)
    (hv : v ∈ stops (SieveRosser.cubicGate T) upper 1 (SieveSmallWeights.primes z)) :
    v.2.toFinset = SieveSmallWeights.pool (lastPrime v : ℝ) := by
  have hdesc : (SieveSmallWeights.primes z).Pairwise (· > ·) :=
    (SieveSmallWeights.pool z).sortedGT_sort.pairwise
  have hpz := ((SieveSmallWeights.mem_primes z (lastPrime v)).mp
    (lastPrime_mem _ upper 1 _ v hv)).2
  ext q
  rw [List.mem_toFinset, stop_tail_membership _ upper 1 _ hdesc v hv,
    SieveSmallWeights.mem_primes, SieveSmallWeights.mem_pool]
  constructor
  · rintro ⟨⟨hprime, _⟩, hlt⟩
    exact ⟨hprime, by exact_mod_cast hlt⟩
  · rintro ⟨hprime, hlt⟩
    exact ⟨⟨hprime, hlt.trans hpz⟩, by exact_mod_cast hlt⟩

theorem small_tail_euler (T z : ℝ) (upper : Bool) (v : Stop)
    (hv : v ∈ stops (SieveRosser.cubicGate T) upper 1 (SieveSmallWeights.primes z)) :
    SievePrefixLoss.euler v.2 (fun p => (p:ℝ)⁻¹) = primeEuler (lastPrime v : ℝ) := by
  simp only [SievePrefixLoss.euler, primeEuler, SieveSmallWeights.primes_toFinset]
  rw [small_tail_eq T z upper v hv]

theorem reciprocal_product (ps : List ℕ) :
    (ps.map (fun p : ℕ => (p:ℝ)⁻¹)).prod = (ps.prod : ℝ)⁻¹ := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    simp only [List.map_cons, List.prod_cons, Nat.cast_mul, mul_inv_rev, ih]
    exact mul_comm _ _

theorem small_weight_exact (T z : ℝ) (upper : Bool) (v : Stop)
    (hv : v ∈ stops (SieveRosser.cubicGate T) upper 1 (SieveSmallWeights.primes z)) :
    weight (fun p => (p:ℝ)⁻¹) v = primeEuler (lastPrime v : ℝ) / (v.1.prod : ℝ) := by
  rw [weight, reciprocal_product, small_tail_euler T z upper v hv]
  exact mul_comm _ _

theorem small_lower_prime_tail (T z : ℝ) :
    HarmanDivisorWindow.reciprocalMass (SieveSmallWeights.support T z false)
        (SieveSmallWeights.weight T z false) = primeEuler z -
      ((stops (SieveRosser.cubicGate T) false 1 (SieveSmallWeights.primes z)).map
        (fun v => primeEuler (lastPrime v : ℝ) / (v.1.prod : ℝ))).sum := by
  rw [small_lower_mass]
  apply congrArg (fun x => primeEuler z - x)
  apply congrArg List.sum
  apply List.map_congr_left
  intro v hv
  exact small_weight_exact T z false v hv

theorem small_upper_prime_tail (T z : ℝ) :
    HarmanDivisorWindow.reciprocalMass (SieveSmallWeights.support T z true)
        (SieveSmallWeights.weight T z true) = primeEuler z +
      ((stops (SieveRosser.cubicGate T) true 1 (SieveSmallWeights.primes z)).map
        (fun v => primeEuler (lastPrime v : ℝ) / (v.1.prod : ℝ))).sum := by
  rw [small_upper_mass]
  apply congrArg (fun x => primeEuler z + x)
  apply congrArg List.sum
  apply List.map_congr_left
  intro v hv
  exact small_weight_exact T z true v hv

run_cmd do
  for decl in [``stop_split, ``lastPrime_append, ``lastPrime_mem, ``tail_membership,
      ``stop_tail_membership, ``small_tail_eq, ``small_tail_euler, ``reciprocal_product,
      ``small_weight_exact, ``small_lower_prime_tail, ``small_upper_prime_tail] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "EXACT COMPLETE PRIME TAILS PASSED; THEIR QUANTITATIVE SUM REMAINS OPEN"

end SieveStoppingExpansion
end
