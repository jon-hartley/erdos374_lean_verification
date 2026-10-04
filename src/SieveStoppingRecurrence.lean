import SieveStoppingTail

/-! Exact first-selected-prime recurrences for the actual cubic Rosser losses.
The remaining list is the complete smaller-prime pool; the level is divided
by the first selected prime. No continuous comparison or decay is assumed. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace SieveStoppingRecurrence

def firstSteps : List ℕ → List (ℕ × List ℕ)
  | [] => []
  | p :: ps => (p, ps) :: firstSteps ps

theorem firstSteps_heads (ps : List ℕ) : (firstSteps ps).map Prod.fst = ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [firstSteps, ih]

theorem firstSteps_split (ps : List ℕ) (v : ℕ × List ℕ)
    (hv : v ∈ firstSteps ps) : ∃ before, ps = before ++ v.1 :: v.2 := by
  induction ps with
  | nil => simp [firstSteps] at hv
  | cons p ps ih =>
    simp only [firstSteps, List.mem_cons] at hv
    rcases hv with rfl | hv
    · exact ⟨[], rfl⟩
    · obtain ⟨before, hb⟩ := ih hv
      exact ⟨p :: before, by simp [hb]⟩

theorem lower_firstSteps (gate : ℕ → ℕ → Prop) (d : ℕ) (ps : List ℕ)
    (b : ℕ → ℝ) (hnd : ps.Nodup) :
    SievePrefixLoss.lower gate d ps b =
      ((firstSteps ps).map (fun v => b v.1 *
        SievePrefixLoss.upper gate (d*v.1) v.2 b)).sum := by
  induction ps with
  | nil => simpa [firstSteps] using (SievePrefixLoss.nil_losses gate d b).1
  | cons p ps ih =>
    obtain ⟨hp, hn⟩ := List.nodup_cons.mp hnd
    rw [SievePrefixLoss.lower_cons gate d p ps b hp, ih hn]
    simp only [firstSteps, List.map_cons, List.sum_cons]
    exact add_comm _ _

theorem upper_firstSteps (gate : ℕ → ℕ → Prop) (d : ℕ) (ps : List ℕ)
    (b : ℕ → ℝ) (hnd : ps.Nodup) :
    SievePrefixLoss.upper gate d ps b =
      ((firstSteps ps).map (fun v => if gate d v.1 then b v.1 *
        SievePrefixLoss.lower gate (d*v.1) v.2 b
        else b v.1 * SievePrefixLoss.euler v.2 b)).sum := by
  induction ps with
  | nil => simpa [firstSteps] using (SievePrefixLoss.nil_losses gate d b).2
  | cons p ps ih =>
    obtain ⟨hp, hn⟩ := List.nodup_cons.mp hnd
    rw [SievePrefixLoss.upper_cons gate d p ps b hp, ih hn]
    simp only [firstSteps, List.map_cons, List.sum_cons]
    exact add_comm _ _

theorem prime_firstSteps_tail (z : ℝ) (v : ℕ × List ℕ)
    (hv : v ∈ firstSteps (SieveSmallWeights.primes z)) :
    v.1.Prime ∧ v.2 = SieveSmallWeights.primes (v.1 : ℝ) := by
  obtain ⟨before, heq⟩ := firstSteps_split _ v hv
  have hdesc : (SieveSmallWeights.primes z).Pairwise (· > ·) :=
    (SieveSmallWeights.pool z).sortedGT_sort.pairwise
  have hp : v.1 ∈ SieveSmallWeights.primes z := by rw [heq]; simp
  have hpz := (SieveSmallWeights.mem_primes z v.1).mp hp
  refine ⟨hpz.1, ?_⟩
  rw [heq] at hdesc
  have htail := (List.pairwise_append.mp hdesc).2.1.of_cons
  apply htail.eq_of_mem_iff (SieveSmallWeights.pool (v.1:ℝ)).sortedGT_sort.pairwise
  intro q
  change q ∈ v.2 ↔ q ∈ SieveSmallWeights.primes (v.1:ℝ)
  rw [SieveStoppingExpansion.tail_membership before v.2 v.1 q hdesc,
    ← heq, SieveSmallWeights.mem_primes, SieveSmallWeights.mem_primes]
  constructor
  · rintro ⟨⟨hq, _⟩, hlt⟩
    exact ⟨hq, by exact_mod_cast hlt⟩
  · rintro ⟨hq, hlt⟩
    exact ⟨⟨hq, hlt.trans hpz.2⟩, by exact_mod_cast hlt⟩

theorem cubicGate_rescale (T : ℝ) (p d q : ℕ) (hp : 0 < p) :
    SieveRosser.cubicGate T (p*d) q ↔
      SieveRosser.cubicGate (T/(p:ℝ)) d q := by
  have hp' : (0:ℝ) < p := by exact_mod_cast hp
  unfold SieveRosser.cubicGate
  rw [lt_div_iff₀ hp']
  simp only [Nat.cast_mul, Nat.cast_pow]
  ring_nf

theorem selected_rescale (T : ℝ) (p : ℕ) (hp : 0 < p)
    (mode : Bool) (d : ℕ) (ps : List ℕ) :
    SievePrefix.selected (SieveRosser.cubicGate T) mode (p*d) ps =
      SievePrefix.selected (SieveRosser.cubicGate (T/(p:ℝ))) mode d ps := by
  induction ps generalizing mode d with
  | nil => rfl
  | cons q ps ih =>
    simp only [SievePrefix.selected, Nat.mul_assoc,
      cubicGate_rescale T p d q hp, ih]

theorem lower_rescale (T : ℝ) (p : ℕ) (hp : 0 < p) (d : ℕ)
    (ps : List ℕ) (b : ℕ → ℝ) :
    SievePrefixLoss.lower (SieveRosser.cubicGate T) (p*d) ps b =
      SievePrefixLoss.lower (SieveRosser.cubicGate (T/(p:ℝ))) d ps b := by
  simp only [SievePrefixLoss.lower, SievePrefix.value, selected_rescale T p hp]

theorem upper_rescale (T : ℝ) (p : ℕ) (hp : 0 < p) (d : ℕ)
    (ps : List ℕ) (b : ℕ → ℝ) :
    SievePrefixLoss.upper (SieveRosser.cubicGate T) (p*d) ps b =
      SievePrefixLoss.upper (SieveRosser.cubicGate (T/(p:ℝ))) d ps b := by
  simp only [SievePrefixLoss.upper, SievePrefix.value, selected_rescale T p hp]

def lowerLoss (T z : ℝ) : ℝ :=
  SievePrefixLoss.lower (SieveRosser.cubicGate T) 1
    (SieveSmallWeights.primes z) (fun p => (p:ℝ)⁻¹)

def upperLoss (T z : ℝ) : ℝ :=
  SievePrefixLoss.upper (SieveRosser.cubicGate T) 1
    (SieveSmallWeights.primes z) (fun p => (p:ℝ)⁻¹)

theorem lowerLoss_first_prime (T z : ℝ) :
    lowerLoss T z = ∑ p ∈ SieveSmallWeights.pool z,
      (p:ℝ)⁻¹ * upperLoss (T/(p:ℝ)) (p:ℝ) := by
  unfold lowerLoss
  rw [lower_firstSteps _ _ _ _ (SieveSmallWeights.primes_nodup z)]
  have hmap : ((firstSteps (SieveSmallWeights.primes z)).map
      (fun v => (v.1:ℝ)⁻¹ * SievePrefixLoss.upper (SieveRosser.cubicGate T)
        (1*v.1) v.2 (fun p => (p:ℝ)⁻¹))) =
      ((firstSteps (SieveSmallWeights.primes z)).map
        (fun v => (v.1:ℝ)⁻¹ * upperLoss (T/(v.1:ℝ)) (v.1:ℝ))) := by
    apply List.map_congr_left
    intro v hv
    obtain ⟨hp, htail⟩ := prime_firstSteps_tail z v hv
    rw [htail]
    congr 1
    simpa only [one_mul, mul_one, upperLoss] using
      upper_rescale T v.1 hp.pos 1 (SieveSmallWeights.primes (v.1:ℝ))
        (fun p => (p:ℝ)⁻¹)
  rw [hmap]
  have hheads := congrArg (fun l : List ℕ =>
    (l.map (fun p : ℕ => (p:ℝ)⁻¹ * upperLoss (T/(p:ℝ)) (p:ℝ))).sum)
      (firstSteps_heads (SieveSmallWeights.primes z))
  simp only [List.map_map, Function.comp_def] at hheads
  rw [hheads]
  rw [← List.sum_toFinset _ (SieveSmallWeights.primes_nodup z),
    SieveSmallWeights.primes_toFinset]

theorem upperLoss_first_prime (T z : ℝ) :
    upperLoss T z = ∑ p ∈ SieveSmallWeights.pool z,
      if (p:ℝ)^3 < T then (p:ℝ)⁻¹ * lowerLoss (T/(p:ℝ)) (p:ℝ)
      else (p:ℝ)⁻¹ * SieveStoppingExpansion.primeEuler (p:ℝ) := by
  unfold upperLoss
  rw [upper_firstSteps _ _ _ _ (SieveSmallWeights.primes_nodup z)]
  have hmap : ((firstSteps (SieveSmallWeights.primes z)).map
      (fun v => if SieveRosser.cubicGate T 1 v.1 then
        (v.1:ℝ)⁻¹ * SievePrefixLoss.lower (SieveRosser.cubicGate T)
          (1*v.1) v.2 (fun p => (p:ℝ)⁻¹)
        else (v.1:ℝ)⁻¹ * SievePrefixLoss.euler v.2 (fun p => (p:ℝ)⁻¹))) =
      ((firstSteps (SieveSmallWeights.primes z)).map
        (fun v => if (v.1:ℝ)^3 < T then
          (v.1:ℝ)⁻¹ * lowerLoss (T/(v.1:ℝ)) (v.1:ℝ)
          else (v.1:ℝ)⁻¹ * SieveStoppingExpansion.primeEuler (v.1:ℝ))) := by
    apply List.map_congr_left
    intro v hv
    obtain ⟨hp, htail⟩ := prime_firstSteps_tail z v hv
    rw [htail]
    simp only [SieveRosser.cubicGate, one_mul, Nat.cast_pow]
    split_ifs
    · congr 1
      simpa only [mul_one, lowerLoss] using
        lower_rescale T v.1 hp.pos 1 (SieveSmallWeights.primes (v.1:ℝ))
          (fun p => (p:ℝ)⁻¹)
    · rfl
  rw [hmap]
  have hheads := congrArg (fun l : List ℕ =>
    (l.map (fun p : ℕ => if (p:ℝ)^3 < T then
      (p:ℝ)⁻¹ * lowerLoss (T/(p:ℝ)) (p:ℝ)
      else (p:ℝ)⁻¹ * SieveStoppingExpansion.primeEuler (p:ℝ))).sum)
      (firstSteps_heads (SieveSmallWeights.primes z))
  simp only [List.map_map, Function.comp_def] at hheads
  rw [hheads]
  rw [← List.sum_toFinset _ (SieveSmallWeights.primes_nodup z),
    SieveSmallWeights.primes_toFinset]

run_cmd do
  for decl in [``firstSteps_heads, ``firstSteps_split, ``lower_firstSteps,
      ``upper_firstSteps, ``prime_firstSteps_tail, ``cubicGate_rescale,
      ``selected_rescale, ``lower_rescale, ``upper_rescale,
      ``lowerLoss_first_prime, ``upperLoss_first_prime] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ACTUAL FIRST-SELECTED-PRIME RECURRENCES PASSED; NO DECAY CLAIM"

end SieveStoppingRecurrence
end
