import SieveReciprocalModel
import SieveSmallWeights
import SieveBoxPrefix

/-! Exact first-failed-test expansion of the actual finite selector losses.
The list enumeration retains every skip/include path. No family of error
terms is supplied as a hypothesis, and no quantitative tail bound is assumed. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace SieveStoppingExpansion

abbrev Stop := List ℕ × List ℕ

/-- Selected prefix (including the first rejected prime), and the complete
remaining ambient tail at that rejection. -/
def stops (gate : ℕ → ℕ → Prop) (upper : Bool) (d : ℕ) : List ℕ → List Stop
  | [] => []
  | p :: ps => stops gate upper d ps ++
      if upper = false ∨ gate d p then
        (stops gate (!upper) (d*p) ps).map (fun v => (p :: v.1, v.2))
      else [([p], ps)]

def weight (b : ℕ → ℝ) (v : Stop) : ℝ :=
  (v.1.map b).prod * SievePrefixLoss.euler v.2 b

def loss (gate : ℕ → ℕ → Prop) (upper : Bool) (d : ℕ)
    (ps : List ℕ) (b : ℕ → ℝ) : ℝ :=
  if upper then SievePrefixLoss.upper gate d ps b else SievePrefixLoss.lower gate d ps b

/-- Earlier selected inclusions passed their tests, and the last selected
inclusion is the first failed checked gate. Skipped primes are not tested. -/
def firstFailure (gate : ℕ → ℕ → Prop) (upper : Bool) (d : ℕ) : List ℕ → Prop
  | [] => False
  | p :: ps => (ps = [] ∧ upper = true ∧ ¬gate d p) ∨
      ((upper = false ∨ gate d p) ∧ firstFailure gate (!upper) (d*p) ps)

theorem weight_prepend (b : ℕ → ℝ) (p : ℕ) (v : Stop) :
    weight b (p :: v.1, v.2) = b p * weight b v := by
  simp only [weight, List.map_cons, List.prod_cons, mul_assoc]

theorem sum_prepend (b : ℕ → ℝ) (p : ℕ) (vs : List Stop) :
    ((vs.map (fun v => (p :: v.1, v.2))).map (weight b)).sum =
      b p * (vs.map (weight b)).sum := by
  induction vs with
  | nil => simp
  | cons v vs ih => simp only [List.map_cons, List.sum_cons, weight_prepend, ih, mul_add]

/-- Both genuine loss recurrences are expanded, with no chosen-error premise. -/
theorem loss_expansion (gate : ℕ → ℕ → Prop) (upper : Bool) (d : ℕ)
    (ps : List ℕ) (b : ℕ → ℝ) (hnd : ps.Nodup) :
    loss gate upper d ps b = ((stops gate upper d ps).map (weight b)).sum := by
  induction ps generalizing upper d with
  | nil =>
    cases upper with
    | false => exact (SievePrefixLoss.nil_losses gate d b).1
    | true => exact (SievePrefixLoss.nil_losses gate d b).2
  | cons p ps ih =>
    obtain ⟨hp, hnd⟩ := List.nodup_cons.mp hnd
    cases upper with
    | false =>
      simp only [loss, Bool.false_eq_true, ite_false]
      rw [SievePrefixLoss.lower_cons gate d p ps b hp]
      change loss gate false d ps b + b p * loss gate true (d*p) ps b = _
      rw [ih false d hnd, ih true (d*p) hnd]
      simp only [stops, true_or, ite_true, Bool.not_false, List.map_append,
        List.sum_append, sum_prepend]
    | true =>
      simp only [loss, ite_true]
      rw [SievePrefixLoss.upper_cons gate d p ps b hp]
      by_cases hg : gate d p
      · simp only [hg, ite_true]
        change loss gate true d ps b + b p * loss gate false (d*p) ps b = _
        rw [ih true d hnd, ih false (d*p) hnd]
        simp only [stops, Bool.true_eq_false, false_or, hg, ite_true, Bool.not_true,
          List.map_append, List.sum_append, sum_prepend]
      · simp only [hg, ite_false]
        change loss gate true d ps b + b p * SievePrefixLoss.euler ps b = _
        rw [ih true d hnd]
        simp [stops, hg, weight]

theorem lower_expansion (gate : ℕ → ℕ → Prop) (d : ℕ)
    (ps : List ℕ) (b : ℕ → ℝ) (hnd : ps.Nodup) :
    SievePrefixLoss.lower gate d ps b =
      ((stops gate false d ps).map (weight b)).sum := loss_expansion gate false d ps b hnd

theorem upper_expansion (gate : ℕ → ℕ → Prop) (d : ℕ)
    (ps : List ℕ) (b : ℕ → ℝ) (hnd : ps.Nodup) :
    SievePrefixLoss.upper gate d ps b =
      ((stops gate true d ps).map (weight b)).sum := loss_expansion gate true d ps b hnd

theorem stop_properties (gate : ℕ → ℕ → Prop) (upper : Bool) (d : ℕ)
    (ps : List ℕ) (v : Stop) (hv : v ∈ stops gate upper d ps) :
    firstFailure gate upper d v.1 ∧ (v.1 ++ v.2).Sublist ps ∧ v.2.IsSuffix ps := by
  induction ps generalizing upper d v with
  | nil => simp [stops] at hv
  | cons p ps ih =>
    simp only [stops, List.mem_append] at hv
    rcases hv with hv | hv
    · obtain ⟨hf, hsub, hsuf⟩ := ih upper d v hv
      exact ⟨hf, hsub.cons p, hsuf.trans (List.suffix_cons p ps)⟩
    · split_ifs at hv with hg
      · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
        obtain ⟨hf, hsub, hsuf⟩ := ih (!upper) (d*p) w hw
        exact ⟨Or.inr ⟨hg, hf⟩, hsub.cons_cons p, hsuf.trans (List.suffix_cons p ps)⟩
      · have heq : v = ([p], ps) := by simpa using hv
        subst v
        have hu : upper = true := by cases upper <;> simp_all
        have hgate : ¬gate d p := by tauto
        exact ⟨Or.inl ⟨rfl, hu, hgate⟩, List.Sublist.refl _, List.suffix_cons p ps⟩

/-- An explicit accepted proper prefix followed by its first rejected test. -/
theorem firstFailure_iff (gate : ℕ → ℕ → Prop) (upper : Bool) (d : ℕ) (qs : List ℕ) :
    firstFailure gate upper d qs ↔ ∃ pre p, qs = pre ++ [p] ∧
      SievePrefix.accepts gate upper d pre ∧
      SieveBoxPrefix.stateAt upper pre.length = true ∧ ¬gate (d*pre.prod) p := by
  induction qs generalizing upper d with
  | nil => simp [firstFailure]
  | cons p qs ih =>
    constructor
    · intro hf
      rcases hf with ⟨rfl, hu, hg⟩ | ⟨hg, hf⟩
      · exact ⟨[], p, rfl, trivial, hu, by simpa using hg⟩
      · obtain ⟨pre, q, hqs, ha, hstate, hfail⟩ := (ih (!upper) (d*p)).mp hf
        refine ⟨p :: pre, q, by simp [hqs], ⟨hg, ha⟩, ?_, ?_⟩
        · simpa only [List.length_cons, SieveBoxPrefix.stateAt] using hstate
        · simpa only [List.prod_cons, mul_assoc] using hfail
    · rintro ⟨pre, q, heq, ha, hstate, hfail⟩
      cases pre with
      | nil =>
        have heq' : p = q ∧ qs = [] := by simpa using heq
        obtain ⟨rfl, rfl⟩ := heq'
        exact Or.inl ⟨rfl, hstate, by simpa using hfail⟩
      | cons r pre =>
        have heq' : p = r ∧ qs = pre ++ [q] := List.cons.inj heq
        obtain ⟨rfl, hqs⟩ := heq'
        refine Or.inr ⟨ha.1, (ih (!upper) (d*p)).mpr ⟨pre, q, hqs, ha.2, ?_, ?_⟩⟩
        · simpa only [List.length_cons, SieveBoxPrefix.stateAt] using hstate
        · simpa only [List.prod_cons, mul_assoc] using hfail

theorem stop_first_failure (gate : ℕ → ℕ → Prop) (upper : Bool) (d : ℕ)
    (ps : List ℕ) (v : Stop) (hv : v ∈ stops gate upper d ps) :
    ∃ pre p, v.1 = pre ++ [p] ∧ SievePrefix.accepts gate upper d pre ∧
      SieveBoxPrefix.stateAt upper pre.length = true ∧ ¬gate (d*pre.prod) p :=
  (firstFailure_iff gate upper d v.1).mp (stop_properties gate upper d ps v hv).1

theorem weight_nonnegative (gate : ℕ → ℕ → Prop) (upper : Bool) (d : ℕ)
    (ps : List ℕ) (b : ℕ → ℝ) (hb : ∀ p ∈ ps, 0 ≤ b p ∧ b p ≤ 1)
    (v : Stop) (hv : v ∈ stops gate upper d ps) : 0 ≤ weight b v := by
  have hsub := (stop_properties gate upper d ps v hv).2.1.subset
  apply mul_nonneg
  · apply List.prod_nonneg
    intro x hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    exact (hb p (hsub (List.mem_append_left _ hp))).1
  · apply Finset.prod_nonneg
    intro p hp
    exact sub_nonneg.mpr (hb p (hsub (List.mem_append_right _ (List.mem_toFinset.mp hp)))).2

theorem stop_descending (gate : ℕ → ℕ → Prop) (upper : Bool) (d : ℕ)
    (ps : List ℕ) (hdesc : ps.Pairwise (fun p q => q ≤ p)) (v : Stop)
    (hv : v ∈ stops gate upper d ps) : (v.1 ++ v.2).Pairwise (fun p q => q ≤ p) :=
  hdesc.sublist (stop_properties gate upper d ps v hv).2.1

theorem lower_reciprocal_expansion (gate : ℕ → ℕ → Prop) (d : ℕ)
    (ps : List ℕ) (hnd : ps.Nodup) :
    SieveReciprocalModel.mass gate false d ps =
      SievePrefixLoss.euler ps (fun p => (p:ℝ)⁻¹) -
        ((stops gate false d ps).map (weight (fun p => (p:ℝ)⁻¹))).sum := by
  rw [SieveReciprocalModel.lower_mass_exact, lower_expansion gate d ps _ hnd]

theorem upper_reciprocal_expansion (gate : ℕ → ℕ → Prop) (d : ℕ)
    (ps : List ℕ) (hnd : ps.Nodup) :
    SieveReciprocalModel.mass gate true d ps =
      SievePrefixLoss.euler ps (fun p => (p:ℝ)⁻¹) +
        ((stops gate true d ps).map (weight (fun p => (p:ℝ)⁻¹))).sum := by
  rw [SieveReciprocalModel.upper_mass_exact, upper_expansion gate d ps _ hnd]

/-- The actual Rosser stop is at its cubic threshold, at the correct parity. -/
theorem rosser_stop (D : ℝ) (upper : Bool) (d : ℕ) (ps : List ℕ)
    (v : Stop) (hv : v ∈ stops (SieveRosser.cubicGate D) upper d ps) :
    ∃ pre p, v.1 = pre ++ [p] ∧
      SievePrefix.accepts (SieveRosser.cubicGate D) upper d pre ∧
      SieveBoxPrefix.stateAt upper pre.length = true ∧
      D ≤ ((d*pre.prod*p^3 : ℕ):ℝ) := by
  obtain ⟨pre, p, hpre, ha, hs, hf⟩ := stop_first_failure _ upper d ps v hv
  exact ⟨pre, p, hpre, ha, hs, not_lt.mp hf⟩

theorem small_lower_mass (T z : ℝ) :
    HarmanDivisorWindow.reciprocalMass (SieveSmallWeights.support T z false)
        (SieveSmallWeights.weight T z false) =
      SievePrefixLoss.euler (SieveSmallWeights.primes z) (fun p => (p:ℝ)⁻¹) -
        ((stops (SieveRosser.cubicGate T) false 1 (SieveSmallWeights.primes z)).map
          (weight (fun p => (p:ℝ)⁻¹))).sum :=
  lower_reciprocal_expansion _ 1 _ (SieveSmallWeights.primes_nodup z)

theorem small_upper_mass (T z : ℝ) :
    HarmanDivisorWindow.reciprocalMass (SieveSmallWeights.support T z true)
        (SieveSmallWeights.weight T z true) =
      SievePrefixLoss.euler (SieveSmallWeights.primes z) (fun p => (p:ℝ)⁻¹) +
        ((stops (SieveRosser.cubicGate T) true 1 (SieveSmallWeights.primes z)).map
          (weight (fun p => (p:ℝ)⁻¹))).sum :=
  upper_reciprocal_expansion _ 1 _ (SieveSmallWeights.primes_nodup z)

theorem small_stop_nonnegative (T z : ℝ) (upper : Bool) (v : Stop)
    (hv : v ∈ stops (SieveRosser.cubicGate T) upper 1 (SieveSmallWeights.primes z)) :
    0 ≤ weight (fun p => (p:ℝ)⁻¹) v :=
  weight_nonnegative _ upper 1 _ _
    (SieveReciprocalModel.reciprocal_in_unit_interval _ (SieveSmallWeights.primes_prime z)) v hv

run_cmd do
  for decl in [``weight_prepend, ``sum_prepend, ``loss_expansion, ``lower_expansion,
      ``upper_expansion, ``stop_properties, ``firstFailure_iff, ``stop_first_failure,
      ``weight_nonnegative, ``stop_descending, ``lower_reciprocal_expansion,
      ``upper_reciprocal_expansion, ``rosser_stop, ``small_lower_mass, ``small_upper_mass,
      ``small_stop_nonnegative] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "SIEVE STOPPING EXPANSION PASSED; QUANTITATIVE TAIL ESTIMATE REMAINS OPEN"

end SieveStoppingExpansion
end
