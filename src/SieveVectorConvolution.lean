import SieveVectorCollection

/-! Actual vector-sieve coefficients collected by integer product. Disjoint
prime pools supply unique factor splits. The pointwise and interval inequalities
are proved from the recursive selectors, not supplied as analytic premises. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped BigOperators

namespace SieveVectorConvolution

def carrier (gate : ℕ → ℕ → Prop) (d : ℕ) (ps : List ℕ) : Finset ℕ :=
  SieveSelectedWindow.support gate false d ps ∪ SieveSelectedWindow.support gate true d ps

theorem support_subset_carrier (gate : ℕ → ℕ → Prop) (upper : Bool) (d : ℕ) (ps : List ℕ) :
    SieveSelectedWindow.support gate upper d ps ⊆ carrier gate d ps := by
  cases upper
  · exact Finset.subset_union_left
  · exact Finset.subset_union_right

theorem carrier_positive (gate : ℕ → ℕ → Prop) (d : ℕ) (ps : List ℕ)
    (hp : ∀ p ∈ ps, p.Prime) (m : ℕ) (hm : m ∈ carrier gate d ps) : 0 < m := by
  rcases Finset.mem_union.mp hm with hm | hm
  · exact SieveSelectedWindow.support_positive gate false d ps hp m hm
  · exact SieveSelectedWindow.support_positive gate true d ps hp m hm

theorem carrier_representation (gate : ℕ → ℕ → Prop) (d : ℕ) (ps : List ℕ)
    (m : ℕ) (hm : m ∈ carrier gate d ps) :
    ∃ s : Finset ℕ, s ⊆ ps.toFinset ∧ SievePrimeSubset.subsetProduct s = m := by
  rcases Finset.mem_union.mp hm with hm | hm
  · obtain ⟨s, hs, he⟩ := Finset.mem_image.mp hm
    exact ⟨s, SievePrefix.selected_subset gate false d ps s hs, he⟩
  · obtain ⟨s, hs, he⟩ := Finset.mem_image.mp hm
    exact ⟨s, SievePrefix.selected_subset gate true d ps s hs, he⟩

theorem carriers_coprime (gate0 gate1 : ℕ → ℕ → Prop) (d0 d1 : ℕ) (ps0 ps1 : List ℕ)
    (hp0 : ∀ p ∈ ps0, p.Prime) (hp1 : ∀ p ∈ ps1, p.Prime)
    (hdis : Disjoint ps0.toFinset ps1.toFinset) :
    ∀ m ∈ carrier gate0 d0 ps0, ∀ n ∈ carrier gate1 d1 ps1, m.Coprime n := by
  intro m hm n hn
  obtain ⟨s, hs, rfl⟩ := carrier_representation gate0 d0 ps0 m hm
  obtain ⟨t, ht, rfl⟩ := carrier_representation gate1 d1 ps1 n hn
  apply Nat.coprime_prod_left_iff.mpr
  intro p hp
  apply Nat.coprime_prod_right_iff.mpr
  intro q hq
  apply (Nat.coprime_primes (hp0 p (List.mem_toFinset.mp (hs hp)))
    (hp1 q (List.mem_toFinset.mp (ht hq)))).mpr
  intro he
  subst q
  exact Finset.disjoint_left.mp hdis (hs hp) (ht hq)

theorem coefficient_zero_of_not_support (gate : ℕ → ℕ → Prop) (upper : Bool)
    (d : ℕ) (ps : List ℕ) (m : ℕ) (hm : m ∉ SieveSelectedWindow.support gate upper d ps) :
    SieveSelectedWindow.coefficient gate upper d ps m = 0 :=
  SievePrimeSubset.selectedCoefficient_zero_of_not_mem _ m hm

theorem evaluation_carrier (gate : ℕ → ℕ → Prop) (upper : Bool)
    (d : ℕ) (ps : List ℕ) (n : ℕ) :
    SieveDivisorWindow.evaluation (carrier gate d ps) (SieveSelectedWindow.coefficient gate upper d ps) n =
      SieveVector.selectedEvaluation gate upper d ps n := by
  unfold SieveVector.selectedEvaluation SieveDivisorWindow.evaluation
  symm
  apply Finset.sum_subset (support_subset_carrier gate upper d ps)
  intro m hm hnot
  rw [coefficient_zero_of_not_support gate upper d ps m hnot]
  split_ifs <;> rfl

theorem mass_carrier (gate : ℕ → ℕ → Prop) (upper : Bool) (d : ℕ) (ps : List ℕ) :
    HarmanDivisorWindow.reciprocalMass (carrier gate d ps) (SieveSelectedWindow.coefficient gate upper d ps) =
      HarmanDivisorWindow.reciprocalMass (SieveSelectedWindow.support gate upper d ps)
        (SieveSelectedWindow.coefficient gate upper d ps) := by
  unfold HarmanDivisorWindow.reciprocalMass
  symm
  apply Finset.sum_subset (support_subset_carrier gate upper d ps)
  intro m hm hnot
  rw [coefficient_zero_of_not_support gate upper d ps m hnot, zero_div]

theorem coefficient_pair_control (gate : ℕ → ℕ → Prop) (d : ℕ) (ps : List ℕ)
    (hp : ∀ p ∈ ps, p.Prime) (m : ℕ) :
    |SieveSelectedWindow.coefficient gate false d ps m| ≤ 1 ∧
    |SieveSelectedWindow.coefficient gate true d ps m| ≤ 1 ∧
    (SieveSelectedWindow.coefficient gate false d ps m = 0 ∨
      SieveSelectedWindow.coefficient gate true d ps m = 0 ∨
      SieveSelectedWindow.coefficient gate false d ps m =
        SieveSelectedWindow.coefficient gate true d ps m) := by
  exact ⟨SieveSelectedWindow.coefficient_abs_le_one gate false d ps hp m,
    SieveSelectedWindow.coefficient_abs_le_one gate true d ps hp m,
    SievePrimeSubset.selectedCoefficient_shared_sign _ _
      (SieveSelectedWindow.selected_primes gate false d ps hp)
      (SieveSelectedWindow.selected_primes gate true d ps hp) m⟩

def support (gate0 gate1 : ℕ → ℕ → Prop) (d0 d1 : ℕ) (ps0 ps1 : List ℕ) : Finset ℕ :=
  FactoredDivisorWeights.support (carrier gate0 d0 ps0) (carrier gate1 d1 ps1)

def lowerCoefficient (gate0 gate1 : ℕ → ℕ → Prop) (d0 d1 : ℕ) (ps0 ps1 : List ℕ) : ℕ → ℝ :=
  SieveVectorCollection.lowerCoefficient (carrier gate0 d0 ps0) (carrier gate1 d1 ps1)
    (SieveSelectedWindow.coefficient gate0 false d0 ps0) (SieveSelectedWindow.coefficient gate0 true d0 ps0)
    (SieveSelectedWindow.coefficient gate1 false d1 ps1) (SieveSelectedWindow.coefficient gate1 true d1 ps1)

def upperCoefficient (gate0 gate1 : ℕ → ℕ → Prop) (d0 d1 : ℕ) (ps0 ps1 : List ℕ) : ℕ → ℝ :=
  FactoredDivisorWeights.coefficient (carrier gate0 d0 ps0) (carrier gate1 d1 ps1)
    (SieveSelectedWindow.coefficient gate0 true d0 ps0) (SieveSelectedWindow.coefficient gate1 true d1 ps1)

theorem support_positive (gate0 gate1 : ℕ → ℕ → Prop) (d0 d1 : ℕ) (ps0 ps1 : List ℕ)
    (hp0 : ∀ p ∈ ps0, p.Prime) (hp1 : ∀ p ∈ ps1, p.Prime) :
    ∀ m ∈ support gate0 gate1 d0 d1 ps0 ps1, 0 < m :=
  HarmanDivisorWindow.productSupport_positive _ _
    (carrier_positive gate0 d0 ps0 hp0) (carrier_positive gate1 d1 ps1 hp1)

theorem lowerCoefficient_abs_le_one (gate0 gate1 : ℕ → ℕ → Prop) (d0 d1 : ℕ)
    (ps0 ps1 : List ℕ) (hp0 : ∀ p ∈ ps0, p.Prime) (hp1 : ∀ p ∈ ps1, p.Prime)
    (hdis : Disjoint ps0.toFinset ps1.toFinset) (m : ℕ) :
    |lowerCoefficient gate0 gate1 d0 d1 ps0 ps1 m| ≤ 1 :=
  SieveVectorCollection.lowerCoefficient_abs_le_one _ _ _ _ _ _
    (carrier_positive gate0 d0 ps0 hp0) (carriers_coprime gate0 gate1 d0 d1 ps0 ps1 hp0 hp1 hdis)
    (fun v _ => coefficient_pair_control gate0 d0 ps0 hp0 v)
    (fun w _ => coefficient_pair_control gate1 d1 ps1 hp1 w) m

theorem upperCoefficient_abs_le_one (gate0 gate1 : ℕ → ℕ → Prop) (d0 d1 : ℕ)
    (ps0 ps1 : List ℕ) (hp0 : ∀ p ∈ ps0, p.Prime) (hp1 : ∀ p ∈ ps1, p.Prime)
    (hdis : Disjoint ps0.toFinset ps1.toFinset) (m : ℕ) :
    |upperCoefficient gate0 gate1 d0 d1 ps0 ps1 m| ≤ 1 :=
  SieveVectorCollection.upperCoefficient_abs_le_one _ _ _ _
    (carrier_positive gate0 d0 ps0 hp0) (carriers_coprime gate0 gate1 d0 d1 ps0 ps1 hp0 hp1 hdis)
    (fun v _ => SieveSelectedWindow.coefficient_abs_le_one gate0 true d0 ps0 hp0 v)
    (fun w _ => SieveSelectedWindow.coefficient_abs_le_one gate1 true d1 ps1 hp1 w) m

theorem lower_evaluation (gate0 gate1 : ℕ → ℕ → Prop) (d0 d1 : ℕ) (ps0 ps1 : List ℕ)
    (hp0 : ∀ p ∈ ps0, p.Prime) (hp1 : ∀ p ∈ ps1, p.Prime)
    (hdis : Disjoint ps0.toFinset ps1.toFinset) (n : ℕ) :
    SieveDivisorWindow.evaluation (support gate0 gate1 d0 d1 ps0 ps1)
      (lowerCoefficient gate0 gate1 d0 d1 ps0 ps1) n =
      SieveVector.lowerEvaluation gate0 gate1 d0 d1 ps0 ps1 n := by
  unfold support lowerCoefficient
  rw [SieveVectorCollection.lowerCoefficient_evaluation _ _ _ _ _ _
    (carriers_coprime gate0 gate1 d0 d1 ps0 ps1 hp0 hp1 hdis) n]
  rw [evaluation_carrier, evaluation_carrier, evaluation_carrier, evaluation_carrier]
  rfl

theorem upper_evaluation (gate0 gate1 : ℕ → ℕ → Prop) (d0 d1 : ℕ) (ps0 ps1 : List ℕ)
    (hp0 : ∀ p ∈ ps0, p.Prime) (hp1 : ∀ p ∈ ps1, p.Prime)
    (hdis : Disjoint ps0.toFinset ps1.toFinset) (n : ℕ) :
    SieveDivisorWindow.evaluation (support gate0 gate1 d0 d1 ps0 ps1)
      (upperCoefficient gate0 gate1 d0 d1 ps0 ps1) n =
      SieveVector.upperEvaluation gate0 gate1 d0 d1 ps0 ps1 n := by
  unfold support upperCoefficient
  rw [SieveVectorCollection.convolution_evaluation _ _ _ _
    (carriers_coprime gate0 gate1 d0 d1 ps0 ps1 hp0 hp1 hdis) n]
  rw [evaluation_carrier, evaluation_carrier]
  rfl

theorem lower_reciprocal_mass (gate0 gate1 : ℕ → ℕ → Prop) (d0 d1 : ℕ) (ps0 ps1 : List ℕ) :
    HarmanDivisorWindow.reciprocalMass (support gate0 gate1 d0 d1 ps0 ps1)
      (lowerCoefficient gate0 gate1 d0 d1 ps0 ps1) =
      SieveVector.lowerKernel
        (HarmanDivisorWindow.reciprocalMass (SieveSelectedWindow.support gate0 false d0 ps0)
          (SieveSelectedWindow.coefficient gate0 false d0 ps0))
        (HarmanDivisorWindow.reciprocalMass (SieveSelectedWindow.support gate0 true d0 ps0)
          (SieveSelectedWindow.coefficient gate0 true d0 ps0))
        (HarmanDivisorWindow.reciprocalMass (SieveSelectedWindow.support gate1 false d1 ps1)
          (SieveSelectedWindow.coefficient gate1 false d1 ps1))
        (HarmanDivisorWindow.reciprocalMass (SieveSelectedWindow.support gate1 true d1 ps1)
          (SieveSelectedWindow.coefficient gate1 true d1 ps1)) := by
  unfold support lowerCoefficient
  rw [SieveVectorCollection.lowerCoefficient_reciprocal_mass,
    mass_carrier, mass_carrier, mass_carrier, mass_carrier]

theorem upper_reciprocal_mass (gate0 gate1 : ℕ → ℕ → Prop) (d0 d1 : ℕ) (ps0 ps1 : List ℕ) :
    HarmanDivisorWindow.reciprocalMass (support gate0 gate1 d0 d1 ps0 ps1)
      (upperCoefficient gate0 gate1 d0 d1 ps0 ps1) =
      HarmanDivisorWindow.reciprocalMass (SieveSelectedWindow.support gate0 true d0 ps0)
          (SieveSelectedWindow.coefficient gate0 true d0 ps0) *
        HarmanDivisorWindow.reciprocalMass (SieveSelectedWindow.support gate1 true d1 ps1)
          (SieveSelectedWindow.coefficient gate1 true d1 ps1) := by
  unfold support upperCoefficient
  rw [FactoredDivisorWeights.reciprocal_mass, mass_carrier, mass_carrier]

theorem evaluation_bounds (gate0 gate1 : ℕ → ℕ → Prop) (d0 d1 : ℕ) (ps0 ps1 : List ℕ)
    (hnd0 : ps0.Nodup) (hnd1 : ps1.Nodup)
    (hp0 : ∀ p ∈ ps0, p.Prime) (hp1 : ∀ p ∈ ps1, p.Prime)
    (hdis : Disjoint ps0.toFinset ps1.toFinset) (n : ℕ) :
    SieveDivisorWindow.evaluation (support gate0 gate1 d0 d1 ps0 ps1)
        (lowerCoefficient gate0 gate1 d0 d1 ps0 ps1) n ≤
      SieveDivisorWindow.indicator (ps0.toFinset ∪ ps1.toFinset) n ∧
    SieveDivisorWindow.indicator (ps0.toFinset ∪ ps1.toFinset) n ≤
      SieveDivisorWindow.evaluation (support gate0 gate1 d0 d1 ps0 ps1)
        (upperCoefficient gate0 gate1 d0 d1 ps0 ps1) n := by
  rw [lower_evaluation gate0 gate1 d0 d1 ps0 ps1 hp0 hp1 hdis,
    upper_evaluation gate0 gate1 d0 d1 ps0 ps1 hp0 hp1 hdis]
  exact SieveVector.evaluation_bounds gate0 gate1 d0 d1 ps0 ps1 hnd0 hnd1 hp0 hp1 n

theorem main_remainder_bounds (gate0 gate1 : ℕ → ℕ → Prop) (d0 d1 : ℕ) (ps0 ps1 : List ℕ)
    (hnd0 : ps0.Nodup) (hnd1 : ps1.Nodup)
    (hp0 : ∀ p ∈ ps0, p.Prime) (hp1 : ∀ p ∈ ps1, p.Prime)
    (hdis : Disjoint ps0.toFinset ps1.toFinset) (L R : ℝ) (hL : 0 ≤ L) (hLR : L ≤ R) :
    (R-L) * HarmanDivisorWindow.reciprocalMass (support gate0 gate1 d0 d1 ps0 ps1)
        (lowerCoefficient gate0 gate1 d0 d1 ps0 ps1) +
      HarmanDivisorWindow.remainder (support gate0 gate1 d0 d1 ps0 ps1)
        (lowerCoefficient gate0 gate1 d0 d1 ps0 ps1) L R ≤
      ((SieveDivisorWindow.siftedWindow (ps0.toFinset ∪ ps1.toFinset) L R).card : ℝ) ∧
    ((SieveDivisorWindow.siftedWindow (ps0.toFinset ∪ ps1.toFinset) L R).card : ℝ) ≤
      (R-L) * HarmanDivisorWindow.reciprocalMass (support gate0 gate1 d0 d1 ps0 ps1)
        (upperCoefficient gate0 gate1 d0 d1 ps0 ps1) +
      HarmanDivisorWindow.remainder (support gate0 gate1 d0 d1 ps0 ps1)
        (upperCoefficient gate0 gate1 d0 d1 ps0 ps1) L R :=
  SieveDivisorWindow.main_remainder_bounds_of_pointwise _ _ _ _ _ L R
    (support_positive gate0 gate1 d0 d1 ps0 ps1 hp0 hp1)
    (support_positive gate0 gate1 d0 d1 ps0 ps1 hp0 hp1) hL hLR
    (fun n _ => evaluation_bounds gate0 gate1 d0 d1 ps0 ps1 hnd0 hnd1 hp0 hp1 hdis n)

#print axioms lowerCoefficient_abs_le_one
#print axioms main_remainder_bounds
run_cmd do
  for decl in [``support_subset_carrier, ``carrier_positive, ``carrier_representation,
      ``carriers_coprime, ``coefficient_zero_of_not_support, ``evaluation_carrier,
      ``mass_carrier, ``coefficient_pair_control, ``support_positive,
      ``lowerCoefficient_abs_le_one, ``upperCoefficient_abs_le_one,
      ``lower_evaluation, ``upper_evaluation, ``lower_reciprocal_mass,
      ``upper_reciprocal_mass, ``evaluation_bounds, ``main_remainder_bounds] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
run_cmd Lean.logInfo "SIEVE_VECTOR_CONVOLUTION_PASSED; CONSTRUCTED UNIT COEFFICIENTS; NO MAIN TERM POSITIVITY"

end SieveVectorConvolution
end
