import SieveSignedComparison
import SieveVectorConvolution
import SieveSmallWeights

/-! Actual collection of signed small-weight/tuple products. Every tuple
representation is counted, including repetitions within outer tuples.
No unit bound for aggregate tuple coefficients is asserted. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped BigOperators

namespace SieveTupleConvolution

def tupleSupport (T : Finset (List ℕ)) : Finset ℕ := T.image List.prod

def tupleCoefficient (T : Finset (List ℕ)) (m : ℕ) : ℝ :=
  ∑ _t ∈ T.filter (fun t => t.prod = m), 1

theorem mem_tupleSupport (T : Finset (List ℕ)) (m : ℕ) :
    m ∈ tupleSupport T ↔ ∃ t ∈ T, t.prod = m := Finset.mem_image

theorem tupleSupport_mono {T U : Finset (List ℕ)} (h : T ⊆ U) :
    tupleSupport T ⊆ tupleSupport U := Finset.image_subset_image h

theorem tupleCoefficient_eq_card (T : Finset (List ℕ)) (m : ℕ) :
    tupleCoefficient T m = ((T.filter (fun t => t.prod = m)).card : ℝ) := by
  simp [tupleCoefficient]

theorem tupleCoefficient_nonneg (T : Finset (List ℕ)) (m : ℕ) :
    0 ≤ tupleCoefficient T m := by
  rw [tupleCoefficient_eq_card]
  positivity

theorem tupleCoefficient_zero_off_support (T : Finset (List ℕ)) (m : ℕ)
    (hm : m ∉ tupleSupport T) : tupleCoefficient T m = 0 := by
  have hfilter : T.filter (fun t => t.prod = m) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro t ht he
    exact hm ((mem_tupleSupport T m).mpr ⟨t, ht, he⟩)
  simp only [tupleCoefficient, hfilter, Finset.sum_empty]

theorem tupleSupport_positive (T : Finset (List ℕ))
    (hp : ∀ t ∈ T, ∀ p ∈ t, 0 < p) (m : ℕ) (hm : m ∈ tupleSupport T) : 0 < m := by
  obtain ⟨t, ht, rfl⟩ := (mem_tupleSupport T m).mp hm
  exact List.prod_pos (hp t ht)

theorem tuple_kernel (T : Finset (List ℕ)) (f : ℕ → ℝ) :
    (∑ m ∈ tupleSupport T, tupleCoefficient T m * f m) = ∑ t ∈ T, f t.prod := by
  calc
    _ = ∑ t ∈ T, ∑ m ∈ tupleSupport T,
        (if t.prod = m then (1 : ℝ) else 0) * f m := by
      simp only [tupleCoefficient, Finset.sum_filter, Finset.sum_mul]
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [Finset.sum_eq_single_of_mem t.prod ((mem_tupleSupport T _).mpr ⟨t, ht, rfl⟩)]
      · simp
      · intro m hm hne
        simp [Ne.symm hne]

theorem tuple_kernel_on (T : Finset (List ℕ)) (R : Finset ℕ)
    (hR : tupleSupport T ⊆ R) (f : ℕ → ℝ) :
    (∑ m ∈ R, tupleCoefficient T m * f m) = ∑ t ∈ T, f t.prod := by
  calc
    _ = ∑ m ∈ tupleSupport T, tupleCoefficient T m * f m := by
      symm
      apply Finset.sum_subset hR
      intro m hm hnot
      rw [tupleCoefficient_zero_off_support T m hnot, zero_mul]
    _ = _ := tuple_kernel T f

theorem tuple_evaluation_on (T : Finset (List ℕ)) (R : Finset ℕ)
    (hR : tupleSupport T ⊆ R) (n : ℕ) :
    SieveDivisorWindow.evaluation R (tupleCoefficient T) n =
      SieveSignedComparison.tupleCount T n := by
  simpa only [SieveDivisorWindow.evaluation, SieveSignedComparison.tupleCount,
    SieveSignedComparison.tupleTerm, mul_ite, mul_one, mul_zero] using
    tuple_kernel_on T R hR (fun d => if d ∣ n then (1 : ℝ) else 0)

theorem tuple_reciprocal_mass_on (T : Finset (List ℕ)) (R : Finset ℕ)
    (hR : tupleSupport T ⊆ R) :
    HarmanDivisorWindow.reciprocalMass R (tupleCoefficient T) =
      ∑ t ∈ T, 1 / (t.prod : ℝ) := by
  simpa only [HarmanDivisorWindow.reciprocalMass, div_eq_mul_inv, one_mul] using
    tuple_kernel_on T R hR (fun d => (d : ℝ)⁻¹)

def tupleCarrier (I O : Finset (List ℕ)) : Finset ℕ := tupleSupport (I ∪ O)

theorem support_subset_tupleCarrier_left (I O : Finset (List ℕ)) :
    tupleSupport I ⊆ tupleCarrier I O := tupleSupport_mono Finset.subset_union_left

theorem support_subset_tupleCarrier_right (I O : Finset (List ℕ)) :
    tupleSupport O ⊆ tupleCarrier I O := tupleSupport_mono Finset.subset_union_right

def signedSupport (S : Finset ℕ) (I O : Finset (List ℕ)) : Finset ℕ :=
  FactoredDivisorWeights.support S (tupleCarrier I O)

def signedCoefficient (S : Finset ℕ) (l u : ℕ → ℝ) (I O : Finset (List ℕ)) (m : ℕ) : ℝ :=
  FactoredDivisorWeights.coefficient S (tupleCarrier I O) l (tupleCoefficient I) m -
    FactoredDivisorWeights.coefficient S (tupleCarrier I O) u (tupleCoefficient O) m

theorem convolution_tuple_kernel (S R : Finset ℕ) (w : ℕ → ℝ)
    (T : Finset (List ℕ)) (hR : tupleSupport T ⊆ R) (f : ℕ → ℝ) :
    (∑ m ∈ FactoredDivisorWeights.support S R,
      FactoredDivisorWeights.coefficient S R w (tupleCoefficient T) m * f m) =
      ∑ d ∈ S, ∑ t ∈ T, w d * f (d*t.prod) := by
  unfold FactoredDivisorWeights.support
  rw [FactoredDivisorWeights.grouped_sum S R _ w (tupleCoefficient T) f
    (HarmanDivisorWindow.productSupport_contains S R), Finset.sum_product]
  apply Finset.sum_congr rfl
  intro d hd
  calc
    _ = ∑ k ∈ R, tupleCoefficient T k * (w d * f (d*k)) := by
      apply Finset.sum_congr rfl
      intro k hk
      simp only [DirichletProductCoefficients.productIndex]
      ring
    _ = _ := tuple_kernel_on T R hR (fun k => w d * f (d*k))

/-- Full collection identity, without primality, distinctness, or injectivity. -/
theorem signed_kernel (S : Finset ℕ) (l u : ℕ → ℝ) (I O : Finset (List ℕ))
    (f : ℕ → ℝ) :
    (∑ m ∈ signedSupport S I O, signedCoefficient S l u I O m * f m) =
      (∑ d ∈ S, ∑ t ∈ I, l d * f (d*t.prod)) -
        ∑ d ∈ S, ∑ t ∈ O, u d * f (d*t.prod) := by
  simp only [signedSupport, signedCoefficient, sub_mul, Finset.sum_sub_distrib]
  rw [convolution_tuple_kernel S _ l I (support_subset_tupleCarrier_left I O),
    convolution_tuple_kernel S _ u O (support_subset_tupleCarrier_right I O)]

theorem signed_evaluation (S : Finset ℕ) (l u : ℕ → ℝ) (I O : Finset (List ℕ))
    (hc : ∀ d ∈ S, ∀ m ∈ tupleCarrier I O, d.Coprime m) (n : ℕ) :
    SieveDivisorWindow.evaluation (signedSupport S I O) (signedCoefficient S l u I O) n =
      SieveDivisorWindow.evaluation S l n * SieveSignedComparison.tupleCount I n -
        SieveDivisorWindow.evaluation S u n * SieveSignedComparison.tupleCount O n := by
  unfold signedSupport signedCoefficient
  rw [SieveVectorCollection.evaluation_sub,
    SieveVectorCollection.convolution_evaluation _ _ l _ hc,
    SieveVectorCollection.convolution_evaluation _ _ u _ hc,
    tuple_evaluation_on I _ (support_subset_tupleCarrier_left I O),
    tuple_evaluation_on O _ (support_subset_tupleCarrier_right I O)]

theorem signed_reciprocal_mass (S : Finset ℕ) (l u : ℕ → ℝ) (I O : Finset (List ℕ)) :
    HarmanDivisorWindow.reciprocalMass (signedSupport S I O) (signedCoefficient S l u I O) =
      HarmanDivisorWindow.reciprocalMass S l * (∑ t ∈ I, 1/(t.prod : ℝ)) -
        HarmanDivisorWindow.reciprocalMass S u * (∑ t ∈ O, 1/(t.prod : ℝ)) := by
  unfold signedSupport
  simp only [HarmanDivisorWindow.reciprocalMass, signedCoefficient, sub_div,
    Finset.sum_sub_distrib]
  change HarmanDivisorWindow.reciprocalMass _ (FactoredDivisorWeights.coefficient _ _ _ _) -
    HarmanDivisorWindow.reciprocalMass _ (FactoredDivisorWeights.coefficient _ _ _ _) = _
  rw [FactoredDivisorWeights.reciprocal_mass, FactoredDivisorWeights.reciprocal_mass,
    tuple_reciprocal_mass_on I _ (support_subset_tupleCarrier_left I O),
    tuple_reciprocal_mass_on O _ (support_subset_tupleCarrier_right I O)]
  rfl

theorem signedSupport_positive (S : Finset ℕ) (I O : Finset (List ℕ))
    (hS : ∀ d ∈ S, 0 < d) (hp : ∀ t ∈ I ∪ O, ∀ p ∈ t, 0 < p) :
    ∀ m ∈ signedSupport S I O, 0 < m :=
  HarmanDivisorWindow.productSupport_positive S (tupleCarrier I O) hS
    (tupleSupport_positive (I ∪ O) hp)

/-- Repetition in a large tuple does not affect coprimality with the small pool. -/
theorem carrier_coprime_tuples (gate : ℕ → ℕ → Prop) (d : ℕ) (ps : List ℕ)
    (Q : Finset ℕ) (I O : Finset (List ℕ))
    (hp : ∀ p ∈ ps, p.Prime) (hQ : ∀ q ∈ Q, q.Prime)
    (hdis : Disjoint ps.toFinset Q)
    (ht : ∀ t ∈ I ∪ O, ∀ q ∈ t, q ∈ Q) :
    ∀ m ∈ SieveVectorConvolution.carrier gate d ps,
      ∀ n ∈ tupleCarrier I O, m.Coprime n := by
  intro m hm n hn
  obtain ⟨s, hs, rfl⟩ := SieveVectorConvolution.carrier_representation gate d ps m hm
  obtain ⟨t, htT, rfl⟩ := (mem_tupleSupport (I ∪ O) n).mp hn
  apply Nat.coprime_prod_left_iff.mpr
  intro p hpS
  apply Nat.coprime_list_prod_right_iff.mpr
  intro q hqt
  apply (Nat.coprime_primes (hp p (List.mem_toFinset.mp (hs hpS))) (hQ q (ht t htT q hqt))).mpr
  intro he
  subst q
  exact Finset.disjoint_left.mp hdis (hs hpS) (ht t htT p hqt)

def selectedSupport (gate : ℕ → ℕ → Prop) (d : ℕ) (ps : List ℕ)
    (I O : Finset (List ℕ)) : Finset ℕ :=
  signedSupport (SieveVectorConvolution.carrier gate d ps) I O

def selectedCoefficient (gate : ℕ → ℕ → Prop) (d : ℕ) (ps : List ℕ)
    (I O : Finset (List ℕ)) : ℕ → ℝ :=
  signedCoefficient (SieveVectorConvolution.carrier gate d ps)
    (SieveSelectedWindow.coefficient gate false d ps)
    (SieveSelectedWindow.coefficient gate true d ps) I O

theorem selected_evaluation (gate : ℕ → ℕ → Prop) (d : ℕ) (ps : List ℕ)
    (Q : Finset ℕ) (I O : Finset (List ℕ))
    (hp : ∀ p ∈ ps, p.Prime) (hQ : ∀ q ∈ Q, q.Prime)
    (hdis : Disjoint ps.toFinset Q) (ht : ∀ t ∈ I ∪ O, ∀ q ∈ t, q ∈ Q) (n : ℕ) :
    SieveDivisorWindow.evaluation (selectedSupport gate d ps I O)
      (selectedCoefficient gate d ps I O) n =
      SieveVector.selectedEvaluation gate false d ps n * SieveSignedComparison.tupleCount I n -
        SieveVector.selectedEvaluation gate true d ps n * SieveSignedComparison.tupleCount O n := by
  unfold selectedSupport selectedCoefficient
  rw [signed_evaluation _ _ _ _ _ (carrier_coprime_tuples gate d ps Q I O hp hQ hdis ht),
    SieveVectorConvolution.evaluation_carrier, SieveVectorConvolution.evaluation_carrier]

theorem selected_reciprocal_mass (gate : ℕ → ℕ → Prop) (d : ℕ) (ps : List ℕ)
    (I O : Finset (List ℕ)) :
    HarmanDivisorWindow.reciprocalMass (selectedSupport gate d ps I O)
      (selectedCoefficient gate d ps I O) =
      HarmanDivisorWindow.reciprocalMass (SieveSelectedWindow.support gate false d ps)
        (SieveSelectedWindow.coefficient gate false d ps) * (∑ t ∈ I, 1/(t.prod : ℝ)) -
      HarmanDivisorWindow.reciprocalMass (SieveSelectedWindow.support gate true d ps)
        (SieveSelectedWindow.coefficient gate true d ps) * (∑ t ∈ O, 1/(t.prod : ℝ)) := by
  unfold selectedSupport selectedCoefficient
  rw [signed_reciprocal_mass, SieveVectorConvolution.mass_carrier,
    SieveVectorConvolution.mass_carrier]

theorem selectedSupport_positive (gate : ℕ → ℕ → Prop) (d : ℕ) (ps : List ℕ)
    (I O : Finset (List ℕ)) (hp : ∀ p ∈ ps, p.Prime)
    (ht : ∀ t ∈ I ∪ O, ∀ p ∈ t, p.Prime) :
    ∀ m ∈ selectedSupport gate d ps I O, 0 < m :=
  signedSupport_positive _ I O (SieveVectorConvolution.carrier_positive gate d ps hp)
    (fun t htT p hpt => (ht t htT p hpt).pos)

def smallSupport (T u : ℝ) (I O : Finset (List ℕ)) : Finset ℕ :=
  selectedSupport (SieveRosser.cubicGate T) 1 (SieveSmallWeights.primes u) I O

def smallCoefficient (T u : ℝ) (I O : Finset (List ℕ)) : ℕ → ℝ :=
  selectedCoefficient (SieveRosser.cubicGate T) 1 (SieveSmallWeights.primes u) I O

theorem small_evaluation (T u : ℝ) (I O : Finset (List ℕ))
    (ht : ∀ t ∈ I ∪ O, ∀ p ∈ t, p.Prime ∧ u ≤ (p : ℝ)) (n : ℕ) :
    SieveDivisorWindow.evaluation (smallSupport T u I O) (smallCoefficient T u I O) n =
      SieveDivisorWindow.evaluation (SieveSmallWeights.support T u false)
        (SieveSmallWeights.weight T u false) n * SieveSignedComparison.tupleCount I n -
      SieveDivisorWindow.evaluation (SieveSmallWeights.support T u true)
        (SieveSmallWeights.weight T u true) n * SieveSignedComparison.tupleCount O n := by
  let Q := (I ∪ O).biUnion List.toFinset
  have hQ : ∀ p ∈ Q, p.Prime := by
    intro p hp
    obtain ⟨t, htT, hpt⟩ := Finset.mem_biUnion.mp hp
    exact (ht t htT p (List.mem_toFinset.mp hpt)).1
  have hdis : Disjoint (SieveSmallWeights.primes u).toFinset Q := by
    apply Finset.disjoint_left.mpr
    intro p hp hpQ
    have hsmall := (SieveSmallWeights.mem_primes u p).mp (List.mem_toFinset.mp hp)
    obtain ⟨t, htT, hpt⟩ := Finset.mem_biUnion.mp hpQ
    exact (not_lt_of_ge (ht t htT p (List.mem_toFinset.mp hpt)).2) hsmall.2
  have htuples : ∀ t ∈ I ∪ O, ∀ p ∈ t, p ∈ Q := by
    intro t htT p hpt
    exact Finset.mem_biUnion.mpr ⟨t, htT, List.mem_toFinset.mpr hpt⟩
  exact selected_evaluation (SieveRosser.cubicGate T) 1 (SieveSmallWeights.primes u)
    Q I O (SieveSmallWeights.primes_prime u) hQ hdis htuples n

theorem small_reciprocal_mass (T u : ℝ) (I O : Finset (List ℕ)) :
    HarmanDivisorWindow.reciprocalMass (smallSupport T u I O) (smallCoefficient T u I O) =
      HarmanDivisorWindow.reciprocalMass (SieveSmallWeights.support T u false)
        (SieveSmallWeights.weight T u false) * (∑ t ∈ I, 1/(t.prod : ℝ)) -
      HarmanDivisorWindow.reciprocalMass (SieveSmallWeights.support T u true)
        (SieveSmallWeights.weight T u true) * (∑ t ∈ O, 1/(t.prod : ℝ)) :=
  selected_reciprocal_mass (SieveRosser.cubicGate T) 1 (SieveSmallWeights.primes u) I O

theorem smallSupport_positive (T u : ℝ) (I O : Finset (List ℕ))
    (ht : ∀ t ∈ I ∪ O, ∀ p ∈ t, p.Prime) :
    ∀ m ∈ smallSupport T u I O, 0 < m :=
  selectedSupport_positive (SieveRosser.cubicGate T) 1 (SieveSmallWeights.primes u) I O
    (SieveSmallWeights.primes_prime u) ht

#print axioms signed_kernel
#print axioms small_evaluation
#print axioms small_reciprocal_mass
run_cmd do
  for decl in [``mem_tupleSupport, ``tupleSupport_mono, ``tupleCoefficient_eq_card,
    ``tupleCoefficient_nonneg, ``tupleCoefficient_zero_off_support, ``tupleSupport_positive,
    ``tuple_kernel, ``tuple_kernel_on, ``tuple_evaluation_on, ``tuple_reciprocal_mass_on,
    ``support_subset_tupleCarrier_left, ``support_subset_tupleCarrier_right,
    ``convolution_tuple_kernel, ``signed_kernel, ``signed_evaluation, ``signed_reciprocal_mass,
    ``signedSupport_positive, ``carrier_coprime_tuples, ``selected_evaluation,
    ``selected_reciprocal_mass, ``selectedSupport_positive, ``small_evaluation,
    ``small_reciprocal_mass, ``smallSupport_positive] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
run_cmd Lean.logInfo "SIEVE TUPLE CONVOLUTION PASSED; MULTIPLICITIES RETAINED; NO UNIT CAP"

end SieveTupleConvolution
end
