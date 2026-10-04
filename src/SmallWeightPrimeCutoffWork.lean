import SeparatedCoreSmallGcdWork
import Mathlib.Data.List.Sort

/-! A fixed small-divisor Rosser coefficient, as the outer prime grows,
is a fixed sign on an initial segment and zero thereafter. This concerns
the small weight only; the other source masks are not separated here. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
attribute [local instance] Classical.propDecidable
namespace SmallWeightPrimeCutoffWork

theorem accepts_mono (g g' : ℕ→ℕ→Prop) (hg : ∀d p,g d p → g' d p)
    (mode : Bool) (d : ℕ) (qs : List ℕ) :
    SievePrefix.accepts g mode d qs → SievePrefix.accepts g' mode d qs := by
  induction qs generalizing mode d with
  | nil => simp [SievePrefix.accepts]
  | cons p qs ih =>
    rintro ⟨hgate,hrest⟩
    exact ⟨hgate.imp_right (hg d p),ih (!mode) (d*p) hrest⟩

theorem primes_sublist (z z' : ℝ) (hz : z≤z') :
    (SieveSmallWeights.primes z).Sublist (SieveSmallWeights.primes z') := by
  apply List.sublist_of_subperm_of_pairwise
    (List.subperm_of_subset (SieveSmallWeights.primes_nodup z) ?_)
    (SieveSmallWeights.primes_descending z) (SieveSmallWeights.primes_descending z')
  intro p hp
  obtain ⟨hpp,hpz⟩ := (SieveSmallWeights.mem_primes z p).mp hp
  exact (SieveSmallWeights.mem_primes z' p).mpr ⟨hpp,hpz.trans_le hz⟩

theorem selected_mono (T T' z z' : ℝ) (hT : T≤T') (hz : z≤z') (mode : Bool) :
    SieveRosser.selected T mode (SieveSmallWeights.primes z) ⊆
      SieveRosser.selected T' mode (SieveSmallWeights.primes z') := by
  intro f hf
  obtain ⟨qs,hsub,he,ha⟩ := (SieveRosser.mem_selected_iff _ _ _ _).mp hf
  apply (SieveRosser.mem_selected_iff _ _ _ _).mpr
  refine ⟨qs,hsub.trans (primes_sublist z z' hz),he,?_⟩
  exact accepts_mono _ _ (fun d p hp => lt_of_lt_of_le hp hT) mode 1 qs ha

theorem weight_stable_of_nonzero (T T' z z' : ℝ) (hT : T≤T') (hz : z≤z')
    (mode : Bool) (d : ℕ) (hd : SieveSmallWeights.weight T z mode d≠0) :
    SieveSmallWeights.weight T' z' mode d=SieveSmallWeights.weight T z mode d := by
  obtain ⟨f,hf,he⟩ := SievePrimeSubset.selectedCoefficient_nonzero_representation
    (SieveRosser.selected T mode (SieveSmallWeights.primes z)) d hd
  have hf' := selected_mono T T' z z' hT hz mode hf
  rw [←he]
  exact (SievePrimeSubset.selectedCoefficient_eq_sign _
    (SieveRosser.selected_primes _ _ _ (SieveSmallWeights.primes_prime z')) f hf').trans
    (SievePrimeSubset.selectedCoefficient_eq_sign _
      (SieveRosser.selected_primes _ _ _ (SieveSmallWeights.primes_prime z)) f hf).symm

theorem originalWeight_stable_downward (X s : ℝ) (hX : 0<X) (hs : 0≤s)
    (p q d : ℕ) (hp : 0<p) (hpq : p≤q) (t : List ℕ)
    (hq : LongerTupleActualProfiles.originalWeight X s true (q,d,t)≠0) :
    LongerTupleActualProfiles.originalWeight X s true (p,d,t)=
      LongerTupleActualProfiles.originalWeight X s true (q,d,t) := by
  have hpp : (0:ℝ)<p := by exact_mod_cast hp
  have hqp : (0:ℝ)<q := by exact_mod_cast (lt_of_lt_of_le hp hpq)
  have hpqR : (p:ℝ)≤q := by exact_mod_cast hpq
  have hlvl : 0≤SieveWeightedCutoffs.level X s := by
    unfold SieveWeightedCutoffs.level
    exact Real.rpow_nonneg hX.le _
  have hD : SieveWeightedCutoffs.level X s/q≤SieveWeightedCutoffs.level X s/p :=
    div_le_div_of_nonneg_left hlvl hpp hpqR
  have hD0 : 0≤SieveWeightedCutoffs.level X s/q := div_nonneg hlvl hqp.le
  have hw := weight_stable_of_nonzero _ _ _ _ (Real.rpow_le_rpow hD0 hD hs)
    (Real.rpow_le_rpow hD0 hD (sq_nonneg s)) true d
    (by simpa only [LongerTupleActualProfiles.originalWeight,Complex.ofReal_ne_zero] using hq)
  exact congrArg (fun x:ℝ => (x:ℂ)) hw

theorem originalWeight_zero_upward (X s : ℝ) (hX : 0<X) (hs : 0≤s)
    (p q d : ℕ) (hp : 0<p) (hpq : p≤q) (t : List ℕ)
    (hz : LongerTupleActualProfiles.originalWeight X s true (p,d,t)=0) :
    LongerTupleActualProfiles.originalWeight X s true (q,d,t)=0 := by
  by_contra hq
  exact hq ((originalWeight_stable_downward X s hX hs p q d hp hpq t hq).symm.trans hz)

/-- On any finite integer interval, the actual small weight is exactly
a single constant times an initial-segment indicator. -/
theorem originalWeight_interval (X s : ℝ) (hX : 0<X) (hs : 0≤s)
    (lo hi d : ℕ) (hlohi : lo≤hi) (t : List ℕ) :
    ∃cut : ℕ,lo≤cut ∧ cut≤hi ∧ ∀p∈Finset.Ioc lo hi,
      LongerTupleActualProfiles.originalWeight X s true (p,d,t) =
        if p≤cut then LongerTupleActualProfiles.originalWeight X s true (lo+1,d,t) else 0 := by
  let F := (Finset.Ioc lo hi).filter
    (fun p => LongerTupleActualProfiles.originalWeight X s true (p,d,t)≠0)
  by_cases hF : F.Nonempty
  · let cut := F.max' hF
    have hc : cut∈F := Finset.max'_mem F hF
    obtain ⟨hcI,hcn⟩ := Finset.mem_filter.mp hc
    obtain ⟨hcl,hch⟩ := Finset.mem_Ioc.mp hcI
    refine ⟨cut,hcl.le,hch,?_⟩
    intro p hp
    obtain ⟨hpl,hph⟩ := Finset.mem_Ioc.mp hp
    by_cases hpc : p≤cut
    · rw [if_pos hpc]
      have h1 := originalWeight_stable_downward X s hX hs p cut d (by omega) hpc t hcn
      have h2 := originalWeight_stable_downward X s hX hs (lo+1) cut d (by omega) (by omega) t hcn
      exact h1.trans h2.symm
    · rw [if_neg hpc]
      by_contra hn
      have hmem : p∈F := Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hpl,hph⟩,hn⟩
      exact hpc (Finset.le_max' F p hmem)
  · refine ⟨lo,le_rfl,hlohi,?_⟩
    intro p hp
    have hpl := (Finset.mem_Ioc.mp hp).1
    rw [if_neg (by omega : ¬p≤lo)]
    by_contra hn
    exact hF ⟨p,Finset.mem_filter.mpr ⟨hp,hn⟩⟩

run_cmd do
  for decl in [``accepts_mono, ``primes_sublist, ``selected_mono,
      ``weight_stable_of_nonzero, ``originalWeight_stable_downward, ``originalWeight_zero_upward,
      ``originalWeight_interval] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end SmallWeightPrimeCutoffWork
