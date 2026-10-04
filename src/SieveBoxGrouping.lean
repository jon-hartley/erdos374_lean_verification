import SieveCompleteBoxing
import FourPrimeSmallWeights

/-! Exact regrouping into Cartesian half-open prime boxes at every length.
The positive flag means the inner-even family; false means the outer-odd
family. Every ordered tuple remains present, including repeated coordinates.
No analytic estimate or main-term positivity is used. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace SieveBoxGrouping
open SieveGeometricGrid SieveBoxTuples SieveBoxedFamily SieveCompleteBoxing

def primeBand (D s z : ℝ) (i : ℕ) : Finset ℕ :=
  FourPrimeSmallWeights.band (scale D s i) (scale D s (i+1)) z

def fibre (D s z : ℝ) : List ℕ → Finset (List ℕ)
  | [] => {[]}
  | i :: g => (primeBand D s z i).biUnion (fun p => (fibre D s z g).image (List.cons p))

def profileTest (positive : Bool) (D s : ℝ) (g : List ℕ) : Prop :=
  if positive then Even g.length ∧ g.Pairwise (· > ·) ∧
    SieveBoxPrefix.accepts (D^(1/ratio s)) false 1 (g.map (scale D s))
  else ¬Even g.length ∧ g.Pairwise (· ≥ ·) ∧
    SieveBoxPrefix.accepts D false 1 (g.map (scale D s))

def profiles (positive : Bool) (D s : ℝ) : Finset (List ℕ) :=
  (boundedTuples (Finset.range (SieveGeometricGrid.cutoff s+1))
    (SieveBoxLength.cutoff s)).filter (profileTest positive D s)

def family (positive : Bool) (D s z : ℝ) : Finset (List ℕ) :=
  if positive then innerFamily D s z else outerFamily D s z

def tupleTest (positive : Bool) (D s : ℝ) (t : List ℕ) : Prop :=
  if positive then innerTest D s t else outerTest D s t

theorem mem_primeBand (D s z : ℝ) (i p : ℕ) :
    p ∈ primeBand D s z i ↔ p.Prime ∧ (p : ℝ) < z ∧ InBox D s (p : ℝ) i := by
  rw [primeBand, FourPrimeSmallWeights.mem_band]
  unfold InBox
  tauto

theorem mem_fibre (D s z : ℝ) (g t : List ℕ) :
    t ∈ fibre D s z g ↔ List.Forall₂ (fun p i => p ∈ primeBand D s z i) t g := by
  induction g generalizing t with
  | nil => cases t <;> simp [fibre]
  | cons i g ih =>
    cases t with
    | nil => simp [fibre]
    | cons p t => simp [fibre, ih, and_comm]

theorem mem_fibre_bands (D s z : ℝ) (g t : List ℕ) :
    t ∈ fibre D s z g ↔
      List.Forall₂ (fun (p i : ℕ) => p.Prime ∧ (p : ℝ) < z ∧ InBox D s (p : ℝ) i) t g := by
  rw [mem_fibre]
  simp_rw [mem_primeBand]

theorem fibre_nil (D s z : ℝ) : fibre D s z [] = {[]} := rfl

theorem mem_primeBand_iff_index (D s z : ℝ) (hD : 1 < D) (hs : 0 < s)
    (hz : z ≤ D) (i p : ℕ) :
    p ∈ primeBand D s z i ↔ p ∈ pool D s z ∧ boxIndex D s (p : ℝ) = i := by
  rw [mem_primeBand, SieveBoxedFamily.mem_pool]
  constructor
  · rintro ⟨hp, hpz, hb⟩
    have hlo : D^(s^2) ≤ (p : ℝ) := by
      have hh := (scale_strictMono D s hD hs).monotone (Nat.zero_le i)
      have hi : D^(s^2) ≤ scale D s i := by simpa only [scale_zero] using hh
      exact hi.trans hb.1
    exact ⟨⟨hp, hpz, hlo⟩, boxIndex_eq_of_inBox D s (p : ℝ) hD hs i hb⟩
  · rintro ⟨⟨hp, hpz, hlo⟩, hi⟩
    refine ⟨hp, hpz, ?_⟩
    simpa only [hi] using boxIndex_spec D s (p : ℝ) hD hs hlo (hpz.trans_le hz)

/-- The Cartesian band condition determines the actual assigned index list.
Its equivalence also proves that no large-pool restriction was lost. -/
theorem mem_fibre_iff_indices (D s z : ℝ) (hD : 1 < D) (hs : 0 < s)
    (hz : z ≤ D) (g t : List ℕ) :
    t ∈ fibre D s z g ↔ (∀ p ∈ t, p ∈ pool D s z) ∧ indices D s t = g := by
  rw [mem_fibre]
  simp_rw [mem_primeBand_iff_index D s z hD hs hz]
  rw [List.forall₂_and_left, ← List.forall₂_map_left_iff, List.forall₂_eq_eq_eq]
  rfl

theorem scales_eq_map_indices (D s : ℝ) (t : List ℕ) :
    scales D s t = (indices D s t).map (scale D s) := by
  unfold scales indices
  rw [List.map_map]
  rfl

theorem profileTest_indices (positive : Bool) (D s : ℝ) (t : List ℕ) :
    profileTest positive D s (indices D s t) ↔ tupleTest positive D s t := by
  cases positive <;>
    simp only [profileTest, tupleTest, innerTest, outerTest, Bool.false_eq_true,
      ite_false, ite_true, ← scales_eq_map_indices]
  all_goals simp only [indices, List.length_map]

theorem mem_family (positive : Bool) (D s z : ℝ) (hD : 1 < D) (hs : 0 < s)
    (t : List ℕ) :
    t ∈ family positive D s z ↔ (∀ p ∈ t, p ∈ pool D s z) ∧ tupleTest positive D s t := by
  cases positive with
  | false => exact mem_outerFamily D s z hD hs t
  | true => exact mem_innerFamily D s z hD hs t

theorem mem_profiles (positive : Bool) (D s : ℝ) (g : List ℕ) :
    g ∈ profiles positive D s ↔ g.length ≤ SieveBoxLength.cutoff s ∧
      (∀ i ∈ g, i ≤ SieveGeometricGrid.cutoff s) ∧ profileTest positive D s g := by
  simp only [profiles, Finset.mem_filter, mem_boundedTuples, Finset.mem_range,
    Nat.lt_succ_iff, and_assoc]

theorem assigned_profile_mem (positive : Bool) (D s z : ℝ)
    (hD : 1 < D) (hs : 0 < s) (hz : z ≤ D) (t : List ℕ)
    (ht : t ∈ family positive D s z) : indices D s t ∈ profiles positive D s := by
  obtain ⟨hp, htest⟩ := (mem_family positive D s z hD hs t).mp ht
  have hlen : t.length ≤ SieveBoxLength.cutoff s := by
    cases positive with
    | false => exact outerTest_length_bound D s hD hs t htest
    | true => exact innerTest_length_bound D s hD hs t htest
  exact (mem_profiles positive D s _).mpr
    ⟨by simpa only [indices, List.length_map] using hlen,
      assigned_indices_bounded D s z hD hs hz t hp,
      (profileTest_indices positive D s t).mpr htest⟩

theorem fibre_eq_filter (positive : Bool) (D s z : ℝ)
    (hD : 1 < D) (hs : 0 < s) (hz : z ≤ D) (g : List ℕ)
    (hg : g ∈ profiles positive D s) :
    fibre D s z g = (family positive D s z).filter (fun t => indices D s t = g) := by
  ext t
  rw [mem_fibre_iff_indices D s z hD hs hz, Finset.mem_filter,
    mem_family positive D s z hD hs]
  constructor
  · rintro ⟨hp, hi⟩
    refine ⟨⟨hp, (profileTest_indices positive D s t).mp ?_⟩, hi⟩
    rw [hi]
    exact ((mem_profiles positive D s g).mp hg).2.2
  · rintro ⟨⟨hp, _⟩, hi⟩
    exact ⟨hp, hi⟩

theorem mem_family_iff_unique_profile (positive : Bool) (D s z : ℝ)
    (hD : 1 < D) (hs : 0 < s) (hz : z ≤ D) (t : List ℕ) :
    t ∈ family positive D s z ↔
      ∃! g : List ℕ, g ∈ profiles positive D s ∧ t ∈ fibre D s z g := by
  constructor
  · intro ht
    have hp := ((mem_family positive D s z hD hs t).mp ht).1
    refine ⟨indices D s t, ⟨assigned_profile_mem positive D s z hD hs hz t ht,
      (mem_fibre_iff_indices D s z hD hs hz _ _).mpr ⟨hp, rfl⟩⟩, ?_⟩
    intro g hg
    exact ((mem_fibre_iff_indices D s z hD hs hz g t).mp hg.2).2.symm
  · rintro ⟨g, ⟨hg, ht⟩, _⟩
    rw [fibre_eq_filter positive D s z hD hs hz g hg] at ht
    exact (Finset.mem_filter.mp ht).1

theorem sum_grouped (positive : Bool) (D s z : ℝ)
    (hD : 1 < D) (hs : 0 < s) (hz : z ≤ D) (f : List ℕ → ℝ) :
    (∑ t ∈ family positive D s z, f t) =
      ∑ g ∈ profiles positive D s, ∑ t ∈ fibre D s z g, f t := by
  symm
  calc
    _ = ∑ g ∈ profiles positive D s,
        ∑ t ∈ (family positive D s z).filter (fun t => indices D s t = g), f t := by
      apply Finset.sum_congr rfl
      intro g hg
      rw [fibre_eq_filter positive D s z hD hs hz g hg]
    _ = _ := Finset.sum_fiberwise_of_maps_to
      (assigned_profile_mem positive D s z hD hs hz) f

theorem sum_inner_grouped (D s z : ℝ) (hD : 1 < D) (hs : 0 < s)
    (hz : z ≤ D) (f : List ℕ → ℝ) :
    (∑ t ∈ innerFamily D s z, f t) =
      ∑ g ∈ profiles true D s, ∑ t ∈ fibre D s z g, f t :=
  sum_grouped true D s z hD hs hz f

theorem sum_outer_grouped (D s z : ℝ) (hD : 1 < D) (hs : 0 < s)
    (hz : z ≤ D) (f : List ℕ → ℝ) :
    (∑ t ∈ outerFamily D s z, f t) =
      ∑ g ∈ profiles false D s, ∑ t ∈ fibre D s z g, f t :=
  sum_grouped false D s z hD hs hz f

theorem empty_mem_positive_profiles (D s : ℝ) : [] ∈ profiles true D s := by
  simp [mem_profiles, profileTest, SieveBoxPrefix.accepts]

#print axioms sum_grouped
#print axioms mem_family_iff_unique_profile
run_cmd do
  for decl in [``mem_primeBand, ``mem_fibre, ``mem_fibre_bands, ``fibre_nil,
      ``mem_primeBand_iff_index, ``mem_fibre_iff_indices, ``scales_eq_map_indices,
      ``profileTest_indices, ``mem_family, ``mem_profiles, ``assigned_profile_mem,
      ``fibre_eq_filter, ``mem_family_iff_unique_profile, ``sum_grouped,
      ``sum_inner_grouped, ``sum_outer_grouped, ``empty_mem_positive_profiles] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end SieveBoxGrouping
end
