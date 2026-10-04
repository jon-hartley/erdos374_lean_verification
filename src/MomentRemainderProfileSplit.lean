import SieveBoxGrouping
import SieveUpperBoxWindow

/-! Exact arbitrary-length Cartesian splitting of actual box profiles.
Product collisions and repeated primes are retained as convolution weights.
The identities do not assume or assert analytic factor-size conditions. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace MomentRemainderProfileSplit
open SieveBoxGrouping SieveTupleConvolution

theorem fibre_append (D s z : ℝ) (g h : List ℕ) :
    fibre D s z (g++h) = ((fibre D s z g) ×ˢ (fibre D s z h)).image
      (fun a => a.1++a.2) := by
  ext t
  constructor
  · intro ht
    have hh := (mem_fibre D s z (g++h) t).mp ht
    refine Finset.mem_image.mpr ⟨(t.take g.length,t.drop g.length),?_,List.take_append_drop _ _⟩
    exact Finset.mem_product.mpr
      ⟨(mem_fibre D s z g _).mpr (List.forall₂_take_append t g h hh),
        (mem_fibre D s z h _).mpr (List.forall₂_drop_append t g h hh)⟩
  · rintro ht
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨ha,hb⟩ := Finset.mem_product.mp ha
    exact (mem_fibre D s z (g++h) _).mpr
      (List.rel_append ((mem_fibre D s z g _).mp ha) ((mem_fibre D s z h _).mp hb))

theorem append_injective_on_fibres (D s z : ℝ) (g h : List ℕ) :
    Set.InjOn (fun a : List ℕ × List ℕ => a.1++a.2)
      (↑((fibre D s z g) ×ˢ (fibre D s z h)) : Set (List ℕ × List ℕ)) := by
  intro a ha b hb he
  have ha' := ((mem_fibre D s z g a.1).mp (Finset.mem_product.mp ha).1).length_eq
  have hb' := ((mem_fibre D s z g b.1).mp (Finset.mem_product.mp hb).1).length_eq
  exact Prod.ext (List.append_inj_left he (ha'.trans hb'.symm))
    (List.append_inj_right he (ha'.trans hb'.symm))

theorem fibre_sum_append (D s z : ℝ) (g h : List ℕ) (f : ℕ→ℝ) :
    (∑t∈fibre D s z (g++h), f t.prod) =
      ∑u∈fibre D s z g, ∑v∈fibre D s z h, f (u.prod*v.prod) := by
  rw [fibre_append, Finset.sum_image (append_injective_on_fibres D s z g h), Finset.sum_product]
  simp only [List.prod_append]

def leftSupport (S : Finset ℕ) (D s z : ℝ) (g : List ℕ) : Finset ℕ :=
  FactoredDivisorWeights.support S (tupleSupport (fibre D s z g))

def leftCoefficient (S : Finset ℕ) (w : ℕ→ℝ) (D s z : ℝ) (g : List ℕ) : ℕ→ℝ :=
  FactoredDivisorWeights.coefficient S (tupleSupport (fibre D s z g)) w
    (tupleCoefficient (fibre D s z g))

def splitSupport (S : Finset ℕ) (D s z : ℝ) (g h : List ℕ) : Finset ℕ :=
  FactoredDivisorWeights.support (leftSupport S D s z g) (tupleSupport (fibre D s z h))

def splitCoefficient (S : Finset ℕ) (w : ℕ→ℝ) (D s z : ℝ) (g h : List ℕ) : ℕ→ℝ :=
  FactoredDivisorWeights.coefficient (leftSupport S D s z g) (tupleSupport (fibre D s z h))
    (leftCoefficient S w D s z g) (tupleCoefficient (fibre D s z h))

theorem split_kernel (S : Finset ℕ) (w : ℕ→ℝ) (D s z : ℝ)
    (g h : List ℕ) (f : ℕ→ℝ) :
    (∑m∈splitSupport S D s z g h, splitCoefficient S w D s z g h m*f m) =
      ∑d∈S, ∑t∈fibre D s z (g++h), w d*f (d*t.prod) := by
  rw [splitSupport,splitCoefficient,convolution_tuple_kernel _ _ _ _ (Finset.Subset.refl _)]
  rw [Finset.sum_comm]
  have hh : (∑v∈fibre D s z h, ∑a∈leftSupport S D s z g,
      leftCoefficient S w D s z g a*f (a*v.prod)) =
      ∑v∈fibre D s z h, ∑d∈S, ∑u∈fibre D s z g, w d*f (d*u.prod*v.prod) := by
    apply Finset.sum_congr rfl
    intro v _
    exact convolution_tuple_kernel S _ w _ (Finset.Subset.refl _) (fun a => f (a*v.prod))
  rw [hh,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  rw [Finset.sum_comm, fibre_sum_append D s z g h (fun a => w d*f (d*a))]
  simp only [mul_assoc]

theorem split_remainder (S : Finset ℕ) (w : ℕ→ℝ) (D s z : ℝ)
    (g h : List ℕ) (L R : ℝ) :
    HarmanDivisorWindow.remainder (splitSupport S D s z g h)
      (splitCoefficient S w D s z g h) L R =
    HarmanDivisorWindow.remainder
      (FactoredDivisorWeights.support S (tupleSupport (fibre D s z (g++h))))
      (FactoredDivisorWeights.coefficient S (tupleSupport (fibre D s z (g++h)))
        w (tupleCoefficient (fibre D s z (g++h)))) L R := by
  simp only [HarmanDivisorWindow.remainder_eq_sum]
  rw [split_kernel, convolution_tuple_kernel _ _ _ _ (Finset.Subset.refl _)]

theorem family_kernel_split (positive : Bool) (D s z : ℝ) (hD : 1<D) (hs : 0<s)
    (hz : z≤D) (S : Finset ℕ) (w : ℕ→ℝ) (cut : List ℕ→ℕ) (f : ℕ→ℝ) :
    (∑d∈S, ∑t∈family positive D s z, w d*f (d*t.prod)) =
      ∑g∈profiles positive D s,
        ∑m∈splitSupport S D s z (g.take (cut g)) (g.drop (cut g)),
          splitCoefficient S w D s z (g.take (cut g)) (g.drop (cut g)) m*f m := by
  simp_rw [split_kernel, List.take_append_drop]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  exact sum_grouped positive D s z hD hs hz (fun t => w d*f (d*t.prod))

theorem lower_boxed_kernel_split (D s z : ℝ) (hD : 1<D) (hs : 0<s) (hz : z≤D)
    (cut : List ℕ→ℕ) (f : ℕ→ℝ) :
    (∑m∈SieveBoxedWindow.support D s z, SieveBoxedWindow.coefficient D s z m*f m) =
      (∑g∈profiles true D s,
        ∑m∈splitSupport (SieveUpperBoxWindow.smallCarrier D s) D s z
          (g.take (cut g)) (g.drop (cut g)),
        splitCoefficient (SieveUpperBoxWindow.smallCarrier D s)
          (SieveSmallWeights.weight (D^s) (D^(s^2)) false) D s z
          (g.take (cut g)) (g.drop (cut g)) m*f m) -
      ∑g∈profiles false D s,
        ∑m∈splitSupport (SieveUpperBoxWindow.smallCarrier D s) D s z
          (g.take (cut g)) (g.drop (cut g)),
        splitCoefficient (SieveUpperBoxWindow.smallCarrier D s)
          (SieveSmallWeights.weight (D^s) (D^(s^2)) true) D s z
          (g.take (cut g)) (g.drop (cut g)) m*f m := by
  rw [SieveBoxedWindow.literal_kernel]
  exact congrArg₂ (fun a b : ℝ => a-b)
    (family_kernel_split true D s z hD hs hz (SieveUpperBoxWindow.smallCarrier D s)
      (SieveSmallWeights.weight (D^s) (D^(s^2)) false) cut f)
    (family_kernel_split false D s z hD hs hz (SieveUpperBoxWindow.smallCarrier D s)
      (SieveSmallWeights.weight (D^s) (D^(s^2)) true) cut f)

def profileRemainder (D s z : ℝ) (upper : Bool) (cut : List ℕ→ℕ)
    (g : List ℕ) (L R : ℝ) : ℝ :=
  HarmanDivisorWindow.remainder
    (splitSupport (SieveUpperBoxWindow.smallCarrier D s) D s z
      (g.take (cut g)) (g.drop (cut g)))
    (splitCoefficient (SieveUpperBoxWindow.smallCarrier D s)
      (SieveSmallWeights.weight (D^s) (D^(s^2)) upper) D s z
      (g.take (cut g)) (g.drop (cut g))) L R

theorem source_remainder_split (D s z : ℝ) (hD : 1<D) (hs : 0<s) (hz : z≤D)
    (cut : List ℕ→ℕ) (L R : ℝ) :
    SieveBoxedWindow.sourceRemainder D s z L R =
      (∑g∈profiles false D s, profileRemainder D s z true cut g L R) -
      ∑g∈profiles true D s, profileRemainder D s z false cut g L R := by
  simp only [SieveBoxedWindow.sourceRemainder, profileRemainder,
    HarmanDivisorWindow.remainder_eq_sum]
  rw [lower_boxed_kernel_split D s z hD hs hz cut]
  ring

theorem profiles_card_le (positive : Bool) (D s : ℝ) :
    (profiles positive D s).card≤
      (SieveBoxedFamily.boundedTuples (Finset.range (SieveGeometricGrid.cutoff s+1))
        (SieveBoxLength.cutoff s)).card := Finset.card_filter_le _ _

run_cmd do
  for decl in [``fibre_append, ``append_injective_on_fibres, ``fibre_sum_append,
      ``split_kernel, ``split_remainder, ``family_kernel_split,
      ``lower_boxed_kernel_split, ``source_remainder_split, ``profiles_card_le] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ACTUAL ALL-LENGTH CARTESIAN PROFILE FACTORIZATION PASSED"

end MomentRemainderProfileSplit
