import OuterLocalizedGeometryWork
import OuterActiveBlockCountWork

/-! Exact nonduplicating rectangular block partition. Each factor has its
own dyadic membership condition; the selected label set carries the joint
product geometry and is independent of all Fourier frequencies. -/
set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace OuterRectangularBlocksWork
open OuterActiveDyadicWork OuterSourceReindexWork OuterSmoothErrorSupportWork
open OuterBoundaryExtensionWork LongerTupleEncoding PositiveSharpBoxedCount

def blockSource (X : ℝ) (k : BlockKey) : Finset Representation :=
  (ambient X).filter (fun r => blockKey r=k)

theorem block_subset_localized (X s : ℝ) (i j : ℕ) (k : BlockKey)
    (hk : k ∈ activeKeys X s i j) : blockSource X k ⊆ localizedSource X s i j := by
  intro r hr
  obtain ⟨hr,he⟩ := Finset.mem_filter.mp hr
  exact Finset.mem_filter.mpr ⟨hr,he ▸ hk⟩

theorem localized_sum_blocks {E : Type*} [AddCommMonoid E] (X s : ℝ) (i j : ℕ)
    (f : Representation → E) :
    (∑r∈localizedSource X s i j,f r) = ∑k∈activeKeys X s i j,∑r∈blockSource X k,f r := by
  exact (Finset.sum_fiberwise_eq_sum_filter (ambient X) (activeKeys X s i j) blockKey f).symm

theorem rebuild_mem_ambient (X : ℝ) (u : Slice) (p : ℕ) :
    rebuild u p ∈ ambient X ↔ u ∈ candidateSlices X ∧ p ∈ largePrimes X := by
  constructor
  · intro hr
    obtain ⟨v,hv,hr⟩ := Finset.mem_biUnion.mp hr
    obtain ⟨q,hq,he⟩ := Finset.mem_image.mp hr
    have hu : v=u := by simpa only [drop_rebuild] using congrArg drop he
    have hp : q=p := congrArg Prod.fst he
    exact ⟨hu ▸ hv,hp ▸ hq⟩
  · rintro ⟨hu,hp⟩
    exact Finset.mem_biUnion.mpr ⟨u,hu,Finset.mem_image.mpr ⟨p,hp,rfl⟩⟩

theorem block_rectangular (X : ℝ) (k : BlockKey) (p d a b : ℕ) :
    (p,d,[a,b]) ∈ blockSource X k ↔
      p ∈ largePrimes X ∧ p.log2=k.1 ∧
      d ∈ Finset.Ioc 0 ⌊X^(1/1000:ℝ)⌋₊ ∧ d.log2=k.2.1 ∧
      a ∈ Finset.Ioc 0 ⌊X^(31/125:ℝ)⌋₊ ∧ a.log2=k.2.2.1 ∧
      b ∈ Finset.Ioc 0 ⌊X^(31/125:ℝ)⌋₊ ∧ b.log2=k.2.2.2 := by
  change rebuild (d,a,b) p ∈ (ambient X).filter (fun r => blockKey r=k) ↔ _
  rw [Finset.mem_filter,rebuild_mem_ambient]
  rcases k with ⟨kp,kd,ka,kb⟩
  simp only [blockKey,drop_rebuild,rebuild,candidateSlices,Finset.mem_product,Prod.mk.injEq]
  tauto

run_cmd do
  for decl in [``block_subset_localized, ``localized_sum_blocks, ``rebuild_mem_ambient,
      ``block_rectangular] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end OuterRectangularBlocksWork
