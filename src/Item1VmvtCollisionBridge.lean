import Item1VmvtDefs
import Item1ProductPrefixMoment
import Item1DifferenceBoxMajorant

/-! Exact count bridges to the retained VMVT counting object.
Injectivity is required when an indexed family is replaced by its image set;
all ordered tuple multiplicities are otherwise retained. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open scoped BigOperators

namespace Item1VmvtCollisionBridge
open Item1PolynomialMomentIdentity Item1TupleCollisionCounting
open Item1ProductPrefixMoment Item1DifferenceBoxMajorant

/-- Coordinates 0,...,d-1 encode precisely the power equations 1,...,d. -/
theorem tupleFrequency_eq_iff_powerSumEq {ι : Type*} (d r : ℕ) (w : ι → ℤ)
    (p q : Fin r → ι) :
    tupleFrequency (powerFrequency d w) p = tupleFrequency (powerFrequency d w) q ↔
      Salt.Vmvt.PowerSumEq d r (w ∘ p) (w ∘ q) := by
  constructor
  · intro h j hj
    have hj' := Finset.mem_Icc.mp hj
    have hjlt : j-1 < d := by omega
    have he := congrFun h (⟨j-1, hjlt⟩ : Fin d)
    have heq : j-1+1 = j := by omega
    simpa only [tupleFrequency, Finset.sum_apply, powerFrequency, heq,
      Function.comp_apply] using he
  · intro h
    funext j
    have he := h (j.val+1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
    simpa only [tupleFrequency, Finset.sum_apply, powerFrequency,
      Function.comp_apply] using he

/-- An injective indexed integer family gives exactly the VMVT count on
its finite image. The bijection is on ordered tuple pairs, not on frequencies. -/
theorem ordered_collisions_eq_Jk_image {ι : Type*} [Fintype ι]
    (d r : ℕ) (w : ι → ℤ) (hw : Function.Injective w) :
    (∑ p : Fin r → ι, ∑ q : Fin r → ι,
      if tupleFrequency (powerFrequency d w) p = tupleFrequency (powerFrequency d w) q
      then (1:ℝ) else 0) = (Salt.Vmvt.Jk d r (Finset.univ.image w):ℝ) := by
  classical
  let S : Finset ((Fin r → ι) × (Fin r → ι)) := Finset.univ.filter
    (fun pq => tupleFrequency (powerFrequency d w) pq.1 =
      tupleFrequency (powerFrequency d w) pq.2)
  let F : ((Fin r → ι) × (Fin r → ι)) → ((Fin r → ℤ) × (Fin r → ℤ)) :=
    fun pq => (w ∘ pq.1, w ∘ pq.2)
  have hF : Function.Injective F := by
    intro pq pq' he
    apply Prod.ext
    · funext j
      apply hw
      exact congrFun (congrArg Prod.fst he) j
    · funext j
      apply hw
      exact congrFun (congrArg Prod.snd he) j
  have himage : S.image F = Salt.Vmvt.solSet d r (Finset.univ.image w) := by
    ext pq
    constructor
    · intro hpq
      obtain ⟨ab, hab, rfl⟩ := Finset.mem_image.mp hpq
      have he := (Finset.mem_filter.mp hab).2
      apply Salt.Vmvt.mem_solSet.mpr
      refine ⟨?_, ?_, ?_⟩
      · intro j
        exact Finset.mem_image.mpr ⟨ab.1 j, Finset.mem_univ _, rfl⟩
      · intro j
        exact Finset.mem_image.mpr ⟨ab.2 j, Finset.mem_univ _, rfl⟩
      · exact (tupleFrequency_eq_iff_powerSumEq d r w ab.1 ab.2).mp he
    · intro hpq
      obtain ⟨hp, hq, he⟩ := Salt.Vmvt.mem_solSet.mp hpq
      have hp' : ∀ j : Fin r, ∃ a : ι, w a = pq.1 j := by
        intro j
        obtain ⟨a, ha, haw⟩ := Finset.mem_image.mp (hp j)
        exact ⟨a, haw⟩
      have hq' : ∀ j : Fin r, ∃ a : ι, w a = pq.2 j := by
        intro j
        obtain ⟨a, ha, haw⟩ := Finset.mem_image.mp (hq j)
        exact ⟨a, haw⟩
      choose p hpw using hp'
      choose q hqw using hq'
      have hmap : F (p,q) = pq := by
        apply Prod.ext
        · funext j
          exact hpw j
        · funext j
          exact hqw j
      apply Finset.mem_image.mpr
      refine ⟨(p,q), ?_, hmap⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      apply (tupleFrequency_eq_iff_powerSumEq d r w p q).mpr
      rw [show w ∘ p = pq.1 from funext hpw, show w ∘ q = pq.2 from funext hqw]
      exact he
  have hcard : S.card = (Salt.Vmvt.solSet d r (Finset.univ.image w)).card := by
    rw [← himage, Finset.card_image_of_injective S hF]
  calc
    _ = ∑ pq : (Fin r → ι) × (Fin r → ι),
        if tupleFrequency (powerFrequency d w) pq.1 = tupleFrequency (powerFrequency d w) pq.2
        then (1:ℝ) else 0 := (Fintype.sum_prod_type _).symm
    _ = (S.card:ℝ) := by simp only [S, Finset.sum_boole]
    _ = _ := by exact_mod_cast hcard

/-- Squared frequency multiplicities equal the same genuine VMVT count. -/
theorem sum_multiplicity_sq_eq_Jk_image {ι : Type*} [Fintype ι]
    (d r : ℕ) (w : ι → ℤ) (hw : Function.Injective w) :
    (∑ c ∈ frequencyImage
      (tupleFrequency (r := r) (powerFrequency d w) : (Fin r → ι) → (Fin d → ℤ)),
      (fiberMultiplicity (tupleFrequency (r := r) (powerFrequency d w)) c:ℝ)^2) =
      (Salt.Vmvt.Jk d r (Finset.univ.image w):ℝ) := by
  rw [← collisions_eq_sum_multiplicity_sq]
  exact ordered_collisions_eq_Jk_image d r w hw

/-- The first exact collision factor is Jk on the integer interval 1,...,A. -/
theorem firstCollision_eq_JkI (d r A : ℕ) :
    J d r A = (Salt.Vmvt.JkI d r A:ℝ) := by
  classical
  have hw : Function.Injective (fun a : Fin A => (a.val:ℤ)+1) := by
    intro a b h
    apply Fin.ext
    have hv : (a.val:ℤ) = (b.val:ℤ) := add_right_cancel h
    exact_mod_cast hv
  have himage : Finset.univ.image (fun a : Fin A => (a.val:ℤ)+1) =
      Finset.Ioc (0:ℤ) (A:ℤ) := by
    ext z
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_Ioc]
    constructor
    · rintro ⟨a, rfl⟩
      constructor <;> omega
    · intro hz
      have hzNat : (z.toNat:ℤ) = z := Int.toNat_of_nonneg (le_of_lt hz.1)
      refine ⟨⟨z.toNat-1, by omega⟩, ?_⟩
      dsimp
      omega
  have h := sum_multiplicity_sq_eq_Jk_image d r
    (fun a : Fin A => (a.val:ℤ)+1) hw
  simpa only [J, productTupleFrequency, himage, Salt.Vmvt.JkI] using h

/-- A finite natural-number set has its exact second collision count on
the integer-cast image. The subtype inclusion is injective. -/
theorem secondCollisionCount_eq_Jk_natImage (B : Finset ℕ) (d s : ℕ) :
    secondCollisionCount d s (fun b : B => (b.val:ℤ)) =
      (Salt.Vmvt.Jk d s (B.image (fun b : ℕ => (b:ℤ))):ℝ) := by
  classical
  have hw : Function.Injective (fun b : B => (b.val:ℤ)) := by
    intro b c h
    apply Subtype.ext
    exact_mod_cast (show (b.val:ℤ) = (c.val:ℤ) from h)
  have himage : Finset.univ.image (fun b : B => (b.val:ℤ)) =
      B.image (fun b : ℕ => (b:ℤ)) := by
    ext z
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨b, rfl⟩
      exact ⟨b.val, b.property, rfl⟩
    · rintro ⟨b, hb, rfl⟩
      exact ⟨⟨b,hb⟩, rfl⟩
  have h := sum_multiplicity_sq_eq_Jk_image d s (fun b : B => (b.val:ℤ)) hw
  simpa only [secondCollisionCount, himage] using h

/-- Positive inputs bounded by Bmax embed directly into the standard interval. -/
theorem secondCollisionCount_le_JkI_of_positive (B : Finset ℕ) (d s Bmax : ℕ)
    (hpos : ∀ b ∈ B, 1 ≤ b) (hmax : ∀ b ∈ B, b ≤ Bmax) :
    secondCollisionCount d s (fun b : B => (b.val:ℤ)) ≤
      (Salt.Vmvt.JkI d s Bmax:ℝ) := by
  have hsubset : B.image (fun b : ℕ => (b:ℤ)) ⊆ Finset.Ioc (0:ℤ) (Bmax:ℤ) := by
    intro z hz
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hz
    apply Finset.mem_Ioc.mpr
    constructor
    · exact_mod_cast (show 0 < b by have := hpos b hb; omega)
    · exact_mod_cast hmax b hb
  rw [secondCollisionCount_eq_Jk_natImage]
  exact_mod_cast Salt.Vmvt.Jk_mono (k := d) (b := s) hsubset

/-- If zero is allowed, translate by one before using the standard interval.
This retains the original count exactly and enlarges only the upper endpoint. -/
theorem secondCollisionCount_le_JkI_succ (B : Finset ℕ) (d s Bmax : ℕ)
    (hmax : ∀ b ∈ B, b ≤ Bmax) :
    secondCollisionCount d s (fun b : B => (b.val:ℤ)) ≤
      (Salt.Vmvt.JkI d s (Bmax+1):ℝ) := by
  let S := B.image (fun b : ℕ => (b:ℤ))
  have hsubset : S.image (fun z => z+1) ⊆ Finset.Ioc (0:ℤ) ((Bmax+1:ℕ):ℤ) := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
    apply Finset.mem_Ioc.mpr
    have hbmax := hmax b hb
    constructor <;> omega
  have h := Salt.Vmvt.Jk_mono (k := d) (b := s) hsubset
  rw [Salt.Vmvt.Jk_image_add] at h
  rw [secondCollisionCount_eq_Jk_natImage]
  exact_mod_cast h

end Item1VmvtCollisionBridge

run_cmd do
  for target in [``Item1VmvtCollisionBridge.tupleFrequency_eq_iff_powerSumEq,
      ``Item1VmvtCollisionBridge.ordered_collisions_eq_Jk_image,
      ``Item1VmvtCollisionBridge.sum_multiplicity_sq_eq_Jk_image,
      ``Item1VmvtCollisionBridge.firstCollision_eq_JkI,
      ``Item1VmvtCollisionBridge.secondCollisionCount_eq_Jk_natImage,
      ``Item1VmvtCollisionBridge.secondCollisionCount_le_JkI_of_positive,
      ``Item1VmvtCollisionBridge.secondCollisionCount_le_JkI_succ] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "VMVT COLLISION BRIDGE: 7 standard-axiom theorem guards passed."
