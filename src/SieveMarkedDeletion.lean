import SieveBoxMass
import SieveStoppingTail
import Mathlib.Data.List.InsertIdx

/-! Deleting a marked coordinate from a decreasing tuple leaves one residual
prime subset. Grouping by that subset and the insertion position costs only
the number of positions. No estimate for the prime fibers is assumed here
except the explicit finite reciprocal-sum hypothesis. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open scoped BigOperators

namespace SieveMarkedDeletion

def residual (mark : List ℕ → ℕ) (t : List ℕ) : Finset ℕ :=
  (t.erase (mark t)).toFinset

def fiber (A : Finset (List ℕ)) (mark pos : List ℕ → ℕ)
    (i : ℕ) (R : Finset ℕ) : Finset ℕ :=
  (A.filter (fun t => (pos t, residual mark t) = (i, R))).image mark

theorem mem_fiber (A : Finset (List ℕ)) (mark pos : List ℕ → ℕ)
    (i : ℕ) (R : Finset ℕ) (p : ℕ) :
    p ∈ fiber A mark pos i R ↔
      ∃ t ∈ A, pos t = i ∧ residual mark t = R ∧ mark t = p := by
  classical
  simp only [fiber, Finset.mem_image, Finset.mem_filter, Prod.mk.injEq]
  constructor
  · rintro ⟨t, ⟨ht, hi, hR⟩, hp⟩
    exact ⟨t, ht, hi, hR, hp⟩
  · rintro ⟨t, ht, hi, hR, hp⟩
    exact ⟨t, ⟨ht, hi, hR⟩, hp⟩

theorem strict_nodup (t : List ℕ) (ht : t.Pairwise (· > ·)) : t.Nodup :=
  List.nodup_iff_pairwise_ne.mpr (ht.imp (fun h => ne_of_gt h))

/-- The finite residual set uniquely determines its decreasing list. -/
theorem erase_eq_of_residual_eq (mark : List ℕ → ℕ) (t v : List ℕ)
    (ht : t.Pairwise (· > ·)) (hv : v.Pairwise (· > ·))
    (hr : residual mark t = residual mark v) :
    t.erase (mark t) = v.erase (mark v) := by
  have hp := List.perm_of_nodup_nodup_toFinset_eq
    ((strict_nodup t ht).erase (mark t)) ((strict_nodup v hv).erase (mark v)) hr
  exact hp.eq_of_pairwise'
    ((ht.erase (mark t)).imp (fun h => le_of_lt h))
    ((hv.erase (mark v)).imp (fun h => le_of_lt h))

theorem tuple_eq_of_mark_residual_eq (mark : List ℕ → ℕ) (t v : List ℕ)
    (ht : t.Pairwise (· > ·)) (hv : v.Pairwise (· > ·))
    (hmt : mark t ∈ t) (hmv : mark v ∈ v)
    (hm : mark t = mark v) (hr : residual mark t = residual mark v) : t = v := by
  have he := erase_eq_of_residual_eq mark t v ht hv hr
  have hp := List.perm_cons_erase hmt
  rw [he, hm] at hp
  exact (hp.trans (List.perm_cons_erase hmv).symm).eq_of_pairwise'
    (ht.imp (fun h => le_of_lt h)) (hv.imp (fun h => le_of_lt h))

theorem weight_factor (mark : List ℕ → ℕ) (w : ℕ → ℝ) (t : List ℕ)
    (ht : t.Nodup) (hm : mark t ∈ t) :
    (t.map w).prod = w (mark t) * ∏ p ∈ residual mark t, w p := by
  rw [residual, List.prod_toFinset w (ht.erase (mark t))]
  simpa only [List.map_cons, List.prod_cons] using
    ((List.perm_cons_erase hm).map w).prod_eq

theorem fiber_mass (A : Finset (List ℕ)) (mark pos : List ℕ → ℕ)
    (w : ℕ → ℝ) (i : ℕ) (R : Finset ℕ)
    (hstrict : ∀ t ∈ A, t.Pairwise (· > ·))
    (hmark : ∀ t ∈ A, mark t ∈ t) :
    (∑ t ∈ A.filter (fun t => (pos t, residual mark t) = (i, R)),
      (t.map w).prod) =
        (∑ p ∈ fiber A mark pos i R, w p) * ∏ p ∈ R, w p := by
  classical
  have hinj : Set.InjOn mark
      (↑(A.filter (fun t => (pos t, residual mark t) = (i, R))) : Set (List ℕ)) := by
    intro t ht v hv hm
    obtain ⟨ht, htr⟩ := Finset.mem_filter.mp ht
    obtain ⟨hv, hvr⟩ := Finset.mem_filter.mp hv
    exact tuple_eq_of_mark_residual_eq mark t v (hstrict t ht) (hstrict v hv)
      (hmark t ht) (hmark v hv) hm
      ((congrArg Prod.snd htr).trans (congrArg Prod.snd hvr).symm)
  rw [fiber, Finset.sum_image hinj, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro t ht
  obtain ⟨ht, htr⟩ := Finset.mem_filter.mp ht
  have hR : residual mark t = R := congrArg Prod.snd htr
  rw [weight_factor mark w t (strict_nodup t (hstrict t ht)) (hmark t ht), hR]

/-- A marked-coordinate bound with arbitrary nonnegative prime weights.
The position is a bounded grouping label; applications also identify it as
the actual marked coordinate, using `take_eq_of_residual_eq` below. -/
theorem weighted_mass_le (A : Finset (List ℕ)) (P : Finset ℕ)
    (mark pos : List ℕ → ℕ) (L : ℕ) (w : ℕ → ℝ) (δ : ℝ)
    (hstrict : ∀ t ∈ A, t.Pairwise (· > ·))
    (hpool : ∀ t ∈ A, ∀ p ∈ t, p ∈ P)
    (hmark : ∀ t ∈ A, mark t ∈ t)
    (hpos : ∀ t ∈ A, pos t < L)
    (hw : ∀ p ∈ P, 0 ≤ w p)
    (hfiber : ∀ i < L, ∀ R ⊆ P, ∑ p ∈ fiber A mark pos i R, w p ≤ δ) :
    (∑ t ∈ A, (t.map w).prod) ≤
      (L : ℝ) * δ * ∏ p ∈ P, (1 + w p) := by
  classical
  have hmaps : ∀ t ∈ A,
      (pos t, residual mark t) ∈ (Finset.range L).product P.powerset := by
    intro t ht
    refine Finset.mem_product.mpr ⟨Finset.mem_range.mpr (hpos t ht), ?_⟩
    apply Finset.mem_powerset.mpr
    intro p hp
    exact hpool t ht p (List.mem_of_mem_erase (List.mem_toFinset.mp hp))
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun t => (t.map w).prod)]
  calc
    _ = ∑ k ∈ (Finset.range L).product P.powerset,
        (∑ p ∈ fiber A mark pos k.1 k.2, w p) * ∏ p ∈ k.2, w p := by
      apply Finset.sum_congr rfl
      intro k _
      exact fiber_mass A mark pos w k.1 k.2 hstrict hmark
    _ ≤ ∑ k ∈ (Finset.range L).product P.powerset,
        δ * ∏ p ∈ k.2, w p := by
      apply Finset.sum_le_sum
      intro k hk
      obtain ⟨hi, hR⟩ := Finset.mem_product.mp hk
      have hsub := Finset.mem_powerset.mp hR
      exact mul_le_mul_of_nonneg_right (hfiber k.1 (Finset.mem_range.mp hi) k.2 hsub)
        (Finset.prod_nonneg (fun p hp => hw p (hsub hp)))
    _ = ∑ i ∈ Finset.range L, ∑ R ∈ P.powerset, δ * ∏ p ∈ R, w p :=
      Finset.sum_product (Finset.range L) P.powerset
        (fun k : ℕ × Finset ℕ => δ * ∏ p ∈ k.2, w p)
    _ = (L : ℝ) * δ * ∏ p ∈ P, (1 + w p) := by
      simp_rw [← Finset.mul_sum, ← Finset.prod_one_add]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring

theorem reciprocal_mass_le (A : Finset (List ℕ)) (P : Finset ℕ)
    (mark pos : List ℕ → ℕ) (L : ℕ) (δ : ℝ)
    (hstrict : ∀ t ∈ A, t.Pairwise (· > ·))
    (hpool : ∀ t ∈ A, ∀ p ∈ t, p ∈ P)
    (hmark : ∀ t ∈ A, mark t ∈ t)
    (hpos : ∀ t ∈ A, pos t < L)
    (hfiber : ∀ i < L, ∀ R ⊆ P,
      ∑ p ∈ fiber A mark pos i R, (p : ℝ)⁻¹ ≤ δ) :
    (∑ t ∈ A, SieveBoxMass.reciprocal t) ≤
      (L : ℝ) * δ * ∏ p ∈ P, (1 + (p : ℝ)⁻¹) := by
  simpa only [SieveStoppingExpansion.reciprocal_product, SieveBoxMass.reciprocal]
    using weighted_mass_le A P mark pos L (fun p => (p : ℝ)⁻¹) δ
      hstrict hpool hmark hpos (fun p _ => inv_nonneg.mpr (Nat.cast_nonneg p)) hfiber

/-- Keeping the deletion position fixes the entire preceding prime prefix. -/
theorem take_eq_of_residual_eq (mark : List ℕ → ℕ) (t v : List ℕ) (i : ℕ)
    (ht : t.Pairwise (· > ·)) (hv : v.Pairwise (· > ·))
    (hit : i < t.length) (hiv : i < v.length)
    (hmt : mark t = t[i]) (hmv : mark v = v[i])
    (hr : residual mark t = residual mark v) : t.take i = v.take i := by
  have he := erase_eq_of_residual_eq mark t v ht hv hr
  rw [hmt, hmv, (strict_nodup t ht).erase_getElem i hit,
    (strict_nodup v hv).erase_getElem i hiv] at he
  calc
    t.take i = (t.eraseIdx i).take i :=
      (List.take_eraseIdx_eq_take_of_le t i i (le_refl i)).symm
    _ = (v.eraseIdx i).take i := congrArg (fun l => l.take i) he
    _ = v.take i := List.take_eraseIdx_eq_take_of_le v i i (le_refl i)

run_cmd do
  for decl in [``mem_fiber, ``strict_nodup, ``erase_eq_of_residual_eq,
    ``tuple_eq_of_mark_residual_eq, ``weight_factor, ``fiber_mass,
    ``weighted_mass_le, ``reciprocal_mass_le, ``take_eq_of_residual_eq] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "MARKED DELETION BOUND WITH ONE RESIDUAL PRIME SUBSET"

end SieveMarkedDeletion
end
