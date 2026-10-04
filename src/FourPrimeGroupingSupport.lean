import FourPrimeGroupingCoefficients

/-! Exact support properties inherited from the independent input supports.
The sixteen-fold ratio concerns the grouped image, without selecting one
representation as its coefficient. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped BigOperators

namespace FourPrimeGrouping

theorem mem_support_iff (S0 S1 S2 S3 : Finset ℕ) (m : ℕ) :
    m ∈ support S0 S1 S2 S3 ↔
      ∃ ν ∈ S0, ∃ p1 ∈ S1, ∃ p2 ∈ S2, ∃ p3 ∈ S3,
        ν * p1 * p2 * p3 = m := by
  constructor
  · intro hm
    obtain ⟨f, hf, hfm⟩ := Finset.mem_image.mp hm
    obtain ⟨h01, h23⟩ := Finset.mem_product.mp hf
    obtain ⟨h0, h1⟩ := Finset.mem_product.mp h01
    obtain ⟨h2, h3⟩ := Finset.mem_product.mp h23
    exact ⟨f.1.1, h0, f.1.2, h1, f.2.1, h2, f.2.2, h3, hfm⟩
  · rintro ⟨ν, hν, p1, h1, p2, h2, p3, h3, rfl⟩
    exact support_contains S0 S1 S2 S3 ((ν, p1), (p2, p3))
      (Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨hν, h1⟩,
        Finset.mem_product.mpr ⟨h2, h3⟩⟩)

theorem support_forall (S0 S1 S2 S3 : Finset ℕ) (P : ℕ → Prop)
    (h : ∀ ν ∈ S0, ∀ p1 ∈ S1, ∀ p2 ∈ S2, ∀ p3 ∈ S3,
      P (ν * p1 * p2 * p3)) :
    ∀ m ∈ support S0 S1 S2 S3, P m := by
  intro m hm
  obtain ⟨ν, hν, p1, h1, p2, h2, p3, h3, rfl⟩ :=
    (mem_support_iff S0 S1 S2 S3 m).mp hm
  exact h ν hν p1 h1 p2 h2 p3 h3

theorem support_cross_forall (S0 S1 S2 S3 S4 : Finset ℕ) (P : ℕ → ℕ → Prop)
    (h : ∀ ν ∈ S0, ∀ p1 ∈ S1, ∀ p2 ∈ S2, ∀ p3 ∈ S3, ∀ p4 ∈ S4,
      P (ν * p1 * p2 * p3) p4) :
    ∀ m ∈ support S0 S1 S2 S3, ∀ n ∈ S4, P m n := by
  exact support_forall S0 S1 S2 S3 (fun m => ∀ n ∈ S4, P m n) h

theorem support_two_le (S0 S1 S2 S3 : Finset ℕ)
    (h0 : ∀ ν ∈ S0, 1 ≤ ν) (h1 : ∀ p ∈ S1, 2 ≤ p)
    (h2 : ∀ p ∈ S2, 1 ≤ p) (h3 : ∀ p ∈ S3, 1 ≤ p) :
    ∀ m ∈ support S0 S1 S2 S3, 2 ≤ m := by
  apply support_forall S0 S1 S2 S3
  intro ν hν p1 hp1 p2 hp2 p3 hp3
  simpa using Nat.mul_le_mul
    (Nat.mul_le_mul (Nat.mul_le_mul (h0 ν hν) (h1 p1 hp1)) (h2 p2 hp2)) (h3 p3 hp3)

theorem support_ratio_sixteen (S0 S1 S2 S3 : Finset ℕ)
    (h0 : ∀ x ∈ S0, ∀ y ∈ S0, y ≤ 2 * x)
    (h1 : ∀ x ∈ S1, ∀ y ∈ S1, y ≤ 2 * x)
    (h2 : ∀ x ∈ S2, ∀ y ∈ S2, y ≤ 2 * x)
    (h3 : ∀ x ∈ S3, ∀ y ∈ S3, y ≤ 2 * x) :
    ∀ m ∈ support S0 S1 S2 S3, ∀ m' ∈ support S0 S1 S2 S3,
      m' ≤ 16 * m := by
  intro m hm m' hm'
  obtain ⟨ν, hν, p1, hp1, p2, hp2, p3, hp3, rfl⟩ :=
    (mem_support_iff S0 S1 S2 S3 m).mp hm
  obtain ⟨ν', hν', p1', hp1', p2', hp2', p3', hp3', rfl⟩ :=
    (mem_support_iff S0 S1 S2 S3 m').mp hm'
  calc
    _ ≤ (2 * ν) * (2 * p1) * (2 * p2) * (2 * p3) :=
      Nat.mul_le_mul (Nat.mul_le_mul
        (Nat.mul_le_mul (h0 ν hν ν' hν') (h1 p1 hp1 p1' hp1'))
        (h2 p2 hp2 p2' hp2')) (h3 p3 hp3 p3' hp3')
    _ = _ := by ring

theorem support_lower_bound (S0 S1 S2 S3 : Finset ℕ) (A : ℝ)
    (h : ∀ ν ∈ S0, ∀ p1 ∈ S1, ∀ p2 ∈ S2, ∀ p3 ∈ S3,
      A ≤ (ν : ℝ) * p1 * p2 * p3) :
    ∀ m ∈ support S0 S1 S2 S3, A ≤ (m : ℝ) := by
  apply support_forall S0 S1 S2 S3
  intro ν hν p1 hp1 p2 hp2 p3 hp3
  simpa only [Nat.cast_mul] using h ν hν p1 hp1 p2 hp2 p3 hp3

theorem support_upper_bound (S0 S1 S2 S3 : Finset ℕ) (A : ℝ)
    (h : ∀ ν ∈ S0, ∀ p1 ∈ S1, ∀ p2 ∈ S2, ∀ p3 ∈ S3,
      (ν : ℝ) * p1 * p2 * p3 ≤ A) :
    ∀ m ∈ support S0 S1 S2 S3, (m : ℝ) ≤ A := by
  apply support_forall S0 S1 S2 S3
  intro ν hν p1 hp1 p2 hp2 p3 hp3
  simpa only [Nat.cast_mul] using h ν hν p1 hp1 p2 hp2 p3 hp3

theorem support_cross_upper_bound (S0 S1 S2 S3 S4 : Finset ℕ) (A : ℝ)
    (h : ∀ ν ∈ S0, ∀ p1 ∈ S1, ∀ p2 ∈ S2, ∀ p3 ∈ S3, ∀ p4 ∈ S4,
      (ν : ℝ) * p1 * p2 * p3 * p4 ≤ A) :
    ∀ m ∈ support S0 S1 S2 S3, ∀ n ∈ S4, (m : ℝ) * n ≤ A := by
  apply support_cross_forall S0 S1 S2 S3 S4
  intro ν hν p1 hp1 p2 hp2 p3 hp3 p4 hp4
  simpa only [Nat.cast_mul] using h ν hν p1 hp1 p2 hp2 p3 hp3 p4 hp4

#print axioms support_ratio_sixteen
run_cmd do
  for decl in [``mem_support_iff, ``support_forall, ``support_cross_forall,
      ``support_two_le, ``support_ratio_sixteen, ``support_lower_bound,
      ``support_upper_bound, ``support_cross_upper_bound] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end FourPrimeGrouping
end
