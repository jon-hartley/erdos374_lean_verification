import OuterBlockSharpCompletionWork
import ComplexSmoothingBoundary

/-! Collect completed products without losing their ordered representations
or complex phase weights. Five-factor divisor bounds control collisions. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Filter Set
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace OuterCompletedCollectionWork
open OuterBlockSharpCompletionWork OuterBlockMainTermWork OuterBlockCofactorWork
open OuterActiveDyadicWork OuterRectangularBlocksWork LongerTupleEncoding
open LongerTupleCollection Erdos374.HarmanGram152

abbrev Entry := Representation×ℕ
def entries (X : ℝ) (k : BlockKey) : Finset Entry :=
  (blockSource X k)×ˢ(Finset.Ioc (lower X k) (upper X k))
def product (a : Entry) : ℕ := index a.1*a.2
def encoding (a : Entry) : Fin 5→ℕ := Fin.cons a.2 (encode 2 a.1)
def weights (X s : ℝ) (i j : ℕ) (ω : Fin 9→ℝ) (a : Entry) : ℂ := modeWeight X s i j ω a.1

theorem entry_length (X : ℝ) (hX : 2≤X) (k : BlockKey) (a : Entry) (ha : a∈entries X k) :
    a.1.2.2.length=2 :=
  (OuterSmoothErrorSupportWork.ambient_data X hX a.1
    (Finset.mem_filter.mp (Finset.mem_product.mp ha).1).1).1

theorem encoding_product (X : ℝ) (hX : 2≤X) (k : BlockKey) (a : Entry) (ha : a∈entries X k) :
    product a=∏i,encoding a i := by
  simp only [encoding,Fin.prod_cons,product,←encode_product 2 a.1 (entry_length X hX k a ha)]
  exact Nat.mul_comm _ _

theorem encoding_injective (X : ℝ) (hX : 2≤X) (k : BlockKey) :
    Set.InjOn encoding (entries X k) := by
  intro a ha b hb he
  have hn : a.2=b.2 := by simpa only [encoding,Fin.cons_zero] using congrFun he 0
  have hr : encode 2 a.1=encode 2 b.1 := by
    funext i
    simpa only [encoding,Fin.cons_succ] using congrFun he i.succ
  exact Prod.ext (encode_injective 2 a.1 b.1 (entry_length X hX k a ha)
    (entry_length X hX k b hb) hr) hn

theorem product_bounds (X : ℝ) (hX : 256≤X) (k : BlockKey)
    (hscale : 256*(scale k:ℝ)≤X) (a : Entry) (ha : a∈entries X k) :
    0<product a ∧ (product a:ℝ)≤X^2 := by
  obtain ⟨hr,hn⟩ := Finset.mem_product.mp ha
  have hm := index_range X (by linarith) k a.1 hr
  have hn' := Finset.mem_Ioc.mp hn
  have hM : (0:ℝ)<scale k := by exact_mod_cast scale_pos k
  have hXp : 0<X := by linarith
  have hu : (upper X k:ℝ)≤8*X/(scale k:ℝ)+1 :=
    (Nat.ceil_lt_add_one (by positivity : 0≤8*X/(scale k:ℝ))).le
  have han : (a.2:ℝ)≤upper X k := by exact_mod_cast hn'.2
  have hmn : (scale k:ℝ)*(a.2:ℝ)≤8*X+(scale k:ℝ) := by
    have hh := mul_le_mul_of_nonneg_left (han.trans hu) hM.le
    field_simp at hh
    nlinarith
  have him : (index a.1:ℝ)≤16*(scale k:ℝ) := by exact_mod_cast hm.2.le
  have hi : (index a.1:ℝ)*(a.2:ℝ)≤16*((scale k:ℝ)*(a.2:ℝ)) := by
    nlinarith [mul_le_mul_of_nonneg_right him (Nat.cast_nonneg a.2)]
  refine ⟨Nat.mul_pos ((scale_pos k).trans_le hm.1) (by omega),?_⟩
  simp only [product,Nat.cast_mul]
  nlinarith

theorem collected_polynomial (X s σ t : ℝ) (i j : ℕ) (k : BlockKey) (ω : Fin 9→ℝ) :
    verticalDirichlet152 (support (entries X k) product)
      (coefficient (entries X k) product (weights X s i j ω)) σ t =
      completedPolynomial X s σ t i j k ω := by
  rw [verticalDirichlet152,grouped_sum]
  simp only [entries,Finset.sum_product,weights,product,completedPolynomial,MellinWindowFactor.line]

theorem collected_count (X s L R : ℝ) (i j : ℕ) (k : BlockKey) (ω : Fin 9→ℝ) (hLR : L≤R) :
    ComplexSmoothingBoundary.sharp (support (entries X k) product)
        (coefficient (entries X k) product (weights X s i j ω)) R-
      ComplexSmoothingBoundary.sharp (support (entries X k) product)
        (coefficient (entries X k) product (weights X s i j ω)) L =
      completedCount X s L R i j k ω := by
  have he (z : ℝ) : ComplexSmoothingBoundary.sharp (support (entries X k) product)
      (coefficient (entries X k) product (weights X s i j ω)) z =
      ∑a∈entries X k,if (product a:ℝ)≤z then weights X s i j ω a else 0 := by
    have hh := grouped_sum (entries X k) product (weights X s i j ω)
      (fun n => if (n:ℝ)≤z then (1:ℂ) else 0)
    simpa only [ComplexSmoothingBoundary.sharp,mul_ite,mul_one,mul_zero] using hh
  rw [he,he,←Finset.sum_sub_distrib]
  simp only [entries,Finset.sum_product,product,weights,completedCount]
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro n hn
  simp only [Nat.cast_mul]
  by_cases hR : (index r:ℝ)*(n:ℝ)≤R
  · by_cases hL : (index r:ℝ)*(n:ℝ)≤L
    · simp [hR,hL,not_lt.mpr hL]
    · simp [hR,hL,lt_of_not_ge hL]
  · have hL : ¬(index r:ℝ)*(n:ℝ)≤L := by linarith
    simp [hR,hL]

theorem eventually_coefficient_cap (η : ℝ) (hη : 0<η) :
    ∀ᶠ X : ℝ in atTop, 2≤X ∧ ∀ (s : ℝ) (i j : ℕ) (k : BlockKey) (ω : Fin 9→ℝ)
      (n : ℕ), 0<n → (n:ℝ)≤X^2 →
      ‖coefficient (entries X k) product (weights X s i j ω) n‖≤X^η := by
  filter_upwards [LongerTupleCollection.eventual_coefficient_cap (α:=Entry) 5 η hη,
    eventually_ge_atTop (2:ℝ)] with X hcap hX
  refine ⟨hX,?_⟩
  intro s i j k ω n hn hnX
  exact hcap.2 (entries X k) product encoding (weights X s i j ω)
    (encoding_product X hX k) (encoding_injective X hX k)
    (fun a ha => OuterBlockMassBudgetWork.modeWeight_norm X s i j ω a.1)
    n hn hnX

run_cmd do
  for decl in [``entry_length, ``encoding_product, ``encoding_injective, ``product_bounds,
      ``collected_polynomial, ``collected_count, ``eventually_coefficient_cap] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end OuterCompletedCollectionWork
