import PositiveSharpMovingWindow

/-! Exact source/actual dyadic endpoint comparison for literal sharp Λ counts.
The source intervals are [2^j,2^(j+1)); the existing actual intervals are
(2^j,2^(j+1)]. The third coordinate and the moving physical window are unchanged.
All finite product multiplicities and all prime powers are retained. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace CancellationTransferEndpoints
open PositiveInteriorModel PositiveInteriorCells PositiveSharpCounts
open PositiveSharpMovingWindow

def sourceCoordinates (X : ℝ) (j : ℕ × ℕ) : Finset Triple :=
  Finset.Ico (2^j.1) (2*2^j.1) ×ˢ
    (Finset.Ico (2^j.2) (2*2^j.2) ×ˢ
      Finset.Ioc ⌊thirdScale X j/8⌋₊ ⌊4*thirdScale X j⌋₊)

def cover (X : ℝ) (j : ℕ × ℕ) : Finset Triple :=
  Finset.Ioc 0 (2*2^j.1) ×ˢ
    (Finset.Ioc 0 (2*2^j.2) ×ˢ
      Finset.Ioc ⌊thirdScale X j/8⌋₊ ⌊4*thirdScale X j⌋₊)

def sourceCount (X : ℝ) (j : ℕ × ℕ) (x y : ℝ) : ℝ :=
  ∑ k ∈ (sourceCoordinates X j).filter (inWindow x y), tripleWeight k

def endpointCell (X : ℝ) (j : ℕ × ℕ) (x y : ℝ) : ℝ :=
  (sourceCount X j x y-weightedCount X j x y)/(y*denominator X j)

def endpointTotal (X x y : ℝ) : ℝ :=
  ∑ j ∈ boxes (mesh X), |endpointCell X j x y|

def kernelSum (S : Finset Triple) (X Y d x : ℝ) : ℝ :=
  ∑ k ∈ S, (tripleWeight k/d)*movingKernel X Y (tripleProduct k) x

def coverBadMass (X : ℝ) (j : ℕ × ℕ) : ℝ :=
  ∑ k ∈ (cover X j).filter (fun k => ¬allPrime k), tripleWeight k

theorem floor_scale (m : ℕ) : ⌊scale m⌋₊=2^m := by
  unfold scale
  norm_cast
  exact Nat.floor_natCast _

theorem floor_twice_scale (m : ℕ) : ⌊2*scale m⌋₊=2*2^m := by
  unfold scale
  norm_cast
  exact Nat.floor_natCast _

theorem source_subset_cover (X : ℝ) (j : ℕ × ℕ) :
    sourceCoordinates X j ⊆ cover X j := by
  intro k hk
  simp only [sourceCoordinates, cover, Finset.mem_product, Finset.mem_Ico,
    Finset.mem_Ioc] at hk ⊢
  have hp : 0<(2:ℕ)^j.1 := by positivity
  have hr : 0<(2:ℕ)^j.2 := by positivity
  exact ⟨⟨by omega,by omega⟩,⟨by omega,by omega⟩,hk.2.2⟩

theorem actual_subset_cover (X : ℝ) (j : ℕ × ℕ) :
    coordinates X j ⊆ cover X j := by
  intro k hk
  simp only [coordinates, cover, floor_scale, floor_twice_scale,
    Finset.mem_product, Finset.mem_Ioc] at hk ⊢
  exact ⟨⟨by omega,hk.1.2⟩,⟨by omega,hk.2.1.2⟩,hk.2.2⟩

theorem prime_dyadic_membership (m p : ℕ) (hm : 2≤m) (hp : p.Prime) :
    p∈Finset.Ico (2^m) (2*2^m) ↔ p∈Finset.Ioc (2^m) (2*2^m) := by
  have hlo : p≠2^m := by
    intro he
    exact Nat.Prime.not_prime_pow hm (he ▸ hp)
  have hhi : p≠2*2^m := by
    intro he
    have ht : 2*2^m=(2:ℕ)^(m+1) := by ring
    rw [ht] at he
    exact Nat.Prime.not_prime_pow (by omega : 2≤m+1) (he ▸ hp)
  simp only [Finset.mem_Ico, Finset.mem_Ioc]
  omega

theorem prime_coordinates_iff (X : ℝ) (j : ℕ × ℕ) (hj : 2≤j.1 ∧ 2≤j.2)
    (k : Triple) (hk : allPrime k) :
    k∈sourceCoordinates X j ↔ k∈coordinates X j := by
  simp only [sourceCoordinates, coordinates, floor_scale, floor_twice_scale,
    Finset.mem_product]
  rw [prime_dyadic_membership j.1 k.1 hj.1 hk.1,
    prime_dyadic_membership j.2 k.2.1 hj.2 hk.2.1]

theorem normalized_count_eq_kernel (S : Finset Triple) (X Y d x : ℝ) :
    (∑ k∈S.filter (inWindow x (x*Y/X)),tripleWeight k)/((x*Y/X)*d)=
      kernelSum S X Y d x := by
  classical
  simp only [Finset.sum_filter, Finset.sum_div, kernelSum]
  apply Finset.sum_congr rfl
  intro k _
  have he : x∈movingSet X Y (tripleProduct k) ↔ inWindow x (x*Y/X) k := Iff.rfl
  simp only [movingKernel, Set.indicator_apply,he]
  split_ifs <;> simp [div_eq_mul_inv]
  ring

theorem endpointCell_eq_kernels (X Y x : ℝ) (j : ℕ × ℕ) :
    endpointCell X j x (x*Y/X)=
      kernelSum (sourceCoordinates X j) X Y (denominator X j) x-
        kernelSum (coordinates X j) X Y (denominator X j) x := by
  unfold endpointCell sourceCount weightedCount windowTuples
  rw [sub_div,normalized_count_eq_kernel,normalized_count_eq_kernel]

theorem kernelSum_integrable (S : Finset Triple) (X Y d : ℝ)
    (hX : 0<X) (hY : 0<Y) :
    IntegrableOn (kernelSum S X Y d) (Icc X (2*X)) :=
  integrable_finsetSum _ (fun k _ =>
    (movingKernel_integrable X Y (tripleProduct k) hX hY).const_mul _)

theorem endpointCell_abs_integrable (X Y : ℝ) (hX : 0<X) (hY : 0<Y)
    (j : ℕ × ℕ) :
    IntegrableOn (fun x => |endpointCell X j x (x*Y/X)|) (Icc X (2*X)) := by
  simp_rw [endpointCell_eq_kernels]
  exact ((kernelSum_integrable _ X Y _ hX hY).sub
    (kernelSum_integrable _ X Y _ hX hY)).abs

theorem endpointTotal_integrable (X Y : ℝ) (hX : 0<X) (hY : 0<Y) :
    IntegrableOn (fun x => endpointTotal X x (x*Y/X)) (Icc X (2*X)) :=
  integrable_finsetSum _ (fun j _ => endpointCell_abs_integrable X Y hX hY j)

theorem abs_sum_sub_le_bad {α : Type*} [DecidableEq α]
    (A B U : Finset α) (f : α → ℝ) (P : α → Prop) [DecidablePred P]
    (hA : A⊆U) (hB : B⊆U) (hf : ∀ k∈U,0≤f k)
    (hP : ∀ k∈U,P k → (k∈A ↔ k∈B)) :
    |(∑ k∈A,f k)-(∑ k∈B,f k)|≤∑ k∈U.filter (fun k => ¬P k),f k := by
  have he (S : Finset α) (hS : S⊆U) :
      (∑ k∈S,f k)=∑ k∈U,if k∈S then f k else 0 := by
    rw [← Finset.sum_filter]
    congr 1
    ext k
    simp only [Finset.mem_filter]
    exact ⟨fun hk => ⟨hS hk,hk⟩,fun hk => hk.2⟩
  rw [he A hA,he B hB,←Finset.sum_sub_distrib,Finset.sum_filter]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro k hk
  have hn := hf k hk
  by_cases hp : P k
  · have hm := hP k hk hp
    simp only [not_true_eq_false,ite_false,hp]
    simp only [hm,sub_self,abs_zero,le_refl]
  · by_cases ha : k∈A <;> by_cases hb : k∈B <;>
      simp [ha,hb,hp,abs_of_nonneg hn,hn]

theorem endpointCell_abs_le_kernel (X Y x : ℝ) (hX : 1<X) (hY : 0<Y)
    (hx : x∈Icc X (2*X)) (j : ℕ × ℕ) (hj : j∈boxes (mesh X))
    (hj2 : 2≤j.1 ∧ 2≤j.2) :
    |endpointCell X j x (x*Y/X)|≤
      kernelSum ((cover X j).filter (fun k => ¬allPrime k)) X Y (denominator X j) x := by
  have hl : 0<Real.log X := Real.log_pos hX
  have hd : 0<denominator X j :=
    (by positivity : 0<(Real.log X)^3/96).trans_le (denominator_lower X hX j hj)
  rw [endpointCell_eq_kernels]
  apply abs_sum_sub_le_bad _ _ _ _ allPrime
    (source_subset_cover X j) (actual_subset_cover X j)
  · intro k _
    apply mul_nonneg (div_nonneg (tripleWeight_nonneg k) hd.le)
    unfold movingKernel
    by_cases hh : x∈movingSet X Y (tripleProduct k)
    · rw [Set.indicator_of_mem hh]
      have hxp : 0<x := (by linarith : 0<X).trans_le hx.1
      positivity
    · rw [Set.indicator_of_notMem hh]
  · intro k _ hk
    exact prime_coordinates_iff X j hj2 k hk

theorem endpointCell_integral_le (X Y : ℝ) (hX : 1<X) (hY : 0<Y)
    (j : ℕ × ℕ) (hj : j∈boxes (mesh X)) (hj2 : 2≤j.1 ∧ 2≤j.2) :
    (∫ x in Icc X (2*X), |endpointCell X j x (x*Y/X)|)≤
      4/denominator X j*coverBadMass X j := by
  have hXp : 0<X := by linarith
  have hl : 0<Real.log X := Real.log_pos hX
  have hd : 0<denominator X j :=
    (by positivity : 0<(Real.log X)^3/96).trans_le (denominator_lower X hX j hj)
  calc
    _ ≤ ∫ x in Icc X (2*X),
        kernelSum ((cover X j).filter (fun k => ¬allPrime k)) X Y (denominator X j) x := by
      apply setIntegral_mono_on (endpointCell_abs_integrable X Y hXp hY j)
        (kernelSum_integrable _ X Y _ hXp hY) measurableSet_Icc
      intro x hx
      exact endpointCell_abs_le_kernel X Y x hX hY hx j hj hj2
    _ ≤ ∑ k∈(cover X j).filter (fun k => ¬allPrime k),
        (tripleWeight k/denominator X j)*4 := by
      simp only [kernelSum]
      rw [integral_finsetSum _ (fun k _ =>
        (movingKernel_integrable X Y (tripleProduct k) hXp hY).const_mul _)]
      apply Finset.sum_le_sum
      intro k _
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left (movingKernel_integral_le X Y (tripleProduct k) hXp hY)
        (div_nonneg (tripleWeight_nonneg k) hd.le)
    _ = _ := by
      unfold coverBadMass
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring

run_cmd do
  for decl in [``floor_scale,``floor_twice_scale,``source_subset_cover,
      ``actual_subset_cover,``prime_dyadic_membership,``prime_coordinates_iff,
      ``normalized_count_eq_kernel,``endpointCell_eq_kernels,``kernelSum_integrable,
      ``endpointCell_abs_integrable,``endpointTotal_integrable,``abs_sum_sub_le_bad,
      ``endpointCell_abs_le_kernel,``endpointCell_integral_le] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ACTUAL DYADIC ENDPOINT DISCREPANCY CONTROLLED BY NONPRIME COVER MASS"
end CancellationTransferEndpoints
end
