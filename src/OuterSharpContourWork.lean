import ComplexFiniteWindowWork
import OuterCompletedCollectionWork

/-! The actual complex completed sharp count has a uniform truncated
Mellin approximation, including collisions and all separator phases. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators
namespace OuterSharpContourWork
open OuterCompletedCollectionWork OuterBlockSharpCompletionWork OuterBlockMainTermWork
open OuterBlockCofactorWork OuterActiveDyadicWork LongerTupleCollection

def discreteContour (X s x δ : ℝ) (i j : ℕ) (k : BlockKey) (ω : Fin 9→ℝ) : ℂ :=
  ((1/(2*Real.pi):ℝ):ℂ)*SmoothedWindowTransfer.transform
    (fun t => completedPolynomial X s (1+1/Real.log X) t i j k ω)
    MellinSmoothingFunction.smoothing (X^(-19/20:ℝ)) (-X) X (1+1/Real.log X) δ x

theorem eventually_sharp_contour : ∀ᶠ X : ℝ in atTop, 256≤X ∧
    ∀ (s x δ : ℝ) (i j : ℕ) (k : BlockKey) (ω : Fin 9→ℝ),
      256*(scale k:ℝ)≤X → x∈Icc X (2*X) → δ∈Icc 0 (1/2) →
      ‖completedCount X s (x-x*δ) x i j k ω-discreteContour X s x δ i j k ω‖≤8*X^(2/25:ℝ) := by
  filter_upwards [ComplexFiniteWindowWork.eventual_approximation,
    OuterCompletedCollectionWork.eventually_coefficient_cap (1/200) (by norm_num),
    eventually_ge_atTop (256:ℝ)] with X happ hcap hX
  refine ⟨hX,?_⟩
  intro s x δ i j k ω hscale hx hδ
  have hXp : 0<X := by linarith
  have hB : 1≤⌊X^2⌋₊ := (Nat.le_floor_iff (by positivity)).mpr (by norm_num only [Nat.cast_one]; nlinarith)
  have hS (n : ℕ) (hn : n∈support (entries X k) product) : 0<n ∧ n≤⌊X^2⌋₊ := by
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hn
    have hb := product_bounds X hX k hscale a ha
    exact ⟨hb.1,Nat.le_floor hb.2⟩
  have hh := happ.2 (support (entries X k) product)
    (coefficient (entries X k) product (weights X s i j ω)) ⌊X^2⌋₊ x δ
    hB (Nat.floor_le (by positivity)) hS (fun n hn =>
      hcap.2 s i j k ω n (hS n hn).1
        ((by exact_mod_cast (hS n hn).2 : (n:ℝ)≤⌊X^2⌋₊).trans (Nat.floor_le (by positivity)))) hx hδ
  unfold ComplexFiniteWindowWork.error at hh
  rw [collected_count X s (x-x*δ) x i j k ω (by nlinarith [hδ.1,hx.1])] at hh
  have he : Erdos374.HarmanGram152.verticalDirichlet152 (support (entries X k) product)
      (coefficient (entries X k) product (weights X s i j ω)) (1+1/Real.log X) =
      fun t => completedPolynomial X s (1+1/Real.log X) t i j k ω := by
    funext t
    exact collected_polynomial X s _ t i j k ω
  rw [he] at hh
  exact hh

theorem eventually_active_sharp_contour (s : ℝ) (hs : 0≤s) :
    ∀ᶠ X : ℝ in atTop, 256≤X ∧ ∀ (x δ : ℝ) (i j : ℕ) (k : BlockKey) (ω : Fin 9→ℝ),
      k∈activeKeys X s i j → x∈Icc X (2*X) → δ∈Icc 0 (1/2) →
      ‖completedCount X s (x-x*δ) x i j k ω-discreteContour X s x δ i j k ω‖≤8*X^(2/25:ℝ) := by
  filter_upwards [eventually_sharp_contour,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1000000:ℝ))] with X hh hlog
  refine ⟨hh.1,?_⟩
  intro x δ i j k ω hk hx hδ
  exact hh.2 s x δ i j k ω
    (OuterBlockCofactorScaleWork.active_lower X s (by linarith [hh.1]) hs hlog i j k hk).1 hx hδ

run_cmd do
  for decl in [``eventually_sharp_contour, ``eventually_active_sharp_contour] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end OuterSharpContourWork
