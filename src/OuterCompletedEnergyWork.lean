import CompletedBandEnergyWork
import OuterCompletedCollectionWork
import OuterBlockContourTailWork
import OuterContinuousTailWork

/-! Unconditional full-height energies for the literal completed and
centered source modes, uniformly in separator translations. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators
namespace OuterCompletedEnergyWork
open OuterCompletedCollectionWork OuterBlockSharpCompletionWork OuterBlockMainTermWork
open OuterBlockCofactorWork OuterActiveDyadicWork OuterRectangularBlocksWork LongerTupleEncoding
open LongerTupleCollection OuterBlockContourTailWork OuterCenteredFlatWork

def centeredPolynomial (X s σ : ℝ) (i j : ℕ) (k : BlockKey) (ω : Fin 9→ℝ) (t : ℝ) : ℂ :=
  modePolynomial X s i j k ω σ t*centeredFlat (lower X k) (upper X k) σ t

theorem product_band (X : ℝ) (hX : 2≤X) (k : BlockKey)
    (hscale : 256*(scale k:ℝ)≤X) (a : Entry) (ha : a∈entries X k) :
    0<product a ∧ X/256≤(product a:ℝ) ∧ (product a:ℝ)≤129*X := by
  obtain ⟨hr,hn⟩ := Finset.mem_product.mp ha
  have hm := index_range X hX k a.1 hr
  have hn' := Finset.mem_Ioc.mp hn
  have hM : (0:ℝ)<scale k := by exact_mod_cast scale_pos k
  have hXp : 0<X := by linarith
  have hlo := OuterBlockCofactorScaleWork.lower_half X k hscale
  have hni : (lower X k:ℝ)≤a.2 := by exact_mod_cast hn'.1.le
  have hmi : (scale k:ℝ)≤ index a.1 := by exact_mod_cast hm.1
  have hlower : X/256≤(scale k:ℝ)*(a.2:ℝ) := by
    have hh := mul_le_mul_of_nonneg_left (hlo.trans hni) hM.le
    field_simp at hh
    nlinarith
  have hu : (upper X k:ℝ)≤8*X/(scale k:ℝ)+1 :=
    (Nat.ceil_lt_add_one (by positivity : 0≤8*X/(scale k:ℝ))).le
  have han : (a.2:ℝ)≤upper X k := by exact_mod_cast hn'.2
  have hmn : (scale k:ℝ)*(a.2:ℝ)≤8*X+(scale k:ℝ) := by
    have hh := mul_le_mul_of_nonneg_left (han.trans hu) hM.le
    field_simp at hh
    nlinarith
  have him : (index a.1:ℝ)≤16*(scale k:ℝ) := by exact_mod_cast hm.2.le
  have hi := mul_le_mul_of_nonneg_right him (Nat.cast_nonneg a.2)
  refine ⟨Nat.mul_pos ((scale_pos k).trans_le hm.1) (by omega),?_,?_⟩
  · simp only [product,Nat.cast_mul]
    exact hlower.trans (mul_le_mul_of_nonneg_right hmi (Nat.cast_nonneg a.2))
  · simp only [product,Nat.cast_mul]
    nlinarith

theorem eventually_completed_energy (η : ℝ) (hη : 0<η) :
    ∀ᶠ X : ℝ in atTop, 256≤X ∧ ∀ (s σ a b : ℝ) (i j : ℕ) (k : BlockKey) (ω : Fin 9→ℝ),
      256*(scale k:ℝ)≤X → 1≤σ → a≤b → b-a≤X →
      (∫t in Icc a b,‖completedPolynomial X s σ t i j k ω‖^2)≤X^η := by
  filter_upwards [CompletedBandEnergyWork.eventually_band_energy η hη,
    OuterCompletedCollectionWork.eventually_coefficient_cap (η/4) (by positivity)] with X he hc
  refine ⟨he.1,?_⟩
  intro s σ a b i j k ω hscale hσ hab hlen
  have hband : ∀n∈support (entries X k) product,0<n ∧ X/256≤(n:ℝ) ∧ (n:ℝ)≤129*X := by
    intro n hn
    obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hn
    exact product_band X (by linarith [he.1]) k hscale r hr
  have hh := he.2 (support (entries X k) product)
    (coefficient (entries X k) product (weights X s i j ω)) σ a b hσ hab hlen hband
    (fun n hn => hc.2 s i j k ω n (hband n hn).1 (by nlinarith [he.1,(hband n hn).2.2]))
  simpa only [collected_polynomial] using hh

theorem mode_continuous (X s σ : ℝ) (i j : ℕ) (k : BlockKey) (ω : Fin 9→ℝ) (hX : 2≤X) :
    Continuous (modePolynomial X s i j k ω σ) := by
  have he : modePolynomial X s i j k ω σ =
      Erdos374.HarmanGram152.verticalDirichlet152 (support (blockSource X k) index)
        (coefficient (blockSource X k) index (modeWeight X s i j ω)) σ := funext (fun t => polynomial_collected X s σ t i j k ω)
  rw [he]
  apply NormalizedMeanSquare.continuous_vertical
  intro n hn
  obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hn
  exact (scale_pos k).trans_le (index_range X hX k r hr).1

theorem centered_continuous (X s σ : ℝ) (i j : ℕ) (k : BlockKey) (ω : Fin 9→ℝ)
    (hX : 2≤X) (hσ : 1<σ) (hscale : 256*(scale k:ℝ)≤X) :
    Continuous (centeredPolynomial X s σ i j k ω) := by
  have hlo := lower_pos X k hscale
  have hhi := lower_le_upper X k (by linarith)
  exact (mode_continuous X s σ i j k ω hX).mul
    (OuterModeContinuityWork.continuous_centeredFlat _ _ σ (by omega) (by omega) hσ)

theorem eventually_centered_energy (η : ℝ) (hη : 0<η) :
    ∀ᶠ X : ℝ in atTop, 256≤X ∧ ∀ (s σ a b : ℝ) (i j : ℕ) (k : BlockKey) (ω : Fin 9→ℝ),
      256*(scale k:ℝ)≤X → 1<σ → a≤b → b-a≤X → (∀t∈Icc a b,1≤|t|) →
      (∫t in Icc a b,‖centeredPolynomial X s σ i j k ω t‖^2)≤X^η := by
  filter_upwards [eventually_completed_energy (η/2) (by positivity),
    (tendsto_rpow_atTop (by positivity : 0<η/2)).eventually (eventually_ge_atTop (18:ℝ))] with X he hp
  refine ⟨he.1,?_⟩
  intro s σ a b i j k ω hscale hσ hab hlen haway
  have hX : 2≤X := by linarith [he.1]
  have hlo := lower_pos X k hscale
  have hhi := lower_le_upper X k (by linarith)
  have hd := he.2 s σ a b i j k ω hscale hσ.le hab hlen
  simp_rw [polynomial_factorization] at hd
  have ht := OuterContinuousTailWork.centered_energy (lower X k) (upper X k) σ a b 1
    (modePolynomial X s i j k ω σ) (by omega) (by omega) hσ hab (by norm_num)
    (mode_continuous X s σ i j k ω hX) (fun t _ => modePolynomial_norm X s σ t i j k ω hX hσ.le) haway
  have hp2 : (X^(η/2))^2=X^η := by rw [←Real.rpow_mul_natCast (by linarith : 0≤X)]; congr 1; ring
  change _ ≤ X^η
  change (∫t in Icc a b,‖centeredPolynomial X s σ i j k ω t‖^2)≤_ at ht
  norm_num only [div_one] at ht
  nlinarith

run_cmd do
  for decl in [``product_band, ``eventually_completed_energy, ``mode_continuous,
      ``centered_continuous, ``eventually_centered_energy] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end OuterCompletedEnergyWork
