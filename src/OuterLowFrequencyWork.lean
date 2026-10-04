import OuterBandMeanWork

/-! Unconditional low physical-frequency means of the actual centered source.
Euler summation uses the literal lower endpoint; no factorization or prime cap. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Filter MeasureTheory Set
namespace OuterLowFrequencyWork
open OuterBandMeanWork OuterUpperFrequencyWork OuterCompletedEnergyWork
open OuterBlockCofactorWork OuterActiveDyadicWork OuterBlockMainTermWork
open MellinSmoothingFunction OuterMainCorrectionWork

def lowHeight (X : ℝ) : ℝ := X^(1/1000:ℝ)

theorem lower_lt_upper (X : ℝ) (k : BlockKey) (hX : 0<X) : lower X k<upper X k := by
  have hM : (0:ℝ)<scale k := by exact_mod_cast scale_pos k
  have hl : (lower X k:ℝ)≤X/(128*(scale k:ℝ)) := Nat.floor_le (by positivity)
  have hu : 8*X/(scale k:ℝ)≤upper X k := Nat.le_ceil _
  have hh : X/(128*(scale k:ℝ))<8*X/(scale k:ℝ) := by
    apply (div_lt_div_iff₀ (by positivity) hM).mpr
    nlinarith [mul_pos hX hM]
  exact_mod_cast hl.trans_lt (hh.trans_le hu)

theorem active_low_energy (X s : ℝ) (i j : ℕ) (k : BlockKey) (ω : Fin 9→ℝ)
    (hX : 2≤X) (hs : 0≤s) (hlog : 1000000≤Real.log X) (hk : k∈activeKeys X s i j) :
    (∫t in Icc (-lowHeight X) (lowHeight X),‖centeredPolynomial X s (1+1/Real.log X) i j k ω t‖^2)
      ≤32*X^(-449/1000:ℝ) := by
  have hXp : 0<X := by linarith
  have ha := OuterBlockCofactorScaleWork.active_lower X s hX hs hlog i j k hk
  have hσ : 1<1+1/Real.log X := lt_add_of_pos_right _ (by positivity)
  have hσ2 : 1+1/Real.log X≤2 := by
    have := (div_le_one (by linarith : 0<Real.log X)).mpr (show 1≤Real.log X by linarith)
    linarith
  have hh := OuterCenteredFlatWork.low_energy X (113/500) (1/1000) (by linarith) (by norm_num)
    (lower X k) (lower X k) (upper X k) (1+1/Real.log X)
    (modePolynomial X s i j k ω (1+1/Real.log X)) (lower_pos X k ha.1)
    ha.2.1 le_rfl (lower_lt_upper X k hXp) hσ hσ2
    (fun t _ => OuterBlockContourTailWork.modePolynomial_norm X s (1+1/Real.log X) t i j k ω hX hσ.le)
  simpa only [lowHeight,centeredPolynomial,show (3*(1/1000)-2*(113/500):ℝ)= -449/1000 by norm_num] using hh

theorem eventually_low_square (s : ℝ) (hs : 0≤s) :
    ∀ᶠ X : ℝ in atTop, Real.exp 1≤X ∧ 2≤X ∧ ∀(Y ε : ℝ) (i j : ℕ) (k : BlockKey) (ω : Fin 9→ℝ),
      k∈activeKeys X s i j → 0≤Y → Y<X → ε∈Ioo 0 1 →
      (1/X)*(∫x in Icc X (2*X),‖band X s Y ε (-lowHeight X) (lowHeight X) i j k ω x‖^2)≤
        Y^2*X^(-1/5:ℝ) := by
  filter_upwards [SmoothedWindowTransfer.eventually_bound smoothing differentiable support nonnegative mass_one
      (2/5) (by norm_num),eventually_ge_atTop (2:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1000000:ℝ)),
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<49/1000)).eventually (eventually_ge_atTop (32:ℝ)),
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<999/1000)).eventually (eventually_ge_atTop (2:ℝ))]
    with X ht hX hlog hpow hlen
  refine ⟨ht.1,hX,?_⟩
  intro Y ε i j k ω hk hY hYX hε
  have hXp : 0<X := by linarith
  have henergy : (∫t in Icc (-lowHeight X) (lowHeight X),
      ‖centeredPolynomial X s (1+1/Real.log X) i j k ω t‖^2)≤X^(-(2/5):ℝ) := by
    apply (active_low_energy X s i j k ω hX hs hlog hk).trans
    have hh := mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hXp.le (-449/1000))
    have he : X^(49/1000:ℝ)*X^(-449/1000:ℝ)=X^(-(2/5):ℝ) := by rw [←Real.rpow_add hXp]; norm_num
    rwa [he] at hh
  have hlen' : lowHeight X-(-lowHeight X)≤X := by
    have hh := mul_le_mul_of_nonneg_right hlen (Real.rpow_nonneg hXp.le (1/1000))
    have he : X^(999/1000:ℝ)*X^(1/1000:ℝ)=X := by rw [←Real.rpow_add hXp]; norm_num
    rw [he] at hh
    dsimp [lowHeight]
    linarith
  have hσ : 1<1+1/Real.log X := lt_add_of_pos_right _ (by positivity)
  have hcont := centered_continuous X s _ i j k ω hX hσ
    (OuterBlockCofactorScaleWork.active_lower X s hX hs hlog i j k hk).1
  have hh := ht.2 Y ε (-lowHeight X) (lowHeight X) _ hY hYX hε
    (by have := Real.rpow_nonneg hXp.le (1/1000); dsimp [lowHeight]; linarith) hlen' hcont henergy
  have hn := SpatialErrorBudget.normalize_mean_square _ X _ hXp hh
  simpa only [band,SignedDivisorErrorDecomposition.normalization,show (-(2/5/2):ℝ)= -1/5 by norm_num] using hn

theorem eventually_low_first (s : ℝ) (hs : 0≤s) :
    ∀ᶠ X : ℝ in atTop, Real.exp 1≤X ∧ 2≤X ∧ ∀(Y ε : ℝ) (i j : ℕ) (k : BlockKey) (ω : Fin 9→ℝ),
      k∈activeKeys X s i j → 0<Y → Y<X → ε∈Ioo 0 1 →
      (1/X)*(∫x in Icc X (2*X),‖band X s Y ε (-lowHeight X) (lowHeight X) i j k ω x‖)≤Y*X^(-1/10:ℝ) := by
  filter_upwards [eventually_low_square s hs,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1000000:ℝ))] with X hm hlog
  refine ⟨hm.1,hm.2.1,?_⟩
  intro Y ε i j k ω hk hY hYX hε
  have hXp : 0<X := (Real.exp_pos 1).trans_le hm.1
  have hc := (OuterBandRegularityWork.band_continuous X s Y ε (-lowHeight X) (lowHeight X) i j k ω
    hm.1 hm.2.1 hYX hε (OuterBlockCofactorScaleWork.active_lower X s hm.2.1 hs hlog i j k hk).1).mono
    (show Icc X (2*X)⊆Ioi 0 from fun x hx => hXp.trans_le hx.1)
  have he : (Y*X^(-1/10:ℝ))^2=Y^2*X^(-1/5:ℝ) := by
    rw [mul_pow,←Real.rpow_mul_natCast hXp.le]; norm_num
  have hh := TripleFirstMean.absolute_mean_le
    (fun x => ‖band X s Y ε (-lowHeight X) (lowHeight X) i j k ω x‖)
    X (Y*X^(-1/10:ℝ)) hXp (by positivity)
    (hc.norm.integrableOn_compact isCompact_Icc) ((hc.norm.pow 2).integrableOn_compact isCompact_Icc)
    (by rw [he]; exact hm.2.2 Y ε i j k ω hk hY.le hYX hε)
  simpa only [abs_norm] using hh

theorem eventually_full_low (s : ℝ) (hs : 0≤s) (A : ℕ) :
    ∀ᶠ X : ℝ in atTop, 2≤X ∧ ∀Y ε : ℝ, 0<Y → Y<X → ε∈Ioo 0 1 →
      (1/X)*(∫x in Icc X (2*X),|fullBand X s Y ε (-lowHeight X) (lowHeight X) x|)≤Y/(Real.log X)^A := by
  filter_upwards [eventually_low_first s hs,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1000000:ℝ)),
    PolynomialLogEnvelope.eventually_bound (totalConstant s) (13+A) (1/10)
      (totalConstant_nonneg s) (by norm_num)] with X hm hlog hbudget
  refine ⟨hm.2.1,?_⟩
  intro Y ε hY hYX hε
  have hXp : 0<X := (Real.exp_pos 1).trans_le hm.1
  have hl : 0<Real.log X := by linarith
  have hh := full_mean_le X s Y ε (-lowHeight X) (lowHeight X) (Y*X^(-1/10:ℝ)) hm.1
    hm.2.1 hs hlog hYX hε (by positivity)
    (fun i j k hk ω => hm.2.2 Y ε i j k ω hk hY hYX hε)
  apply hh.trans
  apply (le_div_iff₀ (pow_pos hl A)).mpr
  have hb : totalConstant s*(1+Real.log X)^13*(Real.log X)^A≤X^(1/10:ℝ) := by
    apply le_trans _ hbudget.2
    rw [pow_add,←mul_assoc]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hl.le (by linarith) A)
      (by have := totalConstant_nonneg s; positivity)
  have hp : X^(-1/10:ℝ)*X^(1/10:ℝ)=1 := by rw [←Real.rpow_add hXp]; norm_num
  have hh := mul_le_mul_of_nonneg_left hb (show 0≤Y*X^(-1/10:ℝ) by positivity)
  calc
    _ = (Y*X^(-1/10:ℝ))*(totalConstant s*(1+Real.log X)^13*(Real.log X)^A) := by ring
    _ ≤ (Y*X^(-1/10:ℝ))*X^(1/10:ℝ) := hh
    _ = Y := by rw [mul_assoc,hp,mul_one]

run_cmd do
  for decl in [``lower_lt_upper, ``active_low_energy, ``eventually_low_square,
      ``eventually_low_first, ``eventually_full_low] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end OuterLowFrequencyWork
