import TailErdosClosure
import MomentRemainderBand

/-! The one-sided first-moment target can be restricted to the same actual
high-index band as the old second-moment target. The small-index contribution
is discharged unconditionally. The high negative-part mean remains open. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open Filter MeasureTheory Set
namespace TailRemainderBand
open MomentSmallRemainder MomentSmallMean TailRemainderMean PositiveSharpPowerWindow
open PositiveSharpRemainderRegularity CancellationTransferCenter

def highNegativeMean (X s a Y : ℝ) : ℝ :=
  (∫x in Icc X (2*X), max (-high X s a x (x*Y/X)) 0)/X

def lowAbsoluteMean (X s a Y : ℝ) : ℝ :=
  (∫x in Icc X (2*X), |low X s a x (x*Y/X)|)/X

theorem moving_remainder_integrable (S : Finset ℕ) (w : ℕ→ℝ) (X Y : ℝ) :
    IntegrableOn (fun x => HarmanDivisorWindow.remainder S w (x-x*Y/X) x)
      (Icc X (2*X)) := by
  have hi := MemLp.integrable (by norm_num : (1:ENNReal)≤2)
    (scaled_remainder_memLp S w (1-Y/X) 1 X)
  have he (x:ℝ) : (1-Y/X)*x=x-x*Y/X := by ring
  change Integrable (fun x => HarmanDivisorWindow.remainder S w (x-x*Y/X) x)
    (volume.restrict (Icc X (2*X)))
  simpa only [he,one_mul] using hi

theorem low_integrable (X s a Y : ℝ) :
    IntegrableOn (fun x => low X s a x (x*Y/X)) (Icc X (2*X)) :=
  moving_remainder_integrable _ _ _ _

theorem high_integrable (X s a Y : ℝ) :
    IntegrableOn (fun x => high X s a x (x*Y/X)) (Icc X (2*X)) :=
  moving_remainder_integrable _ _ _ _

theorem negativeMean_le_low_add_high (X s a Y : ℝ) (hX : 0≤X) :
    negativeMean X s Y≤lowAbsoluteMean X s a Y+highNegativeMean X s a Y := by
  have hb := setIntegral_mono_on (signedRemainder_integrable X s Y).neg_part
    ((low_integrable X s a Y).abs.add (high_integrable X s a Y).neg_part)
    measurableSet_Icc (fun x (_hx:x∈Icc X (2*X)) => by
      change max (-PositiveSharpBoxedCount.signedRemainder X s x (x*Y/X)) 0≤
        |low X s a x (x*Y/X)|+max (-high X s a x (x*Y/X)) 0
      rw [split]
      apply max_le
      · linarith [neg_le_abs (low X s a x (x*Y/X)),
          le_max_left (-high X s a x (x*Y/X)) 0]
      · positivity)
  simp only [Pi.add_apply] at hb
  rw [integral_add (low_integrable X s a Y).abs (high_integrable X s a Y).neg_part] at hb
  unfold negativeMean lowAbsoluteMean highNegativeMean
  rw [←add_div]
  exact div_le_div_of_nonneg_right hb hX

theorem eventually_low_absolute_mean (s a β : ℝ) (A : ℕ)
    (hs : 0<s) (hs1 : s≤1/1000) (haβ : a<β) (hβ : β<1) :
    ∀ᶠ X:ℝ in atTop, 1<X ∧
      lowAbsoluteMean X s a (halfWidth X β)≤halfWidth X β/(Real.log X)^A := by
  filter_upwards [eventually_low_square s a β (2*A) hs hs1 haβ,
    halfWidth_eventually β hβ] with X hb hw
  have hX : 0<X := by linarith [hb.1]
  have hl : 0<Real.log X := Real.log_pos hb.1
  have hYX : halfWidth X β≤X := by linarith [hw.2]
  have hpoint : ∀x∈Icc X (2*X), |low X s a x (x*halfWidth X β/X)|≤
      halfWidth X β/(Real.log X)^A := by
    intro x hx
    have hxy : x*halfWidth X β/X≤x :=
      (div_le_iff₀ hX).mpr (mul_le_mul_of_nonneg_left hYX (hX.le.trans hx.1))
    have hh := hb.2 x _ (hX.le.trans hx.1) hxy
    have he : ((halfWidth X β)/(Real.log X)^A)^2=
        (X^β/2)^2/(Real.log X)^(2*A) := by
      rw [div_pow,←pow_mul,Nat.mul_comm A 2]
      rfl
    apply (sq_le_sq₀ (abs_nonneg _) (div_nonneg hw.1.le (pow_pos hl A).le)).mp
    rw [sq_abs,he]
    exact hh
  have hc : IntegrableOn (fun _ : ℝ => halfWidth X β/(Real.log X)^A) (Icc X (2*X)) :=
    continuousOn_const.integrableOn_compact isCompact_Icc
  have hm := setIntegral_mono_on (low_integrable X s a (halfWidth X β)).abs hc
    measurableSet_Icc hpoint
  rw [setIntegral_const,Real.volume_real_Icc_of_le (by linarith : X≤2*X),smul_eq_mul] at hm
  refine ⟨hb.1,(div_le_iff₀ hX).mpr ?_⟩
  exact hm.trans_eq (by ring)

theorem eventually_full_negative_of_high (s a β C : ℝ) (A : ℕ)
    (hs : 0<s) (hs1 : s≤1/1000) (haβ : a<β) (hβ : β<1)
    (hhigh : ∀ᶠ X:ℝ in atTop,
      highNegativeMean X s a (halfWidth X β)≤C*halfWidth X β/(Real.log X)^A) :
    ∀ᶠ X:ℝ in atTop,
      negativeMean X s (halfWidth X β)≤(C+1)*halfWidth X β/(Real.log X)^A := by
  filter_upwards [eventually_low_absolute_mean s a β A hs hs1 haβ hβ,hhigh] with X hl hh
  have he : (C+1)*halfWidth X β/(Real.log X)^A=
      halfWidth X β/(Real.log X)^A+C*halfWidth X β/(Real.log X)^A := by ring
  rw [he]
  exact (negativeMean_le_low_add_high X s a (halfWidth X β) (by linarith [hl.1])).trans
    (add_le_add hl.2 hh)

theorem eventually_erdos_conclusions_of_source_and_high_negative_mean :
    ∃s₀:ℝ, 0<s₀ ∧ s₀≤1/1000 ∧ ∀s:ℝ, 0<s → s<s₀ →
      ∀C_E C_N:ℝ,
      (∀ᶠ X:ℝ in atTop,
        (∫x in Icc X (2*X), sourceResidualAbs X x (x*halfWidth X (101/1000)/X))/X≤
          C_E/(Real.log X)^2) →
      (∀ᶠ X:ℝ in atTop,
        highNegativeMean X s (1/10) (halfWidth X (101/1000))≤
          C_N*halfWidth X (101/1000)/(Real.log X)^2) →
      Erdos374.MainStatement ∧
      Erdos374.PositiveLowerDensity LiteratureReduction.MinimumSix ∧
      ∃c:ℝ, 0<c ∧ ∃cutoff:ℕ, ∀N:ℕ, cutoff≤N →
        c*(N:ℝ)≤(Erdos374.prefixCount LiteratureReduction.MinimumSix N:ℝ) := by
  obtain ⟨s₀,hs₀,hs1,hp⟩ := TailErdosClosure.eventually_erdos_conclusions_of_source_and_negative_mean
  refine ⟨s₀,hs₀,hs1,?_⟩
  intro s hs hss C_E C_N hE hN
  apply hp s hs hss C_E (C_N+1) hE
  exact eventually_full_negative_of_high s (1/10) (101/1000) C_N 2 hs
    (hss.le.trans hs1) (by norm_num) (by norm_num) hN

run_cmd do
  for decl in [``highNegativeMean,``lowAbsoluteMean,``moving_remainder_integrable,
      ``low_integrable,``high_integrable,``negativeMean_le_low_add_high,
      ``eventually_low_absolute_mean,``eventually_full_negative_of_high,
      ``eventually_erdos_conclusions_of_source_and_high_negative_mean] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "SMALL FIRST MOMENT DISCHARGED; ERDOS REDUCED TO SOURCE RESIDUAL AND HIGH NEGATIVE FIRST MEAN"
end TailRemainderBand
end
