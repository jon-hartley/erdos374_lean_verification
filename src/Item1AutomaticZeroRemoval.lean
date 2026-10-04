import Item1DiskBlaschkeProduct
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Meromorphic.IsolatedZeros

/-!
Construct the finite interior-zero data from the actual analytic function.
The canonical decomposition is initially only codiscrete; the proof explicitly
upgrades its equality using meromorphic normal forms before evaluating at zeros.
Boundary zeros stay in the remaining analytic factor. No boundary nonvanishing
or choice of a zero-avoiding radius is imposed.
-/
set_option autoImplicit false
set_option maxHeartbeats 32000000
noncomputable section
open Set Metric Complex Filter Function MeromorphicOn
open scoped BigOperators ComplexConjugate Topology
namespace Item1AutomaticZeroRemoval
open Item1DiskBlaschkeProduct Item1FiniteZeroCharges

/-- The data are CONSTRUCTED below, not input assumptions of the final detectors. -/
structure RemovalData (f : ℂ → ℂ) (R : ℝ) where
  roots : Finset ℂ
  mult : ℂ → ℕ
  remainder : ℂ → ℂ
  root_iff : ∀ a, a ∈ roots ↔ a ∈ ball (0:ℂ) R ∧ f a = 0
  root_ne : ∀ a ∈ roots, a ≠ 0
  mult_pos : ∀ a ∈ roots, 0 < mult a
  mult_exact : ∀ a, (mult a:ℤ) = divisor f (ball (0:ℂ) R) a
  analytic : AnalyticOnNhd ℂ remainder (closedBall 0 R)
  nonzero : ∀ z ∈ ball (0:ℂ) R, remainder z ≠ 0
  identity : EqOn f (fun z => remainder z * product roots mult R z) (closedBall 0 R)

/-- Construct all interior roots, their actual divisor orders, and the regularized
remaining factor. The theorem needs no supplied root list or growth of a quotient. -/
theorem exists_removal_data (f : ℂ → ℂ) (R : ℝ) (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R)) (hf0 : f 0 ≠ 0) :
    Nonempty (RemovalData f R) := by
  classical
  have h0 : (0:ℂ) ∈ closedBall 0 R := by simpa using hR.le
  have hfNT : ∀ z : closedBall (0:ℂ) R, meromorphicOrderAt f z ≠ ⊤ := by
    apply (hf.meromorphicOn.exists_meromorphicOrderAt_ne_top_iff_forall
      (Metric.isConnected_closedBall hR.le)).mp
    refine ⟨⟨0,h0⟩,?_⟩
    have hz := (hf 0 h0).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr hf0
    simp [hz]
  obtain ⟨g, hg⟩ := hf.meromorphicOn.exists_canonicalDecomp hfNT
  have hfball : AnalyticOnNhd ℂ f (ball 0 R) := hf.mono ball_subset_closedBall
  let dv := divisor f (ball (0:ℂ) R)
  have hfinite : dv.support.Finite := hf.meromorphicOn.divisor_ball_support_finite
  let S : Finset ℂ := hfinite.toFinset
  let m : ℂ → ℕ := fun a => (dv a).toNat
  have hnonneg : ∀ a, 0 ≤ dv a := hfball.divisor_nonneg
  have hmcast (a : ℂ) : (m a:ℤ) = dv a := Int.toNat_of_nonneg (hnonneg a)
  have hzeros := hfball.meromorphicNFOn.zero_set_eq_divisor_support
    (fun z => hfNT ⟨z,ball_subset_closedBall z.property⟩)
  have hroot (a : ℂ) : a ∈ S ↔ a ∈ ball (0:ℂ) R ∧ f a = 0 := by
    change a ∈ hfinite.toFinset ↔ _
    rw [Set.Finite.mem_toFinset]
    change a ∈ Function.support (divisor f (ball (0:ℂ) R)) ↔ _
    rw [←hzeros]
    rfl
  have hne (a : ℂ) (ha : a ∈ S) : a ≠ 0 := by
    intro he
    subst a
    exact hf0 ((hroot 0).mp ha).2
  have hinside (a : ℂ) (ha : a ∈ S) : ‖a‖ < R := by
    simpa using ((hroot a).mp ha).1
  have hmpos (a : ℂ) (ha : a ∈ S) : 0 < m a := by
    have hda : dv a ≠ 0 := by
      have hs : a ∈ dv.support := hfinite.mem_toFinset.mp ha
      exact hs
    have hdp : 0 < dv a := lt_of_le_of_ne (hnonneg a) (Ne.symm hda)
    exact Int.pos_iff_toNat_pos.mp hdp
  have hga : AnalyticOnNhd ℂ g (closedBall 0 R) := by
    apply hg.meromorphicNFOn.divisor_nonneg_iff_analyticOnNhd.mp
    intro a
    rw [hg.divisor_eq_divisor hR]
    exact (hf.mono sphere_subset_closedBall).divisor_nonneg a
  have hprod : (∏ᶠ a, canonicalFactor R a ^ (-dv a)) = product S m R := by
    have hsupp : Function.mulSupport (fun a => canonicalFactor R a ^ (-dv a)) ⊆
        (S:Set ℂ) := by
      intro a ha
      by_contra has
      have hda : dv a = 0 := by
        by_contra hd
        exact has (hfinite.mem_toFinset.mpr hd)
      exact ha (by simp [hda])
    rw [finprod_eq_prod_of_mulSupport_subset _ hsupp]
    funext z
    simp only [Finset.prod_apply, Pi.pow_apply, product]
    apply Finset.prod_congr rfl
    intro a _
    rw [←hmcast a, zpow_neg, zpow_natCast, ←inv_pow, reciprocal_canonical]
  have he : f =ᶠ[codiscreteWithin (closedBall (0:ℂ) R)]
      (fun z => g z * product S m R z) := by
    have hh := hg.eventuallyEq
    change f =ᶠ[codiscreteWithin (closedBall (0:ℂ) R)]
      (∏ᶠ a, canonicalFactor R a ^ (-dv a)) • g at hh
    rw [hprod] at hh
    filter_upwards [hh] with z hz
    simpa only [Pi.smul_apply', smul_eq_mul, mul_comm] using hz
  have hbprod := product_analytic_closed S m R hR hinside
  have hright : AnalyticOnNhd ℂ (fun z => g z * product S m R z)
      (closedBall 0 R) := by
    intro z hz
    exact (hga z hz).mul (hbprod z hz)
  have hperfect : Preperfect (closedBall (0:ℂ) R) := by
    rw [←closure_ball 0 hR.ne']
    exact isOpen_ball.perfect_closure.2
  have hevery : EqOn f (fun z => g z * product S m R z) (closedBall 0 R) := by
    intro z hz
    have hpunct := MeromorphicAt.eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin_preperfect
      (hf z hz).meromorphicAt (hright z hz).meromorphicAt hz hperfect he
    have hn := ((hf z hz).meromorphicNFAt.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds
      (hright z hz).meromorphicNFAt).mp hpunct
    exact hn.eq_of_nhds
  exact ⟨{
    roots := S, mult := m, remainder := g,
    root_iff := hroot, root_ne := hne, mult_pos := hmpos, mult_exact := hmcast,
    analytic := hga, nonzero := hg.ne_zero, identity := hevery
  }⟩

/-- The maximum principle transfers the ACTUAL f-bound. Only the original
function's boundary bound is requested; boundary zeros of the remainder are legal. -/
theorem RemovalData.remaining_growth {f : ℂ → ℂ} {R M : ℝ}
    (D : RemovalData f R) (hR : 0 < R)
    (hb : ∀ z ∈ sphere (0:ℂ) R, ‖f z‖ ≤ Real.exp M * ‖f 0‖) :
    ∀ z ∈ ball (0:ℂ) R, ‖D.remainder z‖ ≤ Real.exp M * ‖D.remainder 0‖ := by
  have h0 : (0:ℂ) ∈ closedBall 0 R := by simpa using hR.le
  have hi (a : ℂ) (ha : a ∈ D.roots) : ‖a‖ < R := by
    simpa using ((D.root_iff a).mp ha).1
  have hcenter : ‖f 0‖ ≤ ‖D.remainder 0‖ := by
    rw [D.identity h0, norm_mul]
    exact (mul_le_mul_of_nonneg_left
      (product_norm_center_le_one D.roots D.mult R hR hi)
      (norm_nonneg _)).trans_eq (mul_one _)
  have hboundary : ∀ z ∈ sphere (0:ℂ) R,
      ‖D.remainder z‖ ≤ Real.exp M * ‖D.remainder 0‖ := by
    intro z hz
    have he := congrArg norm (D.identity (sphere_subset_closedBall hz))
    rw [norm_mul, product_norm_boundary D.roots D.mult R hi z (by simpa using hz),
      mul_one] at he
    rw [←he]
    exact (hb z hz).trans (mul_le_mul_of_nonneg_left hcenter (Real.exp_pos M).le)
  have hd : DiffContOnCl ℂ D.remainder (ball 0 R) := by
    apply DiffContOnCl.mk_ball
    · exact (D.analytic.mono ball_subset_closedBall).differentiableOn
    · exact D.analytic.continuousOn
  intro z hz
  apply Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hd
  · simpa only [frontier_ball (0:ℂ) hR.ne'] using hboundary
  · simpa only [closure_ball (0:ℂ) hR.ne'] using ball_subset_closedBall hz

/-- Exact detector sum for data already constructed by exists_removal_data. -/
theorem RemovalData.detector_sum {f : ℂ → ℂ} {R M : ℝ}
    (D : RemovalData f R) (hR : 0 < R) (hM : 0 < M)
    (hb : ∀ z ∈ sphere (0:ℂ) R, ‖f z‖ ≤ Real.exp M * ‖f 0‖) :
    -(logDeriv f 0).re ≤ 4*M/R -
      ∑ a ∈ D.roots, (D.mult a:ℝ)*charge R a := by
  have h0 : (0:ℂ) ∈ ball 0 R := by simpa using hR
  have hclosed : (0:ℂ) ∈ closedBall 0 R := ball_subset_closedBall h0
  have hnear : f =ᶠ[𝓝 0] (fun z => D.remainder z*product D.roots D.mult R z) := by
    filter_upwards [isOpen_ball.mem_nhds h0] with z hz
    exact D.identity (ball_subset_closedBall hz)
  have he := (logDeriv_congr_nhds hnear).eq_of_nhds
  have hgd : DifferentiableAt ℂ D.remainder 0 := (D.analytic 0 hclosed).differentiableAt
  have hpd : DifferentiableAt ℂ (product D.roots D.mult R) 0 :=
    ((product_analytic_closed D.roots D.mult R hR (fun a ha => by
      simpa using ((D.root_iff a).mp ha).1)) 0 hclosed).differentiableAt
  rw [he, logDeriv_fun_mul 0 (D.nonzero 0 h0)
    (product_center_ne_zero D.roots D.mult R hR.ne' D.root_ne) hgd hpd,
    Complex.add_re, product_logDeriv_re D.roots D.mult R hR.ne' D.root_ne]
  have hbound := Item1CenterLogBound.center_logDeriv_bound D.remainder R M hR hM
    (D.analytic.mono ball_subset_closedBall).differentiableOn D.nonzero
    (D.remaining_growth hR hb)
  have hn : -(logDeriv D.remainder 0).re ≤ ‖logDeriv D.remainder 0‖ :=
    (neg_le_abs _).trans (Complex.abs_re_le_norm _)
  linarith

/-- Automatic local upper bound. No zero list, remaining factor, or radius choice. -/
theorem automatic_upper (f : ℂ → ℂ) (R M : ℝ) (hR : 0 < R) (hM : 0 < M)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R)) (hf0 : f 0 ≠ 0)
    (hb : ∀ z ∈ sphere (0:ℂ) R, ‖f z‖ ≤ Real.exp M * ‖f 0‖)
    (hleft : ∀ z ∈ ball (0:ℂ) R, f z = 0 → z.re ≤ 0) :
    -(logDeriv f 0).re ≤ 4*M/R := by
  obtain ⟨D⟩ := exists_removal_data f R hR hf hf0
  have hsum : 0 ≤ ∑ a ∈ D.roots, (D.mult a:ℝ)*charge R a := by
    apply Finset.sum_nonneg
    intro a ha
    have hra := (D.root_iff a).mp ha
    have han : 0 < ‖a‖ := norm_pos_iff.mpr (D.root_ne a ha)
    have har : ‖a‖ < R := by simpa using hra.1
    have hp : 0 < normSq a := by rw [normSq_eq_norm_sq]; positivity
    have hpr : normSq a ≤ R^2 := by rw [normSq_eq_norm_sq]; nlinarith
    exact mul_nonneg (Nat.cast_nonneg _) (charge_nonneg R a hR hp hpr (hleft a hra.1 hra.2))
  linarith [D.detector_sum hR hM hb]

/-- Automatic single-zero detector, retaining multiplicity and q/R^2.
There is deliberately no assumption that f or its remainder is nonzero on the sphere. -/
theorem automatic_one_zero (f : ℂ → ℂ) (R M q : ℝ)
    (hR : 0 < R) (hM : 0 < M) (hq : 0 < q) (hqR : q < R)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R)) (hf0 : f 0 ≠ 0)
    (hb : ∀ z ∈ sphere (0:ℂ) R, ‖f z‖ ≤ Real.exp M * ‖f 0‖)
    (hleft : ∀ z ∈ ball (0:ℂ) R, f z = 0 → z.re ≤ 0)
    (hzero : f (-(q:ℂ)) = 0) :
    -(logDeriv f 0).re ≤ 4*M/R - 1/q + q/R^2 := by
  obtain ⟨D⟩ := exists_removal_data f R hR hf hf0
  have hcharge (a : ℂ) (ha : a ∈ D.roots) : 0 ≤ charge R a := by
    have hra := (D.root_iff a).mp ha
    have han : 0 < ‖a‖ := norm_pos_iff.mpr (D.root_ne a ha)
    have har : ‖a‖ < R := by simpa using hra.1
    apply charge_nonneg R a hR
    · rw [normSq_eq_norm_sq]; positivity
    · rw [normSq_eq_norm_sq]; nlinarith
    · exact hleft a hra.1 hra.2
  have hroot : -(q:ℂ) ∈ D.roots := (D.root_iff _).mpr ⟨by simpa [abs_of_pos hq] using hqR, hzero⟩
  have hm : (1:ℝ) ≤ D.mult (-(q:ℂ)) := by
    exact_mod_cast Nat.succ_le_of_lt (D.mult_pos _ hroot)
  have hsingle : charge R (-(q:ℂ)) ≤
      ∑ a ∈ D.roots, (D.mult a:ℝ)*charge R a := by
    calc
      _ ≤ (D.mult (-(q:ℂ)):ℝ)*charge R (-(q:ℂ)) := by
        nlinarith [hcharge _ hroot]
      _ ≤ _ := Finset.single_le_sum (fun a ha =>
        mul_nonneg (Nat.cast_nonneg _) (hcharge a ha)) hroot
  rw [aligned_charge R q hR.ne' hq.ne'] at hsingle
  linarith [D.detector_sum hR hM hb]

end Item1AutomaticZeroRemoval

run_cmd do
  for target in [``Item1AutomaticZeroRemoval.exists_removal_data,
    ``Item1AutomaticZeroRemoval.RemovalData.remaining_growth,
    ``Item1AutomaticZeroRemoval.RemovalData.detector_sum,
    ``Item1AutomaticZeroRemoval.automatic_upper,
    ``Item1AutomaticZeroRemoval.automatic_one_zero] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"

#print axioms Item1AutomaticZeroRemoval.exists_removal_data
#print axioms Item1AutomaticZeroRemoval.automatic_one_zero
