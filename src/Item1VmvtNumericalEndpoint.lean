import Item1VmvtSummit2
import Item1VmvtCollisionBridge
import Item1PrefixNumericalReduction

/-! The genuine VMVT bound replaces both collision factors in the explicit
numerical reduction of logarithmic prefixes. The second set may contain zero;
its interval bound then uses Bmax+1. No cancellation estimate for the remaining
coefficient-dependent numerical product is asserted here. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open scoped BigOperators

namespace Item1VmvtNumericalEndpoint
open Item1FiniteAbelPhase Item1LongLogPhase Item1LogPhasePolynomialReduction
open Item1ProductPrefixMoment Item1DifferenceBoxMajorant Item1PrefixNumericalReduction
open Item1VmvtCollisionBridge

/-- The first collision factor, with tuple length d*R, satisfies the actual
VMVT estimate on the positive interval 1,...,A. -/
theorem firstCollision_le_vmvt (d R A : ℕ) (hd : 2 ≤ d) (hR : 1 ≤ R)
    (hA : 1 ≤ A) :
    J d (d*R) A ≤ Salt.Vmvt.vmvtConst d R * (A:ℝ) ^ Salt.Vmvt.vmvtExp d R := by
  rw [firstCollision_eq_JkI]
  exact Salt.Vmvt.vmvt d R A hd hR hA

/-- The second collision factor allows zero in B. Translation by one places
the integer image in 1,...,Bmax+1 without changing its exact collision count. -/
theorem secondCollision_le_vmvt_succ (B : Finset ℕ) (d S Bmax : ℕ)
    (hd : 2 ≤ d) (hS : 1 ≤ S) (hB : ∀ b ∈ B, b ≤ Bmax) :
    secondCollisionCount d (d*S) (fun b : B => (b.val:ℤ)) ≤
      Salt.Vmvt.vmvtConst d S * ((Bmax+1:ℕ):ℝ) ^ Salt.Vmvt.vmvtExp d S := by
  exact (secondCollisionCount_le_JkI_succ B d (d*S) Bmax hB).trans
    (Salt.Vmvt.vmvt d S (Bmax+1) hd hS (by omega))

/-- If B is positive, the sharper interval endpoint Bmax is available. -/
theorem secondCollision_le_vmvt_of_positive (B : Finset ℕ) (d S Bmax : ℕ)
    (hd : 2 ≤ d) (hS : 1 ≤ S) (hBmax : 1 ≤ Bmax)
    (hpos : ∀ b ∈ B, 1 ≤ b) (hB : ∀ b ∈ B, b ≤ Bmax) :
    secondCollisionCount d (d*S) (fun b : B => (b.val:ℤ)) ≤
      Salt.Vmvt.vmvtConst d S * (Bmax:ℝ) ^ Salt.Vmvt.vmvtExp d S := by
  exact (secondCollisionCount_le_JkI_of_positive B d (d*S) Bmax hpos hB).trans
    (Salt.Vmvt.vmvt d S Bmax hd hS hBmax)

/-- The original prefix estimate and every Taylor-sum moment, with both
collision counts replaced by explicit VMVT factors. The arithmetic product
retains the actual logarithmic phase coefficients. -/
theorem prefix_and_vmvt_numerical_even_moments (B : Finset ℕ) (hBne : B.Nonempty)
    (d M K A Bmax R S : ℕ) (t : ℝ) (hd : 2 ≤ d) (hM : 1 ≤ M) (hA : 1 ≤ A)
    (hB : ∀ b ∈ B, b ≤ Bmax) (hhalf : 2*(A*Bmax) ≤ M)
    (hR : 1 ≤ R) (hS : 1 ≤ S) :
    (‖«prefix» (atom M t) K‖ ≤
      (1/((A:ℝ)*(B.card:ℝ)))*(∑ n ∈ Finset.range K, ‖U B d A ((M:ℝ)+n) t‖)+
      (K:ℝ)*(2*|t| *((((A*Bmax:ℕ):ℝ))/M)^(d+1))+
      2*(A:ℝ)*(Bmax:ℝ)) ∧
    ∀ n : ℕ, ‖U B d A ((M:ℝ)+n) t‖^(2*(d*R)*(d*S)) ≤
      (B.card:ℝ)^(2*(d*R)*(d*S)-2*(d*S)) *
      (A:ℝ)^(2*(d*R)*(d*S)-2*(d*R)) *
      (Salt.Vmvt.vmvtConst d R * (A:ℝ) ^ Salt.Vmvt.vmvtExp d R) *
      (Salt.Vmvt.vmvtConst d S * ((Bmax+1:ℕ):ℝ) ^ Salt.Vmvt.vmvtExp d S) *
      numericalProduct d (d*R) (d*S) A Bmax
        (fun j : Fin d => phaseCoefficient ((M:ℝ)+n) t j.val) := by
  have hr : 1 ≤ d*R := by
    have h := Nat.mul_le_mul (show 1 ≤ d by omega) hR
    simpa only [one_mul] using h
  have hs : 1 ≤ d*S := by
    have h := Nat.mul_le_mul (show 1 ≤ d by omega) hS
    simpa only [one_mul] using h
  obtain ⟨hprefix, hmoment⟩ := prefix_and_numerical_even_moments
    B hBne d M K A Bmax (d*R) (d*S) t hM hA hB hhalf hr hs
  refine ⟨hprefix, ?_⟩
  have hfirst := firstCollision_le_vmvt d R A hd hR hA
  have hsecond := secondCollision_le_vmvt_succ B d S Bmax hd hS hB
  have hJ : 0 ≤ J d (d*R) A := by unfold J; positivity
  have hJB : 0 ≤ secondCollisionCount d (d*S) (fun b : B => (b.val:ℤ)) := by
    unfold secondCollisionCount
    positivity
  have hpair := mul_le_mul hfirst hsecond hJB (hJ.trans hfirst)
  intro n
  have hcoeff : 0 ≤
      (B.card:ℝ)^(2*(d*R)*(d*S)-2*(d*S)) *
      (A:ℝ)^(2*(d*R)*(d*S)-2*(d*R)) := by positivity
  have hnum := numericalProduct_nonneg d (d*R) (d*S) A Bmax
    (fun j : Fin d => phaseCoefficient ((M:ℝ)+n) t j.val)
  have hmajor := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hpair hcoeff) hnum
  exact (hmoment n).trans (by simpa only [mul_assoc] using hmajor)

/-- The parameter-facing variant for a positive finite set B. Both VMVT
interval scales remain A and Bmax, preserving the exact prefactor powers. -/
theorem prefix_and_vmvt_numerical_even_moments_of_positive (B : Finset ℕ) (hBne : B.Nonempty)
    (d M K A Bmax R S : ℕ) (t : ℝ) (hd : 2 ≤ d) (hM : 1 ≤ M) (hA : 1 ≤ A)
    (hBmax : 1 ≤ Bmax) (hpos : ∀ b ∈ B, 1 ≤ b)
    (hB : ∀ b ∈ B, b ≤ Bmax) (hhalf : 2*(A*Bmax) ≤ M)
    (hR : 1 ≤ R) (hS : 1 ≤ S) :
    (‖«prefix» (atom M t) K‖ ≤
      (1/((A:ℝ)*(B.card:ℝ)))*(∑ n ∈ Finset.range K, ‖U B d A ((M:ℝ)+n) t‖)+
      (K:ℝ)*(2*|t| *((((A*Bmax:ℕ):ℝ))/M)^(d+1))+
      2*(A:ℝ)*(Bmax:ℝ)) ∧
    ∀ n : ℕ, ‖U B d A ((M:ℝ)+n) t‖^(2*(d*R)*(d*S)) ≤
      (B.card:ℝ)^(2*(d*R)*(d*S)-2*(d*S)) *
      (A:ℝ)^(2*(d*R)*(d*S)-2*(d*R)) *
      (Salt.Vmvt.vmvtConst d R * (A:ℝ) ^ Salt.Vmvt.vmvtExp d R) *
      (Salt.Vmvt.vmvtConst d S * (Bmax:ℝ) ^ Salt.Vmvt.vmvtExp d S) *
      numericalProduct d (d*R) (d*S) A Bmax
        (fun j : Fin d => phaseCoefficient ((M:ℝ)+n) t j.val) := by
  have hr : 1 ≤ d*R := by
    have h := Nat.mul_le_mul (show 1 ≤ d by omega) hR
    simpa only [one_mul] using h
  have hs : 1 ≤ d*S := by
    have h := Nat.mul_le_mul (show 1 ≤ d by omega) hS
    simpa only [one_mul] using h
  obtain ⟨hprefix, hmoment⟩ := prefix_and_numerical_even_moments
    B hBne d M K A Bmax (d*R) (d*S) t hM hA hB hhalf hr hs
  refine ⟨hprefix, ?_⟩
  have hfirst := firstCollision_le_vmvt d R A hd hR hA
  have hsecond := secondCollision_le_vmvt_of_positive B d S Bmax hd hS hBmax hpos hB
  have hJ : 0 ≤ J d (d*R) A := by unfold J; positivity
  have hJB : 0 ≤ secondCollisionCount d (d*S) (fun b : B => (b.val:ℤ)) := by
    unfold secondCollisionCount
    positivity
  have hpair := mul_le_mul hfirst hsecond hJB (hJ.trans hfirst)
  intro n
  have hcoeff : 0 ≤
      (B.card:ℝ)^(2*(d*R)*(d*S)-2*(d*S)) *
      (A:ℝ)^(2*(d*R)*(d*S)-2*(d*R)) := by positivity
  have hnum := numericalProduct_nonneg d (d*R) (d*S) A Bmax
    (fun j : Fin d => phaseCoefficient ((M:ℝ)+n) t j.val)
  have hmajor := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hpair hcoeff) hnum
  exact (hmoment n).trans (by simpa only [mul_assoc] using hmajor)

end Item1VmvtNumericalEndpoint

run_cmd do
  for target in [``Item1VmvtNumericalEndpoint.firstCollision_le_vmvt,
      ``Item1VmvtNumericalEndpoint.secondCollision_le_vmvt_succ,
      ``Item1VmvtNumericalEndpoint.secondCollision_le_vmvt_of_positive,
      ``Item1VmvtNumericalEndpoint.prefix_and_vmvt_numerical_even_moments,
      ``Item1VmvtNumericalEndpoint.prefix_and_vmvt_numerical_even_moments_of_positive] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "VMVT NUMERICAL ENDPOINT: 5 standard-axiom theorem guards passed."
