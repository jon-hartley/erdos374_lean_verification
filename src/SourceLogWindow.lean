import SourceWindowGeometry
import SourceRawMean
import SourceLiteralMass

/-! v7. An ordinary-function representation of the exact centered source window.
UNCOMPILED DRAFT. This proves finite physical identities, not Fourier inversion.
The continuous profile remains clipped outside [X,2X]. No signed-measure
Fourier API, new analytic axiom, or purported full source mean is introduced. -/
set_option autoImplicit false
set_option maxHeartbeats 16000000
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace SourceLogWindow
open SourceWindowGeometry SourceLiteralMoments SourceLiteralMass
open PositiveInteriorModel PositiveSharpCounts CancellationTransferEndpoints
open CancellationTransferCenter

def kernel (ρ u : ℝ) : ℝ :=
  if 0≤u ∧ u< -Real.log ρ then Real.exp (-u) else 0

def continuousProfile (ρ a b u : ℝ) : ℝ :=
  Real.exp (-u)*referenceLength a b (ρ*Real.exp u) (Real.exp u)

theorem log_window_iff (ρ x v : ℝ) (hρ : 0<ρ) (hx : 0<x) (hv : 0<v) :
    (0≤Real.log x-Real.log v ∧ Real.log x-Real.log v< -Real.log ρ) ↔
      ρ*x<v ∧ v≤x := by
  have hlo : Real.log v≤Real.log x ↔ v≤x := Real.log_le_log_iff hv hx
  have hhi : Real.log (ρ*x)<Real.log v ↔ ρ*x<v :=
    Real.log_lt_log_iff (mul_pos hρ hx) hv
  rw [Real.log_mul hρ.ne' hx.ne'] at hhi
  constructor
  · rintro ⟨ha,hb⟩
    exact ⟨hhi.mp (by linarith),hlo.mp (by linarith)⟩
  · rintro ⟨ha,hb⟩
    have hla := hhi.mpr ha
    have hlb := hlo.mpr hb
    constructor <;> linarith

/-- The left physical endpoint is strict; the right endpoint is closed. -/
theorem atom_identity (ρ x v : ℝ) (hρ : 0<ρ) (hx : 0<x) (hv : 0<v) :
    kernel ρ (Real.log x-Real.log v)/v =
      (if ρ*x<v ∧ v≤x then 1 else 0)/x := by
  have hi := log_window_iff ρ x v hρ hx hv
  have he : Real.exp (-(Real.log x-Real.log v))=v/x := by
    rw [neg_sub,Real.exp_sub,Real.exp_log hv,Real.exp_log hx]
  unfold kernel
  simp only [hi]
  split_ifs with ht
  · rw [he]
    field_simp
  · simp

/-- The continuous profile after translation; no support approximation is made. -/
theorem continuous_translate (ρ a b x d : ℝ) (hx : 0<x) (hd : 0<d) :
    continuousProfile ρ a b (Real.log x-Real.log d)/d =
      referenceLength a b (ρ*x/d) (x/d)/x := by
  have he : Real.exp (Real.log x-Real.log d)=x/d := by
    rw [Real.exp_sub,Real.exp_log hx,Real.exp_log hd]
  have hn : Real.exp (-(Real.log x-Real.log d))=d/x := by
    rw [neg_sub,Real.exp_sub,Real.exp_log hd,Real.exp_log hx]
  unfold continuousProfile
  rw [he,hn]
  have harg : ρ*(x/d)=ρ*x/d := by ring
  rw [harg]
  field_simp <;> ring

def discreteProfile (X : ℝ) (j : ℕ × ℕ) (ρ u : ℝ) : ℝ :=
  ∑ k∈sourceCoordinates X j,
    tripleWeight k*(kernel ρ (u-Real.log (tripleProduct k))/tripleProduct k)

def referenceProfile (X : ℝ) (j : ℕ × ℕ) (ρ u : ℝ) : ℝ :=
  ∑ p∈support X j 0, ∑ r∈support X j 1,
    ArithmeticFunction.vonMangoldt p*ArithmeticFunction.vonMangoldt r*
      (continuousProfile ρ (thirdScale X j/8) (4*thirdScale X j)
        (u-Real.log ((p:ℝ)*(r:ℝ)))/((p:ℝ)*(r:ℝ)))

def centeredProfile (X : ℝ) (j : ℕ × ℕ) (ρ u : ℝ) : ℝ :=
  discreteProfile X j ρ u-referenceProfile X j ρ u

theorem triple_positive (X : ℝ) (j : ℕ × ℕ) (k : Triple)
    (hk : k∈sourceCoordinates X j) : 0<tripleProduct k := by
  rw [sourceCoordinates_eq] at hk
  obtain ⟨hp,hrq⟩ := Finset.mem_product.mp hk
  obtain ⟨hr,hq⟩ := Finset.mem_product.mp hrq
  have hp0 := support_pos X j 0 k.1 hp
  have hr0 := support_pos X j 1 k.2.1 hr
  have hq0 := support_pos X j 2 k.2.2 hq
  dsimp [tripleProduct]
  positivity

theorem discrete_eq_count (X x Y : ℝ) (j : ℕ × ℕ)
    (_hX : 0<X) (hx : 0<x) (hρ : 0<1-Y/X) :
    discreteProfile X j (1-Y/X) (Real.log x)=sourceCount X j x (x*Y/X)/x := by
  unfold discreteProfile sourceCount
  rw [Finset.sum_div]
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro k hk
  rw [atom_identity (1-Y/X) x (tripleProduct k) hρ hx (triple_positive X j k hk)]
  have he : (1-Y/X)*x=x-x*Y/X := by ring
  rw [he]
  dsimp [inWindow]
  split_ifs <;> ring

theorem reference_eq_center (X x Y : ℝ) (j : ℕ × ℕ)
    (hX : 0<X) (hx : x∈Icc X (2*X)) (hY : 0≤Y) (hYX : Y≤X/2) :
    referenceProfile X j (1-Y/X) (Real.log x)=
      (Y/X)*sourceMass j.1*sourceMass j.2 := by
  have hxp : 0<x := hX.trans_le hx.1
  have hP : 0<scale j.1 := by unfold scale; positivity
  have hR : 0<scale j.2 := by unfold scale; positivity
  have hL : 0<thirdScale X j := by unfold thirdScale; positivity
  have hid : scale j.1*scale j.2*thirdScale X j=X := by
    unfold thirdScale
    field_simp
  have hd : 0≤Y/X ∧ Y/X≤1/2 :=
    ⟨div_nonneg hY hX.le,(div_le_iff₀ hX).mpr (by linarith)⟩
  unfold referenceProfile
  have hterm (p : ℕ) (hp : p∈support X j 0) (r : ℕ) (hr : r∈support X j 1) :
      continuousProfile (1-Y/X) (thirdScale X j/8) (4*thirdScale X j)
        (Real.log x-Real.log ((p:ℝ)*(r:ℝ)))/((p:ℝ)*(r:ℝ)) =
        (Y/X)/((p:ℝ)*(r:ℝ)) := by
    have hp0 : (0:ℝ)<p := by exact_mod_cast support_pos X j 0 p hp
    have hr0 : (0:ℝ)<r := by exact_mod_cast support_pos X j 1 r hr
    have hp' : scale j.1≤(p:ℝ) ∧ (p:ℝ)<2*scale j.1 := by
      have hh := Finset.mem_Ico.mp hp
      simpa [scale] using (show
        (((2:ℕ)^j.1:ℕ):ℝ)≤p ∧ (p:ℝ)<(2*(2:ℕ)^j.1:ℕ) by exact_mod_cast hh)
    have hr' : scale j.2≤(r:ℝ) ∧ (r:ℝ)<2*scale j.2 := by
      have hh := Finset.mem_Ico.mp hr
      simpa [scale] using (show
        (((2:ℕ)^j.2:ℕ):ℝ)≤r ∧ (r:ℝ)<(2*(2:ℕ)^j.2:ℕ) by exact_mod_cast hh)
    rw [continuous_translate _ _ _ x ((p:ℝ)*(r:ℝ)) hxp (mul_pos hp0 hr0)]
    rw [reference_length_exact (scale j.1) (scale j.2) (thirdScale X j)
      p r x (Y/X) hP hR hL hp' hr' (by simpa [hid] using hx) hd]
    field_simp <;> ring
  calc
    _ = ∑ p∈support X j 0, ∑ r∈support X j 1,
        (Y/X)*(ArithmeticFunction.vonMangoldt p/(p:ℝ))*
          (ArithmeticFunction.vonMangoldt r/(r:ℝ)) := by
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro r hr
      rw [hterm p hp r hr]
      ring
    _ = _ := by
      change (∑ p∈Finset.Ico (2^j.1) (2*2^j.1),
        ∑ r∈Finset.Ico (2^j.2) (2*2^j.2),
          (Y/X)*(ArithmeticFunction.vonMangoldt p/(p:ℝ))*
          (ArithmeticFunction.vonMangoldt r/(r:ℝ))) =
        (Y/X)*(∑ p∈Finset.Ico (2^j.1) (2*2^j.1),
          ArithmeticFunction.vonMangoldt p/(p:ℝ))*
          (∑ r∈Finset.Ico (2^j.2) (2*2^j.2),
          ArithmeticFunction.vonMangoldt r/(r:ℝ))
      simp only [←Finset.mul_sum, ←Finset.sum_mul]

/-- Exact literal source normalization on [X,2X], with the reference clipped globally. -/
theorem centered_eq_raw (X x Y : ℝ) (j : ℕ × ℕ)
    (hX : 0<X) (hx : x∈Icc X (2*X)) (hY : 0<Y) (hYX : Y≤X/2) :
    centeredProfile X j (1-Y/X) (Real.log x)=SourceRawMean.rawDelta X Y j x/x := by
  have hxp : 0<x := hX.trans_le hx.1
  have hρ : 0<1-Y/X := by
    have hh := (div_le_iff₀ hX).mpr (show Y≤(1/2)*X by linarith)
    linarith
  rw [centeredProfile, discrete_eq_count X x Y j hX hxp hρ,
    reference_eq_center X x Y j hX hx hY.le hYX]
  unfold SourceRawMean.rawDelta
  field_simp <;> ring

#print axioms centered_eq_raw
run_cmd do
  for n in [``log_window_iff, ``atom_identity, ``continuous_translate,
      ``triple_positive, ``discrete_eq_count, ``reference_eq_center,
      ``centered_eq_raw] do
    for ax in (← Lean.collectAxioms n) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {n}"
  Lean.logInfo "V7 EXACT ORDINARY SOURCE WINDOW: FOURIER ASSEMBLY NOT CLAIMED"
end SourceLogWindow
