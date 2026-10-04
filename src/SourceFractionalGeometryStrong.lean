import PositiveInteriorModel
import Mathlib.Tactic

/-!
Source moment geometry and a generated exact 16-region certificate.
STATUS: NEW UNCOMPILED PROOF DRAFT. No compiler or kernel audit has run.
The accompanying independent Python checker verifies the rational certificate,
not this Lean implementation. No mean estimate or prime theorem is proved here.
-/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option maxRecDepth 200000
noncomputable section
namespace SourceFractionalGeometryStrong
open PositiveInteriorRectangles PositiveInteriorCells PositiveInteriorModel

def nuPlus : ℝ := 8993 / 10000

def Triangle (u v : ℝ) : Prop :=
  447/1400 ≤ u ∧ u ≤ 499/1000 ∧ 27/35 ≤ u+v ∧ 2*u+3*v ≤ 399/200

def frac (h x : ℝ) : ℝ := 2*x/(4*nuPlus-2*h*x)

/-- Exact tangent remainder, valid independently of any source geometry. -/
theorem tangent_identity (A B q x : ℝ) (hx : A-B*x ≠ 0) (hq : A-B*q ≠ 0) :
    2*x/(A-B*x) - (2*q/(A-B*q) + (2*A/(A-B*q)^2)*(x-q)) =
      2*A*B*(x-q)^2/((A-B*x)*(A-B*q)^2) := by
  field_simp [hx, hq]
  ring_nf at hx hq ⊢
  field_simp [hx, hq]
  <;> ring

theorem tangent_le (h q x : ℝ) (hh : 0 ≤ h)
    (hx : 0 < 4*nuPlus-2*h*x) (hq : 0 < 4*nuPlus-2*h*q) :
    frac h q + (8*nuPlus/(4*nuPlus-2*h*q)^2)*(x-q) ≤ frac h x := by
  have hi := tangent_identity (4*nuPlus) (2*h) q x hx.ne' hq.ne'
  have hp : 0 ≤ 2*(4*nuPlus)*(2*h)*(x-q)^2 /
      ((4*nuPlus-2*h*x)*(4*nuPlus-2*h*q)^2) := by
    have hn : 0 < nuPlus := by norm_num [nuPlus]
    positivity
  unfold frac
  rw [← hi] at hp
  rw [show 2*(4*nuPlus) = 8*nuPlus by ring] at hp
  exact sub_nonneg.mp hp

def band (i : Fin 8) (x : ℝ) : Prop :=
  match i.val with
  | 0 => (1 / 6 : ℝ) ≤ x ∧ x ≤ (8993 / 50000 : ℝ)
  | 1 => (8993 / 50000 : ℝ) ≤ x ∧ x ≤ (8993 / 45000 : ℝ)
  | 2 => (8993 / 45000 : ℝ) ≤ x ∧ x ≤ (8993 / 40000 : ℝ)
  | 3 => (8993 / 40000 : ℝ) ≤ x ∧ x ≤ (8993 / 35000 : ℝ)
  | 4 => (8993 / 35000 : ℝ) ≤ x ∧ x ≤ (8993 / 30000 : ℝ)
  | 5 => (8993 / 30000 : ℝ) ≤ x ∧ x ≤ (8993 / 25000 : ℝ)
  | 6 => (8993 / 25000 : ℝ) ≤ x ∧ x ≤ (8993 / 20000 : ℝ)
  | _ => (8993 / 20000 : ℝ) ≤ x ∧ x ≤ (1 / 2 : ℝ)

def reciprocal (i : Fin 8) (x : ℝ) : ℝ :=
  match i.val with
  | 0 => frac (5 : ℝ) (x)
  | 1 => (1 / 5 : ℝ)
  | 2 => frac (4 : ℝ) (x)
  | 3 => (1 / 4 : ℝ)
  | 4 => frac (3 : ℝ) (x)
  | 5 => (1 / 3 : ℝ)
  | 6 => frac (2 : ℝ) (x)
  | _ => (1 / 2 : ℝ)

theorem triangle_coordinate_bounds (u v : ℝ) (ht : Triangle u v) :
    (1/6 ≤ u ∧ u ≤ 1/2) ∧ (1/6 ≤ v ∧ v ≤ 1/2) ∧
      (1/6 ≤ 1-u-v ∧ 1-u-v ≤ 1/2) := by
  rcases ht with ⟨hu0,hu1,hs,hl⟩
  constructor
  · constructor <;> linarith
  constructor
  · constructor <;> linarith
  constructor <;> linarith

theorem bands_cover (x : ℝ) (hx : 1/6 ≤ x ∧ x ≤ 1/2) :
    ∃ i : Fin 8, band i x := by
  by_cases h0 : x ≤ (8993 / 50000 : ℝ)
  · refine ⟨0, ?_⟩
    change (1 / 6 : ℝ) ≤ x ∧ x ≤ (8993 / 50000 : ℝ)
    constructor <;> linarith [hx.1, hx.2]
  by_cases h1 : x ≤ (8993 / 45000 : ℝ)
  · refine ⟨1, ?_⟩
    change (8993 / 50000 : ℝ) ≤ x ∧ x ≤ (8993 / 45000 : ℝ)
    constructor <;> linarith [hx.1, hx.2]
  by_cases h2 : x ≤ (8993 / 40000 : ℝ)
  · refine ⟨2, ?_⟩
    change (8993 / 45000 : ℝ) ≤ x ∧ x ≤ (8993 / 40000 : ℝ)
    constructor <;> linarith [hx.1, hx.2]
  by_cases h3 : x ≤ (8993 / 35000 : ℝ)
  · refine ⟨3, ?_⟩
    change (8993 / 40000 : ℝ) ≤ x ∧ x ≤ (8993 / 35000 : ℝ)
    constructor <;> linarith [hx.1, hx.2]
  by_cases h4 : x ≤ (8993 / 30000 : ℝ)
  · refine ⟨4, ?_⟩
    change (8993 / 35000 : ℝ) ≤ x ∧ x ≤ (8993 / 30000 : ℝ)
    constructor <;> linarith [hx.1, hx.2]
  by_cases h5 : x ≤ (8993 / 25000 : ℝ)
  · refine ⟨5, ?_⟩
    change (8993 / 30000 : ℝ) ≤ x ∧ x ≤ (8993 / 25000 : ℝ)
    constructor <;> linarith [hx.1, hx.2]
  by_cases h6 : x ≤ (8993 / 20000 : ℝ)
  · refine ⟨6, ?_⟩
    change (8993 / 25000 : ℝ) ≤ x ∧ x ≤ (8993 / 20000 : ℝ)
    constructor <;> linarith [hx.1, hx.2]
  refine ⟨7, ?_⟩
  change (8993 / 20000 : ℝ) ≤ x ∧ x ≤ (1 / 2 : ℝ)
  constructor <;> linarith [hx.1, hx.2]

/-- Exact rational supporting-plane certificate for bands [5, 6, 2]. -/
theorem cell_5_6_2 (u v : ℝ) (ht : Triangle u v)
    (hu : band 5 u) (hv : band 6 v) (hw : band 2 (1-u-v)) :
    (1001/1000 : ℝ) ≤ reciprocal 5 u + reciprocal 6 v +
      reciprocal 2 (1-u-v) := by
  rcases ht with ⟨ht0,ht1,ht2,ht3⟩
  change (8993 / 30000 : ℝ) ≤ u ∧ u ≤ (8993 / 25000 : ℝ) at hu
  change (8993 / 25000 : ℝ) ≤ v ∧ v ≤ (8993 / 20000 : ℝ) at hv
  change (8993 / 45000 : ℝ) ≤ 1-u-v ∧ 1-u-v ≤ (8993 / 40000 : ℝ) at hw
  rcases hu with ⟨hu0,hu1⟩
  rcases hv with ⟨hv0,hv1⟩
  rcases hw with ⟨hw0,hw1⟩
  have hd1 : 0 < 4*nuPlus-2*(2 : ℝ)*(v) := by
    norm_num [nuPlus] at *
    linarith
  have hh1 := tangent_le (2 : ℝ) (341 / 802 : ℝ) (v) (by norm_num) hd1
    (by norm_num [nuPlus])
  norm_num [frac, nuPlus] at hh1
  have hd2 : 0 < 4*nuPlus-2*(4 : ℝ)*(1-u-v) := by
    norm_num [nuPlus] at *
    linarith
  have hh2 := tangent_le (4 : ℝ) (43040 / 200099 : ℝ) (1-u-v) (by norm_num) hd2
    (by norm_num [nuPlus])
  norm_num [frac, nuPlus] at hh2
  have hp : (1001/1000 : ℝ) ≤ (601415789087639 / 594877146945417 : ℝ) + (-1800381054701965000 / 881139492455754249 : ℝ)*(u-(359 / 998 : ℝ)) +
      (-15170453617160025311950000000 / 353878819957919250373577303889 : ℝ)*(v-(341 / 802 : ℝ)) := by
    linarith
  change (1001/1000 : ℝ) ≤ (1 / 3 : ℝ) + frac (2 : ℝ) (v) + frac (4 : ℝ) (1-u-v)
  unfold frac nuPlus
  linarith

/-- Exact rational supporting-plane certificate for bands [5, 6, 3]. -/
theorem cell_5_6_3 (u v : ℝ) (ht : Triangle u v)
    (hu : band 5 u) (hv : band 6 v) (hw : band 3 (1-u-v)) :
    (1001/1000 : ℝ) ≤ reciprocal 5 u + reciprocal 6 v +
      reciprocal 3 (1-u-v) := by
  rcases ht with ⟨ht0,ht1,ht2,ht3⟩
  change (8993 / 30000 : ℝ) ≤ u ∧ u ≤ (8993 / 25000 : ℝ) at hu
  change (8993 / 25000 : ℝ) ≤ v ∧ v ≤ (8993 / 20000 : ℝ) at hv
  change (8993 / 40000 : ℝ) ≤ 1-u-v ∧ 1-u-v ≤ (8993 / 35000 : ℝ) at hw
  rcases hu with ⟨hu0,hu1⟩
  rcases hv with ⟨hv0,hv1⟩
  rcases hw with ⟨hw0,hw1⟩
  have hd1 : 0 < 4*nuPlus-2*(2 : ℝ)*(v) := by
    norm_num [nuPlus] at *
    linarith
  have hh1 := tangent_le (2 : ℝ) (408 / 991 : ℝ) (v) (by norm_num) hd1
    (by norm_num [nuPlus])
  norm_num [frac, nuPlus] at hh1
  have hp : (1001/1000 : ℝ) ≤ (3429673 / 3410868 : ℝ) + (0 : ℝ)*(u-(359 / 998 : ℝ)) +
      (2597604245000 / 1373460755057 : ℝ)*(v-(408 / 991 : ℝ)) := by
    linarith
  change (1001/1000 : ℝ) ≤ (1 / 3 : ℝ) + frac (2 : ℝ) (v) + (1 / 4 : ℝ)
  unfold frac nuPlus
  linarith

/-- Exact rational supporting-plane certificate for bands [5, 7, 3]. -/
theorem cell_5_7_3 (u v : ℝ) (ht : Triangle u v)
    (hu : band 5 u) (hv : band 7 v) (hw : band 3 (1-u-v)) :
    (1001/1000 : ℝ) ≤ reciprocal 5 u + reciprocal 7 v +
      reciprocal 3 (1-u-v) := by
  rcases ht with ⟨ht0,ht1,ht2,ht3⟩
  change (8993 / 30000 : ℝ) ≤ u ∧ u ≤ (8993 / 25000 : ℝ) at hu
  change (8993 / 20000 : ℝ) ≤ v ∧ v ≤ (1 / 2 : ℝ) at hv
  change (8993 / 40000 : ℝ) ≤ 1-u-v ∧ 1-u-v ≤ (8993 / 35000 : ℝ) at hw
  rcases hu with ⟨hu0,hu1⟩
  rcases hv with ⟨hv0,hv1⟩
  rcases hw with ⟨hw0,hw1⟩
  have hp : (1001/1000 : ℝ) ≤ (13 / 12 : ℝ) + (0 : ℝ)*(u-(179 / 557 : ℝ)) +
      (0 : ℝ)*(v-(141 / 313 : ℝ)) := by
    linarith
  change (1001/1000 : ℝ) ≤ (1 / 3 : ℝ) + (1 / 2 : ℝ) + (1 / 4 : ℝ)
  norm_num

/-- Exact rational supporting-plane certificate for bands [6, 5, 1]. -/
theorem cell_6_5_1 (u v : ℝ) (ht : Triangle u v)
    (hu : band 6 u) (hv : band 5 v) (hw : band 1 (1-u-v)) :
    (1001/1000 : ℝ) ≤ reciprocal 6 u + reciprocal 5 v +
      reciprocal 1 (1-u-v) := by
  rcases ht with ⟨ht0,ht1,ht2,ht3⟩
  change (8993 / 25000 : ℝ) ≤ u ∧ u ≤ (8993 / 20000 : ℝ) at hu
  change (8993 / 30000 : ℝ) ≤ v ∧ v ≤ (8993 / 25000 : ℝ) at hv
  change (8993 / 50000 : ℝ) ≤ 1-u-v ∧ 1-u-v ≤ (8993 / 45000 : ℝ) at hw
  rcases hu with ⟨hu0,hu1⟩
  rcases hv with ⟨hv0,hv1⟩
  rcases hw with ⟨hw0,hw1⟩
  have hd0 : 0 < 4*nuPlus-2*(2 : ℝ)*(u) := by
    norm_num [nuPlus] at *
    linarith
  have hh0 := tangent_le (2 : ℝ) (403 / 915 : ℝ) (u) (by norm_num) hd0
    (by norm_num [nuPlus])
  norm_num [frac, nuPlus] at hh0
  have hp : (1001/1000 : ℝ) ≤ (12762752 / 12595785 : ℝ) + (1505832885000 / 705127998961 : ℝ)*(u-(403 / 915 : ℝ)) +
      (0 : ℝ)*(v-(359 / 998 : ℝ)) := by
    linarith
  change (1001/1000 : ℝ) ≤ frac (2 : ℝ) (u) + (1 / 3 : ℝ) + (1 / 5 : ℝ)
  unfold frac nuPlus
  linarith

/-- Exact rational supporting-plane certificate for bands [6, 5, 2]. -/
theorem cell_6_5_2 (u v : ℝ) (ht : Triangle u v)
    (hu : band 6 u) (hv : band 5 v) (hw : band 2 (1-u-v)) :
    (1001/1000 : ℝ) ≤ reciprocal 6 u + reciprocal 5 v +
      reciprocal 2 (1-u-v) := by
  rcases ht with ⟨ht0,ht1,ht2,ht3⟩
  change (8993 / 25000 : ℝ) ≤ u ∧ u ≤ (8993 / 20000 : ℝ) at hu
  change (8993 / 30000 : ℝ) ≤ v ∧ v ≤ (8993 / 25000 : ℝ) at hv
  change (8993 / 45000 : ℝ) ≤ 1-u-v ∧ 1-u-v ≤ (8993 / 40000 : ℝ) at hw
  rcases hu with ⟨hu0,hu1⟩
  rcases hv with ⟨hv0,hv1⟩
  rcases hw with ⟨hw0,hw1⟩
  have hd0 : 0 < 4*nuPlus-2*(2 : ℝ)*(u) := by
    norm_num [nuPlus] at *
    linarith
  have hh0 := tangent_le (2 : ℝ) (213 / 499 : ℝ) (u) (by norm_num) hd0
    (by norm_num [nuPlus])
  norm_num [frac, nuPlus] at hh0
  have hd2 : 0 < 4*nuPlus-2*(4 : ℝ)*(1-u-v) := by
    norm_num [nuPlus] at *
    linarith
  have hh2 := tangent_le (4 : ℝ) (213 / 998 : ℝ) (1-u-v) (by norm_num) hd2
    (by norm_num [nuPlus])
  norm_num [frac, nuPlus] at hh2
  have hp : (1001/1000 : ℝ) ≤ (7150007 / 7072521 : ℝ) + (0 : ℝ)*(u-(213 / 499 : ℝ)) +
      (-11196329965000 / 5557839255049 : ℝ)*(v-(359 / 998 : ℝ)) := by
    linarith
  change (1001/1000 : ℝ) ≤ frac (2 : ℝ) (u) + (1 / 3 : ℝ) + frac (4 : ℝ) (1-u-v)
  unfold frac nuPlus
  linarith

/-- Exact rational supporting-plane certificate for bands [6, 5, 3]. -/
theorem cell_6_5_3 (u v : ℝ) (ht : Triangle u v)
    (hu : band 6 u) (hv : band 5 v) (hw : band 3 (1-u-v)) :
    (1001/1000 : ℝ) ≤ reciprocal 6 u + reciprocal 5 v +
      reciprocal 3 (1-u-v) := by
  rcases ht with ⟨ht0,ht1,ht2,ht3⟩
  change (8993 / 25000 : ℝ) ≤ u ∧ u ≤ (8993 / 20000 : ℝ) at hu
  change (8993 / 30000 : ℝ) ≤ v ∧ v ≤ (8993 / 25000 : ℝ) at hv
  change (8993 / 40000 : ℝ) ≤ 1-u-v ∧ 1-u-v ≤ (8993 / 35000 : ℝ) at hw
  rcases hu with ⟨hu0,hu1⟩
  rcases hv with ⟨hv0,hv1⟩
  rcases hw with ⟨hw0,hw1⟩
  have hd0 : 0 < 4*nuPlus-2*(2 : ℝ)*(u) := by
    norm_num [nuPlus] at *
    linarith
  have hh0 := tangent_le (2 : ℝ) (408 / 991 : ℝ) (u) (by norm_num) hd0
    (by norm_num [nuPlus])
  norm_num [frac, nuPlus] at hh0
  have hp : (1001/1000 : ℝ) ≤ (3429673 / 3410868 : ℝ) + (2597604245000 / 1373460755057 : ℝ)*(u-(408 / 991 : ℝ)) +
      (0 : ℝ)*(v-(359 / 998 : ℝ)) := by
    linarith
  change (1001/1000 : ℝ) ≤ frac (2 : ℝ) (u) + (1 / 3 : ℝ) + (1 / 4 : ℝ)
  unfold frac nuPlus
  linarith

/-- Exact rational supporting-plane certificate for bands [6, 6, 1]. -/
theorem cell_6_6_1 (u v : ℝ) (ht : Triangle u v)
    (hu : band 6 u) (hv : band 6 v) (hw : band 1 (1-u-v)) :
    (1001/1000 : ℝ) ≤ reciprocal 6 u + reciprocal 6 v +
      reciprocal 1 (1-u-v) := by
  rcases ht with ⟨ht0,ht1,ht2,ht3⟩
  change (8993 / 25000 : ℝ) ≤ u ∧ u ≤ (8993 / 20000 : ℝ) at hu
  change (8993 / 25000 : ℝ) ≤ v ∧ v ≤ (8993 / 20000 : ℝ) at hv
  change (8993 / 50000 : ℝ) ≤ 1-u-v ∧ 1-u-v ≤ (8993 / 45000 : ℝ) at hw
  rcases hu with ⟨hu0,hu1⟩
  rcases hv with ⟨hv0,hv1⟩
  rcases hw with ⟨hw0,hw1⟩
  have hd0 : 0 < 4*nuPlus-2*(2 : ℝ)*(u) := by
    norm_num [nuPlus] at *
    linarith
  have hh0 := tangent_le (2 : ℝ) (178 / 439 : ℝ) (u) (by norm_num) hd0
    (by norm_num [nuPlus])
  norm_num [frac, nuPlus] at hh0
  have hd1 : 0 < 4*nuPlus-2*(2 : ℝ)*(v) := by
    norm_num [nuPlus] at *
    linarith
  have hh1 := tangent_le (2 : ℝ) (223 / 565 : ℝ) (v) (by norm_num) hd1
    (by norm_num [nuPlus])
  norm_num [frac, nuPlus] at hh1
  have hp : (1001/1000 : ℝ) ≤ (6190840141743 / 6180857433715 : ℝ) + (8665699765000 / 4699907477329 : ℝ)*(u-(178 / 439 : ℝ)) +
      (574158085000 / 325138303681 : ℝ)*(v-(223 / 565 : ℝ)) := by
    linarith
  change (1001/1000 : ℝ) ≤ frac (2 : ℝ) (u) + frac (2 : ℝ) (v) + (1 / 5 : ℝ)
  unfold frac nuPlus
  linarith

/-- Exact rational supporting-plane certificate for bands [6, 6, 2]. -/
theorem cell_6_6_2 (u v : ℝ) (ht : Triangle u v)
    (hu : band 6 u) (hv : band 6 v) (hw : band 2 (1-u-v)) :
    (1001/1000 : ℝ) ≤ reciprocal 6 u + reciprocal 6 v +
      reciprocal 2 (1-u-v) := by
  rcases ht with ⟨ht0,ht1,ht2,ht3⟩
  change (8993 / 25000 : ℝ) ≤ u ∧ u ≤ (8993 / 20000 : ℝ) at hu
  change (8993 / 25000 : ℝ) ≤ v ∧ v ≤ (8993 / 20000 : ℝ) at hv
  change (8993 / 45000 : ℝ) ≤ 1-u-v ∧ 1-u-v ≤ (8993 / 40000 : ℝ) at hw
  rcases hu with ⟨hu0,hu1⟩
  rcases hv with ⟨hv0,hv1⟩
  rcases hw with ⟨hw0,hw1⟩
  have hd0 : 0 < 4*nuPlus-2*(2 : ℝ)*(u) := by
    norm_num [nuPlus] at *
    linarith
  have hh0 := tangent_le (2 : ℝ) (2 / 5 : ℝ) (u) (by norm_num) hd0
    (by norm_num [nuPlus])
  norm_num [frac, nuPlus] at hh0
  have hd1 : 0 < 4*nuPlus-2*(2 : ℝ)*(v) := by
    norm_num [nuPlus] at *
    linarith
  have hh1 := tangent_le (2 : ℝ) (333 / 836 : ℝ) (v) (by norm_num) hd1
    (by norm_num [nuPlus])
  norm_num [frac, nuPlus] at hh1
  have hd2 : 0 < 4*nuPlus-2*(4 : ℝ)*(1-u-v) := by
    norm_num [nuPlus] at *
    linarith
  have hh2 := tangent_le (4 : ℝ) (843 / 4180 : ℝ) (1-u-v) (by norm_num) hd2
    (by norm_num [nuPlus])
  norm_num [frac, nuPlus] at hh2
  have hp : (1001/1000 : ℝ) ≤ (5426628200720000 / 5418865906208917 : ℝ) + (-654713691870000000 / 26785067828597836081 : ℝ)*(u-(2 / 5 : ℝ)) +
      (-42970004430923955000000 / 1177860007795146622175161 : ℝ)*(v-(333 / 836 : ℝ)) := by
    linarith
  change (1001/1000 : ℝ) ≤ frac (2 : ℝ) (u) + frac (2 : ℝ) (v) + frac (4 : ℝ) (1-u-v)
  unfold frac nuPlus
  linarith

/-- Exact rational supporting-plane certificate for bands [6, 6, 3]. -/
theorem cell_6_6_3 (u v : ℝ) (ht : Triangle u v)
    (hu : band 6 u) (hv : band 6 v) (hw : band 3 (1-u-v)) :
    (1001/1000 : ℝ) ≤ reciprocal 6 u + reciprocal 6 v +
      reciprocal 3 (1-u-v) := by
  rcases ht with ⟨ht0,ht1,ht2,ht3⟩
  change (8993 / 25000 : ℝ) ≤ u ∧ u ≤ (8993 / 20000 : ℝ) at hu
  change (8993 / 25000 : ℝ) ≤ v ∧ v ≤ (8993 / 20000 : ℝ) at hv
  change (8993 / 40000 : ℝ) ≤ 1-u-v ∧ 1-u-v ≤ (8993 / 35000 : ℝ) at hw
  rcases hu with ⟨hu0,hu1⟩
  rcases hv with ⟨hv0,hv1⟩
  rcases hw with ⟨hw0,hw1⟩
  have hd0 : 0 < 4*nuPlus-2*(2 : ℝ)*(u) := by
    norm_num [nuPlus] at *
    linarith
  have hh0 := tangent_le (2 : ℝ) (27 / 70 : ℝ) (u) (by norm_num) hd0
    (by norm_num [nuPlus])
  norm_num [frac, nuPlus] at hh0
  have hd1 : 0 < 4*nuPlus-2*(2 : ℝ)*(v) := by
    norm_num [nuPlus] at *
    linarith
  have hh1 := tangent_le (2 : ℝ) (27 / 70 : ℝ) (v) (by norm_num) hd1
    (by norm_num [nuPlus])
  norm_num [frac, nuPlus] at hh1
  have hp : (1001/1000 : ℝ) ≤ (143951 / 143804 : ℝ) + (2203285000 / 1292474401 : ℝ)*(u-(27 / 70 : ℝ)) +
      (2203285000 / 1292474401 : ℝ)*(v-(27 / 70 : ℝ)) := by
    linarith
  change (1001/1000 : ℝ) ≤ frac (2 : ℝ) (u) + frac (2 : ℝ) (v) + (1 / 4 : ℝ)
  unfold frac nuPlus
  linarith

/-- Exact rational supporting-plane certificate for bands [7, 4, 2]. -/
theorem cell_7_4_2 (u v : ℝ) (ht : Triangle u v)
    (hu : band 7 u) (hv : band 4 v) (hw : band 2 (1-u-v)) :
    (1001/1000 : ℝ) ≤ reciprocal 7 u + reciprocal 4 v +
      reciprocal 2 (1-u-v) := by
  rcases ht with ⟨ht0,ht1,ht2,ht3⟩
  change (8993 / 20000 : ℝ) ≤ u ∧ u ≤ (1 / 2 : ℝ) at hu
  change (8993 / 35000 : ℝ) ≤ v ∧ v ≤ (8993 / 30000 : ℝ) at hv
  change (8993 / 45000 : ℝ) ≤ 1-u-v ∧ 1-u-v ≤ (8993 / 40000 : ℝ) at hw
  rcases hu with ⟨hu0,hu1⟩
  rcases hv with ⟨hv0,hv1⟩
  rcases hw with ⟨hw0,hw1⟩
  have hd1 : 0 < 4*nuPlus-2*(3 : ℝ)*(v) := by
    norm_num [nuPlus] at *
    linarith
  have hh1 := tangent_le (3 : ℝ) (286 / 999 : ℝ) (v) (by norm_num) hd1
    (by norm_num [nuPlus])
  norm_num [frac, nuPlus] at hh1
  have hd2 : 0 < 4*nuPlus-2*(4 : ℝ)*(1-u-v) := by
    norm_num [nuPlus] at *
    linarith
  have hh2 := tangent_le (4 : ℝ) (214499 / 999000 : ℝ) (1-u-v) (by norm_num) hd2
    (by norm_num [nuPlus])
  norm_num [frac, nuPlus] at hh2
  have hp : (1001/1000 : ℝ) ≤ (45527310891119 / 44067591192378 : ℝ) + (-44875114965000 / 22033889476729 : ℝ)*(u-(499 / 1000 : ℝ)) +
      (936198011211841800000 / 53943127597181974439035969 : ℝ)*(v-(286 / 999 : ℝ)) := by
    linarith
  change (1001/1000 : ℝ) ≤ (1 / 2 : ℝ) + frac (3 : ℝ) (v) + frac (4 : ℝ) (1-u-v)
  unfold frac nuPlus
  linarith

/-- Exact rational supporting-plane certificate for bands [7, 4, 3]. -/
theorem cell_7_4_3 (u v : ℝ) (ht : Triangle u v)
    (hu : band 7 u) (hv : band 4 v) (hw : band 3 (1-u-v)) :
    (1001/1000 : ℝ) ≤ reciprocal 7 u + reciprocal 4 v +
      reciprocal 3 (1-u-v) := by
  rcases ht with ⟨ht0,ht1,ht2,ht3⟩
  change (8993 / 20000 : ℝ) ≤ u ∧ u ≤ (1 / 2 : ℝ) at hu
  change (8993 / 35000 : ℝ) ≤ v ∧ v ≤ (8993 / 30000 : ℝ) at hv
  change (8993 / 40000 : ℝ) ≤ 1-u-v ∧ 1-u-v ≤ (8993 / 35000 : ℝ) at hw
  rcases hu with ⟨hu0,hu1⟩
  rcases hv with ⟨hv0,hv1⟩
  rcases hw with ⟨hw0,hw1⟩
  have hd1 : 0 < 4*nuPlus-2*(3 : ℝ)*(v) := by
    norm_num [nuPlus] at *
    linarith
  have hh1 := tangent_le (3 : ℝ) (249 / 914 : ℝ) (v) (by norm_num) hd1
    (by norm_num [nuPlus])
  norm_num [frac, nuPlus] at hh1
  have hp : (1001/1000 : ℝ) ≤ (9216903 / 8969204 : ℝ) + (0 : ℝ)*(u-(499 / 1000 : ℝ)) +
      (9390895285000 / 5027913774601 : ℝ)*(v-(249 / 914 : ℝ)) := by
    linarith
  change (1001/1000 : ℝ) ≤ (1 / 2 : ℝ) + frac (3 : ℝ) (v) + (1 / 4 : ℝ)
  unfold frac nuPlus
  linarith

/-- Exact rational supporting-plane certificate for bands [7, 5, 0]. -/
theorem cell_7_5_0 (u v : ℝ) (ht : Triangle u v)
    (hu : band 7 u) (hv : band 5 v) (hw : band 0 (1-u-v)) :
    (1001/1000 : ℝ) ≤ reciprocal 7 u + reciprocal 5 v +
      reciprocal 0 (1-u-v) := by
  rcases ht with ⟨ht0,ht1,ht2,ht3⟩
  change (8993 / 20000 : ℝ) ≤ u ∧ u ≤ (1 / 2 : ℝ) at hu
  change (8993 / 30000 : ℝ) ≤ v ∧ v ≤ (8993 / 25000 : ℝ) at hv
  change (1 / 6 : ℝ) ≤ 1-u-v ∧ 1-u-v ≤ (8993 / 50000 : ℝ) at hw
  rcases hu with ⟨hu0,hu1⟩
  rcases hv with ⟨hv0,hv1⟩
  rcases hw with ⟨hw0,hw1⟩
  have hd2 : 0 < 4*nuPlus-2*(5 : ℝ)*(1-u-v) := by
    norm_num [nuPlus] at *
    linarith
  have hh2 := tangent_le (5 : ℝ) (168499 / 999000 : ℝ) (1-u-v) (by norm_num) hd2
    (by norm_num [nuPlus])
  norm_num [frac, nuPlus] at hh2
  have hp : (1001/1000 : ℝ) ≤ (14456315 / 14314596 : ℝ) + (-5609389370625 / 2845939703378 : ℝ)*(u-(499 / 1000 : ℝ)) +
      (-5609389370625 / 2845939703378 : ℝ)*(v-(332 / 999 : ℝ)) := by
    linarith
  change (1001/1000 : ℝ) ≤ (1 / 2 : ℝ) + (1 / 3 : ℝ) + frac (5 : ℝ) (1-u-v)
  unfold frac nuPlus
  linarith

/-- Exact rational supporting-plane certificate for bands [7, 5, 1]. -/
theorem cell_7_5_1 (u v : ℝ) (ht : Triangle u v)
    (hu : band 7 u) (hv : band 5 v) (hw : band 1 (1-u-v)) :
    (1001/1000 : ℝ) ≤ reciprocal 7 u + reciprocal 5 v +
      reciprocal 1 (1-u-v) := by
  rcases ht with ⟨ht0,ht1,ht2,ht3⟩
  change (8993 / 20000 : ℝ) ≤ u ∧ u ≤ (1 / 2 : ℝ) at hu
  change (8993 / 30000 : ℝ) ≤ v ∧ v ≤ (8993 / 25000 : ℝ) at hv
  change (8993 / 50000 : ℝ) ≤ 1-u-v ∧ 1-u-v ≤ (8993 / 45000 : ℝ) at hw
  rcases hu with ⟨hu0,hu1⟩
  rcases hv with ⟨hv0,hv1⟩
  rcases hw with ⟨hw0,hw1⟩
  have hp : (1001/1000 : ℝ) ≤ (31 / 30 : ℝ) + (0 : ℝ)*(u-(401 / 853 : ℝ)) +
      (0 : ℝ)*(v-(247 / 724 : ℝ)) := by
    linarith
  change (1001/1000 : ℝ) ≤ (1 / 2 : ℝ) + (1 / 3 : ℝ) + (1 / 5 : ℝ)
  norm_num

/-- Exact rational supporting-plane certificate for bands [7, 5, 2]. -/
theorem cell_7_5_2 (u v : ℝ) (ht : Triangle u v)
    (hu : band 7 u) (hv : band 5 v) (hw : band 2 (1-u-v)) :
    (1001/1000 : ℝ) ≤ reciprocal 7 u + reciprocal 5 v +
      reciprocal 2 (1-u-v) := by
  rcases ht with ⟨ht0,ht1,ht2,ht3⟩
  change (8993 / 20000 : ℝ) ≤ u ∧ u ≤ (1 / 2 : ℝ) at hu
  change (8993 / 30000 : ℝ) ≤ v ∧ v ≤ (8993 / 25000 : ℝ) at hv
  change (8993 / 45000 : ℝ) ≤ 1-u-v ∧ 1-u-v ≤ (8993 / 40000 : ℝ) at hw
  rcases hu with ⟨hu0,hu1⟩
  rcases hv with ⟨hv0,hv1⟩
  rcases hw with ⟨hw0,hw1⟩
  have hd2 : 0 < 4*nuPlus-2*(4 : ℝ)*(1-u-v) := by
    norm_num [nuPlus] at *
    linarith
  have hh2 := tangent_le (4 : ℝ) (137977 / 690420 : ℝ) (1-u-v) (by norm_num) hd2
    (by norm_num [nuPlus])
  norm_num [frac, nuPlus] at hh2
  have hp : (1001/1000 : ℝ) ≤ (46492055 / 44992266 : ℝ) + (-101294452485000 / 56230666661521 : ℝ)*(u-(351 / 740 : ℝ)) +
      (-101294452485000 / 56230666661521 : ℝ)*(v-(304 / 933 : ℝ)) := by
    linarith
  change (1001/1000 : ℝ) ≤ (1 / 2 : ℝ) + (1 / 3 : ℝ) + frac (4 : ℝ) (1-u-v)
  unfold frac nuPlus
  linarith

/-- Exact rational supporting-plane certificate for bands [7, 5, 3]. -/
theorem cell_7_5_3 (u v : ℝ) (ht : Triangle u v)
    (hu : band 7 u) (hv : band 5 v) (hw : band 3 (1-u-v)) :
    (1001/1000 : ℝ) ≤ reciprocal 7 u + reciprocal 5 v +
      reciprocal 3 (1-u-v) := by
  rcases ht with ⟨ht0,ht1,ht2,ht3⟩
  change (8993 / 20000 : ℝ) ≤ u ∧ u ≤ (1 / 2 : ℝ) at hu
  change (8993 / 30000 : ℝ) ≤ v ∧ v ≤ (8993 / 25000 : ℝ) at hv
  change (8993 / 40000 : ℝ) ≤ 1-u-v ∧ 1-u-v ≤ (8993 / 35000 : ℝ) at hw
  rcases hu with ⟨hu0,hu1⟩
  rcases hv with ⟨hv0,hv1⟩
  rcases hw with ⟨hw0,hw1⟩
  have hp : (1001/1000 : ℝ) ≤ (13 / 12 : ℝ) + (0 : ℝ)*(u-(457 / 990 : ℝ)) +
      (0 : ℝ)*(v-(197 / 632 : ℝ)) := by
    linarith
  change (1001/1000 : ℝ) ≤ (1 / 2 : ℝ) + (1 / 3 : ℝ) + (1 / 4 : ℝ)
  norm_num

/-- Exact rational supporting-plane certificate for bands [7, 6, 1]. -/
theorem cell_7_6_1 (u v : ℝ) (ht : Triangle u v)
    (hu : band 7 u) (hv : band 6 v) (hw : band 1 (1-u-v)) :
    (1001/1000 : ℝ) ≤ reciprocal 7 u + reciprocal 6 v +
      reciprocal 1 (1-u-v) := by
  rcases ht with ⟨ht0,ht1,ht2,ht3⟩
  change (8993 / 20000 : ℝ) ≤ u ∧ u ≤ (1 / 2 : ℝ) at hu
  change (8993 / 25000 : ℝ) ≤ v ∧ v ≤ (8993 / 20000 : ℝ) at hv
  change (8993 / 50000 : ℝ) ≤ 1-u-v ∧ 1-u-v ≤ (8993 / 45000 : ℝ) at hw
  rcases hu with ⟨hu0,hu1⟩
  rcases hv with ⟨hv0,hv1⟩
  rcases hw with ⟨hw0,hw1⟩
  have hd1 : 0 < 4*nuPlus-2*(2 : ℝ)*(v) := by
    norm_num [nuPlus] at *
    linarith
  have hh1 := tangent_le (2 : ℝ) (359 / 998 : ℝ) (v) (by norm_num) hd1
    (by norm_num [nuPlus])
  norm_num [frac, nuPlus] at hh1
  have hp : (1001/1000 : ℝ) ≤ (27822549 / 26925070 : ℝ) + (0 : ℝ)*(u-(54 / 119 : ℝ)) +
      (11196329965000 / 7249593945049 : ℝ)*(v-(359 / 998 : ℝ)) := by
    linarith
  change (1001/1000 : ℝ) ≤ (1 / 2 : ℝ) + frac (2 : ℝ) (v) + (1 / 5 : ℝ)
  unfold frac nuPlus
  linarith

/-- The empty cases are discharged from their affine constraints. The sixteen
nonempty cases use explicit tangent certificates rather than sample points. -/
theorem all_band_cases (i j k : Fin 8) (u v : ℝ) (ht : Triangle u v)
    (hu : band i u) (hv : band j v) (hw : band k (1-u-v)) :
    (1001/1000 : ℝ) ≤ reciprocal i u + reciprocal j v + reciprocal k (1-u-v) := by
  fin_cases i
  all_goals first
    | (exfalso; norm_num [band] at hu; linarith [hu.2, ht.1])
    | skip
  all_goals fin_cases j
  all_goals first
    | (exfalso; norm_num [band] at hv; linarith [hv.2, ht.2.1, ht.2.2.1])
    | skip
  all_goals fin_cases k
  all_goals first
    | (exfalso; norm_num [band] at hw; linarith [hw.1, ht.2.2.1])
    | skip
  all_goals
    first
    | (exfalso
       rcases ht with ⟨ht0,ht1,ht2,ht3⟩
       norm_num [band] at hu hv hw
       rcases hu with ⟨hu0,hu1⟩
       rcases hv with ⟨hv0,hv1⟩
       rcases hw with ⟨hw0,hw1⟩
       linarith)
    | exact cell_5_6_2 u v ht hu hv hw
    | exact cell_5_6_3 u v ht hu hv hw
    | exact cell_5_7_3 u v ht hu hv hw
    | exact cell_6_5_1 u v ht hu hv hw
    | exact cell_6_5_2 u v ht hu hv hw
    | exact cell_6_5_3 u v ht hu hv hw
    | exact cell_6_6_1 u v ht hu hv hw
    | exact cell_6_6_2 u v ht hu hv hw
    | exact cell_6_6_3 u v ht hu hv hw
    | exact cell_7_4_2 u v ht hu hv hw
    | exact cell_7_4_3 u v ht hu hv hw
    | exact cell_7_5_0 u v ht hu hv hw
    | exact cell_7_5_1 u v ht hu hv hw
    | exact cell_7_5_2 u v ht hu hv hw
    | exact cell_7_5_3 u v ht hu hv hw
    | exact cell_7_6_1 u v ht hu hv hw

theorem triangle_surplus (u v : ℝ) (ht : Triangle u v) :
    ∃ i j k : Fin 8, band i u ∧ band j v ∧ band k (1-u-v) ∧
      (1001/1000 : ℝ) ≤ reciprocal i u + reciprocal j v + reciprocal k (1-u-v) := by
  obtain ⟨hu,hv,hw⟩ := triangle_coordinate_bounds u v ht
  obtain ⟨i,hi⟩ := bands_cover u hu
  obtain ⟨j,hj⟩ := bands_cover v hv
  obtain ⟨k,hk⟩ := bands_cover (1-u-v) hw
  exact ⟨i,j,k,hi,hj,hk,all_band_cases i j k u v ht hi hj hk⟩

/-- Literal source mesh cells lie in the certified triangle. -/
theorem source_triangle (X : ℝ) (hX : 1 < X) (j : ℕ × ℕ)
    (hj : j ∈ PositiveInteriorCells.boxes (PositiveInteriorModel.mesh X)) :
    Triangle ((j.1:ℝ)*PositiveInteriorModel.mesh X)
      ((j.2:ℝ)*PositiveInteriorModel.mesh X) := by
  obtain ⟨i,hi,hc⟩ := Finset.mem_biUnion.mp hj
  have hi' := Finset.mem_range.mp hi
  have hpair := Finset.mem_product.mp hc
  have hu := index_endpoints (mesh X) (left i) (right i) (mesh_pos X hX)
    (left_nonneg i) (endpoints_ordered i).1.le j.1 hpair.1
  have hv := index_endpoints (mesh X) (lower i) (upper i) (mesh_pos X hX)
    (lower_nonneg i hi') (endpoints_ordered i).2.le j.2 hpair.2
  have hh := endpoint_bounds i hi'
  have hm := mesh_pos X hX
  dsimp [Triangle]
  dsimp [lower,upper] at hv
  dsimp [start,finish] at hh
  constructor
  · linarith [hu.1,hh.1]
  constructor
  · nlinarith [hu.2,hh.2]
  constructor
  · linarith [hu.1,hv.1]
  · nlinarith [hu.2,hv.2]

#print axioms triangle_surplus
#print axioms source_triangle
run_cmd do
  for target in [``tangent_identity, ``tangent_le, ``triangle_coordinate_bounds,
      ``bands_cover, ``cell_5_6_2, ``cell_5_6_3, ``cell_5_7_3,
      ``cell_6_5_1, ``cell_6_5_2, ``cell_6_5_3, ``cell_6_6_1,
      ``cell_6_6_2, ``cell_6_6_3, ``cell_7_4_2, ``cell_7_4_3,
      ``cell_7_5_0, ``cell_7_5_1, ``cell_7_5_2, ``cell_7_5_3,
      ``cell_7_6_1, ``all_band_cases, ``triangle_surplus, ``source_triangle] do
    for ax in (← Lean.collectAxioms target) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "SOURCE FRACTIONAL GEOMETRY AUDIT — ONLY VALID IF THIS FILE COMPILES"
end SourceFractionalGeometryStrong
