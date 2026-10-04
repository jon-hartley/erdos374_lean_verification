import OuterBlockMainTermWork

/-! Unit reciprocal-mass budget for each rectangular block, uniformly in
all separator frequencies. This controls the actual main-term smoothing error. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace OuterBlockMassBudgetWork
open OuterBlockMainTermWork OuterBlockCofactorWork OuterActiveDyadicWork
open OuterRectangularBlocksWork OuterSourceReindexWork OuterSmoothErrorSupportWork
open OuterSmoothCoreWork OuterSeparatedFourierModeWork LongerTupleEncoding
open MellinSmoothingFunction

theorem block_card (X : ℝ) (hX : 2≤X) (k : BlockKey) :
    (blockSource X k).card≤scale k := by
  let R := Finset.Ico (2^k.1) (2*2^k.1) ×ˢ
    (Finset.Ico (2^k.2.1) (2*2^k.2.1) ×ˢ
      (Finset.Ico (2^k.2.2.1) (2*2^k.2.2.1) ×ˢ Finset.Ico (2^k.2.2.2) (2*2^k.2.2.2)))
  have hcard : R.card=scale k := by
    have hsub (n : ℕ) : 2*n-n=n := by omega
    simp [R,Finset.card_product,Nat.card_Ico,hsub,scale,Nat.mul_assoc]
  rw [←hcard]
  apply Finset.card_le_card_of_injOn (fun r : Representation => (r.1,drop r))
  · intro r hr
    have hd := ambient_data X hX r (Finset.mem_filter.mp hr).1
    have he := (Finset.mem_filter.mp hr).2
    have hb (n j : ℕ) (hn : 0<n) (hj : n.log2=j) : n∈Finset.Ico (2^j) (2*2^j) := by
      have hl := Nat.log2_self_le (Nat.ne_of_gt hn)
      have hu := Nat.lt_log2_self (n:=n)
      rw [hj] at hl hu
      rw [Nat.pow_succ] at hu
      exact Finset.mem_Ico.mpr ⟨hl,by omega⟩
    exact Finset.mem_product.mpr ⟨hb _ _ hd.2.2.1 (congrArg (fun z : BlockKey => z.1) he),
      Finset.mem_product.mpr ⟨hb _ _ hd.2.2.2.2.1 (congrArg (fun z : BlockKey => z.2.1) he),
        Finset.mem_product.mpr ⟨hb _ _ hd.2.2.2.2.2.1 (congrArg (fun z : BlockKey => z.2.2.1) he),
          hb _ _ hd.2.2.2.2.2.2 (congrArg (fun z : BlockKey => z.2.2.2) he)⟩⟩⟩
  · intro r hr q hq he
    have hdr := ambient_data X hX r (Finset.mem_filter.mp hr).1
    have hdq := ambient_data X hX q (Finset.mem_filter.mp hq).1
    calc
      r = rebuild (drop r) r.1 := (rebuild_drop r hdr.1).symm
      _ = rebuild (drop q) q.1 := congrArg₂ rebuild (congrArg (fun z : BlockKey => z.2) he) (congrArg (fun z : BlockKey => z.1) he)
      _ = q := rebuild_drop q hdq.1

theorem modeWeight_norm (X s : ℝ) (i j : ℕ) (ω : Fin 9→ℝ) (r : Representation) :
    ‖modeWeight X s i j ω r‖≤1 := by
  have hmode : ‖sourceMode X s i j (drop r).1 r.1 (drop r).2.1 (drop r).2.2 ω‖=1 := by
    simp [sourceMode,norm_prod,OuterMaskFrequencyWork.phase_norm]
  simpa only [modeWeight,norm_mul,hmode,mul_one,Complex.norm_real,Real.norm_eq_abs] using
    atomMultiplier_abs_le X s i j r

theorem mainMass_norm (X s : ℝ) (hX : 2≤X) (i j : ℕ) (k : BlockKey) (ω : Fin 9→ℝ) :
    ‖mainMass X s i j k ω‖≤1 := by
  have hM : (0:ℝ)<scale k := by exact_mod_cast scale_pos k
  calc
    _ ≤ ∑r∈blockSource X k,‖modeWeight X s i j ω r/(index r:ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑_r∈blockSource X k,1/(scale k:ℝ) := by
      apply Finset.sum_le_sum
      intro r hr
      have hrM : (scale k:ℝ) ≤ index r := by exact_mod_cast (index_range X hX k r hr).1
      rw [norm_div,Complex.norm_natCast]
      exact (div_le_div_of_nonneg_right (modeWeight_norm X s i j ω r) (Nat.cast_nonneg _)).trans
        (one_div_le_one_div_of_le hM hrM)
    _ = ((blockSource X k).card:ℝ)/(scale k:ℝ) := by simp [div_eq_mul_inv]
    _ ≤ 1 := (div_le_one hM).mpr (by exact_mod_cast block_card X hX k)

theorem smoothing_error (X s x δ ε σ C : ℝ) (i j : ℕ) (k : BlockKey) (ω : Fin 9→ℝ)
    (hX : 2≤X) (hx : x∈Icc X (2*X)) (hδ : δ∈Icc 0 (1/2))
    (hε : ε∈Ioo 0 (1/4)) (hσ : 1<σ) (hσ2 : σ≤2) (hscale : 256*(scale k:ℝ)≤X)
    (hclose : ‖mellin (fun y => (Smooth1 smoothing ε y:ℂ)) 1-1‖≤C*ε) :
    ‖continuousContour X s x δ ε σ i j k ω-((x*δ:ℝ):ℂ)*mainMass X s i j k ω‖ ≤
      C*ε*(x*δ) := by
  rw [continuousContour_eq X s x δ ε σ i j k ω hX hx hδ hε hσ hσ2 hscale]
  have hwidth : 0≤x*δ := mul_nonneg (by linarith [hx.1]) hδ.1
  have he : ((x*δ:ℝ):ℂ)*mellin (fun y => (Smooth1 smoothing ε y:ℂ)) 1*mainMass X s i j k ω-
      ((x*δ:ℝ):ℂ)*mainMass X s i j k ω =
      ((x*δ:ℝ):ℂ)*(mellin (fun y => (Smooth1 smoothing ε y:ℂ)) 1-1)*mainMass X s i j k ω := by ring
  rw [he,norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hwidth]
  have hCe : 0≤C*ε := (norm_nonneg _).trans hclose
  exact (mul_le_mul (mul_le_mul_of_nonneg_left hclose hwidth)
    (mainMass_norm X s hX i j k ω) (norm_nonneg _) (mul_nonneg hwidth hCe)).trans_eq (by ring)

run_cmd do
  for decl in [``block_card, ``modeWeight_norm, ``mainMass_norm, ``smoothing_error] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end OuterBlockMassBudgetWork
