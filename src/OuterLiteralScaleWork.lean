import OuterLiteralFactorizationWork
import OuterPairFourthScaleWork

/-! Literal dyadic scales and prime-supported tuple factors for the exact
factorization. Active labels supply witnesses before Fourier expansion. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
attribute [local instance] Classical.propDecidable
open Filter
open scoped BigOperators
namespace OuterLiteralScaleWork
open OuterLiteralFactorizationWork OuterActiveDyadicWork OuterSourceReindexWork
open OuterSmoothSupportGeometryWork OuterSmoothErrorSupportWork OuterBlockCofactorWork
open OuterModeUnitCapWork Erdos374.HarmanGram152

def primeScale (k : BlockKey) : ℕ := 2^k.1
def divisorScale (k : BlockKey) : ℕ := 2^k.2.1
def firstScale (k : BlockKey) : ℕ := 2^k.2.2.1
def secondScale (k : BlockKey) : ℕ := 2^k.2.2.2

def firstPrimes (X : ℝ) (k : BlockKey) : Finset ℕ := (firstSet X k).filter Nat.Prime
def secondPrimes (X : ℝ) (k : BlockKey) : Finset ℕ := (secondSet X k).filter Nat.Prime

theorem log2_bounds (n e : ℕ) (hn : 0<n) (he : n.log2=e) : 2^e≤n ∧ n<2*2^e := by
  have hl := Nat.log2_self_le hn.ne'
  have hu := Nat.lt_log2_self (n:=n)
  rw [he] at hl hu
  rw [Nat.pow_succ] at hu
  exact ⟨hl,by omega⟩

theorem prime_log2_bounds (n e : ℕ) (hn : n.Prime) (he : n.log2=e) (hbig : 2<2^e) :
    2^e<n ∧ n≤2*2^e := by
  have hh := log2_bounds n e hn.pos he
  refine ⟨lt_of_le_of_ne hh.1 ?_,hh.2.le⟩
  intro hEq
  have hpow : (2^e).Prime := hEq.symm ▸ hn
  have he1 := hpow.eq_one_of_pow
  simp [he1] at hbig

theorem primeSet_bounds (X : ℝ) (k : BlockKey) (hbig : 2<primeScale k) :
    ∀p∈primeSet X k,p.Prime ∧ primeScale k<p ∧ p≤2*primeScale k := by
  intro p hp
  have hh := PositiveSharpSieveDecomposition.large_band_bounds X p (Finset.mem_filter.mp hp).1
  exact ⟨hh.1,prime_log2_bounds p k.1 hh.1 (Finset.mem_filter.mp hp).2 hbig⟩

theorem firstPrimes_bounds (X : ℝ) (k : BlockKey) (hbig : 2<firstScale k) :
    ∀p∈firstPrimes X k,p.Prime ∧ firstScale k<p ∧ p≤2*firstScale k := by
  intro p hp
  have hh := Finset.mem_filter.mp hp
  exact ⟨hh.2,prime_log2_bounds p k.2.2.1 hh.2 (Finset.mem_filter.mp hh.1).2 hbig⟩

theorem secondPrimes_bounds (X : ℝ) (k : BlockKey) (hbig : 2<secondScale k) :
    ∀p∈secondPrimes X k,p.Prime ∧ secondScale k<p ∧ p≤2*secondScale k := by
  intro p hp
  have hh := Finset.mem_filter.mp hp
  exact ⟨hh.2,prime_log2_bounds p k.2.2.2 hh.2 (Finset.mem_filter.mp hh.1).2 hbig⟩

theorem divisorSet_bounds (X : ℝ) (k : BlockKey) :
    ∀d∈divisorSet X k,divisorScale k≤d ∧ d<2*divisorScale k := by
  intro d hd
  exact log2_bounds d k.2.1 (Finset.mem_Ioc.mp (Finset.mem_filter.mp hd).1).1
    (Finset.mem_filter.mp hd).2

theorem pair_prime_trim (X s σ u v : ℝ) (i j : ℕ) (k : BlockKey) :
    pairPolynomial (firstSet X k) (secondSet X k) (pairWeight X s i j) σ u v=
      pairPolynomial (firstPrimes X k) (secondPrimes X k) (pairWeight X s i j) σ u v := by
  unfold pairPolynomial verticalDirichlet152 firstPrimes secondPrimes
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases hpa : a.Prime
  · simp only [if_pos hpa]
    congr 1
    apply Finset.sum_congr rfl
    intro b hb
    by_cases hpb : b.Prime
    · simp only [if_pos hpb]
    · have hz : pairWeight X s i j a b=0 := by
        simp [pairWeight,OuterSeparatedLogMaskWork.tupleMask,hpb]
      simp [hpb,hz]
  · have hz : ∀b,pairWeight X s i j a b=0 := by
      intro b
      simp [pairWeight,OuterSeparatedLogMaskWork.tupleMask,hpa]
    simp [hpa,hz]

theorem mode_prime_factorization (X s σ t : ℝ) (i j : ℕ) (k : BlockKey) (ω : Fin 9→ℝ) (hX : 2≤X) :
    OuterBlockMainTermWork.modePolynomial X s i j k ω σ t=
      OuterDivisorModeWork.divisorFactor X s i j ω (divisorSet X k) (primeSet X k)
        (firstPrimes X k) (secondPrimes X k) (fun _ => pairWeight X s i j) σ t := by
  rw [mode_factorization X s σ t i j k ω hX]
  simp only [OuterDivisorModeWork.divisorFactor,remainingFactor,pair_prime_trim]

theorem eventually_active_scales :
    ∀ᶠ X : ℝ in atTop,256≤X ∧ ∀(s : ℝ) (i j : ℕ) (k : BlockKey),
      k∈activeKeys X s i j →
      (1/2:ℝ)*X^(9/35:ℝ)≤primeScale k ∧ (primeScale k:ℝ)≤X ∧ 16≤primeScale k ∧
      X^(227/1000:ℝ)≤firstScale k ∧ X^(227/1000:ℝ)≤secondScale k ∧
      2<firstScale k ∧ 2<secondScale k ∧
      ((4*(firstScale k*secondScale k):ℕ):ℝ)≤X ∧ (upper X k:ℝ)≤X := by
  filter_upwards [eventually_ge_atTop (256:ℝ),OuterPairFourthScaleWork.eventually_actual_pair_scales,
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<9/35)).eventually (eventually_ge_atTop (32:ℝ)),
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<227/1000)).eventually (eventually_ge_atTop (3:ℝ)),
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<63/125)).eventually (eventually_ge_atTop (4:ℝ))]
    with X hX hpair hp32 hp3 hp4
  refine ⟨hX,?_⟩
  intro s i j k hk
  have hX2 : 2≤X := by linarith
  have hXp : 0<X := by linarith
  obtain ⟨r,hr,he⟩ := Finset.mem_image.mp hk
  have hd := ambient_data X hX2 r (active_data X s i j r hr).1
  have hblock : r∈OuterRectangularBlocksWork.blockSource X k := Finset.mem_filter.mpr ⟨(active_data X s i j r hr).1,he⟩
  have hmem : r∈localizedSource X s i j := active_subset_localized X s i j hr
  have he0 := congrArg (fun z : BlockKey => z.1) he
  have he1 := congrArg (fun z : BlockKey => z.2.2.1) he
  have he2 := congrArg (fun z : BlockKey => z.2.2.2) he
  have hp := log2_bounds r.1 k.1 hd.2.2.1 he0
  have ha := log2_bounds (drop r).2.1 k.2.2.1 hd.2.2.2.2.2.1 he1
  have hb := log2_bounds (drop r).2.2 k.2.2.2 hd.2.2.2.2.2.2 he2
  have hpr : r.1∈PositiveSharpBoxedCount.largePrimes X := by
    rw [block_eq_image X k hX2] at hblock
    obtain ⟨z,hz,her⟩ := Finset.mem_image.mp hblock
    have hz' := (Finset.mem_product.mp (Finset.mem_product.mp hz).2).1
    simpa only [←her,encode] using (Finset.mem_filter.mp hz').1
  have hpl := (PositiveSharpSieveDecomposition.large_band_bounds X r.1 hpr).2.1
  have hpU : (r.1:ℝ)<2*(primeScale k:ℝ) := by exact_mod_cast hp.2
  have hNp : (1/2:ℝ)*X^(9/35:ℝ)≤primeScale k := by linarith
  have hNpX : (primeScale k:ℝ)≤X := (by exact_mod_cast hp.1 : (primeScale k:ℝ)≤r.1).trans hd.2.2.2.1
  have hNp16 : 16≤primeScale k := by exact_mod_cast (show (16:ℝ)≤primeScale k by linarith)
  have hpairs := hpair.2 s i j r hmem (firstScale k) (secondScale k) ha.2.le hb.2.le
  have hNa3 : 2<firstScale k := by exact_mod_cast (show (2:ℝ)<firstScale k by linarith [hpairs.1])
  have hNb3 : 2<secondScale k := by exact_mod_cast (show (2:ℝ)<secondScale k by linarith [hpairs.2])
  have hslice := hd.2.1
  simp only [OuterBoundaryExtensionWork.candidateSlices,Finset.mem_product,Finset.mem_Ioc] at hslice
  have hNa : (firstScale k:ℝ)≤X^(31/125:ℝ) := (by exact_mod_cast ha.1 : (firstScale k:ℝ)≤(drop r).2.1).trans
    ((by exact_mod_cast hslice.2.1.2 : ((drop r).2.1:ℝ)≤⌊X^(31/125:ℝ)⌋₊).trans (Nat.floor_le (by positivity)))
  have hNb : (secondScale k:ℝ)≤X^(31/125:ℝ) := (by exact_mod_cast hb.1 : (secondScale k:ℝ)≤(drop r).2.2).trans
    ((by exact_mod_cast hslice.2.2.2 : ((drop r).2.2:ℝ)≤⌊X^(31/125:ℝ)⌋₊).trans (Nat.floor_le (by positivity)))
  have hprod : ((4*(firstScale k*secondScale k):ℕ):ℝ)≤X := by
    have hh := mul_le_mul hNa hNb (Nat.cast_nonneg _) (by positivity)
    rw [←Real.rpow_add hXp] at hh
    norm_num at hh
    have hh' := mul_le_mul_of_nonneg_right hp4 (Real.rpow_nonneg hXp.le (62/125))
    rw [←Real.rpow_add hXp] at hh'
    norm_num at hh'
    push_cast
    nlinarith
  have hM : 16≤scale k := by
    have hd1 : 1≤divisorScale k := by unfold divisorScale; exact Nat.one_le_pow _ _ (by norm_num)
    have ha1 : 1≤firstScale k := by unfold firstScale; exact Nat.one_le_pow _ _ (by norm_num)
    have hb1 : 1≤secondScale k := by unfold secondScale; exact Nat.one_le_pow _ _ (by norm_num)
    change 16≤primeScale k*divisorScale k*firstScale k*secondScale k
    exact hNp16.trans (le_trans (Nat.le_mul_of_pos_right _ hd1)
      ((Nat.le_mul_of_pos_right _ ha1).trans (Nat.le_mul_of_pos_right _ hb1)))
  have hMR : (0:ℝ)<scale k := by exact_mod_cast scale_pos k
  have hM16 : (16:ℝ)≤scale k := by exact_mod_cast hM
  have hu : (upper X k:ℝ)<8*X/(scale k:ℝ)+1 := Nat.ceil_lt_add_one (by positivity)
  have huX : (upper X k:ℝ)≤X := by
    have hh : 8*X/(scale k:ℝ)≤X/2 := (div_le_iff₀ hMR).mpr (by nlinarith)
    linarith
  exact ⟨hNp,hNpX,hNp16,hpairs.1,hpairs.2,hNa3,hNb3,hprod,huX⟩

run_cmd do
  for decl in [``log2_bounds, ``prime_log2_bounds, ``primeSet_bounds, ``firstPrimes_bounds,
      ``secondPrimes_bounds, ``divisorSet_bounds, ``pair_prime_trim, ``mode_prime_factorization,
      ``eventually_active_scales] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end OuterLiteralScaleWork
