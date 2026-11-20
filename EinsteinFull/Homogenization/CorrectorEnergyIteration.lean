import EinsteinFull.Homogenization.HighContrastCaccioppoli
import EinsteinFull.Homogenization.CubeOscillationPairing
import EinsteinFull.Homogenization.LinearWeakGradient

/-!
# Energy bounds for whole-space solutions by iteration over scales

For a whole-space solution of a divergence-form equation with a pointwise `(1, K)`-elliptic
coefficient, the Caccioppoli inequality on origin cubes and the oscillation bound from
smooth-test pairings combine into a bound of the energy at one scale by a constant plus a
small multiple of the energy at a larger scale. A growth condition at infinity then closes
the iteration, as in the large-scale regularity theory of Armstrong, Kuusi and Mourrat,
*Quantitative Stochastic Homogenization and Large-Scale Regularity*, Chapter 3.
-/

open MeasureTheory Filter Topology

namespace EinsteinFull.Homogenization

open _root_.Homogenization hiding euclideanBall
open _root_.Homogenization.HighContrast

variable {d : ℕ}

theorem mem_cubeSet_originCube_iff {n : ℕ} {x : Vec d} :
    x ∈ cubeSet (originCube d (n : ℤ)) ↔
      ∀ i, -((3 : ℝ) ^ n / 2) ≤ x i ∧ x i < (3 : ℝ) ^ n / 2 := by
  have hs := cubeScaleFactor_originCube (d := d) n
  simp only [cubeSet, Set.mem_ofPred_eq]
  refine forall_congr' fun i => ?_
  simp only [originCube, Pi.zero_apply, Int.cast_zero, zero_sub, zero_add]
  rw [show cubeScaleFactor ({ scale := (n : ℤ), index := 0 } : TriadicCube d) = (3 : ℝ) ^ n
    from hs]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

theorem cubeSet_originCube_subset_euclideanBall [NeZero d] (n : ℕ) :
    cubeSet (originCube d (n : ℤ)) ⊆ euclideanBall d (Real.sqrt d * (3 : ℝ) ^ n) := by
  intro x hx
  have hcoord := mem_cubeSet_originCube_iff.mp hx
  have hpos : (0 : ℝ) < (3 : ℝ) ^ n := by positivity
  have hd : (0 : ℝ) < d := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne d))
  have hsum : vecNormSq x ≤ d * ((3 : ℝ) ^ n / 2) ^ 2 := by
    change ∑ i, x i * x i ≤ _
    calc ∑ i, x i * x i ≤ ∑ _i : Fin d, ((3 : ℝ) ^ n / 2) ^ 2 := by
          refine Finset.sum_le_sum fun i _ => ?_
          have h := hcoord i
          nlinarith [h.1, h.2]
      _ = d * ((3 : ℝ) ^ n / 2) ^ 2 := by simp
  show vecNormSq (x - 0) < (Real.sqrt d * (3 : ℝ) ^ n) ^ 2
  rw [sub_zero, mul_pow, Real.sq_sqrt hd.le]
  have h0 : (0 : ℝ) < d * ((3 : ℝ) ^ n) ^ 2 := by positivity
  have h1 : d * ((3 : ℝ) ^ n / 2) ^ 2 = d * ((3 : ℝ) ^ n) ^ 2 / 4 := by ring
  linarith

theorem euclideanBall_subset_cubeSet_originCube {R : ℝ} {n : ℕ} (hR0 : 0 ≤ R)
    (hR : R ≤ (3 : ℝ) ^ n / 2) :
    euclideanBall d R ⊆ cubeSet (originCube d (n : ℤ)) :=
  (euclideanBall_subset_openCubeSet_originCube hR0 hR).trans (openCubeSet_subset_cubeSet _)

theorem four_mul_sqrt_le_three_pow (d : ℕ) : 4 * Real.sqrt d ≤ (3 : ℝ) ^ (d + 1) := by
  have h1 : Real.sqrt d ≤ (d + 1) / 2 := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    nlinarith [sq_nonneg ((d : ℝ) - 1)]
  have h2 : (1 : ℝ) + (d + 1 : ℕ) * 2 ≤ (1 + 2) ^ (d + 1) :=
    one_add_le_pow_of_two_add_nonneg (by norm_num) (d + 1)
  push_cast at h2
  norm_num at h2
  nlinarith

/-- **Caccioppoli inequality on origin cubes.** The energy on the origin cube of side `3ⁿ` is
controlled by the square deviation on the origin cube of side `3^(n + d + 1)`. -/
theorem caccioppoli_originCube [NeZero d] {f : CoeffField d} {K : ℝ} (hK : 1 ≤ K)
    (hfm : Measurable (fun x i j => f x i j)) (hf : ∀ x, IsEllipticMatrix 1 K (f x))
    {v : Vec d → ℝ} {Dv : Vec d → Vec d} (hw : HasWeakGradientOn Set.univ v Dv)
    (hloc : ∀ R : ℝ, 0 < R → MemLp v 2 (volume.restrict (euclideanBall d R)) ∧
      ∀ i, MemLp (fun x => Dv x i) 2 (volume.restrict (euclideanBall d R)))
    (hsol : IsWeakSolutionOn f Set.univ Dv) (n : ℕ) (k : ℝ) :
    ∫ x in cubeSet (originCube d (n : ℤ)), vecNormSq (Dv x) ≤
      4096 * K / (d * (3 : ℝ) ^ (2 * n)) *
        ∫ x in cubeSet (originCube d ((n + d + 1 : ℕ) : ℤ)), (v x - k) ^ 2 := by
  have hd : (0 : ℝ) < d := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne d))
  set r := Real.sqrt d * (3 : ℝ) ^ n with hr_def
  have hr : 0 < r := by positivity
  have hcac := caccioppoli_euclideanBall hK hfm hf hw hr (hloc (4 * r) (by positivity)).1
    (hloc (4 * r) (by positivity)).2 hsol k
  have hQB : cubeSet (originCube d (n : ℤ)) ⊆ euclideanBall d r :=
    cubeSet_originCube_subset_euclideanBall n
  have hBQ : euclideanBall d (2 * r) ⊆ cubeSet (originCube d ((n + d + 1 : ℕ) : ℤ)) := by
    refine euclideanBall_subset_cubeSet_originCube (by positivity) ?_
    have h := four_mul_sqrt_le_three_pow d
    rw [hr_def, show n + d + 1 = n + (d + 1) by ring, pow_add]
    have h3 : (0 : ℝ) < (3 : ℝ) ^ n := by positivity
    nlinarith
  have hBQ' : euclideanBall d r ⊆ euclideanBall d (4 * r) := by
    intro x hx
    have hx' : vecNormSq (x - 0) < r ^ 2 := hx
    show vecNormSq (x - 0) < (4 * r) ^ 2
    nlinarith
  have hDint : IntegrableOn (fun x => vecNormSq (Dv x)) (euclideanBall d r) volume := by
    have h := integrable_finsetSum (μ := volume.restrict (euclideanBall d r)) Finset.univ
      fun i _ => (((hloc r hr).2 i).integrable_sq)
    refine h.congr (Filter.Eventually.of_forall fun x => ?_)
    simp [vecNormSq, vecDot, sq]
  have hRbig : 0 < Real.sqrt d * (3 : ℝ) ^ (n + d + 1) := by positivity
  have hvint : IntegrableOn (fun x => (v x - k) ^ 2)
      (cubeSet (originCube d ((n + d + 1 : ℕ) : ℤ))) volume := by
    have hmem := (hloc _ hRbig).1
    have hsub := cubeSet_originCube_subset_euclideanBall (d := d) (n + d + 1)
    have hmemQ : MemLp v 2 (volume.restrict (cubeSet (originCube d ((n + d + 1 : ℕ) : ℤ)))) :=
      hmem.mono_measure (Measure.restrict_mono hsub le_rfl)
    have : IsFiniteMeasure (volume.restrict (cubeSet (originCube d ((n + d + 1 : ℕ) : ℤ)))) :=
      isFiniteMeasure_restrict.mpr (volume_cubeSet_lt_top _).ne
    exact (hmemQ.sub (memLp_const k)).integrable_sq
  have h1 : ∫ x in cubeSet (originCube d (n : ℤ)), vecNormSq (Dv x) ≤
      ∫ x in euclideanBall d r, vecNormSq (Dv x) :=
    setIntegral_mono_set hDint (Filter.Eventually.of_forall fun x => vecNormSq_nonneg _)
      (Filter.Eventually.of_forall hQB)
  have h2 : ∫ x in euclideanBall d (2 * r), (v x - k) ^ 2 ≤
      ∫ x in cubeSet (originCube d ((n + d + 1 : ℕ) : ℤ)), (v x - k) ^ 2 :=
    setIntegral_mono_set hvint (Filter.Eventually.of_forall fun x => sq_nonneg _)
      (Filter.Eventually.of_forall hBQ)
  have hconst : 4 * K * (32 / r) ^ 2 = 4096 * K / (d * (3 : ℝ) ^ (2 * n)) := by
    rw [hr_def, div_pow, mul_pow, Real.sq_sqrt hd.le, ← pow_mul, mul_comm n 2]
    ring
  have hc0 : 0 ≤ 4 * K * (32 / r) ^ 2 := by positivity
  calc ∫ x in cubeSet (originCube d (n : ℤ)), vecNormSq (Dv x)
      ≤ ∫ x in euclideanBall d r, vecNormSq (Dv x) := h1
    _ ≤ 4 * K * (32 / r) ^ 2 * ∫ x in euclideanBall d (2 * r), (v x - k) ^ 2 := hcac
    _ ≤ 4 * K * (32 / r) ^ 2 *
        ∫ x in cubeSet (originCube d ((n + d + 1 : ℕ) : ℤ)), (v x - k) ^ 2 :=
        mul_le_mul_of_nonneg_left h2 hc0
    _ = _ := by rw [hconst]

/-- **Closing an iteration over scales.** If a nonnegative sequence satisfies
`E n ≤ B + θ E (n + c)` from some index on, with `θ < 1`, and the discounted values
`θᵏ E (n + k c)` tend to zero, then `E n ≤ B / (1 - θ)` from that index on. -/
theorem le_div_one_sub_of_iterate {E : ℕ → ℝ} {B θ : ℝ} {n₀ c : ℕ} (hθ0 : 0 ≤ θ)
    (hθ1 : θ < 1) (hB : 0 ≤ B) (hstep : ∀ n, n₀ ≤ n → E n ≤ B + θ * E (n + c))
    (hlim : ∀ n, Tendsto (fun k : ℕ => θ ^ k * E (n + k * c)) atTop (𝓝 0)) :
    ∀ n, n₀ ≤ n → E n ≤ B / (1 - θ) := by
  intro n hn
  have hpos : 0 < 1 - θ := by linarith
  have hk : ∀ k : ℕ, E n ≤ B * (1 - θ ^ k) / (1 - θ) + θ ^ k * E (n + k * c) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hs := hstep (n + k * c) (by omega)
      have hθk : 0 ≤ θ ^ k := pow_nonneg hθ0 k
      have hidx : n + k * c + c = n + (k + 1) * c := by ring
      rw [hidx] at hs
      have hsum : B * (1 - θ ^ k) / (1 - θ) + θ ^ k * B = B * (1 - θ ^ (k + 1)) / (1 - θ) := by
        field_simp
        ring
      calc E n ≤ B * (1 - θ ^ k) / (1 - θ) + θ ^ k * E (n + k * c) := ih
        _ ≤ B * (1 - θ ^ k) / (1 - θ) + θ ^ k * (B + θ * E (n + (k + 1) * c)) := by
            have := mul_le_mul_of_nonneg_left hs hθk
            linarith
        _ = (B * (1 - θ ^ k) / (1 - θ) + θ ^ k * B) + θ ^ (k + 1) * E (n + (k + 1) * c) := by
            ring
        _ = B * (1 - θ ^ (k + 1)) / (1 - θ) + θ ^ (k + 1) * E (n + (k + 1) * c) := by
            rw [hsum]
  have hk' : ∀ k : ℕ, E n ≤ B / (1 - θ) + θ ^ k * E (n + k * c) := by
    intro k
    have h := hk k
    have hle : B * (1 - θ ^ k) / (1 - θ) ≤ B / (1 - θ) := by
      apply div_le_div_of_nonneg_right _ hpos.le
      have : 0 ≤ θ ^ k := pow_nonneg hθ0 k
      nlinarith
    linarith
  have hlim' := (hlim n).const_add (B / (1 - θ))
  rw [add_zero] at hlim'
  exact ge_of_tendsto hlim' (Filter.Eventually.of_forall hk')

theorem exists_originCube_superset_of_isCompact {k : Set (Vec d)} (hk : IsCompact k) :
    ∃ N : ℕ, k ⊆ cubeSet (originCube d (N : ℤ)) := by
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Vec d)).mp hk.isBounded
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (2 * |r|) (by norm_num : (1 : ℝ) < 3)
  refine ⟨N, fun x hx => ?_⟩
  have hx' : ‖x‖ ≤ r := by simpa using hr hx
  rw [mem_cubeSet_originCube_iff]
  intro i
  have hi : |x i| ≤ r := (norm_le_pi_norm x i).trans hx'
  have hr' : r ≤ |r| := le_abs_self r
  constructor
  · have := neg_abs_le (x i)
    linarith [abs_nonneg (x i)]
  · have := le_abs_self (x i)
    linarith

theorem cubeVolume_originCube (n : ℕ) :
    cubeVolume (originCube d (n : ℤ)) = ((3 : ℝ) ^ n) ^ d := by
  rw [cubeVolume_eq_scaleFactor_pow, cubeScaleFactor_originCube]

/-- A whole-space weak solution of a divergence-form equation whose coefficient is measurable
and `(1, K)`-elliptic at every point, with locally square integrable value and gradient. -/
structure EllipticWholeSpaceSolution (d : ℕ) (K : ℝ) where
  /-- The coefficient field. -/
  coeff : CoeffField d
  measurable_coeff : Measurable (fun x i j => coeff x i j)
  elliptic : ∀ x, IsEllipticMatrix 1 K (coeff x)
  /-- The solution. -/
  v : Vec d → ℝ
  /-- Its weak gradient. -/
  Dv : Vec d → Vec d
  weak : HasWeakGradientOn Set.univ v Dv
  locL2 : ∀ R : ℝ, 0 < R → MemLp v 2 (volume.restrict (euclideanBall d R)) ∧
    ∀ i, MemLp (fun x => Dv x i) 2 (volume.restrict (euclideanBall d R))
  solution : IsWeakSolutionOn coeff Set.univ Dv

namespace EllipticWholeSpaceSolution

variable {K : ℝ} (s : EllipticWholeSpaceSolution d K)

/-- The solution minus the linear function of slope `e`. -/
def corrector (e : Vec d) (x : Vec d) : ℝ :=
  s.v x - vecDot e x

/-- The gradient of the solution minus `e`. -/
def correctorGrad (e : Vec d) (x : Vec d) : Vec d :=
  s.Dv x - e

theorem sqrt_mul_three_pow_pos [NeZero d] (n : ℕ) : 0 < Real.sqrt d * (3 : ℝ) ^ n :=
  mul_pos (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne d))))
    (by positivity)

theorem memLp_cubeSet_v [NeZero d] (n : ℕ) :
    MemLp s.v 2 (volume.restrict (cubeSet (originCube d (n : ℤ)))) :=
  (s.locL2 _ (sqrt_mul_three_pow_pos n)).1.mono_measure
    (Measure.restrict_mono (cubeSet_originCube_subset_euclideanBall n) le_rfl)

theorem memLp_cubeSet_Dv [NeZero d] (n : ℕ) (i : Fin d) :
    MemLp (fun x => s.Dv x i) 2 (volume.restrict (cubeSet (originCube d (n : ℤ)))) :=
  ((s.locL2 _ (sqrt_mul_three_pow_pos n)).2 i).mono_measure
    (Measure.restrict_mono (cubeSet_originCube_subset_euclideanBall n) le_rfl)

theorem locallyIntegrable_v [NeZero d] : LocallyIntegrable s.v volume := by
  rw [locallyIntegrable_iff]
  intro k hk
  obtain ⟨N, hN⟩ := exists_originCube_superset_of_isCompact hk
  have : IsFiniteMeasure (volume.restrict (cubeSet (originCube d (N : ℤ)))) :=
    isFiniteMeasure_restrict.mpr (volume_cubeSet_lt_top _).ne
  exact IntegrableOn.mono_set ((s.memLp_cubeSet_v N).integrable one_le_two) hN

theorem locallyIntegrable_Dv [NeZero d] (i : Fin d) :
    LocallyIntegrable (fun x => s.Dv x i) volume := by
  rw [locallyIntegrable_iff]
  intro k hk
  obtain ⟨N, hN⟩ := exists_originCube_superset_of_isCompact hk
  have : IsFiniteMeasure (volume.restrict (cubeSet (originCube d (N : ℤ)))) :=
    isFiniteMeasure_restrict.mpr (volume_cubeSet_lt_top _).ne
  exact IntegrableOn.mono_set ((s.memLp_cubeSet_Dv N i).integrable one_le_two) hN

/-- The corrector has the corrector gradient as weak gradient on the whole space. -/
theorem hasWeakGradientOn_corrector [NeZero d] (e : Vec d) :
    HasWeakGradientOn Set.univ (s.corrector e) (s.correctorGrad e) := by
  intro i χ hχ hcs hsub
  have haff := HasWeakPartialDerivOn.of_contDiff (U := Set.univ) (i := i)
    (contDiff_vecDot_left e) χ hχ hcs hsub
  have hv := s.weak i χ hχ hcs hsub
  simp only [fderiv_vecDot_left_apply] at haff
  simp only [Measure.restrict_univ] at haff hv ⊢
  have hχc : Continuous χ := hχ.continuous
  have hdχc : Continuous (fun x => fderiv ℝ χ x (basisVec i)) :=
    (hχ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdχs : HasCompactSupport (fun x => fderiv ℝ χ x (basisVec i)) :=
    hcs.fderiv_apply (𝕜 := ℝ) (basisVec i)
  have hi1 : Integrable (fun x => s.v x * fderiv ℝ χ x (basisVec i)) := by
    have := s.locallyIntegrable_v.integrable_smul_right_of_hasCompactSupport hdχc hdχs
    simpa [smul_eq_mul, mul_comm] using this
  have hi2 : Integrable (fun x => vecDot e x * fderiv ℝ χ x (basisVec i)) :=
    ((contDiff_vecDot_left e).continuous.mul hdχc).integrable_of_hasCompactSupport
      hdχs.mul_left
  have hi3 : Integrable (fun x => s.Dv x i * χ x) := by
    have := (s.locallyIntegrable_Dv i).integrable_smul_right_of_hasCompactSupport hχc hcs
    simpa [smul_eq_mul, mul_comm] using this
  have hi4 : Integrable (fun x => e i * χ x) :=
    (continuous_const.mul hχc).integrable_of_hasCompactSupport hcs.mul_left
  calc ∫ x, s.corrector e x * fderiv ℝ χ x (basisVec i)
      = ∫ x, (s.v x * fderiv ℝ χ x (basisVec i) -
          vecDot e x * fderiv ℝ χ x (basisVec i)) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [corrector]
        ring
    _ = -∫ x, (s.Dv x i * χ x - e i * χ x) := by
        rw [integral_sub hi1 hi2, hv, haff, integral_sub hi3 hi4]
        ring
    _ = -∫ x, s.correctorGrad e x i * χ x := by
        congr 1
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [correctorGrad, Pi.sub_apply]
        ring

/-- The corrector as an `H¹` function on the open origin cube of side `3ⁿ`. -/
def cubeH1 [NeZero d] (e : Vec d) (n : ℕ) : H1Function (openCubeSet (originCube d (n : ℤ))) where
  toFun := s.corrector e
  grad := s.correctorGrad e
  memL2 := by
    have h := (s.memLp_cubeSet_v n).mono_measure
      (Measure.restrict_mono (openCubeSet_subset_cubeSet _) le_rfl)
    have : IsFiniteMeasure (volume.restrict (openCubeSet (originCube d (n : ℤ)))) :=
      isFiniteMeasure_restrict.mpr
        ((measure_mono (openCubeSet_subset_cubeSet _)).trans_lt (volume_cubeSet_lt_top _)).ne
    have hlin : MemLp (fun x => vecDot e x) 2
        (volume.restrict (openCubeSet (originCube d (n : ℤ)))) := by
      refine MemLp.of_bound (contDiff_vecDot_left e).continuous.aestronglyMeasurable
        (∑ i, |e i| * ((3 : ℝ) ^ n / 2)) ?_
      refine ae_restrict_of_forall_mem (isOpen_openCubeSet _).measurableSet fun x hx => ?_
      have hcoord := mem_openCubeSet_originCube_iff.mp hx
      rw [Real.norm_eq_abs]
      calc |vecDot e x| = |∑ i, e i * x i| := rfl
        _ ≤ ∑ i, |e i * x i| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i, |e i| * ((3 : ℝ) ^ n / 2) := by
            refine Finset.sum_le_sum fun i _ => ?_
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_left (hcoord i).le (abs_nonneg _)
    exact h.sub hlin
  gradMemL2 := by
    intro i
    have h := (s.memLp_cubeSet_Dv n i).mono_measure
      (Measure.restrict_mono (openCubeSet_subset_cubeSet _) le_rfl)
    have : IsFiniteMeasure (volume.restrict (openCubeSet (originCube d (n : ℤ)))) :=
      isFiniteMeasure_restrict.mpr
        ((measure_mono (openCubeSet_subset_cubeSet _)).trans_lt (volume_cubeSet_lt_top _)).ne
    exact h.sub (memLp_const (e i))
  hasWeakGradient := (s.hasWeakGradientOn_corrector e).restrict (isOpen_openCubeSet _)
    (Set.subset_univ _)

/-- The normalized Caccioppoli inequality on origin cubes. -/
theorem cubeAverage_Dv_le [NeZero d] (hK : 1 ≤ K) (n : ℕ) (k : ℝ) :
    cubeAverage (originCube d (n : ℤ)) (fun x => vecNormSq (s.Dv x)) ≤
      4096 * K * (3 : ℝ) ^ ((d + 1) * d) / (d * (3 : ℝ) ^ (2 * n)) *
        cubeAverage (originCube d ((n + d + 1 : ℕ) : ℤ)) (fun x => (s.v x - k) ^ 2) := by
  have hd : (0 : ℝ) < d := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne d))
  have hcac := caccioppoli_originCube hK s.measurable_coeff s.elliptic s.weak s.locL2
    s.solution n k
  have hI : 0 ≤ ∫ x in cubeSet (originCube d ((n + d + 1 : ℕ) : ℤ)), (s.v x - k) ^ 2 :=
    setIntegral_nonneg (measurableSet_cubeSet _) fun x _ => sq_nonneg _
  unfold cubeAverage
  rw [cubeVolume_originCube, cubeVolume_originCube]
  have hpow : ((3 : ℝ) ^ (n + d + 1)) ^ d = ((3 : ℝ) ^ n) ^ d * (3 : ℝ) ^ ((d + 1) * d) := by
    rw [show n + d + 1 = n + (d + 1) by ring, pow_add, mul_pow, ← pow_mul (3 : ℝ) (d + 1) d]
  rw [hpow]
  have h3n : (0 : ℝ) < ((3 : ℝ) ^ n) ^ d := by positivity
  have h3c : (0 : ℝ) < (3 : ℝ) ^ ((d + 1) * d) := by positivity
  have h32 : (0 : ℝ) < (3 : ℝ) ^ (2 * n) := by positivity
  calc (((3 : ℝ) ^ n) ^ d)⁻¹ * ∫ x in cubeSet (originCube d (n : ℤ)), vecNormSq (s.Dv x)
      ≤ (((3 : ℝ) ^ n) ^ d)⁻¹ * (4096 * K / (d * (3 : ℝ) ^ (2 * n)) *
          ∫ x in cubeSet (originCube d ((n + d + 1 : ℕ) : ℤ)), (s.v x - k) ^ 2) :=
        mul_le_mul_of_nonneg_left hcac (by positivity)
    _ = _ := by
        field_simp

theorem abs_vecDot_le_of_mem_cubeSet (e : Vec d) {N : ℕ} {x : Vec d}
    (hx : x ∈ cubeSet (originCube d (N : ℤ))) :
    |vecDot e x| ≤ ∑ i, |e i| * ((3 : ℝ) ^ N / 2) := by
  have hcoord := mem_cubeSet_originCube_iff.mp hx
  calc |vecDot e x| = |∑ i, e i * x i| := rfl
    _ ≤ ∑ i, |e i * x i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |e i| * ((3 : ℝ) ^ N / 2) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [abs_mul]
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        exact abs_le.mpr ⟨(hcoord i).1, (hcoord i).2.le⟩

theorem sq_vecDot_le_of_mem_cubeSet (e : Vec d) {N : ℕ} {x : Vec d}
    (hx : x ∈ cubeSet (originCube d (N : ℤ))) :
    vecDot e x ^ 2 ≤ vecNormSq e * (d * ((3 : ℝ) ^ N / 2) ^ 2) := by
  have hcoord := mem_cubeSet_originCube_iff.mp hx
  have hx2 : vecNormSq x ≤ d * ((3 : ℝ) ^ N / 2) ^ 2 := by
    change ∑ i, x i * x i ≤ _
    calc ∑ i, x i * x i ≤ ∑ _i : Fin d, ((3 : ℝ) ^ N / 2) ^ 2 := by
          refine Finset.sum_le_sum fun i _ => ?_
          have h := hcoord i
          nlinarith [h.1, h.2]
      _ = d * ((3 : ℝ) ^ N / 2) ^ 2 := by simp
  calc vecDot e x ^ 2 ≤ vecNormSq e * vecNormSq x := sq_vecDot_le_vecNormSq_mul_vecNormSq e x
    _ ≤ vecNormSq e * (d * ((3 : ℝ) ^ N / 2) ^ 2) :=
        mul_le_mul_of_nonneg_left hx2 (vecNormSq_nonneg e)

theorem memLp_cubeSet_vecDot (e : Vec d) (N : ℕ) :
    MemLp (fun x => vecDot e x) 2 (volume.restrict (cubeSet (originCube d (N : ℤ)))) := by
  have : IsFiniteMeasure (volume.restrict (cubeSet (originCube d (N : ℤ)))) :=
    isFiniteMeasure_restrict.mpr (volume_cubeSet_lt_top _).ne
  refine MemLp.of_bound (contDiff_vecDot_left e).continuous.aestronglyMeasurable
    (∑ i, |e i| * ((3 : ℝ) ^ N / 2)) ?_
  refine ae_restrict_of_forall_mem (measurableSet_cubeSet _) fun x hx => ?_
  rw [Real.norm_eq_abs]
  exact abs_vecDot_le_of_mem_cubeSet e hx

theorem memLp_cubeSet_corrector [NeZero d] (e : Vec d) (N : ℕ) :
    MemLp (s.corrector e) 2 (volume.restrict (cubeSet (originCube d (N : ℤ)))) :=
  (s.memLp_cubeSet_v N).sub (memLp_cubeSet_vecDot e N)

theorem cubeAverage_const_add_two_mul (Q : TriadicCube d) (C : ℝ) {g : Vec d → ℝ}
    (hg : IntegrableOn g (cubeSet Q) volume) :
    cubeAverage Q (fun x => C + 2 * g x) = C + 2 * cubeAverage Q g := by
  have hfin : volume (cubeSet Q) < ⊤ := volume_cubeSet_lt_top Q
  have hv : 0 < cubeVolume Q := cubeVolume_pos Q
  unfold cubeAverage
  rw [integral_add (integrableOn_const (C := C) hfin.ne) (hg.const_mul 2), setIntegral_const,
    integral_const_mul, smul_eq_mul, measureReal_def, volume_cubeSet_toReal]
  field_simp

/-- The square deviation of the solution from the mean of the corrector on an origin cube. -/
theorem cubeAverage_sq_v_sub_le [NeZero d] (e : Vec d) (N : ℕ) :
    cubeAverage (originCube d (N : ℤ))
        (fun x => (s.v x - cubeAverage (originCube d (N : ℤ)) (s.corrector e)) ^ 2) ≤
      vecNormSq e * (d * ((3 : ℝ) ^ N / 2) ^ 2) * 2 +
        2 * cubeBesovOscillation (originCube d (N : ℤ)) 2 (s.corrector e) ^ 2 := by
  have hΦ := s.memLp_cubeSet_corrector e N
  have : IsFiniteMeasure (volume.restrict (cubeSet (originCube d (N : ℤ)))) :=
    isFiniteMeasure_restrict.mpr (volume_cubeSet_lt_top _).ne
  set k := cubeAverage (originCube d (N : ℤ)) (s.corrector e) with hk
  have hfl : MemLp (fun x => s.corrector e x - k) 2
      (volume.restrict (cubeSet (originCube d (N : ℤ)))) := hΦ.sub (memLp_const k)
  have hnorm : MemLp (cubeFluctuation (originCube d (N : ℤ)) (s.corrector e)) 2
      (normalizedCubeMeasure (originCube d (N : ℤ))) :=
    hfl.smul_measure ENNReal.ofReal_ne_top
  have hosc : cubeBesovOscillation (originCube d (N : ℤ)) 2 (s.corrector e) ^ 2 =
      cubeAverage (originCube d (N : ℤ)) (fun x => (s.corrector e x - k) ^ 2) :=
    (integrable_and_cubeLpNorm_sq_eq_cubeAverage_sq _ _ hnorm).2
  rw [hosc]
  have hint1 : IntegrableOn (fun x => (s.v x - k) ^ 2) (cubeSet (originCube d (N : ℤ))) volume :=
    ((s.memLp_cubeSet_v N).sub (memLp_const k)).integrable_sq
  have hsq : IntegrableOn (fun x => (s.corrector e x - k) ^ 2)
      (cubeSet (originCube d (N : ℤ))) volume := hfl.integrable_sq
  set C := vecNormSq e * (d * ((3 : ℝ) ^ N / 2) ^ 2) * 2 with hC
  have hint2 : IntegrableOn (fun x => C + 2 * (s.corrector e x - k) ^ 2)
      (cubeSet (originCube d (N : ℤ))) volume :=
    (integrableOn_const (C := C) (volume_cubeSet_lt_top _).ne).add (hsq.const_mul 2)
  have hpt : ∀ x ∈ cubeSet (originCube d (N : ℤ)),
      (s.v x - k) ^ 2 ≤ C + 2 * (s.corrector e x - k) ^ 2 := by
    intro x hx
    have h1 := sq_vecDot_le_of_mem_cubeSet e hx
    have h2 : s.v x - k = vecDot e x + (s.corrector e x - k) := by
      simp only [corrector]
      ring
    rw [h2, hC]
    nlinarith [sq_nonneg (vecDot e x - (s.corrector e x - k))]
  calc cubeAverage (originCube d (N : ℤ)) (fun x => (s.v x - k) ^ 2)
      ≤ cubeAverage (originCube d (N : ℤ)) (fun x => C + 2 * (s.corrector e x - k) ^ 2) :=
        mul_le_mul_of_nonneg_left
          (setIntegral_mono_on hint1 hint2 (measurableSet_cubeSet _) hpt)
          (inv_nonneg.mpr (cubeVolume_nonneg _))
    _ = C + 2 * cubeAverage (originCube d (N : ℤ)) (fun x => (s.corrector e x - k) ^ 2) :=
        cubeAverage_const_add_two_mul _ C hsq

theorem vecNormSq_sub_le_two_mul (a b : Vec d) :
    vecNormSq (a - b) ≤ 2 * vecNormSq a + 2 * vecNormSq b := by
  simp only [vecNormSq, vecDot, Pi.sub_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  nlinarith [sq_nonneg (a i + b i)]

theorem integrableOn_vecNormSq_Dv [NeZero d] (N : ℕ) :
    IntegrableOn (fun x => vecNormSq (s.Dv x)) (cubeSet (originCube d (N : ℤ))) volume := by
  have h := integrable_finsetSum (μ := volume.restrict (cubeSet (originCube d (N : ℤ))))
    Finset.univ fun i _ => (s.memLp_cubeSet_Dv N i).integrable_sq
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  simp [vecNormSq, vecDot, sq]

/-- The corrector energy is at most twice the solution energy plus twice `|e|²`. -/
theorem cubeAverage_correctorGrad_le [NeZero d] (e : Vec d) (N : ℕ) :
    cubeAverage (originCube d (N : ℤ)) (fun x => vecNormSq (s.correctorGrad e x)) ≤
      2 * vecNormSq e + 2 * cubeAverage (originCube d (N : ℤ)) (fun x => vecNormSq (s.Dv x)) := by
  have hDv := s.integrableOn_vecNormSq_Dv N
  have hint1 : IntegrableOn (fun x => vecNormSq (s.correctorGrad e x))
      (cubeSet (originCube d (N : ℤ))) volume := by
    have h := integrable_finsetSum (μ := volume.restrict (cubeSet (originCube d (N : ℤ))))
      Finset.univ fun i _ => ((s.memLp_cubeSet_Dv N i).sub (memLp_const (e i))).integrable_sq
    refine h.congr (Filter.Eventually.of_forall fun x => ?_)
    simp [vecNormSq, vecDot, sq, correctorGrad]
  have hint2 : IntegrableOn (fun x => 2 * vecNormSq e + 2 * vecNormSq (s.Dv x))
      (cubeSet (originCube d (N : ℤ))) volume :=
    (integrableOn_const (C := 2 * vecNormSq e) (volume_cubeSet_lt_top _).ne).add
      (hDv.const_mul 2)
  calc cubeAverage (originCube d (N : ℤ)) (fun x => vecNormSq (s.correctorGrad e x))
      ≤ cubeAverage (originCube d (N : ℤ)) (fun x => 2 * vecNormSq e + 2 * vecNormSq (s.Dv x)) :=
        mul_le_mul_of_nonneg_left
          (setIntegral_mono_on hint1 hint2 (measurableSet_cubeSet _) fun x _ => by
            have h := vecNormSq_sub_le_two_mul (s.Dv x) e
            simp only [correctorGrad]
            linarith)
          (inv_nonneg.mpr (cubeVolume_nonneg _))
    _ = _ := cubeAverage_const_add_two_mul _ _ hDv

theorem cubeAverage_correctorGrad_nonneg (e : Vec d) (N : ℕ) :
    0 ≤ cubeAverage (originCube d (N : ℤ)) (fun x => vecNormSq (s.correctorGrad e x)) :=
  cubeAverage_nonneg_of_nonneg _ fun _ => vecNormSq_nonneg _

/-- The pairings of the corrector gradient against smooth cutoffs of the triadic subcubes of
depth at most `m` of the origin cube of side `3ᴺ` are bounded with amplitude `δ`. -/
def PairingBound (e : Vec d) (δ cμ : ℝ) (N m : ℕ) : Prop :=
  ∀ j ≤ m, ∀ R ∈ descendantsAtDepth (originCube d (N : ℤ)) j, ∀ η : Vec d → ℝ,
    ContDiff ℝ (⊤ : ℕ∞) η → HasCompactSupport η → tsupport η ⊆ openCubeSet R →
    (∀ x, 0 ≤ η x) → (∀ x, η x ≤ 1) → ∀ M : ℝ, (∀ x, ‖fderiv ℝ η x‖ ≤ M) →
    ∀ i, |∫ x, η x * s.correctorGrad e x i| ≤
      δ * (3 : ℝ) ^ N * Real.sqrt ((3 : ℝ) ^ (N * d)) * (M + cμ * ((3 : ℝ) ^ N)⁻¹) *
        Real.sqrt (cubeVolume R)

end EllipticWholeSpaceSolution

/-- The oscillation bound from smooth-test pairings in normalized form, for the corrector of a
whole-space solution on the origin cube of side `3ᴺ`. -/
theorem exists_normalized_oscillation_bound (d : ℕ) [NeZero d] :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ {K : ℝ} (s : EllipticWholeSpaceSolution d K) (e : Vec d) (N m : ℕ),
      m ≤ N → ∀ τ : ℝ, 0 < τ → τ ≤ 1 / 4 → ∀ δ cμ : ℝ, 0 ≤ δ → 0 ≤ cμ →
      (∀ j ≤ m, ∀ R ∈ descendantsAtDepth (originCube d (N : ℤ)) j, ∀ η : Vec d → ℝ,
          ContDiff ℝ (⊤ : ℕ∞) η → HasCompactSupport η → tsupport η ⊆ openCubeSet R →
          (∀ x, 0 ≤ η x) → (∀ x, η x ≤ 1) → ∀ M : ℝ, (∀ x, ‖fderiv ℝ η x‖ ≤ M) →
          ∀ i, |∫ x, η x * s.correctorGrad e x i| ≤
            δ * (3 : ℝ) ^ N * Real.sqrt ((3 : ℝ) ^ (N * d)) * (M + cμ * ((3 : ℝ) ^ N)⁻¹) *
              Real.sqrt (cubeVolume R)) →
      cubeBesovOscillation (originCube d (N : ℤ)) 2 (s.corrector e) ≤
        C₀ * (3 : ℝ) ^ N *
          (Real.sqrt (cubeAverage (originCube d (N : ℤ))
              (fun x => vecNormSq (s.correctorGrad e x))) *
              (((3 : ℝ) ^ N)⁻¹ + ((3 : ℝ) ^ m)⁻¹ + Real.sqrt τ) +
            (m + 1) * δ * (τ⁻¹ + cμ) * Real.sqrt ((3 : ℝ) ^ (m * d))) := by
  obtain ⟨C, hC, hosc⟩ := exists_cubeBesovOscillation_le_of_pairing d
  refine ⟨C, hC, ?_⟩
  intro K s e N m hmN τ hτ hτ' δ cμ hδ hcμ hpair
  have h := hosc N m hmN τ hτ hτ' (δ * (3 : ℝ) ^ N * Real.sqrt ((3 : ℝ) ^ (N * d)))
    (cμ * ((3 : ℝ) ^ N)⁻¹) (by positivity) (by positivity) (s.cubeH1 e N) hpair
  refine h.trans (le_of_eq ?_)
  have h3N : (0 : ℝ) < (3 : ℝ) ^ N := by positivity
  have h3m : (0 : ℝ) < (3 : ℝ) ^ m := by positivity
  have hsub : (3 : ℝ) ^ (N - m) = (3 : ℝ) ^ N * ((3 : ℝ) ^ m)⁻¹ := by
    rw [pow_sub₀ _ (by norm_num) hmN]
  have hsq : Real.sqrt ((3 : ℝ) ^ (N * d)) =
      Real.sqrt ((3 : ℝ) ^ ((N - m) * d)) * Real.sqrt ((3 : ℝ) ^ (m * d)) := by
    rw [← Real.sqrt_mul (by positivity), ← pow_add, ← add_mul, Nat.sub_add_cancel hmN]
  have hsq0 : 0 < Real.sqrt ((3 : ℝ) ^ ((N - m) * d)) := Real.sqrt_pos.mpr (by positivity)
  rw [hsub, hsq]
  change C * (Real.sqrt (cubeAverage (originCube d (N : ℤ))
      (fun x => vecNormSq (s.correctorGrad e x))) * _ + _) = _
  field_simp

/-- **The energy step.** The corrector energy on the origin cube of side `3ⁿ` is bounded by
`|e|²`, the corrector energy at the scale `3^(n + d + 1)` times the square of the collar and
depth errors, and the pairing amplitude. -/
theorem exists_energy_step (d : ℕ) [NeZero d] :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ {K : ℝ}, 1 ≤ K → ∀ (s : EllipticWholeSpaceSolution d K) (e : Vec d)
      (n m : ℕ), m ≤ n + d + 1 → ∀ τ : ℝ, 0 < τ → τ ≤ 1 / 4 → ∀ δ cμ : ℝ, 0 ≤ δ → 0 ≤ cμ →
      s.PairingBound e δ cμ (n + d + 1) m →
      cubeAverage (originCube d (n : ℤ)) (fun x => vecNormSq (s.correctorGrad e x)) ≤
        (2 + 4096 * K * (3 : ℝ) ^ ((d + 1) * d) * 9 ^ (d + 1)) * vecNormSq e +
          8 * (4096 * K * (3 : ℝ) ^ ((d + 1) * d) / d) * C₀ ^ 2 * 9 ^ (d + 1) *
            ((((3 : ℝ) ^ (n + d + 1))⁻¹ + ((3 : ℝ) ^ m)⁻¹ + Real.sqrt τ) ^ 2 *
                cubeAverage (originCube d ((n + d + 1 : ℕ) : ℤ))
                  (fun x => vecNormSq (s.correctorGrad e x)) +
              ((m + 1) * δ * (τ⁻¹ + cμ) * Real.sqrt ((3 : ℝ) ^ (m * d))) ^ 2) := by
  obtain ⟨C₀, hC₀, hosc⟩ := exists_normalized_oscillation_bound d
  refine ⟨C₀, hC₀, ?_⟩
  intro K hK s e n m hmN τ hτ hτ' δ cμ hδ hcμ hpair
  have hd : (0 : ℝ) < d := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne d))
  set E' := cubeAverage (originCube d ((n + d + 1 : ℕ) : ℤ))
    (fun x => vecNormSq (s.correctorGrad e x)) with hE'
  have hE'0 : 0 ≤ E' := s.cubeAverage_correctorGrad_nonneg e (n + d + 1)
  set ε := ((3 : ℝ) ^ (n + d + 1))⁻¹ + ((3 : ℝ) ^ m)⁻¹ + Real.sqrt τ with hε
  set A := (m + 1) * δ * (τ⁻¹ + cμ) * Real.sqrt ((3 : ℝ) ^ (m * d)) with hA
  have hε0 : 0 ≤ ε := by positivity
  have hA0 : 0 ≤ A := by positivity
  set osc := cubeBesovOscillation (originCube d ((n + d + 1 : ℕ) : ℤ)) 2 (s.corrector e)
    with hosc_def
  have hosc0 : 0 ≤ osc := cubeLpNorm_nonneg _ _ _
  have h4 := hosc s e (n + d + 1) m hmN τ hτ hτ' δ cμ hδ hcμ hpair
  set X := (3 : ℝ) ^ n with hX
  have hX0 : 0 < X := by positivity
  have h3N : (3 : ℝ) ^ (n + d + 1) = X * 3 ^ (d + 1) := by
    rw [hX, show n + d + 1 = n + (d + 1) by ring, pow_add]
  have h32n : (3 : ℝ) ^ (2 * n) = X ^ 2 := by rw [hX, ← pow_mul, mul_comm]
  have h9 : (9 : ℝ) ^ (d + 1) = ((3 : ℝ) ^ (d + 1)) ^ 2 := by
    rw [← pow_mul, show (9 : ℝ) = 3 ^ 2 by norm_num, ← pow_mul, mul_comm]
  have hosc2 : osc ^ 2 ≤ C₀ ^ 2 * (X * 3 ^ (d + 1)) ^ 2 * (2 * (E' * ε ^ 2 + A ^ 2)) := by
    have h4' : osc ≤ C₀ * (X * 3 ^ (d + 1)) * (Real.sqrt E' * ε + A) := by
      rw [← h3N]
      exact h4
    have hsq : (Real.sqrt E' * ε + A) ^ 2 ≤ 2 * (E' * ε ^ 2 + A ^ 2) := by
      have := Real.sq_sqrt hE'0
      nlinarith [sq_nonneg (Real.sqrt E' * ε - A)]
    calc osc ^ 2 ≤ (C₀ * (X * 3 ^ (d + 1)) * (Real.sqrt E' * ε + A)) ^ 2 :=
          pow_le_pow_left₀ hosc0 h4' 2
      _ = C₀ ^ 2 * (X * 3 ^ (d + 1)) ^ 2 * (Real.sqrt E' * ε + A) ^ 2 := by ring
      _ ≤ C₀ ^ 2 * (X * 3 ^ (d + 1)) ^ 2 * (2 * (E' * ε ^ 2 + A ^ 2)) :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
  have h1 := s.cubeAverage_correctorGrad_le e n
  have h2 := s.cubeAverage_Dv_le hK n (cubeAverage (originCube d ((n + d + 1 : ℕ) : ℤ))
    (s.corrector e))
  have h3 := s.cubeAverage_sq_v_sub_le e (n + d + 1)
  rw [← hosc_def] at h3
  rw [h32n] at h2
  rw [h3N] at h3
  set Cc := 4096 * K * (3 : ℝ) ^ ((d + 1) * d) with hCc
  have hCc0 : 0 ≤ Cc := by positivity
  have hfac : 0 ≤ Cc / (d * X ^ 2) := by positivity
  have h23 := h2.trans (mul_le_mul_of_nonneg_left h3 hfac)
  have hfinal : 2 * vecNormSq e + 2 * (Cc / (d * X ^ 2) *
      (vecNormSq e * (d * (X * 3 ^ (d + 1) / 2) ^ 2) * 2 + 2 * osc ^ 2)) =
      (2 + Cc * 9 ^ (d + 1)) * vecNormSq e + 4 * Cc / (d * X ^ 2) * osc ^ 2 := by
    rw [h9]
    field_simp
    ring
  have hosc' : 4 * Cc / (d * X ^ 2) * osc ^ 2 ≤
      8 * (Cc / d) * C₀ ^ 2 * 9 ^ (d + 1) * (ε ^ 2 * E' + A ^ 2) := by
    have hcoef : 0 ≤ 4 * Cc / (d * X ^ 2) := by positivity
    calc 4 * Cc / (d * X ^ 2) * osc ^ 2 ≤
        4 * Cc / (d * X ^ 2) * (C₀ ^ 2 * (X * 3 ^ (d + 1)) ^ 2 * (2 * (E' * ε ^ 2 + A ^ 2))) :=
          mul_le_mul_of_nonneg_left hosc2 hcoef
      _ = 8 * (Cc / d) * C₀ ^ 2 * 9 ^ (d + 1) * (ε ^ 2 * E' + A ^ 2) := by
          rw [h9]
          field_simp
          ring
  calc cubeAverage (originCube d (n : ℤ)) (fun x => vecNormSq (s.correctorGrad e x))
      ≤ 2 * vecNormSq e + 2 * (Cc / (d * X ^ 2) *
          (vecNormSq e * (d * (X * 3 ^ (d + 1) / 2) ^ 2) * 2 + 2 * osc ^ 2)) := by
        linarith [h1, h23]
    _ = (2 + Cc * 9 ^ (d + 1)) * vecNormSq e + 4 * Cc / (d * X ^ 2) * osc ^ 2 := hfinal
    _ ≤ (2 + Cc * 9 ^ (d + 1)) * vecNormSq e +
          8 * (Cc / d) * C₀ ^ 2 * 9 ^ (d + 1) * (ε ^ 2 * E' + A ^ 2) := by linarith

/-- The discounted energies along the scales `3^(n + k (d + 1))` tend to zero under a growth
bound `9ᴺ ρᴺ` on the square averages with `θ ρ^(d+1) ≤ 1/2`. -/
theorem tendsto_discounted_energy [NeZero d] {K : ℝ} (hK : 1 ≤ K)
    (s : EllipticWholeSpaceSolution d K) (e : Vec d) {θ ρ Cg : ℝ} {Ng : ℕ} (hθ0 : 0 ≤ θ)
    (hθ1 : θ < 1) (hρ : 1 ≤ ρ) (hθρ : θ * ρ ^ (d + 1) ≤ 1 / 2)
    (hgrowth : ∀ N, Ng ≤ N →
      cubeAverage (originCube d (N : ℤ)) (fun x => s.v x ^ 2) ≤ Cg * 9 ^ N * ρ ^ N) (n : ℕ) :
    Tendsto (fun k : ℕ => θ ^ k * cubeAverage (originCube d ((n + k * (d + 1) : ℕ) : ℤ))
      (fun x => vecNormSq (s.correctorGrad e x))) atTop (𝓝 0) := by
  have hd : (0 : ℝ) < d := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne d))
  set Cc := 4096 * K * (3 : ℝ) ^ ((d + 1) * d) with hCc
  set W := 2 * (Cc / d) * Cg * 9 ^ (d + 1) * ρ ^ (n + d + 1) with hW
  have hbound : ∀ k : ℕ, Ng ≤ k → θ ^ k * cubeAverage (originCube d ((n + k * (d + 1) : ℕ) : ℤ))
      (fun x => vecNormSq (s.correctorGrad e x)) ≤
      2 * vecNormSq e * θ ^ k + W * (θ * ρ ^ (d + 1)) ^ k := by
    intro k hk
    set N := n + k * (d + 1) with hN
    have hNg : Ng ≤ N + d + 1 := by
      have : k ≤ k * (d + 1) := Nat.le_mul_of_pos_right k (Nat.succ_pos d)
      omega
    have h1 := s.cubeAverage_correctorGrad_le e N
    have h2 := s.cubeAverage_Dv_le hK N 0
    have h3 := hgrowth (N + d + 1) hNg
    simp only [sub_zero] at h2
    have h32 : (3 : ℝ) ^ (2 * N) = 9 ^ N := by
      rw [pow_mul]
      norm_num
    rw [h32] at h2
    have h9 : (9 : ℝ) ^ (N + d + 1) = 9 ^ N * 9 ^ (d + 1) := by
      rw [show N + d + 1 = N + (d + 1) by ring, pow_add]
    have hρN : ρ ^ (N + d + 1) = ρ ^ (n + d + 1) * (ρ ^ (d + 1)) ^ k := by
      rw [← pow_mul, ← pow_add, hN]
      congr 1
      ring
    have h9N : (0 : ℝ) < 9 ^ N := by positivity
    have hDv : cubeAverage (originCube d (N : ℤ)) (fun x => vecNormSq (s.Dv x)) ≤
        (Cc / d) * Cg * 9 ^ (d + 1) * ρ ^ (n + d + 1) * (ρ ^ (d + 1)) ^ k := by
      calc _ ≤ Cc / (d * 9 ^ N) * (Cg * 9 ^ (N + d + 1) * ρ ^ (N + d + 1)) :=
            h2.trans (mul_le_mul_of_nonneg_left h3 (by positivity))
        _ = _ := by
            rw [h9, hρN]
            field_simp
    have hθk : 0 ≤ θ ^ k := pow_nonneg hθ0 k
    calc θ ^ k * cubeAverage (originCube d (N : ℤ)) (fun x => vecNormSq (s.correctorGrad e x))
        ≤ θ ^ k * (2 * vecNormSq e + 2 * ((Cc / d) * Cg * 9 ^ (d + 1) * ρ ^ (n + d + 1) *
            (ρ ^ (d + 1)) ^ k)) := by
          refine mul_le_mul_of_nonneg_left ?_ hθk
          linarith
      _ = 2 * vecNormSq e * θ ^ k + W * (θ * ρ ^ (d + 1)) ^ k := by
          rw [hW, mul_pow]
          ring
  have hlim1 : Tendsto (fun k : ℕ => 2 * vecNormSq e * θ ^ k + W * (θ * ρ ^ (d + 1)) ^ k)
      atTop (𝓝 0) := by
    have h1 := (tendsto_pow_atTop_nhds_zero_of_lt_one hθ0 hθ1).const_mul (2 * vecNormSq e)
    have hθρ0 : 0 ≤ θ * ρ ^ (d + 1) := mul_nonneg hθ0 (by positivity)
    have h2 := (tendsto_pow_atTop_nhds_zero_of_lt_one hθρ0 (by linarith)).const_mul W
    simpa using h1.add h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim1 ?_ ?_
  · exact Filter.Eventually.of_forall fun k =>
      mul_nonneg (pow_nonneg hθ0 k) (s.cubeAverage_correctorGrad_nonneg e _)
  · exact Filter.eventually_atTop.mpr ⟨Ng, hbound⟩

theorem le_add_mul_of_step {Ek Ek' c₁ Γ A ε ε₀ : ℝ} (hΓ : 0 ≤ Γ) (hE' : 0 ≤ Ek')
    (hε0 : 0 ≤ ε) (hε : ε ≤ 3 * ε₀) (h : Ek ≤ c₁ + Γ * (ε ^ 2 * Ek' + A ^ 2)) :
    Ek ≤ (c₁ + Γ * A ^ 2) + Γ * (3 * ε₀) ^ 2 * Ek' := by
  have hsq : ε ^ 2 ≤ (3 * ε₀) ^ 2 := pow_le_pow_left₀ hε0 hε 2
  have h1 : Γ * (ε ^ 2 * Ek') ≤ Γ * ((3 * ε₀) ^ 2 * Ek') :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsq hE') hΓ
  have h2 : Γ * (ε ^ 2 * Ek' + A ^ 2) = Γ * (ε ^ 2 * Ek') + Γ * A ^ 2 := by ring
  have h3 : Γ * ((3 * ε₀) ^ 2 * Ek') = Γ * (3 * ε₀) ^ 2 * Ek' := by ring
  linarith only [h, h1, h2, h3]

/-- The arithmetic choice of the collar and depth parameters in the energy iteration. -/
theorem exists_energy_parameters {Γ : ℝ} (hΓ : 0 ≤ Γ) :
    ∃ (m : ℕ) (ε₀ : ℝ), 0 < ε₀ ∧ ((3 : ℝ) ^ m)⁻¹ ≤ ε₀ ∧ ε₀ ^ 2 ≤ 1 / 4 ∧
      Γ * (3 * ε₀) ^ 2 ≤ 1 / 4 := by
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (6 * (Γ + 1)) (by norm_num : (1 : ℝ) < 3)
  refine ⟨m, 1 / (6 * (Γ + 1)), by positivity, ?_, ?_, ?_⟩
  · rw [one_div]
    exact inv_anti₀ (by positivity) hm.le
  · have h : 1 / (6 * (Γ + 1)) ≤ 1 / 6 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    have h0 : 0 ≤ 1 / (6 * (Γ + 1)) := by positivity
    nlinarith
  · rw [show Γ * (3 * (1 / (6 * (Γ + 1)))) ^ 2 = Γ / (4 * (Γ + 1) ^ 2) by
      field_simp
      ring]
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith

theorem sq_amplitude_le {m d : ℕ} {δ τ cμ : ℝ} (hτ : 0 < τ) (hcμ : 0 ≤ cμ) :
    ((m + 1) * δ * (τ⁻¹ + cμ) * Real.sqrt ((3 : ℝ) ^ (m * d))) ^ 2 ≤
      (m + 1 : ℝ) ^ 2 * (τ⁻¹ + 1) ^ 2 * (3 : ℝ) ^ (m * d) * ((1 + cμ) ^ 2 * δ ^ 2) := by
  have hτi : 0 ≤ τ⁻¹ := inv_nonneg.mpr hτ.le
  have hfac : τ⁻¹ + cμ ≤ (τ⁻¹ + 1) * (1 + cμ) := by nlinarith
  have hs : Real.sqrt ((3 : ℝ) ^ (m * d)) ^ 2 = (3 : ℝ) ^ (m * d) :=
    Real.sq_sqrt (by positivity)
  have hfac2 : (τ⁻¹ + cμ) ^ 2 ≤ ((τ⁻¹ + 1) * (1 + cμ)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hfac 2
  calc ((m + 1) * δ * (τ⁻¹ + cμ) * Real.sqrt ((3 : ℝ) ^ (m * d))) ^ 2 =
        (m + 1 : ℝ) ^ 2 * δ ^ 2 * (τ⁻¹ + cμ) ^ 2 * (3 : ℝ) ^ (m * d) := by
        rw [mul_pow, mul_pow, mul_pow, hs]
    _ ≤ (m + 1 : ℝ) ^ 2 * δ ^ 2 * ((τ⁻¹ + 1) * (1 + cμ)) ^ 2 * (3 : ℝ) ^ (m * d) := by
        gcongr
    _ = _ := by ring

/-- **Energy bound by iteration over scales.** For a whole-space solution whose corrector
gradient has pairing amplitude at most `δ` at all scales from `3^N₀` on, and whose square
averages grow at most like `9ᴺ ρᴺ` with `ρ^(d+1) ≤ 2`, the corrector energy is bounded by a
constant times `|e|² + (1 + cμ)² δ²` at all scales from `3^(max N₀ n₁)` on. -/
theorem exists_energy_bound (d : ℕ) [NeZero d] (K : ℝ) (hK : 1 ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ n₁ : ℕ, ∀ (s : EllipticWholeSpaceSolution d K) (e : Vec d) (δ cμ : ℝ),
      0 ≤ δ → 0 ≤ cμ → ∀ N₀ : ℕ, (∀ N, N₀ ≤ N → ∀ m ≤ N, s.PairingBound e δ cμ N m) →
      ∀ (ρ Cg : ℝ) (Ng : ℕ), 1 ≤ ρ → ρ ^ (d + 1) ≤ 2 → 0 ≤ Cg →
      (∀ N, Ng ≤ N →
        cubeAverage (originCube d (N : ℤ)) (fun x => s.v x ^ 2) ≤ Cg * 9 ^ N * ρ ^ N) →
      ∀ n, max N₀ n₁ ≤ n →
        cubeAverage (originCube d (n : ℤ)) (fun x => vecNormSq (s.correctorGrad e x)) ≤
          C * (vecNormSq e + (1 + cμ) ^ 2 * δ ^ 2) := by
  obtain ⟨C₀, hC₀, hstep⟩ := exists_energy_step d
  obtain ⟨Cc, hCcdef⟩ : ∃ Cc : ℝ, Cc = 4096 * K * (3 : ℝ) ^ ((d + 1) * d) := ⟨_, rfl⟩
  have hCc0 : 0 ≤ Cc := by rw [hCcdef]; positivity
  obtain ⟨Γ, hΓdef⟩ : ∃ Γ : ℝ, Γ = 8 * (Cc / d) * C₀ ^ 2 * 9 ^ (d + 1) := ⟨_, rfl⟩
  have hΓ0 : 0 ≤ Γ := by rw [hΓdef]; positivity
  obtain ⟨m, ε₀, hε₀0, hm, hτ', hθle⟩ := exists_energy_parameters hΓ0
  obtain ⟨τ, hτdef⟩ : ∃ τ : ℝ, τ = ε₀ ^ 2 := ⟨_, rfl⟩
  have hτ0 : 0 < τ := by rw [hτdef]; positivity
  have hsqτ : Real.sqrt τ = ε₀ := by rw [hτdef, Real.sqrt_sq hε₀0.le]
  obtain ⟨θ, hθdef⟩ : ∃ θ : ℝ, θ = Γ * (3 * ε₀) ^ 2 := ⟨_, rfl⟩
  have hθ0 : 0 ≤ θ := by rw [hθdef]; positivity
  rw [← hθdef] at hθle
  obtain ⟨A₀, hA₀def⟩ : ∃ A₀ : ℝ, A₀ = (m + 1 : ℝ) ^ 2 * (τ⁻¹ + 1) ^ 2 * (3 : ℝ) ^ (m * d) :=
    ⟨_, rfl⟩
  have hA₀0 : 0 ≤ A₀ := by rw [hA₀def]; positivity
  refine ⟨4 / 3 * (2 + Cc * 9 ^ (d + 1) + Γ * A₀),
    mul_nonneg (by norm_num) (add_nonneg (add_nonneg (by norm_num)
      (mul_nonneg hCc0 (by positivity))) (mul_nonneg hΓ0 hA₀0)), m, ?_⟩
  intro s e δ cμ hδ hcμ N₀ hpair ρ Cg Ng hρ hρ2 hCg hgrowth n hn
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = (m + 1) * δ * (τ⁻¹ + cμ) * Real.sqrt ((3 : ℝ) ^ (m * d)) :=
    ⟨_, rfl⟩
  have he0 := vecNormSq_nonneg e
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ, B = (2 + Cc * 9 ^ (d + 1)) * vecNormSq e + Γ * A ^ 2 := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := by
    rw [hBdef]
    exact add_nonneg (mul_nonneg (add_nonneg (by norm_num) (mul_nonneg hCc0 (by positivity)))
      he0) (mul_nonneg hΓ0 (sq_nonneg A))
  have hstep' : ∀ k, max N₀ m ≤ k →
      cubeAverage (originCube d (k : ℤ)) (fun x => vecNormSq (s.correctorGrad e x)) ≤
        B + θ * cubeAverage (originCube d ((k + (d + 1) : ℕ) : ℤ))
          (fun x => vecNormSq (s.correctorGrad e x)) := by
    intro k hk
    have hmk : m ≤ k + d + 1 := by omega
    have h := hstep hK s e k m hmk τ hτ0 (by rw [hτdef]; exact hτ') δ cμ hδ hcμ
      (hpair (k + d + 1) (by omega) m hmk)
    rw [← hCcdef, ← hΓdef, ← hAdef] at h
    have hε : ((3 : ℝ) ^ (k + d + 1))⁻¹ + ((3 : ℝ) ^ m)⁻¹ + Real.sqrt τ ≤ 3 * ε₀ := by
      have h1 : ((3 : ℝ) ^ (k + d + 1))⁻¹ ≤ ((3 : ℝ) ^ m)⁻¹ :=
        inv_anti₀ (by positivity) (pow_le_pow_right₀ (by norm_num) hmk)
      rw [hsqτ]
      linarith
    have h' := le_add_mul_of_step hΓ0 (s.cubeAverage_correctorGrad_nonneg e (k + d + 1))
      (by positivity) hε h
    rw [← hθdef, ← hBdef] at h'
    exact h'
  have hθρ : θ * ρ ^ (d + 1) ≤ 1 / 2 := by
    have : 0 ≤ ρ ^ (d + 1) := by positivity
    nlinarith
  have hlim : ∀ k, Tendsto (fun j : ℕ => θ ^ j *
      cubeAverage (originCube d ((k + j * (d + 1) : ℕ) : ℤ))
        (fun x => vecNormSq (s.correctorGrad e x))) atTop (𝓝 0) :=
    fun k => tendsto_discounted_energy hK s e hθ0 (by linarith) hρ hθρ hgrowth k
  have hiter := le_div_one_sub_of_iterate (E := fun k =>
      cubeAverage (originCube d (k : ℤ)) (fun x => vecNormSq (s.correctorGrad e x)))
    hθ0 (by linarith) hB0 hstep' hlim n (by simpa using hn)
  have hdiv : B / (1 - θ) ≤ 4 / 3 * B := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have hAsq : A ^ 2 ≤ A₀ * ((1 + cμ) ^ 2 * δ ^ 2) := by
    rw [hAdef, hA₀def]
    exact sq_amplitude_le hτ0 hcμ
  have hfin : 4 / 3 * B ≤ 4 / 3 * (2 + Cc * 9 ^ (d + 1) + Γ * A₀) *
      (vecNormSq e + (1 + cμ) ^ 2 * δ ^ 2) := by
    have hq : 0 ≤ (1 + cμ) ^ 2 * δ ^ 2 := by positivity
    have h1 : Γ * A ^ 2 ≤ Γ * (A₀ * ((1 + cμ) ^ 2 * δ ^ 2)) :=
      mul_le_mul_of_nonneg_left hAsq hΓ0
    have h2 : 0 ≤ (2 + Cc * 9 ^ (d + 1)) * ((1 + cμ) ^ 2 * δ ^ 2) :=
      mul_nonneg (add_nonneg (by norm_num) (mul_nonneg hCc0 (by positivity))) hq
    have h3 : 0 ≤ Γ * A₀ * vecNormSq e := mul_nonneg (mul_nonneg hΓ0 hA₀0) he0
    have hexp : 4 / 3 * (2 + Cc * 9 ^ (d + 1) + Γ * A₀) * (vecNormSq e + (1 + cμ) ^ 2 * δ ^ 2) =
        4 / 3 * ((2 + Cc * 9 ^ (d + 1)) * vecNormSq e + Γ * (A₀ * ((1 + cμ) ^ 2 * δ ^ 2)) +
          (2 + Cc * 9 ^ (d + 1)) * ((1 + cμ) ^ 2 * δ ^ 2) + Γ * A₀ * vecNormSq e) := by ring
    rw [hexp, hBdef]
    linarith only [h1, h2, h3]
  exact hiter.trans (hdiv.trans hfin)

theorem amplitude_factor_le {m d q L : ℕ} {γ : ℝ} (hγ : 1 ≤ γ) (hmq : q * m ≤ L)
    (hq : (3 : ℝ) ^ (6 + d) ≤ γ ^ (2 * q)) :
    (m + 1 : ℝ) * 9 ^ m * Real.sqrt ((3 : ℝ) ^ (m * d)) ≤ γ ^ L := by
  have hm1 : (m + 1 : ℝ) ≤ 3 ^ m := by
    have h := one_add_le_pow_of_two_add_nonneg (show (0 : ℝ) ≤ 2 + 2 by norm_num) m
    norm_num at h
    nlinarith
  have hsq : ((m + 1 : ℝ) * 9 ^ m * Real.sqrt ((3 : ℝ) ^ (m * d))) ^ 2 ≤ (γ ^ L) ^ 2 := by
    have h1 : ((m + 1 : ℝ) * 9 ^ m * Real.sqrt ((3 : ℝ) ^ (m * d))) ^ 2 =
        (m + 1 : ℝ) ^ 2 * 81 ^ m * (3 : ℝ) ^ (m * d) := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), ← pow_mul,
        show (9 : ℝ) ^ (m * 2) = 81 ^ m by rw [mul_comm, pow_mul]; norm_num]
    have h2 : (m + 1 : ℝ) ^ 2 ≤ 9 ^ m := by
      calc (m + 1 : ℝ) ^ 2 ≤ (3 ^ m) ^ 2 := pow_le_pow_left₀ (by positivity) hm1 2
        _ = 9 ^ m := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    have h3 : (9 : ℝ) ^ m * 81 ^ m * (3 : ℝ) ^ (m * d) = ((3 : ℝ) ^ (6 + d)) ^ m := by
      rw [show (9 : ℝ) = 3 ^ 2 by norm_num, show (81 : ℝ) = 3 ^ 4 by norm_num, ← pow_mul,
        ← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
      congr 1
      ring
    have h4 : ((3 : ℝ) ^ (6 + d)) ^ m ≤ (γ ^ (2 * q)) ^ m :=
      pow_le_pow_left₀ (by positivity) hq m
    have h5 : (γ ^ (2 * q)) ^ m ≤ (γ ^ L) ^ 2 := by
      rw [← pow_mul, ← pow_mul]
      exact pow_le_pow_right₀ hγ (by nlinarith)
    calc ((m + 1 : ℝ) * 9 ^ m * Real.sqrt ((3 : ℝ) ^ (m * d))) ^ 2
        = (m + 1 : ℝ) ^ 2 * 81 ^ m * (3 : ℝ) ^ (m * d) := h1
      _ ≤ 9 ^ m * 81 ^ m * (3 : ℝ) ^ (m * d) := by gcongr
      _ = ((3 : ℝ) ^ (6 + d)) ^ m := h3
      _ ≤ (γ ^ L) ^ 2 := h4.trans h5
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp hsq

/-- **Oscillation decay.** If the corrector energy is bounded at the scale `3ᴺ` with
`N = n₀ + L` and the pairing amplitude there decays like `γ^(-2L)`, the oscillation of the
corrector on the origin cube of side `3ᴺ`, divided by `3ᴺ`, is bounded by `3^(-N)`,
`3^(-L/q)` and `γ^(-L)` when `3^(6+d) ≤ γ^(2q)`. -/
theorem exists_oscillation_decay (d : ℕ) [NeZero d] :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ {K : ℝ} (s : EllipticWholeSpaceSolution d K) (e : Vec d)
      (cμ Ē D γ : ℝ) (q n₀ L : ℕ), 0 ≤ cμ → 0 ≤ Ē → 0 ≤ D → 1 ≤ γ → 1 ≤ q →
      (3 : ℝ) ^ (6 + d) ≤ γ ^ (2 * q) →
      (∀ m ≤ n₀ + L, s.PairingBound e (D * (γ ^ L) ⁻¹ ^ 2) cμ (n₀ + L) m) →
      cubeAverage (originCube d ((n₀ + L : ℕ) : ℤ))
        (fun x => vecNormSq (s.correctorGrad e x)) ≤ Ē →
      cubeBesovOscillation (originCube d ((n₀ + L : ℕ) : ℤ)) 2 (s.corrector e) ≤
        C₀ * (3 : ℝ) ^ (n₀ + L) * (Real.sqrt Ē * (((3 : ℝ) ^ (n₀ + L))⁻¹ +
          5 / 4 * ((3 : ℝ) ^ (L / q))⁻¹) + 16 * (1 + cμ) * D * (γ ^ L)⁻¹) := by
  obtain ⟨C₀, hC₀, hosc⟩ := exists_normalized_oscillation_bound d
  refine ⟨C₀, hC₀, ?_⟩
  intro K s e cμ Ē D γ q n₀ L hcμ hĒ hD hγ hq1 hq hpair hE
  set m := L / q with hm
  have hmL : m ≤ n₀ + L := (Nat.div_le_self L q).trans (Nat.le_add_left L n₀)
  have hqm : q * m ≤ L := Nat.mul_div_le L q
  set τ := ((3 : ℝ) ^ m)⁻¹ ^ 2 / 16 with hτ
  have h3m : (0 : ℝ) < (3 : ℝ) ^ m := by positivity
  have hτ0 : 0 < τ := by positivity
  have hinv1 : ((3 : ℝ) ^ m)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  have hτ' : τ ≤ 1 / 4 := by
    rw [hτ]
    have : ((3 : ℝ) ^ m)⁻¹ ^ 2 ≤ 1 := pow_le_one₀ (by positivity) hinv1
    linarith
  have hsqτ : Real.sqrt τ = ((3 : ℝ) ^ m)⁻¹ / 4 := by
    rw [hτ, show ((3 : ℝ) ^ m)⁻¹ ^ 2 / 16 = (((3 : ℝ) ^ m)⁻¹ / 4) ^ 2 by ring,
      Real.sqrt_sq (by positivity)]
  have hτinv : τ⁻¹ = 16 * 9 ^ m := by
    have h1 : τ⁻¹ = 16 * ((3 : ℝ) ^ m) ^ 2 := by
      rw [hτ]
      field_simp
    rw [h1, ← pow_mul, mul_comm m 2, pow_mul]
    norm_num
  have hδ0 : 0 ≤ D * (γ ^ L)⁻¹ ^ 2 := by positivity
  have h := hosc s e (n₀ + L) m hmL τ hτ0 hτ' (D * (γ ^ L)⁻¹ ^ 2) cμ hδ0 hcμ (hpair m hmL)
  have hfac := amplitude_factor_le (d := d) hγ hqm hq
  have hγL : (0 : ℝ) < γ ^ L := by positivity
  have hEs : Real.sqrt (cubeAverage (originCube d ((n₀ + L : ℕ) : ℤ))
      (fun x => vecNormSq (s.correctorGrad e x))) ≤ Real.sqrt Ē := Real.sqrt_le_sqrt hE
  have hpos : 0 ≤ C₀ * (3 : ℝ) ^ (n₀ + L) := by positivity
  refine h.trans (mul_le_mul_of_nonneg_left ?_ hpos)
  rw [hsqτ, hτinv]
  have hterm1 : Real.sqrt (cubeAverage (originCube d ((n₀ + L : ℕ) : ℤ))
      (fun x => vecNormSq (s.correctorGrad e x))) *
      (((3 : ℝ) ^ (n₀ + L))⁻¹ + ((3 : ℝ) ^ m)⁻¹ + ((3 : ℝ) ^ m)⁻¹ / 4) ≤
      Real.sqrt Ē * (((3 : ℝ) ^ (n₀ + L))⁻¹ + 5 / 4 * ((3 : ℝ) ^ m)⁻¹) := by
    have heq : ((3 : ℝ) ^ (n₀ + L))⁻¹ + ((3 : ℝ) ^ m)⁻¹ + ((3 : ℝ) ^ m)⁻¹ / 4 =
        ((3 : ℝ) ^ (n₀ + L))⁻¹ + 5 / 4 * ((3 : ℝ) ^ m)⁻¹ := by ring
    rw [heq]
    exact mul_le_mul_of_nonneg_right hEs (by positivity)
  have hterm2 : (m + 1 : ℝ) * (D * (γ ^ L)⁻¹ ^ 2) * (16 * 9 ^ m + cμ) *
      Real.sqrt ((3 : ℝ) ^ (m * d)) ≤ 16 * (1 + cμ) * D * (γ ^ L)⁻¹ := by
    have h9 : (1 : ℝ) ≤ 9 ^ m := one_le_pow₀ (by norm_num)
    have hcm : 16 * 9 ^ m + cμ ≤ 16 * (1 + cμ) * 9 ^ m := by nlinarith
    have hA : 0 ≤ (m + 1 : ℝ) * (D * (γ ^ L)⁻¹ ^ 2) := by positivity
    have hS : 0 ≤ Real.sqrt ((3 : ℝ) ^ (m * d)) := Real.sqrt_nonneg _
    calc (m + 1 : ℝ) * (D * (γ ^ L)⁻¹ ^ 2) * (16 * 9 ^ m + cμ) * Real.sqrt ((3 : ℝ) ^ (m * d))
        ≤ (m + 1 : ℝ) * (D * (γ ^ L)⁻¹ ^ 2) * (16 * (1 + cμ) * 9 ^ m) *
            Real.sqrt ((3 : ℝ) ^ (m * d)) := by gcongr
      _ = 16 * (1 + cμ) * D * (γ ^ L)⁻¹ ^ 2 *
            ((m + 1 : ℝ) * 9 ^ m * Real.sqrt ((3 : ℝ) ^ (m * d))) := by ring
      _ ≤ 16 * (1 + cμ) * D * (γ ^ L)⁻¹ ^ 2 * γ ^ L :=
          mul_le_mul_of_nonneg_left hfac (by positivity)
      _ = 16 * (1 + cμ) * D * (γ ^ L)⁻¹ := by
          field_simp
  linarith [hterm1, hterm2]

end EinsteinFull.Homogenization
