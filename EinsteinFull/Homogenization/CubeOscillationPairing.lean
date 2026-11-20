import EinsteinFull.Homogenization.MultiscalePoincareVector
import EinsteinFull.Homogenization.CubeLpSquareAverage
import Homogenization.Sobolev.Foundations.QuantitativeCutoff
import Homogenization.Deterministic.ConstantCoefficientDirichletBesov.Basic

/-!
# Oscillation bounds from smooth-test pairings

If the pairings of a gradient field against smooth cutoffs of the triadic subcubes of an origin
cube are small, then the oscillation of the function on the cube is small, up to a multiple of
the side of the finest cubes used times its energy. This combines the multiscale Poincaré
inequality of Armstrong, Kuusi and Mourrat, *Quantitative Stochastic Homogenization and
Large-Scale Regularity*, Corollary 1.14, with a comparison of sharp and smooth cube averages.
-/

open MeasureTheory
open scoped ENNReal

namespace EinsteinFull.Homogenization

open _root_.Homogenization

variable {d : ℕ}

/-- Bernoulli's inequality in the form used for the volume of a cube collar. -/
theorem one_sub_pow_le_mul_one_sub {ρ : ℝ} (h0 : 0 ≤ ρ) (n : ℕ) :
    1 - ρ ^ n ≤ n * (1 - ρ) := by
  have h := one_add_le_pow_of_two_add_nonneg (show (0 : ℝ) ≤ 2 + -(1 - ρ) by linarith) n
  have h1 : (1 : ℝ) + -(1 - ρ) = ρ := by ring
  have h2 : (n : ℝ) * -(1 - ρ) = -(n * (1 - ρ)) := by ring
  rw [h1, h2] at h
  linarith

theorem scaledClosedCubeSet_eq_pi (R : TriadicCube d) (ρ : ℝ) :
    scaledClosedCubeSet R ρ = Set.univ.pi fun i =>
      Set.Icc (cubeCenter R i - ρ * cubeRadius R) (cubeCenter R i + ρ * cubeRadius R) := by
  ext x
  simp only [scaledClosedCubeSet, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies,
    Set.mem_Icc, abs_sub_le_iff]
  refine forall_congr' fun i => ?_
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

theorem measurableSet_scaledClosedCubeSet (R : TriadicCube d) (ρ : ℝ) :
    MeasurableSet (scaledClosedCubeSet R ρ) := by
  rw [scaledClosedCubeSet_eq_pi]
  exact MeasurableSet.univ_pi fun _ => measurableSet_Icc

theorem volume_scaledClosedCubeSet_toReal (R : TriadicCube d) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    (volume (scaledClosedCubeSet R ρ)).toReal = ρ ^ d * cubeVolume R := by
  have hr : 0 ≤ cubeRadius R := cubeRadius_nonneg R
  have hside (i : Fin d) : cubeCenter R i + ρ * cubeRadius R - (cubeCenter R i - ρ * cubeRadius R) =
      2 * (ρ * cubeRadius R) := by ring
  rw [scaledClosedCubeSet_eq_pi, volume_pi_pi]
  simp only [Real.volume_Icc, hside, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ENNReal.toReal_pow]
  rw [ENNReal.toReal_ofReal (by positivity), cubeVolume_eq_scaleFactor_pow, ← mul_pow]
  congr 1
  simp only [cubeRadius]
  ring

theorem scaledClosedCubeSet_subset_openCubeSet (R : TriadicCube d) {ρ : ℝ} (hρ1 : ρ < 1) :
    scaledClosedCubeSet R ρ ⊆ openCubeSet R := by
  intro x hx i
  have hs : 0 < cubeScaleFactor R := by
    simpa [cubeScaleFactor] using zpow_pos (show (0 : ℝ) < 3 by norm_num) R.scale
  have h := abs_sub_le_iff.mp (hx i)
  simp only [cubeCenter, cubeRadius] at h
  constructor <;> nlinarith

theorem openCubeSet_subset_cubeSet (R : TriadicCube d) : openCubeSet R ⊆ cubeSet R :=
  fun _ hx i => ⟨(hx i).1.le, (hx i).2⟩

/-- The smooth cutoff of the concentric subcube of relative radius `1 - 2τ`, supported in the
subcube of relative radius `1 - τ`. -/
noncomputable def innerCubeCutoff (R : TriadicCube d) (τ : ℝ) : Vec d → ℝ :=
  QuantitativeCubeCutoff.canonicalFun R (1 - 2 * τ) (1 - τ)

section InnerCubeCutoff

variable {τ : ℝ}

theorem innerCubeCutoff_smooth (R : TriadicCube d) (hτ : 0 < τ) (hτ' : τ ≤ 1 / 4) :
    ContDiff ℝ (⊤ : ℕ∞) (innerCubeCutoff R τ) :=
  QuantitativeCubeCutoff.canonicalFun_smooth R (by linarith) (by linarith)

theorem innerCubeCutoff_hasCompactSupport (R : TriadicCube d) (hτ : 0 < τ) (hτ' : τ ≤ 1 / 4) :
    HasCompactSupport (innerCubeCutoff R τ) :=
  QuantitativeCubeCutoff.canonicalFun_hasCompactSupport R (by linarith) (by linarith)

theorem innerCubeCutoff_nonneg (R : TriadicCube d) (τ : ℝ) (x : Vec d) :
    0 ≤ innerCubeCutoff R τ x :=
  QuantitativeCubeCutoff.canonicalFun_nonneg R _ _ x

theorem innerCubeCutoff_le_one (R : TriadicCube d) (τ : ℝ) (x : Vec d) :
    innerCubeCutoff R τ x ≤ 1 :=
  QuantitativeCubeCutoff.canonicalFun_le_one R _ _ x

theorem tsupport_innerCubeCutoff_subset (R : TriadicCube d) (hτ : 0 < τ) (hτ' : τ ≤ 1 / 4) :
    tsupport (innerCubeCutoff R τ) ⊆ openCubeSet R :=
  (QuantitativeCubeCutoff.canonicalFun_tsupport_subset_scaledClosedCubeSet
    (by linarith) (by linarith)).trans
    (scaledClosedCubeSet_subset_openCubeSet R (by linarith))

theorem innerCubeCutoff_eq_zero_of_not_mem (R : TriadicCube d) (hτ : 0 < τ) (hτ' : τ ≤ 1 / 4)
    {x : Vec d} (hx : x ∉ cubeSet R) : innerCubeCutoff R τ x = 0 := by
  by_contra h
  exact hx (openCubeSet_subset_cubeSet R
    (tsupport_innerCubeCutoff_subset R hτ hτ' (subset_tsupport _ h)))

theorem norm_fderiv_innerCubeCutoff_le (R : TriadicCube d) (hτ : 0 < τ) (hτ' : τ ≤ 1 / 4)
    (x : Vec d) :
    ‖fderiv ℝ (innerCubeCutoff R τ) x‖ ≤
      4 * d * smoothTransitionProfile.derivBound / (τ * cubeScaleFactor R) := by
  have h := QuantitativeCubeCutoff.canonicalFun_gradient_bound R
    (show (0 : ℝ) < 1 - 2 * τ by linarith) (show 1 - 2 * τ < 1 - τ by linarith) x
  have hs : 0 < cubeScaleFactor R := by
    simpa [cubeScaleFactor] using zpow_pos (show (0 : ℝ) < 3 by norm_num) R.scale
  have hτ0 : τ ≠ 0 := hτ.ne'
  have hs0 : cubeScaleFactor R ≠ 0 := hs.ne'
  have hden : (1 - τ - (1 - 2 * τ)) * cubeRadius R = τ * cubeScaleFactor R / 2 := by
    simp only [cubeRadius]
    ring
  have hrw : (d : ℝ) * smoothTransitionProfile.derivBound *
      (2 / ((1 - τ - (1 - 2 * τ)) * cubeRadius R)) =
      4 * d * smoothTransitionProfile.derivBound / (τ * cubeScaleFactor R) := by
    rw [hden]
    field_simp
    ring
  rw [hrw] at h
  exact h

/-- The square of `1 - η` has cube average at most `2 d τ`. -/
theorem cubeAverage_sq_one_sub_innerCubeCutoff_le (R : TriadicCube d) (hτ : 0 < τ)
    (hτ' : τ ≤ 1 / 4) :
    cubeAverage R (fun x => (1 - innerCubeCutoff R τ x) ^ 2) ≤ 2 * d * τ := by
  set η := innerCubeCutoff R τ
  set S := scaledClosedCubeSet R (1 - 2 * τ)
  have hS : MeasurableSet S := measurableSet_scaledClosedCubeSet R _
  have hSR : S ⊆ cubeSet R :=
    (scaledClosedCubeSet_subset_openCubeSet R (by linarith)).trans (openCubeSet_subset_cubeSet R)
  have hRfin : volume (cubeSet R) < ⊤ := volume_cubeSet_lt_top R
  have hRmeas : MeasurableSet (cubeSet R) := measurableSet_cubeSet R
  have hηc : Continuous η := (innerCubeCutoff_smooth R hτ hτ').continuous
  have hpt (x : Vec d) : (1 - η x) ^ 2 ≤ 1 - S.indicator (fun _ => (1 : ℝ)) x := by
    have h0 := innerCubeCutoff_nonneg R τ x
    have h1 := innerCubeCutoff_le_one R τ x
    by_cases hx : x ∈ S
    · have hη1 : η x = 1 :=
        QuantitativeCubeCutoff.canonicalFun_eq_one_on_inner (by linarith) (by linarith) hx
      simp [Set.indicator_of_mem hx, hη1]
    · rw [Set.indicator_of_notMem hx]
      nlinarith
  have hint1 : IntegrableOn (fun x => (1 - η x) ^ 2) (cubeSet R) volume :=
    IntegrableOn.of_bound hRfin ((continuous_const.sub hηc).pow 2).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun x => by
        have h0 := innerCubeCutoff_nonneg R τ x
        have h1 := innerCubeCutoff_le_one R τ x
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        nlinarith)
  have hind : IntegrableOn (S.indicator fun _ => (1 : ℝ)) (cubeSet R) volume :=
    ((MeasureTheory.integrable_indicator_iff hS).mpr
      (integrableOn_const (C := (1 : ℝ)) ((measure_mono hSR).trans_lt hRfin).ne)).integrableOn
  have hone : IntegrableOn (fun _ => (1 : ℝ)) (cubeSet R) volume :=
    integrableOn_const (C := (1 : ℝ)) hRfin.ne
  have hint2 : IntegrableOn (fun x => 1 - S.indicator (fun _ => (1 : ℝ)) x) (cubeSet R) volume :=
    Integrable.sub hone hind
  have hle : ∫ x in cubeSet R, (1 - η x) ^ 2 ≤
      ∫ x in cubeSet R, (1 - S.indicator (fun _ => (1 : ℝ)) x) :=
    setIntegral_mono_on hint1 hint2 hRmeas fun x _ => hpt x
  have hval : ∫ x in cubeSet R, (1 - S.indicator (fun _ => (1 : ℝ)) x) =
      cubeVolume R - (1 - 2 * τ) ^ d * cubeVolume R := by
    rw [integral_sub hone hind, setIntegral_const, setIntegral_indicator hS, setIntegral_const,
      Set.inter_eq_right.mpr hSR]
    simp only [smul_eq_mul, mul_one, Measure.real]
    rw [volume_cubeSet_toReal, volume_scaledClosedCubeSet_toReal R (by linarith)]
  have hs : 0 < cubeScaleFactor R := by
    simpa [cubeScaleFactor] using zpow_pos (show (0 : ℝ) < 3 by norm_num) R.scale
  have hvol : 0 < cubeVolume R := by
    rw [cubeVolume_eq_scaleFactor_pow]
    exact pow_pos hs d
  have hbern := one_sub_pow_le_mul_one_sub (show (0 : ℝ) ≤ 1 - 2 * τ by linarith) d
  unfold cubeAverage
  rw [inv_mul_le_iff₀ hvol]
  calc ∫ x in cubeSet R, (1 - η x) ^ 2 ≤ cubeVolume R - (1 - 2 * τ) ^ d * cubeVolume R :=
        hle.trans hval.le
    _ = (1 - (1 - 2 * τ) ^ d) * cubeVolume R := by ring
    _ ≤ (d * (1 - (1 - 2 * τ))) * cubeVolume R := mul_le_mul_of_nonneg_right hbern hvol.le
    _ = cubeVolume R * (2 * d * τ) := by ring

end InnerCubeCutoff

section PerCube

variable {τ : ℝ}

theorem cubeAverage_nonneg_of_nonneg (R : TriadicCube d) {f : Vec d → ℝ} (hf : ∀ x, 0 ≤ f x) :
    0 ≤ cubeAverage R f :=
  mul_nonneg (inv_nonneg.mpr (cubeVolume_nonneg R))
    (setIntegral_nonneg (measurableSet_cubeSet R) fun x _ => hf x)

theorem integral_innerCubeCutoff_mul_eq (R : TriadicCube d) (hτ : 0 < τ) (hτ' : τ ≤ 1 / 4)
    (g : Vec d → ℝ) :
    ∫ x, innerCubeCutoff R τ x * g x = ∫ x in cubeSet R, innerCubeCutoff R τ x * g x := by
  refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_).symm
  rw [innerCubeCutoff_eq_zero_of_not_mem R hτ hτ' hx, zero_mul]

/-- A sharp cube average is the smooth cutoff average up to the collar error. -/
theorem abs_cubeAverage_le_innerCubeCutoff (R : TriadicCube d) (hτ : 0 < τ) (hτ' : τ ≤ 1 / 4)
    {g : Vec d → ℝ} (hg : MemLp g 2 (normalizedCubeMeasure R)) :
    |cubeAverage R g| ≤ (cubeVolume R)⁻¹ * |∫ x, innerCubeCutoff R τ x * g x| +
      Real.sqrt (2 * d * τ) * Real.sqrt (cubeAverage R (fun x => g x ^ 2)) := by
  haveI : IsProbabilityMeasure (normalizedCubeMeasure R) := ⟨normalizedCubeMeasure_apply_univ R⟩
  set η := innerCubeCutoff R τ
  have hηc : Continuous η := (innerCubeCutoff_smooth R hτ hτ').continuous
  have h1η : MemLp (fun x => 1 - η x) 2 (normalizedCubeMeasure R) :=
    MemLp.of_bound (continuous_const.sub hηc).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun x => by
        have h0 := innerCubeCutoff_nonneg R τ x
        have h1 := innerCubeCutoff_le_one R τ x
        rw [Real.norm_eq_abs, abs_le]
        constructor <;> linarith)
  have hholder := abs_cubeAverage_mul_le_mul_cubeLpNorm_of_holderConjugate R 2 2
    (fun x => 1 - η x) g h1η hg
  have hn1 := (integrable_and_cubeLpNorm_sq_eq_cubeAverage_sq R _ h1η).2
  have hng := (integrable_and_cubeLpNorm_sq_eq_cubeAverage_sq R _ hg).2
  have hc1 : cubeLpNorm R 2 (fun x => 1 - η x) ≤ Real.sqrt (2 * d * τ) := by
    rw [← Real.sqrt_sq (cubeLpNorm_nonneg R 2 _), hn1]
    exact Real.sqrt_le_sqrt (cubeAverage_sq_one_sub_innerCubeCutoff_le R hτ hτ')
  have hcg : cubeLpNorm R 2 g = Real.sqrt (cubeAverage R (fun x => g x ^ 2)) := by
    rw [← hng, Real.sqrt_sq (cubeLpNorm_nonneg R 2 _)]
  have hgint : Integrable g (normalizedCubeMeasure R) := hg.integrable one_le_two
  have hprod : Integrable (fun x => (1 - η x) * g x) (normalizedCubeMeasure R) :=
    h1η.integrable_mul hg
  have hηg : Integrable (fun x => η x * g x) (normalizedCubeMeasure R) := by
    refine (hgint.sub hprod).congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.sub_apply]
    ring
  have hcut : ∫ x, η x * g x = ∫ x in cubeSet R, η x * g x :=
    integral_innerCubeCutoff_mul_eq R hτ hτ' g
  have hdecomp : cubeAverage R g = (cubeVolume R)⁻¹ * (∫ x, η x * g x) +
      cubeAverage R (fun x => (1 - η x) * g x) := by
    rw [hcut]
    have h2 : (cubeVolume R)⁻¹ * (∫ x in cubeSet R, η x * g x) =
        cubeAverage R (fun x => η x * g x) := rfl
    rw [h2, cubeAverage_eq_integral_normalizedCubeMeasure,
      cubeAverage_eq_integral_normalizedCubeMeasure,
      cubeAverage_eq_integral_normalizedCubeMeasure, ← integral_add hηg hprod]
    congr 1
    funext x
    ring
  rw [hdecomp]
  have hinv : 0 ≤ (cubeVolume R)⁻¹ := inv_nonneg.mpr (cubeVolume_nonneg R)
  calc |(cubeVolume R)⁻¹ * (∫ x, η x * g x) + cubeAverage R (fun x => (1 - η x) * g x)|
      ≤ |(cubeVolume R)⁻¹ * (∫ x, η x * g x)| +
          |cubeAverage R (fun x => (1 - η x) * g x)| := abs_add_le _ _
    _ ≤ (cubeVolume R)⁻¹ * |∫ x, η x * g x| +
          Real.sqrt (2 * d * τ) * Real.sqrt (cubeAverage R (fun x => g x ^ 2)) := by
        refine add_le_add (by rw [abs_mul, abs_of_nonneg hinv]) ?_
        calc _ ≤ _ := hholder
          _ ≤ _ := by
            rw [hcg]
            exact mul_le_mul_of_nonneg_right hc1 (Real.sqrt_nonneg _)

/-- The cube average of the squared Euclidean norm is the sum of the coordinate averages. -/
theorem cubeAverage_vecNormSq_eq_sum (R : TriadicCube d) {G : Vec d → Vec d}
    (hG : ∀ i, MemLp (fun x => G x i) 2 (normalizedCubeMeasure R)) :
    cubeAverage R (fun x => vecNormSq (G x)) = ∑ i, cubeAverage R (fun x => G x i ^ 2) := by
  simp only [cubeAverage_eq_integral_normalizedCubeMeasure]
  rw [← integral_finset_sum _ fun i _ => (hG i).integrable_sq]
  congr 1
  funext x
  simp [vecNormSq, vecDot, sq]

/-- Jensen's inequality for the vector of coordinate averages. -/
theorem vecNormSq_cubeAverage_le (R : TriadicCube d) {G : Vec d → Vec d}
    (hG : ∀ i, MemLp (fun x => G x i) 2 (normalizedCubeMeasure R)) :
    vecNormSq (fun i => cubeAverage R (fun x => G x i)) ≤
      cubeAverage R (fun x => vecNormSq (G x)) := by
  rw [cubeAverage_vecNormSq_eq_sum R hG]
  simp only [vecNormSq, vecDot]
  refine Finset.sum_le_sum fun i _ => ?_
  have h := sq_cubeAverage_le_cubeAverage_sq_of_memLp R (fun x => G x i) (hG i)
  nlinarith [h]

/-- The vector of coordinate averages is controlled by the cutoff pairings and the energy. -/
theorem vecNormSq_cubeAverage_le_innerCubeCutoff (R : TriadicCube d) (hτ : 0 < τ)
    (hτ' : τ ≤ 1 / 4) {G : Vec d → Vec d}
    (hG : ∀ i, MemLp (fun x => G x i) 2 (normalizedCubeMeasure R)) {A : ℝ}
    (hA : ∀ i, |∫ x, innerCubeCutoff R τ x * G x i| ≤ A) :
    vecNormSq (fun i => cubeAverage R (fun x => G x i)) ≤
      2 * d * ((cubeVolume R)⁻¹ * A) ^ 2 +
        4 * d * τ * cubeAverage R (fun x => vecNormSq (G x)) := by
  have hinv : 0 ≤ (cubeVolume R)⁻¹ := inv_nonneg.mpr (cubeVolume_nonneg R)
  have hcoord (i : Fin d) : cubeAverage R (fun x => G x i) * cubeAverage R (fun x => G x i) ≤
      2 * ((cubeVolume R)⁻¹ * A) ^ 2 + 4 * d * τ * cubeAverage R (fun x => G x i ^ 2) := by
    have h := abs_cubeAverage_le_innerCubeCutoff R hτ hτ' (hG i)
    have hA' : (cubeVolume R)⁻¹ * |∫ x, innerCubeCutoff R τ x * G x i| ≤ (cubeVolume R)⁻¹ * A :=
      mul_le_mul_of_nonneg_left (hA i) hinv
    have hav : 0 ≤ cubeAverage R (fun x => G x i ^ 2) :=
      cubeAverage_nonneg_of_nonneg R fun x => sq_nonneg _
    have hsq : (Real.sqrt (2 * d * τ) * Real.sqrt (cubeAverage R (fun x => G x i ^ 2))) ^ 2 =
        2 * d * τ * cubeAverage R (fun x => G x i ^ 2) := by
      rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt hav]
    have hb : 0 ≤ Real.sqrt (2 * d * τ) * Real.sqrt (cubeAverage R (fun x => G x i ^ 2)) :=
      by positivity
    have ha : 0 ≤ (cubeVolume R)⁻¹ * |∫ x, innerCubeCutoff R τ x * G x i| :=
      mul_nonneg hinv (abs_nonneg _)
    have habs := abs_le.mp (h.trans (add_le_add hA' le_rfl))
    nlinarith [habs.1, habs.2, hsq, sq_nonneg ((cubeVolume R)⁻¹ * A -
      Real.sqrt (2 * d * τ) * Real.sqrt (cubeAverage R (fun x => G x i ^ 2)))]
  rw [cubeAverage_vecNormSq_eq_sum R hG]
  simp only [vecNormSq, vecDot]
  calc ∑ i, cubeAverage R (fun x => G x i) * cubeAverage R (fun x => G x i)
      ≤ ∑ i : Fin d, (2 * ((cubeVolume R)⁻¹ * A) ^ 2 +
          4 * d * τ * cubeAverage R (fun x => G x i ^ 2)) := Finset.sum_le_sum fun i _ => hcoord i
    _ = 2 * d * ((cubeVolume R)⁻¹ * A) ^ 2 +
          4 * d * τ * ∑ i, cubeAverage R (fun x => G x i ^ 2) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul, Finset.mul_sum]
        ring

end PerCube

section GeometricSums

theorem sum_range_three_pow_sub_eq (n : ℕ) :
    ∑ j ∈ Finset.range (n + 1), (3 : ℝ) ^ (n - j) = ((3 : ℝ) ^ (n + 1) - 1) / 2 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have h : ∑ j ∈ Finset.range (n + 1), (3 : ℝ) ^ (n + 1 - j) =
        3 * ∑ j ∈ Finset.range (n + 1), (3 : ℝ) ^ (n - j) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      rw [show n + 1 - j = n - j + 1 by omega, pow_succ]
      ring
    rw [h, ih, Nat.sub_self, pow_zero]
    ring

theorem sum_range_ite_lt_three_pow_sub_le (m : ℕ) :
    ∀ n : ℕ, ∑ j ∈ Finset.range (n + 1), (if m < j then (3 : ℝ) ^ (n - j) else 0) ≤
      ((3 : ℝ) ^ (n - m) - 1) / 2 := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have h : ∑ j ∈ Finset.range (n + 1), (if m < j then (3 : ℝ) ^ (n + 1 - j) else 0) =
        3 * ∑ j ∈ Finset.range (n + 1), (if m < j then (3 : ℝ) ^ (n - j) else 0) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      split_ifs
      · rw [show n + 1 - j = n - j + 1 by omega, pow_succ]
        ring
      · ring
    rw [h]
    by_cases hmn : m ≤ n
    · rw [if_pos (by omega), Nat.sub_self, pow_zero, show n + 1 - m = n - m + 1 by omega,
        pow_succ]
      linarith
    · rw [if_neg (by omega), show n + 1 - m = 0 by omega, show n - m = 0 by omega] at *
      norm_num at ih ⊢
      linarith

theorem sum_range_ite_le_const (m n : ℕ) (hmn : m ≤ n) (T : ℝ) :
    ∑ j ∈ Finset.range (n + 1), (if j ≤ m then T else 0) = (m + 1) * T := by
  rw [show n + 1 = (m + 1) + (n - m) by omega, Finset.sum_range_add]
  have h1 : ∑ j ∈ Finset.range (m + 1), (if j ≤ m then T else 0) = (m + 1) * T := by
    rw [Finset.sum_congr rfl fun j hj => if_pos (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)),
      Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast
    ring
  have h2 : ∑ k ∈ Finset.range (n - m), (if m + 1 + k ≤ m then T else 0) = 0 :=
    Finset.sum_eq_zero fun k _ => if_neg (by omega)
  rw [h1, h2, add_zero]

end GeometricSums

section Main

theorem cubeScaleFactor_of_mem_descendantsAtDepth_originCube {n j : ℕ} (hj : j ≤ n)
    {R : TriadicCube d} (hR : R ∈ descendantsAtDepth (originCube d (n : ℤ)) j) :
    cubeScaleFactor R = (3 : ℝ) ^ (n - j) := by
  have h := scale_eq_sub_of_mem_descendantsAtDepth hR
  unfold cubeScaleFactor
  rw [h, show (originCube d (n : ℤ)).scale = (n : ℤ) from rfl, ← Nat.cast_sub hj, zpow_natCast]

theorem descendantsAverage_add_const (Q : TriadicCube d) (j : ℕ) (c : ℝ)
    (F : TriadicCube d → ℝ) :
    descendantsAverage Q j (fun R => c + F R) = c + descendantsAverage Q j F := by
  change ((descendantsAtDepth Q j).card : ℝ)⁻¹ * ∑ R ∈ descendantsAtDepth Q j, (c + F R) =
    c + ((descendantsAtDepth Q j).card : ℝ)⁻¹ * ∑ R ∈ descendantsAtDepth Q j, F R
  rw [Finset.sum_add_distrib, mul_add]
  congr 1
  exact descendantsAverage_const Q j c

theorem integrableOn_cubeSet_of_integrable_normalized (Q : TriadicCube d) {f : Vec d → ℝ}
    (hf : Integrable f (normalizedCubeMeasure Q)) : IntegrableOn f (cubeSet Q) volume := by
  have hv : 0 < cubeVolume Q := cubeVolume_pos Q
  have h1 : ENNReal.ofReal (cubeVolume Q)⁻¹ ≠ 0 := by
    rw [ENNReal.ofReal_ne_zero_iff]
    positivity
  exact (integrable_smul_measure h1 ENNReal.ofReal_ne_top).mp hf

theorem sqrt_add_le_add_sqrt {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb, Real.sqrt_nonneg a, Real.sqrt_nonneg b,
    mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)]

/-- The energy of an `H¹` function on an origin cube is the average of its energies on the
descendants of any depth. -/
theorem descendantsAverage_cubeAverage_vecNormSq_grad {n : ℕ}
    (u : H1Function (openCubeSet (originCube d (n : ℤ)))) (j : ℕ) :
    descendantsAverage (originCube d (n : ℤ)) j
        (fun R => cubeAverage R (fun x => vecNormSq (u.grad x))) =
      cubeAverage (originCube d (n : ℤ)) (fun x => vecNormSq (u.grad x)) := by
  have hEint : IntegrableOn (fun x => vecNormSq (u.grad x))
      (cubeSet (originCube d (n : ℤ))) volume := by
    refine integrableOn_cubeSet_of_integrable_normalized _ ?_
    have h := integrable_finset_sum (μ := normalizedCubeMeasure (originCube d (n : ℤ)))
      Finset.univ fun i _ => (u.grad_coord_memL2_normalizedCubeMeasure i).integrable_sq
    refine h.congr (Filter.Eventually.of_forall fun x => ?_)
    simp [vecNormSq, vecDot, sq]
  exact (cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn _ j _ hEint).symm

/-- At every depth, the root mean square of the block averages is at most the energy. -/
theorem descendantsAverage_vecNormSq_cubeAverage_le_energy {n : ℕ}
    (u : H1Function (openCubeSet (originCube d (n : ℤ)))) (j : ℕ) :
    descendantsAverage (originCube d (n : ℤ)) j
        (fun R => vecNormSq (fun i => cubeAverage R (fun x => u.grad x i))) ≤
      cubeAverage (originCube d (n : ℤ)) (fun x => vecNormSq (u.grad x)) := by
  calc _ ≤ descendantsAverage (originCube d (n : ℤ)) j
        (fun R => cubeAverage R (fun x => vecNormSq (u.grad x))) :=
        descendantsAverage_le_descendantsAverage _ j fun R hR =>
          vecNormSq_cubeAverage_le R fun i =>
            u.grad_coord_memL2_normalizedCubeMeasure_descendant hR i
    _ = _ := descendantsAverage_cubeAverage_vecNormSq_grad u j

/-- At a depth `j ≤ m`, the root mean square of the block averages is controlled by the
pairings of the gradient against the smooth cutoffs of the blocks and the collar error. -/
theorem three_pow_mul_sqrt_descendantsAverage_le_of_pairing {n m j : ℕ} (hjn : j ≤ n)
    (hjm : j ≤ m) (hmn : m ≤ n) {τ : ℝ} (hτ : 0 < τ) (hτ' : τ ≤ 1 / 4) {N μ : ℝ} (hN : 0 ≤ N)
    (hμ : 0 ≤ μ) (u : H1Function (openCubeSet (originCube d (n : ℤ))))
    (hpair : ∀ R ∈ descendantsAtDepth (originCube d (n : ℤ)) j, ∀ η : Vec d → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) η → HasCompactSupport η → tsupport η ⊆ openCubeSet R →
      (∀ x, 0 ≤ η x) → (∀ x, η x ≤ 1) → ∀ M : ℝ, (∀ x, ‖fderiv ℝ η x‖ ≤ M) →
      ∀ i, |∫ x, η x * u.grad x i| ≤ N * (M + μ) * Real.sqrt (cubeVolume R)) :
    (3 : ℝ) ^ (n - j) * Real.sqrt (descendantsAverage (originCube d (n : ℤ)) j
        (fun R => vecNormSq (fun i => cubeAverage R (fun x => u.grad x i)))) ≤
      (3 : ℝ) ^ (n - j) * (2 * Real.sqrt (d * τ) *
          Real.sqrt (cubeAverage (originCube d (n : ℤ)) (fun x => vecNormSq (u.grad x)))) +
        Real.sqrt (2 * d) * N * (4 * d * smoothTransitionProfile.derivBound * τ⁻¹ +
          (3 : ℝ) ^ n * μ) / Real.sqrt ((3 : ℝ) ^ ((n - m) * d)) := by
  set D := smoothTransitionProfile.derivBound with hDdef
  have hD : 0 ≤ D := smoothTransitionProfile.derivBound_nonneg
  set E := cubeAverage (originCube d (n : ℤ)) (fun x => vecNormSq (u.grad x)) with hE
  have hE0 : 0 ≤ E := cubeAverage_nonneg_of_nonneg _ fun x => vecNormSq_nonneg _
  set s := (3 : ℝ) ^ (n - j) with hs_def
  have hs : 0 < s := by positivity
  set Mj := 4 * d * D / (τ * s) with hMj
  have hMj0 : 0 ≤ Mj := by positivity
  have hsd : 0 < Real.sqrt (s ^ d) := Real.sqrt_pos.mpr (by positivity)
  set w := N * (Mj + μ) / Real.sqrt (s ^ d) with hw
  have hw0 : 0 ≤ w := by positivity
  have hcube : ∀ R ∈ descendantsAtDepth (originCube d (n : ℤ)) j,
      vecNormSq (fun i => cubeAverage R (fun x => u.grad x i)) ≤
        2 * d * w ^ 2 + 4 * d * τ * cubeAverage R (fun x => vecNormSq (u.grad x)) := by
    intro R hR
    have hsR : cubeScaleFactor R = s :=
      cubeScaleFactor_of_mem_descendantsAtDepth_originCube hjn hR
    have hvR : cubeVolume R = s ^ d := by rw [cubeVolume_eq_scaleFactor_pow, hsR]
    have hA : ∀ i, |∫ x, innerCubeCutoff R τ x * u.grad x i| ≤
        N * (Mj + μ) * Real.sqrt (s ^ d) := by
      intro i
      have h := hpair R hR (innerCubeCutoff R τ) (innerCubeCutoff_smooth R hτ hτ')
        (innerCubeCutoff_hasCompactSupport R hτ hτ') (tsupport_innerCubeCutoff_subset R hτ hτ')
        (innerCubeCutoff_nonneg R τ) (innerCubeCutoff_le_one R τ) Mj
        (fun x => by
          have h' := norm_fderiv_innerCubeCutoff_le R hτ hτ' x
          rwa [hsR] at h') i
      rwa [hvR] at h
    have h := vecNormSq_cubeAverage_le_innerCubeCutoff R hτ hτ'
      (fun i => u.grad_coord_memL2_normalizedCubeMeasure_descendant hR i) hA
    have hwid : (cubeVolume R)⁻¹ * (N * (Mj + μ) * Real.sqrt (s ^ d)) = w := by
      rw [hvR, hw, ← Real.sq_sqrt (show (0 : ℝ) ≤ s ^ d by positivity)]
      rw [Real.sqrt_sq hsd.le]
      field_simp
    rwa [hwid] at h
  have havg : descendantsAverage (originCube d (n : ℤ)) j
      (fun R => vecNormSq (fun i => cubeAverage R (fun x => u.grad x i))) ≤
      2 * d * w ^ 2 + 4 * d * τ * E := by
    calc _ ≤ descendantsAverage (originCube d (n : ℤ)) j (fun R => 2 * d * w ^ 2 +
          4 * d * τ * cubeAverage R (fun x => vecNormSq (u.grad x))) :=
          descendantsAverage_le_descendantsAverage _ j hcube
      _ = 2 * d * w ^ 2 + 4 * d * τ * E := by
          rw [descendantsAverage_add_const, descendantsAverage_mul_left,
            descendantsAverage_cubeAverage_vecNormSq_grad]
  have hsqrt : Real.sqrt (descendantsAverage (originCube d (n : ℤ)) j
      (fun R => vecNormSq (fun i => cubeAverage R (fun x => u.grad x i)))) ≤
      Real.sqrt (2 * d) * w + 2 * Real.sqrt (d * τ) * Real.sqrt E := by
    calc _ ≤ Real.sqrt (2 * d * w ^ 2 + 4 * d * τ * E) := Real.sqrt_le_sqrt havg
      _ ≤ Real.sqrt (2 * d * w ^ 2) + Real.sqrt (4 * d * τ * E) :=
          sqrt_add_le_add_sqrt (by positivity) (by positivity)
      _ = Real.sqrt (2 * d) * w + 2 * Real.sqrt (d * τ) * Real.sqrt E := by
          rw [Real.sqrt_mul (show (0 : ℝ) ≤ 2 * d by positivity) (w ^ 2), Real.sqrt_sq hw0,
            show (4 : ℝ) * d * τ * E = 2 ^ 2 * ((d * τ) * E) by ring,
            Real.sqrt_mul (show (0 : ℝ) ≤ 2 ^ 2 by positivity) ((d * τ) * E),
            Real.sqrt_sq (show (0 : ℝ) ≤ 2 by norm_num),
            Real.sqrt_mul (show (0 : ℝ) ≤ d * τ by positivity) E]
          ring
  have hsw : s * (Real.sqrt (2 * d) * w) ≤ Real.sqrt (2 * d) * N *
      (4 * d * D * τ⁻¹ + (3 : ℝ) ^ n * μ) / Real.sqrt ((3 : ℝ) ^ ((n - m) * d)) := by
    have hnum : s * (Mj + μ) ≤ 4 * d * D * τ⁻¹ + (3 : ℝ) ^ n * μ := by
      have h1 : s * Mj = 4 * d * D * τ⁻¹ := by
        rw [hMj]
        field_simp
      have h2 : s ≤ (3 : ℝ) ^ n := pow_le_pow_right₀ (by norm_num) (Nat.sub_le n j)
      have h3 : s * μ ≤ (3 : ℝ) ^ n * μ := mul_le_mul_of_nonneg_right h2 hμ
      rw [mul_add, h1]
      linarith
    have hden : Real.sqrt ((3 : ℝ) ^ ((n - m) * d)) ≤ Real.sqrt (s ^ d) := by
      refine Real.sqrt_le_sqrt ?_
      rw [hs_def, ← pow_mul]
      exact pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_right d (by omega))
    have hden0 : 0 < Real.sqrt ((3 : ℝ) ^ ((n - m) * d)) := Real.sqrt_pos.mpr (by positivity)
    calc s * (Real.sqrt (2 * d) * w) =
        Real.sqrt (2 * d) * N * (s * (Mj + μ)) / Real.sqrt (s ^ d) := by
          rw [hw]
          ring
      _ ≤ Real.sqrt (2 * d) * N * (4 * d * D * τ⁻¹ + (3 : ℝ) ^ n * μ) /
          Real.sqrt (s ^ d) := by gcongr
      _ ≤ _ := by gcongr
  calc s * Real.sqrt (descendantsAverage (originCube d (n : ℤ)) j
        (fun R => vecNormSq (fun i => cubeAverage R (fun x => u.grad x i))))
      ≤ s * (Real.sqrt (2 * d) * w + 2 * Real.sqrt (d * τ) * Real.sqrt E) :=
        mul_le_mul_of_nonneg_left hsqrt hs.le
    _ = s * (2 * Real.sqrt (d * τ) * Real.sqrt E) + s * (Real.sqrt (2 * d) * w) := by ring
    _ ≤ _ := by linarith

/-- The arithmetic assembling the depth bounds. -/
theorem oscillation_assembly_le {C₀ sE A S T : ℝ} {n m : ℕ} {τ N μ D : ℝ} (hC₀ : 0 ≤ C₀)
    (hsE : 0 ≤ sE) (hτ : 0 < τ) (hN : 0 ≤ N) (hμ : 0 ≤ μ) (hD : 0 ≤ D)
    (hS : S * (2 * Real.sqrt (d * τ) * sE) ≤ 3 * Real.sqrt d * ((3 : ℝ) ^ n * Real.sqrt τ) * sE)
    (hdeep : A ≤ (3 : ℝ) ^ (n - m) * sE)
    (hT : T = Real.sqrt (2 * d) * N * (4 * d * D * τ⁻¹ + (3 : ℝ) ^ n * μ) /
      Real.sqrt ((3 : ℝ) ^ ((n - m) * d))) :
    C₀ * (sE + (S * (2 * Real.sqrt (d * τ) * sE) + (m + 1) * T + A)) ≤
      C₀ * (1 + 3 * Real.sqrt d + Real.sqrt (2 * d) * (4 * d * D + 1)) *
        (sE * (1 + (3 : ℝ) ^ (n - m) + (3 : ℝ) ^ n * Real.sqrt τ) +
          (m + 1) * N * (τ⁻¹ + (3 : ℝ) ^ n * μ) / Real.sqrt ((3 : ℝ) ^ ((n - m) * d))) := by
  set P := 1 + (3 : ℝ) ^ (n - m) + (3 : ℝ) ^ n * Real.sqrt τ with hPdef
  set Z := (m + 1 : ℝ) * N * (τ⁻¹ + (3 : ℝ) ^ n * μ) /
    Real.sqrt ((3 : ℝ) ^ ((n - m) * d)) with hZdef
  set c := Real.sqrt (2 * d) * (4 * d * D + 1) with hc
  have hc0 : 0 ≤ c := by positivity
  have hden0 : 0 < Real.sqrt ((3 : ℝ) ^ ((n - m) * d)) := Real.sqrt_pos.mpr (by positivity)
  have hZ0 : 0 ≤ Z := by positivity
  have hP3 : 0 ≤ (3 : ℝ) ^ n * Real.sqrt τ := by positivity
  have h3nm : 0 ≤ (3 : ℝ) ^ (n - m) := by positivity
  have hexpP : sE * P = sE + (3 : ℝ) ^ (n - m) * sE + ((3 : ℝ) ^ n * Real.sqrt τ) * sE := by
    rw [hPdef]
    ring
  have hSP : 0 ≤ sE * P := by
    rw [hexpP]
    have := mul_nonneg h3nm hsE
    have := mul_nonneg hP3 hsE
    linarith
  have hTle : (m + 1 : ℝ) * T ≤ c * Z := by
    have hτi : 0 ≤ τ⁻¹ := inv_nonneg.mpr hτ.le
    have hk : 4 * d * D * τ⁻¹ + (3 : ℝ) ^ n * μ ≤ (4 * d * D + 1) * (τ⁻¹ + (3 : ℝ) ^ n * μ) := by
      have h1 : 0 ≤ (3 : ℝ) ^ n * μ := by positivity
      have h2 : 0 ≤ 4 * d * D * ((3 : ℝ) ^ n * μ) := mul_nonneg (by positivity) h1
      have h3 : (4 * d * D + 1) * (τ⁻¹ + (3 : ℝ) ^ n * μ) =
          4 * d * D * τ⁻¹ + (3 : ℝ) ^ n * μ + (4 * d * D * ((3 : ℝ) ^ n * μ) + τ⁻¹) := by ring
      linarith
    have hpos : 0 ≤ (m + 1 : ℝ) * Real.sqrt (2 * d) * N := by positivity
    have hmul := mul_le_mul_of_nonneg_left hk hpos
    rw [hT, hZdef, hc]
    calc (m + 1 : ℝ) * (Real.sqrt (2 * d) * N * (4 * d * D * τ⁻¹ + (3 : ℝ) ^ n * μ) /
          Real.sqrt ((3 : ℝ) ^ ((n - m) * d))) =
        ((m + 1 : ℝ) * Real.sqrt (2 * d) * N) * (4 * d * D * τ⁻¹ + (3 : ℝ) ^ n * μ) /
          Real.sqrt ((3 : ℝ) ^ ((n - m) * d)) := by ring
      _ ≤ ((m + 1 : ℝ) * Real.sqrt (2 * d) * N) * ((4 * d * D + 1) * (τ⁻¹ + (3 : ℝ) ^ n * μ)) /
          Real.sqrt ((3 : ℝ) ^ ((n - m) * d)) := by gcongr
      _ = _ := by ring
  have hA2 : S * (2 * Real.sqrt (d * τ) * sE) ≤ 3 * Real.sqrt d * (sE * P) := by
    have h1 : ((3 : ℝ) ^ n * Real.sqrt τ) * sE ≤ sE * P := by
      rw [hexpP]
      have := mul_nonneg h3nm hsE
      linarith
    have h2 : 0 ≤ 3 * Real.sqrt d := by positivity
    calc S * (2 * Real.sqrt (d * τ) * sE) ≤ 3 * Real.sqrt d * ((3 : ℝ) ^ n * Real.sqrt τ) * sE :=
          hS
      _ = 3 * Real.sqrt d * (((3 : ℝ) ^ n * Real.sqrt τ) * sE) := by ring
      _ ≤ 3 * Real.sqrt d * (sE * P) := mul_le_mul_of_nonneg_left h1 h2
  have hA4 : sE + A ≤ sE * P := by
    rw [hexpP]
    have := mul_nonneg hP3 hsE
    linarith
  have hexp : (1 + 3 * Real.sqrt d + c) * (sE * P + Z) = sE * P + 3 * Real.sqrt d * (sE * P) +
      c * Z + (c * (sE * P) + (1 + 3 * Real.sqrt d) * Z) := by ring
  have hrest : 0 ≤ c * (sE * P) + (1 + 3 * Real.sqrt d) * Z :=
    add_nonneg (mul_nonneg hc0 hSP) (mul_nonneg (by positivity) hZ0)
  have hin : sE + (S * (2 * Real.sqrt (d * τ) * sE) + (m + 1) * T + A) ≤
      (1 + 3 * Real.sqrt d + c) * (sE * P + Z) := by
    rw [hexp]
    linarith
  calc C₀ * (sE + (S * (2 * Real.sqrt (d * τ) * sE) + (m + 1) * T + A)) ≤
      C₀ * ((1 + 3 * Real.sqrt d + c) * (sE * P + Z)) := mul_le_mul_of_nonneg_left hin hC₀
    _ = _ := by ring

/-- **Oscillation from smooth-test pairings.** The oscillation of an `H¹` function on the
origin cube of side `3ⁿ` is bounded by its energy times the side of the cubes of depth `m`,
plus the error of the smooth cutoffs at relative collar width `τ`, plus the pairings of its
gradient against the smooth cutoffs of the subcubes of depth at most `m`. -/
theorem exists_cubeBesovOscillation_le_of_pairing (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n m : ℕ), m ≤ n → ∀ τ : ℝ, 0 < τ → τ ≤ 1 / 4 →
      ∀ N μ : ℝ, 0 ≤ N → 0 ≤ μ →
      ∀ u : H1Function (openCubeSet (originCube d (n : ℤ))),
        (∀ j ≤ m, ∀ R ∈ descendantsAtDepth (originCube d (n : ℤ)) j, ∀ η : Vec d → ℝ,
          ContDiff ℝ (⊤ : ℕ∞) η → HasCompactSupport η → tsupport η ⊆ openCubeSet R →
          (∀ x, 0 ≤ η x) → (∀ x, η x ≤ 1) → ∀ M : ℝ, (∀ x, ‖fderiv ℝ η x‖ ≤ M) →
          ∀ i, |∫ x, η x * u.grad x i| ≤ N * (M + μ) * Real.sqrt (cubeVolume R)) →
        cubeBesovOscillation (originCube d (n : ℤ)) 2 (fun x => u x) ≤
          C * (Real.sqrt (cubeAverage (originCube d (n : ℤ)) (fun x => vecNormSq (u.grad x))) *
              (1 + (3 : ℝ) ^ (n - m) + (3 : ℝ) ^ n * Real.sqrt τ) +
            (m + 1) * N * (τ⁻¹ + (3 : ℝ) ^ n * μ) / Real.sqrt ((3 : ℝ) ^ ((n - m) * d))) := by
  obtain ⟨C₀, hC₀, hMP⟩ := exists_originCube_multiscalePoincare d
  have hD : 0 ≤ smoothTransitionProfile.derivBound := smoothTransitionProfile.derivBound_nonneg
  refine ⟨C₀ * (1 + 3 * Real.sqrt d + Real.sqrt (2 * d) *
    (4 * d * smoothTransitionProfile.derivBound + 1)), by positivity, ?_⟩
  intro n m hmn τ hτ hτ' N μ hN hμ u hpair
  obtain ⟨-, hmem, hosc⟩ := hMP n u
  set E := cubeAverage (originCube d (n : ℤ)) (fun x => vecNormSq (u.grad x)) with hE
  have hE0 : 0 ≤ E := cubeAverage_nonneg_of_nonneg _ fun x => vecNormSq_nonneg _
  set sE := Real.sqrt E with hsE
  have hsE0 : 0 ≤ sE := Real.sqrt_nonneg _
  have hL : cubeLpNorm (originCube d (n : ℤ)) 2 (fun x => euclideanNorm (u.grad x)) = sE := by
    have h := (integrable_and_cubeLpNorm_sq_eq_cubeAverage_sq _ _ hmem).2
    have h2 : (fun x => euclideanNorm (u.grad x) ^ 2) = fun x => vecNormSq (u.grad x) := by
      funext x
      unfold euclideanNorm
      rw [Real.sq_sqrt (vecNormSq_nonneg _)]
    rw [h2] at h
    rw [hsE, hE, ← h, Real.sqrt_sq (cubeLpNorm_nonneg _ _ _)]
  set T : ℝ := Real.sqrt (2 * d) * N * (4 * d * smoothTransitionProfile.derivBound * τ⁻¹ +
    (3 : ℝ) ^ n * μ) / Real.sqrt ((3 : ℝ) ^ ((n - m) * d)) with hT
  have hdepth : ∀ j ∈ Finset.range (n + 1),
      (3 : ℝ) ^ (n - j) * Real.sqrt (descendantsAverage (originCube d (n : ℤ)) j
        (fun R => vecNormSq (fun i => cubeAverage R (fun x => u.grad x i)))) ≤
      (3 : ℝ) ^ (n - j) * (2 * Real.sqrt (d * τ) * sE) + (if j ≤ m then T else 0) +
        (if m < j then (3 : ℝ) ^ (n - j) * sE else 0) := by
    intro j hj
    have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    by_cases hjm : j ≤ m
    · rw [if_pos hjm, if_neg (by omega), add_zero]
      exact three_pow_mul_sqrt_descendantsAverage_le_of_pairing hjn hjm hmn hτ hτ' hN hμ u
        (hpair j hjm)
    · rw [if_neg hjm, if_pos (by omega), add_zero]
      have h1 : (3 : ℝ) ^ (n - j) * Real.sqrt (descendantsAverage (originCube d (n : ℤ)) j
          (fun R => vecNormSq (fun i => cubeAverage R (fun x => u.grad x i)))) ≤
          (3 : ℝ) ^ (n - j) * sE :=
        mul_le_mul_of_nonneg_left
          (Real.sqrt_le_sqrt (descendantsAverage_vecNormSq_cubeAverage_le_energy u j))
          (by positivity)
      have h2 : 0 ≤ (3 : ℝ) ^ (n - j) * (2 * Real.sqrt (d * τ) * sE) := by positivity
      linarith
  have hsum := Finset.sum_le_sum hdepth
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_mul,
    sum_range_ite_le_const m n hmn T] at hsum
  have hdeep : ∑ j ∈ Finset.range (n + 1), (if m < j then (3 : ℝ) ^ (n - j) * sE else 0) ≤
      (3 : ℝ) ^ (n - m) * sE := by
    have h := sum_range_ite_lt_three_pow_sub_le m n
    have hfun : ∑ j ∈ Finset.range (n + 1), (if m < j then (3 : ℝ) ^ (n - j) * sE else 0) =
        (∑ j ∈ Finset.range (n + 1), (if m < j then (3 : ℝ) ^ (n - j) else 0)) * sE := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      split_ifs <;> ring
    rw [hfun]
    have h3 : 0 ≤ (3 : ℝ) ^ (n - m) := by positivity
    have h4 : (∑ j ∈ Finset.range (n + 1), (if m < j then (3 : ℝ) ^ (n - j) else 0)) ≤
        (3 : ℝ) ^ (n - m) := by linarith
    exact mul_le_mul_of_nonneg_right h4 hsE0
  have hgeo' : (∑ j ∈ Finset.range (n + 1), (3 : ℝ) ^ (n - j)) * (2 * Real.sqrt (d * τ) * sE) ≤
      3 * Real.sqrt d * ((3 : ℝ) ^ n * Real.sqrt τ) * sE := by
    rw [sum_range_three_pow_sub_eq n, Real.sqrt_mul (Nat.cast_nonneg d), pow_succ]
    have h0 : 0 ≤ Real.sqrt d * Real.sqrt τ * sE := by positivity
    have h1 : 0 ≤ (3 : ℝ) ^ n := by positivity
    have hexp : ((3 : ℝ) ^ n * 3 - 1) / 2 * (2 * (Real.sqrt d * Real.sqrt τ) * sE) =
        3 * Real.sqrt d * ((3 : ℝ) ^ n * Real.sqrt τ) * sE -
          Real.sqrt d * Real.sqrt τ * sE := by ring
    rw [hexp]
    linarith
  rw [hL] at hosc
  have hosc' := hosc.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl hsum) hC₀)
  exact hosc'.trans (oscillation_assembly_le hC₀ hsE0 hτ hN hμ hD hgeo' hdeep hT)

end Main

end EinsteinFull.Homogenization
