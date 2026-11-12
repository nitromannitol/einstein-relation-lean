import EinsteinRelation.Correctors.PairedPDEPointwise
import EinsteinRelation.Correctors.ParabolicUnitScaleGradient
import EinsteinRelation.Correctors.SpatialWeakLocalization

/-! # Combining the large-scale and fixed-scale harmonic gradient estimates

Source: `paper/main.tex:860–869`. The AKM estimate compares the actual
harmonic gradient at its random radius to the large-ball energy. The
Euclidean volume comparison and GT's unit-ball gradient estimate then give
the pointwise bound, retaining the samplewise regularity requirements.
-/

open MeasureTheory

namespace EinsteinRelation.Correctors
open External.AKM External.GilbargTrudinger Environment.AKMTestIntegralSupport

/-- An AKM harmonic field is a GT weak solution on every smaller origin
ball. The vector L² norm is derived from its Euclidean energy and genuine
weak gradient. Source: `paper/main.tex:860–868`. -/
theorem isHarmonic_weakSolution_on_ball {d : ℕ} {K R r : ℝ}
    {A : Coefficient d K} {u : Vec d → ℝ} {G : Vec d → Vec d}
    (hu : IsHarmonic A R u G) (hrR : r ≤ R) :
    WeakSolution (ball 0 r) A u G := by
  have hsub : originBall d r ⊆ originBall d R := fun _ hx => lt_of_lt_of_le hx hrR
  have hgrad := hasWeakGradient_mono hsub hu.2.2.1
  have hnorm := hu.2.1.mono_measure (Measure.restrict_mono_set volume hsub)
  have hm : AEStronglyMeasurable G (volume.restrict (originBall d r)) :=
    (aemeasurable_pi_lambda _ fun j =>
      (hgrad j).2.1.aestronglyMeasurable.aemeasurable).aestronglyMeasurable
  have hG : MemLp G 2 (volume.restrict (originBall d r)) := by
    apply hnorm.of_le hm
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ euclideanNorm (G x) from Real.sqrt_nonneg _)]
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun j => ?_
    rw [Real.norm_eq_abs]
    apply Real.abs_le_sqrt
    change (G x j)^2 ≤ ∑ k : Fin d, G x k * G x k
    rw [sq]
    exact Finset.single_le_sum (fun k _ => mul_self_nonneg _) (Finset.mem_univ j)
  rw [originBall_eq_gt_ball] at hgrad hG
  exact ⟨by simpa only [originBall_eq_gt_ball] using
    hu.1.mono_measure (Measure.restrict_mono_set volume hsub), hG, hgrad,
    by simpa only [originBall_eq_gt_ball] using hasWeakDivergence_mono hsub hu.2.2.2⟩

/-- One source random radius gives the actual pointwise harmonic gradient
bound whenever the radius is good. The coefficient and gradient regularity
used by GT are explicit, not hidden in the AKM solution predicate.
Source: `paper/main.tex:860–869`. -/
theorem ellipticLargeScale_harmonic_gradient_origin
    (hAKM : EllipticLargeScale)
    (h817 : LocalBoundednessEstimate) (h832 : InteriorGradientEstimate)
    (hP : BallPoincareEstimate)
    (d : ℕ) (hd : 2 ≤ d) (K s : ℝ) (hK : 1 < K) (hs : 0 < s) (hsd : s < d)
    {lam Λ H α : ℝ} (hlam : 0 < lam) (hΛ : 0 < Λ)
    (hH : 0 < H) (hα : 0 < α) (hα1 : α < 1) :
    ∃ C₀ C : ℝ, 0 < C₀ ∧ 0 < C ∧
      ∀ P : Measure (Coefficient d K), IsAdmissibleLaw P →
        ∃ X : Coefficient d K → ℝ, Measurable X ∧ (∀ A, 1 ≤ X A) ∧
          StretchedExponentialBound P s C₀ X ∧
          ∀ᵐ A ∂P, ∀ R : ℝ, X A ≤ R →
            ∀ (u : Vec d → ℝ) (G : Vec d → Vec d), IsHarmonic A R u G →
              EllipticBound (ball 0 1) A lam Λ →
              (∀ i j, HolderBound (ball 0 1) α (fun x => A x i j) H) →
              C1Alpha (ball 0 1) α u G →
              euclideanNorm (G 0) ≤ C * (X A)^((d : ℝ)/2) *
                vectorRms volume (originBall d R) G := by
  obtain ⟨C₀, hC₀, hlarge⟩ := hAKM d hd K s hK hs hsd
  obtain ⟨C₁, hC₁, hsmall⟩ := paired_harmonic_gradient_origin_of_gt
    h817 h832 hP hd hlam hΛ hH hα hα1
  refine ⟨C₀, C₁*C₀, hC₀, mul_pos hC₁ hC₀, ?_⟩
  intro P hP
  obtain ⟨X, hXm, hX, htail, hbound⟩ := hlarge P hP
  refine ⟨X, hXm, hX, htail, ?_⟩
  filter_upwards [hbound] with A hA
  intro R hR u G hu hell hholder hreg
  have h1R : 1 ≤ R := (hX A).trans hR
  have hpoint := hsmall A u G hell hholder
    (fun r _ hr => isHarmonic_weakSolution_on_ball hu (hr.trans h1R)) hreg
  rw [← originBall_eq_gt_ball] at hpoint
  have hunit := vectorRms_unitBall_le (hX A) G
    (hu.2.1.mono_measure (Measure.restrict_mono_set volume
      (fun _ hx => lt_of_lt_of_le hx hR)))
  have hlarge := (hA R hR u G hu (X A) le_rfl hR).2.2
  calc
    _ ≤ C₁ * vectorRms volume (originBall d 1) G := hpoint
    _ ≤ C₁ * ((X A)^((d : ℝ)/2) * vectorRms volume (originBall d (X A)) G) :=
      mul_le_mul_of_nonneg_left hunit hC₁.le
    _ ≤ C₁ * ((X A)^((d : ℝ)/2) *
        (C₀ * vectorRms volume (originBall d R) G)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hlarge (Real.rpow_nonneg ((hX A).trans' zero_le_one) _)) hC₁.le
    _ = _ := by ring

end EinsteinRelation.Correctors
