import EinsteinRelation.Calculus.Mollifier
import EinsteinRelation.Correctors.NormalizedSpatialRepresentativeSupport
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

open MeasureTheory

/-! Euclidean transport of the normalized coordinate bump to the spatial kernel carrier. -/

namespace EinsteinRelation.Correctors.NormalizedSpatialRepresentativeSupport

noncomputable def transportedSourceMollifierDensity (d : ℕ) : C(Point d, ℝ) :=
  ⟨fun x => mollifier d x.ofLp,
    (contDiff_mollifier d).continuous.comp
      (PiLp.continuous_ofLp (p := 2) (β := fun _ : Fin d => ℝ))⟩

theorem contDiff_transportedSourceMollifierDensity (d : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (transportedSourceMollifierDensity d) := by
  change ContDiff ℝ (⊤ : ℕ∞) (fun x : Point d => mollifier d x.ofLp)
  exact (contDiff_mollifier d).comp
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).contDiff

theorem nonnegative_transportedSourceMollifierDensity (d : ℕ) (x : Point d) :
    0 ≤ transportedSourceMollifierDensity d x :=
  mollifier_nonneg d x.ofLp

theorem hasCompactSupport_transportedSourceMollifierDensity (d : ℕ) :
    HasCompactSupport (transportedSourceMollifierDensity d) := by
  change HasCompactSupport (fun x : Point d => mollifier d x.ofLp)
  exact (hasCompactSupport_mollifier d).comp_homeomorph
    (PiLp.homeomorph 2 (fun _ : Fin d => ℝ))

theorem tsupport_transportedSourceMollifierDensity_eq (d : ℕ) :
    tsupport (transportedSourceMollifierDensity d) =
      (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)) ⁻¹' tsupport (mollifier d) := by
  change tsupport ((mollifier d) ∘ (PiLp.homeomorph 2 (fun _ : Fin d => ℝ))) = _
  exact tsupport_comp_eq_preimage (mollifier d)
    (PiLp.homeomorph 2 (fun _ : Fin d => ℝ))

theorem supportWithinUnitBall_transportedSourceMollifierDensity (d : ℕ) :
    tsupport (transportedSourceMollifierDensity d) ⊆ Metric.ball 0 1 := by
  rw [tsupport_transportedSourceMollifierDensity_eq]
  intro x hx
  have hcoord : euclideanNorm x.ofLp < 1 := tsupport_mollifier_subset d hx
  have hnorm : euclideanNorm x.ofLp = ‖x‖ := by
    rw [EuclideanSpace.norm_eq]
    unfold euclideanNorm euclideanSq dot
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [Real.norm_eq_abs, pow_two]
    exact (abs_mul_abs_self (x i)).symm
  simpa only [Metric.mem_ball, dist_zero_right, hnorm] using hcoord

theorem integral_transportedSourceMollifierDensity (d : ℕ) :
    (∫ x, transportedSourceMollifierDensity d x ∂volume) = 1 := by
  have hpres : MeasurePreserving (fun x : Point d => x.ofLp) volume volume :=
    PiLp.volume_preserving_ofLp (Fin d)
  have hchange :
      (∫ x : Point d, mollifier d x.ofLp ∂volume) =
        ∫ x : Vec d, mollifier d x ∂volume :=
    hpres.integral_comp
      (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)).measurableEmbedding
      (mollifier d)
  change (∫ x : Point d, mollifier d x.ofLp ∂volume) = 1
  rw [hchange]
  exact integral_mollifier d

noncomputable def canonicalSourceMollifier (d : ℕ) : SourceMollifier d where
  density := transportedSourceMollifierDensity d
  smooth := contDiff_transportedSourceMollifierDensity d
  nonnegative := nonnegative_transportedSourceMollifierDensity d
  compactSupport := hasCompactSupport_transportedSourceMollifierDensity d
  supportWithinUnitBall := supportWithinUnitBall_transportedSourceMollifierDensity d
  integral_one := integral_transportedSourceMollifierDensity d

#print axioms canonicalSourceMollifier

end EinsteinRelation.Correctors.NormalizedSpatialRepresentativeSupport
