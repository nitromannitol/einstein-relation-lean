import Mathlib
import EinsteinRelation.Calculus.Weak
import DeGiorgi.SobolevSpace.WeakDerivatives

open MeasureTheory Filter
open scoped Topology ENNReal

/-! # Weak gradients in the De Giorgi convention

A repository weak gradient (`HasWeakGradient`) tests against spatial tests on `Vec d`.
Pulling a De Giorgi test function on `EuclideanSpace ℝ (Fin d)` back along `WithLp.toLp`
gives such a spatial test, and the set integrals on both sides are transported along the
measure-preserving map `WithLp.ofLp`. This yields the De Giorgi weak gradient
(`DeGiorgi.HasWeakGrad`) on the Euclidean preimage of the open set.
-/

namespace EinsteinRelation.Correctors

/-- The coordinate map `WithLp.ofLp` from the Euclidean space to `Vec d` is a measurable
embedding. -/
private lemma euclidean_ofLp_measurableEmbedding {d : ℕ} :
    MeasurableEmbedding (WithLp.ofLp : EuclideanSpace ℝ (Fin d) → Vec d) :=
  (MeasurableEquiv.toLp 2 (Fin d → ℝ)).symm.measurableEmbedding

/-- Set integrals over the preimage of `U` under the measure-preserving `WithLp.ofLp` agree
with the set integral over `U`. -/
private lemma euclidean_setIntegral_comp_ofLp {d : ℕ} (U : Set (Vec d)) (f : Vec d → ℝ) :
    ∫ x in (WithLp.ofLp : EuclideanSpace ℝ (Fin d) → Vec d) ⁻¹' U, f (WithLp.ofLp x) =
      ∫ y in U, f y :=
  (PiLp.volume_preserving_ofLp (Fin d)).setIntegral_preimage_emb
    euclidean_ofLp_measurableEmbedding f U

/-- A smooth compactly supported test on the Euclidean space, supported in the preimage of `U`,
pulls back along `WithLp.toLp` to a spatial test on `Vec d`. -/
private lemma euclidean_isSpatialTest_comp_toLp {d : ℕ} {U : Set (Vec d)}
    {φ : EuclideanSpace ℝ (Fin d) → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ (WithLp.ofLp : EuclideanSpace ℝ (Fin d) → Vec d) ⁻¹' U) :
    IsSpatialTest U (fun y : Vec d => φ (WithLp.toLp 2 y)) := by
  have hT : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : Vec d => (WithLp.toLp 2 y : EuclideanSpace ℝ (Fin d))) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm.contDiff
  have hcd : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec d => φ (WithLp.toLp 2 y)) := hφ.comp hT
  have hcs : HasCompactSupport (fun y : Vec d => φ (WithLp.toLp 2 y)) :=
    hφc.comp_homeomorph (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)).symm
  have hsub : tsupport (fun y : Vec d => φ (WithLp.toLp 2 y)) ⊆ U := by
    intro y hy
    have hy' : y ∈ ⇑(PiLp.homeomorph 2 (fun _ : Fin d => ℝ)).symm ⁻¹' tsupport φ := by
      rw [← tsupport_comp_eq_preimage φ (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)).symm]
      exact hy
    have hy'' : (WithLp.toLp 2 y : EuclideanSpace ℝ (Fin d)) ∈ tsupport φ := hy'
    exact hφs hy''
  unfold IsSpatialTest
  exact ⟨hcd, hcs, hsub⟩

/-- The coordinate derivative of a pulled-back function is the Fréchet derivative of the
original function along the Euclidean coordinate vector. -/
private lemma euclidean_coordinateDerivative_comp_toLp {d : ℕ}
    {φ : EuclideanSpace ℝ (Fin d) → ℝ} (hφ : Differentiable ℝ φ) (i : Fin d) (x : Vec d) :
    coordinateDerivative i (fun y : Vec d => φ (WithLp.toLp 2 y)) x =
      fderiv ℝ φ (WithLp.toLp 2 x) (EuclideanSpace.single i 1) := by
  have hT : HasFDerivAt (fun y : Vec d => (WithLp.toLp 2 y : EuclideanSpace ℝ (Fin d)))
      ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm :
        Vec d →L[ℝ] EuclideanSpace ℝ (Fin d)) x :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm.hasFDerivAt
  have hcomp : HasFDerivAt (fun y : Vec d => φ (WithLp.toLp 2 y))
      ((fderiv ℝ φ (WithLp.toLp 2 x)).comp
        ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm :
          Vec d →L[ℝ] EuclideanSpace ℝ (Fin d))) x :=
    (hφ (WithLp.toLp 2 x)).hasFDerivAt.comp x hT
  have hsingle : ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm :
      Vec d →L[ℝ] EuclideanSpace ℝ (Fin d)) (unitVector i) = EuclideanSpace.single i 1 :=
    EuclideanSpace.toLp_single i 1
  unfold coordinateDerivative
  rw [hcomp.fderiv, ContinuousLinearMap.comp_apply, hsingle]

/-- Repository weak gradients are De Giorgi weak gradients on the Euclidean preimage of the
open set `U`, with the gradient transported by `WithLp.toLp`. -/
theorem hasWeakGrad_of_hasWeakGradient {d : ℕ} [NeZero d] {U : Set (Vec d)}
    {u : Vec d → ℝ} {g : Vec d → Vec d} (h : HasWeakGradient U u g) :
    DeGiorgi.HasWeakGrad
      (fun x : EuclideanSpace ℝ (Fin d) => WithLp.toLp 2 (g (WithLp.ofLp x)))
      (fun x => u (WithLp.ofLp x))
      ((WithLp.ofLp : EuclideanSpace ℝ (Fin d) → Vec d) ⁻¹' U) := by
  intro i ψ hψ hψc hψs
  have hψd : Differentiable ℝ ψ := hψ.differentiable (by simp)
  have key := (h i).2.2 (fun y : Vec d => ψ (WithLp.toLp 2 y))
    (euclidean_isSpatialTest_comp_toLp hψ hψc hψs)
  simp only [euclidean_coordinateDerivative_comp_toLp hψd i] at key
  have hL : ∫ x in (WithLp.ofLp : EuclideanSpace ℝ (Fin d) → Vec d) ⁻¹' U,
      u (WithLp.ofLp x) * fderiv ℝ ψ x (EuclideanSpace.single i 1) =
      ∫ y in U, u y * fderiv ℝ ψ (WithLp.toLp 2 y) (EuclideanSpace.single i 1) :=
    euclidean_setIntegral_comp_ofLp U
      (fun y : Vec d => u y * fderiv ℝ ψ (WithLp.toLp 2 y) (EuclideanSpace.single i 1))
  have hR : ∫ x in (WithLp.ofLp : EuclideanSpace ℝ (Fin d) → Vec d) ⁻¹' U,
      g (WithLp.ofLp x) i * ψ x =
      ∫ y in U, g y i * ψ (WithLp.toLp 2 y) :=
    euclidean_setIntegral_comp_ofLp U (fun y : Vec d => g y i * ψ (WithLp.toLp 2 y))
  show ∫ x in (WithLp.ofLp : EuclideanSpace ℝ (Fin d) → Vec d) ⁻¹' U,
      u (WithLp.ofLp x) * fderiv ℝ ψ x (EuclideanSpace.single i 1) =
    -∫ x in (WithLp.ofLp : EuclideanSpace ℝ (Fin d) → Vec d) ⁻¹' U,
      g (WithLp.ofLp x) i * ψ x
  rw [hL, hR]
  exact key

end EinsteinRelation.Correctors
