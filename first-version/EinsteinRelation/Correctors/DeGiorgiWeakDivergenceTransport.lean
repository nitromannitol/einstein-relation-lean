import Mathlib
import EinsteinRelation.Calculus.Weak
import DeGiorgi.SobolevSpace.WeakDerivatives

/-! # Weak divergences in the DeGiorgi Euclidean convention

A repository weak divergence on `U ⊆ Vec d` becomes a DeGiorgi weak divergence on
the preimage of `U` under `WithLp.ofLp`. The coordinate transport preserves
Lebesgue measure, and a smooth test on `EuclideanSpace` pulls back to a
repository test whose coordinate derivatives are the `fderiv` components.
-/

open MeasureTheory Filter
open scoped Topology ENNReal

namespace EinsteinRelation.Correctors

/-- Coordinate derivatives of a test pulled back along `WithLp.toLp`. -/
private lemma transport_gradient_toLp {d : ℕ} {ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hψ : Differentiable ℝ ψ) (y : Vec d) (i : Fin d) :
    gradient (fun z : Vec d => ψ (WithLp.toLp 2 z)) y i =
      fderiv ℝ ψ (WithLp.toLp 2 y) (EuclideanSpace.single i 1) := by
  have hf : HasFDerivAt (fun z : Vec d => ψ (WithLp.toLp 2 z))
      ((fderiv ℝ ψ (WithLp.toLp 2 y)).comp
        ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm :
          Vec d →L[ℝ] EuclideanSpace ℝ (Fin d))) y :=
    HasFDerivAt.comp y (hψ (WithLp.toLp 2 y)).hasFDerivAt
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm.hasFDerivAt
  have hd := hf.fderiv
  calc gradient (fun z : Vec d => ψ (WithLp.toLp 2 z)) y i
      = fderiv ℝ (fun z : Vec d => ψ (WithLp.toLp 2 z)) y (unitVector i) := rfl
    _ = fderiv ℝ ψ (WithLp.toLp 2 y) (EuclideanSpace.single i 1) := by
      rw [hd] <;> rfl

/-- The coordinate transport `WithLp.ofLp` identifies integrals over preimages. -/
private lemma transport_setIntegral_ofLp {d : ℕ} (U : Set (Vec d)) (G : Vec d → ℝ) :
    (∫ x in (WithLp.ofLp : EuclideanSpace ℝ (Fin d) → Vec d) ⁻¹' U, G (WithLp.ofLp x)) =
      ∫ x in U, G x := by
  have he : MeasurableEmbedding (WithLp.ofLp : EuclideanSpace ℝ (Fin d) → Vec d) :=
    (MeasurableEquiv.toLp 2 (Vec d)).symm.measurableEmbedding
  exact (PiLp.volume_preserving_ofLp (Fin d)).setIntegral_preimage_emb he G U

/-- A smooth compactly supported test on `EuclideanSpace` pulls back to a repository test. -/
private lemma transport_isSpatialTest_toLp {d : ℕ} {U : Set (Vec d)}
    {ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ)
    (hψs : tsupport ψ ⊆ (WithLp.ofLp : EuclideanSpace ℝ (Fin d) → Vec d) ⁻¹' U) :
    IsSpatialTest U (fun y : Vec d => ψ (WithLp.toLp 2 y)) := by
  have hcont : Continuous (fun y : Vec d => (WithLp.toLp 2 y : EuclideanSpace ℝ (Fin d))) :=
    PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ)
  have hsupp : Function.support (fun y : Vec d => ψ (WithLp.toLp 2 y)) ⊆
      (fun y : Vec d => (WithLp.toLp 2 y : EuclideanSpace ℝ (Fin d))) ⁻¹' tsupport ψ := by
    intro y hy
    have hy' : ψ (WithLp.toLp 2 y) ≠ 0 := hy
    have hmem : (WithLp.toLp 2 y : EuclideanSpace ℝ (Fin d)) ∈ Function.support ψ := hy'
    exact subset_tsupport ψ hmem
  have hclosed : IsClosed
      ((fun y : Vec d => (WithLp.toLp 2 y : EuclideanSpace ℝ (Fin d))) ⁻¹' tsupport ψ) :=
    (isClosed_tsupport ψ).preimage hcont
  have hT : tsupport (fun y : Vec d => ψ (WithLp.toLp 2 y)) ⊆
      (fun y : Vec d => (WithLp.toLp 2 y : EuclideanSpace ℝ (Fin d))) ⁻¹' tsupport ψ :=
    closure_minimal hsupp hclosed
  refine ⟨?_, ?_, ?_⟩
  · exact hψ.comp (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm.contDiff
  · exact hψc.comp_homeomorph (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)).symm
  · intro y hy
    have h1 : (WithLp.toLp 2 y : EuclideanSpace ℝ (Fin d)) ∈ tsupport ψ := hT hy
    exact hψs h1

theorem hasWeakDiv_of_hasWeakDivergence {d : ℕ} [NeZero d] {U : Set (Vec d)}
    {F : Vec d → Vec d} {h : Vec d → ℝ} (hF : HasWeakDivergence U F h) :
    DeGiorgi.HasWeakDiv (fun x : EuclideanSpace ℝ (Fin d) => h (WithLp.ofLp x))
      (fun x => WithLp.toLp 2 (F (WithLp.ofLp x)))
      ((WithLp.ofLp : EuclideanSpace ℝ (Fin d) → Vec d) ⁻¹' U) := by
  intro ψ hψ hψc hψs
  have hψd : Differentiable ℝ ψ := hψ.differentiable (by simp)
  have hφ := transport_isSpatialTest_toLp hψ hψc hψs
  have key := hF.2.2 _ hφ
  have hK : (∫ x in (WithLp.ofLp : EuclideanSpace ℝ (Fin d) → Vec d) ⁻¹' U,
      h (WithLp.ofLp x) * ψ x) = ∫ x in U, h x * ψ (WithLp.toLp 2 x) := by
    have := transport_setIntegral_ofLp U (fun y => h y * ψ (WithLp.toLp 2 y))
    simpa only [WithLp.toLp_ofLp] using this
  have hG : ∀ x : EuclideanSpace ℝ (Fin d),
      (∑ i, (WithLp.toLp 2 (F (WithLp.ofLp x)) : EuclideanSpace ℝ (Fin d)) i *
        (fderiv ℝ ψ x) (EuclideanSpace.single i 1)) =
      dot (F (WithLp.ofLp x))
        (gradient (fun z : Vec d => ψ (WithLp.toLp 2 z)) (WithLp.ofLp x)) := by
    intro x
    simp only [dot, transport_gradient_toLp hψd, WithLp.toLp_ofLp, PiLp.toLp_apply] <;> rfl
  calc (∫ x in (WithLp.ofLp : EuclideanSpace ℝ (Fin d) → Vec d) ⁻¹' U,
          ∑ i, (WithLp.toLp 2 (F (WithLp.ofLp x)) : EuclideanSpace ℝ (Fin d)) i *
            (fderiv ℝ ψ x) (EuclideanSpace.single i 1))
      = ∫ x in (WithLp.ofLp : EuclideanSpace ℝ (Fin d) → Vec d) ⁻¹' U,
          dot (F (WithLp.ofLp x))
            (gradient (fun z : Vec d => ψ (WithLp.toLp 2 z)) (WithLp.ofLp x)) :=
        integral_congr_ae (ae_of_all _ hG)
    _ = ∫ x in U, dot (F x) (gradient (fun z : Vec d => ψ (WithLp.toLp 2 z)) x) :=
        transport_setIntegral_ofLp U
          (fun y => dot (F y) (gradient (fun z : Vec d => ψ (WithLp.toLp 2 z)) y))
    _ = -∫ x in U, h x * ψ (WithLp.toLp 2 x) := key
    _ = -∫ x in (WithLp.ofLp : EuclideanSpace ℝ (Fin d) → Vec d) ⁻¹' U,
          h (WithLp.ofLp x) * ψ x := by
        rw [hK]

end EinsteinRelation.Correctors
