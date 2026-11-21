import EinsteinFull.Regeneration.BoxZeroBoundary

/-!
# Collars outside the transverse support

A function which vanishes near a pair of box faces has zero normalized mass
on sufficiently narrow collars of those faces.
-/

open Filter MeasureTheory Set PDE
open scoped Topology

namespace EinsteinFull.Regeneration

/-- Vanishing in a fixed face neighborhood implies vanishing normalized collar mass. -/
theorem tendsto_box_face_collar_of_vanishes_near_faces
    {d : ℕ} (a b : PDE.Vec d) (i : Fin d)
    (hQ : MeasurableSet (PDE.axisBox a b)) (f : PDE.Vec d → ℝ)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hzero : ∀ x ∈ PDE.axisBox a b, x ∈ boxFaceCollars a b i ρ → f x = 0)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun k => (∫ x in boxFaceCollars a b i (ε k), f x ^ 2
      ∂(PDE.volumeOn (PDE.axisBox a b))) / (ε k) ^ 2) atTop (𝓝 0) := by
  have hevent : ∀ᶠ k in atTop,
      (∫ x in boxFaceCollars a b i (ε k), f x ^ 2
        ∂(PDE.volumeOn (PDE.axisBox a b))) / (ε k) ^ 2 = 0 := by
    filter_upwards [hε.eventually_lt_const hρ] with k hk
    have hz : (∫ x in boxFaceCollars a b i (ε k), f x ^ 2
        ∂(PDE.volumeOn (PDE.axisBox a b))) = 0 := by
      apply integral_eq_zero_of_ae
      have hQae : ∀ᵐ x ∂((PDE.volumeOn (PDE.axisBox a b)).restrict
          (boxFaceCollars a b i (ε k))), x ∈ PDE.axisBox a b :=
        ae_restrict_of_ae (ae_restrict_mem hQ)
      filter_upwards [hQae, ae_restrict_mem (measurableSet_boxFaceCollars a b i (ε k))]
        with x hx hcollar
      have hlarge : x ∈ boxFaceCollars a b i ρ := by
        rcases hcollar with hl | hr
        · left; linarith
        · right; linarith
      rw [hzero x hx hlarge]
      norm_num
    rw [hz, zero_div]
  have heq : (fun k => (∫ x in boxFaceCollars a b i (ε k), f x ^ 2
      ∂(PDE.volumeOn (PDE.axisBox a b))) / (ε k) ^ 2) =ᶠ[atTop] (fun _ => (0 : ℝ)) := hevent
  exact tendsto_const_nhds.congr' heq.symm

end EinsteinFull.Regeneration
