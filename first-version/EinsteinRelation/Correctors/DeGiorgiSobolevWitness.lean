import Mathlib
import DeGiorgi.SobolevSpace.Witnesses
import EinsteinRelation.Correctors.EuclideanMemLpTransport
import EinsteinRelation.Correctors.DeGiorgiWeakGradientTransport

open MeasureTheory Filter
open scoped Topology ENNReal

/-! # Explicit De Giorgi `W^{1,2}` witnesses from repository weak gradients

A repository weak gradient of `u` on a set `U` of coordinate space, together with `L²`
membership of `u` and of the gradient on `U`, yields an explicit De Giorgi witness on the
Euclidean preimage of `U`. The function is transported by `WithLp.ofLp`, the gradient is
transported by `WithLp.toLp`, and its coordinates are pulled back along the coordinate
projections, so each component is `L²` on the preimage by the transport lemma.
-/

namespace EinsteinRelation.Correctors

/-- Repository weak gradients with `L²` data on `U` give an explicit De Giorgi `W^{1,2}`
witness on the Euclidean preimage of `U`, whose weak gradient is the transported field. -/
theorem exists_memW1pWitness_of_hasWeakGradient {d : ℕ} [NeZero d] {U : Set (Vec d)}
    {u : Vec d → ℝ} {g : Vec d → Vec d}
    (hu : MemLp u 2 (volume.restrict U)) (hg : MemLp g 2 (volume.restrict U))
    (h : HasWeakGradient U u g) :
    ∃ hw : DeGiorgi.MemW1pWitness 2
        (fun x : EuclideanSpace ℝ (Fin d) => u (WithLp.ofLp x))
        ((WithLp.ofLp : EuclideanSpace ℝ (Fin d) → Vec d) ⁻¹' U),
      hw.weakGrad = fun x => WithLp.toLp 2 (g (WithLp.ofLp x)) := by
  have hcomp : ∀ i : Fin d, MemLp (fun y : Vec d => g y i) 2 (volume.restrict U) :=
    fun i => hg.continuousLinearMap_comp (ContinuousLinearMap.proj i : Vec d →L[ℝ] ℝ)
  refine ⟨{ memLp := (memLp_comp_ofLp_iff U u 2).mpr hu
            weakGrad := fun x => WithLp.toLp 2 (g (WithLp.ofLp x))
            weakGrad_component_memLp := fun i =>
              (memLp_comp_ofLp_iff U (fun y : Vec d => g y i) 2).mpr (hcomp i)
            isWeakGrad := hasWeakGrad_of_hasWeakGradient h }, rfl⟩

end EinsteinRelation.Correctors
