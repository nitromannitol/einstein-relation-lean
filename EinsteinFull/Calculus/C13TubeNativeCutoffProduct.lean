import EinsteinRelation.Correctors.SpatialWeakProduct
import EinsteinRelation.TimeChange.EuclideanTransport
import PDEFoundation.PDE.DGNM.ProductTest

open EinsteinRelation MeasureTheory
open scoped ENNReal

namespace EinsteinFull

/-- A compact smooth cutoff preserves the native weak gradient and its Euclidean L² energy. -/
theorem c13_native_cutoff_weak_gradient {d : ℕ} {U : Set (Vec d)} (hU : IsOpen U)
    (u : Vec d → ℝ) (grad : Vec d → Vec d) (hu : HasWeakGradient U u grad)
    (hu2 : MemLp u 2 (volume.restrict U))
    (hg2 : MemLp (fun x => euclideanNorm (grad x)) 2 (volume.restrict U))
    (chi : Vec d → ℝ) (hchi : IsSpatialTest U chi) :
    HasWeakGradient U (fun x => chi x * u x)
      (fun x => chi x • grad x + u x • (fun j => fderiv ℝ chi x (unitVector j))) ∧
    MemLp (fun x => chi x * u x) 2 (volume.restrict U) ∧
    MemLp (fun x => euclideanNorm (chi x • grad x +
      u x • (fun j => fderiv ℝ chi x (unitVector j)))) 2 (volume.restrict U) := by
  have hw : HasWeakGradient U (fun x => chi x * u x)
      (fun x => chi x • grad x + u x • (fun j => fderiv ℝ chi x (unitVector j))) := by
    intro j
    simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, coordinateDerivative] using
      (Correctors.hasWeakGradient_mul_smooth hU hu hchi.1 j)
  have htop : MemLp chi ⊤ (volume.restrict U) :=
    PDE.DGNM.memLpOn_top_of_contDiff hchi.1 hchi.2.1
  have hcoord (j : Fin d) : MemLp (fun x => grad x j) 2 (volume.restrict U) := by
    apply hg2.mono' (hu j).2.1.aestronglyMeasurable
    apply ae_of_all
    intro x
    simpa only [TimeChange.euclideanNorm_eq_norm_toLp] using
      (PiLp.norm_apply_le (WithLp.toLp 2 (grad x)) j)
  have hprod : MemLp (fun x => chi x * u x) 2 (volume.restrict U) := by
    simpa only [mul_comm] using hu2.fun_mul htop
  have hvec (j : Fin d) : MemLp
      (fun x => chi x * grad x j + u x * fderiv ℝ chi x (unitVector j)) 2
      (volume.restrict U) := by
    have hdt : MemLp (fun x => fderiv ℝ chi x (unitVector j)) ⊤ (volume.restrict U) := by
      simpa only [PDE.classicalGradient_apply, PDE.basisVec, unitVector] using
        (PDE.DGNM.memLpOn_top_classicalGradient (U := U) hchi.1 hchi.2.1 j)
    have ha : MemLp (fun x => chi x * grad x j) 2 (volume.restrict U) := by
      simpa only [mul_comm] using (hcoord j).fun_mul htop
    exact ha.add (hu2.fun_mul hdt)
  have he : MemLp (fun x => (WithLp.toLp 2
      (chi x • grad x + u x • (fun j => fderiv ℝ chi x (unitVector j))) :
      EuclideanSpace ℝ (Fin d))) 2 (volume.restrict U) := by
    apply memLp_piLp_iff.mpr
    intro j
    simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hvec j
  refine ⟨hw, hprod, ?_⟩
  simpa only [TimeChange.euclideanNorm_eq_norm_toLp] using he.norm

end EinsteinFull
