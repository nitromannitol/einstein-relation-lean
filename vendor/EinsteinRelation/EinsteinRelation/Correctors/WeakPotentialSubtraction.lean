import EinsteinRelation.Calculus.Weak
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.SpecificCodomains.Pi

open MeasureTheory
namespace EinsteinRelation.Correctors

/-- Subtract genuine square-integrable spatial weak potentials on a finite
region; source `paper/main.tex:693-698,727-729`. -/
theorem hasWeakGradient_sub_of_memLp {d : ℕ} (U : Set (Vec d))
    [IsFiniteMeasure (volume.restrict U)]
    (u v : Vec d → ℝ) (g h : Vec d → Vec d)
    (hu : MemLp u 2 (volume.restrict U)) (hv : MemLp v 2 (volume.restrict U))
    (hg : MemLp g 2 (volume.restrict U)) (hh : MemLp h 2 (volume.restrict U))
    (hwu : HasWeakGradient U u g) (hwv : HasWeakGradient U v h) :
    HasWeakGradient U (fun x => u x - v x) (fun x => g x - h x) := by
  intro i
  refine ⟨(hwu i).1.sub (hwv i).1, (hwu i).2.1.sub (hwv i).2.1, ?_⟩
  intro φ hφ
  have hd : Continuous (coordinateDerivative i φ) :=
    (hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdc : HasCompactSupport (coordinateDerivative i φ) :=
    hφ.2.1.fderiv_apply ℝ (unitVector i)
  obtain ⟨B, hB⟩ := hdc.exists_bound_of_continuous hd
  obtain ⟨C, hC⟩ := hφ.2.1.exists_bound_of_continuous hφ.1.continuous
  have huφ := (hu.integrable (by norm_num)).mul_bdd hd.aestronglyMeasurable
    (ae_of_all _ hB)
  have hvφ := (hv.integrable (by norm_num)).mul_bdd hd.aestronglyMeasurable
    (ae_of_all _ hB)
  have hgφ := ((memLp_pi_iff.mp hg i).integrable (by norm_num)).mul_bdd
    hφ.1.continuous.aestronglyMeasurable (ae_of_all _ hC)
  have hhφ := ((memLp_pi_iff.mp hh i).integrable (by norm_num)).mul_bdd
    hφ.1.continuous.aestronglyMeasurable (ae_of_all _ hC)
  change (∫ x in U, (u x - v x) * coordinateDerivative i φ x) =
    -(∫ x in U, (g x i - h x i) * φ x)
  simp_rw [sub_mul]
  rw [integral_sub huφ hvφ, integral_sub hgφ hhφ,
    (hwu i).2.2 φ hφ, (hwv i).2.2 φ hφ]
  ring

end EinsteinRelation.Correctors
