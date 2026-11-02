import EinsteinFull.External.Source.GMPDirichletKernel

open EinsteinRelation MeasureTheory EinsteinFull.External.Source.GMP
open scoped ENNReal

namespace EinsteinFull.Calculus

/-- The positive-power cutoff gradient and its coefficient energy are measurable. -/
theorem b_positive_cutoff_gradient_energy_aemeasurable
    {d : ℕ} {κ : ℝ} {I : Set ℝ} {U : Set (Vec d)}
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hcoeff : IsUniformlyElliptic κ ρ α)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α I U u G)
    (ε : ℝ) (η : ℝ × Vec d → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η) (p : ℝ) :
    let w : ℝ × Vec d → ℝ := fun z => u z + ε
    let J : ℝ × Vec d → Vec d := fun z =>
      η z • ((p / 2 * (w z) ^ (p / 2 - 1)) • G z) +
        (w z) ^ (p / 2) • (fun j => fderiv ℝ η z (0, unitVector j))
    AEStronglyMeasurable J (volume.restrict (I ×ˢ U)) ∧
    AEMeasurable (fun z => ENNReal.ofReal (dot ((α z.2).mulVec (J z)) (J z)))
      (volume.restrict (I ×ˢ U)) := by
  let μ := volume.restrict (I ×ˢ U)
  let w : ℝ × Vec d → ℝ := fun z => u z + ε
  let Dη : ℝ × Vec d → Vec d := fun z j => fderiv ℝ η z (0, unitVector j)
  let J : ℝ × Vec d → Vec d := fun z =>
    η z • ((p / 2 * (w z) ^ (p / 2 - 1)) • G z) + (w z) ^ (p / 2) • Dη z
  have hw : AEMeasurable w μ := hcal.1.aestronglyMeasurable.aemeasurable.add_const ε
  have hDη : Continuous Dη :=
    continuous_pi fun j => (hη.continuous_fderiv (by simp)).clm_apply continuous_const
  have hJ : AEStronglyMeasurable J μ :=
    (hη.continuous.aestronglyMeasurable.smul
      (((hw.pow_const (p / 2 - 1)).aestronglyMeasurable.const_mul (p / 2)).smul
        hcal.2.1)).add
      ((hw.pow_const (p / 2)).aestronglyMeasurable.smul hDη.aestronglyMeasurable)
  refine ⟨hJ, ?_⟩
  apply ENNReal.measurable_ofReal.comp_aemeasurable
  have hα : AEMeasurable (fun z : ℝ × Vec d => α z.2) μ :=
    (hcoeff.2.1.comp measurable_snd).aemeasurable
  have hm (i : Fin d) : AEMeasurable (fun z => ∑ j, α z.2 i j * J z j) μ := by
    convert (Finset.aemeasurable_sum (f := fun j z => α z.2 i j * J z j) Finset.univ
        fun j _ => (((continuous_id : Continuous (fun A : Mat d => A)).matrix_elem i j).measurable.comp_aemeasurable hα).mul (hJ.aemeasurable.eval j)) using 1
    ext z
    simp only [Finset.sum_apply]
  convert (Finset.aemeasurable_sum (f := fun i z => (∑ j, α z.2 i j * J z j) * J z i)
      Finset.univ fun i _ => (hm i).mul (hJ.aemeasurable.eval i)) using 1
  ext z
  simp only [Finset.sum_apply, dot, Matrix.mulVec, dotProduct, J, w, Dη]

end EinsteinFull.Calculus

