import EinsteinFull.Homogenization.SourceBlockComparison
import Homogenization.CoarseGraining.MuOperator.AEEOperator.CoeffOperatorData

/-!
# Integrability of doubled energies

The doubled quadratic energies of Armstrong, Kuusi and Mourrat,
*Quantitative Stochastic Homogenization and Large-Scale Regularity*, Chapter 2,
are integrable for admissible states under almost-everywhere ellipticity.
-/

open MeasureTheory

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport
open _root_.Homogenization

/-- A block L² state has an integrable energy density in an a.e. elliptic
medium on a finite-volume domain. -/
theorem integrableOn_blockEnergyDensity_of_isAEEllipticFieldOn
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d} {lam Lam : ℝ}
    [IsFiniteMeasure (volumeMeasureOn U)] {X : BlockState d}
    (hEll : IsAEEllipticFieldOn lam Lam U a) (hX : MemBlockL2 U X.eval) :
    IntegrableOn (blockEnergyDensity a X) U := by
  by_cases hz : volume U = 0
  · have hzero : volumeMeasureOn U = 0 := Measure.restrict_eq_zero.mpr hz
    rw [IntegrableOn, ← volumeMeasureOn, hzero]
    exact integrable_zero_measure
  have htop : volume U ≠ ⊤ := by
    have hfinite := measure_ne_top (volumeMeasureOn U) Set.univ
    simpa [volumeMeasureOn] using hfinite
  have hv : 0 < (volume U).toReal := ENNReal.toReal_pos hz htop
  let M := AEEMuCoeffOperatorData.ofIsAEEllipticFieldOn hEll hv
  let F : HilbertBlockL2 U := toHilbertBlockL2OfBlockField hX
  have hint : Integrable (fun x => inner ℝ (F x) ((M.operator F) x))
      (volumeMeasureOn U) := MeasureTheory.L2.integrable_inner F (M.operator F)
  have hmatch : (fun x => ((volume U).toReal / 2) *
      inner ℝ (F x) ((M.operator F) x)) =ᵐ[volumeMeasureOn U]
      blockEnergyDensity a X := by
    filter_upwards [M.ae_apply_operator_normalizedBlockCoeffOperator F,
      coeFn_toHilbertBlockL2OfBlockField hX, ae_restrict_mem hEll.measurableSet] with
      x hOp hF hx
    rw [hOp, normalizedBlockCoeffOperator_apply_of_mem a hx, hF]
    simp only [real_inner_smul_right]
    have hcancel : (volume U).toReal / 2 * (volume U).toReal⁻¹ = 1 / 2 := by
      field_simp
    rw [← mul_assoc, hcancel]
    simp [HilbertBlockVec.inner_def, HilbertBlockVec.applyBlockMat_apply,
      hilbertifyBlockField, blockEnergyDensity]
  exact (hint.const_mul ((volume U).toReal / 2)).congr hmatch

/-- Every admissible block state has an integrable energy for a source
coefficient on a finite-volume measurable domain. -/
theorem integrableOn_sourceBlockEnergyDensity {d : ℕ} {K : ℝ}
    (a : Coefficient d K) {U : Set (Vec d)} (hU : MeasurableSet U)
    [IsFiniteMeasure (volumeMeasureOn U)] {P : BlockVec d} {X : BlockState d}
    (hX : IsBlockMuAdmissible U P X) :
    IntegrableOn (blockEnergyDensity a.field X) U := by
  obtain ⟨k, hk⟩ := exists_nat_ge K
  have hk' : K ≤ (k : ℝ) + 1 := by linarith
  have hEll := regularCoefficient_aeeQuantitativeEllipticSlice U hU k hk' a
  have hint := integrableOn_blockEnergyDensity_of_isAEEllipticFieldOn hEll hX.memBlockL2_eval
  apply hint.congr
  filter_upwards [ae_restrict_of_ae (regularCoefficient_ae_eq a)] with x hx
  simp only [blockEnergyDensity, blockCoeffField, hx]

/-- The source Dirichlet energy is the doubled variational energy with zero
prescribed flux, for every open finite-volume domain. -/
theorem sourceDirichletEnergy_eq_Mu {d : ℕ} {K : ℝ}
    (a : Coefficient d K) {U : Set (Vec d)} (hU : IsOpen U)
    [IsFiniteMeasure (volumeMeasureOn U)] (e : Vec d) :
    EinsteinRelation.External.AKM.sourceDirichletEnergy a U e = Mu U (e, 0) a.field := by
  apply le_antisymm
  · apply sourceDirichletEnergy_le_Mu_of_integrable a hU e
    intro X hX
    exact integrableOn_sourceBlockEnergyDensity a hU.measurableSet hX
  · exact Mu_le_sourceDirichletEnergy a hU e

/-- The Dirichlet energy agrees with the doubled energy evaluated on the
measurable representative of the source coefficient. -/
theorem sourceDirichletEnergy_eq_Mu_regularCoefficient {d : ℕ} {K : ℝ}
    (a : Coefficient d K) {U : Set (Vec d)} (hU : IsOpen U)
    [IsFiniteMeasure (volumeMeasureOn U)] (e : Vec d) :
    EinsteinRelation.External.AKM.sourceDirichletEnergy a U e =
      Mu U (e, 0) (regularCoefficient a).toFun := by
  rw [sourceDirichletEnergy_eq_Mu a hU e]
  exact Mu_congr_of_ae_eq (ae_restrict_of_ae (regularCoefficient_ae_eq a).symm) (e, 0)

end EinsteinFull.Homogenization
