import EinsteinFull.Homogenization.SourceDirichletIntegrability
import EinsteinFull.Homogenization.SymmetricBlockEnergy
import EinsteinRelation.Correctors.AKMSourceDirichletCompetitors
import Homogenization.CoarseGraining.Definitions
import Homogenization.CoarseGraining.CoarseBounds.AeBridge

/-!
# Comparison of Dirichlet and block energies

The doubled variational energy in Armstrong, Kuusi and Mourrat,
*Quantitative Stochastic Homogenization and Large-Scale Regularity*, Chapter 2,
allows zero flux and hence is bounded above by the Dirichlet energy.
-/

open MeasureTheory

namespace EinsteinFull.Homogenization

open EinsteinRelation EinsteinRelation.Environment.AKMTestIntegralSupport

/-- For a source coefficient the block energy density is nonnegative. -/
theorem source_blockEnergyDensity_nonneg {d : ℕ} {K : ℝ}
    (a : Coefficient d K) (X : _root_.Homogenization.BlockState d) (x : Vec d) :
    0 ≤ _root_.Homogenization.blockEnergyDensity a.field X x := by
  have hEll := source_isEllipticMatrix a (le_max_left 1 K) (le_max_right 1 K) x
  have hle := potentialEnergy_le_symmetric_blockEnergyDensity a.field X x (a.symmetric x) hEll
  have hp := (a.elliptic x (X.potential x)).1
  have hs : 0 ≤ euclideanSq (X.potential x) := by
    unfold euclideanSq dot
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  nlinarith

/-- The doubled variational energy with zero prescribed flux is at most the
source Dirichlet energy. -/
theorem Mu_le_sourceDirichletEnergy {d : ℕ} {K : ℝ}
    (a : Coefficient d K) {U : Set (Vec d)} (hU : IsOpen U)
    [IsFiniteMeasure (_root_.Homogenization.volumeMeasureOn U)] (e : Vec d) :
    _root_.Homogenization.Mu U (e, 0) a.field ≤
      External.AKM.sourceDirichletEnergy a U e := by
  rw [External.AKM.sourceDirichletEnergy, _root_.Homogenization.Mu]
  apply le_csInf (External.AKM.sourceDirichletEnergy_admissible_nonempty a U e)
  rintro E ⟨u, g, hg, rfl⟩
  obtain ⟨w, _, hw⟩ := sourceH01_exists_h10 hU hg
  let X : _root_.Homogenization.BlockState d :=
    { potential := fun x => e + g x
      flux := fun _ => 0 }
  have hX : _root_.Homogenization.IsBlockMuAdmissible U (e, 0) X := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [X] using hg.2.1
    · refine ⟨w, ?_⟩
      funext x
      simp [X, hw]
    · simp [X, _root_.Homogenization.MemVectorL2]
    · have hz : (fun x => X.flux x - (e, (0 : Vec d)).2) = (0 : Vec d → Vec d) := by
        funext x
        simp [X]
      rw [hz]
      exact _root_.Homogenization.isSolenoidalZeroNormalTraceOn_zero
  have hbelow : BddBelow (_root_.Homogenization.muValueSet U (e, 0) a.field) := by
    refine ⟨0, ?_⟩
    rintro z ⟨Y, hY, rfl⟩
    unfold _root_.Homogenization.volumeAverage
    exact mul_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg)
      (integral_nonneg fun x => source_blockEnergyDensity_nonneg a Y x)
  apply (csInf_le hbelow (_root_.Homogenization.muValueSet_mem hX)).trans_eq
  unfold _root_.Homogenization.volumeAverage
  rw [setAverage_eq]
  congr 1
  apply integral_congr_ae
  filter_upwards with x
  exact symmetric_blockEnergyDensity_of_flux_eq_zero a.field X x (a.symmetric x) rfl

/-- If admissible block energies are integrable, the Dirichlet infimum is no
larger than the doubled energy with zero prescribed flux. -/
theorem sourceDirichletEnergy_le_Mu_of_integrable {d : ℕ} {K : ℝ}
    (a : Coefficient d K) {U : Set (Vec d)} (hU : IsOpen U)
    [IsFiniteMeasure (_root_.Homogenization.volumeMeasureOn U)] (e : Vec d)
    (hInt : ∀ X : _root_.Homogenization.BlockState d,
      _root_.Homogenization.IsBlockMuAdmissible U (e, 0) X →
        IntegrableOn (_root_.Homogenization.blockEnergyDensity a.field X) U) :
    External.AKM.sourceDirichletEnergy a U e ≤
      _root_.Homogenization.Mu U (e, 0) a.field := by
  unfold _root_.Homogenization.Mu
  apply le_csInf (_root_.Homogenization.muValueSet_nonempty U (e, 0) a.field)
  rintro z ⟨X, hX, rfl⟩
  obtain ⟨w, hw⟩ := hX.2.1
  have hw' : External.AKM.SourceH01 U w.toH1Function.toFun w.toH1Function.grad :=
    h10_sourceH01 hU w
  have hpot : (fun x => e + w.toH1Function.grad x) = X.potential := by
    funext x
    have hx := congrFun hw x
    change w.toH1Function.grad x = X.potential x - e at hx
    rw [hx]
    abel
  have hdensity := integrableOn_sourceDirichletDensity_of_sourceH01 a hU.measurableSet e hw'
  have hle := External.AKM.sourceDirichletEnergy_le_admissible a U e
    w.toH1Function.toFun w.toH1Function.grad hw'
  apply hle.trans
  rw [setAverage_eq]
  unfold _root_.Homogenization.volumeAverage
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr ENNReal.toReal_nonneg)
  apply integral_mono hdensity (hInt X hX)
  intro x
  have hpoint := potentialEnergy_le_symmetric_blockEnergyDensity a.field X x (a.symmetric x)
    (source_isEllipticMatrix a (le_max_left 1 K) (le_max_right 1 K) x)
  dsimp only
  rw [congrFun hpot x]
  exact hpoint

end EinsteinFull.Homogenization
