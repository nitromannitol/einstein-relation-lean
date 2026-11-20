import EinsteinFull.Homogenization.SourceEnergyStationarity
import EinsteinFull.Homogenization.SourceDirichletSubadditivity

/-!
# Annealed Dirichlet energies

Subadditivity and stationarity give the monotonicity of the expected Dirichlet
energies in Armstrong, Kuusi and Mourat, *Quantitative Stochastic Homogenization
and Large-Scale Regularity*, (1.21)–(1.22).
-/

open MeasureTheory Filter Topology
open _root_.Homogenization

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport

/-- Expected Dirichlet energy decreases between successive triadic scales. -/
theorem expected_sourceDirichletEnergy_succ_le {d : ℕ} [NeZero d] {K : ℝ}
    (hK : 0 ≤ K) (P : Measure (Coefficient d K)) [IsFiniteMeasure P]
    (hP : ∀ z : LatticeIndex d, Measure.map (translateCoefficient (latticeShift z)) P = P)
    (e : Vec d) (n : ℕ) :
    (∫ a, EinsteinRelation.External.AKM.sourceDirichletEnergy a
      (EinsteinRelation.External.AKM.sourceTriadicCube d (n + 1)) e ∂P) ≤
    ∫ a, EinsteinRelation.External.AKM.sourceDirichletEnergy a
      (EinsteinRelation.External.AKM.sourceTriadicCube d n) e ∂P := by
  classical
  let Q := originCube d ((n + 1 : ℕ) : ℤ)
  let D := descendantsAtDepth Q 1
  let F : Coefficient d K → TriadicCube d → ℝ := fun a R =>
    EinsteinRelation.External.AKM.sourceDirichletEnergy a (openCubeSet R) e
  have hF (R : TriadicCube d) : Integrable (fun a => F a R) P :=
    integrable_sourceDirichletEnergy_openCube hK P R e
  have hsum : Integrable (fun a => ∑ R ∈ D, F a R) P := by
    exact integrable_finsetSum D (fun R _ => hF R)
  have havg : Integrable (fun a => descendantsAverage Q 1 (F a)) P := by
    simpa [descendantsAverage, D] using hsum.const_mul ((D.card : ℝ)⁻¹)
  have hparent : Integrable (fun a => F a Q) P := hF Q
  have hbound := integral_mono hparent havg
    (fun a => sourceDirichletEnergy_le_descendantsAverage a Q 1 e)
  have hchild (R : TriadicCube d) (hR : R ∈ D) :
      (∫ a, F a R ∂P) = ∫ a, EinsteinRelation.External.AKM.sourceDirichletEnergy a
        (EinsteinRelation.External.AKM.sourceTriadicCube d n) e ∂P := by
    have hs := scale_eq_sub_of_mem_descendantsAtDepth hR
    have hs' : R.scale = (n : ℤ) := by dsimp [D, Q, originCube] at hs; omega
    exact sourceDirichletEnergy_expected_eq_origin hK P hP R n hs' e
  have havg_eq : (∫ a, descendantsAverage Q 1 (F a) ∂P) =
      ∫ a, EinsteinRelation.External.AKM.sourceDirichletEnergy a
        (EinsteinRelation.External.AKM.sourceTriadicCube d n) e ∂P := by
    change (∫ a, (D.card : ℝ)⁻¹ * ∑ R ∈ D, F a R ∂P) = _
    rw [integral_const_mul, integral_finsetSum D (fun R _ => hF R)]
    have hD : (D.card : ℝ) ≠ 0 := by
      exact_mod_cast Finset.card_ne_zero.mpr (descendantsAtDepth_nonempty Q 1)
    have heq : (∑ R ∈ D, ∫ a, F a R ∂P) =
        D.card * (∫ a, EinsteinRelation.External.AKM.sourceDirichletEnergy a
          (EinsteinRelation.External.AKM.sourceTriadicCube d n) e ∂P) := by
      rw [Finset.sum_congr rfl hchild, Finset.sum_const, nsmul_eq_mul]
    rw [heq, ← mul_assoc, inv_mul_cancel₀ hD, one_mul]
  rw [havg_eq] at hbound
  rw [sourceTriadicCube_eq_openCubeSet d (n + 1)]
  simpa [F, Q] using hbound

/-- Expected Dirichlet energies are antitone along triadic scales. -/
theorem antitone_expected_sourceDirichletEnergy {d : ℕ} [NeZero d] {K : ℝ}
    (hK : 0 ≤ K) (P : Measure (Coefficient d K)) [IsFiniteMeasure P]
    (hP : ∀ z : LatticeIndex d, Measure.map (translateCoefficient (latticeShift z)) P = P)
    (e : Vec d) :
    Antitone (fun n : ℕ => ∫ a, EinsteinRelation.External.AKM.sourceDirichletEnergy a
      (EinsteinRelation.External.AKM.sourceTriadicCube d n) e ∂P) :=
  antitone_nat_of_succ_le (expected_sourceDirichletEnergy_succ_le hK P hP e)

/-- Expected Dirichlet energies converge to their infimum over triadic scales. -/
theorem tendsto_expected_sourceDirichletEnergy {d : ℕ} [NeZero d] {K : ℝ}
    (hK : 0 ≤ K) (P : Measure (Coefficient d K)) [IsFiniteMeasure P]
    (hP : ∀ z : LatticeIndex d, Measure.map (translateCoefficient (latticeShift z)) P = P)
    (e : Vec d) :
    Tendsto (fun n : ℕ => ∫ a, EinsteinRelation.External.AKM.sourceDirichletEnergy a
      (EinsteinRelation.External.AKM.sourceTriadicCube d n) e ∂P) atTop
      (𝓝 (⨅ n : ℕ, ∫ a, EinsteinRelation.External.AKM.sourceDirichletEnergy a
        (EinsteinRelation.External.AKM.sourceTriadicCube d n) e ∂P)) :=
  EinsteinRelation.External.AKM.tendsto_expected_sourceDirichletEnergy_of_antitone P e
    (antitone_expected_sourceDirichletEnergy hK P hP e)

end EinsteinFull.Homogenization
