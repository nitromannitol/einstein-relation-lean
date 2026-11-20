import EinsteinFull.Homogenization.SourceOptimizerMultiscale
import EinsteinFull.Homogenization.MultiscaleVectorAverages
import Homogenization.PDE.DirichletRHS
import Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundWeakNorms.EnergyDensities

/-!
# Energy of the response optimizer

Uniform ellipticity controls the squared normalized `L²` gradient norm by the
response energy, as used in Armstrong, Kuusi and Mourrat, *Quantitative
Stochastic Homogenization and Large-Scale Regularity*, (2.49).
-/

open scoped ENNReal
open MeasureTheory
open _root_.Homogenization

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinRelation.External.AKM
open Book.Ch05.Section53.JUpperBoundWeakNorms

/-- The normalized squared `L²` gradient norm of the canonical optimizer is at
most twice its response energy. -/
theorem memLp_and_sourceOptimizer_gradient_norm_sq_le_response
    {d : ℕ} [NeZero d] {K : ℝ} (a : Coefficient d K) (Q : TriadicCube d)
    (k : ℕ) (hk : K ≤ (k : ℝ) + 1) (p q : Vec d) :
    let U := Book.Ch02.cubeDomain Q
    let A := sourceCoeffOn a U k hk
    let v := (Book.Ch02.canonicalMaximizer (Book.Ch02.responseExistenceTheory U A) p q).toSolution
    MemLp (fun x => euclideanNorm (v.toH1.grad x)) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) ∧
    (cubeLpNorm Q (2 : ℝ≥0∞) (fun x => euclideanNorm (v.toH1.grad x))) ^ 2 ≤
      2 * Book.Ch02.responseJ U A p q := by
  intro U A v
  have hmem := (memLp_and_cubeLpNorm_grad_coord_le_euclidean Q v.toH1).1
  refine ⟨hmem, ?_⟩
  have hpow := cubeLpNorm_rpow_eq_cubeAverage_norm_rpow
    (Q := Q) (p := (2 : ℝ≥0∞)) (f := fun x => euclideanNorm (v.toH1.grad x))
    (by norm_num) (by norm_num) hmem
  have heq : (cubeLpNorm Q (2 : ℝ≥0∞) (fun x => euclideanNorm (v.toH1.grad x))) ^ 2 =
      cubeAverage Q (fun x => vecNormSq (v.toH1.grad x)) := by
    simpa [Real.rpow_natCast, Real.norm_eq_abs, abs_of_nonneg (euclideanNorm_nonneg _),
      euclideanNorm_sq] using hpow
  have hgrad : IntegrableOn (fun x => vecNormSq (v.toH1.grad x)) (openCubeSet Q) volume :=
    integrableOn_vecNormSq_h1Grad v.toH1
  have henergy := ch02_variationEnergyIntegrand_integrableOn U A v
  change IntegrableOn (Book.Ch02.variationEnergyIntegrand U A v) (openCubeSet Q) volume at henergy
  have hpoint : ∀ᵐ x ∂volume.restrict (openCubeSet Q),
      vecNormSq (v.toH1.grad x) ≤ Book.Ch02.variationEnergyIntegrand U A v x := by
    filter_upwards [ae_restrict_of_ae (regularCoefficient_ae_eq a)] with x hx
    have hl := (a.elliptic x (v.toH1.grad x)).1
    change vecNormSq (v.toH1.grad x) ≤
      vecDot (v.toH1.grad x) (matVecMul (a.field x) (v.toH1.grad x)) at hl
    simpa only [Book.Ch02.variationEnergyIntegrand, A, sourceCoeffOn, hx,
      vecDot_matVecMul_symmPart] using hl
  have havg : cubeAverage Q (fun x => vecNormSq (v.toH1.grad x)) ≤
      Book.Ch02.variationEnergyValue U A v := by
    rw [cubeAverage_eq_integralAverage_openCubeSet]
    unfold integralAverage Book.Ch02.variationEnergyValue Book.Ch02.average
    change _ ≤ (volume (openCubeSet Q)).toReal⁻¹ *
      ∫ x in openCubeSet Q, Book.Ch02.variationEnergyIntegrand U A v x ∂volume
    exact mul_le_mul_of_nonneg_left (integral_mono_ae hgrad henergy hpoint) (by positivity)
  have hresponse := Book.Ch02.responseJ_eq_energy_of_isResponseMaximizer
    (Book.Ch02.canonicalMaximizer (Book.Ch02.responseExistenceTheory U A) p q).isMaximizer
  rw [heq]
  linarith

/-- The optimizer's gradient deviation from a constant vector has `L²`
energy bounded by the response and the squared target vector. -/
theorem memLp_and_sourceOptimizer_gradient_sub_norm_sq_le_response
    {d : ℕ} [NeZero d] {K : ℝ} (a : Coefficient d K) (Q : TriadicCube d)
    (k : ℕ) (hk : K ≤ (k : ℝ) + 1) (p q b : Vec d) :
    let U := Book.Ch02.cubeDomain Q
    let A := sourceCoeffOn a U k hk
    let v := (Book.Ch02.canonicalMaximizer (Book.Ch02.responseExistenceTheory U A) p q).toSolution
    MemLp (fun x => euclideanNorm (v.toH1.grad x - b)) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) ∧
    (cubeLpNorm Q (2 : ℝ≥0∞) (fun x => euclideanNorm (v.toH1.grad x - b))) ^ 2 ≤
      4 * Book.Ch02.responseJ U A p q + 2 * vecNormSq b := by
  intro U A v
  let : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  let hU := (isOpenBoundedConvexDomain_openCubeSet Q).isSobolevRegularDomain
  let v₀ : H1Function (openCubeSet Q) := v.toH1
  let w : H1Function (openCubeSet Q) := v₀ - H1Function.affineOnIsSobolevRegularDomain hU b
  have hw : w.grad = fun x => v.toH1.grad x - b := by
    change (v₀ - H1Function.affineOnIsSobolevRegularDomain hU b).grad =
      fun x => v₀.grad x - b
    rw [H1Function.sub_grad]
    funext x
    rw [H1Function.affineOnIsSobolevRegularDomain_grad]
  have hsub : MemLp (fun x => euclideanNorm (v.toH1.grad x - b)) (2 : ℝ≥0∞)
      (normalizedCubeMeasure Q) := by
    simpa only [hw] using (memLp_and_cubeLpNorm_grad_coord_le_euclidean Q w).1
  have hgrad := (memLp_and_sourceOptimizer_gradient_norm_sq_le_response a Q k hk p q)
  change MemLp (fun x => euclideanNorm (v.toH1.grad x)) (2 : ℝ≥0∞)
      (normalizedCubeMeasure Q) ∧ _ at hgrad
  have hsquare (f : Vec d → Vec d)
      (hf : MemLp (fun x => euclideanNorm (f x)) (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
      (cubeLpNorm Q (2 : ℝ≥0∞) (fun x => euclideanNorm (f x))) ^ 2 =
        cubeAverage Q (fun x => vecNormSq (f x)) := by
    have h := cubeLpNorm_rpow_eq_cubeAverage_norm_rpow
      (Q := Q) (p := (2 : ℝ≥0∞)) (f := fun x => euclideanNorm (f x))
      (by norm_num) (by norm_num) hf
    simpa [Real.rpow_natCast, Real.norm_eq_abs, abs_of_nonneg (euclideanNorm_nonneg _),
      euclideanNorm_sq] using h
  have hint (f : Vec d → Vec d)
      (hf : MemLp (fun x => euclideanNorm (f x)) (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
      Integrable (fun x => vecNormSq (f x)) (normalizedCubeMeasure Q) := by
    simpa only [euclideanNorm_sq] using hf.integrable_sq
  have hpoint (x : Vec d) : vecNormSq (v.toH1.grad x - b) ≤
      2 * vecNormSq (v.toH1.grad x) + 2 * vecNormSq b := by
    have h := vecNormSq_sub_le (v.toH1.grad x) b
    simpa only [mul_add] using h
  have havg : cubeAverage Q (fun x => vecNormSq (v.toH1.grad x - b)) ≤
      2 * cubeAverage Q (fun x => vecNormSq (v.toH1.grad x)) + 2 * vecNormSq b := by
    simp only [cubeAverage_eq_integral_normalizedCubeMeasure]
    have h := integral_mono (hint _ hsub)
      (((hint _ hgrad.1).const_mul 2).add (integrable_const (2 * vecNormSq b))) hpoint
    change (∫ x, vecNormSq (v.toH1.grad x - b) ∂normalizedCubeMeasure Q) ≤
      ∫ x, 2 * vecNormSq (v.toH1.grad x) + 2 * vecNormSq b ∂normalizedCubeMeasure Q at h
    rw [integral_add ((hint _ hgrad.1).const_mul 2) (integrable_const _), integral_const_mul] at h
    simpa only [integral_const, Measure.real_def, normalizedCubeMeasure_apply_univ,
      ENNReal.toReal_one, one_smul] using h
  refine ⟨hsub, ?_⟩
  rw [hsquare _ hsub]
  rw [← hsquare _ hgrad.1] at havg
  linarith [hgrad.2]

end EinsteinFull.Homogenization
