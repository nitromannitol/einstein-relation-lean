import EinsteinFull.Homogenization.OriginCubeAffineMean
import EinsteinFull.Homogenization.SourceResponseDecrement

/-!
# Multiscale bound for the response optimizer

The optimizer in Armstrong, Kuusi and Mourrat, *Quantitative Stochastic
Homogenization and Large-Scale Regularity*, Chapter 2, has zero mean on the
centered cube. The multiscale Poincaré inequality therefore bounds its affine
remainder in normalized `L²`, as in the first step of Lemma 2.15.
-/

open scoped ENNReal
open MeasureTheory
open _root_.Homogenization

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinRelation.External.AKM

/-- The response optimizer minus any linear function has a multiscale `L²`
bound with a constant depending only on dimension. -/
theorem exists_sourceOptimizer_multiscalePoincare (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {K : ℝ} (n k : ℕ) (hk : K ≤ (k : ℝ) + 1)
      (a : Coefficient d K) (p q b : Vec d),
      let Q := originCube d (n : ℤ)
      let U := Book.Ch02.cubeDomain Q
      let A := sourceCoeffOn a U k hk
      let v := (Book.Ch02.canonicalMaximizer (Book.Ch02.responseExistenceTheory U A) p q).toSolution.toH1
      (∀ j, ∀ R ∈ descendantsAtDepth Q j, ∀ i,
        Integrable (fun x => v.grad x i - b i) (normalizedCubeMeasure R)) ∧
      MemLp (fun x => euclideanNorm (v.grad x - b)) (2 : ℝ≥0∞)
        (normalizedCubeMeasure Q) ∧
      cubeLpNorm Q (2 : ℝ≥0∞) (fun x => v x - vecDot b x) ≤
        C * (cubeLpNorm Q (2 : ℝ≥0∞) (fun x => euclideanNorm (v.grad x - b)) +
          ∑ j ∈ Finset.range (n + 1), (3 : ℝ) ^ (n - j) *
            Real.sqrt (descendantsAverage Q j
              (fun R => vecNormSq (fun i => cubeAverage R (fun x => v.grad x i) - b i)))) := by
  obtain ⟨C, hC, h⟩ := exists_originCube_multiscalePoincare_affine d
  refine ⟨C, hC, ?_⟩
  intro K n k hk a p q b Q U A v
  have hz : MeanZeroOn (openCubeSet Q) v.toFun := by
    exact Book.Ch02.canonicalMaximizer_meanZero (Book.Ch02.responseExistenceTheory U A) p q
  have hbound := h n v b
  rw [cubeBesovOscillation_sub_vecDot_eq_cubeLpNorm n v hz b] at hbound
  exact hbound

end EinsteinFull.Homogenization
