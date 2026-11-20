import EinsteinFull.External.DFGW.MartingaleOneTimeCLT
import EinsteinFull.External.DFGW.GridRemainder

/-! # One-time scalar central limit theorem for increments

The projected martingale limit transfers to the original increment through the sublinear
mean-square approximation error.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation Filter
open scoped NNReal ENNReal Topology

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {d : ℕ} {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}
variable {X : ℝ → ℝ → C(ℝ, S) → Vec d}

/-- The projected increment has the normal limit of its martingale approximation on the
diffusively scaled integer grid. -/
theorem tendstoInDistribution_projected_increment_grid
    (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (hcoord : Draft.dfgwCoordSigma (S := S) Set.univ =
      Draft.dfgwTrajectoryMeasurableSpace (S := S))
    (hμ : μ Set.univ ≠ ⊤) (hPfin : P Set.univ ≠ ⊤)
    (φ : S → Vec d) (hφ : MemLp φ 2 μ) (hL2 : ∀ t, MemLp (compensated X φ t) 2 P)
    (N : ℝ≥0 → C(ℝ, S) → Vec d) (hN : Martingale N Draft.dfgwPast P)
    (hN2 : ∀ t, MemLp (N t) 2 P)
    (hstat : ∀ s t, (fun η => N (s + t) η - N s η) =ᵐ[P]
      fun η => N t (Draft.dfgwShift s η)) (e : Vec d)
    (hrem : Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ *
      ∫ η, (dot e (X 0 t η) - dot e (N t η)) ^ 2 ∂P) atTop (𝓝 0)) :
    letI : IsProbabilityMeasure P := hP.probability
    let σsq : ℝ≥0 := ⟨∫ η, dot e (N 1 η) ^ 2 ∂P,
      integral_nonneg fun _ => sq_nonneg _⟩
    TendstoInDistribution (fun (n : ℕ) η => (Real.sqrt (n + 1))⁻¹ *
      dot e (X 0 ((n + 1 : ℕ) : ℝ≥0) η)) atTop (id : ℝ → ℝ)
      (fun _ => P) (gaussianReal 0 σsq) := by
  let : IsProbabilityMeasure P := hP.probability
  let σsq : ℝ≥0 := ⟨∫ η, dot e (N 1 η) ^ 2 ∂P, integral_nonneg fun _ => sq_nonneg _⟩
  let : IsProbabilityMeasure (gaussianReal 0 σsq) := instIsProbabilityMeasureGaussianReal 0 σsq
  let A : ℕ → C(ℝ, S) → ℝ := fun n η => (Real.sqrt (n + 1))⁻¹ *
    dot e (X 0 ((n + 1 : ℕ) : ℝ≥0) η)
  let B : ℕ → C(ℝ, S) → ℝ := fun n η => (Real.sqrt (n + 1))⁻¹ *
    dot e (N ((n + 1 : ℕ) : ℝ≥0) η)
  have hB := tendstoInDistribution_projected_martingale_grid hP hcoord hμ hPfin N hN hN2 hstat e
  have hdiff : TendstoInMeasure P (A - B) atTop 0 := by
    have h := tendstoInMeasure_projected_grid_remainder hP φ hφ hL2 N hN2 e hrem
    refine TendstoInMeasure.congr ?_ EventuallyEq.rfl h
    intro n
    exact ae_of_all P fun η => by simp only [Pi.sub_apply, A, B]; ring
  have hA (n : ℕ) : AEMeasurable (A n) P := by
    have h := increment_dot_memLp hP φ hφ ((n + 1 : ℕ) : ℝ≥0) (hL2 _) e
    exact (h.const_mul _).aestronglyMeasurable.aemeasurable
  exact tendstoInDistribution_of_tendstoInMeasure_sub A id hB hdiff hA

end EinsteinFull.External.DFGW
