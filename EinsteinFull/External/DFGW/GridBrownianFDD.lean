import EinsteinFull.External.DFGW.RoundedBrownianFDD
import EinsteinFull.External.DFGW.MartingaleFiniteTimeRounding
import EinsteinFull.External.DFGW.ScaledFiniteDimensionalTransfer
import EinsteinFull.External.DFGW.GridScale

/-! # Finite-dimensional convergence along diffusive grids

Rounding and the martingale approximation transfer the grid-time limit to the original
continuous increment process at finitely many times.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation Filter
open scoped NNReal ENNReal Topology BigOperators

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {d : ℕ} {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- Diffusively rescaled martingale values converge jointly along grid scales. -/
theorem tendstoInDistribution_grid_martingale_fdd
    (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (hcoord : Draft.dfgwCoordSigma (S := S) Set.univ =
      Draft.dfgwTrajectoryMeasurableSpace (S := S))
    (hμ : μ Set.univ ≠ ⊤) (hPfin : P Set.univ ≠ ⊤)
    (N : ℝ≥0 → C(ℝ, S) → Vec d) (hN : Martingale N Draft.dfgwPast P)
    (hN2 : ∀ t, MemLp (N t) 2 P)
    (hstat : ∀ s t, (fun η => N (s + t) η - N s η) =ᵐ[P]
      fun η => N t (Draft.dfgwShift s η))
    (D : Mat d) (hD : D.transpose = D)
    (hcov : ∀ e : Vec d, dot e (D.mulVec e) = ∫ η, dot e (N 1 η) ^ 2 ∂P)
    (W : Measure (Path d)) (hW : IsBrownianLaw D W)
    (m : ℕ) (t : Fin m → ℝ≥0) (ht : ∀ j, t j ≤ 1) :
    letI : IsProbabilityMeasure P := hP.probability
    letI : IsProbabilityMeasure W := hW.1
    TendstoInDistribution (fun n η j => gridScale n •
      N (((gridScale n)⁻¹ ^ 2).toNNReal * t j) η) atTop
      (fun γ : Path d => fun j => γ (t j)) (fun _ => P) W := by
  let : IsProbabilityMeasure P := hP.probability
  let : IsProbabilityMeasure W := hW.1
  let A : ℕ → C(ℝ, S) → Fin m → Vec d := fun n η j => gridScale n •
    N (((gridScale n)⁻¹ ^ 2).toNNReal * t j) η
  let B : ℕ → C(ℝ, S) → Fin m → Vec d := fun n η j => gridScale n •
    N (floorTime (((gridScale n)⁻¹ ^ 2).toNNReal * t j)) η
  let Z : Path d → Fin m → Vec d := fun γ j => γ (t j)
  have hb := tendstoInDistribution_rounded_martingale_fdd
    hP hcoord hμ hPfin N hN hN2 hstat D hD hcov W hW m t ht
  have hB : TendstoInDistribution B atTop Z (fun _ => P) W := by
    convert hb using 1
    funext n η j
    change gridScale n • N (floorTime (((gridScale n)⁻¹ ^ 2).toNNReal * t j)) η = _
    rw [floorTime_gridScale]
    rfl
  have hdiff : TendstoInMeasure P (A - B) atTop 0 := by
    have h := (tendstoInMeasure_martingale_finite_rounding hP N hN hN2 hstat t).comp
      tendsto_gridScale
    refine TendstoInMeasure.congr ?_ EventuallyEq.rfl h
    intro n
    apply ae_of_all P
    intro η
    funext j i
    simp only [Function.comp_apply, A, B, Pi.sub_apply, Pi.smul_apply, smul_sub]
  have hA (n : ℕ) : AEMeasurable (A n) P := by
    apply Measurable.aemeasurable
    apply measurable_pi_iff.mpr
    intro j
    have hm := (hN.stronglyAdapted (((gridScale n)⁻¹ ^ 2).toNNReal * t j)).mono
      (Draft.dfgwPast.le _)
    exact (hm.const_smul (gridScale n)).measurable
  exact tendstoInDistribution_of_tendstoInMeasure_sub A Z hB hdiff hA

/-- The original process converges at finitely many times along the diffusive grid scales. -/
theorem tendstoInDistribution_grid_process_fdd
    (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (hcoord : Draft.dfgwCoordSigma (S := S) Set.univ =
      Draft.dfgwTrajectoryMeasurableSpace (S := S))
    (hμ : μ Set.univ ≠ ⊤) (hPfin : P Set.univ ≠ ⊤)
    {X : ℝ → ℝ → C(ℝ, S) → Vec d} {Y : C(ℝ, S) → Path d}
    (hX : Draft.IsDFGWTrajectoryFamily P X Y)
    (φ : S → Vec d) (hφ : MemLp φ 2 μ) (hL2 : ∀ t, MemLp (compensated X φ t) 2 P)
    (N : ℝ≥0 → C(ℝ, S) → Vec d) (hN : Martingale N Draft.dfgwPast P)
    (hN2 : ∀ t, MemLp (N t) 2 P)
    (hstat : ∀ s t, (fun η => N (s + t) η - N s η) =ᵐ[P]
      fun η => N t (Draft.dfgwShift s η))
    (hrem : ∀ e : Vec d, Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ *
      ∫ η, (dot e (X 0 t η) - dot e (N t η)) ^ 2 ∂P) atTop (𝓝 0))
    (D : Mat d) (hD : D.transpose = D)
    (hcov : ∀ e : Vec d, dot e (D.mulVec e) = ∫ η, dot e (N 1 η) ^ 2 ∂P)
    (W : Measure (Path d)) (hW : IsBrownianLaw D W)
    (m : ℕ) (t : Fin m → ℝ≥0) (ht : ∀ j, t j ≤ 1) :
    letI : IsProbabilityMeasure P := hP.probability
    letI : IsProbabilityMeasure W := hW.1
    TendstoInDistribution (fun n η j => gridScale n •
      Y η (((gridScale n)⁻¹ ^ 2).toNNReal * t j)) atTop
      (fun γ : Path d => fun j => γ (t j)) (fun _ => P) W := by
  let : IsProbabilityMeasure P := hP.probability
  let : IsProbabilityMeasure W := hW.1
  let A : ℕ → C(ℝ, S) → Fin m → Vec d := fun n η j => gridScale n •
    Y η (((gridScale n)⁻¹ ^ 2).toNNReal * t j)
  let B : ℕ → C(ℝ, S) → Fin m → Vec d := fun n η j => gridScale n •
    N (((gridScale n)⁻¹ ^ 2).toNNReal * t j) η
  let Z : Path d → Fin m → Vec d := fun γ j => γ (t j)
  have hB : TendstoInDistribution B atTop Z (fun _ => P) W :=
    tendstoInDistribution_grid_martingale_fdd hP hcoord hμ hPfin N hN hN2 hstat D hD hcov W hW m t ht
  have hdiff : TendstoInMeasure P (A - B) atTop 0 := by
    have h := (tendstoInMeasure_scaled_finite_dimensional_remainder hP hX φ hφ hL2
      N hN2 hstat hrem t).comp tendsto_gridScale
    refine TendstoInMeasure.congr ?_ EventuallyEq.rfl h
    intro n
    filter_upwards with η
    funext j i
    simp only [Function.comp_apply, A, B, Pi.sub_apply]
  have hA (n : ℕ) : AEMeasurable (A n) P := by
    apply Measurable.aemeasurable
    apply measurable_pi_iff.mpr
    intro j
    have hc : Continuous (fun γ : Path d => gridScale n •
        γ (((gridScale n)⁻¹ ^ 2).toNNReal * t j)) :=
      (continuous_eval_const _).const_smul (gridScale n)
    exact hc.measurable.comp hX.version_measurable
  exact tendstoInDistribution_of_tendstoInMeasure_sub A Z hB hdiff hA

end EinsteinFull.External.DFGW
