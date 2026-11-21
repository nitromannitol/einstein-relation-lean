import EinsteinFull.External.DFGW.GridBrownianFDD
import EinsteinFull.External.DFGW.ScaledTimePerturbation
import EinsteinFull.External.DFGW.GridInterpolation

/-! # Finite-dimensional Brownian limits at arbitrary scales

Bounded time changes interpolate the grid-scale martingale limit to arbitrary positive
scales, and the martingale approximation transfers it to the original process.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation Filter
open scoped NNReal ENNReal Topology BigOperators

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {d : ℕ} {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- Finite-dimensional martingale limits on the unit interval hold at arbitrary scales. -/
theorem tendstoInDistribution_scaled_martingale_fdd
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
    TendstoInDistribution (fun (ε : ℝ) η j => ε •
      N ((ε⁻¹ ^ 2).toNNReal * t j) η) (𝓝[>] 0)
      (fun γ : Path d => fun j => γ (t j)) (fun _ => P) W := by
  let : IsProbabilityMeasure P := hP.probability
  let : IsProbabilityMeasure W := hW.1
  let a (ε : ℝ) : ℝ≥0 := (ε⁻¹ ^ 2).toNNReal
  let A : ℝ → C(ℝ, S) → Fin m → Vec d := fun ε η j => ε • N (a ε * t j) η
  let B : ℝ → C(ℝ, S) → Fin m → Vec d := fun ε η j => ε • N (floorTime (a ε) * t j) η
  let Z : Path d → Fin m → Vec d := fun γ j => γ (t j)
  have hgrid := tendstoInDistribution_grid_martingale_fdd
    hP hcoord hμ hPfin N hN hN2 hstat D hD hcov W hW m t ht
  have hBmeas (ε : ℝ) : AEMeasurable (B ε) P := by
    apply Measurable.aemeasurable
    apply measurable_pi_iff.mpr
    intro j
    have hm := (hN.stronglyAdapted (floorTime (a ε) * t j)).mono (Draft.dfgwPast.le _)
    exact (hm.const_smul ε).measurable
  have hB : TendstoInDistribution B (𝓝[>] 0) Z (fun _ => P) W :=
    tendstoInDistribution_floor_grid_parameter N t Z hgrid hBmeas
  have hdiff : TendstoInMeasure P (A - B) (𝓝[>] 0) 0 := by
    have h := tendstoInMeasure_scaled_martingale_finite_time_perturbation hP N hN hN2 hstat
      (fun ε j => a ε * t j) (fun ε j => floorTime (a ε) * t j) 1
      (fun ε j => by
        gcongr
        exact (floorTime_le_and_sub_le_one (a ε)).1)
      (fun ε j => by
        rw [← tsub_mul]
        have hmul : (a ε - floorTime (a ε)) * t j ≤ 1 := by
          calc
            _ ≤ 1 * t j := by
              gcongr
              exact (floorTime_le_and_sub_le_one (a ε)).2
            _ ≤ 1 := by simpa only [one_mul] using ht j
        exact_mod_cast hmul)
    refine TendstoInMeasure.congr ?_ EventuallyEq.rfl h
    intro ε
    apply ae_of_all P
    intro η
    funext j i
    simp only [A, B, Pi.sub_apply, Pi.smul_apply, smul_sub]
  have hA (ε : ℝ) : AEMeasurable (A ε) P := by
    apply Measurable.aemeasurable
    apply measurable_pi_iff.mpr
    intro j
    have hm := (hN.stronglyAdapted (a ε * t j)).mono (Draft.dfgwPast.le _)
    exact (hm.const_smul ε).measurable
  exact tendstoInDistribution_of_tendstoInMeasure_sub A Z hB hdiff hA

/-- Finite-dimensional limits for the increment process on the unit interval hold at
arbitrary positive scales. -/
theorem tendstoInDistribution_scaled_process_fdd
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
    TendstoInDistribution (fun (ε : ℝ) η j => ε •
      Y η ((ε⁻¹ ^ 2).toNNReal * t j)) (𝓝[>] 0)
      (fun γ : Path d => fun j => γ (t j)) (fun _ => P) W := by
  let : IsProbabilityMeasure P := hP.probability
  let : IsProbabilityMeasure W := hW.1
  have h := tendstoInDistribution_scaled_martingale_fdd hP hcoord hμ hPfin N hN hN2 hstat
    D hD hcov W hW m t ht
  exact tendstoInDistribution_scaled_finite_dimensional_of_martingale hP hX φ hφ hL2
    N hN2 hstat hrem t (fun (γ : Path d) j => γ (t j)) h

end EinsteinFull.External.DFGW
