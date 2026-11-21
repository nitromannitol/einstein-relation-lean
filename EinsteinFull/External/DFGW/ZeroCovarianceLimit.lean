import EinsteinFull.External.DFGW.ZeroCovarianceFDD
import EinsteinFull.External.DFGW.DegenerateBrownian
import EinsteinFull.External.DFGW.SkorokhodFromMartingaleFDD

/-! # Zero-covariance limit under tightness

For a zero-covariance martingale approximation, tightness of the rescaled increment laws yields
the Brownian path limit.
-/

open MeasureTheory ProbabilityTheory Filter EinsteinRelation
open scoped NNReal Topology ENNReal

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {d : ℕ} {P : Measure C(ℝ, S)} [IsProbabilityMeasure P] {μ : Measure S}
variable {T : ℝ≥0 → Kernel S S} {X : ℝ → ℝ → C(ℝ, S) → Vec d}
variable {Y : C(ℝ, S) → Path d}

/-- A zero-covariance stationary martingale approximation gives the zero Brownian limit whenever
the scaled increment laws are tight. -/
theorem zero_covariance_limit_of_tight
    (hP : Draft.IsDFGWTrajectoryProcess P μ T) (hX : Draft.IsDFGWTrajectoryFamily P X Y)
    (φ : S → Vec d) (hφ : MemLp φ 2 μ)
    (hL2 : ∀ t, MemLp (compensated X φ t) 2 P)
    (N : ℝ≥0 → C(ℝ, S) → Vec d) (hN : Martingale N Draft.dfgwPast P)
    (hN2 : ∀ t, MemLp (N t) 2 P)
    (hstat : ∀ s t, (fun η => N (s + t) η - N s η) =ᵐ[P]
      fun η => N t (Draft.dfgwShift s η))
    (hcov : ∀ e : Vec d, dot e ((0 : Mat d).mulVec e) = ∫ η, dot e (N 1 η) ^ 2 ∂P)
    (hrem : ∀ e : Vec d, Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ *
      ∫ η, (dot e (X 0 t η) - dot e (N t η)) ^ 2 ∂P) atTop (𝓝 0))
    (htight : ∀ δ : ℝ, 0 < δ → ∃ K : Set (Path d), IsCompact K ∧
      (Measure.dirac (0 : Path d)) Kᶜ ≤ ENNReal.ofReal δ ∧ ∀ᶠ ε : ℝ in 𝓝[>] 0,
        (P.map fun η => rescalePath ε (Y η)) Kᶜ ≤ ENNReal.ofReal δ) :
    ∃ W : Measure (Path d), IsBrownianLaw (0 : Mat d) W ∧
      ∀ F : Draft.CadlagPath d → ℝ, Draft.IsSkorokhodTest F →
        Tendsto (fun ε : ℝ => ∫ η, F (Draft.Path.toCadlag (rescalePath ε (Y η))) ∂P)
          (𝓝[>] 0) (𝓝 (∫ γ, F (Draft.Path.toCadlag γ) ∂W)) := by
  refine ⟨Measure.dirac 0, isBrownianLaw_zero_dirac d, ?_⟩
  exact tendsto_skorokhod_of_martingale_fdd_of_tight hP hX φ hφ hL2 N hN2 hstat hrem
    (tendstoInDistribution_zero_covariance_martingale_fdd hP N hN hN2 hstat hcov) htight

end EinsteinFull.External.DFGW
