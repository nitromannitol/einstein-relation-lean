import EinsteinFull.External.DFGW.ZeroCovarianceMartingale
import EinsteinFull.External.DFGW.ContinuousPathConvergence
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

/-! # Finite-dimensional limits at zero covariance

The scaled finite-dimensional laws of a zero-covariance stationary-increment martingale are
identically concentrated on the zero path.
-/

open MeasureTheory ProbabilityTheory Filter EinsteinRelation MarkovProcess
open scoped NNReal Topology

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {d : ℕ} {P : Measure C(ℝ, S)} [IsProbabilityMeasure P] {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- The finite-dimensional distributions of a zero-covariance stationary-increment martingale
converge to those of the zero path. -/
theorem tendstoInDistribution_zero_covariance_martingale_fdd
    (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (N : ℝ≥0 → C(ℝ, S) → Vec d) (hN : Martingale N Draft.dfgwPast P)
    (hN2 : ∀ t, MemLp (N t) 2 P)
    (hstat : ∀ s t, (fun η => N (s + t) η - N s η) =ᵐ[P]
      fun η => N t (Draft.dfgwShift s η))
    (hcov : ∀ e : Vec d, dot e ((0 : Mat d).mulVec e) = ∫ η, dot e (N 1 η) ^ 2 ∂P)
    (I : Finset ℝ≥0) :
    TendstoInDistribution
      (fun (ε : ℝ) η (i : I) => ε • N ((ε⁻¹ ^ 2).toNNReal * i) η) (𝓝[>] 0)
      (fun γ : Path d => ContinuousPath.finsetEvaluation I γ) (fun _ => P)
      (Measure.dirac (0 : Path d)) := by
  have hmeas (ε : ℝ) : Measurable (fun η (i : I) =>
      ε • N ((ε⁻¹ ^ 2).toNNReal * i) η) := by
    apply measurable_pi_iff.2
    intro i
    exact ((hN.stronglyAdapted _).mono (Draft.dfgwPast.le _)).measurable.const_smul ε
  have hzero (ε : ℝ) : ∀ᵐ η ∂P, (fun i : I =>
      ε • N ((ε⁻¹ ^ 2).toNNReal * i) η) = 0 := by
    have hi (i : I) : ∀ᵐ η ∂P, N ((ε⁻¹ ^ 2).toNNReal * i) η = 0 :=
      stationary_martingale_ae_zero_of_zero_covariance hP N hN hN2 hstat hcov _
    filter_upwards [ae_all_iff.mpr hi] with η hη
    funext i
    rw [hη i]
    simp
  apply (tendstoInDistribution_iff_forall_integral_rclike_tendsto ℝ
    (fun ε => (hmeas ε).aemeasurable)
    (ContinuousPath.continuous_finiteEvaluation (fun i : I => (i : ℝ≥0))).measurable.aemeasurable).2
  intro f
  have hleft (ε : ℝ) : (∫ η, f (fun i : I =>
      ε • N ((ε⁻¹ ^ 2).toNNReal * i) η) ∂P) = f 0 := by
    calc
      _ = ∫ _η, f 0 ∂P := integral_congr_ae (hzero ε |>.mono fun η hη => by rw [hη])
      _ = _ := by simp
  have hright : (∫ γ, f (ContinuousPath.finsetEvaluation I γ)
      ∂Measure.dirac (0 : Path d)) = f 0 := by
    rw [integral_dirac]
    congr 1
  simpa only [hleft, hright] using tendsto_const_nhds (x := f 0)

end EinsteinFull.External.DFGW
