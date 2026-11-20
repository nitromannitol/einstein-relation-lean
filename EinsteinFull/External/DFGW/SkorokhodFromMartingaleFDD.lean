import EinsteinFull.External.DFGW.ContinuousPathConvergence
import EinsteinFull.External.DFGW.ScaledFiniteDimensionalTransfer

/-! # Skorokhod test convergence from martingale finite-dimensional limits

If the scaled martingale has the finite-dimensional laws of a candidate continuous-path limit,
and the scaled increment laws are tight, the increment laws converge against Skorokhod tests.
-/

open MeasureTheory ProbabilityTheory Filter EinsteinRelation MarkovProcess
open scoped NNReal Topology ENNReal

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {d : ℕ} {P : Measure C(ℝ, S)} [IsProbabilityMeasure P] {μ : Measure S}
variable {T : ℝ≥0 → Kernel S S} {X : ℝ → ℝ → C(ℝ, S) → Vec d}
variable {Y : C(ℝ, S) → Path d} {W : Measure (Path d)} [IsProbabilityMeasure W]

/-- Martingale finite-dimensional convergence and tightness of the scaled continuous increment
laws imply the Skorokhod-test conclusion. -/
theorem tendsto_skorokhod_of_martingale_fdd_of_tight
    (hP : Draft.IsDFGWTrajectoryProcess P μ T) (hX : Draft.IsDFGWTrajectoryFamily P X Y)
    (φ : S → Vec d) (hφ : MemLp φ 2 μ)
    (hL2 : ∀ t, MemLp (compensated X φ t) 2 P)
    (N : ℝ≥0 → C(ℝ, S) → Vec d) (hN2 : ∀ t, MemLp (N t) 2 P)
    (hstat : ∀ s t, (fun η => N (s + t) η - N s η) =ᵐ[P]
      fun η => N t (Draft.dfgwShift s η))
    (hrem : ∀ e : Vec d, Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ *
      ∫ η, (dot e (X 0 t η) - dot e (N t η)) ^ 2 ∂P) atTop (𝓝 0))
    (hfd : ∀ I : Finset ℝ≥0, TendstoInDistribution
      (fun (ε : ℝ) η (i : I) => ε • N ((ε⁻¹ ^ 2).toNNReal * i) η) (𝓝[>] 0)
      (fun γ : Path d => ContinuousPath.finsetEvaluation I γ) (fun _ => P) W)
    (htight : ∀ δ : ℝ, 0 < δ → ∃ K : Set (Path d), IsCompact K ∧
      W Kᶜ ≤ ENNReal.ofReal δ ∧ ∀ᶠ ε : ℝ in 𝓝[>] 0,
        (P.map fun η => rescalePath ε (Y η)) Kᶜ ≤ ENNReal.ofReal δ) :
    ∀ F : Draft.CadlagPath d → ℝ, Draft.IsSkorokhodTest F →
      Tendsto (fun ε : ℝ => ∫ η, F (Draft.Path.toCadlag (rescalePath ε (Y η))) ∂P)
        (𝓝[>] 0) (𝓝 (∫ γ, F (Draft.Path.toCadlag γ) ∂W)) := by
  have hresc (ε : ℝ) : Measurable (fun η => rescalePath ε (Y η)) := by
    apply ContinuousMap.measurable_iff_eval.2
    intro t
    exact ((continuous_eval_const _).measurable.comp hX.version_measurable).const_smul ε
  let Q : ℝ → ProbabilityMeasure (Path d) := fun ε =>
    ⟨P.map (fun η => rescalePath ε (Y η)),
      (Measure.isProbabilityMeasure_map_iff (hresc ε).aemeasurable).2 inferInstance⟩
  let W' : ProbabilityMeasure (Path d) := ⟨W, inferInstance⟩
  have hT : ∀ δ : ℝ, 0 < δ → ∃ K : Set (Path d), IsCompact K ∧
      (W' : Measure (Path d)) Kᶜ ≤ ENNReal.ofReal δ ∧
      ∀ᶠ ε in 𝓝[>] 0, (Q ε : Measure (Path d)) Kᶜ ≤ ENNReal.ofReal δ := htight
  have hFD (I : Finset ℝ≥0) (g : BoundedContinuousFunction (I → Vec d) ℝ) :
      Tendsto (fun ε => ∫ γ, g (ContinuousPath.finsetEvaluation I γ) ∂(Q ε : Measure (Path d)))
        (𝓝[>] 0) (𝓝 (∫ γ, g (ContinuousPath.finsetEvaluation I γ) ∂(W' : Measure (Path d)))) := by
    have hconv := tendstoInDistribution_scaled_finite_dimensional_of_martingale
      hP hX φ hφ hL2 N hN2 hstat hrem (fun i : I => (i : ℝ≥0))
      (fun γ : Path d => ContinuousPath.finsetEvaluation I γ) (hfd I)
    have htest := (tendstoInDistribution_iff_forall_integral_rclike_tendsto ℝ
      hconv.forall_aemeasurable hconv.aemeasurable_limit).1 hconv g
    apply htest.congr'
    filter_upwards with ε
    change (∫ η, g (fun i : I => ε • Y η ((ε⁻¹ ^ 2).toNNReal * i)) ∂P) =
      ∫ γ, g (ContinuousPath.finsetEvaluation I γ) ∂P.map (fun η => rescalePath ε (Y η))
    rw [integral_map (hresc ε).aemeasurable]
    · rfl
    · exact (g.continuous.comp (ContinuousPath.continuous_finiteEvaluation _)).aestronglyMeasurable
  have hpath (G : BoundedContinuousFunction (Path d) ℝ) :
      Tendsto (fun ε : ℝ => ∫ η, G (rescalePath ε (Y η)) ∂P) (𝓝[>] 0)
        (𝓝 (∫ γ, G γ ∂W)) := by
    have h := tendsto_path_integral_of_tight_of_finiteDimensional Q W' hT hFD G
    apply h.congr'
    filter_upwards with ε
    change (∫ γ, G γ ∂P.map (fun η => rescalePath ε (Y η))) = _
    exact integral_map (hresc ε).aemeasurable G.continuous.aestronglyMeasurable
  exact tendsto_skorokhod_of_boundedContinuous hpath

end EinsteinFull.External.DFGW
