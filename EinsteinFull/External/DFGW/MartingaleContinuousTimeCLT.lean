import EinsteinFull.External.DFGW.MartingaleOneTimeCLT
import EinsteinFull.External.DFGW.DiffusiveGrid

/-! # Scalar martingale limits at arbitrary scales

Rounding time to the integer grid and adjusting the normalization extends the scalar martingale
central limit theorem to every positive diffusive scale.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation Filter
open scoped NNReal ENNReal Topology BigOperators

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {d : ℕ} {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- A projected stationary-increment martingale has its normal limit at arbitrary positive
diffusive scales. -/
theorem tendstoInDistribution_projected_martingale
    (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (hcoord : Draft.dfgwCoordSigma (S := S) Set.univ =
      Draft.dfgwTrajectoryMeasurableSpace (S := S))
    (hμ : μ Set.univ ≠ ⊤) (hPfin : P Set.univ ≠ ⊤)
    (N : ℝ≥0 → C(ℝ, S) → Vec d) (hN : Martingale N Draft.dfgwPast P)
    (hN2 : ∀ t, MemLp (N t) 2 P)
    (hstat : ∀ s t, (fun η => N (s + t) η - N s η) =ᵐ[P]
      fun η => N t (Draft.dfgwShift s η)) (e : Vec d) :
    letI : IsProbabilityMeasure P := hP.probability
    let σsq : ℝ≥0 := ⟨∫ η, dot e (N 1 η) ^ 2 ∂P,
      integral_nonneg fun _ => sq_nonneg _⟩
    TendstoInDistribution (fun (ε : ℝ) η => ε * dot e (N (ε⁻¹ ^ 2).toNNReal η))
      (𝓝[>] 0) (id : ℝ → ℝ) (fun _ => P) (gaussianReal 0 σsq) := by
  let : IsProbabilityMeasure P := hP.probability
  let σsq : ℝ≥0 := ⟨∫ η, dot e (N 1 η) ^ 2 ∂P, integral_nonneg fun _ => sq_nonneg _⟩
  let : IsProbabilityMeasure (gaussianReal 0 σsq) := instIsProbabilityMeasureGaussianReal 0 σsq
  let idx := diffusiveGridIndex
  let W : ℝ → C(ℝ, S) → ℝ := fun ε η => (Real.sqrt (idx ε + 1))⁻¹ *
    dot e (N ((idx ε + 1 : ℕ) : ℝ≥0) η)
  let q : ℝ → ℝ := fun ε => ε * Real.sqrt (idx ε + 1)
  let B : ℝ → C(ℝ, S) → ℝ := fun ε η => ε *
    dot e (N ((idx ε + 1 : ℕ) : ℝ≥0) η)
  let A : ℝ → C(ℝ, S) → ℝ := fun ε η => ε * dot e (N (ε⁻¹ ^ 2).toNNReal η)
  have hevent : ∀ᶠ ε in 𝓝[>] (0 : ℝ), idx ε + 1 = ⌊ε⁻¹ ^ 2⌋₊ := by
    filter_upwards [tendsto_diffusiveGridIndex.eventually (eventually_ge_atTop 1)] with ε hε
    dsimp only [idx, diffusiveGridIndex] at hε ⊢
    omega
  have hq : Tendsto q (𝓝[>] 0) (𝓝 1) := by
    apply tendsto_diffusiveFloor_sqrt.congr'
    filter_upwards [hevent] with ε hε
    have hcast : (⌊ε⁻¹ ^ 2⌋₊ : ℝ) = (idx ε : ℝ) + 1 := by exact_mod_cast hε.symm
    simp only [q, hcast]
  have hqmeasure : TendstoInMeasure P (fun ε _ => q ε) (𝓝[>] 0) (fun _ => 1) := by
    apply tendstoInMeasure_iff_dist.mpr
    intro δ hδ
    have hsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), dist (q ε) 1 < δ :=
      (Metric.tendsto_nhds.mp hq) δ hδ
    have hzero : ∀ᶠ ε in 𝓝[>] (0 : ℝ), P {η : C(ℝ, S) | δ ≤ dist (q ε) 1} = 0 := by
      filter_upwards [hsmall] with ε hε
      have hempty : {η : C(ℝ, S) | δ ≤ dist (q ε) 1} = ∅ := by
        ext η
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        exact not_le_of_gt hε
      rw [hempty, measure_empty]
    have heq : (fun ε => P {η : C(ℝ, S) | δ ≤ dist (q ε) 1}) =ᶠ[𝓝[>] (0 : ℝ)]
        fun _ => (0 : ℝ≥0∞) := hzero
    exact tendsto_const_nhds.congr' heq.symm
  have hseq := tendstoInDistribution_projected_martingale_grid hP hcoord hμ hPfin N hN hN2 hstat e
  have hW : TendstoInDistribution W (𝓝[>] 0) (id : ℝ → ℝ) (fun _ => P) (gaussianReal 0 σsq) := by
    refine ⟨fun ε => hseq.forall_aemeasurable (idx ε), hseq.aemeasurable_limit, ?_⟩
    exact hseq.tendsto.comp tendsto_diffusiveGridIndex
  have hprod := hW.continuous_comp_prodMk_of_tendstoInMeasure_const
    (g := fun z : ℝ × ℝ => z.1 * z.2) (by fun_prop) hqmeasure
      (fun _ => measurable_const.aemeasurable)
  have hB : TendstoInDistribution B (𝓝[>] 0) (id : ℝ → ℝ) (fun _ => P) (gaussianReal 0 σsq) := by
    apply TendstoInDistribution.congr (h := hprod) _ _
    · intro ε
      apply ae_of_all P
      intro η
      have hn : 0 < (idx ε + 1 : ℝ) := by positivity
      have hr : Real.sqrt (idx ε + 1) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hn)
      simp only [W, q, B]
      field_simp
    · exact ae_of_all _ fun x => by simp
  have hdiff : TendstoInMeasure P (A - B) (𝓝[>] 0) 0 := by
    have hr := tendstoInMeasure_martingale_rounding hP N hN hN2 hstat e
    apply TendstoInMeasure.congr' _ EventuallyEq.rfl hr
    filter_upwards [hevent] with ε hε
    apply ae_of_all P
    intro η
    have hfloor : floorTime (ε⁻¹ ^ 2).toNNReal = ((idx ε + 1 : ℕ) : ℝ≥0) := by
      simp only [floorTime, Real.coe_toNNReal _ (sq_nonneg _), hε]
    simp only [Pi.sub_apply, A, B, hfloor, dot, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
  have hA (ε : ℝ) : AEMeasurable (A ε) P := by
    let L : Vec d →L[ℝ] ℝ := ∑ i : Fin d, (e i) • ContinuousLinearMap.proj i
    have hL (v : Vec d) : L v = dot e v := by
      simp only [L, sum_apply, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul, dot]
    have h := ((hN2 (ε⁻¹ ^ 2).toNNReal).continuousLinearMap_comp L).const_mul ε
    simpa only [A, hL] using h.aestronglyMeasurable.aemeasurable
  exact tendstoInDistribution_of_tendstoInMeasure_sub A id hB hdiff hA

end EinsteinFull.External.DFGW
