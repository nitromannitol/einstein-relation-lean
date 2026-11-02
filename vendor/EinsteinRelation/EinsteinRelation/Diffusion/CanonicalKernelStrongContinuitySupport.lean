import EinsteinRelation.Diffusion.KernelL2ActionSupport
import EinsteinRelation.External.GantertSection7Support
import EinsteinRelation.SpatialDirichlet.PhysicalResolventSupport

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped ENNReal NNReal InnerProductSpace Topology

namespace EinsteinRelation.Diffusion

open EinsteinRelation.External.GantertSection7Support
open EinsteinRelation.SpatialDirichlet
open EinsteinRelation.WeightedKernelL2

theorem physicalReversibleMeasure_eq_sourceDensity
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam : ℝ) :
    physicalReversibleMeasure ω hd lam =
      densityWeightedMeasure (sourcePhysicalDensity ω hd lam) := by
  rfl

theorem physicalReversibleMeasure_sigmaFinite
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam : ℝ) :
    SigmaFinite (physicalReversibleMeasure ω hd lam) := by
  rw [physicalReversibleMeasure_eq_sourceDensity]
  letI : IsLocallyFiniteMeasure
      (densityWeightedMeasure (sourcePhysicalDensity ω hd lam)) :=
    densityWeightedMeasure_locallyFinite _ (continuousSourcePhysicalDensity ω hd lam)
  infer_instance

end EinsteinRelation.Diffusion

namespace EinsteinRelation.External.GantertSection7Support.GantertFixedEnvironmentRealization

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped ENNReal NNReal InnerProductSpace Topology
open EinsteinRelation.Diffusion
open EinsteinRelation.External.GantertSection7Support
open EinsteinRelation.SpatialDirichlet
open EinsteinRelation.WeightedKernelL2

/-- Detailed balance in the genuine fixed-environment record makes its actual transition
kernel invariant for the source physical reversible measure. -/
theorem transitionKernel_invariant
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ : ℝ} (hΛ₀ : 1 ≤ Λ₀)
    {ω : FieldPair d} {hω : IsRegular Λ₀ ω} {lam : ℝ}
    {hlam : 0 ≤ lam} {hlam_le_one : lam ≤ 1}
    (R : GantertFixedEnvironmentRealization hd Λ₀ hΛ₀ ω hω lam hlam hlam_le_one)
    (t : ℝ≥0) :
    Kernel.Invariant (R.transitionKernel t) (physicalReversibleMeasure ω hd lam) := by
  letI : IsMarkovKernel (R.transitionKernel t) := R.transitionKernel_isMarkovKernel t
  exact Kernel.IsReversible.invariant (by
    intro A B hA hB
    exact R.transitionKernel_reversible t A B hA hB)

end EinsteinRelation.External.GantertSection7Support.GantertFixedEnvironmentRealization

namespace EinsteinRelation.Diffusion

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped ENNReal NNReal InnerProductSpace Topology
open EinsteinRelation.External.GantertSection7Support
open EinsteinRelation.SpatialDirichlet
open EinsteinRelation.WeightedKernelL2

/-- The induced L² kernel action respects subtraction. This is the representative-level
linearity needed to extend continuity from a dense range. -/
theorem kernelIntegralL2_sub {α : Type*} [MeasurableSpace α]
    {K : Kernel α α} [IsMarkovKernel K] {m : Measure α} [SigmaFinite m]
    (hInv : Kernel.Invariant K m) (f g : Lp ℝ 2 m) :
    kernelIntegralL2 hInv (f - g) = kernelIntegralL2 hInv f - kernelIntegralL2 hInv g := by
  have hfSq : Integrable (fun x => f x ^ 2) m := (Lp.memLp f).integrable_sq
  have hgSq : Integrable (fun x => g x ^ 2) m := (Lp.memLp g).integrable_sq
  have hfSqBind : Integrable (fun x => f x ^ 2) (Measure.bind m K) := by
    rw [hInv.def]
    exact hfSq
  have hgSqBind : Integrable (fun x => g x ^ 2) (Measure.bind m K) := by
    rw [hInv.def]
    exact hgSq
  have hfSqSm : AEStronglyMeasurable (fun x => f x ^ 2) (Measure.bind m K) := by
    rw [hInv.def]
    exact hfSq.aestronglyMeasurable
  have hgSqSm : AEStronglyMeasurable (fun x => g x ^ 2) (Measure.bind m K) := by
    rw [hInv.def]
    exact hgSq.aestronglyMeasurable
  have hfParts := (Measure.integrable_comp_iff (κ := K) (μ := m) hfSqSm).1 hfSqBind
  have hgParts := (Measure.integrable_comp_iff (κ := K) (μ := m) hgSqSm).1 hgSqBind
  have hpoint : kernelIntegral K (f - g) =ᵐ[m]
      fun x => kernelIntegral K f x - kernelIntegral K g x := by
    filter_upwards [hfParts.1, hgParts.1] with x hfx hgx
    letI : IsProbabilityMeasure (K x) := inferInstance
    have hfm : MemLp f 2 (K x) :=
      (memLp_two_iff_integrable_sq (Lp.stronglyMeasurable f).aestronglyMeasurable).2 hfx
    have hgm : MemLp g 2 (K x) :=
      (memLp_two_iff_integrable_sq (Lp.stronglyMeasurable g).aestronglyMeasurable).2 hgx
    have hfi : Integrable f (K x) :=
      memLp_one_iff_integrable.mp (hfm.mono_exponent (by norm_num))
    have hgi : Integrable g (K x) :=
      memLp_one_iff_integrable.mp (hgm.mono_exponent (by norm_num))
    change (∫ y, (f y - g y) ∂K x) =
      (∫ y, f y ∂K x) - (∫ y, g y ∂K x)
    rw [integral_sub hfi hgi]
  apply Lp.ext
  have hleft := kernelIntegralL2_coe hInv (f - g)
  have hrightF := kernelIntegralL2_coe hInv f
  have hrightG := kernelIntegralL2_coe hInv g
  have hinputSub := Lp.coeFn_sub f g
  have hKinputSub := kernelIntegral_ae_congr hInv hinputSub
  have hrightSub := Lp.coeFn_sub (kernelIntegralL2 hInv f) (kernelIntegralL2 hInv g)
  filter_upwards [hleft, hrightF, hrightG, hpoint, hKinputSub, hrightSub]
    with x hxL hxF hxG hxSub hxKSub hxR
  rw [hxL, hxKSub, hxSub, ← hxF, ← hxG]
  exact hxR.symm

private theorem kernelIntegralL2_form_difference_identity
    {α : Type*} [MeasurableSpace α] {K : Kernel α α} [IsMarkovKernel K]
    {m : Measure α} [SigmaFinite m] (hInv : Kernel.Invariant K m)
    (t : ℝ≥0) (f : α → ℝ) (hf : MemLp f 2 m) :
    (1 / (t : ℝ)) * ∫ x, (f x - kernelIntegral K f x) * f x ∂m =
      (1 / (t : ℝ)) *
        (‖hf.toLp f‖ ^ 2 -
          inner ℝ (kernelIntegralL2 hInv (hf.toLp f)) (hf.toLp f)) := by
  let fL2 : Lp ℝ 2 m := hf.toLp f
  have hfRep : fL2 =ᵐ[m] f := hf.coeFn_toLp
  have hKmem : MemLp (kernelIntegral K fL2) 2 m :=
    kernelIntegral_memLp hInv (Lp.stronglyMeasurable fL2) (Lp.memLp fL2)
  have hKRep := kernelIntegral_ae_congr hInv hfRep
  have hActionRep : kernelIntegralL2 hInv fL2 =ᵐ[m] kernelIntegral K f :=
    (kernelIntegralL2_coe hInv fL2).trans hKRep
  have hfProduct : Integrable (fun x => fL2 x * fL2 x) m :=
    (Lp.memLp fL2).integrable_mul (Lp.memLp fL2)
  have hKProduct : Integrable (fun x => kernelIntegral K fL2 x * fL2 x) m :=
    hKmem.integrable_mul (Lp.memLp fL2)
  have hNum :
      ∫ x, (f x - kernelIntegral K f x) * f x ∂m =
        ‖fL2‖ ^ 2 - inner ℝ (kernelIntegralL2 hInv fL2) fL2 := by
    have hAE : (fun x => (f x - kernelIntegral K f x) * f x) =ᵐ[m]
        fun x => fL2 x * fL2 x - kernelIntegral K fL2 x * fL2 x := by
      filter_upwards [hfRep, hKRep] with x hx hk
      rw [← hx, ← hk]
      ring
    calc
      ∫ x, (f x - kernelIntegral K f x) * f x ∂m =
          ∫ x, (fL2 x * fL2 x - kernelIntegral K fL2 x * fL2 x) ∂m :=
        integral_congr_ae hAE
      _ = ∫ x, fL2 x * fL2 x ∂m -
          ∫ x, kernelIntegral K fL2 x * fL2 x ∂m := integral_sub hfProduct hKProduct
      _ = ‖fL2‖ ^ 2 - inner ℝ (kernelIntegralL2 hInv fL2) fL2 := by
        have hnormIntegral :
            ∫ x, fL2 x * fL2 x ∂m = ‖fL2‖ ^ 2 := by
          calc
            ∫ x, fL2 x * fL2 x ∂m = ∫ x, ‖fL2 x‖ ^ 2 ∂m := by
              apply integral_congr_ae
              filter_upwards [] with x
              simp [Real.norm_eq_abs, pow_two]
            _ = ‖fL2‖ ^ 2 := (l2_norm_sq_eq_integral_norm_sq fL2).symm
        have hinner : inner ℝ (kernelIntegralL2 hInv fL2) fL2 =
            ∫ x, kernelIntegral K fL2 x * fL2 x ∂m := by
          rw [L2.inner_def]
          apply integral_congr_ae
          filter_upwards [kernelIntegralL2_coe hInv fL2] with x hx
          rw [hx]
          simp
          ring
        rw [hnormIntegral, hinner]
  rw [hNum]

private theorem kernelIntegralL2_norm_difference_sq_le_form
    {α : Type*} [MeasurableSpace α] {K : Kernel α α} [IsMarkovKernel K]
    {m : Measure α} [SigmaFinite m] (hInv : Kernel.Invariant K m)
    (t : ℝ≥0) (ht : 0 < (t : ℝ)) (f : α → ℝ) (hf : MemLp f 2 m) :
    ‖kernelIntegralL2 hInv (hf.toLp f) - hf.toLp f‖ ^ 2 ≤
      2 * (t : ℝ) *
        ((1 / (t : ℝ)) * ∫ x, (f x - kernelIntegral K f x) * f x ∂m) := by
  let fL2 : Lp ℝ 2 m := hf.toLp f
  have hcontract := kernelIntegralL2_norm_le hInv fL2
  have hnormSq :
      ‖kernelIntegralL2 hInv fL2‖ ^ 2 ≤ ‖fL2‖ ^ 2 := by
    have hnonnegT := norm_nonneg (kernelIntegralL2 hInv fL2)
    have hnonnegF := norm_nonneg fL2
    nlinarith
  have hdiff :
      ‖kernelIntegralL2 hInv fL2 - fL2‖ ^ 2 ≤
        2 * (‖fL2‖ ^ 2 - inner ℝ (kernelIntegralL2 hInv fL2) fL2) := by
    rw [norm_sub_sq_real]
    nlinarith
  calc
    ‖kernelIntegralL2 hInv (hf.toLp f) - hf.toLp f‖ ^ 2 =
        ‖kernelIntegralL2 hInv fL2 - fL2‖ ^ 2 := by rfl
    _ ≤ 2 * (‖fL2‖ ^ 2 - inner ℝ (kernelIntegralL2 hInv fL2) fL2) := hdiff
    _ = 2 * (t : ℝ) *
        ((1 / (t : ℝ)) *
          (‖fL2‖ ^ 2 - inner ℝ (kernelIntegralL2 hInv fL2) fL2)) := by
      field_simp [ne_of_gt ht]
    _ = 2 * (t : ℝ) *
        ((1 / (t : ℝ)) * ∫ x, (f x - kernelIntegral K f x) * f x ∂m) := by
      rw [← kernelIntegralL2_form_difference_identity hInv t f hf]

end EinsteinRelation.Diffusion

namespace EinsteinRelation.External.GantertSection7Support.GantertFixedEnvironmentRealization

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped ENNReal NNReal InnerProductSpace Topology
open EinsteinRelation.Diffusion
open EinsteinRelation.External.GantertSection7Support
open EinsteinRelation.SpatialDirichlet
open EinsteinRelation.WeightedKernelL2

/-- The actual kernel action on the physical reversible L² space of a genuine fixed-environment
GMP realization, induced by the generic kernel integral action. -/
noncomputable def kernelL2Action
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ : ℝ} (hΛ₀ : 1 ≤ Λ₀)
    {ω : FieldPair d} {hω : IsRegular Λ₀ ω} {lam : ℝ}
    {hlam : 0 ≤ lam} {hlam_le_one : lam ≤ 1}
    (R : GantertFixedEnvironmentRealization hd Λ₀ hΛ₀ ω hω lam hlam hlam_le_one)
    (t : ℝ≥0)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    Lp ℝ 2 (physicalReversibleMeasure ω hd lam) := by
  letI : SigmaFinite (physicalReversibleMeasure ω hd lam) :=
    physicalReversibleMeasure_sigmaFinite hd ω lam
  letI : IsMarkovKernel (R.transitionKernel t) := R.transitionKernel_isMarkovKernel t
  exact kernelIntegralL2 (R.transitionKernel_invariant hd hΛ₀ t) f

theorem kernelL2Action_norm_le
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ : ℝ} (hΛ₀ : 1 ≤ Λ₀)
    {ω : FieldPair d} {hω : IsRegular Λ₀ ω} {lam : ℝ}
    {hlam : 0 ≤ lam} {hlam_le_one : lam ≤ 1}
    (R : GantertFixedEnvironmentRealization hd Λ₀ hΛ₀ ω hω lam hlam hlam_le_one)
    (t : ℝ≥0) (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    ‖R.kernelL2Action hd hΛ₀ t f‖ ≤ ‖f‖ := by
  letI : SigmaFinite (physicalReversibleMeasure ω hd lam) :=
    physicalReversibleMeasure_sigmaFinite hd ω lam
  letI : IsMarkovKernel (R.transitionKernel t) := R.transitionKernel_isMarkovKernel t
  exact kernelIntegralL2_norm_le (R.transitionKernel_invariant hd hΛ₀ t) f

theorem kernelL2Action_sub
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ : ℝ} (hΛ₀ : 1 ≤ Λ₀)
    {ω : FieldPair d} {hω : IsRegular Λ₀ ω} {lam : ℝ}
    {hlam : 0 ≤ lam} {hlam_le_one : lam ≤ 1}
    (R : GantertFixedEnvironmentRealization hd Λ₀ hΛ₀ ω hω lam hlam hlam_le_one)
    (t : ℝ≥0) (f g : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    R.kernelL2Action hd hΛ₀ t (f - g) =
      R.kernelL2Action hd hΛ₀ t f - R.kernelL2Action hd hΛ₀ t g := by
  letI : SigmaFinite (physicalReversibleMeasure ω hd lam) :=
    physicalReversibleMeasure_sigmaFinite hd ω lam
  letI : IsMarkovKernel (R.transitionKernel t) := R.transitionKernel_isMarkovKernel t
  exact kernelIntegralL2_sub (R.transitionKernel_invariant hd hΛ₀ t) f g

/-- A finite short-time form limit and contraction imply strong continuity for the actual
fixed-environment kernel action on its physical reversible `L²` space. -/
private theorem kernelL2Action_tendsto_of_formLimit
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ : ℝ} (hΛ₀ : 1 ≤ Λ₀)
    (ω : FieldPair d) (hω : IsRegular Λ₀ ω)
    (lam : ℝ) (hlam : 0 ≤ lam) (hlam_le_one : lam ≤ 1)
    (R : GantertFixedEnvironmentRealization hd Λ₀ hΛ₀ ω hω lam hlam hlam_le_one)
    (f : Vec d → ℝ) (hf : MemLp f 2 (physicalReversibleMeasure ω hd lam))
    (E : ℝ)
    (hlimit : Tendsto
      (fun t : ℝ≥0 => semigroupFormDifferenceQuotient ω hd lam R.transitionKernel t f)
      (𝓝[Set.Ioi 0] (0 : ℝ≥0)) (𝓝 E)) :
    Tendsto
      (fun t : ℝ≥0 => R.kernelL2Action hd hΛ₀ t (hf.toLp f))
      (𝓝[Set.Ioi 0] (0 : ℝ≥0)) (𝓝 (hf.toLp f)) := by
  letI : SigmaFinite (physicalReversibleMeasure ω hd lam) :=
    physicalReversibleMeasure_sigmaFinite hd ω lam
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨δq, hδq, hclose⟩ :=
    (Metric.tendsto_nhdsWithin_nhds.mp hlimit) 1 zero_lt_one
  let B := 2 * (|E| + 1)
  have hB : 0 < B := by positivity
  let δε := ε ^ 2 / B
  have hδε : 0 < δε := div_pos (sq_pos_of_pos hε) hB
  let δ := min δq δε
  have hδ : 0 < δ := lt_min hδq hδε
  refine ⟨δ, hδ, ?_⟩
  intro t ht0 htδ
  have htδq : dist t (0 : ℝ≥0) < δq := lt_of_lt_of_le htδ (min_le_left _ _)
  have htδε : dist t (0 : ℝ≥0) < δε := lt_of_lt_of_le htδ (min_le_right _ _)
  have htDist : dist t (0 : ℝ≥0) = t := by simp [NNReal.dist_eq]
  have htSmall : (t : ℝ) < δε := by
    rw [htDist] at htδε
    exact_mod_cast htδε
  have hqclose := hclose ht0 htδq
  have hqBound :
      semigroupFormDifferenceQuotient ω hd lam R.transitionKernel t f ≤ |E| + 1 := by
    rw [Real.dist_eq] at hqclose
    have hdiff :
        semigroupFormDifferenceQuotient ω hd lam R.transitionKernel t f - E < 1 :=
      (abs_lt.mp hqclose).2
    have hE : E ≤ |E| := le_abs_self E
    linarith
  have htpos : 0 < (t : ℝ) := by exact_mod_cast ht0
  letI : IsMarkovKernel (R.transitionKernel t) := R.transitionKernel_isMarkovKernel t
  have hcore := kernelIntegralL2_norm_difference_sq_le_form
    (R.transitionKernel_invariant hd hΛ₀ t) t htpos f hf
  have hest :
      ‖R.kernelL2Action hd hΛ₀ t (hf.toLp f) - hf.toLp f‖ ^ 2 ≤
        2 * (t : ℝ) * semigroupFormDifferenceQuotient ω hd lam R.transitionKernel t f := by
    change ‖kernelIntegralL2 (R.transitionKernel_invariant hd hΛ₀ t) (hf.toLp f) -
      hf.toLp f‖ ^ 2 ≤ _
    exact hcore
  have hsq :
      ‖R.kernelL2Action hd hΛ₀ t (hf.toLp f) - hf.toLp f‖ ^ 2 ≤ B * (t : ℝ) := by
    calc
      _ ≤ 2 * (t : ℝ) *
          semigroupFormDifferenceQuotient ω hd lam R.transitionKernel t f := hest
      _ ≤ 2 * (t : ℝ) * (|E| + 1) :=
        mul_le_mul_of_nonneg_left hqBound (by positivity)
      _ = B * (t : ℝ) := by dsimp [B]; ring
  have hprod : B * (t : ℝ) < ε ^ 2 := by
    calc
      B * (t : ℝ) < B * δε := mul_lt_mul_of_pos_left htSmall hB
      _ = ε ^ 2 := by dsimp [δε]; field_simp
  have hnorm : ‖R.kernelL2Action hd hΛ₀ t (hf.toLp f) - hf.toLp f‖ < ε := by
    by_contra hnot
    have hεle : ε ≤ ‖R.kernelL2Action hd hΛ₀ t (hf.toLp f) - hf.toLp f‖ :=
      le_of_not_gt hnot
    nlinarith [sq_nonneg (‖R.kernelL2Action hd hΛ₀ t (hf.toLp f) - hf.toLp f‖ - ε)]
  simpa only [dist_eq_norm] using hnorm

/-- Every member of the full physical weighted `H¹` form domain has strong continuity for the
actual fixed-environment kernel action, by the exact closed-form value field of the realization. -/
theorem kernelL2Action_tendsto_fullPhysicalH1
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ : ℝ} (hΛ₀ : 1 ≤ Λ₀)
    (ω : FieldPair d) (hω : IsRegular Λ₀ ω)
    (lam : ℝ) (hlam : 0 ≤ lam) (hlam_le_one : lam ≤ 1)
    (R : GantertFixedEnvironmentRealization hd Λ₀ hΛ₀ ω hω lam hlam hlam_le_one)
    (f : Vec d → ℝ) (hf : MemLp f 2 (physicalReversibleMeasure ω hd lam))
    (q : DensityWeightedH1 (physicalForceWeight hd lam))
    (hq : densityWeightedH1Value (physicalForceWeight hd lam) q =ᵐ[
      physicalReversibleMeasure ω hd lam] f)
    (u : WeightedSobolevGraph (physicalForceMeasure hd lam))
    (hu : u.value =ᵐ[physicalReversibleMeasure ω hd lam] f) :
    Tendsto
      (fun t : ℝ≥0 => R.kernelL2Action hd hΛ₀ t
        (hf.toLp f))
      (𝓝[Set.Ioi 0] (0 : ℝ≥0))
      (𝓝 (hf.toLp f)) := by
  let E := physicalH1FormEnergy ω hd lam u
  apply kernelL2Action_tendsto_of_formLimit hd hΛ₀ ω hω lam hlam
    hlam_le_one R f hf E
  exact R.closedForm_value f q hq u hu

end EinsteinRelation.External.GantertSection7Support.GantertFixedEnvironmentRealization
