import EinsteinRelation.Probability.AnalyticGraph
import EinsteinRelation.Correctors.BorelKernelSpaces
import EinsteinRelation.Correctors.HeatKernelPositiveCongruence
import EinsteinRelation.Correctors.AKMHeatKernelCoefficientCongruence
import EinsteinRelation.Environment.AKMReconstructionAgreement
import EinsteinRelation.Correctors.AKMLocalCorrectorSpecialization

/-! # Unique E.1 kernel selection from an analytic graph

Source: `paper/main.tex:693–698,777–784,842`. The graph uses actual
E.1 kernels on continuous normalized elliptic coefficients. Its sections
are singletons by the proved kernel uniqueness theorem. Analyticity is
an explicit internal obligation, rather than an external literature input.
-/

open MeasureTheory
open scoped Topology

noncomputable section

namespace EinsteinRelation.Correctors.BorelKernel
open External.AKM Environment.AKMTestIntegralSupport

local instance {d : ℕ} : PolishSpace (CoefficientField d) :=
  Localization.coefficientField_polish d

/-- The exact E.1 graph, in the compact-open continuous kernel space.
Source: `paper/main.tex:777–784,842`; AKM Proposition E.1. -/
def kernelGraph {d : ℕ} {K : ℝ} (C : ℝ → ℝ)
    (A : ContinuousCoefficient d K) (P : ContinuousKernel d) : Prop :=
  ∃ (X Y : ℝ → Vec d → Vec d → Vec d)
    (H : ℝ → Vec d → Vec d → Mat d),
    HeatKernelProperties (toCoefficient A) (extendKernel P) X Y H C

/-- Every E.1 kernel gives a point of the continuous-kernel graph.
Source: `paper/main.tex:777–784,842`. -/
theorem kernelGraph_nonempty {d : ℕ} {K : ℝ} {C : ℝ → ℝ}
    (hex : ∀ A : Coefficient d K,
      ∃ (P : ℝ → Vec d → Vec d → ℝ)
        (X Y : ℝ → Vec d → Vec d → Vec d)
        (H : ℝ → Vec d → Vec d → Mat d), HeatKernelProperties A P X Y H C)
    (A : ContinuousCoefficient d K) : ∃ P, kernelGraph C A P := by
  obtain ⟨P, X, Y, H, hP⟩ := hex (toCoefficient A)
  let p : ContinuousKernel d := ⟨fun z => P z.1.1 z.2.1 z.2.2,
    hP.1.comp_continuous
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
      (fun z => ⟨z.1.2, Set.mem_univ _⟩)⟩
  refine ⟨p, X, Y, H, heatKernelProperties_congr_positive hP ?_⟩
  intro t ht x y
  exact (extendKernel_pos p t ht x y).symm

/-- Kernel uniqueness gives singleton graph sections, for the actual E.1
predicate rather than a renamed uniqueness assumption.
Source: `paper/main.tex:777–784,842`; AKM Proposition E.1. -/
theorem kernelGraph_unique {d : ℕ} {K : ℝ} (hK : 0 < K) {C : ℝ → ℝ}
    (A : ContinuousCoefficient d K) {P Q : ContinuousKernel d}
    (hP : kernelGraph C A P) (hQ : kernelGraph C A Q) : P = Q := by
  obtain ⟨X₁, Y₁, H₁, hP⟩ := hP
  obtain ⟨X₂, Y₂, H₂, hQ⟩ := hQ
  ext z
  exact (extendKernel_pos P z.1.1 z.1.2 z.2.1 z.2.2).symm.trans
    ((akm_heatKernel_unique hK hP hQ z.1.1 z.1.2 z.2.1 z.2.2).trans
      (extendKernel_pos Q z.1.1 z.1.2 z.2.1 z.2.2))

/-- Analyticity of the E.1 graph suffices for a measurable continuous
kernel family on normalized continuous coefficients.
Source: `paper/main.tex:777–784,842`. -/
theorem exists_measurable_kernel_of_analytic_graph {d : ℕ} {K : ℝ}
    (hK : 0 < K) (C : ℝ → ℝ)
    (hex : ∀ A : Coefficient d K,
      ∃ (P : ℝ → Vec d → Vec d → ℝ)
        (X Y : ℝ → Vec d → Vec d → Vec d)
        (H : ℝ → Vec d → Vec d → Mat d), HeatKernelProperties A P X Y H C)
    (hgraph : AnalyticSet {z : ContinuousCoefficient d K × ContinuousKernel d |
      kernelGraph C z.1 z.2}) :
    ∃ P : ContinuousCoefficient d K → ContinuousKernel d,
      Measurable P ∧ ∀ A, kernelGraph C A (P A) := by
  apply Probability.exists_measurable_of_analytic_unique (kernelGraph C) hgraph
  intro A
  obtain ⟨P, hP⟩ := kernelGraph_nonempty hex A
  exact ⟨P, hP, fun Q hQ => kernelGraph_unique hK A hQ hP⟩

/-- The continuous normalized carrier is nonempty throughout the source
parameter range. Source: `paper/main.tex:693–698`; AKM (0.6). -/
theorem continuousCoefficient_nonempty (d : ℕ) {K : ℝ} (hK : 1 ≤ K) :
    Nonempty (ContinuousCoefficient d K) := by
  refine ⟨⟨ContinuousMap.const (Vec d) (1 : Mat d), ?_, ?_⟩⟩
  · intro x
    simp only [ContinuousMap.const_apply, Matrix.transpose_one]
  · intro x ξ
    simp only [ContinuousMap.const_apply, Matrix.one_mulVec]
    exact ⟨le_rfl, le_mul_of_one_le_left (euclideanSq_nonneg_coords ξ) hK⟩

/-- The continuous normalized representative can be extended measurably
from the continuous-coefficient subtype to the full observation carrier.
It agrees exactly with every continuous raw coefficient.
Source: `paper/main.tex:693–698`; AKM (0.11). -/
theorem exists_measurable_coefficient_reconstruction {d : ℕ} {K : ℝ}
    (hK : 1 ≤ K) :
    ∃ R : Coefficient d K → ContinuousCoefficient d K, Measurable R ∧
      ∀ (A : Coefficient d K) (hA : Continuous A.field),
        (R A).1 = (⟨A.field, hA⟩ : CoefficientField d) := by
  letI : Nonempty (ContinuousCoefficient d K) := continuousCoefficient_nonempty d hK
  let F : {A : Coefficient d K // Continuous A.field} → ContinuousCoefficient d K :=
    fun A => ⟨⟨A.1.field, A.2⟩, A.1.symmetric, A.1.elliptic⟩
  have hF : Measurable F :=
    (measurable_continuous_field_of_akm_observations (d := d) (K := K)).subtype_mk
  obtain ⟨R, hR, heq⟩ := hF.exists_eq_measurable_comp
  refine ⟨R, hR, fun A hA => ?_⟩
  exact congrArg Subtype.val (congrFun heq (⟨A, hA⟩ :
    {A : Coefficient d K // Continuous A.field})).symm

/-- The analytic-graph route supplies exactly the jointly measurable
scalar-kernel premise used in the paper's final chain. No measurability
of the raw pointwise coefficient evaluation is assumed.
Source: `paper/main.tex:693–698,777–784,842`. -/
theorem actualLaw_measurable_kernel_of_analytic_graph
    {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀)
    (C : ℝ → ℝ)
    (hex : ∀ A : Coefficient d (AKMUpperEllipticity L),
      ∃ (P : ℝ → Vec d → Vec d → ℝ)
        (X Y : ℝ → Vec d → Vec d → Vec d)
        (H : ℝ → Vec d → Vec d → Mat d), HeatKernelProperties A P X Y H C)
    (hgraph : AnalyticSet
      {z : ContinuousCoefficient d (AKMUpperEllipticity L) × ContinuousKernel d |
        kernelGraph C z.1 z.2}) :
    ∃ P : Coefficient d (AKMUpperEllipticity L) → ℝ → Vec d → Vec d → ℝ,
      Measurable (fun z :
        (Coefficient d (AKMUpperEllipticity L) × (ℝ × Vec d)) × Vec d =>
        P z.1.1 z.1.2.1 z.1.2.2 z.2) ∧
      ∀ᵐ A ∂actualCoefficientLaw Q,
        ∃ (X Y : ℝ → Vec d → Vec d → Vec d)
          (H : ℝ → Vec d → Vec d → Mat d), HeatKernelProperties A (P A) X Y H C := by
  have hK := one_lt_AKMUpperEllipticity Q.ellipticity_parameter
  obtain ⟨R, hR, hReq⟩ := exists_measurable_coefficient_reconstruction (d := d) hK.le
  obtain ⟨p, hp, hpG⟩ := exists_measurable_kernel_of_analytic_graph
    (zero_lt_one.trans hK) C hex hgraph
  refine ⟨fun A => extendKernel (p (R A)), ?_, ?_⟩
  · exact (measurable_extendKernel d).comp
      (((hp.comp hR).comp measurable_fst.fst).prodMk
        (measurable_fst.snd.fst.prodMk (measurable_fst.snd.snd.prodMk measurable_snd)))
  · have heq := ae_actualCoefficientLaw_field_eq_reconstruction Q
      (fun A => (R A).1) (measurable_subtype_coe.comp hR) hReq
    filter_upwards [heq] with A hA
    obtain ⟨X, Y, H, hP⟩ := hpG (R A)
    exact ⟨X, Y, H, heatKernelProperties_congr_coefficient_ae hA.symm hP⟩

/-- Frozen E.1 existence, together with the remaining analytic-graph
obligation, gives the entire measurable-kernel interface, including the
single constant function chosen before the coefficient and environment.
Source: `paper/main.tex:777–784,842`. -/
theorem measurableKernelHypothesis_of_analytic_graph
    (hE : ParabolicHeatKernel)
    (hgraph : ∀ (d : ℕ), 2 ≤ d → ∀ (K : ℝ), 1 < K → ∀ C : ℝ → ℝ,
      (∀ A : Coefficient d K,
        ∃ (P : ℝ → Vec d → Vec d → ℝ)
          (X Y : ℝ → Vec d → Vec d → Vec d)
          (H : ℝ → Vec d → Vec d → Mat d), HeatKernelProperties A P X Y H C) →
      AnalyticSet {z : ContinuousCoefficient d K × ContinuousKernel d |
        kernelGraph C z.1 z.2}) :
    ∀ (d : ℕ) [Fact (2 ≤ d)] (L r₀ : ℝ) (Q : EnvironmentLaw d L r₀),
      ∃ (CK : ℝ → ℝ)
        (P : Coefficient d (AKMUpperEllipticity L) → ℝ → Vec d → Vec d → ℝ),
        (∀ α, 0 < α → α < (AKMUpperEllipticity L)⁻¹ → 0 < CK α) ∧
        Measurable (fun z :
          (Coefficient d (AKMUpperEllipticity L) × (ℝ × Vec d)) × Vec d =>
          P z.1.1 z.1.2.1 z.1.2.2 z.2) ∧
        ∀ᵐ A ∂actualCoefficientLaw Q,
          ∃ (X Y : ℝ → Vec d → Vec d → Vec d)
            (H : ℝ → Vec d → Vec d → Mat d), HeatKernelProperties A (P A) X Y H CK := by
  intro d hd L r₀ Q
  have hK := one_lt_AKMUpperEllipticity Q.ellipticity_parameter
  obtain ⟨C, hC, hex⟩ := hE d hd.out (AKMUpperEllipticity L) hK
  obtain ⟨P, hPm, hP⟩ := actualLaw_measurable_kernel_of_analytic_graph Q C hex
    (hgraph d hd.out (AKMUpperEllipticity L) hK C hex)
  exact ⟨C, P, hC, hPm, hP⟩

end EinsteinRelation.Correctors.BorelKernel
