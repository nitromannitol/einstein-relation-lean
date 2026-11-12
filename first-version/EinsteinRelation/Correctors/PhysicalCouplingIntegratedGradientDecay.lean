import EinsteinRelation.Correctors.PhysicalCouplingEnergyMomentDecay
import EinsteinRelation.Correctors.PairedSemigroupPositiveDissipation
import EinsteinRelation.Correctors.CutoffPlateauSpacetimeEnergy
import EinsteinRelation.Correctors.IntegratedGradientEnergyEnvelope
import EinsteinRelation.Correctors.IntegratedGradientMeasurability

/-! # Literal paired integrated gradients of a specified canonical flow

Source: `paper/main.tex:834–857`. The cutoff dissipation is restricted to
its plateau before time Cauchy–Schwarz. All integrability through time zero
comes from the actual paired energy estimate.
-/

open MeasureTheory Set
open scoped ENNReal Topology
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport ReductionImageV3

/-- The sharp probability bound concerns the actual Bochner time integral
of the paired canonical gradient. The domain ratio is explicit; initial traces and space-time integrability
are derived. The large-time scalar profile remains an internal obligation
on this same specified flow; no kernel-decay predicate is assumed.
Source: `paper/main.tex:834–857`. -/
theorem physicalCoupling_paired_canonical_integrated_gradient_decay
    (d n : ℕ) (hd : 2 ≤ d) (hn : 1+(d : ℝ)/2 < (n : ℝ))
    (L r₀ C D : ℝ) (hC : 0 ≤ C) :
    ∃ B : ℝ, 0 < B ∧ ∀ (Q : EnvironmentLaw d L r₀) (i : Fin d)
      (u : Coefficient d (AKMUpperEllipticity L) → ℝ × Vec d → ℝ)
      (G : Coefficient d (AKMUpperEllipticity L) → ℝ × Vec d → Vec d),
      Measurable (fun z : Coefficient d (AKMUpperEllipticity L) ×
        (ℝ × Vec d) => u z.1 z.2) →
      Measurable (fun z : Coefficient d (AKMUpperEllipticity L) ×
        (ℝ × Vec d) => G z.1 z.2) →
      (∀ᵐ A ∂actualCoefficientLaw Q,
        IsSemigroupSolution A (fun x => (A x).mulVec (unitVector i)) (u A) (G A) ∧
        HasCanonicalKernelRepresentation A (fun x => (A x).mulVec (unitVector i)) (u A)) →
      ∀ p : ℝ, 2 ≤ p →
      (∀ t : ℝ, 1 ≤ t → ∀ x : Vec d,
        eLpNorm (fun A => u A (t,x)) (ENNReal.ofReal p) (actualCoefficientLaw Q) ≤
          ENNReal.ofReal (C*t^(-(1 : ℝ)/2-(d : ℝ)/4))) →
      ∀ μ : Measure (PhysicalField d L × PhysicalField d L), IsProbabilityMeasure μ →
      MeasurePreserving Prod.fst μ (physicalReferenceLaw Q) →
      MeasurePreserving Prod.snd μ (physicalReferenceLaw Q) →
      ∀ (R : ℝ), 1 ≤ R → ∀ U : Set (Vec d), IsOpen U → IsCompact (closure U) →
      ∀ [IsFiniteMeasure (volume.restrict U)], 0 < volume.real U →
      (∀ᵐ A ∂μ, Set.EqOn (project (r₀ := r₀) Q.ellipticity_parameter A.1) (project (r₀ := r₀) Q.ellipticity_parameter A.2) U) →
      ∀ χ : Vec d → ℝ, IsSpatialTest U χ →
      (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) →
      (∀ x, euclideanSq (gradient χ x) ≤ (D/R)^2) →
      ∀ V : Set (Vec d), MeasurableSet V → V ⊆ U → 0 < volume.real V →
      (∀ x ∈ V, χ x = 1) →
      let F := fun A => Real.sqrt (⨍ x in V, euclideanSq
        (∫ t in Icc (0 : ℝ) (4*R^2), G (project (r₀ := r₀) Q.ellipticity_parameter A.1) (t,x) - G (project (r₀ := r₀) Q.ellipticity_parameter A.2) (t,x)))
      MemLp F (ENNReal.ofReal p) μ ∧
        eLpNorm F (ENNReal.ofReal p) μ ≤
          ENNReal.ofReal (Real.sqrt (volume.real U / volume.real V) *
            B*R^(-(d : ℝ)/2)) := by
  obtain ⟨B, hB, hbound⟩ := physicalCoupling_paired_canonical_energy_moment_decay
    d n hd hn L r₀ C D hC
  refine ⟨B, hB, ?_⟩
  intro Q i u G hum hGm hflow p hp hlate μ hμ hfst hsnd R hR U hU hUc _ hUpos hEq χ hχ hχb hχD
    V hVm hVU hVpos hχV
  generalize hπdef : project (d := d) (r₀ := r₀) Q.ellipticity_parameter = π at hEq ⊢
  have hEq' := hEq
  rw [← hπdef] at hEq'
  have hπ : MeasurePreserving π (physicalReferenceLaw Q) (actualCoefficientLaw Q) :=
    hπdef ▸ measurePreserving_akmProject Q
  have hGmPhys : Measurable (fun z : PhysicalField d L × (ℝ × Vec d) =>
      G (π z.1) z.2) :=
    hGm.comp (hπ.measurable.prodMap measurable_id)
  let W := fun A : PhysicalField d L × PhysicalField d L =>
    fun z : ℝ × Vec d => G (π A.1) z - G (π A.2) z
  have hWm : Measurable (fun z :
      (PhysicalField d L × PhysicalField d L) ×
        (ℝ × Vec d) => W z.1 z.2) :=
    (hGmPhys.comp (measurable_fst.fst.prodMk measurable_snd)).sub
      (hGmPhys.comp (measurable_fst.snd.prodMk measurable_snd))
  let F := fun A => Real.sqrt (⨍ x in V, euclideanSq
    (∫ t in Icc (0 : ℝ) (4*R^2), W A (t,x)))
  let E := fun A => Real.sqrt ((4*R^2) * ∫ t in Icc (0 : ℝ) (4*R^2),
    ⨍ x in U, χ x^(2*n) * euclideanSq (W A (t,x)))
  have hFm : Measurable F := by
    have hm := measurable_integrated_gradient_rms (volume.restrict V) (4*R^2) W hWm
    have hc : Measurable (fun _ : PhysicalField d L × PhysicalField d L => Real.sqrt ((volume.real V)⁻¹)) :=
      measurable_const
    simpa only [F, setAverage_eq, smul_eq_mul,
      Real.sqrt_mul (inv_nonneg.mpr hVpos.le)] using hc.mul hm
  have hT : 0 < 4*R^2 := by have : 0 < R := zero_lt_one.trans_le hR; positivity
  have hK : 0 < AKMUpperEllipticity L := zero_lt_one.trans (one_lt_AKMUpperEllipticity Q.ellipticity_parameter)
  have hn2 : 2 ≤ n := by
    have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
    have hn' : (2 : ℝ) < n := by linarith
    exact_mod_cast hn'.le
  have hw := physicalCoupling_paired_canonical_weighted_energy_bound Q i u G hflow μ
    hfst hsnd hU hUc hEq' hT hχ hχb hχD n hn2
  rw [hπdef] at hw
  have hpoint : ∀ᵐ A ∂μ, ‖F A‖ ≤ Real.sqrt (volume.real U / volume.real V) * ‖E A‖ := by
    filter_upwards [(hπ.comp hfst).quasiMeasurePreserving.ae hflow,
      (hπ.comp hsnd).quasiMeasurePreserving.ae hflow, hEq, hw] with A h₁ h₂ hA henergy
    have hslice := (ae_restrict_iff' measurableSet_Ioi).mp
      (paired_semigroup_power_gradient_integrable_positive_ae hK h₁.1 h₂.1
        hU hUc hA hχ.1.continuous.measurable hχb n)
    have hslice' : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) (4*R^2)),
        Integrable (fun x => χ x^(2*n) * euclideanSq (W A (t,x)))
          (volume.restrict U) := by
      filter_upwards [ae_restrict_of_ae hslice, ae_restrict_mem measurableSet_Icc,
        ae_restrict_of_ae (volume.ae_ne (0 : ℝ))] with t ht hmem hne
      exact ht (lt_of_le_of_ne hmem.1 (Ne.symm hne))
    have hplateau := power_cutoff_plateau_spacetime_energy measurableSet_Icc
      hU.measurableSet hVm hVU χ hχ.1.continuous.measurable (fun x => (hχb x).1)
      hχV (W A) (hWm.comp (measurable_const.prodMk measurable_id)) hslice' henergy.1
    rw [Real.norm_of_nonneg (show 0 ≤ F A from Real.sqrt_nonneg _),
      Real.norm_of_nonneg (show 0 ≤ E A from Real.sqrt_nonneg _)]
    exact integrated_gradient_setAverage_le_energy_envelope hT.le hUpos hVpos (W A)
      (fun t x => χ x^(2*n) * euclideanSq (W A (t,x))) hplateau.1 hplateau.2
  have hE := hbound Q i u G hum hGm hflow p hp hlate μ hμ hfst hsnd R hR U hU hUc hUpos
    hEq' χ hχ hχb hχD
  rw [hπdef] at hE
  refine ⟨hE.1.of_le_mul hFm.aestronglyMeasurable hpoint, ?_⟩
  calc
    eLpNorm F (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (Real.sqrt (volume.real U / volume.real V)) *
          eLpNorm E (ENNReal.ofReal p) μ := eLpNorm_le_mul_eLpNorm_of_ae_le_mul hpoint _
    _ ≤ ENNReal.ofReal (Real.sqrt (volume.real U / volume.real V)) *
        ENNReal.ofReal (B*R^(-(d : ℝ)/2)) := mul_le_mul_right hE.2 _
    _ = _ := by rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]; congr 1; ring

end EinsteinRelation.Correctors
