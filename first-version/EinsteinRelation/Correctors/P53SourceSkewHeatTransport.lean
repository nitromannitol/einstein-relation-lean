import EinsteinRelation.Correctors.P53SourceSkewDilation
import EinsteinRelation.Correctors.AKMCanonicalHeatDilation
import EinsteinRelation.Correctors.SpatialWeakDilation
import EinsteinRelation.Correctors.SpatialLocalL2LimitDilation
import EinsteinRelation.Correctors.P53SourceSkewOrbitMoment

/-!
# The physical heat-selected flux gradient

Source: `paper/main.tex:722,740-756`. AKM Lemma 6.1 (the frozen literature
input `FluxGradientEstimate`) supplies, on AKM's coefficient carrier, a flux
potential whose gradient is selected by the heat formula (6.7). This module
transports it to the reduced environment: the potential and gradient become
jointly measurable functions of the reduced pair, and the literal heat formula
for the canonical centered flux, with its integer cutoffs in physical time,
selects the transported gradient almost surely. The time-cutoff mismatch caused
by the range dilation is handled by the stationary cutoff rescaling.
-/

open MeasureTheory Filter Topology Set
noncomputable section
namespace EinsteinRelation.Correctors
open External.AKM HeatSelectedSkewMeaning Environment.AKMTestIntegralSupport ReductionImageV3

open Classical in
/-- The physical field of a reduced pair in the reduced image, with a fixed
value outside it. -/
def physicalOfReduced {d : ℕ} {L : ℝ} (ω₀ : PhysicalField d L) (ρ : FieldPair d) :
    PhysicalField d L :=
  if h : ρ ∈ physicalReducedRange L then inverseReducePhysical ⟨ρ, h⟩ else ω₀

theorem measurable_physicalOfReduced {d : ℕ} {L : ℝ} (ω₀ : PhysicalField d L) :
    Measurable (physicalOfReduced ω₀) := by
  classical
  exact Measurable.dite (physicalReduceHomeomorph (d := d) (L := L)).symm.continuous.measurable
    measurable_const (measurableSet_physicalReducedRange L)

theorem physicalOfReduced_reduce {d : ℕ} {L : ℝ} (ω₀ ω : PhysicalField d L) :
    physicalOfReduced ω₀ (reduce ω.1) = ω := by
  have h : reduce ω.1 ∈ physicalReducedRange L := ⟨ω.1, ω.2, rfl⟩
  rw [physicalOfReduced, dif_pos h]
  exact inverseReduce_reducePhysical ω

theorem reduce_physicalOfReduced {d : ℕ} {L : ℝ} (ω₀ : PhysicalField d L)
    {ρ : FieldPair d} (h : ρ ∈ physicalReducedRange L) :
    reduce (physicalOfReduced ω₀ ρ).1 = ρ := by
  rw [physicalOfReduced, dif_pos h]
  exact congrArg Subtype.val (reducePhysical_inverseReduce ⟨ρ, h⟩)

/-- Reconstruction carries the reduced law to the physical reference law. -/
theorem measurePreserving_physicalOfReduced {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (ω₀ : PhysicalField d L) :
    MeasurePreserving (physicalOfReduced ω₀) (reducedEnvironmentLaw Q)
      (physicalReferenceLaw Q) := by
  refine ⟨measurable_physicalOfReduced ω₀, ?_⟩
  rw [← (measurePreserving_physicalReduction Q).map_eq,
    Measure.map_map (measurable_physicalOfReduced ω₀)
      (measurePreserving_physicalReduction Q).measurable]
  conv_rhs => rw [← Measure.map_id (μ := physicalReferenceLaw Q)]
  congr 1
  funext ω
  exact physicalOfReduced_reduce ω₀ ω

private theorem measurable_mat_entry {d : ℕ} (j k : Fin d) :
    Measurable (fun M : Mat d => M j k) :=
  (Continuous.matrix_elem continuous_id j k).measurable

/-- AKM Lemma 6.1 gives jointly measurable fields on the reduced pairs: a
potential and a gradient selected, almost surely, by the literal heat formula
for the canonical centered flux. The unit-ball `L²` norm of the gradient has a
finite second moment, by (6.8). -/
theorem exists_physical_heatSelected_fluxGradient (h68 : FluxGradientEstimate)
    (hP : External.GilbargTrudinger.BallPoincareEstimate)
    {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d) :
    ∃ (σ : FieldPair d → Vec d → Mat d) (G : FieldPair d → Fin d → Fin d → Vec d → Vec d),
      (∀ j k, Measurable (fun p : FieldPair d × Vec d => σ p.1 p.2 j k)) ∧
      (∀ j k l, Measurable (fun p : FieldPair d × Vec d => G p.1 j k p.2 l)) ∧
      (∀ᵐ ρ ∂reducedEnvironmentLaw Q,
        IsHeatSelectedFluxGradient
          (fun y => (canonicalCorrectorFlux Q i (translate y ρ) -
            expectedCorrectorFlux Q i).ofLp) (G ρ) ∧
        (∀ j k, HasWeakGradient Set.univ (fun x => σ ρ x j k) (G ρ j k)) ∧
        (∀ R : ℝ, 0 < R → ∀ j k,
          MemLp (fun x => σ ρ x j k) 2 (volume.restrict (ball 0 R)))) ∧
      ∀ j k l, ∫⁻ ρ, eLpNorm (fun x => G ρ j k x l) 2
        (volume.restrict (ball 0 1)) ^ 2 ∂reducedEnvironmentLaw Q < ⊤ := by
  have hr : 0 < r₀ := zero_lt_one.trans_le Q.range_parameter
  have hκ : 0 < ellipticityScale L := ellipticityScale_pos Q.ellipticity_parameter
  set κ := ellipticityScale L with hκdef
  obtain ⟨C, -, hS⟩ := exists_unitAKMFluxCorrector_with_canonical_source h68 hP d L r₀ 2
    Q.ellipticity_parameter two_pos
  obtain ⟨φ, S, hsource, hmoment⟩ := hS Q i
  haveI : IsProbabilityMeasure (physicalReferenceLaw Q) := physicalReferenceLaw_probability Q
  obtain ⟨ω₀, hω₀⟩ := Q.regular.exists
  let P := physicalOfReduced (⟨ω₀, hω₀⟩ : PhysicalField d L)
  let Ψ : FieldPair d → Coefficient d (AKMUpperEllipticity L) := fun ρ =>
    project (r₀ := r₀) Q.ellipticity_parameter (P ρ)
  have hΨ : Measurable Ψ :=
    (measurable_project Q.ellipticity_parameter).comp (measurable_physicalOfReduced _)
  let F₀ : FieldPair d → Vec d := fun ω =>
    (canonicalCorrectorFlux Q i ω - expectedCorrectorFlux Q i).ofLp
  obtain ⟨hF₀, hF₀2⟩ := canonical_flux_source_measurable_memLp Q i
  have hdil : Measurable (fun p : FieldPair d × Vec d => (Ψ p.1, r₀⁻¹ • p.2)) :=
    (hΨ.comp measurable_fst).prodMk ((measurable_const_smul r₀⁻¹).comp measurable_snd)
  have hΨmp : MeasurePreserving Ψ (reducedEnvironmentLaw Q) (actualCoefficientLaw Q) :=
    (measurePreserving_akmProject Q).comp (measurePreserving_physicalOfReduced Q _)
  refine ⟨fun ρ x j k => (r₀ / κ) * S.potential (Ψ ρ) (r₀⁻¹ • x) j k,
    fun ρ j k x => κ⁻¹ • S.grad (Ψ ρ) j k (r₀⁻¹ • x), ?_, ?_, ?_, ?_⟩
  · intro j k
    exact ((measurable_mat_entry j k).comp (S.measurable_potential.comp hdil)).const_mul _
  · intro j k l
    exact ((measurable_pi_apply l).comp ((S.measurable_grad j k).comp hdil)).const_mul _
  have hphys : ∀ᵐ ω ∂physicalReferenceLaw Q,
      IsHeatSelectedFluxGradient (fun y => F₀ (translate y (reduce ω.1)))
        (fun j k x => κ⁻¹ • S.grad (project (r₀ := r₀) Q.ellipticity_parameter ω) j k
          (r₀⁻¹ • x)) ∧
      (∀ j k, HasWeakGradient Set.univ
        (fun x => (r₀ / κ) *
          S.potential (project (r₀ := r₀) Q.ellipticity_parameter ω) (r₀⁻¹ • x) j k)
        (fun x => κ⁻¹ • S.grad (project (r₀ := r₀) Q.ellipticity_parameter ω) j k
          (r₀⁻¹ • x))) ∧
      (∀ R : ℝ, 0 < R → ∀ j k, MemLp (fun x => (r₀ / κ) *
          S.potential (project (r₀ := r₀) Q.ellipticity_parameter ω) (r₀⁻¹ • x) j k)
        2 (volume.restrict (ball 0 R))) := by
    have hres := ae_dilated_heat_selection_rescaled_local_L2 (reducedEnvironmentLaw Q)
      (reducedEnvironmentLaw_stationary Q) F₀ hF₀ hF₀2 r₀ κ (r₀ ^ 2)⁻¹ hr.ne' (by positivity)
    have hres' := (measurePreserving_physicalReduction Q).quasiMeasurePreserving.ae hres
    have hsel := (measurePreserving_akmProject Q).quasiMeasurePreserving.ae S.heat_selected
    have hweak := (measurePreserving_akmProject Q).quasiMeasurePreserving.ae S.weak_gradient
    have hloc := (measurePreserving_akmProject Q).quasiMeasurePreserving.ae
      S.locally_square_integrable
    filter_upwards [hsource, hres', hsel, hweak, hloc] with ω hsrc hrs hse hwe hlo
    set A := project (r₀ := r₀) Q.ellipticity_parameter ω with hAdef
    set ρ := reduce ω.1 with hρdef
    let g' : Vec d → Vec d := fun y => κ • F₀ (translate (r₀ • y) ρ)
    have hsel' : IsHeatSelectedFluxGradient g' (S.grad A) := by
      apply isHeatSelectedFluxGradient_congr_source_ae ?_ hse
      filter_upwards [hsrc] with y hy
      rw [hy]
      simp only [g', F₀, WithLp.ofLp_sub, hκdef]
    have hconv := hrs (S.grad A) hsel'
    have hsrcEq : (fun z => κ⁻¹ • g' (r₀⁻¹ • z)) = fun x => F₀ (translate x ρ) := by
      funext z
      simp only [g', smul_smul, mul_inv_cancel₀ hr.ne', one_smul,
        inv_mul_cancel₀ hκ.ne']
    have htrunc (m n : ℕ) (j k l : Fin d) (x : Vec d) :
        iteratedAKMHeatGradientTruncation (fun x => F₀ (translate x ρ)) m n j k l x =
          κ⁻¹ * rescaledAKMHeatGradientTruncation g' (r₀ ^ 2)⁻¹ m n j k l (r₀⁻¹ • x) := by
      rw [← hsrcEq]
      have h := iteratedAKMHeatGradientTruncation_dilation g' r₀ κ⁻¹ hr m n j k l (r₀⁻¹ • x)
      rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul] at h
      rw [h, rescaledAKMHeatGradientTruncation]
      congr 2
      · push_cast
        rw [div_eq_mul_inv]
    have hGL (R : ℝ) (hR : 0 < R) (j k l : Fin d) :
        MemLp (fun x => κ⁻¹ * S.grad A j k (r₀⁻¹ • x) l) 2 (volume.restrict (ball 0 R)) := by
      have h := memLp_two_on_euclidean_balls_dilation (fun x => S.grad A j k x l)
        (fun R hR => memLp_pi_iff.mp (hlo R hR j k).2 l) r₀⁻¹ κ⁻¹ (inv_pos.mpr hr) R hR
      simpa only [smul_eq_mul] using h
    refine ⟨?_, ?_, ?_⟩
    · intro j k l R
      let f : ℕ × ℕ → Vec d → ℝ := fun mn x =>
        rescaledAKMHeatGradientTruncation g' (r₀ ^ 2)⁻¹ mn.1 mn.2 j k l x - S.grad A j k x l
      have hf (R' : ℕ) (mn : ℕ × ℕ) :
          MemLp (f mn) 2 (volume.restrict (ball 0 ((R' : ℝ) + 1))) :=
        ((hconv j k l R').1 mn.1 mn.2).sub
          (memLp_pi_iff.mp (hlo ((R' : ℝ) + 1) (by positivity) j k).2 l)
      have hdl := local_L2_zero_dilation f hf (fun R' => (hconv j k l R').2) r₀⁻¹ κ⁻¹
        (inv_pos.mpr hr) R
      have hfun (mn : ℕ × ℕ) : (fun x => κ⁻¹ * f mn (r₀⁻¹ • x)) =
          fun x => iteratedAKMHeatGradientTruncation (fun x => F₀ (translate x ρ))
            mn.1 mn.2 j k l x - (κ⁻¹ • S.grad A j k (r₀⁻¹ • x)) l := by
        funext x
        rw [htrunc]
        simp only [f, Pi.smul_apply, smul_eq_mul]
        ring
      refine ⟨?_, fun m n => ?_, ?_, ?_⟩
      · intro m n
        have h := heat_window_integrability_of_dilated_selection hsel' r₀ κ⁻¹ hr j k l R m n
        simpa only [hsrcEq] using h
      · have h := (hdl.1 (m, n)).add (hGL ((R : ℝ) + 1) (by positivity) j k l)
        refine h.ae_eq (Eventually.of_forall fun x => ?_)
        simp only [Pi.add_apply]
        rw [htrunc]
        simp only [f]
        ring
      · simpa only [Pi.smul_apply, smul_eq_mul] using hGL ((R : ℝ) + 1) (by positivity) j k l
      · simpa only [hfun] using hdl.2
    · intro j k
      have h := hasWeakGradient_dilation (fun x => S.potential A x j k) (S.grad A j k)
        (fun R hR => (hlo R hR j k).1) (fun R hR => (hlo R hR j k).2) (hwe j k) r₀⁻¹ (r₀ / κ)
        (inv_pos.mpr hr)
      have hc : r₀ / κ * r₀⁻¹ = κ⁻¹ := by field_simp
      simpa only [hc] using h
    · intro R hR j k
      have h := memLp_two_on_euclidean_balls_dilation (fun x => S.potential A x j k)
        (fun R hR => (hlo R hR j k).1) r₀⁻¹ (r₀ / κ) (inv_pos.mpr hr) R hR
      simpa only [smul_eq_mul] using h
  have hP' := (measurePreserving_physicalOfReduced Q ⟨ω₀, hω₀⟩).quasiMeasurePreserving.ae hphys
  have hmem : ∀ᵐ ρ ∂reducedEnvironmentLaw Q, ρ ∈ physicalReducedRange L :=
    ae_map_reduce_mem_physicalImage Q
  · filter_upwards [hP', hmem] with ρ hρ hρm
    rw [reduce_physicalOfReduced _ hρm] at hρ
    exact hρ
  · intro j k l
    simpa only [Pi.smul_apply, smul_eq_mul] using
      lintegral_sq_eLpNorm_physical_fluxGradient_lt_top Q S hmoment Ψ hΨmp κ
        Q.range_parameter j k l

end EinsteinRelation.Correctors
