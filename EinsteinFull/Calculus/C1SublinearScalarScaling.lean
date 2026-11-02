import EinsteinFull.Calculus.C3SublinearSmoothBootstrap
import EinsteinRelation.Correctors.SpatialAverageDilation
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import EinsteinFull.Frozen.ReducedLawStationary
import EinsteinRelation.Correctors.HeatAverageTranslation
import EinsteinFull.Calculus.C6SublinearFluxTraceIdentification
import EinsteinRelation.Correctors.FrobeniusDilation

/-! Literal range dilation of the same selected scalar corrector. -/
open MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinRelation.Correctors EinsteinRelation.External.AKM
open EinsteinRelation.Environment.AKMTestIntegralSupport EinsteinRelation.ReductionImageV3

namespace C1SublinearScalarScaling

/-- Return a unit-range potential to the physical spatial variable. -/
def physicalPotential {d : ℕ} (r : ℝ) (v : Vec d → ℝ) (x : Vec d) : ℝ :=
  r * v (r⁻¹ • x)

theorem physicalPotential_contDiff {d : ℕ} {r : ℝ} {v : Vec d → ℝ}
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) :
    ContDiff ℝ (⊤ : ℕ∞) (physicalPotential r v) := by
  change ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec d => r * v (r⁻¹ • x))
  exact contDiff_const.mul (hv.comp (contDiff_id.const_smul r⁻¹))

/-- The potential amplitude cancels exactly the inverse spatial scale. -/
theorem physicalPotential_fderiv {d : ℕ} {r : ℝ} (hr : 0 < r)
    {v : Vec d → ℝ} (hv : Differentiable ℝ v) (x h : Vec d) :
    fderiv ℝ (physicalPotential r v) x h = fderiv ℝ v (r⁻¹ • x) h := by
  have hc := ((hv (r⁻¹ • x)).hasFDerivAt.comp x
    ((hasFDerivAt_id x).const_smul r⁻¹)).const_mul r
  change fderiv ℝ (fun y => r * (v ∘ (fun z : Vec d => r⁻¹ • z)) y) x h = _
  rw [hc.fderiv]
  simp only [smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, map_smul, smul_eq_mul]
  rw [← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul]

/-- Dilation preserves the original potential's volume almost-everywhere class. -/
theorem physicalPotential_ae_eq {d : ℕ} {r : ℝ} (hr : 0 < r)
    {v u : Vec d → ℝ} (h : v =ᵐ[(volume : Measure (Vec d))] u) :
    physicalPotential r v =ᵐ[(volume : Measure (Vec d))] physicalPotential r u := by
  have h' := (Measure.quasiMeasurePreserving_smul (volume : Measure (Vec d))
    (inv_ne_zero hr.ne')).ae h
  filter_upwards [h'] with x hx
  exact congrArg (fun t : ℝ => r * t) hx

/-- Volume normalization cancels the Jacobian on the actual dilated ball.
The additive constant and potential amplitude retain their range factor. -/
theorem physicalPotential_meanSquare {d : ℕ} (u : Vec d → ℝ)
    (a r R : ℝ) (hr : 0 < r) (hR : 0 < R) :
    (⨍ x in ball 0 (r * R), |physicalPotential r u x - r * a| ^ 2) =
      r ^ 2 * (⨍ y in ball 0 R, |u y - a| ^ 2) := by
  rw [← setAverage_euclideanBall_smul
    (fun x => |physicalPotential r u x - r * a| ^ 2) r R hr hR]
  have hi (y : Vec d) : |physicalPotential r u (r • y) - r * a| ^ 2 =
      r ^ 2 * |u y - a| ^ 2 := by
    simp only [physicalPotential, smul_smul, inv_mul_cancel₀ hr.ne', one_smul,
      ← mul_sub, abs_mul, mul_pow, sq_abs]
  simp_rw [hi]
  exact average_const_mul (μ := volume.restrict (ball (0 : Vec d) R)) (r ^ 2) _

theorem physicalPotential_rms {d : ℕ} (u : Vec d → ℝ)
    (a r R : ℝ) (hr : 0 < r) (hR : 0 < R) :
    Real.sqrt (⨍ x in ball 0 (r * R), |physicalPotential r u x - r * a| ^ 2) =
      r * Real.sqrt (⨍ y in ball 0 R, |u y - a| ^ 2) := by
  rw [physicalPotential_meanSquare u a r R hr hR, Real.sqrt_mul (sq_nonneg r),
    Real.sqrt_sq hr.le]

/-- The admitted exponential moment gives the literal stretched exponential
tail for its measurable random radius. -/
theorem measure_radius_gt_le {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → ℝ} {s θ : ℝ}
    (hX : OsBound P X s θ) (R : ℝ) (hR : 0 ≤ R) :
    P {ω | R < X ω} ≤ ENNReal.ofReal (2 * Real.exp (-((θ⁻¹ * R) ^ s))) := by
  let f : Ω → ℝ≥0∞ := fun ω =>
    ENNReal.ofReal (Real.exp ((θ⁻¹ * max (X ω) 0) ^ s))
  let a : ℝ≥0∞ := ENNReal.ofReal (Real.exp ((θ⁻¹ * R) ^ s))
  have hf : Measurable f := by
    exact ENNReal.measurable_ofReal.comp
      (((measurable_const.mul (hX.1.max measurable_const)).pow_const s).exp)
  have ha : a ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _)
  have hsub : {ω | R < X ω} ⊆ {ω | a ≤ f ω} := by
    intro ω hω
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    exact Real.rpow_le_rpow (mul_nonneg (inv_nonneg.mpr hX.2.2.1.le) hR)
      (mul_le_mul_of_nonneg_left (hω.le.trans (le_max_left _ _))
        (inv_nonneg.mpr hX.2.2.1.le)) hX.2.1.le
  calc
    P {ω | R < X ω} ≤ P {ω | a ≤ f ω} := measure_mono hsub
    _ ≤ (∫⁻ ω, f ω ∂P) / a :=
      meas_ge_le_lintegral_div hf.aemeasurable ha ENNReal.ofReal_ne_top
    _ ≤ 2 / a := ENNReal.div_le_div_right hX.2.2.2 a
    _ = ENNReal.ofReal (2 * Real.exp (-((θ⁻¹ * R) ^ s))) := by
      rw [show (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) by norm_num,
        ← ENNReal.ofReal_div_of_pos (Real.exp_pos _)]
      congr 1
      rw [div_eq_mul_inv, Real.exp_neg]

/-- Physical reduction is an embedding into the full reduced field space. -/
theorem measurableEmbedding_physicalReduce {d : ℕ} (L : ℝ) :
    MeasurableEmbedding (fun ω : PhysicalField d L => reduce ω.1) :=
  (Probability.measurableEmbedding_reduce d).comp
    (MeasurableEmbedding.subtype_coe
      (Sharpness.measurableSet_isRegular_fieldPair (d := d) L))

theorem map_physicalReduce {d : ℕ} {L r : ℝ} (Q : EnvironmentLaw d L r) :
    (physicalReferenceLaw Q).map (fun ω => reduce ω.1) = reducedLaw Q := by
  change (physicalReferenceLaw Q).map
    (reduce ∘ (Subtype.val : PhysicalField d L → FieldPair d)) = reducedLaw Q
  rw [← Measure.map_map Probability.measurable_reduce measurable_subtype_coe,
    physicalReferenceLaw_forget]
  rfl

/-- Extend a selected physical potential without selecting a different
representative at any physical reduced sample. -/
def reducedPotential {d : ℕ} {L : ℝ}
    (v : PhysicalField d L → Vec d → ℝ) : FieldPair d → Vec d → ℝ :=
  Function.extend (fun ω : PhysicalField d L => reduce ω.1) v (fun _ _ => 0)

theorem reducedPotential_reduce {d : ℕ} {L : ℝ}
    (v : PhysicalField d L → Vec d → ℝ) (ω : PhysicalField d L) :
    reducedPotential v (reduce ω.1) = v ω :=
  (measurableEmbedding_physicalReduce L).injective.extend_apply _ _ _

/-- A measurable physical good event has a measurable reduced image with
exactly the same exceptional probability. -/
theorem reduced_good_event {d : ℕ} {L r : ℝ} (Q : EnvironmentLaw d L r)
    (B : Set (PhysicalField d L)) (hB : MeasurableSet B) :
    MeasurableSet ((fun ω : PhysicalField d L => reduce ω.1) '' B) ∧
      reducedLaw Q ((fun ω : PhysicalField d L => reduce ω.1) '' B)ᶜ =
        physicalReferenceLaw Q Bᶜ := by
  have he := measurableEmbedding_physicalReduce (d := d) L
  have hE := he.measurableSet_image.mpr hB
  refine ⟨hE, ?_⟩
  rw [← map_physicalReduce Q, Measure.map_apply he.measurable hE.compl]
  simp only [Set.preimage_compl, he.injective.preimage_image]

/-- Extract one measurable common full event even when the chosen-potential
predicate itself has not been shown measurable. -/
theorem measurable_common_event {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (p : Ω → Prop) (hp : ∀ᵐ ω ∂P, p ω) :
    ∃ B : Set Ω, MeasurableSet B ∧ P Bᶜ = 0 ∧ ∀ ω ∈ B, p ω := by
  refine ⟨(toMeasurable P {ω | ¬p ω})ᶜ,
    (measurableSet_toMeasurable P _).compl, ?_, ?_⟩
  · simpa only [compl_compl, measure_toMeasurable] using ae_iff.mp hp
  · intro ω hω
    by_contra hn
    exact hω (subset_toMeasurable P {ω | ¬p ω} hn)

/-- Intersect all coordinate radius events with one common full event, then
transport the resulting measurable event to the actual full reduced law. -/
theorem exists_reduced_radius_event {d : ℕ} {L r : ℝ}
    {ι : Type*} [Fintype ι] (Q : EnvironmentLaw d L r)
    (p : PhysicalField d L → Prop) (hp : ∀ᵐ ω ∂physicalReferenceLaw Q, p ω)
    (X : ι → Coefficient d (AKMUpperEllipticity L) → ℝ) {s θ : ℝ}
    (hX : ∀ i, OsBound (actualCoefficientLaw Q) (X i) s θ)
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ E : Set (FieldPair d), MeasurableSet E ∧
      reducedLaw Q Eᶜ ≤ (Fintype.card ι : ℝ≥0∞) *
        ENNReal.ofReal (2 * Real.exp (-((θ⁻¹ * R) ^ s))) ∧
      ∀ ρ ∈ E, ∃ ω : PhysicalField d L,
        reduce ω.1 = ρ ∧ p ω ∧
          ∀ i, X i (project (r₀ := r) Q.ellipticity_parameter ω) ≤ R := by
  obtain ⟨B, hB, hBnull, hBp⟩ := measurable_common_event _ p hp
  let Y := fun i ω => X i (project (r₀ := r) Q.ellipticity_parameter ω)
  have hY (i : ι) : OsBound (physicalReferenceLaw Q) (Y i) s θ :=
    osBound_comp (measurable_project (r₀ := r) Q.ellipticity_parameter) (hX i)
  let G := B ∩ {ω | ∀ i, Y i ω ≤ R}
  have hG : MeasurableSet G := hB.inter (by
    simpa only [Set.ofPred_forall] using
      MeasurableSet.iInter fun i => measurableSet_le (hY i).1 measurable_const)
  let E := (fun ω : PhysicalField d L => reduce ω.1) '' G
  obtain ⟨hE, hmeasure⟩ := reduced_good_event Q G hG
  refine ⟨E, hE, ?_, ?_⟩
  · rw [hmeasure]
    have hcomp : Gᶜ = Bᶜ ∪ ⋃ i, {ω | R < Y i ω} := by
      ext ω
      simp only [G, Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_ofPred_eq,
        not_and_or, not_forall, not_le, Set.mem_union, Set.mem_iUnion]
    rw [hcomp]
    calc
      _ ≤ physicalReferenceLaw Q Bᶜ +
          physicalReferenceLaw Q (⋃ i, {ω | R < Y i ω}) := measure_union_le _ _
      _ = physicalReferenceLaw Q (⋃ i, {ω | R < Y i ω}) := by rw [hBnull, zero_add]
      _ ≤ ∑ i, physicalReferenceLaw Q {ω | R < Y i ω} :=
        measure_iUnion_fintype_le _ _
      _ ≤ ∑ _i : ι, ENNReal.ofReal (2 * Real.exp (-((θ⁻¹ * R) ^ s))) :=
        Finset.sum_le_sum fun i _ => measure_radius_gt_le (hY i) R hR
      _ = _ := by simp [nsmul_eq_mul]
  · rintro ρ ⟨ω, hω, rfl⟩
    exact ⟨ω, rfl, hBp ω hω.1, hω.2⟩

end C1SublinearScalarScaling

/-- The chosen source corrector, after literal dependence-range dilation, is
smooth in the same potential class and has the actual canonical gradient.
The identification premise is the conclusion of the actual source-pair producer. -/
theorem sublinear_source_corrector_physical_representative
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q) (i : Fin d)
    (φ : Corrector (actualCoefficientLaw Q) (correctorUnitVector i).ofLp)
    (hφ : ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ y ∂(volume : Measure (Vec d)),
      (correctorUnitVector i).ofLp +
        φ.grad (project (r₀ := D.dependenceRange) Q.ellipticity_parameter ω) y =
      (correctorUnitVector i + (canonicalCorrectorGradient Q i :
        Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
          (translate (D.dependenceRange • y) (reduce ω.1))).ofLp) :
    ∀ᵐ ω ∂physicalReferenceLaw Q, ∃ v : Vec d → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) v ∧
      v =ᵐ[(volume : Measure (Vec d))]
        (C1SublinearScalarScaling.physicalPotential D.dependenceRange
          (φ.potential (project (r₀ := D.dependenceRange)
            Q.ellipticity_parameter ω))) ∧
      (∀ R : ℝ, 0 < R → ∀ a : ℝ,
        Real.sqrt (⨍ x in ball 0 (D.dependenceRange * R),
          |v x - D.dependenceRange * a| ^ 2) =
        D.dependenceRange * Real.sqrt (⨍ y in ball 0 R,
          |φ.potential (project (r₀ := D.dependenceRange)
            Q.ellipticity_parameter ω) y - a| ^ 2)) ∧
      ∀ᵐ x ∂(volume : Measure (Vec d)), ∀ j : Fin d,
        fderiv ℝ v x (unitVector j) =
          correctorGradient Q i (translate x (reduce ω.1)) j := by
  have hr : 0 < D.dependenceRange := zero_lt_one.trans_le Q.range_parameter
  filter_upwards [sublinear_source_corrector_smooth_representative d hd D Q hQ i φ, hφ]
    with ω hv hident
  obtain ⟨v, hvc, hvp, hvg⟩ := hv
  refine ⟨C1SublinearScalarScaling.physicalPotential D.dependenceRange v,
    C1SublinearScalarScaling.physicalPotential_contDiff hvc,
    C1SublinearScalarScaling.physicalPotential_ae_eq hr hvp, ?_, ?_⟩
  · intro R hR a
    rw [C1SublinearScalarScaling.physicalPotential_rms v a D.dependenceRange R hr hR]
    congr 2
    apply average_congr
    filter_upwards [ae_restrict_of_ae hvp] with y hy
    rw [hy]
  have hdil := (Measure.quasiMeasurePreserving_smul (volume : Measure (Vec d))
    (inv_ne_zero hr.ne')).ae (hvg.and hident)
  filter_upwards [hdil] with x hx
  intro j
  rw [C1SublinearScalarScaling.physicalPotential_fderiv hr
    (hvc.differentiable (by norm_num)), hx.1 j]
  have hcoord := congrFun hx.2 j
  simp only [Pi.add_apply, WithLp.ofLp_add, smul_smul,
    mul_inv_cancel₀ hr.ne', one_smul] at hcoord
  change φ.grad _ (D.dependenceRange⁻¹ • x) j = _
  exact add_left_cancel hcoord

/-- Actual source pairs admit smooth physical scalar representatives on one
common event. The same random radii and the same selected flux correctors are
retained; the oscillation bound uses the literal dilated Euclidean ball. -/
theorem exists_sourcePairs_physical_scalar
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ β C Cs : ℝ, 0 < β ∧ 0 < C ∧ 0 < Cs ∧
      ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange),
        HasSmoothBounds D Q →
        ∃ φ : (i : Fin d) →
            Corrector (actualCoefficientLaw Q) (correctorUnitVector i).ofLp,
          ∃ S : (i : Fin d) → FluxCorrector (φ i),
          ∃ X : Fin d → Coefficient d (AKMUpperEllipticity D.ellipticity) → ℝ,
            (∀ i : Fin d, Measurable (X i) ∧
              OsBound (actualCoefficientLaw Q) (X i) ((d : ℝ) / 2) Cs) ∧
            ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ i : Fin d,
              ∃ v : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) v ∧
                v =ᵐ[(volume : Measure (Vec d))]
                  C1SublinearScalarScaling.physicalPotential D.dependenceRange
                    ((φ i).potential (project (r₀ := D.dependenceRange)
                      Q.ellipticity_parameter ω)) ∧
                (∀ᵐ x ∂(volume : Measure (Vec d)), ∀ j : Fin d,
                  fderiv ℝ v x (unitVector j) =
                    correctorGradient Q i (translate x (reduce ω.1)) j) ∧
                1 ≤ X i (project (r₀ := D.dependenceRange) Q.ellipticity_parameter ω) ∧
                ∀ R : ℝ,
                  X i (project (r₀ := D.dependenceRange) Q.ellipticity_parameter ω) ≤ R →
                  ∃ a : ℝ,
                    Real.sqrt (⨍ x in ball 0 (D.dependenceRange * R),
                      |v x - a| ^ 2) +
                    D.dependenceRange * Real.sqrt (⨍ y in ball 0 R,
                      frobeniusNorm ((S i).potential
                        (project (r₀ := D.dependenceRange) Q.ellipticity_parameter ω) y -
                        (Matrix.of fun j k => ⨍ z in ball 0 R,
                          (S i).potential (project (r₀ := D.dependenceRange)
                            Q.ellipticity_parameter ω) z j k)) ^ 2) ≤
                      D.dependenceRange * C *
                        R ^ (1 - β * ((d : ℝ) - (d : ℝ) / 2)) := by
  obtain ⟨β, C, Cs, hβ, hC, hCs, hpairs⟩ :=
    EinsteinFull.Calculus.C3SublinearPair.exists_sourcePairs d hd
      D.ellipticity D.one_le_ellipticity
  refine ⟨β, C, Cs, hβ, hC, hCs, ?_⟩
  intro Q hQ
  obtain ⟨φ, hident, S, X, hX⟩ := hpairs Q
  refine ⟨φ, S, X, fun i => ⟨(hX i).1, (hX i).2.1⟩, ?_⟩
  have hphysical : ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ i : Fin d,
      1 ≤ X i (project (r₀ := D.dependenceRange) Q.ellipticity_parameter ω) ∧
        ∀ R : ℝ,
          X i (project (r₀ := D.dependenceRange) Q.ellipticity_parameter ω) ≤ R →
          Real.sqrt (⨍ y in ball 0 R,
            |(φ i).potential (project (r₀ := D.dependenceRange)
              Q.ellipticity_parameter ω) y -
              (⨍ z in ball 0 R, (φ i).potential (project (r₀ := D.dependenceRange)
                Q.ellipticity_parameter ω) z)| ^ 2) +
            Real.sqrt (⨍ y in ball 0 R,
              frobeniusNorm ((S i).potential
                (project (r₀ := D.dependenceRange) Q.ellipticity_parameter ω) y -
                (Matrix.of fun j k => ⨍ z in ball 0 R,
                  (S i).potential (project (r₀ := D.dependenceRange)
                    Q.ellipticity_parameter ω) z j k)) ^ 2) ≤
                C * R ^ (1 - β * ((d : ℝ) - (d : ℝ) / 2)) := by
    apply ae_all_iff.mpr
    intro i
    have hh := ae_of_ae_map
      (measurable_project (r₀ := D.dependenceRange) Q.ellipticity_parameter).aemeasurable
      (hX i).2.2
    exact hh.mono fun ω hω => ⟨hω.1, fun R hR => (hω.2 R hR).1⟩
  have hsmooth := ae_all_iff.mpr fun i =>
    sublinear_source_corrector_physical_representative d hd D Q hQ i (φ i)
      (hident.mono fun _ hω => hω i)
  have hr : 0 < D.dependenceRange := zero_lt_one.trans_le Q.range_parameter
  filter_upwards [hphysical, hsmooth] with ω hω hv
  intro i
  obtain ⟨v, hvc, hvp, hvrms, hvg⟩ := hv i
  refine ⟨v, hvc, hvp, hvg, (hω i).1, ?_⟩
  intro R hR
  have hRpos : 0 < R := zero_lt_one.trans_le ((hω i).1.trans hR)
  refine ⟨D.dependenceRange *
    (⨍ y in ball 0 R, (φ i).potential (project (r₀ := D.dependenceRange)
      Q.ellipticity_parameter ω) y), ?_⟩
  rw [hvrms R hRpos]
  calc
    _ = D.dependenceRange * (_ + _) := (mul_add _ _ _).symm
    _ ≤ D.dependenceRange * (C * R ^ (1 - β * ((d : ℝ) - (d : ℝ) / 2))) :=
      mul_le_mul_of_nonneg_left ((hω i).2 R hR) hr.le
    _ = _ := (mul_assoc _ _ _).symm

/-- The actual selected source pair has a reduced scalar representative and
measurable common coordinate events with the original stretched exponential
tail. Constants are chosen before the environment law. -/
theorem exists_sourcePairs_reduced_scalar
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ β C Cs : ℝ, 0 < β ∧ 0 < C ∧ 0 < Cs ∧
      ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange),
        HasSmoothBounds D Q →
        ∃ φ : (i : Fin d) →
            Corrector (actualCoefficientLaw Q) (correctorUnitVector i).ofLp,
          ∃ _S : (i : Fin d) → FluxCorrector (φ i),
          ∃ u : Fin d → FieldPair d → Vec d → ℝ,
            (∀ᵐ ω ∂physicalReferenceLaw Q, ∀ i : Fin d,
              u i (reduce ω.1) =ᵐ[(volume : Measure (Vec d))]
                C1SublinearScalarScaling.physicalPotential D.dependenceRange
                  ((φ i).potential (project (r₀ := D.dependenceRange)
                    Q.ellipticity_parameter ω))) ∧
            (∀ᵐ ρ ∂reducedLaw Q, ∀ i : Fin d,
              ContDiff ℝ (⊤ : ℕ∞) (u i ρ) ∧
              ∀ᵐ x ∂(volume : Measure (Vec d)), ∀ j : Fin d,
                fderiv ℝ (u i ρ) x (unitVector j) =
                  correctorGradient Q i (translate x ρ) j) ∧
            ∀ R : ℝ, 0 ≤ R → ∃ E : Set (FieldPair d), MeasurableSet E ∧
              reducedLaw Q Eᶜ ≤ (d : ℝ≥0∞) * ENNReal.ofReal
                (2 * Real.exp (-((Cs⁻¹ * R) ^ ((d : ℝ) / 2)))) ∧
              ∀ ρ ∈ E, ∃ a : Fin d → ℝ, ∀ i : Fin d,
                Real.sqrt (⨍ x in ball 0 (D.dependenceRange * R),
                  |u i ρ x - a i| ^ 2) ≤
                    D.dependenceRange * C *
                      R ^ (1 - β * ((d : ℝ) - (d : ℝ) / 2)) := by
  classical
  obtain ⟨β, C, Cs, hβ, hC, hCs, hpairs⟩ :=
    exists_sourcePairs_physical_scalar d hd D
  refine ⟨β, C, Cs, hβ, hC, hCs, ?_⟩
  intro Q hQ
  obtain ⟨φ, S, X, hX, hp⟩ := hpairs Q hQ
  obtain ⟨B, hB, hBnull, hBp⟩ :=
    C1SublinearScalarScaling.measurable_common_event _ _ hp
  let v : PhysicalField d D.ellipticity → Fin d → Vec d → ℝ := fun ω i =>
    if h : ω ∈ B then Classical.choose (hBp ω h i) else fun _ => 0
  have hv (ω : PhysicalField d D.ellipticity) (hω : ω ∈ B) (i : Fin d) :=
    Classical.choose_spec (hBp ω hω i)
  have hv_eq (ω : PhysicalField d D.ellipticity) (hω : ω ∈ B) (i : Fin d) :
      v ω i = Classical.choose (hBp ω hω i) := dite_eq_left hω
  let u : Fin d → FieldPair d → Vec d → ℝ := fun i =>
    C1SublinearScalarScaling.reducedPotential (fun ω => v ω i)
  have hu (ω : PhysicalField d D.ellipticity) (i : Fin d) :
      u i (reduce ω.1) = v ω i :=
    C1SublinearScalarScaling.reducedPotential_reduce _ _
  have hBae : ∀ᵐ ω ∂physicalReferenceLaw Q, ω ∈ B := ae_iff.mpr hBnull
  refine ⟨φ, S, u, ?_, ?_, ?_⟩
  · filter_upwards [hBae] with ω hω
    intro i
    rw [hu, hv_eq ω hω i]
    exact (hv ω hω i).2.1
  · let p : FieldPair d → Prop := fun ρ => ∀ i : Fin d,
      ContDiff ℝ (⊤ : ℕ∞) (u i ρ) ∧
        ∀ᵐ x ∂(volume : Measure (Vec d)), ∀ j : Fin d,
          fderiv ℝ (u i ρ) x (unitVector j) =
            correctorGradient Q i (translate x ρ) j
    change ∀ᵐ ρ ∂reducedLaw Q, p ρ
    rw [← C1SublinearScalarScaling.map_physicalReduce Q,
      (C1SublinearScalarScaling.measurableEmbedding_physicalReduce
        D.ellipticity).ae_map_iff]
    filter_upwards [hBae] with ω hω
    intro i
    rw [hu, hv_eq ω hω i]
    exact ⟨(hv ω hω i).1, (hv ω hω i).2.2.1⟩
  · intro R hR
    obtain ⟨E, hE, hEtail, hEp⟩ :=
      C1SublinearScalarScaling.exists_reduced_radius_event Q
        (fun ω => ω ∈ B) hBae X (fun i => (hX i).2) R hR
    refine ⟨E, hE, ?_, ?_⟩
    · simpa only [Fintype.card_fin] using hEtail
    · intro ρ hρ
      obtain ⟨ω, rfl, hω, hrad⟩ := hEp ρ hρ
      have hosc (i : Fin d) := (hv ω hω i).2.2.2.2 R (hrad i)
      choose a ha using hosc
      refine ⟨a, ?_⟩
      intro i
      rw [hu, hv_eq ω hω i]
      exact (le_add_of_nonneg_right (mul_nonneg
        (zero_lt_one.trans_le Q.range_parameter).le (Real.sqrt_nonneg _))).trans (ha i)

namespace C1SublinearScalarScaling

/-- Smooth scalar representatives with equal coordinate derivatives almost
everywhere differ by one spatial constant. -/
theorem smooth_eq_add_of_ae_fderiv_eq {d : ℕ} {u v : Vec d → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (h : ∀ᵐ x ∂(volume : Measure (Vec d)), ∀ j : Fin d,
      fderiv ℝ u x (unitVector j) = fderiv ℝ v x (unitVector j)) :
    ∃ c : ℝ, ∀ x, u x = v x + c := by
  have he : fderiv ℝ u = fderiv ℝ v := by
    apply Measure.eq_of_ae_eq (μ := (volume : Measure (Vec d))) ?_
      (hu.continuous_fderiv (by simp)) (hv.continuous_fderiv (by simp))
    filter_upwards [h] with x hx
    apply ContinuousLinearMap.ext
    intro y
    have hy : y = ∑ j : Fin d, y j • unitVector j := by
      ext k
      simp [unitVector, Finset.sum_apply, Pi.single_apply]
    rw [hy, map_sum, map_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [map_smul, map_smul, hx j]
  obtain ⟨c, hc⟩ := isOpen_univ.exists_eq_add_of_fderiv_eq isPreconnected_univ
    (hu.differentiable (by simp)).differentiableOn
    (hv.differentiable (by simp)).differentiableOn
    (fun x _ => congrFun he x)
  exact ⟨c, fun x => hc (Set.mem_univ x)⟩

/-- Only the gradient is stationary: translating a smooth selected scalar
representative changes it by a sample-dependent additive constant. -/
theorem scalar_translate_gauge {d : ℕ} {L r : ℝ} (Q : EnvironmentLaw d L r)
    (u : Fin d → FieldPair d → Vec d → ℝ)
    (hu : ∀ᵐ ρ ∂reducedLaw Q, ∀ i : Fin d,
      ContDiff ℝ (⊤ : ℕ∞) (u i ρ) ∧
      ∀ᵐ x ∂(volume : Measure (Vec d)), ∀ j : Fin d,
        fderiv ℝ (u i ρ) x (unitVector j) =
          correctorGradient Q i (translate x ρ) j)
    (z : Vec d) :
    ∀ᵐ ρ ∂reducedLaw Q, ∀ i : Fin d, ∃ c : ℝ,
      ∀ x, u i ρ (x + z) = u i (translate z ρ) x + c := by
  have hz := (measurePreserving_translate (reducedLaw Q)
    (reducedLaw_stationary Q) z).quasiMeasurePreserving.ae hu
  filter_upwards [hu, hz] with ρ hρ hρz
  intro i
  apply smooth_eq_add_of_ae_fderiv_eq
    ((hρ i).1.comp (contDiff_id.add contDiff_const)) (hρz i).1
  have hx := (measurePreserving_add_right (volume : Measure (Vec d)) z).quasiMeasurePreserving.ae
    (hρ i).2
  filter_upwards [hx, (hρz i).2] with x hx hxz
  intro j
  change fderiv ℝ (fun y => u i ρ (y + z)) x (unitVector j) =
    fderiv ℝ (u i (translate z ρ)) x (unitVector j)
  rw [fderiv_comp_add_right, hx j, hxz j, translate_add]

/-- Move a scalar oscillation event to any center without losing exceptional
probability; the representative is fixed before the center and radius. -/
theorem centered_scalar_event {d : ℕ} {L r : ℝ} (Q : EnvironmentLaw d L r)
    (u : Fin d → FieldPair d → Vec d → ℝ)
    (hu : ∀ᵐ ρ ∂reducedLaw Q, ∀ i : Fin d,
      ContDiff ℝ (⊤ : ℕ∞) (u i ρ) ∧
      ∀ᵐ x ∂(volume : Measure (Vec d)), ∀ j : Fin d,
        fderiv ℝ (u i ρ) x (unitVector j) =
          correctorGradient Q i (translate x ρ) j)
    (z : Vec d) (R K : ℝ) (T : ℝ≥0∞)
    (E : Set (FieldPair d)) (hE : MeasurableSet E)
    (hEtail : reducedLaw Q Eᶜ ≤ T)
    (hEosc : ∀ ρ ∈ E, ∃ a : Fin d → ℝ, ∀ i : Fin d,
      Real.sqrt (⨍ x in ball 0 R, |u i ρ x - a i| ^ 2) ≤ K) :
    ∃ F : Set (FieldPair d), MeasurableSet F ∧ reducedLaw Q Fᶜ ≤ T ∧
      ∀ ρ ∈ F, ∃ a : Fin d → ℝ, ∀ i : Fin d,
        Real.sqrt (⨍ x in ball z R, |u i ρ x - a i| ^ 2) ≤ K := by
  obtain ⟨G, hG, hGnull, hGprop⟩ :=
    measurable_common_event _ _ (scalar_translate_gauge Q u hu z)
  let F := G ∩ (translate z) ⁻¹' E
  have hmp := measurePreserving_translate (reducedLaw Q) (reducedLaw_stationary Q) z
  refine ⟨F, hG.inter (hE.preimage hmp.measurable), ?_, ?_⟩
  · calc
      _ = reducedLaw Q (Gᶜ ∪ (translate z) ⁻¹' Eᶜ) := by
        congr 1
        exact Set.compl_inter _ _
      _ ≤ reducedLaw Q Gᶜ + reducedLaw Q ((translate z) ⁻¹' Eᶜ) := measure_union_le _ _
      _ = reducedLaw Q Eᶜ := by
        rw [hGnull, zero_add, hmp.measure_preimage hE.compl.nullMeasurableSet]
      _ ≤ T := hEtail
  · intro ρ hρ
    obtain ⟨a, ha⟩ := hEosc _ hρ.2
    choose c hc using hGprop ρ hρ.1
    refine ⟨fun i => a i + c i, ?_⟩
    intro i
    have hi : (fun x => |u i ρ (x + z) - (a i + c i)| ^ 2) =
        (fun x => |u i (translate z ρ) x - a i| ^ 2) := by
      funext x
      rw [hc i x, add_sub_add_right_eq_sub]
    rw [setAverage_ball_translation, hi]
    exact ha i

end C1SublinearScalarScaling

/-- The same selected source pair and reduced scalar representatives satisfy
the scalar oscillation estimate at every spatial center. -/
theorem exists_sourcePairs_centered_scalar
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ β C Cs : ℝ, 0 < β ∧ 0 < C ∧ 0 < Cs ∧
      ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange),
        HasSmoothBounds D Q →
        ∃ φ : (i : Fin d) →
            Corrector (actualCoefficientLaw Q) (correctorUnitVector i).ofLp,
          ∃ _S : (i : Fin d) → FluxCorrector (φ i),
          ∃ u : Fin d → FieldPair d → Vec d → ℝ,
            (∀ᵐ ω ∂physicalReferenceLaw Q, ∀ i : Fin d,
              u i (reduce ω.1) =ᵐ[(volume : Measure (Vec d))]
                C1SublinearScalarScaling.physicalPotential D.dependenceRange
                  ((φ i).potential (project (r₀ := D.dependenceRange)
                    Q.ellipticity_parameter ω))) ∧
            (∀ᵐ ρ ∂reducedLaw Q, ∀ i : Fin d,
              ContDiff ℝ (⊤ : ℕ∞) (u i ρ) ∧
              ∀ᵐ x ∂(volume : Measure (Vec d)), ∀ j : Fin d,
                fderiv ℝ (u i ρ) x (unitVector j) =
                  correctorGradient Q i (translate x ρ) j) ∧
            ∀ R : ℝ, 0 ≤ R → ∀ z : Vec d,
              ∃ E : Set (FieldPair d), MeasurableSet E ∧
                reducedLaw Q Eᶜ ≤ (d : ℝ≥0∞) * ENNReal.ofReal
                  (2 * Real.exp (-((Cs⁻¹ * R) ^ ((d : ℝ) / 2)))) ∧
                ∀ ρ ∈ E, ∃ a : Fin d → ℝ, ∀ i : Fin d,
                  Real.sqrt (⨍ x in ball z (D.dependenceRange * R),
                    |u i ρ x - a i| ^ 2) ≤
                      D.dependenceRange * C *
                        R ^ (1 - β * ((d : ℝ) - (d : ℝ) / 2)) := by
  obtain ⟨β, C, Cs, hβ, hC, hCs, hpairs⟩ :=
    exists_sourcePairs_reduced_scalar d hd D
  refine ⟨β, C, Cs, hβ, hC, hCs, ?_⟩
  intro Q hQ
  obtain ⟨φ, S, u, hclass, hu, hosc⟩ := hpairs Q hQ
  refine ⟨φ, S, u, hclass, hu, ?_⟩
  intro R hR z
  obtain ⟨E, hE, hEtail, hEosc⟩ := hosc R hR
  exact C1SublinearScalarScaling.centered_scalar_event Q u hu z _ _ _ E hE hEtail hEosc

namespace C1SublinearScalarScaling

/-- Choose the radius and tail constants before the environment law. -/
theorem exists_scalar_normalization (d : ℕ) (hd : 2 ≤ d)
    (r₀ β C Cs : ℝ) (hr₀ : 1 ≤ r₀) (hβ : 0 < β)
    (hC : 0 < C) (hCs : 0 < Cs) :
    ∃ κ A a c : ℝ, 0 < κ ∧ κ < 1 / 2 ∧ 1 ≤ A ∧ 0 < a ∧ 0 < c ∧
      A = r₀ * a ∧ ∀ r : ℝ, 1 ≤ r →
        (d : ℝ) * r₀ * C * (a * r) ^ (1 - β * ((d : ℝ) - (d : ℝ) / 2)) ≤
          A * r ^ (1 - κ) ∧
        (d : ℝ) * (2 * Real.exp (-((Cs⁻¹ * (a * r)) ^ ((d : ℝ) / 2)))) ≤
          A * Real.exp (-c * r ^ ((d : ℝ) / 2)) := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  let κ : ℝ := min (β * (d : ℝ) / 2) (1 / 4)
  have hκ : 0 < κ := lt_min (by positivity) (by norm_num)
  have hκβ : κ ≤ β * (d : ℝ) / 2 := min_le_left _ _
  have hκhalf : κ < 1 / 2 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  let a : ℝ := max 1 (max (2 * (d : ℝ)) (((d : ℝ) * C) ^ κ⁻¹))
  have ha1 : 1 ≤ a := le_max_left _ _
  have ha : 0 < a := lt_of_lt_of_le zero_lt_one ha1
  have had : 2 * (d : ℝ) ≤ a := (le_max_left _ _).trans (le_max_right _ _)
  have hap : ((d : ℝ) * C) ^ κ⁻¹ ≤ a :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hpow : (d : ℝ) * C ≤ a ^ κ := by
    simpa only [Real.rpow_inv_rpow (by positivity : 0 ≤ (d : ℝ) * C) hκ.ne'] using
      Real.rpow_le_rpow (by positivity) hap hκ.le
  have hcoef : (d : ℝ) * C * a ^ (1 - κ) ≤ a := by
    calc
      _ ≤ a ^ κ * a ^ (1 - κ) := mul_le_mul_of_nonneg_right hpow (by positivity)
      _ = a := by rw [← Real.rpow_add ha, show κ + (1 - κ) = 1 by ring, Real.rpow_one]
  have hr₀pos : 0 < r₀ := lt_of_lt_of_le zero_lt_one hr₀
  have haA : a ≤ r₀ * a := by nlinarith
  have hA : 1 ≤ r₀ * a := ha1.trans haA
  refine ⟨κ, r₀ * a, a, (Cs⁻¹ * a) ^ ((d : ℝ) / 2),
    hκ, hκhalf, hA, ha, by positivity, rfl, ?_⟩
  intro r hr
  have hrpos : 0 ≤ r := le_trans zero_le_one hr
  have har : 1 ≤ a * r := by nlinarith
  constructor
  · have hexp : 1 - β * ((d : ℝ) - (d : ℝ) / 2) ≤ 1 - κ := by linarith
    calc
      _ ≤ (d : ℝ) * r₀ * C * (a * r) ^ (1 - κ) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le har hexp)
          (by positivity)
      _ = r₀ * ((d : ℝ) * C * a ^ (1 - κ)) * r ^ (1 - κ) := by
        rw [Real.mul_rpow ha.le hrpos]; ring
      _ ≤ r₀ * a * r ^ (1 - κ) := by gcongr
  · have htail : 2 * (d : ℝ) ≤ r₀ * a := had.trans haA
    have heq : (Cs⁻¹ * (a * r)) ^ ((d : ℝ) / 2) =
        (Cs⁻¹ * a) ^ ((d : ℝ) / 2) * r ^ ((d : ℝ) / 2) := by
      rw [← mul_assoc, Real.mul_rpow (by positivity) hrpos]
    rw [heq]
    simpa only [mul_assoc, mul_left_comm, neg_mul] using
      mul_le_mul_of_nonneg_right htail
        (Real.exp_nonneg (-((Cs⁻¹ * a) ^ ((d : ℝ) / 2) * r ^ ((d : ℝ) / 2))))

end C1SublinearScalarScaling

/-- The scalar oscillation bound with the root radius, sum and tail normalization. -/
theorem exists_sourcePairs_normalized_scalar
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ κ C c : ℝ, 0 < κ ∧ κ < 1 / 2 ∧ 1 ≤ C ∧ 0 < c ∧
      ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange),
        HasSmoothBounds D Q →
        ∃ φ : (i : Fin d) →
            Corrector (actualCoefficientLaw Q) (correctorUnitVector i).ofLp,
          ∃ _S : (i : Fin d) → FluxCorrector (φ i),
          ∃ u : Fin d → FieldPair d → Vec d → ℝ,
            (∀ᵐ ω ∂physicalReferenceLaw Q, ∀ i : Fin d,
              u i (reduce ω.1) =ᵐ[(volume : Measure (Vec d))]
                C1SublinearScalarScaling.physicalPotential D.dependenceRange
                  ((φ i).potential (project (r₀ := D.dependenceRange)
                    Q.ellipticity_parameter ω))) ∧
            (∀ᵐ ρ ∂reducedLaw Q, ∀ i : Fin d,
              ContDiff ℝ (⊤ : ℕ∞) (u i ρ) ∧
              ∀ᵐ x ∂(volume : Measure (Vec d)), ∀ j : Fin d,
                fderiv ℝ (u i ρ) x (unitVector j) =
                  correctorGradient Q i (translate x ρ) j) ∧
            ∀ r : ℝ, 1 ≤ r → ∀ z : Vec d,
              ∃ E : Set (FieldPair d), MeasurableSet E ∧
                reducedLaw Q Eᶜ ≤ ENNReal.ofReal
                  (C * Real.exp (-c * r ^ ((d : ℝ) / 2))) ∧
                ∀ ρ ∈ E, ∃ a : Fin d → ℝ,
                  let B := {x : Vec d | euclideanNorm (x - z) < C * r}
                  (∑ i : Fin d, Real.sqrt ((volume B).toReal⁻¹ *
                    ∫ x in B, |u i ρ x - a i| ^ 2)) ≤ C * r ^ (1 - κ) := by
  obtain ⟨β, C, Cs, hβ, hC, hCs, hpairs⟩ :=
    exists_sourcePairs_centered_scalar d hd D
  obtain ⟨κ, A, a, c, hκ, hκhalf, hA, ha, hc, hAa, hnorm⟩ :=
    C1SublinearScalarScaling.exists_scalar_normalization d hd
      D.dependenceRange β C Cs D.one_le_dependenceRange hβ hC hCs
  refine ⟨κ, A, c, hκ, hκhalf, hA, hc, ?_⟩
  intro Q hQ
  obtain ⟨φ, S, u, hclass, hu, hosc⟩ := hpairs Q hQ
  refine ⟨φ, S, u, hclass, hu, ?_⟩
  intro r hr z
  have hrpos : 0 ≤ r := le_trans zero_le_one hr
  obtain ⟨E, hE, hEtail, hEosc⟩ := hosc (a * r) (mul_nonneg ha.le hrpos) z
  obtain ⟨hsize, htail⟩ := hnorm r hr
  refine ⟨E, hE, hEtail.trans ?_, ?_⟩
  · calc
      _ = ENNReal.ofReal ((d : ℝ) *
          (2 * Real.exp (-((Cs⁻¹ * (a * r)) ^ ((d : ℝ) / 2))))) := by
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg d), ENNReal.ofReal_natCast]
      _ ≤ _ := ENNReal.ofReal_le_ofReal htail
  · intro ρ hρ
    obtain ⟨b, hb⟩ := hEosc ρ hρ
    refine ⟨b, ?_⟩
    have hrad : D.dependenceRange * (a * r) = A * r := by rw [hAa]; ring
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hb i)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
    have hsum' : (∑ i : Fin d, Real.sqrt
        (⨍ x in ball z (A * r), |u i ρ x - b i| ^ 2)) ≤ A * r ^ (1 - κ) := by
      rw [hrad] at hsum
      exact hsum.trans (by convert hsize using 1; ring)
    simpa only [ball, setAverage_eq, measureReal_def, smul_eq_mul] using hsum'

namespace C1SublinearScalarScaling

/-- The actual source skew potential in physical spatial coordinates. -/
def physicalSkew {d : ℕ} (r : ℝ) (v : Vec d → Mat d) (x : Vec d) : Mat d :=
  r • v (r⁻¹ • x)

/-- Extend the raw physical skew field along the same injective reduction map. -/
def reducedSkew {d : ℕ} {L : ℝ}
    (v : PhysicalField d L → Vec d → Mat d) : FieldPair d → Vec d → Mat d :=
  Function.extend (fun ω : PhysicalField d L => reduce ω.1) v (fun _ _ => 0)

theorem reducedSkew_reduce {d : ℕ} {L : ℝ}
    (v : PhysicalField d L → Vec d → Mat d) (ω : PhysicalField d L) :
    reducedSkew v (reduce ω.1) = v ω :=
  (measurableEmbedding_physicalReduce L).injective.extend_apply _ _ _

/-- The Frobenius oscillation scales with precisely the physical range. -/
theorem physicalSkew_rms {d : ℕ} (v : Vec d → Mat d)
    (b : Mat d) (r R : ℝ) (hr : 0 < r) (hR : 0 < R) :
    Real.sqrt (⨍ x in ball 0 (r * R),
      frobeniusNorm (physicalSkew r v x - r • b) ^ 2) =
        r * Real.sqrt (⨍ y in ball 0 R, frobeniusNorm (v y - b) ^ 2) := by
  have hi (y : Vec d) :
      frobeniusNorm (physicalSkew r v (r • y) - r • b) ^ 2 =
        r ^ 2 * frobeniusNorm (v y - b) ^ 2 := by
    simp only [physicalSkew, smul_smul, inv_mul_cancel₀ hr.ne', one_smul,
      ← smul_sub]
    rw [frobeniusNorm_smul, mul_pow, sq_abs]
  rw [← setAverage_euclideanBall_smul
    (fun x => frobeniusNorm (physicalSkew r v x - r • b) ^ 2) r R hr hR]
  simp_rw [hi]
  rw [average_const_mul, Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq hr.le]

/-- Equal weak gradients determine a scalar potential up to an AE constant. -/
theorem weak_eq_add_of_ae_gradient_eq {d : ℕ} (hd : 0 < d)
    {u v : Vec d → ℝ} {G H : Vec d → Vec d}
    (hu : HasWeakGradient Set.univ u G) (hv : HasWeakGradient Set.univ v H)
    (hGH : G =ᵐ[(volume : Measure (Vec d))] H) :
    ∃ c : ℝ, u =ᵐ[(volume : Measure (Vec d))] (fun x => v x + c) := by
  have hv' : HasWeakGradient Set.univ v G := by
    apply hasWeakGradient_congr_ae isOpen_univ hv (ae_eq_refl _)
    simpa only [Measure.restrict_univ] using hGH.symm
  have hw := hasWeakGradient_sub hu hv'
  have hl : LocallyIntegrable (fun x => u x - v x) volume :=
    locallyIntegrableOn_univ.mp (hw ⟨0, hd⟩).1
  obtain ⟨c, hc⟩ := EinsteinRelation.ae_eq_const_of_zero_weak_gradient hl
    (fun j ψ hψ => by
      have h := (hw j).2.2 ψ hψ
      simpa only [Measure.restrict_univ, Pi.sub_apply, sub_self,
        zero_mul, integral_zero, neg_zero] using h)
  refine ⟨c, ?_⟩
  filter_upwards [hc] with x hx
  change u x - v x = c at hx
  linarith

/-- The selected source skew potential is covariant up to a spatial matrix
constant, retaining the physical AE class and every real translation. -/
theorem physicalSkew_translate_gauge {d : ℕ} [Fact (2 ≤ d)] {L r : ℝ}
    (Q : EnvironmentLaw d L r) (i : Fin d)
    {φ : Corrector (actualCoefficientLaw Q) (correctorUnitVector i).ofLp}
    (S : FluxCorrector φ) (z : Vec d) :
    ∀ᵐ ω ∂physicalReferenceLaw Q, ∃ b : Mat d,
      (fun x => physicalSkew r (S.potential
        (project (r₀ := r) Q.ellipticity_parameter ω)) (x + z)) =ᵐ[volume]
      (fun x => physicalSkew r (S.potential
        (project (r₀ := r) Q.ellipticity_parameter (physicalTranslate z ω))) x + b) := by
  have hr : 0 < r := zero_lt_one.trans_le Q.range_parameter
  have hd : 0 < d := lt_of_lt_of_le (by omega : 0 < 2) Fact.out
  have hmp : MeasurePreserving (physicalTranslate z)
      (physicalReferenceLaw Q) (physicalReferenceLaw Q) :=
    ⟨measurable_physicalTranslate _, physicalReferenceLaw_translation_invariant Q _⟩
  have hw := (measurePreserving_akmProject Q).quasiMeasurePreserving.ae S.weak_gradient
  have hcov := c6_actualSourceFluxGradient_real_covariant Q i S (r⁻¹ • z)
  have hcancel : r • (r⁻¹ • z) = z := by
    rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  simp only [hcancel] at hcov
  filter_upwards [hw, hmp.quasiMeasurePreserving.ae hw, hcov] with ω hω hzω hgrad
  have hc (j k : Fin d) : ∃ c : ℝ,
      (fun x => S.potential (project (r₀ := r) Q.ellipticity_parameter ω)
        (x + r⁻¹ • z) j k) =ᵐ[volume]
      (fun x => S.potential (project (r₀ := r) Q.ellipticity_parameter
        (physicalTranslate z ω)) x j k + c) := by
    have hwt := (hω j k).comp_add_left (r⁻¹ • z)
    simp only [add_comm (r⁻¹ • z)] at hwt
    apply weak_eq_add_of_ae_gradient_eq hd hwt (hzω j k)
    filter_upwards [hgrad] with x hx
    exact funext fun l => hx j k l
  choose c hc using hc
  have hc' : ∀ᵐ x ∂(volume : Measure (Vec d)), ∀ j k,
      S.potential (project (r₀ := r) Q.ellipticity_parameter ω)
        (x + r⁻¹ • z) j k =
      S.potential (project (r₀ := r) Q.ellipticity_parameter
        (physicalTranslate z ω)) x j k + c j k :=
    ae_all_iff.mpr fun j => ae_all_iff.mpr fun k => hc j k
  have hdil := (Measure.quasiMeasurePreserving_smul (volume : Measure (Vec d))
    (inv_ne_zero hr.ne')).ae hc'
  refine ⟨r • (Matrix.of c), ?_⟩
  filter_upwards [hdil] with x hx
  ext j k
  simp only [physicalSkew, smul_add, Matrix.smul_apply, smul_eq_mul,
    Matrix.add_apply, Matrix.of_apply, hx j k, mul_add]

/-- The raw reduced skew representative uses the selected source potential. -/
def sourceReducedSkew {d : ℕ} {L r : ℝ} (Q : EnvironmentLaw d L r)
    {i : Fin d}
    {φ : Corrector (actualCoefficientLaw Q) (correctorUnitVector i).ofLp}
    (S : FluxCorrector φ) : FieldPair d → Vec d → Mat d :=
  reducedSkew fun ω => physicalSkew r
    (S.potential (project (r₀ := r) Q.ellipticity_parameter ω))

/-- The reduced raw representative inherits the same matrix gauge. -/
theorem sourceReducedSkew_translate_gauge {d : ℕ} [Fact (2 ≤ d)] {L r : ℝ}
    (Q : EnvironmentLaw d L r) (i : Fin d)
    {φ : Corrector (actualCoefficientLaw Q) (correctorUnitVector i).ofLp}
    (S : FluxCorrector φ) (z : Vec d) :
    ∀ᵐ ρ ∂reducedLaw Q, ∃ b : Mat d,
      (fun x => sourceReducedSkew Q S ρ (x + z)) =ᵐ[volume]
        (fun x => sourceReducedSkew Q S (translate z ρ) x + b) := by
  rw [← map_physicalReduce Q, (measurableEmbedding_physicalReduce L).ae_map_iff]
  filter_upwards [physicalSkew_translate_gauge Q i S z] with ω hω
  have ht : translate z (reduce ω.1) = reduce (physicalTranslate z ω).1 := by
    exact (reduce_translate ω.1 z).symm
  simpa only [sourceReducedSkew, ht, reducedSkew_reduce] using hω

/-- Scalar and matrix gauges move one joint event to any spatial center
without any change in its exceptional probability. -/
theorem centered_joint_event {d : ℕ} {L r : ℝ} (Q : EnvironmentLaw d L r)
    (u : Fin d → FieldPair d → Vec d → ℝ)
    (v : Fin d → FieldPair d → Vec d → Mat d)
    (hu : ∀ᵐ ρ ∂reducedLaw Q, ∀ i : Fin d,
      ContDiff ℝ (⊤ : ℕ∞) (u i ρ) ∧
      ∀ᵐ x ∂(volume : Measure (Vec d)), ∀ j : Fin d,
        fderiv ℝ (u i ρ) x (unitVector j) =
          correctorGradient Q i (translate x ρ) j)
    (z : Vec d)
    (hv : ∀ᵐ ρ ∂reducedLaw Q, ∀ i : Fin d, ∃ b : Mat d,
      (fun x => v i ρ (x + z)) =ᵐ[volume]
        (fun x => v i (translate z ρ) x + b))
    (R K : ℝ) (T : ℝ≥0∞)
    (E : Set (FieldPair d)) (hE : MeasurableSet E)
    (hEtail : reducedLaw Q Eᶜ ≤ T)
    (hEosc : ∀ ρ ∈ E, ∃ a : Fin d → ℝ, ∃ b : Fin d → Mat d, ∀ i,
      Real.sqrt (⨍ x in ball 0 R, |u i ρ x - a i| ^ 2) +
        Real.sqrt (⨍ x in ball 0 R, frobeniusNorm (v i ρ x - b i) ^ 2) ≤ K) :
    ∃ F : Set (FieldPair d), MeasurableSet F ∧ reducedLaw Q Fᶜ ≤ T ∧
      ∀ ρ ∈ F, ∃ a : Fin d → ℝ, ∃ b : Fin d → Mat d, ∀ i,
        Real.sqrt (⨍ x in ball z R, |u i ρ x - a i| ^ 2) +
          Real.sqrt (⨍ x in ball z R, frobeniusNorm (v i ρ x - b i) ^ 2) ≤ K := by
  obtain ⟨G, hG, hGnull, hGprop⟩ := measurable_common_event _ _
    ((scalar_translate_gauge Q u hu z).and hv)
  let F := G ∩ (translate z) ⁻¹' E
  have hmp := measurePreserving_translate (reducedLaw Q) (reducedLaw_stationary Q) z
  refine ⟨F, hG.inter (hE.preimage hmp.measurable), ?_, ?_⟩
  · calc
      _ = reducedLaw Q (Gᶜ ∪ (translate z) ⁻¹' Eᶜ) := by
        congr 1
        exact Set.compl_inter _ _
      _ ≤ reducedLaw Q Gᶜ + reducedLaw Q ((translate z) ⁻¹' Eᶜ) := measure_union_le _ _
      _ = reducedLaw Q Eᶜ := by
        rw [hGnull, zero_add, hmp.measure_preimage hE.compl.nullMeasurableSet]
      _ ≤ T := hEtail
  · intro ρ hρ
    obtain ⟨a, b, hab⟩ := hEosc _ hρ.2
    choose c hc using (hGprop ρ hρ.1).1
    choose B hB using (hGprop ρ hρ.1).2
    refine ⟨fun i => a i + c i, fun i => b i + B i, ?_⟩
    intro i
    have hi : (fun x => |u i ρ (x + z) - (a i + c i)| ^ 2) =
        (fun x => |u i (translate z ρ) x - a i| ^ 2) := by
      funext x
      rw [hc i x, add_sub_add_right_eq_sub]
    have hmat : (⨍ x in ball 0 R,
        frobeniusNorm (v i ρ (x + z) - (b i + B i)) ^ 2) =
        (⨍ x in ball 0 R, frobeniusNorm (v i (translate z ρ) x - b i) ^ 2) := by
      apply average_congr
      filter_upwards [ae_restrict_of_ae (hB i)] with x hx
      rw [hx, add_sub_add_right_eq_sub]
    have hs : (⨍ x in ball z R, |u i ρ x - (a i + c i)| ^ 2) =
        (⨍ x in ball 0 R, |u i (translate z ρ) x - a i| ^ 2) := by
      rw [setAverage_ball_translation, hi]
    have hm : (⨍ x in ball z R, frobeniusNorm (v i ρ x - (b i + B i)) ^ 2) =
        (⨍ x in ball 0 R, frobeniusNorm (v i (translate z ρ) x - b i) ^ 2) := by
      rw [setAverage_ball_translation, hmat]
    rw [hs, hm]
    exact hab i

end C1SublinearScalarScaling

/-- The same source pair has joint scalar and Frobenius oscillations on one
measurable event at every center and radius, in its exact physical AE class. -/
theorem exists_sourcePairs_normalized_joint_class
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ κ C c : ℝ, 0 < κ ∧ κ < 1 / 2 ∧ 1 ≤ C ∧ 0 < c ∧
      ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange),
        HasSmoothBounds D Q →
        ∃ φ : (i : Fin d) →
            Corrector (actualCoefficientLaw Q) (correctorUnitVector i).ofLp,
          ∃ S : (i : Fin d) → FluxCorrector (φ i),
          ∃ u : Fin d → FieldPair d → Vec d → ℝ,
          ∃ v : Fin d → FieldPair d → Vec d → Mat d,
            (∀ᵐ ω ∂physicalReferenceLaw Q, ∀ i : Fin d,
              u i (reduce ω.1) =ᵐ[(volume : Measure (Vec d))]
                C1SublinearScalarScaling.physicalPotential D.dependenceRange
                  ((φ i).potential (project (r₀ := D.dependenceRange)
                    Q.ellipticity_parameter ω))) ∧
            (∀ᵐ ω ∂physicalReferenceLaw Q, ∀ i : Fin d,
              v i (reduce ω.1) =ᵐ[(volume : Measure (Vec d))]
                (fun x => D.dependenceRange • ((S i).potential
                  (project (r₀ := D.dependenceRange) Q.ellipticity_parameter ω)
                  (D.dependenceRange⁻¹ • x)))) ∧
            (∀ᵐ ρ ∂reducedLaw Q, ∀ i : Fin d,
              ContDiff ℝ (⊤ : ℕ∞) (u i ρ) ∧
              ∀ᵐ x ∂(volume : Measure (Vec d)), ∀ j : Fin d,
                fderiv ℝ (u i ρ) x (unitVector j) =
                  correctorGradient Q i (translate x ρ) j) ∧
            ∀ r : ℝ, 1 ≤ r → ∀ z : Vec d,
              ∃ E : Set (FieldPair d), MeasurableSet E ∧
                reducedLaw Q Eᶜ ≤ ENNReal.ofReal
                  (C * Real.exp (-c * r ^ ((d : ℝ) / 2))) ∧
                ∀ ρ ∈ E, ∃ a : Fin d → ℝ, ∃ b : Fin d → Mat d,
                  let B := {x : Vec d | euclideanNorm (x - z) < C * r}
                  (∑ i : Fin d, (Real.sqrt ((volume B).toReal⁻¹ *
                    ∫ x in B, |u i ρ x - a i| ^ 2) +
                    Real.sqrt ((volume B).toReal⁻¹ *
                      ∫ x in B, frobeniusNorm (v i ρ x - b i) ^ 2))) ≤ C * r ^ (1 - κ) := by
  classical
  let : Fact (2 ≤ d) := ⟨hd⟩
  obtain ⟨β, C, Cs, hβ, hC, hCs, hpairs⟩ :=
    exists_sourcePairs_physical_scalar d hd D
  obtain ⟨κ, A, a, c, hκ, hκhalf, hA, ha, hc, hAa, hnorm⟩ :=
    C1SublinearScalarScaling.exists_scalar_normalization d hd
      D.dependenceRange β C Cs D.one_le_dependenceRange hβ hC hCs
  refine ⟨κ, A, c, hκ, hκhalf, hA, hc, ?_⟩
  intro Q hQ
  obtain ⟨φ, S, X, hX, hp⟩ := hpairs Q hQ
  obtain ⟨B, hB, hBnull, hBp⟩ :=
    C1SublinearScalarScaling.measurable_common_event _ _ hp
  let w : PhysicalField d D.ellipticity → Fin d → Vec d → ℝ := fun ω i =>
    if h : ω ∈ B then Classical.choose (hBp ω h i) else fun _ => 0
  have hw (ω : PhysicalField d D.ellipticity) (hω : ω ∈ B) (i : Fin d) :=
    Classical.choose_spec (hBp ω hω i)
  have hw_eq (ω : PhysicalField d D.ellipticity) (hω : ω ∈ B) (i : Fin d) :
      w ω i = Classical.choose (hBp ω hω i) := dite_eq_left hω
  let u : Fin d → FieldPair d → Vec d → ℝ := fun i =>
    C1SublinearScalarScaling.reducedPotential (fun ω => w ω i)
  let v : Fin d → FieldPair d → Vec d → Mat d := fun i =>
    C1SublinearScalarScaling.sourceReducedSkew Q (S i)
  have hu_eq (ω : PhysicalField d D.ellipticity) (i : Fin d) :
      u i (reduce ω.1) = w ω i :=
    C1SublinearScalarScaling.reducedPotential_reduce _ _
  have hv_eq (ω : PhysicalField d D.ellipticity) (i : Fin d) :
      v i (reduce ω.1) = C1SublinearScalarScaling.physicalSkew D.dependenceRange
        ((S i).potential (project (r₀ := D.dependenceRange) Q.ellipticity_parameter ω)) :=
    C1SublinearScalarScaling.reducedSkew_reduce _ _
  have hBae : ∀ᵐ ω ∂physicalReferenceLaw Q, ω ∈ B := ae_iff.mpr hBnull
  have hu : ∀ᵐ ρ ∂reducedLaw Q, ∀ i : Fin d,
      ContDiff ℝ (⊤ : ℕ∞) (u i ρ) ∧
      ∀ᵐ x ∂(volume : Measure (Vec d)), ∀ j : Fin d,
        fderiv ℝ (u i ρ) x (unitVector j) =
          correctorGradient Q i (translate x ρ) j := by
    let p : FieldPair d → Prop := fun ρ => ∀ i : Fin d,
      ContDiff ℝ (⊤ : ℕ∞) (u i ρ) ∧
      ∀ᵐ x ∂(volume : Measure (Vec d)), ∀ j : Fin d,
        fderiv ℝ (u i ρ) x (unitVector j) =
          correctorGradient Q i (translate x ρ) j
    change ∀ᵐ ρ ∂reducedLaw Q, p ρ
    rw [← C1SublinearScalarScaling.map_physicalReduce Q,
      (C1SublinearScalarScaling.measurableEmbedding_physicalReduce
        D.ellipticity).ae_map_iff]
    filter_upwards [hBae] with ω hω
    intro i
    rw [hu_eq, hw_eq ω hω i]
    exact ⟨(hw ω hω i).1, (hw ω hω i).2.2.1⟩
  refine ⟨φ, S, u, v, ?_, ?_, hu, ?_⟩
  · filter_upwards [hBae] with ω hω
    intro i
    rw [hu_eq, hw_eq ω hω i]
    exact (hw ω hω i).2.1
  · exact Filter.Eventually.of_forall fun ω i => by rw [hv_eq]; exact ae_eq_refl _
  · intro r hr z
    have hrpos : 0 < r := zero_lt_one.trans_le hr
    have hRpos : 0 < a * r := mul_pos ha hrpos
    have hr₀ : 0 < D.dependenceRange := zero_lt_one.trans_le Q.range_parameter
    obtain ⟨E, hE, hEtail, hEp⟩ :=
      C1SublinearScalarScaling.exists_reduced_radius_event Q
        (fun ω => ω ∈ B) hBae X (fun i => (hX i).2) (a * r) hRpos.le
    have hEosc : ∀ ρ ∈ E, ∃ b : Fin d → ℝ, ∃ M : Fin d → Mat d, ∀ i,
        Real.sqrt (⨍ x in ball 0 (D.dependenceRange * (a * r)),
          |u i ρ x - b i| ^ 2) +
        Real.sqrt (⨍ x in ball 0 (D.dependenceRange * (a * r)),
          frobeniusNorm (v i ρ x - M i) ^ 2) ≤
          D.dependenceRange * C *
            (a * r) ^ (1 - β * ((d : ℝ) - (d : ℝ) / 2)) := by
      intro ρ hρ
      obtain ⟨ω, rfl, hω, hrad⟩ := hEp ρ hρ
      have hosc (i : Fin d) := (hw ω hω i).2.2.2.2 (a * r) (hrad i)
      choose b hb using hosc
      let M : Fin d → Mat d := fun i => Matrix.of fun j k =>
        ⨍ x in ball 0 (a * r), (S i).potential
          (project (r₀ := D.dependenceRange) Q.ellipticity_parameter ω) x j k
      refine ⟨b, fun i => D.dependenceRange • M i, ?_⟩
      intro i
      rw [hu_eq, hw_eq ω hω i, hv_eq,
        C1SublinearScalarScaling.physicalSkew_rms _ _ _ _ hr₀ hRpos]
      exact hb i
    have hvgauge : ∀ᵐ ρ ∂reducedLaw Q, ∀ i : Fin d, ∃ b : Mat d,
        (fun x => v i ρ (x + z)) =ᵐ[volume]
          (fun x => v i (translate z ρ) x + b) :=
      ae_all_iff.mpr fun i =>
        C1SublinearScalarScaling.sourceReducedSkew_translate_gauge Q i (S i) z
    obtain ⟨F, hF, hFtail, hFosc⟩ :=
      C1SublinearScalarScaling.centered_joint_event Q u v hu z hvgauge
        (D.dependenceRange * (a * r)) _ _ E hE hEtail hEosc
    obtain ⟨hsize, htail⟩ := hnorm r hr
    refine ⟨F, hF, hFtail.trans ?_, ?_⟩
    · calc
        _ = ENNReal.ofReal ((d : ℝ) *
            (2 * Real.exp (-((Cs⁻¹ * (a * r)) ^ ((d : ℝ) / 2))))) := by
          rw [Fintype.card_fin, ENNReal.ofReal_mul (Nat.cast_nonneg d),
            ENNReal.ofReal_natCast]
        _ ≤ _ := ENNReal.ofReal_le_ofReal htail
    · intro ρ hρ
      obtain ⟨b, M, hb⟩ := hFosc ρ hρ
      refine ⟨b, M, ?_⟩
      have hrad : D.dependenceRange * (a * r) = A * r := by rw [hAa]; ring
      have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hb i)
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
      have hsum' : (∑ i : Fin d,
          (Real.sqrt (⨍ x in ball z (A * r), |u i ρ x - b i| ^ 2) +
          Real.sqrt (⨍ x in ball z (A * r), frobeniusNorm (v i ρ x - M i) ^ 2))) ≤
          A * r ^ (1 - κ) := by
        rw [hrad] at hsum
        exact hsum.trans (by convert hsize using 1; ring)
      simpa only [ball, setAverage_eq, measureReal_def, smul_eq_mul] using hsum'

end EinsteinFull.Blueprint
