import EinsteinRelation.Correctors.PhysicalAffineRegularity
import EinsteinRelation.Correctors.PairedCorrectorGradientMoments
import EinsteinRelation.Correctors.GradientCopyBoundedRadii
import EinsteinRelation.Correctors.PhysicalContinuousGradientIdentification

/-! # Sharp point-gradient decay for the actual canonical copies

Source: `paper/main.tex:852–867,878–886`. The actual continuous affine
solutions consume the checked stationary spatial energy estimate in AKM's
harmonic random-radius upgrade. Lemma 5.1 supplies higher point moments.
-/

open MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace EinsteinRelation.Correctors
open External.AKM External.GilbargTrudinger Environment.AKMTestIntegralSupport ReductionImageV3
open NormalizedSpatialRepresentativeSupport

attribute [local instance] ReductionImageV3.fieldPair_standardBorel
attribute [local irreducible] continuousCanonicalGradient
local instance pointRestrictionMeasurableSpace {d : ℕ} (U : Set (Vec d)) :
    MeasurableSpace C(U, Mat d) := borel C(U, Mat d)

/-- The actual paired affine solutions supply every local hypothesis of
AKM's harmonic upgrade. Source: `paper/main.tex:852–867,878–886`. -/
theorem actual_paired_affine_harmonic_data
    (hP : BallPoincareEstimate) (h836 : InteriorRegularRepresentative)
    {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀)
    (i : Fin d) (R : ℝ) (hR : 1 ≤ R) (y : Point d) :
    let K := AKMUpperEllipticity L
    let A := normalized_lipschitz_constant L r₀
    let g : PhysicalField d L → Vec d → Vec d := fun ω x =>
      continuousCanonicalGradient Q i (reduce ω.1) (r₀ • x)
    let φ : PhysicalField d L → Vec d → ℝ := fun ω x =>
      x i+r₀⁻¹*canonicalScalarRayPrimitive Q i (reduce ω.1) (r₀ • x)
    let a₁ : PhysicalField d L × PhysicalField d L → Coefficient d K := fun z =>
      project (r₀ := r₀) Q.ellipticity_parameter z.1
    let a₂ : PhysicalField d L × PhysicalField d L → Coefficient d K := fun z =>
      project (r₀ := r₀) Q.ellipticity_parameter z.2
    ∀ᵐ z ∂recenteredPhysicalCopyLaw Q (r₀*R) y,
      EqOn (fun x => a₁ z x) (fun x => a₂ z x) (originBall d (2*R)) ∧
      MemLp (φ z.1) 2 (volume.restrict (originBall d (2*R))) ∧
      MemLp (φ z.2) 2 (volume.restrict (originBall d (2*R))) ∧
      MemLp (fun x => euclideanNorm ((unitVector i+g z.1 x)-(unitVector i+g z.2 x))) 2
        (volume.restrict (originBall d (2*R))) ∧
      HasWeakGradient (originBall d (2*R)) (φ z.1) (fun x => unitVector i+g z.1 x) ∧
      HasWeakGradient (originBall d (2*R)) (φ z.2) (fun x => unitVector i+g z.2 x) ∧
      HasWeakDivergence (originBall d (2*R))
        (fun x => (a₁ z x).mulVec (0+(unitVector i+g z.1 x))) (fun _ => 0) ∧
      HasWeakDivergence (originBall d (2*R))
        (fun x => (a₂ z x).mulVec (0+(unitVector i+g z.2 x))) (fun _ => 0) ∧
      EllipticBound (ball 0 1) (a₁ z) K⁻¹ (((d:ℝ)+1)*K) ∧
      (∀ j k, HolderBound (ball 0 1) (1/2) (fun x => a₁ z x j k) (K+2*A)) ∧
      C1Alpha (ball 0 1) (1/2) (fun x => φ z.1 x-φ z.2 x)
        (fun x => (unitVector i+g z.1 x)-(unitVector i+g z.2 x)) := by
  dsimp only
  let K := AKMUpperEllipticity L
  let A := normalized_lipschitz_constant L r₀
  let g : PhysicalField d L → Vec d → Vec d := fun ω x =>
    continuousCanonicalGradient Q i (reduce ω.1) (r₀ • x)
  let φ : PhysicalField d L → Vec d → ℝ := fun ω x =>
    x i+r₀⁻¹*canonicalScalarRayPrimitive Q i (reduce ω.1) (r₀ • x)
  let a₁ : PhysicalField d L × PhysicalField d L → Coefficient d K := fun z =>
    project (r₀ := r₀) Q.ellipticity_parameter z.1
  let a₂ : PhysicalField d L × PhysicalField d L → Coefficient d K := fun z =>
    project (r₀ := r₀) Q.ellipticity_parameter z.2
  obtain ⟨_,_,hfst,hsnd,heq⟩ := recenteredPhysicalCopy_properties Q (r₀*R) y
  have hGc := (measurePreserving_physicalReduction Q).quasiMeasurePreserving.ae
    (ae_continuousCanonicalGradient hP h836 Q i)
  have hmeta := ae_physical_affine_corrector_regularity hP h836 Q i
  have hK0 : 0 < K := zero_lt_one.trans (one_lt_AKMUpperEllipticity Q.ellipticity_parameter)
  have hA : 0 ≤ A := by
    have hs := ellipticityScale_pos Q.ellipticity_parameter
    have hL0 : 0 ≤ L := zero_le_one.trans Q.ellipticity_parameter
    have hr0 : 0 ≤ r₀ := zero_le_one.trans Q.range_parameter
    dsimp [A,normalized_lipschitz_constant]
    positivity
  simp only [originBall_eq_gt_ball]
  filter_upwards [heq,hfst.quasiMeasurePreserving.ae hmeta,
    hsnd.quasiMeasurePreserving.ae hmeta,hfst.quasiMeasurePreserving.ae hGc,
    hsnd.quasiMeasurePreserving.ae hGc,
    hfst.quasiMeasurePreserving.ae (ae_project_operator_lipschitz Q)]
      with z hz h₁ h₂ hc₁ hc₂ hlip
  have h₁R := h₁ (2*R) (by linarith)
  have h₂R := h₂ (2*R) (by linarith)
  have hnormc : Continuous (fun x => euclideanNorm
      ((unitVector i+g z.1 x)-(unitVector i+g z.2 x))) := by
    have hg₁ : Continuous (g z.1) := hc₁.1.comp (continuous_const.smul continuous_id)
    have hg₂ : Continuous (g z.2) := hc₂.1.comp (continuous_const.smul continuous_id)
    simpa only [add_sub_add_left_eq_sub] using
      ((by unfold euclideanNorm euclideanSq dot; fun_prop :
        Continuous (fun x : Vec d => euclideanNorm x)).comp (hg₁.sub hg₂))
  have hell := project_isElliptic Q z.1
  have ham : Continuous (a₁ z).field := by
    change Continuous (fun x => ellipticityScale L • (reduce z.1.1).1 (r₀ • x))
    exact continuous_const.smul ((reduce z.1.1).1.continuous.comp (continuous_const.smul continuous_id))
  refine ⟨hz.mono ?_,h₁R.1.1,h₂R.1.1,
    continuous_memLp_euclideanBall _ hnormc _,h₁R.1.2.2.1,h₂R.1.2.2.1,
    by simpa only [zero_add] using h₁R.1.2.2.2,
    by simpa only [zero_add] using h₂R.1.2.2.2,
    ellipticBound_of_isElliptic hK0 hell (fun j k =>
      ((continuous_apply k).comp ((continuous_apply j).comp ham)).measurable) _,
    holderBound_half_of_isElliptic_lipschitz hK0 hA hell hlip,
    EinsteinRelation.Correctors.C1Alpha.sub (h₁ 1 zero_lt_one).2 (h₂ 1 zero_lt_one).2⟩
  intro x hx
  change euclideanNorm x < 8*(r₀*R)/r₀
  rw [show 8*(r₀*R)/r₀ = 8*R by field_simp [(zero_lt_one.trans_le Q.range_parameter).ne']]
  simp only [ball,mem_setOf_eq,sub_zero] at hx
  linarith

/-- Joint measurability of the actual continuous physical gradient.
Source: `paper/main.tex:852–867`. -/
theorem measurable_physical_continuous_gradient
    {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d) :
    Measurable (fun z : PhysicalField d L × Vec d =>
      continuousCanonicalGradient Q i (reduce z.1.1) z.2) := by
  have hin : Measurable (fun z : PhysicalField d L × Vec d => (reduce z.1.1,z.2)) :=
    (((measurePreserving_physicalReduction Q).measurable.comp measurable_fst).prodMk
      measurable_snd)
  change Measurable ((fun z : FieldPair d × Vec d =>
    continuousCanonicalGradient Q i z.1 z.2) ∘ (fun z : PhysicalField d L × Vec d =>
      (reduce z.1.1,z.2)))
  exact (measurable_continuousCanonicalGradient Q i).comp hin

/-- Exact transport to the actual continuous point-copy norm.
Source: `paper/main.tex:852–867,878–886`. -/
theorem continuous_gradient_copy_norm_eq
    (hP : BallPoincareEstimate) (h836 : InteriorRegularRepresentative)
    {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀)
    (i : Fin d) (R : ℝ) (y : Point d) (p : ℝ≥0∞) :
    eLpNorm (fun z : C(conditionalCorrectorBall R y, Mat d) ×
      (FieldPair d × FieldPair d) => euclideanNorm
        (conditionalCorrectorGradient Q i y z.2.1-conditionalCorrectorGradient Q i y z.2.2))
      p (reducedConditionalCopyLaw (reducedEnvironmentLaw Q) (conditionalCorrectorBall R y)) =
    eLpNorm (fun z : PhysicalField d L × PhysicalField d L => euclideanNorm
      (continuousCanonicalGradient Q i (reduce z.1.1) 0-
        continuousCanonicalGradient Q i (reduce z.2.1) 0)) p (recenteredPhysicalCopyLaw Q R y) := by
  have hGc := (measurePreserving_physicalReduction Q).quasiMeasurePreserving.ae
    (ae_continuousCanonicalGradient hP h836 Q i)
  exact eLpNorm_conditionalCopy_gradient_eq_physical_continuous_version Q i
    (fun ω x => continuousCanonicalGradient Q i (reduce ω.1) x)
    (measurable_physical_continuous_gradient Q i)
    (hGc.mono fun _ h => h.1) (hGc.mono fun _ h => h.2) R y p

/-- Lemma 5.1 point moments transfer to the actual physical coupling.
Source: `paper/main.tex:762–766,878–886`. -/
theorem physical_continuous_gradient_copy_moment
    (hP : BallPoincareEstimate) (h836 : InteriorRegularRepresentative)
    {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀)
    (i : Fin d) (p B R : ℝ) (y : Point d) (hp : 1 ≤ p) (hB : 0 ≤ B)
    (hb : eLpNorm (fun ω => euclideanNorm (conditionalCorrectorGradient Q i 0 ω))
      (ENNReal.ofReal p) (reducedEnvironmentLaw Q) ≤ ENNReal.ofReal B) :
    let Z := fun z : PhysicalField d L × PhysicalField d L => euclideanNorm
      (continuousCanonicalGradient Q i (reduce z.1.1) 0 -
        continuousCanonicalGradient Q i (reduce z.2.1) 0)
    MemLp Z (ENNReal.ofReal p) (recenteredPhysicalCopyLaw Q R y) ∧
      eLpNorm Z (ENNReal.ofReal p) (recenteredPhysicalCopyLaw Q R y) ≤
        ENNReal.ofReal (2*B) := by
  let Z := fun z : PhysicalField d L × PhysicalField d L => euclideanNorm
    (continuousCanonicalGradient Q i (reduce z.1.1) 0 -
      continuousCanonicalGradient Q i (reduce z.2.1) 0)
  have hzero : eLpNorm Z (ENNReal.ofReal p) (recenteredPhysicalCopyLaw Q R y) ≤
      ENNReal.ofReal (2*B) := by
    have hc := canonicalGradientCopy_moment_le Q i y (conditionalCorrectorBall R y)
      (isOpen_conditionalCorrectorBall _ _)
      (ENNReal.one_le_ofReal.mpr hp) hB hb
    rw [← continuous_gradient_copy_norm_eq hP h836 Q i R y (ENNReal.ofReal p)]
    exact hc.2
  have hZm : Measurable Z := by
    have hgm : Measurable (fun ω : PhysicalField d L => continuousCanonicalGradient Q i (reduce ω.1) 0) :=
      (measurable_physical_continuous_gradient Q i).comp
        (measurable_id.prodMk measurable_const)
    change Measurable (fun z : PhysicalField d L × PhysicalField d L => euclideanNorm
      (continuousCanonicalGradient Q i (reduce z.1.1) 0-continuousCanonicalGradient Q i (reduce z.2.1) 0))
    exact (by unfold euclideanNorm euclideanSq dot; fun_prop : Measurable (fun x : Vec d => euclideanNorm x)).comp
      ((hgm.comp measurable_fst).sub (hgm.comp measurable_snd))
  exact ⟨⟨hZm.aestronglyMeasurable,hzero.trans_lt ENNReal.ofReal_lt_top⟩,hzero⟩

/-- Sharp actual physical origin-copy decay, with the specified canonical
column flow. Stationary identification, time-zero energy, regularity and
spatial-energy decay are proved internally.
Source: `paper/main.tex:852–867,878–886`. -/
theorem actual_canonical_point_copy_decay
    (hdecay : ParabolicSemigroupKernelDecay) (hreg : ParabolicLargeScale)
    (hAKM : EllipticLargeScale) (hP : BallPoincareEstimate)
    (h817 : LocalBoundednessEstimate) (h832 : InteriorGradientEstimate)
    (h836 : InteriorRegularRepresentative) (H51 : CorrectorGradientMoments)
    (d : ℕ) [Fact (2 ≤ d)] (L r₀ m : ℝ)
    (hL : 1 ≤ L) (hr₀ : 1 ≤ r₀) (hm : 2 ≤ m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Q : EnvironmentLaw d L r₀) (i : Fin d)
      (u : Coefficient d (AKMUpperEllipticity L) → ℝ × Vec d → ℝ)
      (G : Coefficient d (AKMUpperEllipticity L) → ℝ × Vec d → Vec d),
      Measurable (fun z : Coefficient d (AKMUpperEllipticity L) ×
        (ℝ × Vec d) => u z.1 z.2) →
      Measurable (fun z : Coefficient d (AKMUpperEllipticity L) ×
        (ℝ × Vec d) => G z.1 z.2) →
      (∀ᵐ A ∂actualCoefficientLaw Q,
        IsSemigroupSolution A (fun x => (A x).mulVec (unitVector i)) (u A) (G A) ∧
        HasCanonicalKernelRepresentation A (fun x => (A x).mulVec (unitVector i)) (u A)) →
      (∀ᵐ A ∂actualCoefficientLaw Q, ∀ t : ℝ, 0 < t →
        HasWeakGradient univ (fun x => u A (t,x)) (fun x => G A (t,x))) →
      ∀ R : ℝ, 1 ≤ R → ∀ y : Point d,
      eLpNorm (fun z : PhysicalField d L × PhysicalField d L => euclideanNorm
        (continuousCanonicalGradient Q i (reduce z.1.1) 0 -
          continuousCanonicalGradient Q i (reduce z.2.1) 0))
        (ENNReal.ofReal m) (recenteredPhysicalCopyLaw Q (r₀*R) y) ≤
          ENNReal.ofReal (C*R^(-(d : ℝ)/2)) := by
  have hd : 2 ≤ d := Fact.out
  have hm2 : 2 ≤ 2*m := by linarith
  obtain ⟨B,hB,hpoint⟩ := exists_canonicalGradient_moment_bound H51 hd L r₀ hm2
  obtain ⟨E,hE,henergy⟩ := continuous_canonical_gradient_paired_spatial_decay
    hdecay hreg hP h836 d L r₀ (2*m) hL hm2
  let K := AKMUpperEllipticity L
  let A := normalized_lipschitz_constant L r₀
  have hK : 1 < K := one_lt_AKMUpperEllipticity hL
  have hK0 : 0 < K := zero_lt_one.trans hK
  have hA : 0 ≤ A := by
    have hs := ellipticityScale_pos hL
    have hL0 : 0 ≤ L := zero_le_one.trans hL
    have hr0 : 0 ≤ r₀ := zero_le_one.trans hr₀
    dsimp [A,normalized_lipschitz_constant]
    positivity
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨C,hC,hbound⟩ := ellipticLargeScale_paired_corrector_gradient_moments
    hAKM h817 h832 hP d hd K 1 hK (by norm_num) (by linarith)
    (inv_pos.mpr hK0) (mul_pos (by positivity : 0 < (d : ℝ)+1) hK0)
    (show 0 < K+2*A by positivity) (by norm_num : (0 : ℝ) < 1/2)
    (by norm_num : (1:ℝ)/2 < 1) m (2*B) E (one_le_two.trans hm) (by positivity) hE.le
  refine ⟨C,hC,?_⟩
  intro Q i u G hu hG hflow hweak R hR y
  let P := recenteredPhysicalCopyLaw Q (r₀*R) y
  let g : PhysicalField d L → Vec d → Vec d := fun ω x =>
    continuousCanonicalGradient Q i (reduce ω.1) (r₀ • x)
  let φ : PhysicalField d L → Vec d → ℝ := fun ω x =>
    x i+r₀⁻¹*canonicalScalarRayPrimitive Q i (reduce ω.1) (r₀ • x)
  let a₁ : PhysicalField d L × PhysicalField d L → Coefficient d K := fun z =>
    project (r₀ := r₀) Q.ellipticity_parameter z.1
  let a₂ : PhysicalField d L × PhysicalField d L → Coefficient d K := fun z =>
    project (r₀ := r₀) Q.ellipticity_parameter z.2
  obtain ⟨_,_,hfst,_,_⟩ := recenteredPhysicalCopy_properties Q (r₀*R) y
  have hdata := actual_paired_affine_harmonic_data hP h836 Q i R hR y
  have hb : eLpNorm (fun ω => euclideanNorm (conditionalCorrectorGradient Q i 0 ω))
      (ENNReal.ofReal (2*m)) (reducedEnvironmentLaw Q) ≤ ENNReal.ofReal B := by
    simpa only [conditionalCorrectorGradient,WithLp.ofLp_zero] using hpoint Q i
  have hzero := physical_continuous_gradient_copy_moment hP h836 Q i
    (2*m) B (r₀*R) y (by linarith) hB hb
  have hen := henergy Q i u G hu hG hflow hweak R hR y
  have hout := hbound (actualCoefficientLaw Q) (isAdmissibleLaw_actualCoefficientLaw Q)
    P a₁ a₂ ((measurePreserving_akmProject Q).comp hfst) R (zero_lt_one.trans_le hR) 0
    (fun z => φ z.1) (fun z => φ z.2)
    (fun z x => unitVector i+g z.1 x) (fun z x => unitVector i+g z.2 x) hdata
    (by simpa only [add_sub_add_left_eq_sub,g,smul_zero] using hzero.1)
    (by simpa only [add_sub_add_left_eq_sub,g,smul_zero] using hzero.2)
    (by simpa only [add_sub_add_left_eq_sub] using hen.1)
    (by simpa only [add_sub_add_left_eq_sub] using hen.2)
  simpa only [add_sub_add_left_eq_sub,g,smul_zero] using hout.2

end EinsteinRelation.Correctors
