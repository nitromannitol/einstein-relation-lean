import EinsteinRelation.Correctors.ContinuousPairedSpatialEnergy
import EinsteinRelation.Correctors.CanonicalScalarRegularExistence
import EinsteinRelation.Correctors.ConditionalCopyHarmonicEquation
import EinsteinRelation.Correctors.SpatialWeakDilationUniv
import EinsteinRelation.Correctors.PlanarContinuousBallSupport
import EinsteinRelation.Correctors.RegularCorrectorSubtraction

/-! # Regular actual affine correctors in normalized physical coordinates

Source: `paper/main.tex:852–867`. The measurable ray primitive and the
continuous canonical gradient satisfy the actual normalized homogeneous
equation. Local GT representatives identify these same continuous fields.
-/

open MeasureTheory Set
noncomputable section
namespace EinsteinRelation.Correctors
open External.AKM External.GilbargTrudinger Environment.AKMTestIntegralSupport ReductionImageV3
open NormalizedSpatialRepresentativeSupport

/-- The deterministic operator Lipschitz bound after physical normalization.
Source: `paper/main.tex:198–207,693–702`. -/
def normalized_lipschitz_constant (L r₀ : ℝ) : ℝ :=
  ellipticityScale L * r₀ * (Real.exp (2*L)*(L+2*L^2))

/-- Actual normalized coefficients have their inherited operator Lipschitz
bound. Source: `paper/main.tex:693–702,852–867`. -/
theorem ae_project_operator_lipschitz
    {d : ℕ} {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) :
    ∀ᵐ ω ∂physicalReferenceLaw Q,
      IsOperatorLipschitz (normalized_lipschitz_constant L r₀)
        (project (r₀ := r₀) Q.ellipticity_parameter ω) := by
  filter_upwards [(measurePreserving_physicalReduction Q).quasiMeasurePreserving.ae
    (ActualImageLpStateTransport.ae_reducedEnvironmentLaw_mem_image Q)] with ω hω
  obtain ⟨η,hη,hηeq⟩ := hω
  have hlip := (sourceReducedBound_support Q.ellipticity_parameter hη).2.2.2.1
  have hlip' : IsOperatorLipschitz (Real.exp (2*L)*(L+2*L^2)) (reduce ω.1).1 := by
    simpa only [← hηeq] using hlip
  have hr : 0 < r₀ := zero_lt_one.trans_le Q.range_parameter
  have hB := ellipticityScale_pos Q.ellipticity_parameter
  intro x y ξ
  change euclideanNorm ((ellipticityScale L • (reduce ω.1).1 (r₀ • x) -
    ellipticityScale L • (reduce ω.1).1 (r₀ • y)).mulVec ξ) ≤ _
  rw [← smul_sub,Matrix.smul_mulVec,euclideanNorm_smul _ hB.le]
  have h := hlip' (r₀ • x) (r₀ • y) ξ
  rw [← smul_sub,euclideanNorm_smul _ hr.le] at h
  exact (mul_le_mul_of_nonneg_left h hB.le).trans_eq (by
    unfold normalized_lipschitz_constant
    ring)

/-- AKM's lower bound one gives the symmetric two-sided ellipticity used
by GT, on the same coefficient. Source: `paper/main.tex:693–702`. -/
theorem project_isElliptic {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (ω : PhysicalField d L) :
    IsElliptic (AKMUpperEllipticity L) (project (r₀ := r₀) Q.ellipticity_parameter ω) := by
  let A := project (r₀ := r₀) Q.ellipticity_parameter ω
  have hK : 1 ≤ AKMUpperEllipticity L :=
    (one_lt_AKMUpperEllipticity Q.ellipticity_parameter).le
  intro x
  refine ⟨A.symmetric x,fun ξ => ⟨?_,(A.elliptic x ξ).2⟩⟩
  exact (mul_le_of_le_one_left (euclideanSq_nonneg_fisher ξ)
    (inv_le_one_of_one_le₀ hK)).trans (A.elliptic x ξ).1

/-- Global continuous representatives inherit the full C1 Hölder class
from local representatives in their volume classes.
Source: `paper/main.tex:852–867`. -/
theorem c1Alpha_of_continuous_versions {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpen U) {f : Vec d → ℝ} {G : Vec d → Vec d}
    (hf : Continuous f) (hG : Continuous G)
    {v : Vec d → ℝ} {h : Vec d → Vec d} {α : ℝ} (hα : 0 < α)
    (hreg : C1Alpha U α v h)
    (hv : v =ᵐ[volume.restrict U] f) (hh : h =ᵐ[volume.restrict U] G) :
    C1Alpha U α f G := by
  obtain ⟨K,hK⟩ := hreg.2
  have hhc : ContinuousOn h U := continuousOn_pi.mpr
    (fun j => continuousOn_of_holderBound hα (hK j))
  have hheq := Measure.eqOn_open_of_ae_eq hh hU hhc hG.continuousOn
  refine ⟨fun x hx => hasFDerivAt_of_local_regular_representatives f G hf hG x U hU hx v h
    (fun y hy => (hreg.1 y hy).continuousAt.continuousWithinAt) hhc hreg.1 hv.symm hh.symm,
    K,fun j => ?_⟩
  obtain ⟨S,H,hS,hH,hKH,hsup,hholder⟩ := hK j
  refine ⟨S,H,hS,hH,hKH,fun x hx => ?_,fun x hx y hy => ?_⟩
  · simpa only [← hheq hx] using hsup x hx
  · simpa only [← hheq hx,← hheq hy] using hholder x hx y hy

/-- The actual ray primitive and continuous gradient give regular affine
solutions on every normalized ball. No representative or regularity data
is assumed. Source: `paper/main.tex:852–867`. -/
theorem ae_physical_affine_corrector_regularity
    (hP : BallPoincareEstimate) (h836 : InteriorRegularRepresentative)
    {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d) :
    let f := fun (ω : PhysicalField d L) (x : Vec d) =>
      x i + r₀⁻¹*canonicalScalarRayPrimitive Q i (reduce ω.1) (r₀ • x)
    let G := fun (ω : PhysicalField d L) (x : Vec d) =>
      unitVector i + continuousCanonicalGradient Q i (reduce ω.1) (r₀ • x)
    ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ R : ℝ, 0 < R →
      WeakSolution (ball 0 R) (project (r₀ := r₀) Q.ellipticity_parameter ω) (f ω) (G ω) ∧
      C1Alpha (ball 0 R) (1/2) (f ω) (G ω) := by
  dsimp only
  have hr : 0 < r₀ := zero_lt_one.trans_le Q.range_parameter
  have hB : 0 < AKMUpperEllipticity L :=
    zero_lt_one.trans (one_lt_AKMUpperEllipticity Q.ellipticity_parameter)
  have hL : 0 ≤ L := zero_le_one.trans Q.ellipticity_parameter
  have hscale : 0 < ellipticityScale L := ellipticityScale_pos Q.ellipticity_parameter
  have hA : 0 ≤ normalized_lipschitz_constant L r₀ := by
    unfold normalized_lipschitz_constant
    positivity
  filter_upwards [(measurePreserving_physicalReduction Q).quasiMeasurePreserving.ae
      (ae_canonicalScalarRayPrimitive_weakGradient hP h836 Q i),
    (measurePreserving_physicalReduction Q).quasiMeasurePreserving.ae
      (ae_continuousCanonicalGradient hP h836 Q i),
    (measurePreserving_physicalReduction Q).quasiMeasurePreserving.ae
      (ae_conditionalCorrectorGradient_flux_divergence Q i),
    ae_project_operator_lipschitz Q,
    ae_physical_continuous_gradient_dilation hP h836 Q i]
      with ω hφ hG hdiv hlip hid
  let u : Vec d → ℝ := fun x => r₀⁻¹*canonicalScalarRayPrimitive Q i (reduce ω.1) (r₀ • x)
  let g : Vec d → Vec d := fun x => continuousCanonicalGradient Q i (reduce ω.1) (r₀ • x)
  have huc : Continuous u := continuous_const.mul (hφ.1.comp (continuous_const.smul continuous_id))
  have hgc : Continuous g := hG.1.comp (continuous_const.smul continuous_id)
  have huw : HasWeakGradient univ u g := by
    have hw := hasWeakGradient_univ_dilation hφ.2 r₀ r₀⁻¹ hr
    simp only [inv_mul_cancel₀ hr.ne',one_smul] at hw
    exact hasWeakGradient_congr_ae isOpen_univ hw (ae_eq_refl _)
      (by simpa only [Measure.restrict_univ] using hid.symm)
  have hflux : HasWeakDivergence univ
      (fun x => (project (r₀ := r₀) Q.ellipticity_parameter ω x).mulVec (unitVector i + g x))
      (fun _ => 0) := by
    have hw := hasWeakDivergence_dilation hdiv r₀ (ellipticityScale L) hr
    simp only [mul_zero] at hw
    apply hasWeakDivergence_congr_ae isOpen_univ hw ?_ (ae_eq_refl _)
    simp only [Measure.restrict_univ]
    filter_upwards [hid] with x hx
    change ellipticityScale L • ((reduce ω.1).1 (r₀ • x)).mulVec
      (unitVector i + conditionalCorrectorGradient Q i (WithLp.toLp 2 (r₀ • x)) (reduce ω.1)) = _
    change g x = conditionalCorrectorGradient Q i (WithLp.toLp 2 (r₀ • x)) (reduce ω.1) at hx
    rw [← hx]
    exact (Matrix.smul_mulVec _ _ _).symm
  have hw (S : ℝ) (hS : 0 < S) : WeakSolution (ball 0 S)
      (project (r₀ := r₀) Q.ellipticity_parameter ω) (fun x => x i+u x)
      (fun x => unitVector i+g x) :=
    affine_weakSolution_of_weakPotential S hS i _ u g
      (continuous_memLp_euclideanBall u huc S) (continuous_memLp_euclideanBall g hgc S)
      (hasWeakGradient_mono (subset_univ _) huw) (hasWeakDivergence_mono (subset_univ _) hflux)
  intro R hR
  refine ⟨hw R hR,?_⟩
  obtain ⟨v,h,hreg,hv,hh⟩ := h836 d Fact.out (AKMUpperEllipticity L)⁻¹
    (AKMUpperEllipticity L+normalized_lipschitz_constant L r₀*(4*R+1))
    (1/2) R (inv_pos.mpr hB) (by positivity) (by norm_num) (by norm_num) hR _
    (fun x _ ξ => ((project_isElliptic Q ω x).2 ξ).1)
    (holderBound_half_ball_of_isElliptic_lipschitz hB hA hR
      (project_isElliptic Q ω) hlip) _ _ (hw (2*R) (by positivity))
  exact c1Alpha_of_continuous_versions (paired_isOpen_ball 0 R)
    ((continuous_apply i).add huc) (continuous_const.add hgc) (by norm_num) hreg hv hh

end EinsteinRelation.Correctors
