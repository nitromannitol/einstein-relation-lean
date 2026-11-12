import EinsteinRelation.Correctors.ConditionalCopyPlanarAmplitude
import EinsteinRelation.Correctors.PlanarAffineComparison

/-! A fixed affine reference controls the literal centered scalar and skew
fields under the single environment law. Source: `paper/main.tex:872–894`. -/
open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM External.GilbargTrudinger NormalizedSpatialRepresentativeSupport
open NormalizedScalarPhysicalLawTransportSupport HeatSelectedSkewMeaning
local instance planarSingleDim : Fact (2 ≤ 2) := ⟨by decide⟩

/-- The affine comparison removes the constant total gradient and mean flux;
it leaves the normalization of the actual fields unchanged.
Source: `paper/main.tex:872–883`. -/
theorem ae_single_planar_centered_correctors_le_affine_energy
    (h817 : LocalBoundednessEstimate) (hP : BallPoincareEstimate) (L : ℝ)
    (href : ∀ (i : Fin 2) (m : Vec 2),
      HasWeakGradient Set.univ (fun x : Vec 2 => -(x i)) (fun _ => -(unitVector i)) ∧
      HasWeakRowDivergence Set.univ (planarAffineSkewReference m) (fun _ => -m)) :
    ∃ C : ℝ, 0 < C ∧ ∀ {r₀ : ℝ} (Q : EnvironmentLaw 2 L r₀)
      (ζ : SourceMollifier 2) (R : ℝ) (hR : 1 ≤ R) (y : Point 2) (i : Fin 2)
      (φ : FieldPair 2 → Point 2 → ℝ) (σ : FieldPair 2 → Vec 2 → Mat 2),
      IsNormalizedCanonicalScalarCorrector Q i ζ R hR y φ →
      HasHeatSelectedSkewCorrectorColumn (by decide) Q i σ →
      (∀ᵐ ω ∂reducedEnvironmentLaw Q, Continuous (φ ω) ∧ Continuous (σ ω)) →
      let w : Vec 2 → ℝ := fun x =>
        sourceScaledMollifierKernel ζ R y (WithLp.toLp 2 (x+y.ofLp))
      let c : ℝ := -∫ x, w x * (-(x i))
      let A : Mat 2 := Matrix.of (fun j k =>
        -∫ x, w x * planarAffineSkewReference (expectedCorrectorFlux Q i).ofLp x j k)
      ∀ᵐ ω ∂reducedEnvironmentLaw Q,
        |conditionalCenteredScalar ζ R y φ ω-c| +
          frobeniusNorm (conditionalCenteredSkew ζ R y σ ω-A) ≤
          C*R * vectorRms volume (ball 0 (2*R)) (fun x =>
            unitVector i + conditionalCorrectorGradient Q i
              (WithLp.toLp 2 (x+y.ofLp)) ω) := by
  have hL : 0 < sourceReducedBound L := by
    unfold sourceReducedBound
    exact mul_pos (Real.exp_pos _) (by nlinarith [sq_nonneg (L+1), sq_nonneg L])
  obtain ⟨C,hC,hb⟩ := planar_single_centered_amplitude_of_reference h817 hP hL
  refine ⟨C,hC,?_⟩
  intro r₀ Q ζ R hR y i φ σ hφ hσ hc
  dsimp only
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hsk : ∀ᵐ ω ∂reducedEnvironmentLaw Q,
      ∀ᵐ x ∂volume, (σ ω x).transpose = -(σ ω x) :=
    hσ.choose_spec.2.mono fun _ h => h.1.1
  filter_upwards [hc, hφ.2, hsk, ae_reducedEnvironmentLaw_field_isElliptic Q,
    ae_conditionalCorrectorGradient_flux_divergence Q i,
    ae_heatSelectedSkew_rowDivergence Q i σ hσ,
    ae_canonicalGradient_translated_localL2 Q i y]
    with ω hcω hφω hskω hell hd hr hG
  let a := fun x : Vec 2 => ω.1 (x+y.ofLp)
  let u := fun x : Vec 2 => φ ω (WithLp.toLp 2 (x+y.ofLp))
  let G := fun x : Vec 2 => conditionalCorrectorGradient Q i
    (WithLp.toLp 2 (x+y.ofLp)) ω
  let S := fun x : Vec 2 => σ ω (x+y.ofLp)
  have hu : Continuous u := hcω.1.comp
    ((PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp (continuous_id.add continuous_const))
  have hS : Continuous S := hcω.2.comp (continuous_id.add continuous_const)
  have hg' : HasWeakGradient Set.univ u G := by
    simpa only [u, G, conditionalCorrectorGradient, WithLp.ofLp_toLp] using
      hasWeakGradient_translation _ _ hφω.2.1 y.ofLp
  have hd' : HasWeakDivergence Set.univ
      (fun x => (a x).mulVec (unitVector i+G x)) (fun _ => 0) := by
    simpa only [a,G,Set.preimage_univ,sub_neg_eq_add] using
      hasWeakDivergence_translate isOpen_univ hd (-y.ofLp)
  have hr' : HasWeakRowDivergence Set.univ S
      (fun x => (a x).mulVec (unitVector i+G x)-(expectedCorrectorFlux Q i).ofLp) := by
    intro j
    simpa only [S,a,G,Set.preimage_univ,sub_neg_eq_add] using
      hasWeakDivergence_translate isOpen_univ (hr j) (-y.ofLp)
  have hGe : MemLp (fun x => euclideanNorm (unitVector i+G x)) 2
      (volume.restrict (ball 0 (2*R))) := by
    letI : IsFiniteMeasure (volume.restrict (ball (0 : Vec 2) (2*R))) :=
      isFiniteMeasure_restrict.mpr (ENNReal.toReal_pos_iff.mp
        (ball_volume_pos_finite 2 (2*R) (by positivity))).2.ne
    have he := ((memLp_const (WithLp.toLp 2 (unitVector i))).add
      (hG (2*R) (by positivity))).norm
    simpa only [Pi.add_apply, ← WithLp.toLp_add,
      ← TimeChange.euclideanNorm_eq_norm_toLp,G] using he
  obtain ⟨hwc,hws,_,hwn,hw1,hwb⟩ := sourceMollifier_centered_coordinates ζ hR y
  let w := fun x : Vec 2 => sourceScaledMollifierKernel ζ R y
    (WithLp.toLp 2 (x+y.ofLp))
  have hval := hb i (expectedCorrectorFlux Q i).ofLp (href i (expectedCorrectorFlux Q i).ofLp).1
    (href i (expectedCorrectorFlux Q i).ofLp).2
    R hRp a u G S (fun x => hell (x+y.ofLp))
    (ω.1.continuous.comp (continuous_id.add continuous_const)) hu hS
    (fun x => continuous_skew_of_ae _ hcω.2 hskω (x+y.ofLp)) hGe hg' hd' hr'
    w hwc hws hwn hw1 hwb
  obtain ⟨hscalar,hskew⟩ := conditionalCentered_coordinates ζ R y φ σ ω
  rw [hscalar,hskew]
  simpa only [a,u,G,S,w,zero_add,WithLp.toLp_ofLp,Matrix.of_apply,Pi.sub_apply] using hval
end EinsteinRelation.Correctors
