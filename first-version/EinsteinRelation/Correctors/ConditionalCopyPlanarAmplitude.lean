import EinsteinRelation.Correctors.ConditionalCopyPlanarEquation
import EinsteinRelation.Correctors.PlanarContinuousBallSupport
import EinsteinRelation.Correctors.ConditionalCenteredShift
import EinsteinRelation.Correctors.SpatialWeakTranslation
import EinsteinRelation.Correctors.CanonicalGradientLocalSquareIntegrability

/-! The repaired planar comparison on the actual conditional-copy law.
Source: `paper/main.tex:872–894`. Continuity is a hypothesis on the actual
representatives whose point values occur in the conclusion. -/
open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM External.GilbargTrudinger NormalizedSpatialRepresentativeSupport
open NormalizedScalarPhysicalLawTransportSupport HeatSelectedSkewMeaning
attribute [local instance] ReductionImageV3.fieldPair_standardBorel
local instance planarAmplitudeDim : Fact (2 ≤ 2) := ⟨by decide⟩
local instance planarAmplitudeRestrictionMeasurableSpace {d : ℕ} (U : Set (Vec d)) : MeasurableSpace C(U, Mat d) := borel C(U, Mat d)

/-- The scalar and full Frobenius-skew amplitudes of the literal copies
are controlled by their common spatial energy. The constant precedes the
law, radius, center and correctors. Source: `paper/main.tex:872–883`. -/
theorem ae_paired_planar_centered_correctors_le_energy
    (h817 : LocalBoundednessEstimate) (hP : BallPoincareEstimate) (L : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {r₀ : ℝ} (Q : EnvironmentLaw 2 L r₀)
      (ζ : SourceMollifier 2) (R : ℝ) (hR : 1 ≤ R) (y : Point 2) (i : Fin 2)
      (φ : FieldPair 2 → Point 2 → ℝ) (σ : FieldPair 2 → Vec 2 → Mat 2),
      IsNormalizedCanonicalScalarCorrector Q i ζ R hR y φ →
      HasHeatSelectedSkewCorrectorColumn (by decide) Q i σ →
      (∀ᵐ ω ∂reducedEnvironmentLaw Q, Continuous (φ ω) ∧ Continuous (σ ω)) →
      ∀ᵐ z ∂reducedConditionalCopyLaw (reducedEnvironmentLaw Q)
          (conditionalCorrectorBall R y),
        |conditionalCenteredScalar ζ R y φ z.2.1 -
          conditionalCenteredScalar ζ R y φ z.2.2| +
        frobeniusNorm (conditionalCenteredSkew ζ R y σ z.2.1 -
          conditionalCenteredSkew ζ R y σ z.2.2) ≤
        C*R * vectorRms volume (ball 0 (2*R)) (fun x =>
          conditionalCorrectorGradient Q i (WithLp.toLp 2 (x+y.ofLp)) z.2.1 -
            conditionalCorrectorGradient Q i (WithLp.toLp 2 (x+y.ofLp)) z.2.2) := by
  have hL : 0 < sourceReducedBound L := by
    unfold sourceReducedBound
    exact mul_pos (Real.exp_pos _) (by nlinarith [sq_nonneg (L+1), sq_nonneg L])
  obtain ⟨C, hC, hb⟩ := paired_planar_centered_correctors_of_gt h817 hP hL
  refine ⟨C, hC, ?_⟩
  intro r₀ Q ζ R hR y i φ σ hφ hσ hc
  have hRp : 0 < R := lt_of_lt_of_le zero_lt_one hR
  let U := conditionalCorrectorBall R y
  obtain ⟨_, hfirst, hsecond, hagree⟩ := reducedConditionalCopy_properties
    (reducedEnvironmentLaw Q) U (isOpen_conditionalCorrectorBall R y)
  have hmp₁ : MeasurePreserving
      (fun z : C(U, Mat 2) × (FieldPair 2 × FieldPair 2) => z.2.1)
      (reducedConditionalCopyLaw (reducedEnvironmentLaw Q) U) (reducedEnvironmentLaw Q) :=
    ⟨measurable_fst.comp measurable_snd, hfirst⟩
  have hmp₂ : MeasurePreserving
      (fun z : C(U, Mat 2) × (FieldPair 2 × FieldPair 2) => z.2.2)
      (reducedConditionalCopyLaw (reducedEnvironmentLaw Q) U) (reducedEnvironmentLaw Q) :=
    ⟨measurable_snd.comp measurable_snd, hsecond⟩
  have hG : ∀ᵐ z ∂reducedConditionalCopyLaw (reducedEnvironmentLaw Q) U,
      MemLp (fun x : Vec 2 => euclideanNorm
        (conditionalCorrectorGradient Q i (WithLp.toLp 2 (x+y.ofLp)) z.2.1 -
          conditionalCorrectorGradient Q i (WithLp.toLp 2 (x+y.ofLp)) z.2.2)) 2
        (volume.restrict (ball 0 (2*R))) := by
    filter_upwards [hmp₁.quasiMeasurePreserving.ae
      (ae_canonicalGradient_translated_localL2 Q i y),
      hmp₂.quasiMeasurePreserving.ae (ae_canonicalGradient_translated_localL2 Q i y)]
      with z h₁ h₂
    have hn := ((h₁ (2*R) (by positivity)).sub (h₂ (2*R) (by positivity))).norm
    simpa only [Pi.sub_apply, ← WithLp.toLp_sub, ← TimeChange.euclideanNorm_eq_norm_toLp]
      using hn
  have hsk : ∀ᵐ ω ∂reducedEnvironmentLaw Q,
      ∀ᵐ x ∂volume, (σ ω x).transpose = -(σ ω x) :=
    hσ.choose_spec.2.mono fun _ h => h.1.1
  filter_upwards [hagree, hG, hmp₁.quasiMeasurePreserving.ae hc,
    hmp₂.quasiMeasurePreserving.ae hc, hmp₁.quasiMeasurePreserving.ae hφ.2,
    hmp₂.quasiMeasurePreserving.ae hφ.2, hmp₁.quasiMeasurePreserving.ae hsk,
    hmp₂.quasiMeasurePreserving.ae hsk,
    hmp₁.quasiMeasurePreserving.ae (ae_reducedEnvironmentLaw_field_isElliptic Q),
    hmp₁.quasiMeasurePreserving.ae (ae_conditionalCorrectorGradient_flux_divergence Q i),
    hmp₂.quasiMeasurePreserving.ae (ae_conditionalCorrectorGradient_flux_divergence Q i),
    hmp₁.quasiMeasurePreserving.ae (ae_heatSelectedSkew_rowDivergence Q i σ hσ),
    hmp₂.quasiMeasurePreserving.ae (ae_heatSelectedSkew_rowDivergence Q i σ hσ)]
    with z heq hGz hc₁ hc₂ hφ₁ hφ₂ hsk₁ hsk₂ hell hd₁ hd₂ hr₁ hr₂
  obtain ⟨hli₁, hg₁, _⟩ := hφ₁
  obtain ⟨hli₂, hg₂, _⟩ := hφ₂
  let a := fun (ω : FieldPair 2) (x : Vec 2) => ω.1 (x+y.ofLp)
  let u := fun (ω : FieldPair 2) (x : Vec 2) => φ ω (WithLp.toLp 2 (x+y.ofLp))
  let G := fun (ω : FieldPair 2) (x : Vec 2) =>
    conditionalCorrectorGradient Q i (WithLp.toLp 2 (x+y.ofLp)) ω
  let S := fun (ω : FieldPair 2) (x : Vec 2) => σ ω (x+y.ofLp)
  have hu₁ : Continuous (u z.2.1) := hc₁.1.comp
    ((PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp (continuous_id.add continuous_const))
  have hu₂ : Continuous (u z.2.2) := hc₂.1.comp
    ((PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp (continuous_id.add continuous_const))
  have hS₁ : Continuous (S z.2.1) := hc₁.2.comp (continuous_id.add continuous_const)
  have hS₂ : Continuous (S z.2.2) := hc₂.2.comp (continuous_id.add continuous_const)
  have hse₁ (j k : Fin 2) : Continuous (fun x => S z.2.1 x j k) :=
    (continuous_apply k).comp ((continuous_apply j).comp hS₁)
  have hse₂ (j k : Fin 2) : Continuous (fun x => S z.2.2 x j k) :=
    (continuous_apply k).comp ((continuous_apply j).comp hS₂)
  have hg'₁ : HasWeakGradient Set.univ (u z.2.1) (G z.2.1) := by
    simpa only [u, G, conditionalCorrectorGradient, WithLp.ofLp_toLp] using
      hasWeakGradient_translation _ _ hg₁ y.ofLp
  have hg'₂ : HasWeakGradient Set.univ (u z.2.2) (G z.2.2) := by
    simpa only [u, G, conditionalCorrectorGradient, WithLp.ofLp_toLp] using
      hasWeakGradient_translation _ _ hg₂ y.ofLp
  have hd'₁ : HasWeakDivergence Set.univ
      (fun x => (a z.2.1 x).mulVec (unitVector i + G z.2.1 x)) (fun _ => 0) := by
    simpa only [a, G, Set.preimage_univ, sub_neg_eq_add] using
      hasWeakDivergence_translate isOpen_univ hd₁ (-y.ofLp)
  have hd'₂ : HasWeakDivergence Set.univ
      (fun x => (a z.2.2 x).mulVec (unitVector i + G z.2.2 x)) (fun _ => 0) := by
    simpa only [a, G, Set.preimage_univ, sub_neg_eq_add] using
      hasWeakDivergence_translate isOpen_univ hd₂ (-y.ofLp)
  have hr'₁ : HasWeakRowDivergence Set.univ (S z.2.1)
      (fun x => (a z.2.1 x).mulVec (unitVector i + G z.2.1 x) -
        (expectedCorrectorFlux Q i).ofLp) := by
    intro j
    simpa only [S, a, G, Set.preimage_univ, sub_neg_eq_add] using
      hasWeakDivergence_translate isOpen_univ (hr₁ j) (-y.ofLp)
  have hr'₂ : HasWeakRowDivergence Set.univ (S z.2.2)
      (fun x => (a z.2.2 x).mulVec (unitVector i + G z.2.2 x) -
        (expectedCorrectorFlux Q i).ofLp) := by
    intro j
    simpa only [S, a, G, Set.preimage_univ, sub_neg_eq_add] using
      hasWeakDivergence_translate isOpen_univ (hr₂ j) (-y.ofLp)
  have heq' : Set.EqOn (a z.2.1) (a z.2.2) (ball 0 (2*R)) := by
    intro x hx
    apply heq
    change dist (WithLp.toLp 2 (x+y.ofLp)) y < 8*R
    rw [dist_eq_norm, show WithLp.toLp 2 (x+y.ofLp) - y = WithLp.toLp 2 x by simp,
      ← TimeChange.euclideanNorm_eq_norm_toLp]
    have hx' : euclideanNorm x < 2*R := by simpa [ball] using hx
    linarith
  obtain ⟨hwc, hws, hwi, hwn, hw1, hwb⟩ := sourceMollifier_centered_coordinates ζ hR y
  let w := fun x : Vec 2 => sourceScaledMollifierKernel ζ R y (WithLp.toLp 2 (x+y.ofLp))
  have hval := hb R hRp (a z.2.1) (a z.2.2) (unitVector i)
    (expectedCorrectorFlux Q i).ofLp (u z.2.1) (u z.2.2) (G z.2.1) (G z.2.2)
    (S z.2.1) (S z.2.2) (fun x => hell (x+y.ofLp))
    (z.2.1.1.continuous.comp (continuous_id.add continuous_const)) heq'
    (continuous_memLp_euclideanBall _ hu₁ _) (continuous_memLp_euclideanBall _ hu₂ _) hGz
    (hasWeakGradient_mono (Set.subset_univ _) hg'₁)
    (hasWeakGradient_mono (Set.subset_univ _) hg'₂)
    (hasWeakDivergence_mono (Set.subset_univ _) hd'₁)
    (hasWeakDivergence_mono (Set.subset_univ _) hd'₂)
    (fun x => continuous_skew_of_ae _ hc₁.2 hsk₁ (x+y.ofLp))
    (fun x => continuous_skew_of_ae _ hc₂.2 hsk₂ (x+y.ofLp))
    (fun j => hasWeakDivergence_mono (Set.subset_univ _) (hr'₁ j))
    (fun j => hasWeakDivergence_mono (Set.subset_univ _) (hr'₂ j))
    (continuous_memLp_euclideanBall _
      ((hse₁ 0 1).sub (hse₂ 0 1)) _)
    (hu₁.sub hu₂).continuousOn
    ((hse₁ 0 1).sub (hse₂ 0 1)).continuousOn
    w hwi ((hwc.mul (hu₁.sub hu₂)).integrable_of_hasCompactSupport (hws.mul_right))
    (fun j k => (hwc.mul ((hse₁ j k).sub (hse₂ j k))).integrable_of_hasCompactSupport
      (hws.mul_right)) hwn hw1 hwb 0
    (by simpa [ball, euclideanNorm, euclideanSq, dot] using hRp)
  obtain ⟨hscalar, hskew⟩ := conditionalCentered_copy_shift ζ hR y φ σ z.2.1 z.2.2
    hli₁ hli₂ (fun j k => ((continuous_apply k).comp ((continuous_apply j).comp hc₁.2)).locallyIntegrable)
    (fun j k => ((continuous_apply k).comp ((continuous_apply j).comp hc₂.2)).locallyIntegrable)
  rw [hscalar, hskew]
  simpa only [u, G, S, w, zero_add, WithLp.toLp_ofLp] using hval
end EinsteinRelation.Correctors
