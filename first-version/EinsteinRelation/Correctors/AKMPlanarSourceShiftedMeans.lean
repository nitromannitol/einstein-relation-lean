import EinsteinRelation.Correctors.AKMCanonicalPlanarMomentsFromLiterature
import EinsteinRelation.Correctors.NormalizedScalarPhysicalLawTransportSupport
import EinsteinRelation.Correctors.HeatSelectedSkewEquations

/-! # Shifted means for the exact normalized and heat-selected source objects

Source: `paper/main.tex:762–766,948–955`. This specializes the canonical
moment theorem to the actual scalar normalization and iterated heat selection
predicates used by Lemma 5.2. All spatial weak equations and skewness are derived
from those predicates, and no separate source-identification premise remains.
-/

open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM HeatSelectedSkewMeaning NormalizedScalarPhysicalLawTransportSupport
open NormalizedSpatialRepresentativeSupport

local instance : Fact (2 ≤ 2) := ⟨le_rfl⟩

/-- Every normalized scalar corrector and heat-selected skew corrector obeys
the printed planar shifted-mean bound, with constants uniform in the law,
normalization radius and center. Source: `paper/main.tex:948–955`. -/
theorem canonical_planar_source_shifted_means_of_literature (hAKM : CorrectorWeakH2)
    (hP : External.GilbargTrudinger.BallPoincareEstimate)
    (L r₀ m : ℝ) (hL : 1 ≤ L) (hr₀ : 1 ≤ r₀) (hm : 1 ≤ m) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q : EnvironmentLaw 2 L r₀) (i : Fin 2),
      ∀ (ζ : NormalizedSpatialRepresentativeSupport.SourceMollifier 2)
        (R₀ : ℝ) (hR₀ : 1 ≤ R₀) (y₀ : Point 2)
        (φ : FieldPair 2 → Point 2 → ℝ) (σ : FieldPair 2 → Vec 2 → Mat 2),
        IsNormalizedCanonicalScalarCorrector Q i ζ R₀ hR₀ y₀ φ →
        HasHeatSelectedSkewCorrectorColumn (by norm_num) Q i σ →
      ∀ R : ℝ, 1 ≤ R → ∀ y : Vec 2, euclideanNorm y ≤ R →
        (MemLp (fun ω => ∫ z, (Calculus.unitMassScaledMollifier 2 R z -
            Calculus.unitMassScaledMollifier 2 R (z - y)) * φ ω (WithLp.toLp 2 z))
            (ENNReal.ofReal m) (reducedEnvironmentLaw Q) ∧
          eLpNorm (fun ω => ∫ z, (Calculus.unitMassScaledMollifier 2 R z -
            Calculus.unitMassScaledMollifier 2 R (z - y)) * φ ω (WithLp.toLp 2 z))
            (ENNReal.ofReal m) (reducedEnvironmentLaw Q) ≤ ENNReal.ofReal C) ∧
        ∀ k : Fin 2,
          MemLp (fun ω => euclideanNorm (fun j => ∫ z,
            (Calculus.unitMassScaledMollifier 2 R z -
              Calculus.unitMassScaledMollifier 2 R (z - y)) * σ ω z j k))
              (ENNReal.ofReal m) (reducedEnvironmentLaw Q) ∧
          eLpNorm (fun ω => euclideanNorm (fun j => ∫ z,
            (Calculus.unitMassScaledMollifier 2 R z -
              Calculus.unitMassScaledMollifier 2 R (z - y)) * σ ω z j k))
              (ENNReal.ofReal m) (reducedEnvironmentLaw Q) ≤ ENNReal.ofReal C := by
  obtain ⟨C, hC, hbound⟩ := canonical_planar_shifted_means_of_literature
    hAKM hP L r₀ m hL hr₀ hm
  refine ⟨C, hC, ?_⟩
  intro Q i ζ R₀ hR₀ y₀ φ σ hφ hσ
  have hu : ∀ᵐ ω ∂reducedEnvironmentLaw Q,
      HasWeakGradient Set.univ (fun x => φ ω (WithLp.toLp 2 x))
        (fun x => ((canonicalCorrectorGradient Q i :
          Lp (EuclideanSpace ℝ (Fin 2)) 2 (reducedEnvironmentLaw Q))
            (translate x ω)).ofLp) := by
    filter_upwards [hφ.2] with ω hω
    obtain ⟨_, hw, _⟩ := hω
    exact hw
  have hskew : ∀ᵐ ω ∂reducedEnvironmentLaw Q,
      ∀ᵐ x ∂volume, (σ ω x).transpose = -(σ ω x) := by
    obtain ⟨_, _, hselected⟩ := hσ
    exact hselected.mono fun _ h => h.1.1
  have hdiv : ∀ᵐ ω ∂reducedEnvironmentLaw Q,
      HasWeakRowDivergence Set.univ (σ ω)
        (fun x => (canonicalCorrectorFlux Q i (translate x ω)).ofLp -
          (expectedCorrectorFlux Q i).ofLp) := by
    simpa only [PiLp.sub_apply] using hσ.ae_hasWeakRowDivergence
  exact hbound Q i (fun ω x => φ ω (WithLp.toLp 2 x)) σ hu hskew hdiv

end EinsteinRelation.Correctors
