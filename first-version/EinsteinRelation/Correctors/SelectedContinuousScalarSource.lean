import EinsteinRelation.Correctors.CanonicalScalarRegularExistence

/-! # A fixed continuous normalized scalar source

Source: `paper/main.tex:735–737,762–766,909–914`. The source is selected
from proved continuous existence before choosing any moment exponent.
-/

open MeasureTheory

noncomputable section

namespace EinsteinRelation.Correctors
open External.GilbargTrudinger NormalizedSpatialRepresentativeSupport
open NormalizedScalarPhysicalLawTransportSupport

/-- A normalized scalar source selected with continuous representatives.
The radius is at least one throughout its definition.
Source: `paper/main.tex:762–766,909–914`. -/
def selectedContinuousCanonicalScalarSource
    (hP : BallPoincareEstimate) (h836 : InteriorRegularRepresentative)
    {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀)
    (R : ℝ) (i : Fin d) (ω : FieldPair d) (x : Vec d) : ℝ :=
  (exists_continuous_normalizedCanonicalScalarCorrector hP h836 Q i
    (canonicalSourceMollifier d) (max 1 R) (le_max_left _ _) 0).choose ω
      (WithLp.toLp 2 x)

/-- The continuous selection has the original canonical normalization.
Source: `paper/main.tex:762–766`. -/
theorem selectedContinuousCanonicalScalarSource_normalized
    (hP : BallPoincareEstimate) (h836 : InteriorRegularRepresentative)
    {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀)
    (R : ℝ) (hR : 1 ≤ R) (i : Fin d) :
    IsNormalizedCanonicalScalarCorrector Q i (canonicalSourceMollifier d) R hR 0
      (fun ω x => selectedContinuousCanonicalScalarSource hP h836 Q R i ω x.ofLp) := by
  have h := (exists_continuous_normalizedCanonicalScalarCorrector hP h836 Q i
    (canonicalSourceMollifier d) (max 1 R) (le_max_left _ _) 0).choose_spec.1
  simpa only [max_eq_right hR] using
    (show IsNormalizedCanonicalScalarCorrector Q i (canonicalSourceMollifier d)
      (max 1 R) (le_max_left _ _) 0
      (fun ω x => selectedContinuousCanonicalScalarSource hP h836 Q R i ω x.ofLp) from by
        simpa only [selectedContinuousCanonicalScalarSource, WithLp.toLp_ofLp] using h)

/-- The regular source is jointly measurable, including outside the estimate
range of radii. Source: `paper/main.tex:762–766,909–914`. -/
theorem measurable_selectedContinuousCanonicalScalarSource
    (hP : BallPoincareEstimate) (h836 : InteriorRegularRepresentative)
    {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀)
    (R : ℝ) (i : Fin d) :
    Measurable (fun z : FieldPair d × Vec d =>
      selectedContinuousCanonicalScalarSource hP h836 Q R i z.1 z.2) := by
  exact (exists_continuous_normalizedCanonicalScalarCorrector hP h836 Q i
    (canonicalSourceMollifier d) (max 1 R) (le_max_left _ _) 0).choose_spec.1.1.comp
      measurable_swap

/-- The selected scalar is continuous almost surely; continuity is proved
as part of the selection rather than added as an independent hypothesis.
Source: `paper/main.tex:735–737,762–766`. -/
theorem ae_continuous_selectedContinuousCanonicalScalarSource
    (hP : BallPoincareEstimate) (h836 : InteriorRegularRepresentative)
    {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀)
    (R : ℝ) (i : Fin d) :
    ∀ᵐ ω ∂reducedEnvironmentLaw Q,
      Continuous (selectedContinuousCanonicalScalarSource hP h836 Q R i ω) := by
  filter_upwards [(exists_continuous_normalizedCanonicalScalarCorrector hP h836 Q i
    (canonicalSourceMollifier d) (max 1 R) (le_max_left _ _) 0).choose_spec.2] with ω hω
  exact hω.comp (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ))

end EinsteinRelation.Correctors
