import EinsteinRelation.Correctors.P53SourceSkewScalarPotential

/-! # A fixed measurable scalar source family

Source: `paper/main.tex:762–766,909–914`. The source is selected before the
moment exponent. At every radius it is an actual normalized canonical
potential, using normalization radius `max 1 R` outside the estimate range.
-/

open MeasureTheory
namespace EinsteinRelation.Correctors
open External.GilbargTrudinger NormalizedSpatialRepresentativeSupport
open NormalizedScalarPhysicalLawTransportSupport

/-- A normalized canonical scalar source, chosen from proved existence.
Source: `paper/main.tex:762–766`. -/
noncomputable def selectedCanonicalScalarSource (hP : BallPoincareEstimate)
    {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀)
    (R : ℝ) (i : Fin d) (ω : FieldPair d) (x : Vec d) : ℝ :=
  (exists_normalizedCanonicalScalarCorrector hP Q i (canonicalSourceMollifier d)
    (max 1 R) (le_max_left _ _) 0).choose ω (WithLp.toLp 2 x)

/-- On the source radius range, the selected family has exactly the
production normalization and gradient. Source: `paper/main.tex:762–766`. -/
theorem selectedCanonicalScalarSource_normalized (hP : BallPoincareEstimate)
    {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀)
    (R : ℝ) (hR : 1 ≤ R) (i : Fin d) :
    IsNormalizedCanonicalScalarCorrector Q i (canonicalSourceMollifier d) R hR 0
      (fun ω x => selectedCanonicalScalarSource hP Q R i ω x.ofLp) := by
  simpa only [selectedCanonicalScalarSource, WithLp.toLp_ofLp, max_eq_right hR] using
    (exists_normalizedCanonicalScalarCorrector hP Q i (canonicalSourceMollifier d)
      (max 1 R) (le_max_left _ _) 0).choose_spec

end EinsteinRelation.Correctors
