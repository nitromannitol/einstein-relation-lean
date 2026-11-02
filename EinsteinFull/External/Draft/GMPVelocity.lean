import EinsteinRelation.Diffusion.GMPFamily

namespace EinsteinFull.External.Draft
open EinsteinRelation
open EinsteinRelation.External.GantertSection7Support

/-- DRAFT graph leaf `external:GMP#5.9`: the fixed positive-force law of large
numbers of Proposition 5.9, printed p.27, and the strict longitudinal positivity
stated in Section 2.3, printed p.5. Section 7, printed p.32, extends this law to
its actual weak-operator process. Translation ergodicity is explicit. The
source force range is retained. This statement concerns the physical source
origin law only: reduced coefficients, signed/arbitrary forces, martingale-law
identification and the regeneration-ratio application remain internal. -/
def gmpVelocityStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (L R : ℝ) (Q : EnvironmentLaw d L R),
    IsTranslationErgodic Q.measure →
    ∀ (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
      (P : ProbabilityTheory.Kernel (FieldPair d) (Path d)),
      IsGMPPhysicalOriginLaw hd Q.ellipticity_parameter Q lam h₀.le h₁ P →
      ∃ v : Vec d, HasQuenchedVelocity Q.measure P v ∧
        0 < v (firstCoordinateIndex hd)

end EinsteinFull.External.Draft
