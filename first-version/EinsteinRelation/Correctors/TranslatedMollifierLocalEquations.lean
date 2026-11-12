import EinsteinRelation.Correctors.LocalMollifierSpatialTest
import EinsteinRelation.Correctors.SpatialWeakDivergenceTranslation
import EinsteinRelation.Correctors.StationaryCenterTransport

/-! # Joint transport of the localized conditional equations

Source: `paper/main.tex:913–938`. A single almost-sure center-zero weak
equation is first localized by the literal mollifier, then translated jointly
in its center and environment. This gives a common product-almost-sure
equation for the exact weighted scalar and skew fields used in the center
average, with their actual derivative-correction terms.
-/

open MeasureTheory

namespace EinsteinRelation.Correctors

/-- Center-zero local equations yield the actual mollifier-weighted equations
at almost every center, on one probability-one event. No unweighted equation
outside its conditioning ball is required. Source: `paper/main.tex:913–938`. -/
theorem ae_translated_mollifier_local_equations {d : ℕ} {L r₀ R : ℝ}
    (Q : EnvironmentLaw d L r₀) (hR : 0 < R)
    (v : FieldPair d → Vec d → ℝ) (G : FieldPair d → Vec d → Vec d)
    (S : FieldPair d → Vec d → Mat d) (e b : Vec d)
    (hlocal : ∀ᵐ ω ∂reducedEnvironmentLaw Q,
      HasWeakGradient {x : Vec d | euclideanNorm x < 32 * R} (v ω) (G ω) ∧
        HasWeakRowDivergence {x : Vec d | euclideanNorm x < 32 * R} (S ω)
          (fun x => (ω.1 x).mulVec (e + G ω x) - b)) :
    ∀ᵐ ω ∂reducedEnvironmentLaw Q, ∀ᵐ y : Vec d ∂volume,
      HasWeakGradient Set.univ
        (fun x => Calculus.unitMassScaledMollifier d R (x - y) *
          v (translate y ω) (x - y))
        (fun x j => Calculus.unitMassScaledMollifier d R (x - y) *
          G (translate y ω) (x - y) j + v (translate y ω) (x - y) *
            coordinateDerivative j (Calculus.unitMassScaledMollifier d R) (x - y)) ∧
      HasWeakRowDivergence Set.univ
        (fun x j k => Calculus.unitMassScaledMollifier d R (x - y) *
          S (translate y ω) (x - y) j k)
        (fun x j => Calculus.unitMassScaledMollifier d R (x - y) *
          ((ω.1 x).mulVec (e + G (translate y ω) (x - y)) - b) j +
            ((S (translate y ω) (x - y)).mulVec
              (gradient (Calculus.unitMassScaledMollifier d R) (x - y))) j) := by
  have hw : IsSpatialTest {x : Vec d | euclideanNorm x < 32 * R}
      (Calculus.unitMassScaledMollifier d R) := by
    simpa only [sub_zero] using isSpatialTest_translated_unitMassScaledMollifier hR (0 : Vec d)
  have hweighted := hlocal.mono fun ω hω =>
    And.intro (hasWeakGradient_mul_spatialTest hω.1 hw)
      (hasWeakRowDivergence_mul_spatialTest hω.2 hw)
  have hprod := ae_joint_translate (volume : Measure (Vec d))
    (reducedEnvironmentLaw Q) (reducedEnvironmentLaw_stationary Q) hweighted
  have hswap := (Measure.measurePreserving_swap
    (μ := reducedEnvironmentLaw Q) (ν := (volume : Measure (Vec d)))).quasiMeasurePreserving.ae hprod
  filter_upwards [Measure.ae_ae_of_ae_prod hswap] with ω hω
  filter_upwards [hω] with y hy
  refine ⟨?_, ?_⟩
  · simpa only [neg_add_eq_sub] using hy.1.comp_add_left (-y)
  · have hdiv := hasWeakRowDivergence_comp_add_left hy.2 (-y)
    have hxy (x : Vec d) : y + (x - y) = x := by abel
    simpa only [Prod.swap_prod_mk, neg_add_eq_sub, translate_matrix, hxy] using hdiv

end EinsteinRelation.Correctors
