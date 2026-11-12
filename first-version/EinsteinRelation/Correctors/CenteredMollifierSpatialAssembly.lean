import EinsteinRelation.Correctors.MollifierWeightedEquationAssembly
import EinsteinRelation.Correctors.TranslatedMollifierLocalEquations
import EinsteinRelation.Correctors.ConditionalSpatialTestTransport
import EinsteinRelation.Correctors.SpatialWeakExhaustion

/-! # Spatial equations for one common family of local fields

Source: `paper/main.tex:913–938`. Ordinary local integrability of the
center-zero versions supplies every product-integrability requirement of
the center average. One countable spatial exhaustion gives the whole-space
equations for the same five fields.
-/

open MeasureTheory

namespace EinsteinRelation.Correctors

/-- A local source, multiplied by a supported test and translated jointly
with its center, is integrable in center and space almost surely.
Source: `paper/main.tex:926–938`. -/
theorem ae_integrable_centered_local_spatialTest {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) {B V : Set (Vec d)}
    [IsFiniteMeasure (volume.restrict V)]
    {u : FieldPair d → Vec d → ℝ}
    (hui : Integrable (Function.uncurry u)
      ((reducedEnvironmentLaw Q).prod (volume.restrict B)))
    {w : Vec d → ℝ} (hw : IsSpatialTest B w) :
    ∀ᵐ ω ∂reducedEnvironmentLaw Q, Integrable (fun z : Vec d × Vec d =>
      w (z.2 - z.1) * u (translate z.1 ω) (z.2 - z.1))
      (volume.prod (volume.restrict V)) :=
  ae_integrable_centered_stationary_spatial_field (reducedEnvironmentLaw Q)
    (reducedEnvironmentLaw_stationary Q) (volume.restrict V)
    (integrable_spatialTest_mul_product hui hw).swap

/-- The actual common center averages satisfy both spatial equations.
The assumptions concern only the center-zero local fields and their weak
equations, with no premise about the averaged gradient or flux error.
Source: `paper/main.tex:913–938`. -/
theorem ae_centeredMollifierFields_spatial_equations {d : ℕ} {L r₀ R : ℝ}
    (Q : EnvironmentLaw d L r₀) (hR : 0 < R)
    (u : FieldPair d → Vec d → ℝ) (G : FieldPair d → Vec d → Vec d)
    (S : FieldPair d → Vec d → Mat d) (e b : Vec d)
    (hui : Integrable (Function.uncurry u) ((reducedEnvironmentLaw Q).prod
      (volume.restrict {x : Vec d | euclideanNorm x < 32 * R})))
    (hGi : ∀ j, Integrable (fun z : FieldPair d × Vec d => G z.1 z.2 j)
      ((reducedEnvironmentLaw Q).prod
        (volume.restrict {x : Vec d | euclideanNorm x < 32 * R})))
    (hSi : ∀ j k, Integrable (fun z : FieldPair d × Vec d => S z.1 z.2 j k)
      ((reducedEnvironmentLaw Q).prod
        (volume.restrict {x : Vec d | euclideanNorm x < 32 * R})))
    (hlocal : ∀ᵐ ω ∂reducedEnvironmentLaw Q,
      HasWeakGradient {x : Vec d | euclideanNorm x < 32 * R} (u ω) (G ω) ∧
      HasWeakRowDivergence {x : Vec d | euclideanNorm x < 32 * R} (S ω)
        (fun x => (ω.1 x).mulVec (e + G ω x) - b)) :
    let f := centeredMollifierFields R u G S
    ∀ᵐ ω ∂reducedEnvironmentLaw Q,
      HasWeakGradient Set.univ (orbit f.scalar ω)
        (fun x => f.gradient (translate x ω)) ∧
      HasWeakRowDivergence Set.univ (fun x => f.skew (translate x ω))
        (fun x => (ω.1 x).mulVec (e + f.gradient (translate x ω)) - b -
          f.flux (translate x ω)) := by
  let f := centeredMollifierFields R u G S
  have hw : IsSpatialTest {x : Vec d | euclideanNorm x < 32 * R}
      (Calculus.unitMassScaledMollifier d R) := by
    simpa only [sub_zero] using isSpatialTest_translated_unitMassScaledMollifier hR (0 : Vec d)
  have heq := ae_translated_mollifier_local_equations Q hR u G S e b hlocal
  have hballs (n : ℕ) : ∀ᵐ ω ∂reducedEnvironmentLaw Q,
      HasWeakGradient (Metric.ball 0 ((n : ℝ) + 1)) (orbit f.scalar ω)
        (fun x => f.gradient (translate x ω)) ∧
      HasWeakRowDivergence (Metric.ball 0 ((n : ℝ) + 1))
        (fun x => f.skew (translate x ω))
        (fun x => (ω.1 x).mulVec (e + f.gradient (translate x ω)) - b -
          f.flux (translate x ω)) := by
    let V : Set (Vec d) := Metric.ball 0 ((n : ℝ) + 1)
    haveI : IsFiniteMeasure (volume.restrict V) :=
      isFiniteMeasure_restrict.mpr Metric.isBounded_ball.measure_lt_top.ne
    have hu := ae_integrable_centered_local_spatialTest (V := V) Q hui hw
    have hg := ae_all_iff.mpr fun j =>
      ae_integrable_centered_local_spatialTest (V := V) (u := fun ω x => G ω x j)
        Q (hGi j) hw
    have hdu := ae_all_iff.mpr fun j =>
      ae_integrable_centered_local_spatialTest (V := V) Q hui
        (isSpatialTest_coordinateDerivative hw j)
    have hs := ae_all_iff.mpr fun j => ae_all_iff.mpr fun k =>
      ae_integrable_centered_local_spatialTest (V := V) (u := fun ω x => S ω x j k)
        Q (hSi j k) hw
    have hds := ae_all_iff.mpr fun j => ae_all_iff.mpr fun k =>
      ae_integrable_centered_local_spatialTest (V := V) (u := fun ω x => S ω x j k)
        Q (hSi j k)
        (isSpatialTest_coordinateDerivative hw k)
    filter_upwards [hu, hg, hdu, hs, hds, heq, ae_reduced_coefficient_entry_bound Q]
      with ω hωu hωG hωDu hωS hωDS hωeq hωA
    have hflux (j : Fin d) : Integrable (fun z : Vec d × Vec d =>
        Calculus.unitMassScaledMollifier d R (z.2 - z.1) *
          ((ω.1 z.2).mulVec (e + G (translate z.1 ω) (z.2 - z.1)) - b) j)
        (volume.prod (volume.restrict V)) := by
      have hi (k : Fin d) : Integrable (fun z : Vec d × Vec d =>
          ω.1 z.2 j k * (Calculus.unitMassScaledMollifier d R (z.2 - z.1) *
            (e k + G (translate z.1 ω) (z.2 - z.1) k)))
          (volume.prod (volume.restrict V)) := by
        have hc : Measurable (fun z : Vec d × Vec d => ω.1 z.2 j k) :=
          ((ω.1.continuous.matrix_elem j k).comp continuous_snd).measurable
        have hbase := ((integrable_translated_unitMassScaledMollifier_product hR V).mul_const
          (e k)).add (hωG k)
        have hb := hbase.bdd_mul (c := Real.exp (2 * L) * L) hc.aestronglyMeasurable
          (Filter.Eventually.of_forall fun z => by
            simpa only [Real.norm_eq_abs] using hωA z.2 j k)
        simpa only [Pi.add_apply, mul_add] using hb
      have hi' := (integrable_finset_sum Finset.univ fun k _ => hi k).sub
        ((integrable_translated_unitMassScaledMollifier_product hR V).mul_const (b j))
      convert hi' using 1
      funext z
      simp only [Matrix.mulVec, dotProduct, Pi.sub_apply, Pi.add_apply,
        mul_sub, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun k _ => by ring
    have hK (j : Fin d) : Integrable (fun z : Vec d × Vec d =>
        ((S (translate z.1 ω) (z.2 - z.1)).mulVec
          (gradient (Calculus.unitMassScaledMollifier d R) (z.2 - z.1))) j)
        (volume.prod (volume.restrict V)) := by
      simpa only [Matrix.mulVec, dotProduct, gradient, mul_comm] using
        integrable_finset_sum Finset.univ (fun k _ => hωDS j k)
    have h := hasWeakGradient_and_flux_of_mollifier_weighted_equations hR
      (U := V) Metric.isOpen_ball
      (fun y x => u (translate y ω) (x - y))
      (fun y x => G (translate y ω) (x - y))
      (fun y x => S (translate y ω) (x - y)) (fun x => ω.1 x) e b
      hωu hωG (fun j => by simpa only [mul_comm] using hωDu j)
      hωS hflux hK hωeq
    have ht := centeredMollifierFields_translate R u G S
    have hφ : (fun x => ∫ y, Calculus.unitMassScaledMollifier d R (x - y) *
        u (translate y ω) (x - y)) = orbit f.scalar ω :=
      funext fun x => (ht x ω).1.symm
    have hS : (fun x j k => ∫ y, Calculus.unitMassScaledMollifier d R (x - y) *
        S (translate y ω) (x - y) j k) = fun x => f.skew (translate x ω) := by
      funext x j k
      exact ((ht x ω).2.1 j k).symm
    have hG (x : Vec d) : (fun j =>
        (∫ y, Calculus.unitMassScaledMollifier d R (x - y) * G (translate y ω) (x - y) j) +
        ∫ y, u (translate y ω) (x - y) *
          coordinateDerivative j (Calculus.unitMassScaledMollifier d R) (x - y)) =
        f.gradient (translate x ω) := by
      funext j
      exact congrArg₂ (· + ·) ((ht x ω).2.2.1 j).symm ((ht x ω).2.2.2.1 j).symm
    have hH (x : Vec d) : (fun j => ∫ y, u (translate y ω) (x - y) *
        coordinateDerivative j (Calculus.unitMassScaledMollifier d R) (x - y)) =
        f.scalarCorrection (translate x ω) := by
      funext j
      exact ((ht x ω).2.2.2.1 j).symm
    have hK' (x : Vec d) : (fun j => ∫ y, ((S (translate y ω) (x - y)).mulVec
        (gradient (Calculus.unitMassScaledMollifier d R) (x - y))) j) =
        f.skewCorrection (translate x ω) := by
      funext j
      exact ((ht x ω).2.2.2.2 j).symm
    dsimp only at h
    rw [hφ, hS, funext hG] at h
    simp_rw [hG, hH, hK'] at h
    simpa only [LocalCorrectorFields.flux, translate_matrix, add_zero] using h
  filter_upwards [ae_all_iff.mpr hballs] with ω hω
  exact ⟨hasWeakGradient_univ_of_ball _ _ (fun n => (hω n).1),
    hasWeakRowDivergence_univ_of_ball _ _ (fun n => (hω n).2)⟩

end EinsteinRelation.Correctors
