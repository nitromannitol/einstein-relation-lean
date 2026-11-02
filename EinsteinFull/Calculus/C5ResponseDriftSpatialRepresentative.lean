import EinsteinFull.Blueprint.G4.node_p_u3A_response_u23_cesaro_u2D_abel
import EinsteinFull.Calculus.S4GeneratorBridgeSupport
import EinsteinRelation.Calculus.GeneratorMeasurability
import EinsteinRelation.Calculus.HorizontalTranslationLp

open MeasureTheory
namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- The actual forced drift observation agrees with its spatial representative
on almost every physical environment and almost every spatial point. -/
theorem response_forced_drift_observation_spatial_ae
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q))
    (hβ : IsReducedDriftObservation Q hQ β)
    (ha : IsReducedCoefficientObservation Q a) (lam : ℝ) :
    ∀ᵐ ω ∂Q.measure, ∀ j : Fin d,
      (fun x : Vec d =>
        (β j + (lam : ℂ) • a (⟨0, by omega⟩ : Fin d) j)
          (translate x (reduce ω))) =ᵐ[(volume : Measure (Vec d))]
        (fun x : Vec d =>
          (forcedDrift (reducedCoefficient ω) (⟨0, by omega⟩ : Fin d) lam x j : ℂ)) := by
  let i : Fin d := ⟨0, by omega⟩
  have hj : ∀ j : Fin d, ∀ᵐ ω ∂Q.measure, ∀ᵐ x ∂(volume : Measure (Vec d)),
      (β j + (lam : ℂ) • a i j) (translate x (reduce ω)) =
        (forcedDrift (reducedCoefficient ω) i lam x j : ℂ) := by
    intro j
    let f : FieldPair d → ℂ := fun ω => (β j + (lam : ℂ) • a i j) (reduce ω)
    let g : FieldPair d → ℂ := fun ω =>
      (((1 / 2 : ℝ) * ∑ k, coordinateDerivative k
        (fun y => (reduce ω).1 y k j) 0 : ℝ) : ℂ) +
          (lam : ℂ) * ((reduce ω).1 0 i j : ℂ)
    have hf : Measurable f :=
      (Lp.stronglyMeasurable _).measurable.comp Probability.measurable_reduce
    have hder : ∀ k : Fin d, Measurable (fun ω : FieldPair d =>
        coordinateDerivative k (fun y => ω.1 y k j) 0) := by
      intro k
      have hc : Continuous (fun p : FieldPair d × Vec d => p.1.1 p.2 k j) :=
        (continuous_apply j).comp ((continuous_apply k).comp
          (continuous_fst.fst.eval continuous_snd))
      exact (measurable_fderiv_apply_const_with_param ℝ
        (f := fun (ω : FieldPair d) (y : Vec d) => ω.1 y k j) hc (unitVector k)).comp
        (measurable_id.prodMk measurable_const)
    have hentry : Continuous (fun ω : FieldPair d => ω.1 0 i j) :=
      (continuous_apply j).comp ((continuous_apply i).comp
        ((continuous_eval_const (0 : Vec d)).comp continuous_fst))
    have hg : Measurable g := by
      apply Measurable.add
      · exact Complex.measurable_ofReal.comp (measurable_const.mul
          (Finset.measurable_sum _ (fun k _ => (hder k).comp Probability.measurable_reduce)))
      · exact measurable_const.mul (Complex.measurable_ofReal.comp
          (hentry.measurable.comp Probability.measurable_reduce))
    have hred : (β j + (lam : ℂ) • a i j : Lp ℂ 2 (reducedLaw Q)) =ᵐ[reducedLaw Q]
        (fun ω => (((1 / 2 : ℝ) * ∑ k, coordinateDerivative k
          (fun y => ω.1 y k j) 0 : ℝ) : ℂ) + (lam : ℂ) * (ω.1 0 i j : ℂ)) := by
      filter_upwards [Lp.coeFn_add (β j) ((lam : ℂ) • a i j),
        Lp.coeFn_smul (lam : ℂ) (a i j), hβ j, ha i j] with ω hadd hsmul hb hc
      rw [hadd]
      change β j ω + ((lam : ℂ) • a i j) ω = _
      rw [hsmul]
      change β j ω + (lam : ℂ) * a i j ω = _
      rw [hb, hc]
    have hfg : f =ᵐ[Q.measure] g :=
      ae_of_ae_map Probability.measurable_reduce.aemeasurable hred
    have horbit : ∀ᵐ ω ∂Q.measure, ∀ᵐ x ∂(volume : Measure (Vec d)),
        f (translate x ω) = g (translate x ω) := by
      apply (Measure.ae_ae_comm ?_).mp
        (ae_of_all _ fun x =>
          (measurePreserving_translate Q.measure Q.stationary x).quasiMeasurePreserving.ae hfg)
      exact measurableSet_eq_fun
        (hf.comp Probability.continuous_translate.measurable)
        (hg.comp Probability.continuous_translate.measurable)
    filter_upwards [horbit, Q.regular] with ω hω hreg
    filter_upwards [hω] with x hx
    have hsym : (reducedCoefficient ω x) i j = (reducedCoefficient ω x) j i := by
      have hs := congrArg (fun M : Mat d => M j i) (hreg.1 x).1
      change ω.1 x i j = ω.1 x j i at hs
      exact congrArg (fun z : ℝ => clockDensity ω x * z) hs
    have hmul : ((reducedCoefficient ω x).mulVec (unitVector i)) j =
        reducedCoefficient ω x j i := by
      exact congrFun (Matrix.mulVec_single_one (reducedCoefficient ω x) i) j
    change (β j + (lam : ℂ) • a i j) (reduce (translate x ω)) =
      (((1 / 2 : ℝ) * ∑ k, coordinateDerivative k
        (fun y => (reduce (translate x ω)).1 y k j) 0 : ℝ) : ℂ) +
          (lam : ℂ) * ((reduce (translate x ω)).1 0 i j : ℂ) at hx
    rw [reduce_translate] at hx
    have hshift (k : Fin d) :
        fderiv ℝ (fun y => (reduce ω).1 (x + y) k j) 0 =
          fderiv ℝ (fun y => (reduce ω).1 y k j) x := by
      simpa only [add_zero] using
        (fderiv_comp_add_left (𝕜 := ℝ)
          (f := fun y => (reduce ω).1 y k j) (x := 0) x)
    simp only [translate_matrix, coordinateDerivative, hshift, add_zero] at hx
    change (β j + (lam : ℂ) • a i j) (translate x (reduce ω)) =
      (((1 / 2 : ℝ) * ∑ k, coordinateDerivative k
        (fun y => reducedCoefficient ω y k j) x : ℝ) : ℂ) +
          (lam : ℂ) * (reducedCoefficient ω x i j : ℂ) at hx
    simpa only [forcedDrift, matrixDivDrift, hmul, ← hsym,
      Complex.ofReal_add, Complex.ofReal_mul] using hx
  exact (ae_all_iff.mpr hj)

end EinsteinFull.Blueprint
