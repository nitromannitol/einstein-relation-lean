import EinsteinRelation.Regeneration.Coupling
import EinsteinRelation.Regeneration.Measurability
import EinsteinRelation.Probability.LocalSigma
import EinsteinRelation.Probability.PathMaps
import EinsteinRelation.Probability.ProbabilityPart
import EinsteinRelation.Probability.ReductionLocality
import Mathlib.Probability.Kernel.MeasurableIntegral

/-! # Joint measurability of the killed future expectation

Source `paper/main.tex:377–403`, with `B_Φ(y,ω)` defined at lines 387–390. The killed
future test is jointly measurable in the physical starting point `y`, the environment `ω`,
and the coupled sample `z`. Its kernel integral against the finite part `probabilityPart K`
is then jointly measurable in `(y, ω)`, which is the measurability needed for Fubini.

Only joint measurability is proved here. The a.e. identifications with the actual kernel
`K` use the origin qualifier `hK.1` and the product-a.e. qualifier `hK.2` directly. No
future locality, factorization, stationarity, or renewal is assumed or concluded.
-/

open MeasureTheory
open scoped NNReal ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

namespace EinsteinRelation.Regeneration

/-- The spatially recentered path, the bits of the sample, and the translated reduced
environment restricted to the future half-space, as one measurable map of the physical
starting point, the environment, and the coupled sample. The environment factor is
evaluated only at fixed future points after the joint physical reduction and translation. -/
theorem measurable_spatial_future_triple {d : ℕ} (R : ℝ) (i : Fin d) :
 Measurable (fun p : (Vec d × FieldPair d) × CoupledSample d =>
   ((recenterSample p.1.1 p.2).1, p.2.2,
    fun x : FutureHalfSpace d i R =>
     ((translate p.1.1 (reduce p.1.2)).1 x, (translate p.1.1 (reduce p.1.2)).2 x))) := by
  have hx : Measurable (fun p : (Vec d × FieldPair d) × CoupledSample d => p.1.1) :=
    measurable_fst.fst
  have hEnv : Measurable (fun p : (Vec d × FieldPair d) × CoupledSample d => p.1.2) :=
    measurable_fst.snd
  have hz : Measurable (fun p : (Vec d × FieldPair d) × CoupledSample d => p.2.1) :=
    measurable_snd.fst
  have hbits : Measurable (fun p : (Vec d × FieldPair d) × CoupledSample d => p.2.2) :=
    measurable_snd.snd
  -- Path part: joint continuity of recentering, composed with measurable projections.
  have hpath : Measurable (fun p : (Vec d × FieldPair d) × CoupledSample d =>
      (recenterSample p.1.1 p.2).1) :=
    Probability.continuous_path_recenter.measurable.comp (hx.prodMk hz)
  -- Environment part: joint physical reduction and translation.
  have hred : Measurable (fun p : (Vec d × FieldPair d) × CoupledSample d =>
      reduce p.1.2) :=
    Probability.measurable_reduce.comp hEnv
  have hH : Measurable (fun p : (Vec d × FieldPair d) × CoupledSample d =>
      translate p.1.1 (reduce p.1.2)) :=
    Probability.continuous_translate.measurable.comp (hx.prodMk hred)
  -- Each raw coordinate is evaluated at a fixed future point after the joint translation.
  have hcoord : ∀ x : FutureHalfSpace d i R,
      Measurable (fun p : (Vec d × FieldPair d) × CoupledSample d =>
        ((translate p.1.1 (reduce p.1.2)).1 x, (translate p.1.1 (reduce p.1.2)).2 x)) := by
    intro x
    have heval : Continuous (fun ω : FieldPair d => (ω.1 (x : Vec d), ω.2 (x : Vec d))) :=
      (continuous_fst.eval continuous_const).prodMk (continuous_snd.eval continuous_const)
    exact heval.measurable.comp hH
  have hfield : Measurable (fun p : (Vec d × FieldPair d) × CoupledSample d =>
      fun x : FutureHalfSpace d i R =>
        ((translate p.1.1 (reduce p.1.2)).1 x, (translate p.1.1 (reduce p.1.2)).2 x)) :=
    measurable_pi_iff.mpr hcoord
  exact hpath.prodMk (hbits.prodMk hfield)

/-- The killed future test on the physical starting point, the environment, and the
coupled sample: the source integrand of `B_Φ` (paper lines 387–390), killed by
`NoBacktracking` on the path. -/
private theorem measurable_killed_future_test {d : ℕ} (R : ℝ) (i : Fin d)
    (Φ : FutureState d i R → ℝ) (hΦ : Measurable Φ) :
    Measurable (fun q : (Vec d × FieldPair d) × CoupledSample d =>
      if NoBacktracking R q.2.1 i then Φ ((recenterSample q.1.1 q.2).1, q.2.2,
        fun x : FutureHalfSpace d i R =>
          ((translate q.1.1 (reduce q.1.2)).1 x, (translate q.1.1 (reduce q.1.2)).2 x))
      else 0) := by
  have hpath : Measurable (fun q : (Vec d × FieldPair d) × CoupledSample d => q.2.1) :=
    measurable_snd.fst
  have hset : MeasurableSet {q : (Vec d × FieldPair d) × CoupledSample d |
      NoBacktracking R q.2.1 i} :=
    (measurableSet_NoBacktracking R i).preimage hpath
  exact Measurable.ite hset (hΦ.comp (measurable_spatial_future_triple R i)) measurable_const

/-- Source `paper/main.tex:377–403`: the killed future expectation `B_Φ(y,ω)` is jointly
measurable in the starting point and the environment, and it agrees with the actual kernel
`K` at the origin for `Q`-a.e. `ω` and for `volume.prod Q`-a.e. `(y, ω)`. -/
theorem exists_measurable_killed_future_expectation {d : ℕ} (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
 (K : CoupledQuenchedLaws d) (_hK : HasProbabilityLaws Q K) (R : ℝ) (i : Fin d)
 (Φ : FutureState d i R → ℝ) (_hΦ : Measurable Φ) (_hb : BoundedRealTest Φ) :
 ∃ B : Vec d × FieldPair d → ℝ, Measurable B ∧
  (∀ᵐ ω ∂Q, B (0,ω) = ∫ z,
   (if NoBacktracking R z.1 i then Φ ((recenterSample (0 : Vec d) z).1,z.2,
    fun x : FutureHalfSpace d i R => ((translate (0 : Vec d) (reduce ω)).1 x,
     (translate (0 : Vec d) (reduce ω)).2 x)) else 0) ∂K (0,ω)) ∧
  B =ᵐ[((volume : Measure (Vec d)).prod Q)] (fun xω => ∫ z,
   (if NoBacktracking R z.1 i then Φ ((recenterSample xω.1 z).1,z.2,
    fun x : FutureHalfSpace d i R => ((translate xω.1 (reduce xω.2)).1 x,
     (translate xω.1 (reduce xω.2)).2 x)) else 0) ∂K xω) := by
  have hF := measurable_killed_future_test R i Φ _hΦ
  -- Kernel integral against the finite part of `K`, which is jointly measurable.
  have hBm : Measurable (fun xω : Vec d × FieldPair d => ∫ z,
      (if NoBacktracking R z.1 i then Φ ((recenterSample xω.1 z).1,z.2,
        fun x : FutureHalfSpace d i R => ((translate xω.1 (reduce xω.2)).1 x,
         (translate xω.1 (reduce xω.2)).2 x)) else 0) ∂(Probability.probabilityPart K xω)) :=
    stronglyMeasurable_iff_measurable.mp
      (hF.stronglyMeasurable.integral_kernel_prod_right' (κ := Probability.probabilityPart K))
  refine ⟨_, hBm, ?_, ?_⟩
  · -- Origin qualifier: `hK.1` makes each origin fibre a probability measure.
    filter_upwards [_hK.1] with ω hω
    haveI := hω
    simp only [Probability.probabilityPart_eq_of_isProbabilityMeasure K (0, ω)]
  · -- Product-a.e. qualifier: `hK.2` gives the a.e. identity of the finite part with `K`.
    filter_upwards [Probability.probabilityPart_ae_eq
      ((volume : Measure (Vec d)).prod Q) K _hK.2] with xω hxω
    simp only [hxω]

end EinsteinRelation.Regeneration
