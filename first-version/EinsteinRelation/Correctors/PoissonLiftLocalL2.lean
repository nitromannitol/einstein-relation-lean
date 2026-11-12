import EinsteinRelation.Correctors.PoissonLift
import EinsteinRelation.Correctors.SpatialBallLocalL2
import Mathlib.MeasureTheory.Function.LpSeminorm.Prod
import Mathlib.MeasureTheory.SpecificCodomains.Pi

/-! Source: `paper/main.tex:735-739`. Local L² functions remain locally
L² after adding the independent height coordinate. -/
open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM

/-- Dropping the height coordinate does not increase the Euclidean norm. -/
theorem euclideanNorm_poissonLiftBase_le {d : ℕ} (x : Vec (d + 1)) :
    euclideanNorm (poissonLiftBase x) ≤ euclideanNorm x := by
  apply Real.sqrt_le_sqrt
  change (∑ i : Fin d, x i.succ * x i.succ) ≤ ∑ i : Fin (d + 1), x i * x i
  rw [Fin.sum_univ_succ]
  exact le_add_of_nonneg_left (mul_self_nonneg (x 0))

/-- Pullback to a ball in one higher dimension preserves L². The proof
uses the actual coordinate product Lebesgue measure on a finite cylinder. -/
theorem memLp_poissonLiftBase_on_ball {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] (f : Vec d → E) (R : ℝ) (_hR : 0 < R)
    (hf : MemLp f 2 (volume.restrict (ball 0 R))) :
    MemLp (fun x : Vec (d + 1) => f (poissonLiftBase x)) 2
      (volume.restrict (ball 0 R)) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0
  have hb : MeasurableSet (ball (0 : Vec d) R) := by
    unfold ball euclideanNorm euclideanSq dot
    exact (isOpen_lt (by fun_prop) continuous_const).measurableSet
  let s : Set (ℝ × Vec d) := Set.Icc (-R) R ×ˢ ball 0 R
  have hs : MeasurableSet s := measurableSet_Icc.prod hb
  have hmp := (volume_preserving_piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0).restrict_preimage hs
  have hp : MemLp (fun p : ℝ × Vec d => f p.2) 2
      ((volume : Measure (ℝ × Vec d)).restrict s) := by
    simpa only [Measure.prod_restrict] using
      hf.comp_snd (volume.restrict (Set.Icc (-R) R))
  have ht := hp.comp_measurePreserving hmp
  have he : (fun x : Vec (d + 1) => f ((e x).2)) =
      (fun x => f (poissonLiftBase x)) := rfl
  change MemLp (fun x => f ((e x).2)) 2 (volume.restrict (e ⁻¹' s)) at ht
  rw [he] at ht
  apply ht.mono_measure
  apply Measure.restrict_mono_set
  intro x hx
  change x 0 ∈ Set.Icc (-R) R ∧ poissonLiftBase x ∈ ball (0 : Vec d) R
  have hx' : euclideanNorm x < R := by simpa only [ball, sub_zero] using hx
  have habs := Regeneration.coordinate_abs_le_euclideanNorm x 0
  refine ⟨?_, ?_⟩
  · exact abs_le.mp (habs.trans hx'.le)
  · simpa only [ball, sub_zero] using (euclideanNorm_poissonLiftBase_le x).trans_lt hx'

/-- The lifted potential and its explicit gradient are locally L² in the
higher dimensional coordinate measure. -/
theorem memLp_poissonLift_potential_gradient {d : ℕ}
    (u : Vec d → ℝ) (g : Vec d → Vec d) (M R : ℝ) (hR : 0 < R)
    (hu : MemLp u 2 (volume.restrict (ball 0 R)))
    (hg : MemLp g 2 (volume.restrict (ball 0 R))) :
    MemLp (poissonLiftPotential u M) 2 (volume.restrict (ball 0 R)) ∧
      MemLp (poissonLiftGradient g M) 2 (volume.restrict (ball 0 R)) := by
  have hsub : ball (0 : Vec (d + 1)) R ⊆ Metric.closedBall 0 R := by
    intro x hx
    have hx' : euclideanNorm x < R := by simpa only [ball, sub_zero] using hx
    rw [Metric.mem_closedBall, dist_pi_le_iff hR.le]
    intro j
    simpa only [Pi.zero_apply, Real.dist_eq, sub_zero] using
      (Regeneration.coordinate_abs_le_euclideanNorm x j).trans hx'.le
  have hfin : volume (ball (0 : Vec (d + 1)) R) < ⊤ :=
    lt_of_le_of_lt (measure_mono hsub) (isCompact_closedBall (0 : Vec (d + 1)) R).measure_lt_top
  letI : IsFiniteMeasure (volume.restrict (ball (0 : Vec (d + 1)) R)) :=
    ⟨by simpa using hfin⟩
  have hheight : MemLp (fun x : Vec (d + 1) => x 0) 2
      (volume.restrict (ball 0 R)) := by
    apply MemLp.of_bound (continuous_apply 0).aestronglyMeasurable R
    filter_upwards [ae_restrict_mem (by
      unfold ball euclideanNorm euclideanSq dot
      exact (isOpen_lt (by fun_prop) continuous_const).measurableSet)] with x hx
    change |x 0| ≤ R
    have hx' : euclideanNorm x < R := by simpa only [ball, sub_zero] using hx
    exact (Regeneration.coordinate_abs_le_euclideanNorm x 0).trans hx'.le
  constructor
  · exact (memLp_poissonLiftBase_on_ball u R hR hu).add (hheight.const_mul M)
  · apply memLp_pi_iff.mpr
    intro j
    refine Fin.cases ?_ (fun k => ?_) j
    · simpa only [poissonLiftGradient, Fin.cons_zero] using
        (memLp_const M : MemLp (fun _ : Vec (d + 1) => M) 2
          (volume.restrict (ball 0 R)))
    · simpa only [poissonLiftGradient, Fin.cons_succ] using
        (memLp_poissonLiftBase_on_ball g R hR hg).eval k

end EinsteinRelation.Correctors
