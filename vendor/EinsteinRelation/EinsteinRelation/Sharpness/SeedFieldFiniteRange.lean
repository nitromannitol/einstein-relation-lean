import EinsteinRelation.Calculus.Mollifier
import EinsteinRelation.External.WhiteNoise
import EinsteinRelation.Sharpness.NoiseFieldIndependence
import EinsteinRelation.Sharpness.NoiseMollifier
import EinsteinRelation.Sharpness.SeedField
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.Probability.Independence.Basic
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Hom.ContinuousEvalConst

/-! # Independence of the canonical seed field at separated outer families

Source: `paper/main.tex:1212–1216`, the environment `h ≔ ζ * tanh(K * W)` in the proof of
`sharp.example`. The canonical seed field `seedField d` is the smoothed field of
`mollifierNoiseTest d` used as both `ζ` and `K` (`Sharpness/SeedField.lean`). Its compact-open
law is `seedFieldLaw P`, the pushforward of the white-noise law `P` by `seedContinuousField`.

Both results below are fully proved from the frozen white-noise input
`External.IsWhiteNoiseLaw`, with no extra support or cardinality premise:
1. `indepFun_seedField_processes_of_separated`: the seed field processes at two outer families
   whose Euclidean separations exceed `4` are independent.
2. `indepFun_seedFieldLaw_evaluations_of_separated`: the evaluation processes of the compact-open
   seed law are independent, for the compact-open Borel σ-algebra on `C(Vec d, ℝ)`.

The separation `4` is `2 * (Rζ + RK)` with `Rζ = RK = 1`, the Euclidean support radius of the
unit-mass kernel. These statements close only the scalar seed-law range. They do not prove the
physical `(a0, V)` derivative bounds, nondegeneracy, or the final sharpness theorem. -/

open MeasureTheory

namespace EinsteinRelation.Sharpness

/-- The unit-mass kernel is supported in the closed Euclidean unit ball: a nonzero value gives
membership in the topological support, which lies in the open unit ball. -/
private theorem euclideanNorm_le_one_of_ne_zero_mollifierNoiseTest {d : ℕ} (u : Vec d)
    (hu : mollifierNoiseTest d u ≠ 0) : euclideanNorm u ≤ 1 := by
  have hmoll : mollifier d u ≠ 0 := hu
  have hmem : u ∈ tsupport (mollifier d) :=
    subset_tsupport (mollifier d) (Function.mem_support.mpr hmoll)
  have hlt : euclideanNorm u < 1 := tsupport_mollifier_subset d hmem
  exact hlt.le

/-- Evaluation at one point is Borel measurable on the compact-open continuous-field space. -/
private theorem measurable_seedFieldLaw_eval {d : ℕ} (x : Vec d) :
    @Measurable C(Vec d, ℝ) ℝ (borel C(Vec d, ℝ)) inferInstance (fun H : C(Vec d, ℝ) => H x) :=
  (continuous_eval_const x : Continuous (fun H : C(Vec d, ℝ) => H x)).borel_measurable

/-- The finite evaluation vector `H ↦ (H (xs s))_{s : S}` is Borel measurable for the
compact-open Borel σ-algebra, with the product σ-algebra on `S → ℝ`. -/
private theorem measurable_seedFieldLaw_evaluations {d : ℕ} (S : Type*) (xs : S → Vec d) :
    @Measurable C(Vec d, ℝ) (S → ℝ) (borel C(Vec d, ℝ)) MeasurableSpace.pi
      (fun H : C(Vec d, ℝ) => fun s : S => H (xs s)) :=
  @Measurable.of_eval C(Vec d, ℝ) S (fun _ => ℝ) (borel C(Vec d, ℝ)) _
    (fun H : C(Vec d, ℝ) => fun s : S => H (xs s))
    (fun s => measurable_seedFieldLaw_eval (xs s))

/-- The compact-open seed law gives a Borel set the noise probability of its preimage under the
measurable map `seedContinuousField d`. -/
private theorem seedFieldLaw_apply_of_measurableSet {d : ℕ} {P : Measure (NoiseSample d)}
    {A : Set C(Vec d, ℝ)} (hA : @MeasurableSet C(Vec d, ℝ) (borel C(Vec d, ℝ)) A) :
    seedFieldLaw P A = P (seedContinuousField d ⁻¹' A) := by
  unfold seedFieldLaw
  exact Measure.map_apply (measurable_seedContinuousField d) hA

/-- Joint independence of the canonical seed field `seedField d` at two outer families separated
by more than `4`. Source: `paper/main.tex:1212–1216`. The statement assumes only the frozen
white-noise input `External.IsWhiteNoiseLaw P`. -/
theorem indepFun_seedField_processes_of_separated {d : ℕ} {P : Measure (NoiseSample d)}
    (hP : External.IsWhiteNoiseLaw P) (S T : Type*) (xs : S → Vec d) (zs : T → Vec d)
    (hsep : ∀ s t, (4 : ℝ) < euclideanNorm (xs s-zs t)) :
  ProbabilityTheory.IndepFun (fun W : NoiseSample d => fun s : S => seedField d W (xs s))
    (fun W : NoiseSample d => fun t : T => seedField d W (zs t)) P := by
  letI : IsProbabilityMeasure P := hP.1
  exact indepFun_smoothedNoiseField_processes_of_separated P id
    (fun f => External.measurable_noiseEvaluation f) hP.2
    (mollifierNoiseTest d) (mollifierNoiseTest d) 1 1
    (fun u hu => euclideanNorm_le_one_of_ne_zero_mollifierNoiseTest u hu)
    (fun u hu => euclideanNorm_le_one_of_ne_zero_mollifierNoiseTest u hu)
    S T xs zs (fun s t => lt_of_eq_of_lt (by norm_num) (hsep s t))

/-- Joint independence of the evaluation processes of the compact-open seed law `seedFieldLaw P`
at two outer families separated by more than `4`. Source: `paper/main.tex:1212–1216`. The σ-algebra
on `C(Vec d, ℝ)` is the existing compact-open Borel σ-algebra `borel C(Vec d, ℝ)`, given by the
`letI` in the statement and not a new global instance. -/
theorem indepFun_seedFieldLaw_evaluations_of_separated {d : ℕ}
    {P : Measure (NoiseSample d)} (hP : External.IsWhiteNoiseLaw P)
    (S T : Type*) (xs : S → Vec d) (zs : T → Vec d)
    (hsep : ∀ s t, (4 : ℝ) < euclideanNorm (xs s-zs t)) :
  letI : MeasurableSpace C(Vec d, ℝ) := borel C(Vec d, ℝ)
  ProbabilityTheory.IndepFun (fun H : C(Vec d, ℝ) => fun s : S => H (xs s))
    (fun H : C(Vec d, ℝ) => fun t : T => H (zs t)) (seedFieldLaw P) := by
  have hX := measurable_seedFieldLaw_evaluations S xs
  have hY := measurable_seedFieldLaw_evaluations T zs
  refine ProbabilityTheory.indepFun_iff_measure_inter_preimage_eq_mul.2 ?_
  intro u v hu hv
  have hind :=
    (indepFun_seedField_processes_of_separated hP S T xs zs hsep).measure_inter_preimage_eq_mul
      u v hu hv
  rw [seedFieldLaw_apply_of_measurableSet ((hX hu).inter (hY hv)),
    seedFieldLaw_apply_of_measurableSet (hX hu), seedFieldLaw_apply_of_measurableSet (hY hv)]
  exact hind

end EinsteinRelation.Sharpness
