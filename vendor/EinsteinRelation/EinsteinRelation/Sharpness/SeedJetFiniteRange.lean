import EinsteinRelation.Calculus.Mollifier
import EinsteinRelation.External.WhiteNoise
import EinsteinRelation.Sharpness.CoordinateIterates
import EinsteinRelation.Sharpness.NoiseDerivativeLocality
import EinsteinRelation.Sharpness.NoiseLocality
import EinsteinRelation.Sharpness.NoiseMollifier
import EinsteinRelation.Sharpness.NoiseProcessIndependence
import EinsteinRelation.Sharpness.SeedField
import EinsteinRelation.TimeChange.EuclideanTransport
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! # Joint independence of the seed field's coordinate-derivative jets

Source: `paper/main.tex:1212–1231`, the environment `h ≔ ζ * tanh(K * W)` of the proof of
`sharp.example`, with the proved unit-mass kernel as both `ζ` and `K` (`Sharpness/SeedField.lean`),
and its actual smooth coordinate derivatives used by the physical jet consumers.

For outer families `xs : S → Vec d` and `zs : T → Vec d` whose Euclidean separations exceed `4`,
the whole arrays of iterated coordinate derivatives of the seed field, indexed by
`S × List (Fin d)` and `T × List (Fin d)`, are independent. This is joint independence of the
entire arrays, not pairwise independence of single derivatives, and it assumes only the frozen
white-noise input `External.IsWhiteNoiseLaw P`.

The proof follows `NoiseFieldIndependence` with two changes:
1. The raw observations are indexed by `tsupport ζ`, not by `{y | ζ y ≠ 0}`. An iterated derivative
   of `ζ * tanh(K * W)` at `x` is measurable for the observations `(K * W)(x - y)` with
   `y ∈ tsupport ζ` (`measurable_iterated_smoothedNoiseField_local`), because a derivative of `ζ`
   may be nonzero at a point where `ζ` vanishes.
2. Cross-family orthogonality uses the norm bound on all of `tsupport ζ`, which for the unit-mass
   kernel lies in the open Euclidean unit ball, rather than a bound on `{ζ ≠ 0}`. No equivalence of
   these two index sets is assumed.
-/

open MeasureTheory
open EinsteinRelation.TimeChange

namespace EinsteinRelation.Sharpness

private theorem seedJet_euclideanNorm_neg {d : ℕ} (v : Vec d) :
    euclideanNorm (-v) = euclideanNorm v := by
  rw [← neg_one_smul ℝ v, euclideanNorm_smul]
  norm_num

/-- Every point of the topological support of the unit-mass kernel lies in the closed Euclidean
unit ball; the support is contained in the open ball. -/
private theorem euclideanNorm_le_one_of_mem_tsupport_mollifier {d : ℕ} (u : Vec d)
    (hu : u ∈ tsupport (mollifier d)) : euclideanNorm u ≤ 1 := by
  have hlt : euclideanNorm u < 1 := tsupport_mollifier_subset d hu
  exact hlt.le

/-- Euclidean separation of the reflected kernel tests. If `x - z` has norm greater than `4` and
`y`, `w` lie in the closed unit ball, then `(x - y) - (z - w)` has norm greater than `2 * 1`. -/
private theorem two_lt_euclideanNorm_outer_sub {d : ℕ} (x z y w : Vec d)
    (hy : euclideanNorm y ≤ 1) (hw : euclideanNorm w ≤ 1)
    (hsep : (4 : ℝ) < euclideanNorm (x - z)) :
    2 * (1 : ℝ) < euclideanNorm ((x - y) - (z - w)) := by
  have hyw : euclideanNorm (y - w) ≤ euclideanNorm y + euclideanNorm w := by
    have h := euclideanNorm_add_le y (-w)
    rw [seedJet_euclideanNorm_neg, ← sub_eq_add_neg] at h
    exact h
  have hid : x - z = ((x - y) - (z - w)) + (y - w) := by abel
  have htri : euclideanNorm (x - z) ≤
      euclideanNorm ((x - y) - (z - w)) + euclideanNorm (y - w) := by
    rw [hid]
    exact euclideanNorm_add_le _ _
  linarith

/-- Cross-family orthogonality of the reflected unit-mass kernel tests at points of the
topological support. The pointwise product vanishes everywhere, so the integral is zero. -/
private theorem integral_kernelTest_tsupport_mul_eq_zero {d : ℕ} (x z y w : Vec d)
    (hy : y ∈ tsupport (mollifierNoiseTest d : Vec d → ℝ))
    (hw : w ∈ tsupport (mollifierNoiseTest d : Vec d → ℝ))
    (hsep : (4 : ℝ) < euclideanNorm (x - z)) :
    (∫ u : Vec d, kernelTest (mollifierNoiseTest d) (x - y) u *
      kernelTest (mollifierNoiseTest d) (z - w) u) = 0 := by
  have hmy : y ∈ tsupport (mollifier d) := hy
  have hmw : w ∈ tsupport (mollifier d) := hw
  have hsep' := two_lt_euclideanNorm_outer_sub x z y w
    (euclideanNorm_le_one_of_mem_tsupport_mollifier y hmy)
    (euclideanNorm_le_one_of_mem_tsupport_mollifier w hmw) hsep
  have hK : ∀ u : Vec d, mollifierNoiseTest d u ≠ 0 → euclideanNorm u ≤ 1 := by
    intro u hu
    have hmoll : mollifier d u ≠ 0 := hu
    exact euclideanNorm_le_one_of_mem_tsupport_mollifier u
      (subset_tsupport (mollifier d) (Function.mem_support.mpr hmoll))
  have hpt : ∀ u : Vec d, kernelTest (mollifierNoiseTest d) (x - y) u *
      kernelTest (mollifierNoiseTest d) (z - w) u = 0 :=
    fun u => kernelTest_mul_eq_zero_of_separated (mollifierNoiseTest d) 1 hK (x - y) (z - w)
      hsep' u
  simp only [hpt, integral_zero]

/-- Joint independence of the raw kernel observations `(K * W)(xs s - y)` indexed by
`S × tsupport ζ`, against `(K * W)(zs t - w)` indexed by `T × tsupport ζ`, with `ζ = K` the
unit-mass kernel. This is the orthogonal-block theorem applied to the reflected kernel tests. -/
private theorem indepFun_tsupport_observations {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {d : ℕ} (W : Ω → NoiseSample d)
    (hmeas : ∀ f : NoiseTest d, Measurable (fun ω => W ω f))
    (hwhite : ∀ (f : NoiseTest d) (r : ℝ),
      (∫ ω, Complex.exp (Complex.I * (r : ℂ) * (W ω f : ℂ)) ∂P) =
        Complex.exp (((-(1/2 : ℝ))*r^2*∫ y : Vec d, (f y)^2) : ℂ))
    (S T : Type) (xs : S → Vec d) (zs : T → Vec d)
    (hsep : ∀ s t, (4 : ℝ) < euclideanNorm (xs s - zs t)) :
    ProbabilityTheory.IndepFun
      (fun ω (p : S × tsupport (mollifierNoiseTest d : Vec d → ℝ)) =>
        mollifiedNoise (W ω) (mollifierNoiseTest d) (xs p.1 - p.2.1))
      (fun ω (q : T × tsupport (mollifierNoiseTest d : Vec d → ℝ)) =>
        mollifiedNoise (W ω) (mollifierNoiseTest d) (zs q.1 - q.2.1)) P :=
  indepFun_noise_processes_of_orthogonal P W hmeas hwhite
    (S × tsupport (mollifierNoiseTest d : Vec d → ℝ))
    (T × tsupport (mollifierNoiseTest d : Vec d → ℝ))
    (fun p => kernelTest (mollifierNoiseTest d) (xs p.1 - p.2.1))
    (fun q => kernelTest (mollifierNoiseTest d) (zs q.1 - q.2.1))
    (fun i j => integral_kernelTest_tsupport_mul_eq_zero (xs i.1) (zs j.1) i.2.1 j.2.1 i.2.2 j.2.2
      (hsep i.1 j.1))

/-- Independence transfers to any pair of random elements measurable for the σ-algebras generated
by the two sides. Only the comparisons `comap X ≤ comap U` and `comap Y ≤ comap V` are used. -/
private theorem indepFun_of_comap_measurable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {α β γ δ : Type*} [mα : MeasurableSpace α] [mβ : MeasurableSpace β]
    [mγ : MeasurableSpace γ] [mδ : MeasurableSpace δ] {U : Ω → α} {V : Ω → β} {X : Ω → γ}
    {Y : Ω → δ} (hUV : ProbabilityTheory.IndepFun U V P)
    (hX : @Measurable Ω γ (MeasurableSpace.comap U mα) mγ X)
    (hY : @Measurable Ω δ (MeasurableSpace.comap V mβ) mδ Y) :
    ProbabilityTheory.IndepFun X Y P := by
  have hind : ProbabilityTheory.Indep (MeasurableSpace.comap U mα)
      (MeasurableSpace.comap V mβ) P :=
    (ProbabilityTheory.IndepFun_iff_Indep U V P).1 hUV
  have hind' : ProbabilityTheory.Indep (MeasurableSpace.comap X mγ)
      (MeasurableSpace.comap Y mδ) P :=
    ProbabilityTheory.indep_of_indep_of_le_right
      (ProbabilityTheory.indep_of_indep_of_le_left hind hX.comap_le) hY.comap_le
  exact (ProbabilityTheory.IndepFun_iff_Indep X Y P).2 hind'

/-- Each actual iterated coordinate derivative of the seed field at `xs s` is measurable for the
σ-algebra of the raw observations `(K * W)(xs s - y)`, `y ∈ tsupport ζ`, and that σ-algebra lies
below the pullback of the Pi σ-algebra along the whole observation array. Hence the entire
derivative array indexed by `S × List (Fin d)` is measurable for that pullback. -/
private theorem measurable_seedJet_comap_observations {Ω : Type*} {d : ℕ} {S : Type}
    (W : Ω → NoiseSample d) (xs : S → Vec d) :
    @Measurable Ω (S × List (Fin d) → ℝ)
      (MeasurableSpace.comap
        (fun ω (p : S × tsupport (mollifierNoiseTest d : Vec d → ℝ)) =>
          mollifiedNoise (W ω) (mollifierNoiseTest d) (xs p.1 - p.2.1))
        MeasurableSpace.pi)
      MeasurableSpace.pi
      (fun ω (p : S × List (Fin d)) =>
        iteratedCoordinateDerivative p.2 (seedField d (W ω)) (xs p.1)) := by
  have hobs : @Measurable Ω (S × tsupport (mollifierNoiseTest d : Vec d → ℝ) → ℝ)
      (MeasurableSpace.comap
        (fun ω (p : S × tsupport (mollifierNoiseTest d : Vec d → ℝ)) =>
          mollifiedNoise (W ω) (mollifierNoiseTest d) (xs p.1 - p.2.1))
        MeasurableSpace.pi)
      MeasurableSpace.pi
      (fun ω (p : S × tsupport (mollifierNoiseTest d : Vec d → ℝ)) =>
        mollifiedNoise (W ω) (mollifierNoiseTest d) (xs p.1 - p.2.1)) :=
    comap_measurable _
  refine @Measurable.of_eval Ω (S × List (Fin d)) (fun _ => ℝ)
    (MeasurableSpace.comap
      (fun ω (p : S × tsupport (mollifierNoiseTest d : Vec d → ℝ)) =>
        mollifiedNoise (W ω) (mollifierNoiseTest d) (xs p.1 - p.2.1))
      MeasurableSpace.pi) _
    (fun ω (p : S × List (Fin d)) =>
      iteratedCoordinateDerivative p.2 (seedField d (W ω)) (xs p.1)) ?_
  rintro ⟨s, is⟩
  refine (measurable_iterated_smoothedNoiseField_local W (mollifierNoiseTest d)
    (mollifierNoiseTest d) is (xs s)).mono ?_ le_rfl
  refine iSup_le fun y => ?_
  exact ((measurable_pi_apply
    (X := fun _ : S × tsupport (mollifierNoiseTest d : Vec d → ℝ) => ℝ) (s, y)).comp hobs).comap_le

/-- Joint independence of the whole arrays of iterated coordinate derivatives of the canonical seed
field `seedField d` at two outer families whose Euclidean separations exceed `4`. The arrays are
indexed by `S × List (Fin d)` and `T × List (Fin d)`. Source: `paper/main.tex:1212–1231`. The
statement assumes only the frozen white-noise input `External.IsWhiteNoiseLaw P`. -/
theorem indepFun_seedField_jet_processes_of_separated {d : ℕ} {P : Measure (NoiseSample d)}
    (hP : External.IsWhiteNoiseLaw P) (S T : Type) (xs : S → Vec d) (zs : T → Vec d)
    (hsep : ∀ s t, (4 : ℝ) < euclideanNorm (xs s-zs t)) :
    ProbabilityTheory.IndepFun
      (fun W : NoiseSample d => fun p : S × List (Fin d) =>
        iteratedCoordinateDerivative p.2 (seedField d W) (xs p.1))
      (fun W : NoiseSample d => fun q : T × List (Fin d) =>
        iteratedCoordinateDerivative q.2 (seedField d W) (zs q.1)) P := by
  letI : IsProbabilityMeasure P := hP.1
  have hobs := indepFun_tsupport_observations P id
    (fun f => External.measurable_noiseEvaluation f) hP.2 S T xs zs hsep
  exact indepFun_of_comap_measurable hobs
    (measurable_seedJet_comap_observations id xs)
    (measurable_seedJet_comap_observations id zs)

end EinsteinRelation.Sharpness
