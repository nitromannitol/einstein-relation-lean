import EinsteinRelation.Sharpness.NoiseFieldLocality
import EinsteinRelation.Sharpness.NoiseProcessIndependence
import EinsteinRelation.Sharpness.OuterRange
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Probability.Independence.Basic

/-! # Joint independence of the literal smoothed noise field

Source: `paper/main.tex:1212–1216`, the internal finite-range field `h ≔ ζ * tanh(K * W)` in the
proof of `sharp.example` (Proposition 7.1). For outer families `xs : S → Vec d` and `zs : T → Vec d`
whose Euclidean separations exceed `2 * (Rζ + RK)`, the field processes `(h (xs s))_{s : S}` and
`(h (zs t))_{t : T}` are independent. This is independence of the field itself, not only of the raw
noise tests.

The proof compares σ-algebras and assumes nothing about `h`:
1. The joint process of actual kernel observations `(K * W)(xs s - y)` over `(s, y)` with `ζ y ≠ 0`
   is independent across the two families. This is
   `indepFun_noise_processes_of_orthogonal` applied to the reflected kernel tests, whose cross
   integrals vanish by `integral_kernelTest_outer_mul_eq_zero_of_separated`.
2. Each `h (xs s)` is measurable for the σ-algebra of its own local observations
   (`measurable_smoothedNoiseField_local`). Those σ-algebras lie below the pullback of the Pi
   σ-algebra along the observation process, so the whole field process is measurable for that
   pullback.
3. Independence passes to these coarser σ-algebras by `indep_of_indep_of_le_left` and
   `indep_of_indep_of_le_right`.

The generic Gaussian characteristic law `hwhite` is an explicit hypothesis, sourced from AKM
Definition 5.1 / Proposition 5.14, exactly as in `NoiseProcessIndependence`. It is not a premise
about `h`. This file does not prove finite range or nondegeneracy of the physical `h`. -/

open MeasureTheory

namespace EinsteinRelation.Sharpness

/-- Independence of the actual kernel observations on the outer index sets `S × A` and `T × A`,
where `A` is the support of `ζ`. This is the orthogonal-block theorem applied to the reflected
kernel tests `kernelTest K (xs s - y)` and `kernelTest K (zs t - w)`, whose cross integrals vanish
by outer-neighborhood orthogonality. -/
private theorem indepFun_localObservations {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {d : ℕ} (W : Ω → NoiseSample d)
    (hmeas : ∀ f : NoiseTest d, Measurable (fun ω => W ω f))
    (hwhite : ∀ (f : NoiseTest d) (r : ℝ),
      (∫ ω, Complex.exp (Complex.I * (r : ℂ) * (W ω f : ℂ)) ∂P) =
        Complex.exp (((-(1/2 : ℝ))*r^2*∫ y : Vec d, (f y)^2) : ℂ))
    (ζ K : NoiseTest d) (Rζ RK : ℝ)
    (hζ : ∀ u : Vec d, ζ u ≠ 0 → euclideanNorm u ≤ Rζ)
    (hK : ∀ u : Vec d, K u ≠ 0 → euclideanNorm u ≤ RK)
    (S T : Type*) (xs : S → Vec d) (zs : T → Vec d)
    (hsep : ∀ s t, 2*(Rζ+RK) < euclideanNorm (xs s-zs t)) :
    ProbabilityTheory.IndepFun
      (fun ω (p : S × {y : Vec d // ζ y ≠ 0}) => mollifiedNoise (W ω) K (xs p.1 - p.2.1))
      (fun ω (q : T × {y : Vec d // ζ y ≠ 0}) => mollifiedNoise (W ω) K (zs q.1 - q.2.1)) P :=
  indepFun_noise_processes_of_orthogonal P W hmeas hwhite (S × {y : Vec d // ζ y ≠ 0})
    (T × {y : Vec d // ζ y ≠ 0}) (fun p => kernelTest K (xs p.1 - p.2.1))
    (fun q => kernelTest K (zs q.1 - q.2.1))
    (fun p q => integral_kernelTest_outer_mul_eq_zero_of_separated ζ K Rζ RK hζ hK
      (xs p.1) (zs q.1) (hsep p.1 q.1) p.2.1 q.2.1 p.2.2 q.2.2)

/-- Independence transfers from a pair of random elements to any pair of random elements measurable
for the σ-algebras they generate. Only the comparisons `comap X ≤ comap U` and `comap Y ≤ comap V`
are used, so no factorization or extra premise on `X` and `Y` enters. -/
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

/-- The literal smoothed field at every outer point `xs s` is measurable for the pullback of the Pi
σ-algebra along the actual local observations `(s, y) ↦ (K * W)(xs s - y)` with `ζ y ≠ 0`. Each
coordinate `h (xs s)` is measurable for the σ-algebra of its own local observations, which lies
below that pullback, and the Pi σ-algebra is the supremum of the coordinate pullbacks. -/
private theorem measurable_smoothedNoiseField_comap_observations {Ω : Type*} {d : ℕ} {S : Type*}
    (W : Ω → NoiseSample d) (ζ K : NoiseTest d) (xs : S → Vec d) :
    @Measurable Ω (S → ℝ)
      (MeasurableSpace.comap
        (fun ω (p : S × {y : Vec d // ζ y ≠ 0}) => mollifiedNoise (W ω) K (xs p.1 - p.2.1))
        MeasurableSpace.pi)
      MeasurableSpace.pi (fun ω s => smoothedNoiseField ζ K (W ω) (xs s)) := by
  have hobs : @Measurable Ω (S × {y : Vec d // ζ y ≠ 0} → ℝ)
      (MeasurableSpace.comap
        (fun ω (p : S × {y : Vec d // ζ y ≠ 0}) => mollifiedNoise (W ω) K (xs p.1 - p.2.1))
        MeasurableSpace.pi)
      MeasurableSpace.pi
      (fun ω (p : S × {y : Vec d // ζ y ≠ 0}) => mollifiedNoise (W ω) K (xs p.1 - p.2.1)) :=
    comap_measurable _
  refine @Measurable.of_eval Ω S (fun _ => ℝ)
    (MeasurableSpace.comap
      (fun ω (p : S × {y : Vec d // ζ y ≠ 0}) => mollifiedNoise (W ω) K (xs p.1 - p.2.1))
      MeasurableSpace.pi) _ (fun ω s => smoothedNoiseField ζ K (W ω) (xs s)) ?_
  intro s
  refine (measurable_smoothedNoiseField_local W ζ K (xs s)).mono ?_ le_rfl
  refine iSup_le fun y => ?_
  exact ((measurable_pi_apply (X := fun _ : S × {y : Vec d // ζ y ≠ 0} => ℝ) (s, y)).comp
    hobs).comap_le

/-- Joint independence of the literal smoothed noise field `h = ζ * tanh(K * W)` at two outer
families separated by more than `2 * (Rζ + RK)`. Source: `paper/main.tex:1212–1216`.
The field processes are independent as processes, with the ordinary Pi σ-algebra on each side.
The statement assumes only the generic Gaussian characteristic law `hwhite`. -/
theorem indepFun_smoothedNoiseField_processes_of_separated
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {d : ℕ} (W : Ω → NoiseSample d)
    (hmeas : ∀ f : NoiseTest d, Measurable (fun ω => W ω f))
    (hwhite : ∀ (f : NoiseTest d) (r : ℝ),
      (∫ ω, Complex.exp (Complex.I * (r : ℂ) * (W ω f : ℂ)) ∂P) =
        Complex.exp (((-(1/2 : ℝ))*r^2*∫ y : Vec d, (f y)^2) : ℂ))
    (ζ K : NoiseTest d) (Rζ RK : ℝ)
    (hζ : ∀ u : Vec d, ζ u ≠ 0 → euclideanNorm u ≤ Rζ)
    (hK : ∀ u : Vec d, K u ≠ 0 → euclideanNorm u ≤ RK)
    (S T : Type*) (xs : S → Vec d) (zs : T → Vec d)
    (hsep : ∀ s t, 2*(Rζ+RK) < euclideanNorm (xs s-zs t)) :
    ProbabilityTheory.IndepFun (fun ω => fun s : S => smoothedNoiseField ζ K (W ω) (xs s))
      (fun ω => fun t : T => smoothedNoiseField ζ K (W ω) (zs t)) P := by
  have hobs := indepFun_localObservations P W hmeas hwhite ζ K Rζ RK hζ hK S T xs zs hsep
  exact indepFun_of_comap_measurable hobs
    (measurable_smoothedNoiseField_comap_observations W ζ K xs)
    (measurable_smoothedNoiseField_comap_observations W ζ K zs)

end EinsteinRelation.Sharpness
