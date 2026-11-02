import EinsteinRelation.Sharpness.NoiseStationarity
import Mathlib.Data.Finset.Pi
import Mathlib.Data.Fintype.EquivFin
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Probability.Process.FiniteDimensionalLaws

/-! # Process-level stationarity of the first convolution `K * W`

Source: `paper/main.tex:1212–1216`, the first convolution `K * W` inside `h := ζ * tanh(K * W)`.
For a fixed smooth compact kernel `K`, the whole process `t ↦ (K * W)(h + xₜ)` and
`t ↦ (K * W)(xₜ)`, indexed by an arbitrary type `T` and carried by the evaluation product
σ-algebra on `T → ℝ`, has the same law under `P`.

The finite-dimensional input is `identDistrib_mollifiedNoise_translate`, applied to an enumeration
`Fin n ≃ I` of each finite index set `I : Finset T`. The full process law is then assembled by
`ProbabilityTheory.identDistrib_iff_forall_finset_identDistrib`, which consumes the joint finite
families for every `I`, not only one-point marginals.

This is law stationarity of the raw process of first-convolution values only. The outer field `h`,
its physical coefficient law, and field-law existence remain separate obligations. -/

open MeasureTheory

namespace EinsteinRelation.Sharpness

/-- Finite-family stationarity along an arbitrary enumeration `e : I ≃ Fin n` of a finite index
set. The coordinate reindexing `v ↦ (i ↦ v (e i))` is measurable and undoes the enumeration. -/
private theorem identDistrib_mollifiedNoise_finset {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (W : Ω → NoiseSample d)
    (hmeas : ∀ f : NoiseTest d, Measurable (fun ω => W ω f))
    (hwhite : ∀ (f : NoiseTest d) (r : ℝ),
      (∫ ω, Complex.exp (Complex.I * (r : ℂ) * (W ω f : ℂ)) ∂P) =
        Complex.exp (((-(1/2 : ℝ))*r^2*∫ y : Vec d, (f y)^2) : ℂ))
    (K : NoiseTest d) {T : Type*} (xs : T → Vec d) (h : Vec d) (I : Finset T)
    (n : ℕ) (e : I ≃ Fin n) :
    ProbabilityTheory.IdentDistrib
      (fun ω => I.restrict (fun t : T => mollifiedNoise (W ω) K (h + xs t)))
      (fun ω => I.restrict (fun t : T => mollifiedNoise (W ω) K (xs t))) P P := by
  have hEnum := identDistrib_mollifiedNoise_translate P W hmeas hwhite K n
    (fun j : Fin n => xs (e.symm j : T)) h
  have hu : Measurable (fun v : Fin n → ℝ => fun i : I => v (e i)) :=
    Measurable.of_eval fun i => measurable_pi_apply (e i)
  have hA : (fun ω => I.restrict (fun t : T => mollifiedNoise (W ω) K (h + xs t))) =
      (fun v : Fin n → ℝ => fun i : I => v (e i)) ∘
        (fun ω => fun j : Fin n => mollifiedNoise (W ω) K (h + xs (e.symm j : T))) := by
    funext ω i
    change mollifiedNoise (W ω) K (h + xs (i : T)) =
      mollifiedNoise (W ω) K (h + xs ((e.symm (e i) : I) : T))
    rw [Equiv.symm_apply_apply]
  have hB : (fun ω => I.restrict (fun t : T => mollifiedNoise (W ω) K (xs t))) =
      (fun v : Fin n → ℝ => fun i : I => v (e i)) ∘
        (fun ω => fun j : Fin n => mollifiedNoise (W ω) K (xs (e.symm j : T))) := by
    funext ω i
    change mollifiedNoise (W ω) K (xs (i : T)) =
      mollifiedNoise (W ω) K (xs ((e.symm (e i) : I) : T))
    rw [Equiv.symm_apply_apply]
  rw [hA, hB]
  exact hEnum.comp hu

/-- **Process-level stationarity of the first convolution.** Source: `paper/main.tex:1212–1216`.
For every compact kernel `K`, index type `T`, family `xs : T → Vec d`, and shift `h`, the processes
`t ↦ (K * W)(h + xₜ)` and `t ↦ (K * W)(xₜ)` are identically distributed under `P`, as `T → ℝ`
with the evaluation product σ-algebra. The hypothesis `hwhite` is the cited generic white-noise
characteristic functional; no stationarity is assumed. -/
theorem identDistrib_mollifiedNoise_process_translate {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (W : Ω → NoiseSample d)
    (hmeas : ∀ f : NoiseTest d, Measurable (fun ω => W ω f))
    (hwhite : ∀ (f : NoiseTest d) (r : ℝ),
      (∫ ω, Complex.exp (Complex.I * (r : ℂ) * (W ω f : ℂ)) ∂P) =
        Complex.exp (((-(1/2 : ℝ))*r^2*∫ y : Vec d, (f y)^2) : ℂ))
    (K : NoiseTest d) (T : Type*) (xs : T → Vec d) (h : Vec d) :
    ProbabilityTheory.IdentDistrib
      (fun ω => fun t : T => mollifiedNoise (W ω) K (h+xs t))
      (fun ω => fun t : T => mollifiedNoise (W ω) K (xs t)) P P := by
  have hF : AEMeasurable (fun ω => fun t : T => mollifiedNoise (W ω) K (h + xs t)) P :=
    (Measurable.of_eval
      fun t => measurable_mollifiedNoise W hmeas K (h + xs t)).aemeasurable
  have hG : AEMeasurable (fun ω => fun t : T => mollifiedNoise (W ω) K (xs t)) P :=
    (Measurable.of_eval
      fun t => measurable_mollifiedNoise W hmeas K (xs t)).aemeasurable
  refine (ProbabilityTheory.identDistrib_iff_forall_finset_identDistrib
    (X := fun t ω => mollifiedNoise (W ω) K (h + xs t))
    (Y := fun t ω => mollifiedNoise (W ω) K (xs t)) hF hG).mpr fun I => ?_
  exact identDistrib_mollifiedNoise_finset P W hmeas hwhite K xs h I (Fintype.card I)
    (Fintype.equivFin I)

end EinsteinRelation.Sharpness
