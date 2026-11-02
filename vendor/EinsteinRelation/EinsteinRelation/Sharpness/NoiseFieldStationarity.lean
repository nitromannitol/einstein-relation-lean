import EinsteinRelation.Sharpness.NoiseProcessStationarity
import EinsteinRelation.Sharpness.OuterFunctional
import EinsteinRelation.Sharpness.NoiseField
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Probability.IdentDistrib

/-! # Process-level stationarity of the literal smoothed field `ζ * tanh(K * W)`

Source: `paper/main.tex:1212–1216`, the outer convolution `h := ζ * tanh(K * W)`.
The literal field is `smoothedNoiseField ζ K W x = ∫ ζ(y) tanh((K * W)(x - y)) dy`.

The outer functional is realised by one measurable `Φ` on the evaluation space `Vec d → ℝ`,
given by `exists_measurable_outer_tanh_functional` and reproducing the literal integral on every
continuous path. The joint array law of the first convolution, indexed by `T × Vec d` with
positions `xₜ - y`, is `identDistrib_mollifiedNoise_process_translate`. Composing that law with the
measurable slice map `v ↦ (t ↦ Φ (y ↦ v (t, y)))` gives the law of the literal smoothed process
`t ↦ smoothedNoiseField ζ K W (h + xₜ)` and `t ↦ smoothedNoiseField ζ K W xₜ`.

The shift `h` stays a literal vector. No stationarity of `h`, factorization, or extra property of
the field is assumed. The white-noise characteristic functional `hwhite` is the same cited input as
in `identDistrib_mollifiedNoise_process_translate`. -/

open MeasureTheory

namespace EinsteinRelation.Sharpness

/-- The outer functional of a noise slice `y ↦ (K * W)(x - y)` is the literal smoothed field at `x`.
The slice is continuous, so the characterization of `Φ` on continuous paths applies to it. -/
private theorem outer_slice_eq_smoothedNoiseField {d : ℕ} (ζ K : NoiseTest d)
    (Φ : (Vec d → ℝ) → ℝ)
    (hchar : ∀ G : C(Vec d, ℝ), Φ (G : Vec d → ℝ) = ∫ y : Vec d, ζ y * Real.tanh (G y))
    (W : NoiseSample d) (x : Vec d) :
    Φ (fun y : Vec d => mollifiedNoise W K (x - y)) = smoothedNoiseField ζ K W x := by
  have hc : Continuous fun y : Vec d => mollifiedNoise W K (x - y) :=
    (continuous_mollifiedNoise W K).comp (continuous_const.sub continuous_id)
  exact hchar ⟨fun y : Vec d => mollifiedNoise W K (x - y), hc⟩

/-- **Process-level stationarity of the literal smoothed field.** Source: `paper/main.tex:1212–1216`.
For every pair of test functions `ζ, K`, index type `T`, family `xs : T → Vec d`, and shift `h`, the
processes `t ↦ smoothedNoiseField ζ K W (h + xₜ)` and `t ↦ smoothedNoiseField ζ K W xₜ` are
identically distributed under `P`, as `T → ℝ` with the evaluation product σ-algebra. The hypothesis
`hwhite` is the cited generic white-noise characteristic functional; no stationarity is assumed. -/
theorem identDistrib_smoothedNoiseField_process_translate
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {d : ℕ} (W : Ω → NoiseSample d)
    (hmeas : ∀ f : NoiseTest d, Measurable (fun ω => W ω f))
    (hwhite : ∀ (f : NoiseTest d) (r : ℝ),
      (∫ ω, Complex.exp (Complex.I * (r : ℂ) * (W ω f : ℂ)) ∂P) =
        Complex.exp (((-(1/2 : ℝ))*r^2*∫ y : Vec d, (f y)^2) : ℂ))
    (ζ K : NoiseTest d) (T : Type*) (xs : T → Vec d) (h : Vec d) :
  ProbabilityTheory.IdentDistrib
    (fun ω => fun t : T => smoothedNoiseField ζ K (W ω) (h+xs t))
    (fun ω => fun t : T => smoothedNoiseField ζ K (W ω) (xs t)) P P := by
  obtain ⟨Φ, hΦ, hchar⟩ := exists_measurable_outer_tanh_functional ζ
  -- Joint law of the first convolution along the positions `xs t - y`, indexed by `T × Vec d`.
  have hjoint : ProbabilityTheory.IdentDistrib
      (fun ω => fun p : T × Vec d => mollifiedNoise (W ω) K (h + (xs p.1 - p.2)))
      (fun ω => fun p : T × Vec d => mollifiedNoise (W ω) K (xs p.1 - p.2)) P P :=
    identDistrib_mollifiedNoise_process_translate P W hmeas hwhite K (T × Vec d)
      (fun p : T × Vec d => xs p.1 - p.2) h
  -- Measurable slice map from joint arrays to processes indexed by `T`.
  have hF : Measurable
      (fun v : T × Vec d → ℝ => fun t : T => Φ (fun y : Vec d => v (t, y))) :=
    Measurable.of_eval fun t =>
      Measurable.fun_comp (g := Φ) (f := fun v : T × Vec d → ℝ => fun y : Vec d => v (t, y)) hΦ
        (Measurable.of_eval fun y => measurable_pi_apply (t, y))
  have hcomp := hjoint.comp hF
  have e1 : (fun v : T × Vec d → ℝ => fun t : T => Φ (fun y : Vec d => v (t, y))) ∘
      (fun ω => fun p : T × Vec d => mollifiedNoise (W ω) K (h + (xs p.1 - p.2))) =
      fun ω => fun t : T => smoothedNoiseField ζ K (W ω) (h + xs t) := by
    funext ω t
    change Φ (fun y : Vec d => mollifiedNoise (W ω) K (h + (xs t - y))) =
      smoothedNoiseField ζ K (W ω) (h + xs t)
    rw [← outer_slice_eq_smoothedNoiseField ζ K Φ hchar (W ω) (h + xs t)]
    simp only [add_sub_assoc]
  have e2 : (fun v : T × Vec d → ℝ => fun t : T => Φ (fun y : Vec d => v (t, y))) ∘
      (fun ω => fun p : T × Vec d => mollifiedNoise (W ω) K (xs p.1 - p.2)) =
      fun ω => fun t : T => smoothedNoiseField ζ K (W ω) (xs t) := by
    funext ω t
    exact outer_slice_eq_smoothedNoiseField ζ K Φ hchar (W ω) (xs t)
  rw [e1, e2] at hcomp
  exact hcomp

end EinsteinRelation.Sharpness
