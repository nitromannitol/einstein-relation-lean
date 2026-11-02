import EinsteinRelation.Sharpness.IteratedConvolution
import EinsteinRelation.Sharpness.NoiseField

/-! # Actual iterated coordinate derivatives of the literal smoothed noise field

Source: `paper/main.tex`, proof of Proposition 7.1, Step 1, lines 1212–1218. The literal field
`h ≔ ζ * tanh(K * W)` is `smoothedNoiseField ζ K W`, where the first convolution is
`mollifiedNoise W K` evaluated on an actual distribution sample `W`. Every iterated coordinate
derivative of this field falls on the fixed kernel `ζ`, and the amplitude bound `|tanh| ≤ 1`
bounds it by the `L¹` norm of the same derivative of `ζ`.

The uniform constant depends only on `ζ` and the coordinate list. It is chosen before the kernel
`K`, the sample `W`, and the point `x`. The results assume no stationarity, finite range, Gaussian
law, or nondegeneracy.
-/

open MeasureTheory

namespace EinsteinRelation.Sharpness

/-- `Real.tanh` is continuous, as the quotient of the continuous `sinh` by the everywhere positive
`cosh`. The pinned Mathlib has no `Real.continuous_tanh`, so the fact is derived here. -/
private theorem continuous_tanh_field : Continuous Real.tanh := by
  have heq : Real.tanh = fun t => Real.sinh t / Real.cosh t :=
    funext Real.tanh_eq_sinh_div_cosh
  rw [heq]
  exact Real.continuous_sinh.div₀ Real.continuous_cosh (fun t => (Real.cosh_pos t).ne')

/-- `|tanh t| ≤ 1`. The pinned Mathlib has no such lemma, so it is derived from `|sinh t| ≤ cosh t`,
which holds because `cosh t ± sinh t = exp (±t) > 0`. -/
private theorem abs_tanh_field_le_one (t : ℝ) : |Real.tanh t| ≤ 1 := by
  rw [Real.tanh_eq_sinh_div_cosh, abs_div, abs_of_pos (Real.cosh_pos t),
    div_le_one (Real.cosh_pos t), abs_le]
  constructor
  · linarith [Real.cosh_add_sinh t, Real.exp_pos t]
  · linarith [Real.cosh_sub_sinh t, Real.exp_pos (-t)]

/-- Source: `paper/main.tex`, Proposition 7.1, Step 1, lines 1212–1218. For smooth, compactly
supported kernels `ζ` and `K` and an actual sample `W`, each iterated coordinate derivative of the
literal field `ζ * tanh(K * W)` is the outer convolution of the same iterated derivative of `ζ`
with the bounded continuous field `tanh(K * W)`. -/
theorem iteratedCoordinateDerivative_smoothedNoiseField {d : ℕ} (ζ K : NoiseTest d)
    (W : NoiseSample d) (is : List (Fin d)) (x : Vec d) :
    iteratedCoordinateDerivative is (smoothedNoiseField ζ K W) x =
      ∫ y : Vec d, iteratedCoordinateDerivative is (ζ : Vec d → ℝ) y *
        Real.tanh (mollifiedNoise W K (x-y)) :=
  iteratedCoordinateDerivative_outer_convolution (ζ : Vec d → ℝ)
    (fun z => Real.tanh (mollifiedNoise W K z)) ζ.contDiff ζ.hasCompactSupport
    (continuous_tanh_field.comp (continuous_mollifiedNoise W K)) is x

/-- Source: `paper/main.tex`, Proposition 7.1, Step 1, lines 1212–1218. For a fixed smooth,
compactly supported `ζ` and a fixed list of coordinates, the iterated coordinate derivatives of the
literal field `ζ * tanh(K * W)` are bounded by one deterministic constant. The bound is uniform in
the kernel `K`, the actual sample `W`, and the point `x`. The constant is the `L¹` norm of the
absolute iterated derivative of `ζ`, chosen before `K`, `W`, and `x`. -/
theorem exists_uniform_smoothedNoiseField_derivative_bound {d : ℕ}
    (ζ : NoiseTest d) (is : List (Fin d)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (K : NoiseTest d) (W : NoiseSample d) (x : Vec d),
      |iteratedCoordinateDerivative is (smoothedNoiseField ζ K W) x| ≤ C := by
  refine ⟨(∫ y : Vec d, |iteratedCoordinateDerivative is (ζ : Vec d → ℝ) y|), ?_, ?_⟩
  · exact integral_nonneg fun y => abs_nonneg _
  · intro K W x
    exact abs_iteratedCoordinateDerivative_outer_convolution_le (ζ : Vec d → ℝ)
      (fun z => Real.tanh (mollifiedNoise W K z)) ζ.contDiff ζ.hasCompactSupport
      (continuous_tanh_field.comp (continuous_mollifiedNoise W K))
      (fun z => abs_tanh_field_le_one (mollifiedNoise W K z)) is x

end EinsteinRelation.Sharpness
