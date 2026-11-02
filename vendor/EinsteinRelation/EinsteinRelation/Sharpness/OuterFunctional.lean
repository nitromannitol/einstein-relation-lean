import EinsteinRelation.Sharpness.NoiseField
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Function.FactorsThrough
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Topology.ContinuousMap.Defs

/-! # Measurable outer functional on actual continuous paths

Source: `paper/main.tex` lines 1212–1216, the outer convolution `ζ * tanh(·)` of the sharpness
example. The real functional `G ↦ ∫ ζ(y) tanh(G y) dy` is defined on actual continuous paths
`G : C(Vec d, ℝ)`. These paths carry the local σ-algebra `pathSigma d`, the pullback of the
coordinate σ-algebra of `Vec d → ℝ` along the coercion. It is a definition, not a global instance,
and it is not claimed to be the Borel σ-algebra of `C(Vec d, ℝ)`.

Doob–Dynkin then gives a measurable `Φ` on the full evaluation space `Vec d → ℝ` that reproduces
the functional on every continuous path. The literal `smoothedNoiseField` is unchanged. No
probability law, white-noise, stationarity, or `h`-property is assumed.
-/

open MeasureTheory

namespace EinsteinRelation.Sharpness

/-- `Real.tanh` is continuous, as the quotient of the continuous `sinh` by the everywhere
positive `cosh`. -/
private theorem continuous_outerTanh : Continuous Real.tanh := by
  have h : Real.tanh = fun t => Real.sinh t / Real.cosh t :=
    funext Real.tanh_eq_sinh_div_cosh
  rw [h]
  exact Real.continuous_sinh.div₀ Real.continuous_cosh (fun t => (Real.cosh_pos t).ne')

/-- The pullback σ-algebra on continuous paths along the coercion to value functions. -/
private def pathSigma (d : ℕ) : MeasurableSpace C(Vec d, ℝ) :=
  MeasurableSpace.comap (fun G : C(Vec d, ℝ) => (G : Vec d → ℝ))
    (inferInstance : MeasurableSpace (Vec d → ℝ))

/-- The coercion `G ↦ (G : Vec d → ℝ)` is measurable for `pathSigma d`, by the definition of the
pullback. -/
private theorem measurable_pathCoe (d : ℕ) :
    Measurable[pathSigma d] (fun G : C(Vec d, ℝ) => (G : Vec d → ℝ)) :=
  comap_measurable (fun G : C(Vec d, ℝ) => (G : Vec d → ℝ))

/-- Measurability of `ω ↦ ∫ ζ(y) tanh(X ω y) dy` for continuous paths `X ω` whose evaluations are
measurable in `ω`. Joint measurability in `(y, ω)` follows from continuity in `y` and measurability
in `ω`, with the continuous coordinate `y` as the index of the uncurrying lemma. Fubini–Tonelli in
the first coordinate (`integral_prod_left'`) then gives measurability of the integral. -/
private theorem measurable_outerTanh_integral {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ}
    (ζ : NoiseTest d) (X : Ω → Vec d → ℝ) (hX : ∀ ω, Continuous (X ω))
    (hev : ∀ y : Vec d, Measurable fun ω => X ω y) :
    Measurable fun ω => ∫ y : Vec d, ζ y * Real.tanh (X ω y) := by
  have hXjoint : Measurable (fun p : Vec d × Ω => X p.2 p.1) :=
    MeasureTheory.measurable_uncurry_of_continuous_of_measurable
      (u := fun (y : Vec d) (ω : Ω) => X ω y) hX hev
  have htanh : Measurable (fun p : Vec d × Ω => Real.tanh (X p.2 p.1)) :=
    Measurable.fun_comp (g := Real.tanh) (f := fun p : Vec d × Ω => X p.2 p.1)
      continuous_outerTanh.measurable hXjoint
  have hζ : Measurable (fun p : Vec d × Ω => ζ p.1) :=
    Measurable.fun_comp (g := fun y : Vec d => ζ y) (f := (Prod.fst : Vec d × Ω → Vec d))
      ζ.contDiff.continuous.measurable measurable_fst
  have hsm : StronglyMeasurable (fun p : Vec d × Ω => ζ p.1 * Real.tanh (X p.2 p.1)) :=
    (hζ.mul htanh).stronglyMeasurable
  have hint : StronglyMeasurable (fun ω : Ω => ∫ y : Vec d, ζ y * Real.tanh (X ω y)) :=
    MeasureTheory.StronglyMeasurable.integral_prod_left'
      (μ := (volume : MeasureTheory.Measure (Vec d)))
      (f := fun p : Vec d × Ω => ζ p.1 * Real.tanh (X p.2 p.1)) hsm
  exact hint.measurable

/-- The outer functional `G ↦ ∫ ζ(y) tanh(G y) dy` is measurable on continuous paths for the
local σ-algebra `pathSigma d`. -/
private theorem measurable_pathOuterTanh {d : ℕ} (ζ : NoiseTest d) :
    Measurable[pathSigma d] (fun G : C(Vec d, ℝ) => ∫ y : Vec d, ζ y * Real.tanh (G y)) := by
  have hcoe : Measurable[pathSigma d] (fun G : C(Vec d, ℝ) => (G : Vec d → ℝ)) :=
    measurable_pathCoe d
  have hev : ∀ y : Vec d, Measurable[pathSigma d] (fun G : C(Vec d, ℝ) => (G : Vec d → ℝ) y) :=
    fun y => Measurable.fun_comp (g := fun f : Vec d → ℝ => f y)
      (f := fun G : C(Vec d, ℝ) => (G : Vec d → ℝ)) (measurable_pi_apply y) hcoe
  exact measurable_outerTanh_integral (mΩ := pathSigma d) ζ
    (fun G : C(Vec d, ℝ) => (G : Vec d → ℝ)) (fun G => G.continuous) hev

/-- Doob–Dynkin factorization of the outer convolution functional through the evaluation
process. The factor `Φ` is common to all continuous paths and does not depend on any noise
sample, shift, or law. -/
theorem exists_measurable_outer_tanh_functional {d : ℕ} (ζ : NoiseTest d) :
  ∃ Φ : (Vec d → ℝ) → ℝ, Measurable Φ ∧
    ∀ G : C(Vec d, ℝ), Φ (G : Vec d → ℝ) = ∫ y : Vec d, ζ y * Real.tanh (G y) := by
  obtain ⟨Φ, hΦ, hfac⟩ := Measurable.exists_eq_measurable_comp
    (f := fun G : C(Vec d, ℝ) => (G : Vec d → ℝ))
    (g := fun G : C(Vec d, ℝ) => ∫ y : Vec d, ζ y * Real.tanh (G y))
    (measurable_pathOuterTanh ζ)
  exact ⟨Φ, hΦ, fun G => (congrFun hfac G).symm⟩

end EinsteinRelation.Sharpness
