import EinsteinRelation.External.WhiteNoise
import EinsteinRelation.Sharpness.CoordinateIterates
import EinsteinRelation.Sharpness.NoiseField
import EinsteinRelation.Sharpness.NoiseFieldDerivatives
import EinsteinRelation.Sharpness.NoiseMollifier
import EinsteinRelation.Sharpness.NoiseProcessStationarity
import EinsteinRelation.Sharpness.OuterFunctional
import EinsteinRelation.Sharpness.SeedField
import Mathlib.Probability.IdentDistrib

/-! # Joint process-level stationarity of the actual canonical seed jets

Source: `paper/main.tex`, proof of Proposition 7.1, Steps 1–2, lines 1212–1231. The Jacobian
`J = I + e₁ ⊗ ∇ψ` and the coefficient `μ = 1 + (δ/2) ∇·(a e₁)` depend on several derivatives of the
seed `ψ = ε ζ * tanh(K * W)` at once. The physical coefficient law therefore needs the law of the
whole jet, not one derivative at a time.

The canonical seed is `seedField d W`, the literal field `ζ * tanh(K * W)` with `ζ = K =
mollifierNoiseTest d`. The joint array indexed by `S × List (Fin d)` with entries
`∂_is (seedField d W) (h + xₛ)` has the same law under `P` as the array at `xₛ`.

The proof has the same shape as `identDistrib_smoothedNoiseField_process_translate`. The raw first
convolution is indexed by `(S × List (Fin d)) × Vec d` at the positions `xₛ - y`. For each
coordinate list `is`, the derivative `∂_is (seedField d W) x` is the outer convolution of `D_is ζ`
against `tanh(K * W)`. A measurable functional `Φ_is` of that kernel, chosen by
`exists_measurable_outer_tanh_functional`, turns each raw slice into the derivative. Composing the
shift law of the raw array with the measurable slice map `v ↦ (p ↦ Φ_{p.2}(y ↦ v (p, y)))` gives
the joint law. The white-noise input is the frozen `External.IsWhiteNoiseLaw P` alone. -/

open MeasureTheory

namespace EinsteinRelation.Sharpness

/-- The iterated coordinate derivative `D_is ζ` of the canonical kernel `ζ = mollifierNoiseTest d`,
packaged as an actual compact smooth test for each coordinate list `is`. The `C^∞` and compact
support fields come from the checked producers for iterated coordinate derivatives. -/
private noncomputable def jetDerivativeTest {d : ℕ} (is : List (Fin d)) : NoiseTest d where
  toFun := iteratedCoordinateDerivative is (mollifierNoiseTest d : Vec d → ℝ)
  contDiff' := contDiff_iteratedCoordinateDerivative (mollifierNoiseTest d : Vec d → ℝ)
    (mollifierNoiseTest d).contDiff is
  hasCompactSupport' :=
    hasCompactSupport_iteratedCoordinateDerivative (mollifierNoiseTest d : Vec d → ℝ)
      (mollifierNoiseTest d).hasCompactSupport is
  tsupport_subset' := Set.subset_univ _

/-- Source: `paper/main.tex`, Proposition 7.1, Step 1, lines 1212–1218. The actual iterated
coordinate derivative of the canonical seed at a sample `W` and a point `x` is the literal smoothed
field of the derivative kernel `D_is ζ`, with the canonical inner kernel `K`. This is the exact
integral derivative identity, read as an equality of the two named fields. -/
private theorem iteratedCoordinateDerivative_seedField_eq_jet {d : ℕ} (is : List (Fin d))
    (W : NoiseSample d) (x : Vec d) :
    iteratedCoordinateDerivative is (seedField d W) x =
      smoothedNoiseField (jetDerivativeTest is) (mollifierNoiseTest d) W x :=
  iteratedCoordinateDerivative_smoothedNoiseField (mollifierNoiseTest d) (mollifierNoiseTest d)
    W is x

/-- The outer functional of the noise slice `y ↦ (K * W)(x - y)` is the literal smoothed field at
`x` for the kernel `ζ`. The slice is continuous, so the characterization of `Φ` on continuous
paths applies to it. -/
private theorem jet_outer_slice_eq_smoothedNoiseField {d : ℕ} (ζ K : NoiseTest d)
    (Φ : (Vec d → ℝ) → ℝ)
    (hchar : ∀ G : C(Vec d, ℝ), Φ (G : Vec d → ℝ) = ∫ y : Vec d, ζ y * Real.tanh (G y))
    (W : NoiseSample d) (x : Vec d) :
    Φ (fun y : Vec d => mollifiedNoise W K (x - y)) = smoothedNoiseField ζ K W x := by
  have hc : Continuous fun y : Vec d => mollifiedNoise W K (x - y) :=
    (continuous_mollifiedNoise W K).comp (continuous_const.sub continuous_id)
  exact hchar ⟨fun y : Vec d => mollifiedNoise W K (x - y), hc⟩

/-- **Joint process-level stationarity of the canonical seed jets.** Source: `paper/main.tex`,
Proposition 7.1, Steps 1–2, lines 1212–1231. For a white-noise law `P`, an index type `S`, a family
`xs : S → Vec d`, and a shift `h`, the whole joint array
`(s, is) ↦ ∂_is (ζ * tanh(K * W)) (h + xₛ)` and `(s, is) ↦ ∂_is (ζ * tanh(K * W)) xₛ`, indexed by
`S × List (Fin d)`, are identically distributed under `P`, as functions `S × List (Fin d) → ℝ` with
the evaluation product σ-algebra. The coordinate lists are arbitrary and the joint law is not
inferred from one list at a time. -/
theorem identDistrib_seedField_jet_process_translate :
    ∀ {d : ℕ} {P : Measure (NoiseSample d)}, External.IsWhiteNoiseLaw P →
      ∀ (S : Type) (xs : S → Vec d) (h : Vec d), ProbabilityTheory.IdentDistrib
        (fun W : NoiseSample d => fun p : S × List (Fin d) =>
          iteratedCoordinateDerivative p.2 (seedField d W) (h + xs p.1))
        (fun W : NoiseSample d => fun p : S × List (Fin d) =>
          iteratedCoordinateDerivative p.2 (seedField d W) (xs p.1)) P P := by
  intro d P hP S xs h
  letI : IsProbabilityMeasure P := hP.1
  -- One measurable outer functional for each actual derivative kernel `D_is ζ`.
  have hex : ∀ is : List (Fin d), ∃ Φ : (Vec d → ℝ) → ℝ, Measurable Φ ∧
      ∀ G : C(Vec d, ℝ),
        Φ (G : Vec d → ℝ) = ∫ y : Vec d, jetDerivativeTest is y * Real.tanh (G y) :=
    fun is => exists_measurable_outer_tanh_functional (jetDerivativeTest is)
  choose Φ hΦ hchar using hex
  -- Joint first convolution along the positions `xₛ - y`, indexed by `(S × List (Fin d)) × Vec d`.
  have hjoint : ProbabilityTheory.IdentDistrib
      (fun W : NoiseSample d => fun q : (S × List (Fin d)) × Vec d =>
        mollifiedNoise W (mollifierNoiseTest d) (h + (xs q.1.1 - q.2)))
      (fun W : NoiseSample d => fun q : (S × List (Fin d)) × Vec d =>
        mollifiedNoise W (mollifierNoiseTest d) (xs q.1.1 - q.2)) P P :=
    identDistrib_mollifiedNoise_process_translate P id
      (fun f => External.measurable_noiseEvaluation f) hP.2 (mollifierNoiseTest d)
      ((S × List (Fin d)) × Vec d) (fun q : (S × List (Fin d)) × Vec d => xs q.1.1 - q.2) h
  -- Measurable slice map from joint raw arrays to joint arrays of derivative jets.
  have hΨ : Measurable (fun v : (S × List (Fin d)) × Vec d → ℝ =>
      fun p : S × List (Fin d) => Φ p.2 (fun y : Vec d => v (p, y))) :=
    Measurable.of_eval fun p : S × List (Fin d) =>
      Measurable.fun_comp (g := Φ p.2)
        (f := fun v : (S × List (Fin d)) × Vec d → ℝ => fun y : Vec d => v (p, y))
        (hΦ p.2) (Measurable.of_eval fun y : Vec d => measurable_pi_apply (p, y))
  have hcomp := hjoint.comp hΨ
  have e1 : (fun v : (S × List (Fin d)) × Vec d → ℝ => fun p : S × List (Fin d) =>
        Φ p.2 (fun y : Vec d => v (p, y))) ∘
      (fun W : NoiseSample d => fun q : (S × List (Fin d)) × Vec d =>
        mollifiedNoise W (mollifierNoiseTest d) (h + (xs q.1.1 - q.2))) =
      fun W : NoiseSample d => fun p : S × List (Fin d) =>
        iteratedCoordinateDerivative p.2 (seedField d W) (h + xs p.1) := by
    funext W p
    change Φ p.2 (fun y : Vec d => mollifiedNoise W (mollifierNoiseTest d) (h + (xs p.1 - y))) =
      iteratedCoordinateDerivative p.2 (seedField d W) (h + xs p.1)
    rw [iteratedCoordinateDerivative_seedField_eq_jet p.2 W (h + xs p.1),
      ← jet_outer_slice_eq_smoothedNoiseField (jetDerivativeTest p.2) (mollifierNoiseTest d)
        (Φ p.2) (hchar p.2) W (h + xs p.1)]
    simp only [add_sub_assoc]
  have e2 : (fun v : (S × List (Fin d)) × Vec d → ℝ => fun p : S × List (Fin d) =>
        Φ p.2 (fun y : Vec d => v (p, y))) ∘
      (fun W : NoiseSample d => fun q : (S × List (Fin d)) × Vec d =>
        mollifiedNoise W (mollifierNoiseTest d) (xs q.1.1 - q.2)) =
      fun W : NoiseSample d => fun p : S × List (Fin d) =>
        iteratedCoordinateDerivative p.2 (seedField d W) (xs p.1) := by
    funext W p
    exact (jet_outer_slice_eq_smoothedNoiseField (jetDerivativeTest p.2) (mollifierNoiseTest d)
        (Φ p.2) (hchar p.2) W (xs p.1)).trans
      (iteratedCoordinateDerivative_seedField_eq_jet p.2 W (xs p.1)).symm
  rw [e1, e2] at hcomp
  exact hcomp

end EinsteinRelation.Sharpness
