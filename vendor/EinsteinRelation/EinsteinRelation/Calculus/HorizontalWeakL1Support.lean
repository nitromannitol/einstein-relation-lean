import EinsteinRelation.Calculus.HorizontalSobolev
import EinsteinRelation.Correctors.HorizontalCharacterizationSupport
import EinsteinRelation.Correctors.HorizontalH1EuclideanGradient

/-! # Weak horizontal gradients in `L¹`

The distributional derivative is tested against the actual bounded smooth orbit tests
`IsHorizontalTest`. Their scalar derivatives are bounded by `bound_derivative`, so both sides
of the distributional pairing are ordinary integrals for `L¹` data. Vector fields use
`EuclideanSpace ℝ (Fin d)` and coordinate `i` is its standard `Fin d` component; this is the
Euclidean vector norm convention used by the paper.

The source describes its tests as all horizontally smooth functions with bounded horizontal
derivatives. The repository supplies `IsHorizontalTest` as an actual smooth orbit test class.
This file uses that class literally; it does not claim a theorem identifying it with every test
allowed by the prose definition.
-/

open MeasureTheory

noncomputable section

namespace EinsteinRelation

/-- The weak horizontal gradient relation for an `L¹` scalar and an `L¹` Euclidean vector field.
The coordinate equations are the distributional identities
`∫ f D_i H = -∫ G_i H` for the actual bounded smooth horizontal tests. -/
def HasWeakHorizontalL1Gradient {d : ℕ} (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (f : Lp ℝ 1 Q)
    (G : Lp (EuclideanSpace ℝ (Fin d)) 1 Q) : Prop :=
  ∀ i : Fin d, ∀ H : FieldPair d → ℝ, IsHorizontalTest H →
    Integrable (fun ω => f ω * horizontalDerivative i H ω) Q ∧
    Integrable (fun ω => G ω i * H ω) Q ∧
    (∫ ω, f ω * horizontalDerivative i H ω ∂Q) =
      -(∫ ω, G ω i * H ω ∂Q)

/-- The predicate is on `L¹` quotient classes, so changing either representative on a null set
does not change its meaning. -/
theorem HasWeakHorizontalL1Gradient.congr {d : ℕ} {Q : Measure (FieldPair d)}
    [IsProbabilityMeasure Q] {f f' : Lp ℝ 1 Q}
    {G G' : Lp (EuclideanSpace ℝ (Fin d)) 1 Q}
    (hf : f = f') (hG : G = G') :
    HasWeakHorizontalL1Gradient Q f G ↔ HasWeakHorizontalL1Gradient Q f' G' := by
  subst f
  subst G
  rfl

/-- The test and first derivative bounds in `IsHorizontalTest` make both `L¹` distributional
pairings integrable for every scalar and Euclidean-vector `L¹` class. -/
theorem horizontalWeakL1_pairings_integrable {d : ℕ} {Q : Measure (FieldPair d)}
    [IsProbabilityMeasure Q] (f : Lp ℝ 1 Q)
    (G : Lp (EuclideanSpace ℝ (Fin d)) 1 Q) (i : Fin d)
    (H : FieldPair d → ℝ) (hH : IsHorizontalTest H) :
    Integrable (fun ω => f ω * horizontalDerivative i H ω) Q ∧
    Integrable (fun ω => G ω i * H ω) Q := by
  obtain ⟨B, _hB0, hB⟩ := hH.bound_orbit
  obtain ⟨D, _hD0, hD⟩ := hH.bound_derivative i
  have hfInt : Integrable (fun ω => f ω) Q :=
    (Lp.memLp f).integrable (by norm_num : (1 : ENNReal) ≤ 1)
  have hGmem : MemLp (fun ω => G ω i) 1 Q := by
    have hcontinuous : Continuous (fun z : EuclideanSpace ℝ (Fin d) => z i) := by fun_prop
    apply (Lp.memLp G).of_le
    · exact hcontinuous.comp_aestronglyMeasurable (Lp.memLp G).aestronglyMeasurable
    · filter_upwards with ω
      change ‖G ω i‖ ≤ ‖G ω‖
      exact PiLp.norm_apply_le (G ω) i
  have hGInt : Integrable (fun ω => G ω i) Q :=
    hGmem.integrable (by norm_num : (1 : ENNReal) ≤ 1)
  have hderBound : ∀ᵐ ω ∂Q, ‖horizontalDerivative i H ω‖ ≤ D := by
    filter_upwards with ω
    simpa only [Real.norm_eq_abs, horizontalDerivative] using hD ω 0
  have hvalueBound : ∀ᵐ ω ∂Q, ‖H ω‖ ≤ B := by
    filter_upwards with ω
    simpa only [Real.norm_eq_abs, orbit_zero] using hB ω 0
  exact ⟨hfInt.mul_bdd (hH.measurable_derivative i).aestronglyMeasurable hderBound,
    hGInt.mul_bdd hH.1.aestronglyMeasurable hvalueBound⟩

/-- On a probability space, an `L²` class has its canonical `L¹` class. -/
noncomputable def horizontalLpTwoToOne {d : ℕ} {α : Type*} [NormedAddCommGroup α]
    [NormedSpace ℝ α] (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (f : Lp α 2 Q) : Lp α 1 Q :=
  ((Lp.memLp f).mono_exponent (by norm_num : (1 : ENNReal) ≤ 2)).toLp f

theorem horizontalLpTwoToOne_coeFn {d : ℕ} {α : Type*} [NormedAddCommGroup α]
    [NormedSpace ℝ α] (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (f : Lp α 2 Q) : horizontalLpTwoToOne Q f =ᵐ[Q] fun ω => f ω := by
  exact ((Lp.memLp f).mono_exponent (by norm_num : (1 : ENNReal) ≤ 2)).coeFn_toLp

/-- A full horizontal `H¹` element supplies an actual weak `L¹` gradient. The vector witness is
the Euclidean assembly of its canonical `L²` generator derivatives, transported to `L¹` on the
same probability space. -/
theorem horizontalH1_exists_weakL1Gradient {d : ℕ} (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (hQ : IsStationary Q) (f : horizontalH1 Q hQ) :
    ∃ G : Lp (EuclideanSpace ℝ (Fin d)) 1 Q,
      HasWeakHorizontalL1Gradient Q (horizontalLpTwoToOne Q (f : Lp ℝ 2 Q)) G := by
  obtain ⟨G₂, hG₂⟩ := Correctors.exists_euclidean_horizontalH1Gradient Q hQ f
  refine ⟨horizontalLpTwoToOne Q G₂, ?_⟩
  intro i H hH
  let f₂ : Lp ℝ 2 Q := f
  let g₂ : Lp ℝ 2 Q := horizontalH1Gradient Q hQ f i
  have hweak : Correctors.HasWeakHorizontalLpDerivative Q i f₂ g₂ :=
    Correctors.hasHorizontalLpDerivative_to_weak
      (hasHorizontalLpDerivative_horizontalH1Gradient Q hQ f i)
  have hfAe : horizontalLpTwoToOne Q f₂ =ᵐ[Q] fun ω => f₂ ω :=
    horizontalLpTwoToOne_coeFn Q f₂
  have hGAe : horizontalLpTwoToOne Q G₂ =ᵐ[Q] fun ω => G₂ ω :=
    horizontalLpTwoToOne_coeFn Q G₂
  have hCoord : (fun ω => horizontalLpTwoToOne Q G₂ ω i) =ᵐ[Q]
      fun ω => g₂ ω := by
    filter_upwards [hGAe, hG₂.1 i] with ω hω hωi
    rw [hω]
    exact hωi
  have hLeft : (fun ω => horizontalLpTwoToOne Q f₂ ω * horizontalDerivative i H ω) =ᵐ[Q]
      fun ω => f₂ ω * horizontalDerivative i H ω := by
    filter_upwards [hfAe] with ω hω
    rw [hω]
  have hRight : (fun ω => g₂ ω * H ω) =ᵐ[Q]
      fun ω => horizontalLpTwoToOne Q G₂ ω i * H ω := by
    filter_upwards [hCoord] with ω hω
    rw [hω]
  refine ⟨(hweak H hH).1.congr hLeft.symm,
    (hweak H hH).2.1.congr hRight, ?_⟩
  calc
    (∫ ω, horizontalLpTwoToOne Q f₂ ω * horizontalDerivative i H ω ∂Q) =
        ∫ ω, f₂ ω * horizontalDerivative i H ω ∂Q := integral_congr_ae hLeft
    _ = -(∫ ω, g₂ ω * H ω ∂Q) := (hweak H hH).2.2
    _ = -(∫ ω, horizontalLpTwoToOne Q G₂ ω i * H ω ∂Q) := by
      congr 1
      exact integral_congr_ae hRight

end EinsteinRelation
