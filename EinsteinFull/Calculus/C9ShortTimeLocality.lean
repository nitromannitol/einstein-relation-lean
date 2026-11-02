import EinsteinFull.Blueprint.G3.node_p_u3A_late_u23_dyadic_u2D_increments
import EinsteinFull.Calculus.C1ForcedLocalityClosureSupport
import EinsteinFull.Calculus.ComplexCommonSpatialSupport
import EinsteinRelation.Correctors.SpatialWeakCongruence
import EinsteinFull.Calculus.S5PointwiseSupport
import EinsteinFull.Work.W6.HorizontalPhysicalRealizationProof
import EinsteinFull.Work.W6.PhysicalLocalTestingSupport
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondexpL2
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- Proposed internal cutoff estimate for paper/main.tex:1073–1080.
This is an UNPROVED specification, excluded from production. It is neither
a literature input nor an additional premise of the dyadic reduction.

Unlike scalar short-time locality, the same radius admits time-integrable
local approximants for the actual gradient and transpose endpoint. The error
uses the Euclidean sum of coordinate L² norms, integrated in time; this L¹
time estimate suffices for Minkowski and does not require an L² time bound.
All constants precede the law and the force on the fixed disc of radius two.
The existing bounded-time size estimates are separate from this locality gap. -/
def c9ShortTimeGradientLocalityStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d),
    ∃ C c : ℝ, 1 ≤ C ∧ 0 < c ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q))
      (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ ζ : ℂ, ‖ζ‖ ≤ 2 →
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
      IsComplexTransposeSemigroup Q P Pdag →
    ∀ G F : ℝ≥0 → FluxIndex d → Fin d → Lp ℂ 2 (reducedLaw Q),
      IsFiniteTimeFlux hd Q ζ P Pdag β a μ G F →
    ∀ (ν : FluxIndex d) (ρ : ℝ), C ≤ ρ →
      ∃ Gloc : ℝ → Fin d → Lp ℂ 2 (reducedLaw Q),
      ∃ Uloc : ℝ → Lp ℂ 2 (reducedLaw Q),
        (∀ j, IntegrableOn (fun r => Gloc r j) (Set.Icc (0 : ℝ) 1)) ∧
        IntegrableOn Uloc (Set.Icc (0 : ℝ) 1) ∧
        (∀ᵐ r ∂volume.restrict (Set.Icc (0 : ℝ) 1),
          (∀ j, IsComplexLocalObservation Q ρ (Gloc r j)) ∧
          IsComplexLocalObservation Q ρ (Uloc r)) ∧
        IntegrableOn (fun r : ℝ =>
          Real.sqrt (∑ j : Fin d, ‖G r.toNNReal ν j - Gloc r j‖ ^ 2) +
            ‖transposeEndpoint Q ⟨0, by omega⟩ Pdag β r.toNNReal - Uloc r‖)
          (Set.Icc (0 : ℝ) 1) ∧
        (∫ r in Set.Icc (0 : ℝ) 1,
          Real.sqrt (∑ j : Fin d, ‖G r.toNNReal ν j - Gloc r j‖ ^ 2) +
            ‖transposeEndpoint Q ⟨0, by omega⟩ Pdag β r.toNNReal - Uloc r‖) ≤
          C * Real.exp (-c * ρ ^ 2)

end EinsteinFull.Blueprint

namespace EinsteinFull.C9ShortTimeLocality
open EinsteinRelation

noncomputable section

variable {d : ℕ} {Λ r₀ : ℝ} (Q : EnvironmentLaw d Λ r₀) (ρ : ℝ)

/-- A fixed joint-field localization operator, independent of time. -/
def localProjection : Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q) :=
  (lpMeas ℂ ℂ (localSigma {x : Vec d | euclideanNorm x < ρ}) 2
    (reducedLaw Q)).subtypeL.comp
      (condExpL2 ℂ ℂ (Probability.localSigma_le_borel
        {x : Vec d | euclideanNorm x < ρ}))

/-- Every projected class has a representative measurable in the joint local
coefficient and clock sigma algebra. -/
theorem localProjection_isLocal (f : Lp ℂ 2 (reducedLaw Q)) :
    IsComplexLocalObservation Q ρ (localProjection Q ρ f) := by
  have ha := aestronglyMeasurable_condExpL2 (𝕜 := ℂ)
    (Probability.localSigma_le_borel {x : Vec d | euclideanNorm x < ρ}) f
  exact ⟨ha.mk _, ha.stronglyMeasurable_mk.measurable, ha.ae_eq_mk.symm⟩

/-- This localization does not increase the actual environment L² norm. -/
theorem norm_localProjection_le (f : Lp ℂ 2 (reducedLaw Q)) :
    ‖localProjection Q ρ f‖ ≤ ‖f‖ :=
  norm_condExpL2_coe_le
    (Probability.localSigma_le_borel {x : Vec d | euclideanNorm x < ρ}) f

/-- Already local observations are fixed by the same time-independent operator. -/
theorem localProjection_of_isLocal {f : Lp ℂ 2 (reducedLaw Q)}
    (hf : IsComplexLocalObservation Q ρ f) : localProjection Q ρ f = f := by
  letI : Fact (localSigma {x : Vec d | euclideanNorm x < ρ} ≤ borel (FieldPair d)) :=
    ⟨Probability.localSigma_le_borel _⟩
  obtain ⟨g, hg, hgf⟩ := hf
  have hmem : f ∈ lpMeas ℂ ℂ
      (localSigma {x : Vec d | euclideanNorm x < ρ}) 2 (reducedLaw Q) :=
    mem_lpMeas_iff_aestronglyMeasurable.mpr
      (hg.stronglyMeasurable.aestronglyMeasurable.congr hgf)
  let v : lpMeas ℂ ℂ (localSigma {x : Vec d | euclideanNorm x < ρ})
      2 (reducedLaw Q) := ⟨f, hmem⟩
  change (((lpMeas ℂ ℂ (localSigma {x : Vec d | euclideanNorm x < ρ})
    2 (reducedLaw Q)).orthogonalProjectionOnto v) : Lp ℂ 2 (reducedLaw Q)) = f
  exact congrArg Subtype.val
    (Submodule.orthogonalProjectionOnto_mem_subspace_eq_self v)

/-- Any proved cutoff approximant bounds the error of the coherent projection.
The approximant is used only in this elementary comparison, not selected in time. -/
theorem norm_sub_localProjection_le {f v : Lp ℂ 2 (reducedLaw Q)}
    (hv : IsComplexLocalObservation Q ρ v) :
    ‖f - localProjection Q ρ f‖ ≤ 2 * ‖f - v‖ := by
  have he : (f - v) - localProjection Q ρ (f - v) = f - localProjection Q ρ f := by
    rw [map_sub, localProjection_of_isLocal Q ρ hv]
    abel
  rw [← he]
  exact (norm_sub_le _ _).trans (by
    have h := norm_localProjection_le Q ρ (f - v)
    linarith)

/-- Coordinatewise comparison retains the Euclidean error without a factor
depending on the number of coordinates. -/
theorem euclidean_sub_localProjection_le
    (f v : Fin d → Lp ℂ 2 (reducedLaw Q))
    (hv : ∀ j, IsComplexLocalObservation Q ρ (v j)) :
    Real.sqrt (∑ j : Fin d, ‖f j - localProjection Q ρ (f j)‖ ^ 2) ≤
      2 * Real.sqrt (∑ j : Fin d, ‖f j - v j‖ ^ 2) := by
  calc
    Real.sqrt (∑ j : Fin d, ‖f j - localProjection Q ρ (f j)‖ ^ 2) ≤
        Real.sqrt (∑ j : Fin d, (2 * ‖f j - v j‖) ^ 2) := by
      apply Real.sqrt_le_sqrt
      apply Finset.sum_le_sum
      intro j _
      exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr
        (norm_sub_localProjection_le Q ρ (hv j))
    _ = 2 * Real.sqrt (∑ j : Fin d, ‖f j - v j‖ ^ 2) := by
      have he : (∑ j : Fin d, (2 * ‖f j - v j‖) ^ 2) =
          4 * ∑ j : Fin d, ‖f j - v j‖ ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      rw [he, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
      rw [(Real.sqrt_eq_iff_mul_self_eq (by norm_num : (0 : ℝ) ≤ 4)
        (by norm_num : (0 : ℝ) ≤ 2)).mpr (by norm_num)]

/-- A coherent local approximation to a continuous orbit remains continuous
through the initial time; there is no separate timewise choice of witnesses. -/
theorem continuous_localProjection {f : ℝ≥0 → Lp ℂ 2 (reducedLaw Q)}
    (hf : Continuous f) : Continuous (fun t => localProjection Q ρ (f t)) :=
  (localProjection Q ρ).continuous.comp hf

/-- Projected continuous orbits are Bochner integrable on the first unit interval. -/
theorem integrableOn_localProjection {f : ℝ≥0 → Lp ℂ 2 (reducedLaw Q)}
    (hf : Continuous f) :
    IntegrableOn (fun t : ℝ => localProjection Q ρ (f t.toNNReal))
      (Set.Icc (0 : ℝ) 1) :=
  ((continuous_localProjection Q ρ hf).comp
    continuous_real_toNNReal).continuousOn.integrableOn_Icc

/-- Integrating at a fixed localization radius preserves the joint local class. -/
theorem integral_localProjection_isLocal
    {f : ℝ → Lp ℂ 2 (reducedLaw Q)}
    (hf : IntegrableOn f (Set.Icc (0 : ℝ) 1)) :
    IsComplexLocalObservation Q ρ
      (∫ t in Set.Icc (0 : ℝ) 1, localProjection Q ρ (f t)) := by
  rw [(localProjection Q ρ).integral_comp_comm hf]
  exact localProjection_isLocal Q ρ _

/-- The Euclidean gradient error plus scalar error is genuinely integrable
for continuous orbits. In particular its integral cannot vanish merely because
of the convention for a nonintegrable Bochner integral. -/
theorem integrableOn_projection_error
    {g : ℝ≥0 → Fin d → Lp ℂ 2 (reducedLaw Q)}
    {u : ℝ≥0 → Lp ℂ 2 (reducedLaw Q)}
    (hg : ∀ j, Continuous (fun t => g t j)) (hu : Continuous u) :
    IntegrableOn (fun t : ℝ =>
      Real.sqrt (∑ j : Fin d,
        ‖g t.toNNReal j - localProjection Q ρ (g t.toNNReal j)‖ ^ 2) +
      ‖u t.toNNReal - localProjection Q ρ (u t.toNNReal)‖)
      (Set.Icc (0 : ℝ) 1) := by
  have hc : Continuous (fun t : ℝ≥0 =>
      Real.sqrt (∑ j : Fin d, ‖g t j - localProjection Q ρ (g t j)‖ ^ 2) +
        ‖u t - localProjection Q ρ (u t)‖) :=
    (Real.continuous_sqrt.comp (continuous_finsetSum _ (fun j _ =>
      ((hg j).sub (continuous_localProjection Q ρ (hg j))).norm.pow 2))).add
      (hu.sub (continuous_localProjection Q ρ hu)).norm
  exact (hc.comp continuous_real_toNNReal).continuousOn.integrableOn_Icc

/-- A local gradient vector and scalar may be compared jointly with the fixed
projection, retaining the Euclidean norm and a dimension-independent factor. -/
theorem combined_projection_error_le
    (g v : Fin d → Lp ℂ 2 (reducedLaw Q))
    (u w : Lp ℂ 2 (reducedLaw Q))
    (hv : ∀ j, IsComplexLocalObservation Q ρ (v j))
    (hw : IsComplexLocalObservation Q ρ w) :
    Real.sqrt (∑ j : Fin d, ‖g j - localProjection Q ρ (g j)‖ ^ 2) +
        ‖u - localProjection Q ρ u‖ ≤
      2 * (Real.sqrt (∑ j : Fin d, ‖g j - v j‖ ^ 2) + ‖u - w‖) := by
  have hg := euclidean_sub_localProjection_le Q ρ g v hv
  have hu := norm_sub_localProjection_le Q ρ (f := u) hw
  linarith

/-- Timewise cutoff comparisons transfer to the coherent projected orbits.
The comparison witnesses need no time measurability: only the majorant is
integrated. This is a generic transfer lemma, not a Gaussian cutoff estimate. -/
theorem integral_projection_error_le_of_local_witnesses
    {g : ℝ≥0 → Fin d → Lp ℂ 2 (reducedLaw Q)}
    {u : ℝ≥0 → Lp ℂ 2 (reducedLaw Q)}
    (hg : ∀ j, Continuous (fun t => g t j)) (hu : Continuous u)
    (B : ℝ → ℝ) (hB : IntegrableOn B (Set.Icc (0 : ℝ) 1))
    (hcut : ∀ᵐ t ∂volume.restrict (Set.Icc (0 : ℝ) 1),
      ∃ v : Fin d → Lp ℂ 2 (reducedLaw Q),
      ∃ w : Lp ℂ 2 (reducedLaw Q),
        (∀ j, IsComplexLocalObservation Q ρ (v j)) ∧
        IsComplexLocalObservation Q ρ w ∧
        Real.sqrt (∑ j : Fin d, ‖g t.toNNReal j - v j‖ ^ 2) +
          ‖u t.toNNReal - w‖ ≤ B t) :
    (∫ t in Set.Icc (0 : ℝ) 1,
      Real.sqrt (∑ j : Fin d,
        ‖g t.toNNReal j - localProjection Q ρ (g t.toNNReal j)‖ ^ 2) +
      ‖u t.toNNReal - localProjection Q ρ (u t.toNNReal)‖) ≤
      2 * ∫ t in Set.Icc (0 : ℝ) 1, B t := by
  rw [← integral_const_mul]
  apply integral_mono_ae (integrableOn_projection_error Q ρ hg hu) (hB.const_mul 2)
  filter_upwards [hcut] with t ht
  obtain ⟨v, w, hv, hw, herr⟩ := ht
  exact (combined_projection_error_le Q ρ (g t.toNNReal) v
    (u t.toNNReal) w hv hw).trans (mul_le_mul_of_nonneg_left herr (by norm_num))

/-- The actual finite-time-flux gradient and transpose endpoint admit coherent
local projected orbits with genuine Bochner integrals on the first interval.
This proves the time-selection prerequisite only; no Gaussian error is asserted. -/
theorem finiteTimeFlux_local_orbits
    (hd : 2 ≤ d) (ζ : ℂ)
    (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
    (G F : ℝ≥0 → FluxIndex d → Fin d → Lp ℂ 2 (reducedLaw Q))
    (hF : IsFiniteTimeFlux hd Q ζ P Pdag β a μ G F) (ν : FluxIndex d) :
    ∃ Gloc : ℝ≥0 → Fin d → Lp ℂ 2 (reducedLaw Q),
    ∃ Uloc : ℝ≥0 → Lp ℂ 2 (reducedLaw Q),
      (∀ j, Continuous (fun t => Gloc t j) ∧
        IntegrableOn (fun t : ℝ => Gloc t.toNNReal j) (Set.Icc (0 : ℝ) 1) ∧
        ∀ t, IsComplexLocalObservation Q ρ (Gloc t j)) ∧
      Continuous Uloc ∧
      IntegrableOn (fun t : ℝ => Uloc t.toNNReal) (Set.Icc (0 : ℝ) 1) ∧
      (∀ t, IsComplexLocalObservation Q ρ (Uloc t)) ∧
      IntegrableOn (fun t : ℝ =>
        Real.sqrt (∑ j : Fin d, ‖G t.toNNReal ν j - Gloc t.toNNReal j‖ ^ 2) +
          ‖transposeEndpoint Q ⟨0, by omega⟩ Pdag β t.toNNReal - Uloc t.toNNReal‖)
        (Set.Icc (0 : ℝ) 1) := by
  obtain ⟨hG, hU, _⟩ := hF
  refine ⟨fun t j => localProjection Q ρ (G t ν j),
    fun t => localProjection Q ρ (transposeEndpoint Q ⟨0, by omega⟩ Pdag β t), ?_, ?_⟩
  · intro j
    exact ⟨continuous_localProjection Q ρ (hG ν j),
      integrableOn_localProjection Q ρ (hG ν j),
      fun _ => localProjection_isLocal Q ρ _⟩
  · have hT : Continuous (fun t => transposeEndpoint Q ⟨0, by omega⟩ Pdag β t) :=
      hU _
    refine ⟨continuous_localProjection Q ρ hT,
      integrableOn_localProjection Q ρ hT,
      (fun _ => localProjection_isLocal Q ρ _), ?_⟩
    exact integrableOn_projection_error Q ρ
      (g := fun t j => G t ν j)
      (u := fun t => transposeEndpoint Q ⟨0, by omega⟩ Pdag β t)
      (hG ν) hT

end
end EinsteinFull.C9ShortTimeLocality

namespace EinsteinFull.C9ShortTimeLocality
open EinsteinRelation
noncomputable section

/-- The divergence forcing in the difference between the actual and retained
coefficient operators, evaluated on the same complex gradient. -/
def retainedFluxDefect {d : ℕ} (χ : C(Vec d, ℝ)) (ω : FieldPair d)
    (x : Vec d) (X : Fin d → ℂ) (j : Fin d) : ℂ :=
  (1 / 2 : ℂ) * ∑ k : Fin d,
    ((ω.1 x j k - (ForcedLocality.retainedPair χ ω).1 x j k : ℝ) : ℂ) * X k

/-- The lower-order forcing retains the actual signed complex force. -/
def retainedDriftDefect {d : ℕ} (χ : C(Vec d, ℝ)) (ω : FieldPair d)
    (x : Vec d) (X : Fin d → ℂ) (i : Fin d) (ζ : ℂ) : ℂ :=
  ζ * ∑ j : Fin d,
    ((ω.1 x j i - (ForcedLocality.retainedPair χ ω).1 x j i : ℝ) : ℂ) * X j

/-- The retained coefficient defect is exactly the discarded fraction of
`a-Id`; this is an identity on the actual fields, not a law comparison. -/
theorem retainedPair_coefficient_sub {d : ℕ} (χ : C(Vec d, ℝ))
    (ω : FieldPair d) (x : Vec d) (j k : Fin d) :
    ω.1 x j k - (ForcedLocality.retainedPair χ ω).1 x j k =
      (1 - χ x) * (ω.1 x j k - (1 : Mat d) j k) := by
  change ω.1 x j k - (χ x * ω.1 x j k + (1 - χ x) * (1 : Mat d) j k) = _
  ring

/-- Both operator-difference sources vanish in the retained interior. -/
theorem retainedDefects_eq_zero {d : ℕ} (χ : C(Vec d, ℝ))
    (ω : FieldPair d) {x : Vec d} (hx : χ x = 1)
    (X : Fin d → ℂ) (i : Fin d) (ζ : ℂ) :
    (∀ j, retainedFluxDefect χ ω x X j = 0) ∧
      retainedDriftDefect χ ω x X i ζ = 0 := by
  have he := (ForcedLocality.retainedPair_eq_at χ ω hx).1
  simp only [retainedFluxDefect, retainedDriftDefect, he, sub_self,
    Complex.ofReal_zero, zero_mul, Finset.sum_const_zero, mul_zero, implies_true,
    and_self]

/-- After an outer cutoff, the actual operator-difference forcing is supported
in the Euclidean annulus between the retained interior and outer boundary. -/
theorem retainedDefects_annulus {d : ℕ} (χ : C(Vec d, ℝ))
    (ψ : Vec d → ℝ) (ω : FieldPair d) (z : Vec d) (r : ℝ)
    (hχ : ∀ x, euclideanNorm (x - z) < r → χ x = 1)
    (hψ : ∀ x, 2 * r ≤ euclideanNorm (x - z) → ψ x = 0)
    (X : Vec d → Fin d → ℂ) (i : Fin d) (ζ : ℂ)
    (x : Vec d) (hx : x ∉ {y : Vec d |
      r ≤ euclideanNorm (y - z) ∧ euclideanNorm (y - z) < 2 * r}) :
    (∀ j, (ψ x : ℂ) * retainedFluxDefect χ ω x (X x) j = 0) ∧
      (ψ x : ℂ) * retainedDriftDefect χ ω x (X x) i ζ = 0 := by
  by_cases hi : euclideanNorm (x - z) < r
  · obtain ⟨hf, hb⟩ := retainedDefects_eq_zero χ ω (hχ x hi) (X x) i ζ
    simp only [hf, hb, mul_zero, implies_true, and_self]
  · have ho : 2 * r ≤ euclideanNorm (x - z) := by
      by_contra hn
      exact hx ⟨le_of_not_gt hi, lt_of_not_ge hn⟩
    simp only [hψ x ho, Complex.ofReal_zero, zero_mul, implies_true, and_self]

/-- Exact divergence part of the actual retained-operator difference. -/
theorem retainedFluxDefect_test_eq {d : ℕ} (χ : C(Vec d, ℝ))
    (ω : FieldPair d) (x : Vec d) (X : Fin d → ℂ) (D : Fin d → ℝ) :
    (∑ j : Fin d, (D j : ℂ) * retainedFluxDefect χ ω x X j) =
      (1 / 2 : ℂ) * ((∑ j, ∑ k, (D j : ℂ) * (ω.1 x j k : ℂ) * X k) -
        ∑ j, ∑ k, (D j : ℂ) * ((ForcedLocality.retainedPair χ ω).1 x j k : ℂ) * X k) := by
  simp only [retainedFluxDefect, Finset.mul_sum, ← Finset.sum_sub_distrib,
    Complex.ofReal_sub]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Euclidean bound for testing the divergence forcing. The two coefficient
ellipticity constants are kept explicit; no stationary cutoff law is used. -/
theorem retainedFluxDefect_test_bound {d : ℕ} (χ : C(Vec d, ℝ))
    (ω : FieldPair d) (x : Vec d) (X : Fin d → ℂ) (D : Fin d → ℝ)
    {L M : ℝ} (hA : S5Elliptic (ω.1 x) L)
    (hB : S5Elliptic ((ForcedLocality.retainedPair χ ω).1 x) M) :
    ‖∑ j : Fin d, (D j : ℂ) * retainedFluxDefect χ ω x X j‖ ≤
      (L + M) * s5Nrm D * s5CNrm X := by
  rw [retainedFluxDefect_test_eq, norm_mul]
  have hn : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num
  rw [hn]
  have hnorm := norm_sub_le
    (∑ j, ∑ k, (D j : ℂ) * (ω.1 x j k : ℂ) * X k)
    (∑ j, ∑ k, (D j : ℂ) * ((ForcedLocality.retainedPair χ ω).1 x j k : ℂ) * X k)
  have ha := s5_cbil_norm_le hA D X
  have hb := s5_cbil_norm_le hB D X
  nlinarith only [hnorm, ha, hb]

/-- The drift defect has the corresponding Euclidean gradient bound, keeping
its linear dependence on the signed complex force. -/
theorem retainedDriftDefect_bound {d : ℕ} (χ : C(Vec d, ℝ))
    (ω : FieldPair d) (x : Vec d) (X : Fin d → ℂ) (i : Fin d) (ζ : ℂ)
    {L M : ℝ} (hA : S5Elliptic (ω.1 x) L)
    (hB : S5Elliptic ((ForcedLocality.retainedPair χ ω).1 x) M) :
    ‖retainedDriftDefect χ ω x X i ζ‖ ≤
      2 * (L + M) * ‖ζ‖ * s5CNrm X := by
  simp only [retainedDriftDefect, Complex.ofReal_sub, sub_mul,
    Finset.sum_sub_distrib, norm_mul]
  have ha := s5_row_norm_le hA i X
  have hb := s5_row_norm_le hB i X
  calc
    _ ≤ ‖ζ‖ * (‖∑ j, (ω.1 x j i : ℂ) * X j‖ +
        ‖∑ j, ((ForcedLocality.retainedPair χ ω).1 x j i : ℂ) * X j‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le _ _) (norm_nonneg _)
    _ ≤ ‖ζ‖ * (2 * L * s5CNrm X + 2 * M * s5CNrm X) :=
      mul_le_mul_of_nonneg_left (add_le_add ha hb) (norm_nonneg _)
    _ = _ := by ring

/-- Exact weak generator-density difference on the same gradient and real
test function. The source consists of a divergence part and force drift. -/
theorem retained_generator_density_difference {d : ℕ} (χ : C(Vec d, ℝ))
    (ω : FieldPair d) (x : Vec d) (X : Fin d → ℂ) (D : Fin d → ℝ)
    (v : ℝ) (i : Fin d) (ζ : ℂ) :
    (-(1 / 2 : ℂ) * (∑ j, ∑ k, (D j : ℂ) * (ω.1 x j k : ℂ) * X k) +
      ζ * (∑ j, (ω.1 x j i : ℂ) * X j) * (v : ℂ)) -
    (-(1 / 2 : ℂ) * (∑ j, ∑ k, (D j : ℂ) *
      ((ForcedLocality.retainedPair χ ω).1 x j k : ℂ) * X k) +
      ζ * (∑ j, ((ForcedLocality.retainedPair χ ω).1 x j i : ℂ) * X j) * (v : ℂ)) =
      -(∑ j, (D j : ℂ) * retainedFluxDefect χ ω x X j) +
        retainedDriftDefect χ ω x X i ζ * (v : ℂ) := by
  rw [retainedFluxDefect_test_eq]
  simp only [retainedDriftDefect, Complex.ofReal_sub, sub_mul, Finset.sum_sub_distrib]
  ring


/-- Weak physical generator density, with the real test value and gradient
kept separate so that the cutoff product rule can be stated explicitly. -/
def cutoffGeneratorDensity {d : ℕ} (A : Mat d) (X : Fin d → ℂ)
    (D : Fin d → ℝ) (v : ℝ) (i : Fin d) (ζ : ℂ) : ℂ :=
  -(1 / 2 : ℂ) * (∑ j, ∑ k, (D j : ℂ) * (A j k : ℂ) * X k) +
    ζ * (∑ j, (A j i : ℂ) * X j) * (v : ℂ)

/-- Divergence source generated by the derivative of the outer cutoff. -/
def cutoffFluxSource {d : ℕ} (A : Mat d) (E : Fin d → ℝ)
    (u : ℂ) (j : Fin d) : ℂ :=
  -(1 / 2 : ℂ) * u * ∑ k, (A j k : ℂ) * (E k : ℂ)

/-- Scalar source generated by the derivative of the outer cutoff. -/
def cutoffScalarSource {d : ℕ} (A : Mat d) (X : Fin d → ℂ)
    (E : Fin d → ℝ) (u : ℂ) (i : Fin d) (ζ : ℂ) : ℂ :=
  (1 / 2 : ℂ) * (∑ j, ∑ k, (E j : ℂ) * (A j k : ℂ) * X k) +
    ζ * u * ∑ j, (A j i : ℂ) * (E j : ℂ)

/-- Exact weak cutoff commutator. Here `E` is the cutoff gradient, so that
`ψ*X+u*E` and `ψ*D+v*E` are the two product-rule gradients. -/
theorem cutoff_generator_density_commutator {d : ℕ} (A : Mat d)
    (X : Fin d → ℂ) (D E : Fin d → ℝ) (u : ℂ) (ψ v : ℝ)
    (i : Fin d) (ζ : ℂ) :
    cutoffGeneratorDensity A (fun k => (ψ : ℂ) * X k + u * (E k : ℂ)) D v i ζ -
      cutoffGeneratorDensity A X (fun j => ψ * D j + v * E j) (ψ * v) i ζ =
      (∑ j, (D j : ℂ) * cutoffFluxSource A E u j) +
        (v : ℂ) * cutoffScalarSource A X E u i ζ := by
  have hX : (∑ j, ∑ k, (D j : ℂ) * (A j k : ℂ) *
      ((ψ : ℂ) * X k + u * (E k : ℂ))) =
      (ψ : ℂ) * (∑ j, ∑ k, (D j : ℂ) * (A j k : ℂ) * X k) +
      u * (∑ j, ∑ k, (D j : ℂ) * (A j k : ℂ) * (E k : ℂ)) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hD : (∑ j, ∑ k, ((ψ * D j + v * E j : ℝ) : ℂ) *
      (A j k : ℂ) * X k) =
      (ψ : ℂ) * (∑ j, ∑ k, (D j : ℂ) * (A j k : ℂ) * X k) +
      (v : ℂ) * (∑ j, ∑ k, (E j : ℂ) * (A j k : ℂ) * X k) := by
    simp only [Complex.ofReal_add, Complex.ofReal_mul,
      Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hR : (∑ j, (A j i : ℂ) * ((ψ : ℂ) * X j + u * (E j : ℂ))) =
      (ψ : ℂ) * (∑ j, (A j i : ℂ) * X j) +
      u * (∑ j, (A j i : ℂ) * (E j : ℂ)) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hF : (∑ j, (D j : ℂ) * cutoffFluxSource A E u j) =
      -(1 / 2 : ℂ) * u *
        (∑ j, ∑ k, (D j : ℂ) * (A j k : ℂ) * (E k : ℂ)) := by
    simp only [cutoffFluxSource, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  simp only [cutoffGeneratorDensity, hX, hD, hR, hF, cutoffScalarSource,
    Complex.ofReal_mul]
  ring

/-- Both outer-cutoff sources vanish wherever the cutoff gradient vanishes. -/
theorem cutoffSources_eq_zero {d : ℕ} (A : Mat d) (X : Fin d → ℂ)
    (E : Fin d → ℝ) (hE : ∀ j, E j = 0) (u : ℂ) (i : Fin d) (ζ : ℂ) :
    (∀ j, cutoffFluxSource A E u j = 0) ∧
      cutoffScalarSource A X E u i ζ = 0 := by
  simp [cutoffFluxSource, cutoffScalarSource, hE]

/-- The derivative sources have the same Euclidean annulus support as the
cutoff gradient. This statement uses the actual coefficient field pointwise. -/
theorem cutoffSources_annulus {d : ℕ} (ω : FieldPair d)
    (X : Vec d → Fin d → ℂ) (E : Vec d → Fin d → ℝ)
    (u : Vec d → ℂ) (z : Vec d) (r : ℝ)
    (hE : ∀ x, euclideanNorm (x - z) < r ∨
      2 * r ≤ euclideanNorm (x - z) → ∀ j, E x j = 0)
    (i : Fin d) (ζ : ℂ) (x : Vec d)
    (hx : x ∉ {y : Vec d | r ≤ euclideanNorm (y - z) ∧
      euclideanNorm (y - z) < 2 * r}) :
    (∀ j, cutoffFluxSource (ω.1 x) (E x) (u x) j = 0) ∧
      cutoffScalarSource (ω.1 x) (X x) (E x) (u x) i ζ = 0 := by
  apply cutoffSources_eq_zero
  apply hE x
  by_cases hi : euclideanNorm (x - z) < r
  · exact Or.inl hi
  · exact Or.inr (not_lt.mp fun ho => hx ⟨le_of_not_gt hi, ho⟩)

/-- Complexification preserves the explicit Euclidean coordinate norm. -/
theorem s5CNrm_ofReal {d : ℕ} (E : Fin d → ℝ) :
    s5CNrm (fun j => (E j : ℂ)) = s5Nrm E := by
  simp [s5CNrm, s5Nrm, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- Dimension-free bound on the divergence cutoff source tested against a
real gradient. The cutoff derivative enters through its Euclidean norm. -/
theorem cutoffFluxSource_test_bound {d : ℕ} {A : Mat d} {L : ℝ}
    (hA : S5Elliptic A L) (D E : Fin d → ℝ) (u : ℂ) :
    ‖∑ j, (D j : ℂ) * cutoffFluxSource A E u j‖ ≤
      L * ‖u‖ * s5Nrm D * s5Nrm E := by
  have he : (∑ j, (D j : ℂ) * cutoffFluxSource A E u j) =
      -(1 / 2 : ℂ) * u * ∑ j, ∑ k,
        (D j : ℂ) * (A j k : ℂ) * (E k : ℂ) := by
    simp only [cutoffFluxSource, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [he, norm_mul, norm_mul]
  have hn : ‖-(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num
  rw [hn]
  have hb := s5_cbil_norm_le hA D (fun k => (E k : ℂ))
  rw [s5CNrm_ofReal] at hb
  nlinarith only [mul_le_mul_of_nonneg_left hb (show 0 ≤ (1 / 2 : ℝ) * ‖u‖ by positivity)]

/-- Dimension-free bound on the scalar cutoff source, including its signed
complex force contribution. -/
theorem cutoffScalarSource_bound {d : ℕ} {A : Mat d} {L : ℝ}
    (hA : S5Elliptic A L) (X : Fin d → ℂ) (E : Fin d → ℝ)
    (u : ℂ) (i : Fin d) (ζ : ℂ) :
    ‖cutoffScalarSource A X E u i ζ‖ ≤
      L * s5Nrm E * s5CNrm X + 2 * L * ‖ζ‖ * ‖u‖ * s5Nrm E := by
  have hb := s5_cbil_norm_le hA E X
  have hr := s5_row_norm_le hA i (fun j => (E j : ℂ))
  rw [s5CNrm_ofReal] at hr
  unfold cutoffScalarSource
  calc
    _ ≤ ‖(1 / 2 : ℂ) * (∑ j, ∑ k, (E j : ℂ) * (A j k : ℂ) * X k)‖ +
        ‖ζ * u * ∑ j, (A j i : ℂ) * (E j : ℂ)‖ := norm_add_le _ _
    _ ≤ (1 / 2 : ℝ) * (2 * L * s5Nrm E * s5CNrm X) +
        (‖ζ‖ * ‖u‖) * (2 * L * s5Nrm E) := by
      simp only [norm_mul]
      have hn : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num
      rw [hn]
      exact add_le_add (mul_le_mul_of_nonneg_left hb (by positivity))
        (mul_le_mul_of_nonneg_left hr (by positivity))
    _ = _ := by ring


/-- Full pointwise source decomposition for localizing the original operator
and comparing it with the retained operator. No stationarity of the retained
field law is assumed. -/
theorem retained_cutoff_generator_density_difference {d : ℕ}
    (χ : C(Vec d, ℝ)) (ω : FieldPair d) (x : Vec d)
    (X : Fin d → ℂ) (D E : Fin d → ℝ) (u : ℂ) (ψ v : ℝ)
    (i : Fin d) (ζ : ℂ) :
    cutoffGeneratorDensity (ω.1 x)
        (fun k => (ψ : ℂ) * X k + u * (E k : ℂ)) D v i ζ -
      cutoffGeneratorDensity ((ForcedLocality.retainedPair χ ω).1 x) X
        (fun j => ψ * D j + v * E j) (ψ * v) i ζ =
      (∑ j, (D j : ℂ) * cutoffFluxSource (ω.1 x) E u j) +
        (v : ℂ) * cutoffScalarSource (ω.1 x) X E u i ζ -
        (∑ j, ((ψ * D j + v * E j : ℝ) : ℂ) *
          retainedFluxDefect χ ω x X j) +
        retainedDriftDefect χ ω x X i ζ * ((ψ * v : ℝ) : ℂ) := by
  have hc := cutoff_generator_density_commutator (ω.1 x) X D E u ψ v i ζ
  have hr := retained_generator_density_difference χ ω x X
    (fun j => ψ * D j + v * E j) (ψ * v) i ζ
  change cutoffGeneratorDensity (ω.1 x) X _ _ i ζ -
    cutoffGeneratorDensity ((ForcedLocality.retainedPair χ ω).1 x) X _ _ i ζ = _ at hr
  calc
    _ = (cutoffGeneratorDensity (ω.1 x)
          (fun k => (ψ : ℂ) * X k + u * (E k : ℂ)) D v i ζ -
        cutoffGeneratorDensity (ω.1 x) X (fun j => ψ * D j + v * E j)
          (ψ * v) i ζ) +
        (cutoffGeneratorDensity (ω.1 x) X (fun j => ψ * D j + v * E j)
          (ψ * v) i ζ -
        cutoffGeneratorDensity ((ForcedLocality.retainedPair χ ω).1 x) X
          (fun j => ψ * D j + v * E j) (ψ * v) i ζ) := by ring
    _ = _ := by rw [hc, hr]; ring


/-- On a single environment event, every compact smooth cutoff of an actual
horizontal-gradient pair belongs to the physical H1 domain. The domain
representative includes the cutoff derivative, rather than identifying the
cutoff of a gradient with the gradient of the cutoff function. -/
theorem ae_physical_cutoff_h1 {d : ℕ} [Fact (2 ≤ d)] {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀)
    {f : Lp ℂ 2 (reducedLaw Q)} {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G) :
    ∀ᵐ ω ∂reducedLaw Q, ∀ ψ : Vec d → ℝ, IsSpatialTest Set.univ ψ →
      ∃ (u : Lp ℂ 2 (volume : Measure (Vec d)))
        (H : Fin d → Lp ℂ 2 (volume : Measure (Vec d))),
        IsPhysicalH1Graph volume (Or.inl rfl) u H ∧
        (u : Vec d → ℂ) =ᵐ[volume]
          (fun x => (ψ x : ℂ) * f (translate x ω)) ∧
        (∀ j, (H j : Vec d → ℂ) =ᵐ[volume]
          (fun x => (ψ x : ℂ) * G j (translate x ω) +
            f (translate x ω) * (coordinateDerivative j ψ x : ℂ))) ∧
        (∀ᵐ x ∂volume, x ∉ tsupport ψ → u x = 0 ∧ ∀ j, H j x = 0) := by
  filter_upwards [hG.ae_reduced_spatial Q] with ω hω
  intro ψ hψ
  exact physicalLocalH1_mul_test (isClosed_tsupport ψ).measurableSet
    ((hω.2.2 (tsupport ψ) hψ.2.1).1)
    (fun j => (hω.2.2 (tsupport ψ) hψ.2.1).2 j)
    (Correctors.hasWeakGradient_mono (Set.subset_univ _) hω.1)
    (Correctors.hasWeakGradient_mono (Set.subset_univ _) hω.2.1)
    ⟨hψ.1, hψ.2.1, Set.Subset.rfl⟩

/-- The actual indexed gradients in the finite-time flux contract admit
physical cutoff-domain representatives, including the transpose index. -/
theorem finiteTimeFlux_ae_physical_cutoff_h1 {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (ζ : ℂ)
    (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
    (G F : ℝ≥0 → FluxIndex d → Fin d → Lp ℂ 2 (reducedLaw Q))
    (hF : IsFiniteTimeFlux hd Q ζ P Pdag β a μ G F) (τ : ℝ≥0) (ν : FluxIndex d) :
    ∀ᵐ ω ∂reducedLaw Q, ∀ ψ : Vec d → ℝ, IsSpatialTest Set.univ ψ →
      ∃ (u : Lp ℂ 2 (volume : Measure (Vec d)))
        (H : Fin d → Lp ℂ 2 (volume : Measure (Vec d))),
        IsPhysicalH1Graph volume (Or.inl rfl) u H ∧
        (u : Vec d → ℂ) =ᵐ[volume] (fun x => (ψ x : ℂ) *
          (indexedEndpoint hd Q (ν.elim Sum.inl (fun _ => Sum.inr true))
            ζ P Pdag β a μ τ) (translate x ω)) ∧
        (∀ j, (H j : Vec d → ℂ) =ᵐ[volume] (fun x =>
          (ψ x : ℂ) * G τ ν j (translate x ω) +
          (indexedEndpoint hd Q (ν.elim Sum.inl (fun _ => Sum.inr true))
            ζ P Pdag β a μ τ) (translate x ω) * (coordinateDerivative j ψ x : ℂ))) ∧
        (∀ᵐ x ∂volume, x ∉ tsupport ψ → u x = 0 ∧ ∀ j, H j x = 0) := by
  let : Fact (2 ≤ d) := ⟨hd⟩
  exact ae_physical_cutoff_h1 Q (hF.choose_spec.choose_spec.1 τ ν)


/-- Local physical L2 data times a compact smooth cutoff give a whole-space
L2 function, without a global integrability assumption on the original data. -/
theorem memLp_local_mul_cutoff {d : ℕ} {u : Vec d → ℂ}
    (hu : ∀ K : Set (Vec d), IsCompact K → MemLp u 2 (volume.restrict K))
    {ψ : Vec d → ℝ} (hψ : IsSpatialTest Set.univ ψ) :
    MemLp (fun x => (ψ x : ℂ) * u x) 2 volume := by
  exact physicalLocal_memLp_mul_test (isClosed_tsupport ψ).measurableSet
    (hu (tsupport ψ) hψ.2.1) ⟨hψ.1, hψ.2.1, Set.Subset.rfl⟩

/-- Both outer-cutoff sources are genuine physical L2 functions. Coefficient
multipliers are derived from actual ellipticity and continuity; only local
L2 integrability is required of the unlocalized function and gradient. -/
theorem cutoffSources_memLp {d : ℕ} (A : Vec d → Mat d) (L : ℝ)
    (hL : 0 < L) (hA : IsElliptic L A)
    (hc : ∀ j k, Continuous (fun x => A x j k))
    {u : Vec d → ℂ} {X : Vec d → Fin d → ℂ}
    (hu : ∀ K : Set (Vec d), IsCompact K → MemLp u 2 (volume.restrict K))
    (hX : ∀ K : Set (Vec d), IsCompact K →
      ∀ j, MemLp (fun x => X x j) 2 (volume.restrict K))
    {ψ : Vec d → ℝ} (hψ : IsSpatialTest Set.univ ψ) (i : Fin d) (ζ : ℂ) :
    (∀ j, MemLp (fun x => cutoffFluxSource (A x)
      (fun k => coordinateDerivative k ψ x) (u x) j) 2 volume) ∧
    MemLp (fun x => cutoffScalarSource (A x) (X x)
      (fun k => coordinateDerivative k ψ x) (u x) i ζ) 2 volume := by
  have ha (j k : Fin d) := memLp_complex_elliptic_entry volume A L hL hA hc j k
  have hdu (j : Fin d) : MemLp
      (fun x => (coordinateDerivative j ψ x : ℂ) * u x) 2 volume :=
    memLp_local_mul_cutoff hu (Correctors.isSpatialTest_coordinateDerivative hψ j)
  have hdX (j k : Fin d) : MemLp
      (fun x => (coordinateDerivative j ψ x : ℂ) * X x k) 2 volume :=
    memLp_local_mul_cutoff (fun K hK => hX K hK k)
      (Correctors.isSpatialTest_coordinateDerivative hψ j)
  constructor
  · intro j
    have hs : MemLp (fun x => ∑ k, (A x j k : ℂ) *
        ((coordinateDerivative k ψ x : ℂ) * u x)) 2 volume :=
      memLp_finsetSum _ fun k _ => (ha j k).mul (hdu k)
    convert hs.const_mul (-(1 / 2 : ℂ)) using 1
    funext x
    simp only [cutoffFluxSource, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  · have hs : MemLp (fun x => ∑ j, ∑ k, (A x j k : ℂ) *
        ((coordinateDerivative j ψ x : ℂ) * X x k)) 2 volume :=
      memLp_finsetSum _ fun j _ => memLp_finsetSum _ fun k _ =>
        (ha j k).mul (hdX j k)
    have ht : MemLp (fun x => ∑ j, (A x j i : ℂ) *
        ((coordinateDerivative j ψ x : ℂ) * u x)) 2 volume :=
      memLp_finsetSum _ fun j _ => (ha j i).mul (hdu j)
    convert (hs.const_mul (1 / 2 : ℂ)).add (ht.const_mul ζ) using 1
    funext x
    simp only [cutoffScalarSource, Finset.mul_sum]
    congr 1
    · apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      ring
    · apply Finset.sum_congr rfl
      intro j _
      ring

/-- Compact localization puts both sides of an inhomogeneous divergence
in physical L2, including the contraction with the cutoff gradient. -/
theorem cutoffDivergenceSource_memLp {d : ℕ} {F : Vec d → Fin d → ℂ}
    {q : Vec d → ℂ}
    (hF : ∀ K : Set (Vec d), IsCompact K →
      ∀ j, MemLp (fun x => F x j) 2 (volume.restrict K))
    (hq : ∀ K : Set (Vec d), IsCompact K → MemLp q 2 (volume.restrict K))
    {ψ : Vec d → ℝ} (hψ : IsSpatialTest Set.univ ψ) :
    (∀ j, MemLp (fun x => (ψ x : ℂ) * F x j) 2 volume) ∧
      MemLp (fun x => (ψ x : ℂ) * q x +
        ∑ j, F x j * (coordinateDerivative j ψ x : ℂ)) 2 volume := by
  refine ⟨fun j => memLp_local_mul_cutoff (fun K hK => hF K hK j) hψ,
    (memLp_local_mul_cutoff hq hψ).add ?_⟩
  apply memLp_finsetSum
  intro j _
  simpa only [mul_comm] using memLp_local_mul_cutoff (fun K hK => hF K hK j)
    (Correctors.isSpatialTest_coordinateDerivative hψ j)

private theorem physical_divergence_projection {d : ℕ} {F : Vec d → Fin d → ℂ}
    {q : Vec d → ℂ}
    (hF : ∀ K : Set (Vec d), IsCompact K →
      ∀ j, MemLp (fun x => F x j) 2 (volume.restrict K))
    (hq : ∀ K : Set (Vec d), IsCompact K → MemLp q 2 (volume.restrict K))
    (hw : ∀ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      (∫ x, q x * (φ x : ℂ)) = -(∫ x, ∑ j, F x j * (coordinateDerivative j φ x : ℂ)))
    (L : ℂ →L[ℝ] ℝ) :
    HasWeakDivergence Set.univ (fun x j => L (F x j)) (fun x => L (q x)) := by
  have hloc {v : Vec d → ℂ}
      (hv : ∀ K : Set (Vec d), IsCompact K → MemLp v 2 (volume.restrict K)) :
      LocallyIntegrable (fun x => L (v x)) volume := by
    rw [locallyIntegrable_iff]
    intro K hK
    let : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_ne_top
    exact (L.comp_memLp' (hv K hK)).integrable (by norm_num)
  refine ⟨fun j => (hloc (fun K hK => hF K hK j)).locallyIntegrableOn Set.univ,
    (hloc hq).locallyIntegrableOn Set.univ, ?_⟩
  intro φ hφ
  have hi := integrable_spatial_mul_test hq hφ.1.continuous hφ.2.1
  have hj (j : Fin d) : Integrable (fun x => F x j * (coordinateDerivative j φ x : ℂ)) volume := integrable_spatial_mul_test (fun K hK => hF K hK j)
    ((hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const)
    (hφ.2.1.fderiv_apply ℝ (unitVector j))
  have hs := integrable_finsetSum Finset.univ (fun j _ => hj j)
  have he := congrArg L (hw φ hφ.1 hφ.2.1)
  rw [map_neg, ← L.integral_comp_comm hi, ← L.integral_comp_comm hs] at he
  have hp (z : ℂ) (c : ℝ) : L (z * (c : ℂ)) = L z * c := by
    rw [mul_comm, ← Complex.real_smul, L.map_smul, smul_eq_mul, mul_comm]
  simp only [map_sum, hp] at he
  simpa only [Measure.restrict_univ, dot, gradient] using (neg_eq_iff_eq_neg.mp he.symm)

/-- The actual generator equation localizes as a physical weak divergence.
The event precedes every smooth compact cutoff and both real projections.
The source retains the generator output, signed drift, and cutoff shell term. -/
theorem generatorPair_ae_cutoff_divergence {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) {i : Fin d} {ζ : ℂ}
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i ζ f g)
    {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G) :
    ∀ᵐ ω ∂reducedLaw Q, ∀ ψ : Vec d → ℝ, IsSpatialTest Set.univ ψ →
      ∀ L : ℂ →L[ℝ] ℝ,
      HasWeakDivergence Set.univ
        (fun x j => ψ x * L (∑ k, (ω.1 x j k : ℂ) * G k (translate x ω)))
        (fun x => ψ x * L (2 * g (translate x ω) -
            2 * ζ * (∑ j, (ω.1 x j i : ℂ) * G j (translate x ω))) +
          dot (fun j => L (∑ k, (ω.1 x j k : ℂ) * G k (translate x ω)))
            (gradient ψ x)) := by
  let F : Fin d → FieldPair d → ℂ := fun j ω => ∑ k, (ω.1 0 j k : ℂ) * G k ω
  let b : FieldPair d → ℂ := fun ω => ∑ j, (ω.1 0 j i : ℂ) * G j ω
  let h : FieldPair d → ℂ := fun ω => 2 * g ω - 2 * ζ * b ω
  have hm (j k : Fin d) : Measurable (fun ω : FieldPair d => (ω.1 0 j k : ℂ)) :=
    (Complex.continuous_ofReal.comp
      (((continuous_eval_const (0 : Vec d)).comp continuous_fst).matrix_elem j k)).measurable
  have hFm (j : Fin d) : Measurable (F j) :=
    Finset.measurable_sum _ fun k _ => (hm j k).mul (Lp.stronglyMeasurable _).measurable
  have hbm : Measurable b :=
    Finset.measurable_sum _ fun j _ => (hm j i).mul (Lp.stronglyMeasurable _).measurable
  have hb : MemLp b 2 (reducedLaw Q) := by
    apply memLp_finset_sum
    intro j _
    exact (Lp.memLp (complexCoefficientMul Q j i (G j))).ae_eq
      (complexCoefficientMul_coe Q j i (G j))
  have hhm : Measurable h :=
    (measurable_const.mul (Lp.stronglyMeasurable g).measurable).sub
      (measurable_const.mul hbm)
  have hh : MemLp h 2 (reducedLaw Q) :=
    ((Lp.memLp g).const_mul 2).sub (hb.const_mul (2 * ζ))
  letI : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  have he := ae_complex_spatial_divergence_all_tests (reducedLaw Q)
    (reducedLaw_stationary Q) F h hFm hhm (memLp_complex_coefficient_flux Q G) hh
    (fun v V hV => hfg.horizontal_flux hG v V hV)
  filter_upwards [he,
    ae_complex_function_orbit_memLp_on_all_compacts (reducedLaw Q)
      (reducedLaw_stationary Q) hhm hh,
    ae_all_iff.mpr fun j => ae_complex_function_orbit_memLp_on_all_compacts
      (reducedLaw Q) (reducedLaw_stationary Q) (hFm j)
        (memLp_complex_coefficient_flux Q G j)] with ω he hhω hFω
  intro ψ hψ L
  have hd := physical_divergence_projection (fun K hK j => hFω j K hK) hhω he L
  have hc := Correctors.hasWeakDivergence_mul_spatialTest hd hψ
  simpa only [F, h, b, translate_matrix, add_zero] using hc


/-- Joint representatives of the actual orbit and gradient satisfy the
localized time-tested PDE. They are chosen before all temporal tests; for
each temporal test the environment event precedes every spatial cutoff.
No pointwise temporal trace or retained-law semigroup is assumed. -/
theorem exists_joint_timeTest_cutoff_divergence {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) (f : Lp ℂ 2 (reducedLaw Q)) :
    ∃ (U : ℝ × FieldPair d → ℂ) (V : Fin d → ℝ × FieldPair d → ℂ),
      Measurable U ∧ (∀ j, Measurable (V j)) ∧
      (∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] P s.toNNReal f) ∧
      (∀ j s, (fun ω => V j (s, ω)) =ᵐ[reducedLaw Q] (hP.gradientOrbit f s) j) ∧
      ∀ (η η' : ℝ → ℝ), (∀ s, HasDerivAt η (η' s) s) → Continuous η' →
        ∀ (t : ℝ≥0), η 0 = 0 → η t = 0 → ∀ᵐ ω ∂reducedLaw Q,
        let X : Vec d → Fin d → ℂ := fun x j =>
          ∫ s in Set.Icc (0 : ℝ) (t : ℝ), (η s : ℂ) * V j (s, translate x ω)
        let q : Vec d → ℂ := fun x =>
          -2 * (∫ s in Set.Icc (0 : ℝ) (t : ℝ), (η' s : ℂ) * U (s, translate x ω)) -
            2 * ζ * (∑ j, (ω.1 x j i : ℂ) * X x j)
        ∀ ψ : Vec d → ℝ, IsSpatialTest Set.univ ψ → ∀ L : ℂ →L[ℝ] ℝ,
          HasWeakDivergence Set.univ
            (fun x j => ψ x * L (∑ k, (ω.1 x j k : ℂ) * X x k))
            (fun x => ψ x * L (q x) +
              dot (fun j => L (∑ k, (ω.1 x j k : ℂ) * X x k)) (gradient ψ x)) := by
  obtain ⟨U, hU, heU, _⟩ := hP.exists_joint_spatial_representative f
  obtain ⟨V, hV, heV⟩ := hP.exists_joint_gradient_representative f
  refine ⟨U, V, hU, hV, heU, heV, ?_⟩
  intro η η' hη hη' t hzero ht
  have hηc : Continuous η := continuous_iff_continuousAt.mpr fun s => (hη s).continuousAt
  have hg := hP.generator_timeTest_allData f η η' hη hη' t hzero ht
  rw [intervalIntegral.integral_of_le (NNReal.coe_nonneg t),
    intervalIntegral.integral_of_le (NNReal.coe_nonneg t),
    ← integral_Icc_eq_integral_Ioc, ← integral_Icc_eq_integral_Ioc] at hg
  let g : Lp ℂ 2 (reducedLaw Q) :=
    ∫ s in Set.Icc (0 : ℝ) (t : ℝ), η' s • P s.toNNReal f
  have hn := ae_complex_spatial_orbit_congr (reducedLaw Q) (reducedLaw_stationary Q)
    (Lp.stronglyMeasurable (-g)).measurable (Lp.stronglyMeasurable g).measurable.neg
    (Lp.coeFn_neg g)
  have hcu := ae_spatial_weighted_integral_joint_l2_representative t
    (integrableOn_comp_toNNReal_Icc _ (hP.2.2.1 f) (t : ℝ)) hU heU η' hη'
  have hcv (j : Fin d) := ae_spatial_weighted_integral_joint_l2_representative t
    ((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)) j).integrable_comp
      (hP.integrableOn_gradientOrbit f t)) (hV j) (heV j) η hηc
  filter_upwards [generatorPair_ae_cutoff_divergence Q hg
      (hP.weighted_integral_orbit_gradient f η hηc t), hn, hcu, ae_all_iff.mpr hcv]
    with ω hw hn hcu hcv
  dsimp only
  intro ψ hψ L
  apply Correctors.hasWeakDivergence_congr_ae isOpen_univ (hw ψ hψ L)
  · rw [Measure.restrict_univ]
    filter_upwards [ae_all_iff.mpr hcv] with x hx
    funext j
    exact congrArg (fun W : Fin d → ℂ =>
      ψ x * L (∑ k, (ω.1 x j k : ℂ) * W k)) (funext hx)
  · rw [Measure.restrict_univ]
    filter_upwards [hn, hcu, ae_all_iff.mpr hcv] with x hn hu hx
    change (-g) (translate x ω) = -g (translate x ω) at hn
    change g (translate x ω) = _ at hu
    have he := hn.trans (congrArg Neg.neg hu)
    have ha := congrArg₂ (fun (z : ℂ) (W : Fin d → ℂ) =>
      ψ x * L (2 * z - 2 * ζ * (∑ j, (ω.1 x j i : ℂ) * W j)) +
        dot (fun j => L (∑ k, (ω.1 x j k : ℂ) * W k)) (gradient ψ x))
      he (funext hx)
    refine ha.trans ?_
    congr 2
    ring



/-- The physical gradient of the actual outer-cutoff function. -/
def cutoffGradient {d : ℕ} (ψ : ℝ) (E : Fin d → ℝ) (u : ℂ)
    (X : Fin d → ℂ) (k : Fin d) : ℂ := (ψ : ℂ) * X k + u * (E k : ℂ)

/-- Divergence correction when the cutoff equation is written with the
retained coefficient acting on the full product-rule gradient. -/
def retainedCutoffFluxSource {d : ℕ} (χ : C(Vec d, ℝ)) (ω : FieldPair d)
    (x : Vec d) (ψ : ℝ) (E : Fin d → ℝ) (u : ℂ) (X : Fin d → ℂ) (j : Fin d) : ℂ :=
  2 * ((ψ : ℂ) * retainedFluxDefect χ ω x X j +
    cutoffFluxSource ((ForcedLocality.retainedPair χ ω).1 x) E u j)

/-- The complete scalar correction, with the actual signed force. -/
def retainedCutoffScalarSource {d : ℕ} (χ : C(Vec d, ℝ)) (ω : FieldPair d)
    (x : Vec d) (ψ : ℝ) (E : Fin d → ℝ) (u : ℂ) (X : Fin d → ℂ)
    (i : Fin d) (ζ : ℂ) : ℂ :=
  2 * (ψ : ℂ) * retainedDriftDefect χ ω x X i ζ -
    2 * ζ * u * (∑ j, ((ForcedLocality.retainedPair χ ω).1 x j i : ℂ) * (E j : ℂ)) -
    ∑ j, (∑ k, (ω.1 x j k : ℂ) * X k) * (E j : ℂ)

private theorem cutoffGradient_contraction {d : ℕ} (A : Fin d → ℝ)
    (ψ : ℝ) (E : Fin d → ℝ) (u : ℂ) (X : Fin d → ℂ) :
    (∑ k, (A k : ℂ) * cutoffGradient ψ E u X k) =
      (ψ : ℂ) * (∑ k, (A k : ℂ) * X k) +
        u * (∑ k, (A k : ℂ) * (E k : ℂ)) := by
  simp only [cutoffGradient, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro k _ <;> ring

/-- The retained cutoff principal flux plus its correction is exactly the
localized original flux, including the derivative of the cutoff. -/
theorem retained_cutoff_flux_eq {d : ℕ} (χ : C(Vec d, ℝ)) (ω : FieldPair d)
    (x : Vec d) (ψ : ℝ) (E : Fin d → ℝ) (u : ℂ) (X : Fin d → ℂ) (j : Fin d) :
    (∑ k, ((ForcedLocality.retainedPair χ ω).1 x j k : ℂ) *
        cutoffGradient ψ E u X k) + retainedCutoffFluxSource χ ω x ψ E u X j =
      (ψ : ℂ) * (∑ k, (ω.1 x j k : ℂ) * X k) := by
  rw [cutoffGradient_contraction]
  simp only [retainedCutoffFluxSource, retainedFluxDefect, cutoffFluxSource,
    Complex.ofReal_sub, sub_mul, Finset.sum_sub_distrib]
  ring

/-- The complete retained scalar source recovers the localized original
source. This is the sign needed for the retained inhomogeneous evolution. -/
theorem retained_cutoff_scalar_eq {d : ℕ} (χ : C(Vec d, ℝ)) (ω : FieldPair d)
    (x : Vec d) (ψ : ℝ) (E : Fin d → ℝ) (u g : ℂ) (X : Fin d → ℂ)
    (i : Fin d) (ζ : ℂ) :
    2 * (ψ : ℂ) * g -
        2 * ζ * (∑ j, ((ForcedLocality.retainedPair χ ω).1 x j i : ℂ) *
          cutoffGradient ψ E u X j) - retainedCutoffScalarSource χ ω x ψ E u X i ζ =
      (ψ : ℂ) * (2 * g - 2 * ζ * (∑ j, (ω.1 x j i : ℂ) * X j)) +
        ∑ j, (∑ k, (ω.1 x j k : ℂ) * X k) * (E j : ℂ) := by
  rw [cutoffGradient_contraction]
  simp only [retainedCutoffScalarSource, retainedDriftDefect,
    Complex.ofReal_sub, sub_mul, Finset.sum_sub_distrib]
  ring

/-- Both complete retained cutoff sources vanish in the retained interior,
where the outer cutoff is constant. -/
theorem retainedCutoffSources_eq_zero {d : ℕ} (χ : C(Vec d, ℝ))
    (ω : FieldPair d) (x : Vec d) (hχ : χ x = 1) (ψ : ℝ)
    (E : Fin d → ℝ) (hE : ∀ j, E j = 0) (u : ℂ) (X : Fin d → ℂ)
    (i : Fin d) (ζ : ℂ) :
    (∀ j, retainedCutoffFluxSource χ ω x ψ E u X j = 0) ∧
      retainedCutoffScalarSource χ ω x ψ E u X i ζ = 0 := by
  obtain ⟨hf, hs⟩ := retainedDefects_eq_zero χ ω hχ X i ζ
  constructor
  · intro j
    simp only [retainedCutoffFluxSource, hf j, cutoffFluxSource, hE,
      Complex.ofReal_zero, mul_zero, Finset.sum_const_zero, add_zero]
  · simp only [retainedCutoffScalarSource, hs, hE, Complex.ofReal_zero,
      mul_zero, Finset.sum_const_zero, sub_zero]


/-- The complete retained cutoff forcing is supported in the physical
Euclidean shell, including both coefficient and outer-cutoff corrections. -/
theorem retainedCutoffSources_annulus {d : ℕ} (χ : C(Vec d, ℝ))
    (ω : FieldPair d) (ψ : Vec d → ℝ) (E : Vec d → Fin d → ℝ)
    (u : Vec d → ℂ) (X : Vec d → Fin d → ℂ) (z : Vec d) (r : ℝ)
    (hχ : ∀ x, euclideanNorm (x - z) < r → χ x = 1)
    (hψ : ∀ x, 2 * r ≤ euclideanNorm (x - z) → ψ x = 0)
    (hE : ∀ x, euclideanNorm (x - z) < r ∨
      2 * r ≤ euclideanNorm (x - z) → ∀ j, E x j = 0)
    (i : Fin d) (ζ : ℂ) (x : Vec d)
    (hx : x ∉ {y : Vec d | r ≤ euclideanNorm (y - z) ∧
      euclideanNorm (y - z) < 2 * r}) :
    (∀ j, retainedCutoffFluxSource χ ω x (ψ x) (E x) (u x) (X x) j = 0) ∧
      retainedCutoffScalarSource χ ω x (ψ x) (E x) (u x) (X x) i ζ = 0 := by
  by_cases hi : euclideanNorm (x - z) < r
  · exact retainedCutoffSources_eq_zero χ ω x (hχ x hi) (ψ x) (E x)
      (hE x (Or.inl hi)) (u x) (X x) i ζ
  · have ho : 2 * r ≤ euclideanNorm (x - z) :=
      not_lt.mp fun ho => hx ⟨le_of_not_gt hi, ho⟩
    have he := hE x (Or.inr ho)
    simp only [retainedCutoffFluxSource, retainedCutoffScalarSource,
      cutoffFluxSource, hψ x ho, he, Complex.ofReal_zero, zero_mul, mul_zero,
      Finset.sum_const_zero, add_zero, sub_zero, implies_true, and_self]

/-- Conversion of a genuine localized divergence equation to the retained
operator with its complete sources. This is pointwise spatial algebra and
does not require a law for the retained coefficient. -/
theorem retained_cutoff_equation_of_divergence {d : ℕ} (χ : C(Vec d, ℝ))
    (ω : FieldPair d) (i : Fin d) (ζ : ℂ)
    (u g : Vec d → ℂ) (X : Vec d → Fin d → ℂ) (ψ : Vec d → ℝ)
    (L : ℂ →L[ℝ] ℝ)
    (hw : HasWeakDivergence Set.univ
      (fun x j => ψ x * L (∑ k, (ω.1 x j k : ℂ) * X x k))
      (fun x => ψ x * L (2 * g x - 2 * ζ * (∑ j, (ω.1 x j i : ℂ) * X x j)) +
        dot (fun j => L (∑ k, (ω.1 x j k : ℂ) * X x k)) (gradient ψ x))) :
    let H : Vec d → Fin d → ℂ := fun x => cutoffGradient (ψ x)
      (fun k => coordinateDerivative k ψ x) (u x) (X x)
    HasWeakDivergence Set.univ
      (fun x j => L ((∑ k, ((ForcedLocality.retainedPair χ ω).1 x j k : ℂ) * H x k) +
        retainedCutoffFluxSource χ ω x (ψ x) (fun k => coordinateDerivative k ψ x)
          (u x) (X x) j))
      (fun x => L (2 * (ψ x : ℂ) * g x -
        2 * ζ * (∑ j, ((ForcedLocality.retainedPair χ ω).1 x j i : ℂ) * H x j) -
        retainedCutoffScalarSource χ ω x (ψ x) (fun k => coordinateDerivative k ψ x)
          (u x) (X x) i ζ)) := by
  have hm (z : ℂ) (r : ℝ) : L ((r : ℂ) * z) = r * L z := by
    rw [← Complex.real_smul, L.map_smul, smul_eq_mul]
  have hn (z : ℂ) (r : ℝ) : L (z * (r : ℂ)) = L z * r := by
    rw [mul_comm, hm, mul_comm]
  apply Correctors.hasWeakDivergence_congr_ae isOpen_univ hw
  · exact Filter.Eventually.of_forall fun x => by
      funext j
      symm
      dsimp only
      rw [retained_cutoff_flux_eq, hm]
  · exact Filter.Eventually.of_forall fun x => by
      symm
      dsimp only
      rw [retained_cutoff_scalar_eq, L.map_add, hm]
      simp only [map_sum, hn, dot, gradient]


/-- The actual cutoff function satisfies the retained-coefficient equation
with the complete explicit divergence and scalar corrections. One environment
event precedes all retained fields, outer cutoffs, and real projections. -/
theorem generatorPair_ae_retained_cutoff_equation {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) {i : Fin d} {ζ : ℂ}
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i ζ f g)
    {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G) :
    ∀ᵐ ω ∂reducedLaw Q, ∀ χ : C(Vec d, ℝ),
      ∀ ψ : Vec d → ℝ, IsSpatialTest Set.univ ψ → ∀ L : ℂ →L[ℝ] ℝ,
      let H : Vec d → Fin d → ℂ := fun x => cutoffGradient (ψ x)
        (fun k => coordinateDerivative k ψ x) (f (translate x ω))
        (fun k => G k (translate x ω))
      HasWeakDivergence Set.univ
        (fun x j => L ((∑ k, ((ForcedLocality.retainedPair χ ω).1 x j k : ℂ) * H x k) +
          retainedCutoffFluxSource χ ω x (ψ x) (fun k => coordinateDerivative k ψ x)
            (f (translate x ω)) (fun k => G k (translate x ω)) j))
        (fun x => L (2 * (ψ x : ℂ) * g (translate x ω) -
          2 * ζ * (∑ j, ((ForcedLocality.retainedPair χ ω).1 x j i : ℂ) * H x j) -
          retainedCutoffScalarSource χ ω x (ψ x) (fun k => coordinateDerivative k ψ x)
            (f (translate x ω)) (fun k => G k (translate x ω)) i ζ)) := by
  filter_upwards [generatorPair_ae_cutoff_divergence Q hfg hG] with ω hw
  intro χ ψ hψ L
  exact retained_cutoff_equation_of_divergence χ ω i ζ
    (fun x => f (translate x ω)) (fun x => g (translate x ω))
    (fun x k => G k (translate x ω)) ψ L (hw ψ hψ L)


/-- The actual joint orbit representatives satisfy the retained-coefficient
cutoff equation after temporal testing. The representatives are chosen before
all temporal tests, and each test has one environment event before all
retained fields, spatial cutoffs and real projections. The time integrals are
literal representatives, without a retained-law semigroup or temporal trace. -/
theorem exists_joint_timeTest_retained_cutoff_equation {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) (f : Lp ℂ 2 (reducedLaw Q)) :
    ∃ (U : ℝ × FieldPair d → ℂ) (V : Fin d → ℝ × FieldPair d → ℂ),
      Measurable U ∧ (∀ j, Measurable (V j)) ∧
      (∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] P s.toNNReal f) ∧
      (∀ j s, (fun ω => V j (s, ω)) =ᵐ[reducedLaw Q] (hP.gradientOrbit f s) j) ∧
      ∀ (η η' : ℝ → ℝ), (∀ s, HasDerivAt η (η' s) s) → Continuous η' →
        ∀ (t : ℝ≥0), η 0 = 0 → η t = 0 → ∀ᵐ ω ∂reducedLaw Q,
        let u : Vec d → ℂ := fun x =>
          ∫ s in Set.Icc (0 : ℝ) (t : ℝ), (η s : ℂ) * U (s, translate x ω)
        let X : Vec d → Fin d → ℂ := fun x j =>
          ∫ s in Set.Icc (0 : ℝ) (t : ℝ), (η s : ℂ) * V j (s, translate x ω)
        let g : Vec d → ℂ := fun x =>
          -(∫ s in Set.Icc (0 : ℝ) (t : ℝ), (η' s : ℂ) * U (s, translate x ω))
        ∀ χ : C(Vec d, ℝ), ∀ ψ : Vec d → ℝ,
          IsSpatialTest Set.univ ψ → ∀ L : ℂ →L[ℝ] ℝ,
          let H : Vec d → Fin d → ℂ := fun x => cutoffGradient (ψ x)
            (fun k => coordinateDerivative k ψ x) (u x) (X x)
          HasWeakDivergence Set.univ
            (fun x j => L ((∑ k, ((ForcedLocality.retainedPair χ ω).1 x j k : ℂ) * H x k) +
              retainedCutoffFluxSource χ ω x (ψ x) (fun k => coordinateDerivative k ψ x)
                (u x) (X x) j))
            (fun x => L (2 * (ψ x : ℂ) * g x -
              2 * ζ * (∑ j, ((ForcedLocality.retainedPair χ ω).1 x j i : ℂ) * H x j) -
              retainedCutoffScalarSource χ ω x (ψ x) (fun k => coordinateDerivative k ψ x)
                (u x) (X x) i ζ)) := by
  obtain ⟨U, V, hU, hV, heU, heV, hw⟩ := exists_joint_timeTest_cutoff_divergence Q hP f
  refine ⟨U, V, hU, hV, heU, heV, ?_⟩
  intro η η' hη hη' t hzero ht
  filter_upwards [hw η η' hη hη' t hzero ht] with ω hω
  dsimp only at hω ⊢
  intro χ ψ hψ L
  apply retained_cutoff_equation_of_divergence χ ω i ζ
  simpa only [mul_neg, neg_mul] using hω ψ hψ L


/-- The literal weighted joint representatives have the actual physical
cutoff H1 graph. Thus the gradient used in temporal retained equations is
the product-rule gradient of the same weighted scalar orbit. The event is
chosen before all spatial cutoffs. -/
theorem ae_joint_timeIntegral_cutoff_h1 {d : ℕ} [Fact (2 ≤ d)] {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) (f : Lp ℂ 2 (reducedLaw Q))
    {U : ℝ × FieldPair d → ℂ} {V : Fin d → ℝ × FieldPair d → ℂ}
    (hU : Measurable U) (hV : ∀ j, Measurable (V j))
    (heU : ∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] P s.toNNReal f)
    (heV : ∀ j s, (fun ω => V j (s, ω)) =ᵐ[reducedLaw Q] (hP.gradientOrbit f s) j)
    (η : ℝ → ℝ) (hη : Continuous η) (t : ℝ≥0) :
    ∀ᵐ ω ∂reducedLaw Q,
      let v : Vec d → ℂ := fun x =>
        ∫ s in Set.Icc (0 : ℝ) (t : ℝ), (η s : ℂ) * U (s, translate x ω)
      let X : Vec d → Fin d → ℂ := fun x j =>
        ∫ s in Set.Icc (0 : ℝ) (t : ℝ), (η s : ℂ) * V j (s, translate x ω)
      ∀ ψ : Vec d → ℝ, IsSpatialTest Set.univ ψ →
        ∃ (u : Lp ℂ 2 (volume : Measure (Vec d)))
          (H : Fin d → Lp ℂ 2 (volume : Measure (Vec d))),
          IsPhysicalH1Graph volume (Or.inl rfl) u H ∧
          (u : Vec d → ℂ) =ᵐ[volume] (fun x => (ψ x : ℂ) * v x) ∧
          (∀ j, (H j : Vec d → ℂ) =ᵐ[volume]
            (fun x => cutoffGradient (ψ x) (fun k => coordinateDerivative k ψ x)
              (v x) (X x) j)) ∧
          (∀ᵐ x ∂volume, x ∉ tsupport ψ → u x = 0 ∧ ∀ j, H j x = 0) := by
  have hcu := ae_spatial_weighted_integral_joint_l2_representative t
    (integrableOn_comp_toNNReal_Icc _ (hP.2.2.1 f) (t : ℝ)) hU heU η hη
  have hcv (j : Fin d) := ae_spatial_weighted_integral_joint_l2_representative t
    ((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)) j).integrable_comp
      (hP.integrableOn_gradientOrbit f t)) (hV j) (heV j) η hη
  filter_upwards [ae_physical_cutoff_h1 Q (hP.weighted_integral_orbit_gradient f η hη t),
    hcu, ae_all_iff.mpr hcv] with ω hw hu hv
  dsimp only
  intro ψ hψ
  obtain ⟨u, H, hH, heu, heH, hz⟩ := hw ψ hψ
  refine ⟨u, H, hH, ?_, ?_, hz⟩
  · filter_upwards [heu, hu] with x hx hxU
    rw [hx, hxU]
  · intro j
    filter_upwards [heH j, hu, hv j] with x hx hxU hxV
    change (∫ s in Set.Icc (0 : ℝ) (t : ℝ),
      η s • (hP.gradientOrbit f s) j) (translate x ω) = _ at hxV
    dsimp only [cutoffGradient]
    rw [hx, hxU, hxV]


/-- The complete retained divergence and scalar corrections are physical L2
forcing. Only local L2 data are needed; compact cutoff factors occur in every
term. Both coefficient multipliers come from actual spatial ellipticity. -/
theorem retainedCutoffSources_memLp {d : ℕ} (χ : C(Vec d, ℝ)) (ω : FieldPair d)
    (A B : ℝ) (hA : 0 < A) (hB : 0 < B)
    (hellA : IsElliptic A ω.1)
    (hellB : IsElliptic B (ForcedLocality.retainedPair χ ω).1)
    {u : Vec d → ℂ} {X : Vec d → Fin d → ℂ}
    (hu : ∀ K : Set (Vec d), IsCompact K → MemLp u 2 (volume.restrict K))
    (hX : ∀ K : Set (Vec d), IsCompact K →
      ∀ j, MemLp (fun x => X x j) 2 (volume.restrict K))
    {ψ : Vec d → ℝ} (hψ : IsSpatialTest Set.univ ψ) (i : Fin d) (ζ : ℂ) :
    (∀ j, MemLp (fun x => retainedCutoffFluxSource χ ω x (ψ x)
      (fun k => coordinateDerivative k ψ x) (u x) (X x) j) 2 volume) ∧
    MemLp (fun x => retainedCutoffScalarSource χ ω x (ψ x)
      (fun k => coordinateDerivative k ψ x) (u x) (X x) i ζ) 2 volume := by
  have ha (j k : Fin d) := memLp_complex_elliptic_entry volume ω.1 A hA hellA
    (fun j k => ω.1.continuous.matrix_elem j k) j k
  have hb (j k : Fin d) := memLp_complex_elliptic_entry volume
    (ForcedLocality.retainedPair χ ω).1 B hB hellB
    (fun j k => (ForcedLocality.retainedPair χ ω).1.continuous.matrix_elem j k) j k
  have hψX (j : Fin d) := memLp_local_mul_cutoff (fun K hK => hX K hK j) hψ
  have hdX (j k : Fin d) := memLp_local_mul_cutoff (fun K hK => hX K hK k)
    (Correctors.isSpatialTest_coordinateDerivative hψ j)
  have hdU (j : Fin d) := memLp_local_mul_cutoff hu
    (Correctors.isSpatialTest_coordinateDerivative hψ j)
  let H : Vec d → Fin d → ℂ := fun x => cutoffGradient (ψ x)
    (fun k => coordinateDerivative k ψ x) (u x) (X x)
  have hH (j : Fin d) : MemLp (fun x => H x j) 2 volume := by
    convert (hψX j).add (hdU j) using 1
    funext x
    dsimp only [H, cutoffGradient, Pi.add_apply]
    ring
  have hF (j : Fin d) : MemLp
      (fun x => (ψ x : ℂ) * (∑ k, (ω.1 x j k : ℂ) * X x k)) 2 volume := by
    convert (memLp_finsetSum (p := 2) (Finset.univ : Finset (Fin d)) fun k _ => (ha j k).mul (hψX k)) using 1
    funext x
    dsimp only [Pi.mul_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hFH (j : Fin d) : MemLp (fun x =>
      ∑ k, ((ForcedLocality.retainedPair χ ω).1 x j k : ℂ) * H x k) 2 volume :=
    memLp_finsetSum (p := 2) (Finset.univ : Finset (Fin d)) fun k _ => (hb j k).mul (hH k)
  have hD : MemLp (fun x => (ψ x : ℂ) *
      (∑ j, (ω.1 x j i : ℂ) * X x j)) 2 volume := by
    convert (memLp_finsetSum (p := 2) (Finset.univ : Finset (Fin d)) fun j _ => (ha j i).mul (hψX j)) using 1
    funext x
    dsimp only [Pi.mul_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hDH : MemLp (fun x =>
      ∑ j, ((ForcedLocality.retainedPair χ ω).1 x j i : ℂ) * H x j) 2 volume :=
    memLp_finsetSum (p := 2) (Finset.univ : Finset (Fin d)) fun j _ => (hb j i).mul (hH j)
  have hC : MemLp (fun x => ∑ j, (∑ k, (ω.1 x j k : ℂ) * X x k) *
      (coordinateDerivative j ψ x : ℂ)) 2 volume := by
    convert (memLp_finsetSum (p := 2) (Finset.univ : Finset (Fin d)) fun j _ => memLp_finsetSum (p := 2) (Finset.univ : Finset (Fin d)) fun k _ =>
      (ha j k).mul (hdX j k)) using 1
    funext x
    dsimp only [Pi.mul_apply]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    ring
  constructor
  · intro j
    convert (hF j).sub (hFH j) using 1
    funext x
    have he := retained_cutoff_flux_eq χ ω x (ψ x)
      (fun k => coordinateDerivative k ψ x) (u x) (X x) j
    dsimp only [H, Pi.sub_apply, Pi.add_apply, Pi.mul_apply]
    linear_combination he
  · convert (hDH.const_mul (-2 * ζ)).sub
      ((hD.const_mul (-2 * ζ)).add hC) using 1
    funext x
    have he := retained_cutoff_scalar_eq χ ω x (ψ x)
      (fun k => coordinateDerivative k ψ x) (u x) 0 (X x) i ζ
    dsimp only [H, Pi.sub_apply, Pi.add_apply, Pi.mul_apply]
    linear_combination -he


/-- The complete retained forcing of the actual weighted joint orbit is
physical L2. One environment event precedes every elliptic retained cutoff
and every spatial test. No global spatial L2 assumption on the original
stationary orbit is made. -/
theorem ae_joint_timeIntegral_retained_sources_memLp
    {d : ℕ} [Fact (2 ≤ d)] {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) (f : Lp ℂ 2 (reducedLaw Q))
    {U : ℝ × FieldPair d → ℂ} {V : Fin d → ℝ × FieldPair d → ℂ}
    (hU : Measurable U) (hV : ∀ j, Measurable (V j))
    (heU : ∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] P s.toNNReal f)
    (heV : ∀ j s, (fun ω => V j (s, ω)) =ᵐ[reducedLaw Q] (hP.gradientOrbit f s) j)
    (η : ℝ → ℝ) (hη : Continuous η) (t : ℝ≥0) :
    ∀ᵐ ω ∂reducedLaw Q,
      let u : Vec d → ℂ := fun x =>
        ∫ s in Set.Icc (0 : ℝ) (t : ℝ), (η s : ℂ) * U (s, translate x ω)
      let X : Vec d → Fin d → ℂ := fun x j =>
        ∫ s in Set.Icc (0 : ℝ) (t : ℝ), (η s : ℂ) * V j (s, translate x ω)
      ∀ (χ : C(Vec d, ℝ)) (A B : ℝ), 0 < A → 0 < B →
        IsElliptic A ω.1 → IsElliptic B (ForcedLocality.retainedPair χ ω).1 →
        ∀ ψ : Vec d → ℝ, IsSpatialTest Set.univ ψ →
        (∀ j, MemLp (fun x => retainedCutoffFluxSource χ ω x (ψ x)
          (fun k => coordinateDerivative k ψ x) (u x) (X x) j) 2 volume) ∧
        MemLp (fun x => retainedCutoffScalarSource χ ω x (ψ x)
          (fun k => coordinateDerivative k ψ x) (u x) (X x) i ζ) 2 volume := by
  have hcu := ae_spatial_weighted_integral_joint_l2_representative t
    (integrableOn_comp_toNNReal_Icc _ (hP.2.2.1 f) (t : ℝ)) hU heU η hη
  have hcv (j : Fin d) := ae_spatial_weighted_integral_joint_l2_representative t
    ((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)) j).integrable_comp
      (hP.integrableOn_gradientOrbit f t)) (hV j) (heV j) η hη
  filter_upwards [(hP.weighted_integral_orbit_gradient f η hη t).ae_reduced_spatial Q,
    hcu, ae_all_iff.mpr hcv] with ω hw hu hv
  dsimp only
  intro χ A B hA hB hellA hellB ψ hψ
  apply retainedCutoffSources_memLp χ ω A B hA hB hellA hellB
    (ψ := ψ) (i := i) (ζ := ζ) (hψ := hψ)
  · intro K hK
    exact (hw.2.2 K hK).1.ae_eq (ae_restrict_of_ae hu)
  · intro K hK j
    have hj := hv j
    change (fun x => (∫ s in Set.Icc (0 : ℝ) (t : ℝ),
      η s • (hP.gradientOrbit f s) j) (translate x ω)) =ᵐ[volume] _ at hj
    exact ((hw.2.2 K hK).2 j).ae_eq (ae_restrict_of_ae hj)


private theorem contraction_mul {d : ℕ} (A X : Fin d → ℂ) (c : ℂ) :
    (∑ k, A k * (c * X k)) = c * ∑ k, A k * X k := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Scalar temporal weights commute with the full retained divergence source. -/
theorem retainedCutoffFluxSource_mul {d : ℕ} (χ : C(Vec d, ℝ)) (ω : FieldPair d)
    (x : Vec d) (ψ : ℝ) (E : Fin d → ℝ) (u : ℂ) (X : Fin d → ℂ)
    (c : ℂ) (j : Fin d) :
    retainedCutoffFluxSource χ ω x ψ E (c * u) (fun k => c * X k) j =
      c * retainedCutoffFluxSource χ ω x ψ E u X j := by
  simp only [retainedCutoffFluxSource, retainedFluxDefect, cutoffFluxSource,
    contraction_mul]
  ring

/-- Scalar temporal weights commute with the complete signed scalar source. -/
theorem retainedCutoffScalarSource_mul {d : ℕ} (χ : C(Vec d, ℝ)) (ω : FieldPair d)
    (x : Vec d) (ψ : ℝ) (E : Fin d → ℝ) (u : ℂ) (X : Fin d → ℂ)
    (c : ℂ) (i : Fin d) (ζ : ℂ) :
    retainedCutoffScalarSource χ ω x ψ E (c * u) (fun k => c * X k) i ζ =
      c * retainedCutoffScalarSource χ ω x ψ E u X i ζ := by
  have he (F : Fin d → ℂ) : (∑ j, (c * F j) * (E j : ℂ)) =
      c * ∑ j, F j * (E j : ℂ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp only [retainedCutoffScalarSource, retainedDriftDefect, contraction_mul, he]
  ring

/-- The complete retained forcing is a genuine integrable temporal source.
Its time integral is the forcing evaluated on the integrated scalar and
gradient. No time derivative or semigroup for the retained law is assumed. -/
theorem integral_retainedCutoffSources {T : Type*} [MeasurableSpace T]
    {μ : Measure T} {d : ℕ} (χ : C(Vec d, ℝ)) (ω : FieldPair d)
    (x : Vec d) (ψ : ℝ) (E : Fin d → ℝ) (i : Fin d) (ζ : ℂ)
    {u : T → ℂ} {X : T → Fin d → ℂ} (hu : Integrable u μ)
    (hX : ∀ k, Integrable (fun s => X s k) μ) :
    (∀ j, Integrable (fun s => retainedCutoffFluxSource χ ω x ψ E (u s) (X s) j) μ) ∧
    Integrable (fun s => retainedCutoffScalarSource χ ω x ψ E (u s) (X s) i ζ) μ ∧
    (∀ j, (∫ s, retainedCutoffFluxSource χ ω x ψ E (u s) (X s) j ∂μ) =
      retainedCutoffFluxSource χ ω x ψ E (∫ s, u s ∂μ)
        (fun k => ∫ s, X s k ∂μ) j) ∧
    (∫ s, retainedCutoffScalarSource χ ω x ψ E (u s) (X s) i ζ ∂μ) =
      retainedCutoffScalarSource χ ω x ψ E (∫ s, u s ∂μ)
        (fun k => ∫ s, X s k ∂μ) i ζ := by
  have hi (A : Fin d → ℂ) : Integrable (fun s => ∑ k, A k * X s k) μ :=
    integrable_finset_sum (Finset.univ : Finset (Fin d)) fun k _ => (hX k).const_mul (A k)
  have he (A : Fin d → ℂ) : (∫ s, ∑ k, A k * X s k ∂μ) =
      ∑ k, A k * (∫ s, X s k ∂μ) := by
    rw [integral_finsetSum]
    · simp only [integral_const_mul]
    · intro k _
      exact (hX k).const_mul (A k)
  have hf (j : Fin d) : Integrable
      (fun s => retainedCutoffFluxSource χ ω x ψ E (u s) (X s) j) μ := by
    exact (((hi _).const_mul (1 / 2 : ℂ)).const_mul (ψ : ℂ) |>.add
      ((hu.const_mul (-(1 / 2 : ℂ))).mul_const _)).const_mul 2
  have hs : Integrable
      (fun s => retainedCutoffScalarSource χ ω x ψ E (u s) (X s) i ζ) μ := by
    exact (((hi _).const_mul ζ).const_mul (2 * (ψ : ℂ)) |>.sub
      ((hu.const_mul (2 * ζ)).mul_const _)).sub
      (integrable_finset_sum (Finset.univ : Finset (Fin d)) fun j _ => (hi _).mul_const (E j : ℂ))
  refine ⟨hf, hs, ?_, ?_⟩
  · intro j
    simp only [retainedCutoffFluxSource, retainedFluxDefect, cutoffFluxSource]
    rw [integral_const_mul, integral_add
      (((hi _).const_mul (1 / 2 : ℂ)).const_mul (ψ : ℂ))
      ((hu.const_mul (-(1 / 2 : ℂ))).mul_const _)]
    simp only [integral_const_mul, integral_mul_const, he]
  · simp only [retainedCutoffScalarSource, retainedDriftDefect]
    erw [integral_sub
      ((((hi _).const_mul ζ).const_mul (2 * (ψ : ℂ))).sub
        ((hu.const_mul (2 * ζ)).mul_const _))
      (integrable_finset_sum (Finset.univ : Finset (Fin d)) fun j _ => (hi _).mul_const (E j : ℂ)),
      integral_sub (((hi _).const_mul ζ).const_mul (2 * (ψ : ℂ)))
        ((hu.const_mul (2 * ζ)).mul_const _),
      integral_finsetSum (Finset.univ : Finset (Fin d)) (fun j _ => (hi _).mul_const (E j : ℂ))]
    simp only [integral_const_mul, integral_mul_const, he]


/-- For actual jointly measurable orbit and gradient representatives, the
instantaneous retained forcing commutes with temporal integration. One
environment event, then one spatial event on the whole space, precedes all
continuous temporal weights and all retained fields and cutoff data. -/
theorem ae_joint_retained_sources_timeIntegral {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) (f : Lp ℂ 2 (reducedLaw Q))
    {U : ℝ × FieldPair d → ℂ} {V : Fin d → ℝ × FieldPair d → ℂ}
    (hU : Measurable U) (hV : ∀ j, Measurable (V j))
    (heU : ∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] P s.toNNReal f)
    (heV : ∀ j s, (fun ω => V j (s, ω)) =ᵐ[reducedLaw Q] (hP.gradientOrbit f s) j)
    (t : ℝ≥0) :
    ∀ᵐ ω ∂reducedLaw Q, ∀ᵐ x ∂(volume : Measure (Vec d)), ∀ η : ℝ → ℝ, Continuous η →
      ∀ (χ : C(Vec d, ℝ)) (ψ : ℝ) (E : Fin d → ℝ),
      let u : ℝ → ℂ := fun s => (η s : ℂ) * U (s, translate x ω)
      let X : ℝ → Fin d → ℂ := fun s j => (η s : ℂ) * V j (s, translate x ω)
      (∀ j, IntegrableOn (fun s => (η s : ℂ) * retainedCutoffFluxSource χ ω x ψ E
        (U (s, translate x ω)) (fun k => V k (s, translate x ω)) j)
        (Set.Icc (0 : ℝ) (t : ℝ))) ∧
      IntegrableOn (fun s => (η s : ℂ) * retainedCutoffScalarSource χ ω x ψ E
        (U (s, translate x ω)) (fun k => V k (s, translate x ω)) i ζ)
        (Set.Icc (0 : ℝ) (t : ℝ)) ∧
      (∀ j, (∫ s in Set.Icc (0 : ℝ) (t : ℝ),
        (η s : ℂ) * retainedCutoffFluxSource χ ω x ψ E
          (U (s, translate x ω)) (fun k => V k (s, translate x ω)) j) =
        retainedCutoffFluxSource χ ω x ψ E
          (∫ s in Set.Icc (0 : ℝ) (t : ℝ), u s)
          (fun k => ∫ s in Set.Icc (0 : ℝ) (t : ℝ), X s k) j) ∧
      (∫ s in Set.Icc (0 : ℝ) (t : ℝ),
        (η s : ℂ) * retainedCutoffScalarSource χ ω x ψ E
          (U (s, translate x ω)) (fun k => V k (s, translate x ω)) i ζ) =
        retainedCutoffScalarSource χ ω x ψ E
          (∫ s in Set.Icc (0 : ℝ) (t : ℝ), u s)
          (fun k => ∫ s in Set.Icc (0 : ℝ) (t : ℝ), X s k) i ζ := by
  letI : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  have hlu := ae_locally_integrable_joint_spatial_translate
    (reducedLaw Q) (reducedLaw_stationary Q)
    (integrable_joint_l2_representative
      (integrableOn_comp_toNNReal_Icc _ (hP.2.2.1 f) (t : ℝ)) hU heU)
  have hlv (j : Fin d) := ae_locally_integrable_joint_spatial_translate
    (reducedLaw Q) (reducedLaw_stationary Q)
    (integrable_joint_l2_representative
      ((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)) j).integrable_comp
        (hP.integrableOn_gradientOrbit f t)) (hV j) (heV j))
  filter_upwards [hlu, ae_all_iff.mpr hlv] with ω hu hv
  have hx : ∀ᵐ x ∂(volume : Measure (Vec d)),
      IntegrableOn (fun s => U (s, translate x ω)) (Set.Icc (0 : ℝ) (t : ℝ)) ∧
      ∀ j, IntegrableOn (fun s => V j (s, translate x ω))
        (Set.Icc (0 : ℝ) (t : ℝ)) := by
    have hn (n : ℕ) : ∀ᵐ x ∂volume.restrict (Metric.closedBall (0 : Vec d) (n : ℝ)),
        IntegrableOn (fun s => U (s, translate x ω)) (Set.Icc (0 : ℝ) (t : ℝ)) ∧
        ∀ j, IntegrableOn (fun s => V j (s, translate x ω))
          (Set.Icc (0 : ℝ) (t : ℝ)) := by
      filter_upwards [(hu _ (isCompact_closedBall _ _)).prod_right_ae,
        ae_all_iff.mpr (fun j => (hv j _ (isCompact_closedBall _ _)).prod_right_ae)]
        with x hux hvx
      exact ⟨hux, hvx⟩
    have hh := (ae_restrict_iUnion_iff
      (fun n : ℕ => Metric.closedBall (0 : Vec d) (n : ℝ)) _).mpr hn
    simpa only [Metric.iUnion_closedBall_nat, Measure.restrict_univ] using hh
  filter_upwards [hx] with x hxx
  rcases hxx with ⟨hux, hvx⟩
  intro η hη χ ψ E
  have huη : IntegrableOn (fun s => (η s : ℂ) * U (s, translate x ω))
      (Set.Icc (0 : ℝ) (t : ℝ)) := by
    simpa only [Complex.coe_smul, Complex.real_smul, smul_eq_mul] using!
      (show IntegrableOn _ (Set.Icc (0 : ℝ) (t : ℝ)) from hux).continuousOn_smul
        hη.continuousOn isCompact_Icc
  have hvη (j : Fin d) : IntegrableOn (fun s => (η s : ℂ) * V j (s, translate x ω))
      (Set.Icc (0 : ℝ) (t : ℝ)) := by
    simpa only [Complex.coe_smul, Complex.real_smul, smul_eq_mul] using!
      (show IntegrableOn _ (Set.Icc (0 : ℝ) (t : ℝ)) from hvx j).continuousOn_smul
        hη.continuousOn isCompact_Icc
  simpa only [IntegrableOn, retainedCutoffFluxSource_mul, retainedCutoffScalarSource_mul] using!
    integral_retainedCutoffSources χ ω x ψ E i ζ huη hvη


/-- The actual retained cutoff equation with literal instantaneous forcing.
The same joint orbit and gradient representatives are chosen before the
weights. The divergence and scalar sources here are temporal integrals of
the instantaneous complete cutoff sources, rather than formal replacements
of their scalar and gradient arguments by temporal integrals. -/
theorem exists_joint_retained_forced_weak_time_equation {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) (f : Lp ℂ 2 (reducedLaw Q)) :
    ∃ (U : ℝ × FieldPair d → ℂ) (V : Fin d → ℝ × FieldPair d → ℂ),
      Measurable U ∧ (∀ j, Measurable (V j)) ∧
      (∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] P s.toNNReal f) ∧
      (∀ j s, (fun ω => V j (s, ω)) =ᵐ[reducedLaw Q] (hP.gradientOrbit f s) j) ∧
      ∀ (η η' : ℝ → ℝ), (∀ s, HasDerivAt η (η' s) s) → Continuous η' →
        ∀ (t : ℝ≥0), η 0 = 0 → η t = 0 → ∀ᵐ ω ∂reducedLaw Q,
        let u : Vec d → ℂ := fun x =>
          ∫ s in Set.Icc (0 : ℝ) (t : ℝ), (η s : ℂ) * U (s, translate x ω)
        let X : Vec d → Fin d → ℂ := fun x j =>
          ∫ s in Set.Icc (0 : ℝ) (t : ℝ), (η s : ℂ) * V j (s, translate x ω)
        let g : Vec d → ℂ := fun x =>
          -(∫ s in Set.Icc (0 : ℝ) (t : ℝ), (η' s : ℂ) * U (s, translate x ω))
        ∀ χ : C(Vec d, ℝ), ∀ ψ : Vec d → ℝ,
          IsSpatialTest Set.univ ψ → ∀ L : ℂ →L[ℝ] ℝ,
          let H : Vec d → Fin d → ℂ := fun x => cutoffGradient (ψ x)
            (fun k => coordinateDerivative k ψ x) (u x) (X x)
          let R : Vec d → Fin d → ℂ := fun x j =>
            ∫ s in Set.Icc (0 : ℝ) (t : ℝ), (η s : ℂ) *
              retainedCutoffFluxSource χ ω x (ψ x) (fun k => coordinateDerivative k ψ x)
                (U (s, translate x ω)) (fun k => V k (s, translate x ω)) j
          let S : Vec d → ℂ := fun x =>
            ∫ s in Set.Icc (0 : ℝ) (t : ℝ), (η s : ℂ) *
              retainedCutoffScalarSource χ ω x (ψ x) (fun k => coordinateDerivative k ψ x)
                (U (s, translate x ω)) (fun k => V k (s, translate x ω)) i ζ
          HasWeakDivergence Set.univ
            (fun x j => L ((∑ k, ((ForcedLocality.retainedPair χ ω).1 x j k : ℂ) * H x k) +
              R x j))
            (fun x => L (2 * (ψ x : ℂ) * g x -
              2 * ζ * (∑ j, ((ForcedLocality.retainedPair χ ω).1 x j i : ℂ) * H x j) -
              S x)) := by
  obtain ⟨U, V, hU, hV, heU, heV, hw⟩ :=
    exists_joint_timeTest_retained_cutoff_equation Q hP f
  refine ⟨U, V, hU, hV, heU, heV, ?_⟩
  intro η η' hη hη' t hzero ht
  have hηc : Continuous η := continuous_iff_continuousAt.mpr fun s => (hη s).continuousAt
  filter_upwards [hw η η' hη hη' t hzero ht,
    ae_joint_retained_sources_timeIntegral Q hP f hU hV heU heV t] with ω hω hc
  dsimp only at hω ⊢
  intro χ ψ hψ L
  apply Correctors.hasWeakDivergence_congr_ae isOpen_univ (hω χ ψ hψ L)
  · filter_upwards [ae_restrict_of_ae hc] with x hx
    funext j
    erw [(hx η hηc χ (ψ x) (fun k => coordinateDerivative k ψ x)).2.2.1 j]
  · filter_upwards [ae_restrict_of_ae hc] with x hx
    erw [(hx η hηc χ (ψ x) (fun k => coordinateDerivative k ψ x)).2.2.2]


end
end EinsteinFull.C9ShortTimeLocality
