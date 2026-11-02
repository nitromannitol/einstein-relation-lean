import EinsteinFull.Calculus.ComplexHorizontalClosedGraphSupport
import EinsteinFull.Calculus.ComplexHorizontalIntegrationSupport
import EinsteinFull.Frozen.ReducedLawStationary
import EinsteinFull.Frozen.ReducedLawProbability
import EinsteinFull.Frozen.ComplexGeneratorGraph
import EinsteinRelation.Correctors.CommonScalarOrbitTests
import EinsteinRelation.Correctors.ScalarOrbitLocalL2
import EinsteinRelation.Calculus.WeakRepresentativeOperations

/-!
# Literal spatial realizations of complex horizontal gradients

The real scalar blueprint supplies Fubini and the countable dense test argument.
Real linear projections commute with translations and their strong derivatives.
All spatial representatives below are the literal translated L2 representatives.
-/

open MeasureTheory Filter
open scoped Topology

noncomputable section
namespace EinsteinFull
open EinsteinRelation EinsteinRelation.Correctors

/-- Real linear scalar projections commute with stationary complex translation. -/
theorem scalarProjection_complexTranslation {d : ℕ} (Q : Measure (FieldPair d))
    (hQ : IsStationary Q) (L : ℂ →L[ℝ] ℝ) (x : Vec d) (f : Lp ℂ 2 Q) :
    L.compLpL 2 Q (complexTranslation Q hQ x f) =
      translationLp Q hQ x (L.compLpL 2 Q f) := by
  apply Lp.ext
  have hc := (measurePreserving_translate Q hQ x).quasiMeasurePreserving.ae
    (L.coeFn_compLpL f)
  filter_upwards [L.coeFn_compLpL (complexTranslation Q hQ x f),
    coeFn_complexTranslation Q hQ x f,
    coeFn_translationLp Q hQ x (L.compLpL 2 Q f), hc] with ω ha hb hd he
  change (L.compLpL 2 Q f) (translate x ω) = L (f (translate x ω)) at he
  rw [ha, hb, hd, he]

/-- Projection of the actual complex generator is the actual real generator. -/
theorem HasComplexHorizontalDerivative.scalarProjection {d : ℕ}
    {Q : Measure (FieldPair d)} {hQ : IsStationary Q} {i : Fin d}
    {f g : Lp ℂ 2 Q} (h : HasComplexHorizontalDerivative Q hQ i f g)
    (L : ℂ →L[ℝ] ℝ) :
    HasHorizontalLpDerivative Q hQ i (L.compLpL 2 Q f) (L.compLpL 2 Q g) := by
  have ht := ((L.compLpL 2 Q).continuous.tendsto g).comp h
  change Tendsto (fun t : ℝ => L.compLpL 2 Q ((t : ℂ)⁻¹ •
    (complexTranslation Q hQ (t • unitVector i) f - f))) _ _ at ht
  simp only [← Complex.ofReal_inv, Complex.coe_smul] at ht
  change Tendsto (fun t : ℝ => L.compLpL 2 Q (t⁻¹ •
    (complexTranslation Q hQ (t • unitVector i) f - f))) _ _ at ht
  simp only [map_smul, map_sub, scalarProjection_complexTranslation] at ht
  exact ht

/-- A measurable equality in the environment law holds along almost every
spatial orbit on one full-measure event. -/
theorem ae_spatial_orbit_congr {d : ℕ} (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    {a b : FieldPair d → ℝ} (ha : Measurable a) (hb : Measurable b)
    (hab : a =ᵐ[Q] b) :
    ∀ᵐ ω ∂Q, ∀ᵐ x ∂(volume : Measure (Vec d)),
      a (translate x ω) = b (translate x ω) := by
  apply (Measure.ae_ae_comm ?_).mp
    (ae_of_all _ fun x => (measurePreserving_translate Q hQ x).quasiMeasurePreserving.ae hab)
  exact measurableSet_eq_fun (ha.comp Probability.continuous_translate.measurable)
    (hb.comp Probability.continuous_translate.measurable)

/-- Real strong horizontal gradients realize spatial weak gradients with all
compact tests simultaneously and locally square integrable representatives. -/
theorem ae_realHorizontalGradient_spatial {d : ℕ} [Fact (2 ≤ d)]
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    (f : Lp ℝ 2 Q) (G : Fin d → Lp ℝ 2 Q)
    (hG : ∀ j, HasHorizontalLpDerivative Q hQ j f (G j)) :
    ∀ᵐ ω ∂Q, HasWeakGradient Set.univ (fun x => f (translate x ω))
      (fun x j => G j (translate x ω)) ∧
      (∀ K : Set (Vec d), IsCompact K →
        MemLp (fun x => f (translate x ω)) 2 (volume.restrict K) ∧
        ∀ j, MemLp (fun x => G j (translate x ω)) 2 (volume.restrict K)) := by
  let v : horizontalH1 Q hQ := ⟨f, G, hG⟩
  have hid : horizontalH1Gradient Q hQ v = G :=
    horizontalH1Gradient_eq_of_hasHorizontalLpDerivative Q hQ v G hG
  have hw (j : Fin d) : ∀ᵐ ω ∂Q, HasWeakPartialDerivative Set.univ j
      (fun x => f (translate x ω)) (fun x => G j (translate x ω)) := by
    apply SpatialScalar.ae_hasWeakPartialDerivative_of_ae_fixedTest Q _ _ j
    · filter_upwards [ae_scalar_orbit_memLp_on_all_compacts Q hQ f,
        ae_scalar_orbit_memLp_on_all_compacts Q hQ (G j)] with ω hf hg
      exact fun K hK => ⟨hf K hK, hg K hK⟩
    · intro ψ
      simpa only [hid] using ae_horizontalH1_orbit_weak_test Q hQ v j ψ
  filter_upwards [ae_all_iff.mpr hw, ae_scalar_orbit_memLp_on_all_compacts Q hQ f,
    ae_all_iff.mpr (fun j => ae_scalar_orbit_memLp_on_all_compacts Q hQ (G j))]
      with ω hw hf hg
  exact ⟨hw, fun K hK => ⟨hf K hK, fun j => hg j K hK⟩⟩

/-- Every real scalar projection of an actual complex horizontal gradient has
its literal orbit as a locally H1 spatial realization, on one event for all tests. -/
theorem HasComplexHorizontalGradient.ae_scalarProjection_spatial {d : ℕ}
    [Fact (2 ≤ d)] {Q : Measure (FieldPair d)} [IsProbabilityMeasure Q]
    {hQ : IsStationary Q} {f : Lp ℂ 2 Q} {G : Fin d → Lp ℂ 2 Q}
    (hG : HasComplexHorizontalGradient Q hQ f G) (L : ℂ →L[ℝ] ℝ) :
    ∀ᵐ ω ∂Q, HasWeakGradient Set.univ (fun x => L (f (translate x ω)))
      (fun x j => L (G j (translate x ω))) ∧
      (∀ K : Set (Vec d), IsCompact K →
        MemLp (fun x => L (f (translate x ω))) 2 (volume.restrict K) ∧
        ∀ j, MemLp (fun x => L (G j (translate x ω))) 2 (volume.restrict K)) := by
  have hf := ae_spatial_orbit_congr Q hQ
    (Lp.stronglyMeasurable (L.compLpL 2 Q f)).measurable
    (L.continuous.measurable.comp (Lp.stronglyMeasurable f).measurable)
    (L.coeFn_compLpL f)
  have hg (j : Fin d) := ae_spatial_orbit_congr Q hQ
    (Lp.stronglyMeasurable (L.compLpL 2 Q (G j))).measurable
    (L.continuous.measurable.comp (Lp.stronglyMeasurable (G j)).measurable)
    (L.coeFn_compLpL (G j))
  filter_upwards [ae_realHorizontalGradient_spatial Q hQ (L.compLpL 2 Q f)
    (fun j => L.compLpL 2 Q (G j)) (fun j => (hG j).scalarProjection L),
    hf, ae_all_iff.mpr hg] with ω hw hf hg
  refine ⟨fun j => (hw.1 j).congr_ae ?_ ?_, fun K hK => ⟨?_, fun j => ?_⟩⟩
  · simpa only [Measure.restrict_univ] using! hf
  · simpa only [Measure.restrict_univ] using! hg j
  · exact (hw.2 K hK).1.ae_eq (hf.filter_mono (ae_mono Measure.restrict_le_self))
  · exact (hw.2 K hK).2 j |>.ae_eq ((hg j).filter_mono (ae_mono Measure.restrict_le_self))

/-- One common event realizes the literal complex orbit in local H1, with the
actual coordinate gradients and no choice of spatial representative. -/
theorem HasComplexHorizontalGradient.ae_spatial {d : ℕ} [Fact (2 ≤ d)]
    {Q : Measure (FieldPair d)} [IsProbabilityMeasure Q] {hQ : IsStationary Q}
    {f : Lp ℂ 2 Q} {G : Fin d → Lp ℂ 2 Q}
    (hG : HasComplexHorizontalGradient Q hQ f G) :
    ∀ᵐ ω ∂Q,
      HasWeakGradient Set.univ (fun x => (f (translate x ω)).re)
        (fun x j => (G j (translate x ω)).re) ∧
      HasWeakGradient Set.univ (fun x => (f (translate x ω)).im)
        (fun x j => (G j (translate x ω)).im) ∧
      ∀ K : Set (Vec d), IsCompact K →
        MemLp (fun x => f (translate x ω)) 2 (volume.restrict K) ∧
        ∀ j, MemLp (fun x => G j (translate x ω)) 2 (volume.restrict K) := by
  filter_upwards [hG.ae_scalarProjection_spatial Complex.reCLM,
    hG.ae_scalarProjection_spatial Complex.imCLM] with ω hre him
  refine ⟨hre.1, him.1, fun K hK => ⟨?_, fun j => ?_⟩⟩
  · exact memLp_re_im_iff.mp ⟨(hre.2 K hK).1, (him.2 K hK).1⟩
  · exact memLp_re_im_iff.mp ⟨(hre.2 K hK).2 j, (him.2 K hK).2 j⟩

/-- The preceding common realization applies to the actual joint reduced law. -/
theorem HasComplexHorizontalGradient.ae_reduced_spatial {d : ℕ} [Fact (2 ≤ d)]
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    {f : Lp ℂ 2 (reducedLaw Q)} {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G) :
    ∀ᵐ ω ∂reducedLaw Q,
      HasWeakGradient Set.univ (fun x => (f (translate x ω)).re)
        (fun x j => (G j (translate x ω)).re) ∧
      HasWeakGradient Set.univ (fun x => (f (translate x ω)).im)
        (fun x j => (G j (translate x ω)).im) ∧
      ∀ K : Set (Vec d), IsCompact K →
        MemLp (fun x => f (translate x ω)) 2 (volume.restrict K) ∧
        ∀ j, MemLp (fun x => G j (translate x ω)) 2 (volume.restrict K) :=
by
  letI : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  exact hG.ae_spatial

/-- The literal complex compact-test identity has the Lebesgue integration by
parts sign; its event is shared by all coordinates and all tests. -/
theorem HasComplexHorizontalGradient.ae_spatial_test {d : ℕ} [Fact (2 ≤ d)]
    {Q : Measure (FieldPair d)} [IsProbabilityMeasure Q] {hQ : IsStationary Q}
    {f : Lp ℂ 2 Q} {G : Fin d → Lp ℂ 2 Q}
    (hG : HasComplexHorizontalGradient Q hQ f G) :
    ∀ᵐ ω ∂Q, ∀ j : Fin d, ∀ φ : Vec d → ℝ, IsSpatialTest Set.univ φ →
      (∫ x, f (translate x ω) * (coordinateDerivative j φ x : ℂ)) =
        -(∫ x, G j (translate x ω) * (φ x : ℂ)) := by
  filter_upwards [hG.ae_spatial] with ω hω
  intro j φ hφ
  have hd : Continuous (coordinateDerivative j φ) :=
    (hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdc : HasCompactSupport (coordinateDerivative j φ) :=
    hφ.2.1.fderiv_apply ℝ (unitVector j)
  have hi (u : Vec d → ℂ)
      (hu : ∀ K : Set (Vec d), IsCompact K → MemLp u 2 (volume.restrict K))
      (a : Vec d → ℝ) (ha : Continuous a) (hac : HasCompactSupport a) :
      Integrable (fun x => u x * (a x : ℂ)) volume := by
    have hl : LocallyIntegrable u volume := by
      rw [locallyIntegrable_iff]
      intro K hK
      letI : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_ne_top
      exact (hu K hK).integrable (by norm_num)
    simpa only [Complex.real_smul, mul_comm] using
      hl.integrable_smul_left_of_hasCompactSupport ha hac
  have hf := hi _ (fun K hK => (hω.2.2 K hK).1) _ hd hdc
  have hg := hi _ (fun K hK => (hω.2.2 K hK).2 j) _ hφ.1.continuous hφ.2.1
  apply Complex.ext
  · rw [Complex.neg_re]
    change (@RCLike.re ℂ _ _) = -(@RCLike.re ℂ _ _)
    rw [← integral_re hf, ← integral_re hg]
    simp only [RCLike.re_to_complex]
    simpa only [Measure.restrict_univ, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero] using (hω.1 j).2.2 φ hφ
  · rw [Complex.neg_im]
    change (@RCLike.im ℂ _ _) = -(@RCLike.im ℂ _ _)
    rw [← integral_im hf, ← integral_im hg]
    simp only [RCLike.im_to_complex]
    simpa only [Measure.restrict_univ, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, zero_add] using (hω.2.1 j).2.2 φ hφ

/-- Local H1 realization controls the actual sum of squared Euclidean gradient
coordinates, without using the supremum norm on the coordinate carrier. -/
theorem HasComplexHorizontalGradient.ae_spatial_gradient_energy {d : ℕ} [Fact (2 ≤ d)]
    {Q : Measure (FieldPair d)} [IsProbabilityMeasure Q] {hQ : IsStationary Q}
    {f : Lp ℂ 2 Q} {G : Fin d → Lp ℂ 2 Q}
    (hG : HasComplexHorizontalGradient Q hQ f G) :
    ∀ᵐ ω ∂Q, ∀ K : Set (Vec d), IsCompact K →
      IntegrableOn (fun x => ∑ j, ‖G j (translate x ω)‖ ^ 2) K volume := by
  filter_upwards [hG.ae_spatial] with ω hω
  intro K hK
  exact integrable_finset_sum _ fun j _ =>
    (memLp_two_iff_integrable_sq_norm ((hω.2.2 K hK).2 j).aestronglyMeasurable).mp
      ((hω.2.2 K hK).2 j)

/-- Literal orbits of arbitrary complex L2 fields are locally L2 on a common
event for every compact set; no derivative assumption is needed. -/
theorem ae_complex_orbit_memLp_on_all_compacts {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    (f : Lp ℂ 2 Q) :
    ∀ᵐ ω ∂Q, ∀ K : Set (Vec d), IsCompact K →
      MemLp (fun x => f (translate x ω)) 2 (volume.restrict K) := by
  have hp (L : ℂ →L[ℝ] ℝ) : ∀ᵐ ω ∂Q, ∀ K : Set (Vec d), IsCompact K →
      MemLp (fun x => L (f (translate x ω))) 2 (volume.restrict K) := by
    have he := ae_spatial_orbit_congr Q hQ
      (Lp.stronglyMeasurable (L.compLpL 2 Q f)).measurable
      (L.continuous.measurable.comp (Lp.stronglyMeasurable f).measurable)
      (L.coeFn_compLpL f)
    filter_upwards [ae_scalar_orbit_memLp_on_all_compacts Q hQ (L.compLpL 2 Q f), he]
      with ω hω he
    exact fun K hK => (hω K hK).ae_eq
      (he.filter_mono (ae_mono Measure.restrict_le_self))
  filter_upwards [hp Complex.reCLM, hp Complex.imCLM] with ω hr hi
  exact fun K hK => memLp_re_im_iff.mp ⟨hr K hK, hi K hK⟩

/-- An actual complete stationary generator pair supplies the physical value,
source and weak gradient on one event. This asserts spatial H1 regularity only;
the distributional divergence equation is a separate obligation. -/
theorem IsComplexGeneratorPair.exists_ae_spatial_gradient {d : ℕ} [Fact (2 ≤ d)]
    {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i ζ f g) :
    ∃ G : Fin d → Lp ℂ 2 (reducedLaw Q),
      HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G ∧
      ∀ᵐ ω ∂reducedLaw Q,
        HasWeakGradient Set.univ (fun x => (f (translate x ω)).re)
          (fun x j => (G j (translate x ω)).re) ∧
        HasWeakGradient Set.univ (fun x => (f (translate x ω)).im)
          (fun x j => (G j (translate x ω)).im) ∧
        ∀ K : Set (Vec d), IsCompact K →
          MemLp (fun x => f (translate x ω)) 2 (volume.restrict K) ∧
          MemLp (fun x => g (translate x ω)) 2 (volume.restrict K) ∧
          ∀ j, MemLp (fun x => G j (translate x ω)) 2 (volume.restrict K) := by
  letI : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  obtain ⟨G, hG, _⟩ := hfg
  refine ⟨G, hG, ?_⟩
  filter_upwards [hG.ae_spatial,
    ae_complex_orbit_memLp_on_all_compacts (reducedLaw Q) (reducedLaw_stationary Q) g]
      with ω hω hg
  exact ⟨hω.1, hω.2.1, fun K hK =>
    ⟨(hω.2.2 K hK).1, hg K hK, (hω.2.2 K hK).2⟩⟩

end EinsteinFull
