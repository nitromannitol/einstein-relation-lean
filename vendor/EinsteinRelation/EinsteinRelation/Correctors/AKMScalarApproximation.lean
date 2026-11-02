import EinsteinRelation.Correctors.AKMScalarApproximationPullback
import EinsteinRelation.Calculus.SpatialPropertyPushforward

/-!
# Scalar Sobolev approximation on the raw AKM coefficient law

Source: `paper/main.tex:693-702`. Transfer the actual coefficient-factored
scalar approximants through measurable spatial events. All weak tests and
all compact spatial regions hold on one common event on the raw law.
-/

open MeasureTheory Filter Topology
noncomputable section
namespace EinsteinRelation.Correctors
open Environment.AKMTestIntegralSupport ReductionImageV3

/-- The raw coefficient carrier admits actual scalar Sobolev approximants
to a jointly measurable, canonically identified gradient. -/
theorem exists_akm_scalar_gradient_approximation {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (i : Fin d) :
    ∃ u : ℕ → Coefficient d (AKMUpperEllipticity L) → Vec d → ℝ,
    ∃ g : ℕ → Coefficient d (AKMUpperEllipticity L) → Vec d → EuclideanSpace ℝ (Fin d),
    ∃ G : Coefficient d (AKMUpperEllipticity L) → Vec d → EuclideanSpace ℝ (Fin d),
      (∀ n, Measurable (fun p : Coefficient d (AKMUpperEllipticity L) × Vec d => u n p.1 p.2) ∧
        Measurable (fun p : Coefficient d (AKMUpperEllipticity L) × Vec d => g n p.1 p.2)) ∧
      Measurable (fun p : Coefficient d (AKMUpperEllipticity L) × Vec d => G p.1 p.2) ∧
      (∀ᵐ a ∂actualCoefficientLaw Q,
        (∀ n, HasWeakGradient Set.univ (u n a) (fun x => (g n a x).ofLp)) ∧
        (∀ n (K : Set (Vec d)), IsCompact K →
          MemLp (u n a) 2 (volume.restrict K) ∧ MemLp (g n a) 2 (volume.restrict K)) ∧
        (∀ K : Set (Vec d), IsCompact K → MemLp (G a) 2 (volume.restrict K)) ∧
        ∀ K : Set (Vec d), IsCompact K → Tendsto
          (fun n => ∫ x in K, ‖g n a x - G a x‖ ^ 2) atTop (𝓝 0)) ∧
      ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ x ∂(volume : Measure (Vec d)),
        G (project (r₀ := r₀) Q.ellipticity_parameter ω) x =
          (canonicalCorrectorGradient Q i :
            Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
              (translate x (reduce ω.1)) := by
  obtain ⟨u, g, G, hm, hG, hsource⟩ := exists_akm_scalar_approximation_pullback Q i
  let π := project (d := d) (r₀ := r₀) Q.ellipticity_parameter
  have hπ := measurable_project (d := d) (r₀ := r₀) Q.ellipticity_parameter
  have hu (n : ℕ) : ∀ᵐ a ∂actualCoefficientLaw Q, ∀ K : Set (Vec d), IsCompact K →
      MemLp (u n a) 2 (volume.restrict K) :=
    ae_local_square_integrable_of_pullback (physicalReferenceLaw Q) π hπ (u n) (hm n).1
      (hsource.mono fun ω hω K hK => (hω.2.1 n K hK).1)
  have hg (n : ℕ) : ∀ᵐ a ∂actualCoefficientLaw Q, ∀ K : Set (Vec d), IsCompact K →
      MemLp (g n a) 2 (volume.restrict K) :=
    ae_local_square_integrable_of_pullback (physicalReferenceLaw Q) π hπ (g n) (hm n).2
      (hsource.mono fun ω hω K hK => (hω.2.1 n K hK).2)
  have hGG : ∀ᵐ a ∂actualCoefficientLaw Q, ∀ K : Set (Vec d), IsCompact K →
      MemLp (G a) 2 (volume.restrict K) :=
    ae_local_square_integrable_of_pullback (physicalReferenceLaw Q) π hπ G hG
      (hsource.mono fun ω hω => hω.2.2.1)
  let J := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).toContinuousLinearMap
  have hw (n : ℕ) : ∀ᵐ a ∂actualCoefficientLaw Q,
      HasWeakGradient Set.univ (u n a) (fun x => (g n a x).ofLp) := by
    apply ae_spatial_weakGradient_of_pullback (physicalReferenceLaw Q) π hπ (u n)
      (fun a x => (g n a x).ofLp) (hm n).1 (J.continuous.measurable.comp (hm n).2)
    · exact hsource.mono fun ω hω K hK =>
        ⟨(hω.2.1 n K hK).1, J.comp_memLp' (hω.2.1 n K hK).2⟩
    · exact hsource.mono fun ω hω => hω.1 n
  have hl (k : ℕ) : ∀ᵐ a ∂actualCoefficientLaw Q,
      Tendsto (fun n => ∫ x in Metric.closedBall (0 : Vec d) (k : ℝ),
        ‖g n a x - G a x‖ ^ 2) atTop (𝓝 0) :=
    ae_spatial_L2_limit_of_pullback (physicalReferenceLaw Q) π hπ g G
      (fun n => (hm n).2) hG _
      (hsource.mono fun ω hω => hω.2.2.2.1 _ (isCompact_closedBall _ _))
  refine ⟨u, g, G, hm, hG, ?_, hsource.mono fun ω hω => hω.2.2.2.2⟩
  filter_upwards [ae_all_iff.mpr hu, ae_all_iff.mpr hg, hGG,
    ae_all_iff.mpr hw, ae_all_iff.mpr hl] with a hua hga hGa hwa hla
  refine ⟨hwa, fun n K hK => ⟨hua n K hK, hga n K hK⟩, hGa, ?_⟩
  intro K hK
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Vec d)).mp hK.isBounded
  obtain ⟨k, hk⟩ := exists_nat_gt R
  let V := Metric.closedBall (0 : Vec d) (k : ℝ)
  have hsub : K ⊆ V := hR.trans (Metric.closedBall_subset_closedBall hk.le)
  apply squeeze_zero (fun n => integral_nonneg fun _ => sq_nonneg _) ?_ (hla k)
  intro n
  have hmem := (hga n V (isCompact_closedBall _ _)).sub (hGa V (isCompact_closedBall _ _))
  exact setIntegral_mono_set
    ((memLp_two_iff_integrable_sq_norm hmem.aestronglyMeasurable).mp hmem)
    (ae_of_all _ fun _ => sq_nonneg _) (ae_of_all _ fun _ hx => hsub hx)

end EinsteinRelation.Correctors
