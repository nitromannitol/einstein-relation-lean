import EinsteinRelation.Correctors.PairedPDECutoffGlobalGradient
import EinsteinRelation.Correctors.SpatialWeakLocalization
import EinsteinRelation.Correctors.ParabolicSpatialConvolution

/-! # The actual compact cutoff has a whole-space spatial weak gradient

Source: `paper/main.tex:832–840`. Compact support inside the cylinder
extends the samplewise spatial product rule to all times and all space.
No zero trace of the original solution is used.
-/

open MeasureTheory
open scoped Convolution

namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- The actual compact cutoff solution and its product-rule field satisfy
the whole-space slice weak-gradient equation almost everywhere in time.
Source: `paper/main.tex:832–840`. -/
theorem parabolicSolution_cutoff_global_weakGradient {d : ℕ} {K : ℝ}
    {A : Coefficient d K} {I : Set ℝ} {U : Set (Vec d)}
    (hI : MeasurableSet I)
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hsol : IsParabolicSolution A I U u G)
    {ζ : ℝ × Vec d → ℝ} (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hζc : HasCompactSupport ζ) (hζsupp : tsupport ζ ⊆ I ×ˢ U) :
    ∀ᵐ t ∂(volume : Measure ℝ),
      HasWeakGradient Set.univ (fun x => ζ (t,x) * u (t,x))
        (fun x j => ζ (t,x) * G (t,x) j +
          u (t,x) * fderiv ℝ ζ (t,x) (0,unitVector j)) := by
  have hae := (ae_restrict_iff' hI).mp hsol.2.2.2.1
  filter_upwards [hae] with t ht
  by_cases htI : t ∈ I
  · have hs : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec d => ζ (t,x)) :=
      hζ.comp (contDiff_const.prodMk contDiff_id)
    have hemb : Topology.IsClosedEmbedding (fun x : Vec d => (t,x)) := by
      rw [Topology.IsClosedEmbedding.isClosedEmbedding_iff_continuous_injective_isClosedMap]
      exact ⟨continuous_const.prodMk continuous_id,
        fun _ _ h => congrArg Prod.snd h, isClosedMap_prodMk_left t⟩
    have hsub : tsupport (fun x : Vec d => ζ (t,x)) ⊆
        (fun x : Vec d => (t,x)) ⁻¹' tsupport ζ := by
      apply closure_minimal
      · intro x hx
        exact subset_tsupport ζ hx
      · exact (isClosed_tsupport ζ).preimage (continuous_const.prodMk continuous_id)
    have htest : IsSpatialTest U (fun x => ζ (t,x)) :=
      ⟨hs, hζc.comp_isClosedEmbedding hemb, fun x hx => (hζsupp (hsub hx)).2⟩
    have hg := hasWeakGradient_mul_spatialTest (ht htI) htest
    have hder (j : Fin d) (x : Vec d) :
        coordinateDerivative j (fun y => ζ (t,y)) x =
          fderiv ℝ ζ (t,x) (0,unitVector j) := by
      have hd := ((hζ.differentiable (by simp) (t,x)).hasFDerivAt).comp x
        ((hasFDerivAt_const t x).prodMk (hasFDerivAt_id x))
      change fderiv ℝ (ζ ∘ Prod.mk t) x (unitVector j) = _
      rw [hd.fderiv]
      rfl
    simpa only [hder] using hg
  · have hn (x : Vec d) : (t,x) ∉ tsupport ζ :=
      fun hx => htI (hζsupp hx).1
    have hz (x : Vec d) : ζ (t,x) = 0 := image_eq_zero_of_notMem_tsupport (hn x)
    have hd (x : Vec d) : fderiv ℝ ζ (t,x) = 0 :=
      fderiv_of_notMem_tsupport ℝ (hn x)
    have hzero : HasWeakGradient Set.univ (fun _ : Vec d => (0 : ℝ))
        (fun _ => (0 : Vec d)) := by
      intro j
      refine ⟨locallyIntegrableOn_zero, locallyIntegrableOn_zero, ?_⟩
      intro ψ _
      simp
    simpa only [hz, hd, ContinuousLinearMap.zero_apply, zero_mul, mul_zero,
      add_zero, Pi.zero_apply] using hzero

/-- Smoothing the actual cutoff solution transfers its genuine spatial
product-rule gradient through the convolution. Source: `paper/main.tex:832–840`. -/
theorem parabolicSolution_cutoff_convolution_spatial_fderiv {d : ℕ} {K : ℝ}
    {A : Coefficient d K} {I : Set ℝ} {U : Set (Vec d)}
    (hI : MeasurableSet I) (hU : IsOpen U)
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hsol : IsParabolicSolution A I U u G)
    {ζ κ : ℝ × Vec d → ℝ} (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hζc : HasCompactSupport ζ) (hζsupp : tsupport ζ ⊆ I ×ˢ U)
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (hκc : HasCompactSupport κ)
    (z : ℝ × Vec d) (j : Fin d) :
    fderiv ℝ ((fun w => ζ w * u w) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] κ)
        z (0,unitVector j) =
      ((fun w => ζ w * G w j + u w * fderiv ℝ ζ w (0,unitVector j))
        ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] κ) z := by
  exact paired_convolution_spatial_fderiv
    (parabolicSolution_cutoff_memLp_global hI hU.measurableSet hsol
      hζ.continuous hζc hζsupp)
    (fun k => parabolicSolution_cutoff_gradient_memLp_global hI hU hsol hζ hζc hζsupp k)
    (parabolicSolution_cutoff_global_weakGradient hI hsol hζ hζc hζsupp) hκ hκc z j

end EinsteinRelation.Correctors
