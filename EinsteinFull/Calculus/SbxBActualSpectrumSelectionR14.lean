import EinsteinFull.Calculus.SbxBNativeFundamentalAssemblyR13
import EinsteinFull.Calculus.SbxBPointSourceCaloricR01
import EinsteinFull.Calculus.SbxBNativeKernelIntegralR13

open MeasureTheory Filter EinsteinRelation
open scoped Topology InnerProductSpace NNReal

namespace EinsteinFull
open External.Source.GMP Calculus Blueprint.SbxS3UniformCrossHeat Blueprint.TubeProbability

noncomputable section

/-- One actual Dirichlet spectrum has native variational lifts and a common
scaled gradient on every positive strip. The pointwise initial delta is kept
separate and, when supplied for this spectrum, completes the native certificate. -/
theorem b_actual_spectrum_selection_r14 {d : ℕ} (hd : 2 ≤ d)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (hell : IsUniformlyElliptic κ ρ α) :
    ∃ (s : DirichletSpectralResolution ρ α R)
      (u : ℕ → DirichletHilbertSpace (d := d) R hR)
      (G : ℝ → Vec d → Vec d → Vec d),
      Tendsto s.eigenvalue atTop atTop ∧
      (∀ n, spectralHeatBasis s n = dirichletHilbertInclusion ρ R hR κ⁻¹
        (fun x _ => (hell.2.2 x).2.1) (u n)) ∧
      (∀ n w, (∫ x in sourceBall (0 : Vec d) R,
        dot ((α x).mulVec (fun i => (u n).val (some i) x))
          (fun i => w.val (some i) x)) = s.eigenvalue n * inner ℝ
        (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (hell.2.2 x).2.1) (u n))
        (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (hell.2.2 x).2.1) w)) ∧
      BNativeSpectralCaloricR13 s G ∧ BNativeSpectralZeroExtensionR13 s G ∧
      (BNativeSpectralInitialDeltaR13 s →
        IsSpectralDirichletFundamentalSolution ρ α R (bNativeSpectralKernelR13 s) G) := by
  obtain ⟨s, u, hs, hb, hv, _⟩ :=
    exists_sourceBall_spectral_heat_native_lift hd hκ hell R hR
  obtain ⟨H, hH⟩ := spectral_heat_global_positive_strip_gradient hd hκ hell R hR s hs u hb hv
  let G : ℝ → Vec d → Vec d → Vec d := fun t x y => ρ y • H t x y
  have hscaled (y : Vec d) (hy : y ∈ sourceBall (0 : Vec d) R)
      (a b : ℝ) (ha : 0 < a) (hab : a < b) :=
    b_weighted_caloric_trace_const_mul (hH y hy a b ha hab).1
      (hH y hy a b ha hab).2 (ρ y)
  have hc : BNativeSpectralCaloricR13 s G := by
    intro y hy a b ha hab
    exact (hscaled y hy a b ha hab).1
  have hz : BNativeSpectralZeroExtensionR13 s G := by
    intro y hy a b ha hab
    exact (hscaled y hy a b ha hab).2
  exact ⟨s, u, G, hs, hb, hv, hc, hz,
    fun hi => b_native_fundamental_assembly_r13 hd hκ hR hell s G hc hz hi⟩

/-- The selected kernel represents the spectral heat action in weighted L²;
this is an almost-everywhere identity and does not assert a pointwise delta. -/
theorem b_actual_spectral_kernel_action_ae_r14 {d : ℕ} (hd : 2 ≤ d)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (hell : IsUniformlyElliptic κ ρ α)
    (s : DirichletSpectralResolution ρ α R)
    (φ : Vec d → ℝ) (hφ : IsSpatialTest (sourceBall 0 R) φ)
    (t : ℝ≥0) (ht : 0 < (t : ℝ)) :
    (fun x => SpectralHeat.heatOperator (spectralHeatBasis s) s.eigenvalue
      (fun n => (s.eigenvalue_pos n).le) t
      ((c16_spatial_test_memLp_dirichlet hR hell φ hφ).toLp φ) x) =ᵐ[dirichletVolume ρ R]
    fun x => ∫ y in sourceBall (0 : Vec d) R, bNativeSpectralKernelR13 s t x y * φ y := by
  apply br13_native_kernel_integral_represents_heat hκ hR hell s ?_ φ hφ t ht
  intro τ hτ x hx y hy
  exact spectral_heat_cross_summable_closedBall hd hκ hell hR s τ hτ x y
    (subset_closure hx) (subset_closure hy)

#print axioms exists_sourceBall_dirichletSpectralResolution_with_variational
#print axioms spectral_heat_global_positive_strip_gradient
#print axioms b_actual_spectrum_selection_r14
#print axioms b_actual_spectral_kernel_action_ae_r14

end
end EinsteinFull
