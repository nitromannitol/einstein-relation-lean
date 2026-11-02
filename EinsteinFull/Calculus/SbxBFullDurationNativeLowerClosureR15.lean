import EinsteinFull.Calculus.SbxBFullDurationNativeLowerR12
import EinsteinFull.Calculus.SbxBWeightedRowInitialTraceClosureR15
import EinsteinFull.Calculus.SbxBActualSpectrumSelectionR14

open EinsteinRelation MeasureTheory Filter EinsteinFull.External.Source.GMP
open EinsteinFull.Blueprint.TubeProbability EinsteinFull.Blueprint.SbxS3UniformCrossHeat
open scoped Topology InnerProductSpace NNReal

namespace EinsteinFull.Calculus

/-- The native Dirichlet spectral kernel has a uniform lower bound for either
orientation at every prescribed positive duration. -/
theorem b_full_duration_native_lower_closure_r15
    (d : ℕ) (hd : 2 ≤ d) (κ S T : ℝ)
    (hκ : 0 < κ) (hS : 0 < S) (hT : 0 < T) :
    ∃ c : ℝ, 0 < c ∧ ∀ (R lam : ℝ),
    0 < R → 0 < lam → S = lam * R →
    ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d), IsUniformlyElliptic κ ρ α →
    Continuous ρ → ∀ s : DirichletSpectralResolution ρ α R,
    ∀ x ∈ sourceBall 0 (S/2), ∀ y ∈ sourceBall 0 (S/2),
      c ≤ (lam⁻¹)^d * bNativeSpectralKernelR13 s (T / lam^2)
        (lam⁻¹ • x) (lam⁻¹ • y) / ρ (lam⁻¹ • y) ∧
      c ≤ (lam⁻¹)^d * bNativeSpectralKernelR13 s (T / lam^2)
        (lam⁻¹ • y) (lam⁻¹ • x) / ρ (lam⁻¹ • x) := by
  obtain ⟨δ₁, hδ₁, hmass⟩ := EinsteinFull.b_renewal_native_half_survival_of_ellipticity d hd κ hκ
  obtain ⟨δ₂, H, hδ₂, hH, hcompare⟩ := EinsteinFull.b_renewal_native_harnack_of_ellipticity d hd κ hκ
  obtain ⟨c, hc, hbound⟩ := b_full_duration_native_lower d hd κ (min δ₁ δ₂) H S T
    hκ (lt_min hδ₁ hδ₂) hH hS hT
  refine ⟨c, hc, ?_⟩
  intro R lam hR hlam hSR ρ α hell hρ s
  obtain ⟨w, hw, hv⟩ := br06_native_spectral_eigenvectors hκ hR hell s
  have hb : ∀ n, spectralHeatBasis s n = dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (hell.2.2 x).2.1) (w n) := by
    intro n
    have h : spectralHeatBasis s n = (s.square_integrable n).toLp (s.eigenfunction n) :=
      congrFun (HilbertBasis.coe_mk s.orthonormal
        (le_of_eq (Submodule.dense_iff_topologicalClosure_eq_top.mp s.complete).symm)) n
    exact h.trans (hw n)
  have hs := br06_native_spectral_eigenvalue_tendsto_atTop hd hκ hR hell s
  obtain ⟨G, hG⟩ := spectral_heat_global_positive_strip_gradient hd hκ hell R hR s hs w hb hv
  let F : ℝ → Vec d → Vec d → Vec d := fun t x y => ρ y • G t x y
  have hcal : BNativeSpectralCaloricR13 s F := by
    intro y hy a b ha hab
    exact (b_weighted_caloric_trace_const_mul (hG y hy a b ha hab).1
      (hG y hy a b ha hab).2 (ρ y)).1
  have hzero : BNativeSpectralZeroExtensionR13 s F := by
    intro y hy a b ha hab
    exact (b_weighted_caloric_trace_const_mul (hG y hy a b ha hab).1
      (hG y hy a b ha hab).2 (ρ y)).2
  have hinit : BNativeSpectralInitialDeltaR13 s := by
    intro y hy φ hφ
    exact br14_native_column_initial_delta hκ hell hρ s
      (br15_weighted_row_initial_trace_of_ellipticity hd hκ hR hell s)
      y hy φ hφ.1.continuous hφ.2.1 hφ.2.2
  have hfund := b_native_fundamental_assembly_r13 hd hκ hR hell s F hcal hzero hinit
  apply hbound R lam hR hlam hSR ρ α hell (bNativeSpectralKernelR13 s) F hfund
  · intro x r u hr hball hu hcap
    exact hmass R ρ α _ _ hell hfund x r u hr hball hu
      (le_trans hcap (mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg r)))
  · intro x y r u hr hball hy hu hcap hdist
    exact hcompare R ρ α _ _ hell hfund x y r u hr hball hy hu
      (le_trans hcap (mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg r))) hdist

#print axioms b_full_duration_native_lower_closure_r15

end EinsteinFull.Calculus
