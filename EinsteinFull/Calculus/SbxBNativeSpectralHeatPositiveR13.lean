import EinsteinFull.Calculus.SbxBNativeResolventIdentificationR04
import EinsteinFull.Calculus.SbxBNativeSpectralCompactnessR06

open MeasureTheory
open scoped NNReal ENNReal Topology InnerProductSpace

namespace EinsteinFull.Calculus
open EinsteinRelation EinsteinRelation.SpatialDirichlet
open EinsteinFull.External.Source.GMP EinsteinFull.Blueprint.TubeProbability
open EinsteinFull.Blueprint.TubeProbability.DimensionLift
open EinsteinFull.Blueprint.SbxS3UniformCrossHeat
open SubdiffusiveProcess

noncomputable section

/-- The selected native shifted resolvent preserves nonnegative weighted data.
The variational nonnegativity theorem tests the weak equation by the negative part. -/
theorem br13_native_shifted_resolvent_nonneg {d : ℕ} (hd : 2 ≤ d)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (hell : IsUniformlyElliptic κ ρ α)
    (μ : MarkovProcess.Semigroup.PositiveShift)
    (f : Lp ℝ 2 (dirichletVolume ρ R))
    (hf : ∀ᵐ x ∂dirichletVolume ρ R, 0 ≤ f x) :
    ∀ᵐ x ∂dirichletVolume ρ R,
      0 ≤ dirichletHilbertInclusion ρ R hR κ⁻¹
        (fun x _ => (hell.2.2 x).2.1)
        (bNativeShiftedDirichletResolvent hd hκ hell R hR μ f) x := by
  apply dirichletHilbert_shifted_variational_nonneg hκ hell R hR
    (inv_nonneg.mpr μ.property.le) f hf
  exact (b_native_shifted_dirichlet_resolvent_spec hd hκ hell R hR μ).2 f _ |>.mp rfl

/-- The spectral heat operator of the supplied Dirichlet resolution preserves
nonnegative data and the unit interval in the actual weighted L² space. -/
theorem br13_native_spectral_heat_order {d : ℕ} (hd : 2 ≤ d)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (hell : IsUniformlyElliptic κ ρ α)
    (s : DirichletSpectralResolution ρ α R)
    (t : ℝ≥0) (f : Lp ℝ 2 (dirichletVolume ρ R)) :
    ((∀ᵐ x ∂dirichletVolume ρ R, 0 ≤ f x) →
      ∀ᵐ x ∂dirichletVolume ρ R, 0 ≤
        SpectralHeat.heatOperator (spectralHeatBasis s) s.eigenvalue
          (fun n => (s.eigenvalue_pos n).le) t f x) ∧
    ((∀ᵐ x ∂dirichletVolume ρ R, 0 ≤ f x ∧ f x ≤ 1) →
      ∀ᵐ x ∂dirichletVolume ρ R, 0 ≤
        SpectralHeat.heatOperator (spectralHeatBasis s) s.eigenvalue
          (fun n => (s.eigenvalue_pos n).le) t f x ∧
        SpectralHeat.heatOperator (spectralHeatBasis s) s.eigenvalue
          (fun n => (s.eigenvalue_pos n).le) t f x ≤ 1) := by
  obtain ⟨u, hu, hv⟩ := br06_native_spectral_eigenvectors hκ hR hell s
  apply spectral_heat_order_of_variational hd hκ hell R hR s u _ hv t f
  intro n
  have hb : spectralHeatBasis s n = (s.square_integrable n).toLp (s.eigenfunction n) := by
    exact congrFun (HilbertBasis.coe_mk s.orthonormal
      (le_of_eq (Submodule.dense_iff_topologicalClosure_eq_top.mp s.complete).symm)) n
  exact hb.trans (hu n)

#print axioms br13_native_shifted_resolvent_nonneg
#print axioms br13_native_spectral_heat_order

end
end EinsteinFull.Calculus
