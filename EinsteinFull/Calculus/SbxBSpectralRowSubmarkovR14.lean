import EinsteinFull.Calculus.SbxBNativeKernelNonnegativeR13
import EinsteinFull.Calculus.SbxBNativeSpectralHeatPositiveR13
import EinsteinFull.Calculus.C8TubeInitialDeltaAfterSurvival

open MeasureTheory Filter
open scoped NNReal ENNReal Topology InnerProductSpace

namespace EinsteinFull.Calculus
open EinsteinRelation External.Source.GMP Blueprint.TubeProbability
open Blueprint.TubeProbability.DimensionLift Blueprint.SbxS3UniformCrossHeat

noncomputable section

/-- Every positive-time native spectral row is nonnegative on the ball,
Lebesgue integrable there, and has total mass at most one. -/
theorem br14_native_spectral_row_submarkov {d : ℕ} (hd : 2 ≤ d)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (hell : IsUniformlyElliptic κ ρ α)
    (s : DirichletSpectralResolution ρ α R)
    (t : ℝ) (ht : 0 < t) (x : Vec d) (hx : x ∈ sourceBall 0 R) :
    (∀ y ∈ sourceBall 0 R, 0 ≤ ρ y * ∑' n,
      Real.exp (-s.eigenvalue n * t) * s.eigenfunction n x * s.eigenfunction n y) ∧
    IntegrableOn (fun y => ρ y * ∑' n,
      Real.exp (-s.eigenvalue n * t) * s.eigenfunction n x * s.eigenfunction n y)
      (sourceBall 0 R) ∧
    0 ≤ (∫ y in sourceBall 0 R, ρ y * ∑' n,
      Real.exp (-s.eigenvalue n * t) * s.eigenfunction n x * s.eigenfunction n y) ∧
    (∫ y in sourceBall 0 R, ρ y * ∑' n,
      Real.exp (-s.eigenvalue n * t) * s.eigenfunction n x * s.eigenfunction n y) ≤ 1 := by
  classical
  haveI : IsFiniteMeasure (dirichletVolume ρ R) :=
    dirichletVolume_isFinite ρ R hR κ⁻¹ (fun y _ => (hell.2.2 y).2.1)
  have hρ0 : ∀ y, 0 ≤ ρ y := fun y => hκ.le.trans (hell.2.2 y).1
  let q : Vec d → ℝ := fun y => ∑' n, Real.exp (-s.eigenvalue n * t) *
    s.eigenfunction n x * s.eigenfunction n y
  have hqi : Integrable q (dirichletVolume ρ R) :=
    (spectral_heat_row_memLp hd hκ hell hR s t ht x hx).integrable (by norm_num)
  have hi : IntegrableOn (fun y => ρ y * q y) (sourceBall 0 R) := by
    unfold dirichletVolume at hqi
    have h := (integrable_withDensity_iff_integrable_smul' hell.1.ennreal_ofReal
      (ae_of_all _ fun y => ENNReal.ofReal_lt_top)).1 hqi
    change Integrable (fun y => ρ y * q y) (volume.restrict (sourceBall 0 R))
    simpa [hρ0, smul_eq_mul, mul_comm] using h
  obtain ⟨u, hu, hv⟩ := br06_native_spectral_eigenvectors hκ hR hell s
  have hb : ∀ n, spectralHeatBasis s n =
      dirichletHilbertInclusion ρ R hR κ⁻¹ (fun z _ => (hell.2.2 z).2.1) (u n) := by
    intro n
    have he : spectralHeatBasis s n = (s.square_integrable n).toLp (s.eigenfunction n) :=
      congrFun (HilbertBasis.coe_mk s.orthonormal
        (le_of_eq (Submodule.dense_iff_topologicalClosure_eq_top.mp s.complete).symm)) n
    exact he.trans (hu n)
  have hm := c8_native_spectral_heat_mass_bounds hd hκ hR hell s u
    (br06_native_spectral_eigenvalue_tendsto_atTop hd hκ hR hell s) hb hv
    t.toNNReal (by simpa only [Real.coe_toNNReal _ ht.le] using ht) x hx
  have heq : (∫ y, q y ∂dirichletVolume ρ R) =
      ∫ y in sourceBall 0 R, ρ y * q y := by
    change (∫ y, q y ∂(volume.restrict
      (sourceBall (0 : Vec d) R)).withDensity (fun y => ENNReal.ofReal (ρ y))) = _
    rw [integral_withDensity_eq_integral_toReal_smul hell.1.ennreal_ofReal
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    apply integral_congr_ae
    filter_upwards [] with y
    simp only [ENNReal.toReal_ofReal (hρ0 y), smul_eq_mul]
  have hm' : 0 ≤ (∫ y in sourceBall 0 R, ρ y * q y) ∧
      (∫ y in sourceBall 0 R, ρ y * q y) ≤ 1 := by
    simpa only [Real.coe_toNNReal _ ht.le, ← heq, q] using hm
  refine ⟨?_, hi, hm'⟩
  intro y hy
  have hp : br13NativeSpectralHeatPositive s := by
    intro τ f hf
    exact (br13_native_spectral_heat_order hd hκ hR hell s τ f).1 hf
  simpa only [Real.coe_toNNReal _ ht.le] using
    br13_native_kernel_nonnegative_of_heat_positive hd hκ hR hell s hp
      t.toNNReal (by simpa only [Real.coe_toNNReal _ ht.le] using ht) x y hx hy

#print axioms br14_native_spectral_row_submarkov

end
end EinsteinFull.Calculus
