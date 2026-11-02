import EinsteinFull.Calculus.C12TubeDiagonalLower
import EinsteinFull.Blueprint.Foundation.Proofs.SbxS3UniformCrossHeat

open EinsteinRelation MeasureTheory Filter EinsteinFull.External.Source.GMP
open PDE hiding Vec Mat
open EinsteinFull.Blueprint.TubeProbability
open EinsteinFull.Blueprint.TubeProbability.DimensionLift
open EinsteinFull.Blueprint.SbxS3UniformCrossHeat
open scoped Topology

noncomputable section
namespace EinsteinFull.Calculus

/-- A native spectral diagonal lower bound conditional on its survival mass. -/
theorem c12_native_spectral_diagonal_lower {d : ℕ} (hd : 2 ≤ d)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (s : DirichletSpectralResolution ρ α R)
    (t : ℝ) (ht : 0 < t) (x : Vec d) (hx : x ∈ sourceBall 0 R)
    (m : ℝ) (hm : 0 ≤ m)
    (hmass : m ≤ ∫ y in sourceBall 0 R,
      (∑' i, Real.exp (-s.eigenvalue i*t)*s.eigenfunction i x*s.eigenfunction i y)*ρ y) :
    m^2/(κ⁻¹*(volume (sourceBall (0 : Vec d) R)).toReal) ≤
      ∑' i, Real.exp (-2*s.eigenvalue i*t)*(s.eigenfunction i x)^2 := by
  let k : Vec d → ℝ := fun y => ∑' i, Real.exp (-s.eigenvalue i*t)*
    s.eigenfunction i x*s.eigenfunction i y
  letI : IsFiniteMeasure (dirichletVolume ρ R) :=
    dirichletVolume_isFinite ρ R hR κ⁻¹ (fun y _ => (hell.2.2 y).2.1)
  have hρ0 : ∀ y, 0 ≤ ρ y := fun y => le_trans hκ.le (hell.2.2 y).1
  have hk := spectral_heat_row_memLp hd hκ hell hR s t ht x hx
  change MemLp k 2 (dirichletVolume ρ R) at hk
  have hconvert (f : Vec d → ℝ) :
      (∫ y, f y ∂dirichletVolume ρ R) = ∫ y in sourceBall 0 R, f y * ρ y := by
    unfold dirichletVolume
    rw [integral_withDensity_eq_integral_toReal_smul hell.1.ennreal_ofReal
      (ae_of_all _ fun y => ENNReal.ofReal_lt_top)]
    simp [hρ0, mul_comm]
  have hweight (f : Vec d → ℝ) (hf : Integrable f (dirichletVolume ρ R)) :
      IntegrableOn (fun y => f y * ρ y) (sourceBall 0 R) := by
    unfold dirichletVolume at hf
    have hi := (integrable_withDensity_iff_integrable_smul' hell.1.ennreal_ofReal
      (ae_of_all _ fun y => ENNReal.ofReal_lt_top)).1 hf
    change Integrable (fun y => f y * ρ y) (volume.restrict (sourceBall 0 R))
    simpa [hρ0, smul_eq_mul, mul_comm] using hi
  have hdiag : (∑' i, Real.exp (-2*s.eigenvalue i*t)*(s.eigenfunction i x)^2) =
      ∫ y in sourceBall 0 R, (k y)^2 * ρ y := by
    rw [← hconvert]
    exact (spectral_heat_row_integral_sq hd hκ hell hR s t ht x hx).symm
  have hvol : 0 < (volume (sourceBall (0 : Vec d) R)).toReal := by
    apply ENNReal.toReal_pos
    · rw [← pde_ball_eq_sourceBall _ hR]
      exact ne_of_gt ((PDE.isOpen_euclideanBall _ _).measure_pos volume
        ⟨_, PDE.center_mem_euclideanBall _ hR⟩)
    · exact c9_sourceBall_measure_ne_top 0 R
  apply c12_diagonal_lower_div (mul_pos (inv_pos.mpr hκ) hvol)
  exact c12_diagonal_lower_from_row_mass hR (inv_pos.mpr hκ) hm ρ k hell.1
    (fun y => ⟨hρ0 y, (hell.2.2 y).2.1⟩)
    (hweight k (hk.integrable (by norm_num))) (hweight _ hk.integrable_sq) hmass hdiag

end EinsteinFull.Calculus
