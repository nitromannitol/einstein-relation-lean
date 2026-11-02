import EinsteinFull.Blueprint.G2.node_e_u3A_holder_u2D_average_u23_unforced_u2D_interior
import EinsteinFull.Blueprint.Foundation.node_e_u3A_local_u2D_time
import EinsteinFull.Blueprint.Foundation.Proofs.ReducedBounds
import EinsteinFull.Calculus.ParabolicBridgeFinal2

open MeasureTheory
open scoped ENNReal

namespace EinsteinFull.Blueprint

open EinsteinRelation

/-- Reduction of `e:holder-average#unforced-interior`.  The proof uses the proved reduced bounds
(`eq.reduced-bounds`), time mollification of the distributional solution, the Moser/Harnack
oscillation decay for weak solutions of `∂ₜu = ∇·(a∇u)` with rescaled time, and the mean
oscillation conversion; the binder is the listed (unused) dependency. -/
theorem node_e_u3A_holder_u2D_average_u23_unforced_u2D_interior_of_deps
    (_hdeps : node_e_u3A_local_u2D_timeStmt) :
    node_e_u3A_holder_u2D_average_u23_unforced_u2D_interiorStmt := by
  intro d hd2 D
  have hd : 0 < d := by omega
  obtain ⟨Λ, A, B, hΛ1, hA, hB, hAB, hred⟩ :=
    node_eq_u2E_reduced_u2D_bounds_of_deps D.ellipticity D.one_le_ellipticity
  obtain ⟨α₀, C, hα0, hα1, hC1, hcore⟩ :=
    EinsteinFull.ParabolicBridge.holder_interior_ae d hd Λ hΛ1
  refine ⟨α₀, C, hα0, hα1, hC1, ?_⟩
  intro Q hQ
  filter_upwards [(hred d D.dependenceRange Q).2.2] with ω hω
  intro τ x r hr cyl v g hv hg H1 H2 θ hθ hθ2
  have hcyl : ∀ ρ : ℝ, 0 < ρ → cyl ρ = Set.Ioo (τ - ρ ^ 2) τ ×ˢ PDE.euclideanBall x ρ := by
    intro ρ hρ
    show Set.Ioo (τ - ρ ^ 2) τ ×ˢ {y : Vec d | euclideanNorm (y - x) < ρ} = _
    rw [EinsteinFull.ParabolicBridge.euclideanNorm_ball_eq x hρ]
  have hθr0 : 0 < θ * r := mul_pos hθ hr
  rw [hcyl r hr] at hv hg H1 H2
  rw [hcyl (θ * r) hθr0, hcyl r hr]
  have hmeas : ∀ j k : Fin d, Measurable fun y => (ω.1 y) j k := fun j k =>
    (ω.1.continuous.matrix_elem j k).measurable
  have hell : ∀ y : Vec d, ((ω.1 y).transpose = ω.1 y ∧
      (∀ ξ : Vec d, Λ⁻¹ * PDE.vecNormSq ξ ≤ PDE.vecDot ξ (PDE.matVecMul (ω.1 y) ξ)) ∧
      (∀ ξ : Vec d, PDE.vecDot ξ (PDE.matVecMul (ω.1 y) ξ) ≤ Λ * PDE.vecNormSq ξ)) :=
    fun y => ⟨(hω.1 y).1, fun ξ => ((hω.1 y).2 ξ).1, fun ξ => ((hω.1 y).2 ξ).2⟩
  exact hcore (fun y => ω.1 y) hmeas hell τ x r hr v g hv hg H1 H2 θ hθ hθ2

end EinsteinFull.Blueprint
