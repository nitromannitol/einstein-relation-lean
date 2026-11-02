import EinsteinFull.Blueprint.Foundation.node_l_u3A_forced_u2D_local_u23_off_u2D_diagonal
import EinsteinFull.Blueprint.Foundation.node_eq_u2E_reduced_u2D_bounds
import EinsteinFull.Calculus.S5OffDiagonalSupport

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinFull

/-- Davies' method for the physical forward and transpose evolutions: the exponential-weight
estimate for every Euclidean-`1`-Lipschitz exponent and the Gaussian estimate between
separated sets, with constants depending only on `d` and the structural bound.
`paper/main.tex:707–713`. -/
theorem node_l_u3A_forced_u2D_local_u23_off_u2D_diagonal_of_deps
    (hdeps : node_eq_u2E_reduced_u2D_boundsStmt) :
    node_l_u3A_forced_u2D_local_u23_off_u2D_diagonalStmt := by
  intro d hd Λ₀ hΛ₀
  obtain ⟨Λ, A, B, hΛ, -, -, -, hrest⟩ := hdeps Λ₀ hΛ₀
  have hΛ0 : 0 < Λ := by linarith
  have hC : 0 < 5 * Λ ^ 3 := by positivity
  refine ⟨5 * Λ ^ 3, 1 / (4 * (5 * Λ ^ 3)), ?_, by positivity, ?_⟩
  · have h1 : 1 ≤ Λ ^ 3 := one_le_pow₀ hΛ
    linarith
  · intro r₀ Q
    obtain ⟨-, -, hae⟩ := hrest d r₀ Q
    filter_upwards [hae] with ω hω
    obtain ⟨hell, -, -, -⟩ := hω
    have hell' := s5Elliptic_of_isElliptic hΛ hell
    have hmeas : ∀ j k, Measurable fun x => ω.1 x j k := fun j k =>
      (ω.1.continuous.matrix_elem j k).measurable
    intro i ζ P Pdag hP hPd S hS t ht
    have ht' : (0 : ℝ) < (t : ℝ) := NNReal.coe_pos.mpr ht
    have hS' : S = P ∨ S = Pdag := by simpa using hS
    have hW : ∀ (q : ℝ) (ψ : Vec d → ℝ), (∀ x y, |ψ x - ψ y| ≤ euclideanNorm (x - y)) →
        ∀ f : Lp ℂ 2 (volume : Measure (Vec d)),
          MemLp (fun x => ((Real.exp (q * ψ x) : ℝ) : ℂ) * f x) 2 volume →
          MemLp (fun x => ((Real.exp (q * ψ x) : ℝ) : ℂ) * (S t f) x) 2 volume ∧
            (eLpNorm (fun x => ((Real.exp (q * ψ x) : ℝ) : ℂ) * (S t f) x) 2 volume).toReal ≤
              Real.exp (5 * Λ ^ 3 * (‖ζ‖ ^ 2 + q ^ 2) * (t : ℝ)) *
                (eLpNorm (fun x => ((Real.exp (q * ψ x) : ℝ) : ℂ) * f x) 2 volume).toReal := by
      intro q ψ hψ f hf
      rcases hS' with rfl | rfl
      · exact s5_weighted_forward hell' hmeas i ζ hP t q hψ f hf
      · exact s5_weighted_transpose hell' hmeas i ζ hPd t q hψ f hf
    refine ⟨fun q ψ hψ f hf => hW q ψ hψ f hf, ?_⟩
    intro E F hE hF ℓ hℓ hsep f hf0
    exact s5_gaussian_of_weighted hC ht' (S t) hW E F hF ℓ hℓ hsep f hf0

end EinsteinFull.Blueprint
