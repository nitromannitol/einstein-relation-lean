import EinsteinFull.Blueprint.G4.node_e_u3A_division
import EinsteinFull.Blueprint.G4.node_e_u3A_numerator_u2D_clock
import EinsteinFull.Blueprint.G4.node_e_u3A_linear_u2D_velocity
import EinsteinFull.Blueprint.G4.node_eq_u2E_time_u2D_change_u2D_identities
import EinsteinFull.Blueprint.G4.node_clock_u2D_zero_u2D_coefficient
import EinsteinFull.Calculus.S4DivisionMisc
import EinsteinFull.Calculus.S4DivisionKernel2
import EinsteinFull.Calculus.S4SharpFamilySupport
import EinsteinFull.Calculus.S2ForwardFamily
import EinsteinRelation.Correctors.HomogenizedMatrixBounds
import EinsteinFull.Blueprint.Foundation.Draft.S2SmoothScopeTimeChange

/-!
# `e:division`

The reciprocal expansion of the clock rate and the velocity expansion divided by the clock rate,
assembled from `e:numerator-clock`, `e:linear-velocity`, `eq.time-change-identities` and
`clock-zero-coefficient`.  The analytic work is in `S4DivisionAbstract`, `S4DivisionVector`,
`S4DivisionNine`, `S4DivisionKernel2` and `S4DivisionMisc`.
-/

open MeasureTheory Filter
open scoped Topology NNReal BigOperators

namespace EinsteinFull.Blueprint
open EinsteinFull EinsteinRelation

theorem node_e_u3A_division_of_deps
    (hnum : node_e_u3A_numerator_u2D_clockStmt)
    (hlin : node_e_u3A_linear_u2D_velocityStmt)
    (htc : node_eq_u2E_time_u2D_change_u2D_identitiesStmtV2)
    (hclk0 : node_clock_u2D_zero_u2D_coefficientStmt) :
    node_e_u3A_divisionStmt := by
  intro d hd D
  obtain ⟨C₁, lamStar₁, hC₁, hls₁, hls₁e, hnumQ⟩ := hnum d hd D
  obtain ⟨Λ₀, hΛ₀, hclkQ⟩ := hclk0 d hd D
  set Λ : ℝ := max Λ₀ (Real.exp (2 * D.ellipticity)) with hΛdef
  have hΛ1 : 1 ≤ Λ := le_trans hΛ₀ (le_max_left _ _)
  have hΛ0 : 0 ≤ Λ := by linarith
  have hΛpos : 0 < Λ := by linarith
  obtain ⟨K₀, hK₀0, hscal⟩ := division_scalar_claim d hd C₁ Λ hC₁.le hΛ0
  obtain ⟨K₁, hK₁0, hvec⟩ :=
    division_vector_claim (E := EuclideanSpace ℝ (Fin d)) d hd C₁ Λ hC₁.le hΛ0
  set Csum : ℝ := ((d : ℝ) + 1) * recipBound Λ C₁ d +
    ((d : ℝ) + 1) * (((d : ℝ) + 1) * (recipBound Λ C₁ d * C₁)) +
    (2 * Λ * C₁ + 2 * C₁ * Λ ^ 2 * C₁) with hCsum
  set C : ℝ := max (max Λ 16) (max (max K₀ K₁) Csum) with hCdef
  have hΛC : Λ ≤ C := le_trans (le_max_left _ _) (le_max_left _ _)
  have h16 : 16 ≤ C := le_trans (le_max_right _ _) (le_max_left _ _)
  have hK₀C : K₀ ≤ C := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_right _ _)
  have hK₁C : K₁ ≤ C := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_right _ _)
  have hCsC : Csum ≤ C := le_trans (le_max_right _ _) (le_max_right _ _)
  have hCpos : 0 < C := by linarith
  refine ⟨C, lamStar₁, hCpos, hls₁, hls₁e, ?_⟩
  intro Q hQ β a μ Z covariance hβ ha hμ hZ hcov P hP
  have hnumQ' := hnumQ Q hQ β a μ Z covariance hβ ha hμ hZ hcov P hP
  have hclkQ' := hclkQ Q hQ β a μ Z covariance hβ ha hμ hZ hcov P hP
  obtain ⟨-, -, -, -, hclkLam⟩ := hclkQ'
  intro first A p₀ γ u₀ u₂ K
  obtain ⟨hγ, hK, hR, hI, hrest⟩ := hnumQ'
  refine ⟨hγ, ?_⟩
  intro k χ m aCoeff etaCoeff
  obtain ⟨hk0, haC, hηC, hχ, hexp⟩ := hrest
  -- the mean clock density and its lower bound
  have hm_low : Λ⁻¹ ≤ m := by
    have h1 : m = ∫ ω, clockDensity ω (0 : Vec d) ∂Q.measure := reducedLaw_integral_clock Q
    have h2 := clock_mean_lower Q
    calc Λ⁻¹ ≤ (Real.exp (2 * D.ellipticity))⁻¹ :=
          inv_anti₀ (Real.exp_pos _) (le_max_right _ _)
      _ = Real.exp (-2 * D.ellipticity) := by rw [← Real.exp_neg]; ring_nf
      _ ≤ m := by rw [h1]; exact h2
  have hmpos : 0 < m := lt_of_lt_of_le (inv_pos.2 hΛpos) hm_low
  have hmΛ : |m⁻¹| ≤ Λ := by
    rw [abs_of_pos (inv_pos.2 hmpos)]
    exact (inv_le_comm₀ hmpos hΛpos).2 hm_low
  -- (1) the first coefficient vector
  have hA1 : aCoeff ⟨0, Nat.zero_lt_succ d⟩ = A.mulVec (unitVector first) := by
    funext i
    have e : aCoeff ⟨0, Nat.zero_lt_succ d⟩ i =
        (∫ ω, ω.1 0 first i ∂reducedLaw Q) - 2 * k (some i) ⟨0, Nat.zero_lt_succ d⟩ :=
      if_pos rfl
    obtain ⟨⟨hint, -⟩, hAi⟩ := hlin d hd D Q hQ β a hβ ha (P 0) (hP 0) i
    have h := integrated_kernel_zero (d := d) (by omega) (u₀ (some i)) (u₂ (some i)) γ
      (K (some i)) hint
    have e1 : k (some i) ⟨0, Nat.zero_lt_succ d⟩ =
        (∫ t in Set.Ici (0 : ℝ), iteratedDeriv 0 (fun lam : ℝ =>
          (kernelProfileRemainder d (u₀ (some i)) (u₂ (some i)) γ (K (some i)) t
            (lam : ℂ)).re) 0 / (((0 : ℕ).factorial : ℕ) : ℝ)) +
          2 * profileTaylorCoefficient (u₀ (some i)) (u₂ (some i)) γ 0 / (((d - 0 : ℕ)) : ℝ) := by
      simp only [k, Fin.val_mk]
      rw [if_pos (by omega)]
    have hk : k (some i) ⟨0, Nat.zero_lt_succ d⟩ =
        ∫ t in Set.Ici (0 : ℝ), (velocityCorrelation Q first i 0 (P 0) β a t.toNNReal).re :=
      e1.trans h
    have hmul : (A.mulVec (unitVector first)) i = A i first := by
      simp [Matrix.mulVec, dotProduct, unitVector, Pi.single_apply]
    rw [e, hk, hmul]
    have hcomm : A i first = A first i :=
      (homogenizedMatrix_apply_comm Q i first)
    rw [hcomm]
    exact hAi
  -- the covariance clause
  have hcovClause : ∀ X : DiffusionFamily d, IsSignedPhysicalFamily first Q X →
      ∀ covariance : Mat d, HasDiffusivity Q.measure (originLaw (X 0)) covariance →
        divB d m etaCoeff aCoeff ⟨0, Nat.zero_lt_succ d⟩ =
          covariance.mulVec (unitVector first) := by
    intro X hX cov hcovX
    have hsm : ∀ᵐ ω ∂Q.measure, IsSmoothFieldPair ω := hQ.mono fun ω h => h.1
    obtain ⟨Λt, hΛt1, hall⟩ := htc D.ellipticity D.one_le_ellipticity
    obtain ⟨Y, hYsol, hYrel⟩ := exists_reducedFamily_of_signedPhysical first Q hsm X hX
    obtain ⟨-, -, hdiff⟩ := hall d hd D.dependenceRange D.derivativeBound Q
      D.one_le_dependenceRange D.derivativeBound_pos hQ X Y hX hYsol hYrel
    have hcc : cov = m⁻¹ • homogenizedCoefficient Q := hcovX.unique hdiff
    rw [divB_zero m etaCoeff aCoeff hA1, hcc, Matrix.smul_mulVec]
  refine ⟨divRecip d m etaCoeff, divB d m etaCoeff aCoeff, divC m χ (A.mulVec (unitVector first)),
    hA1, divRecip_zero d m etaCoeff, fun n hn => divRecip_succ d m etaCoeff n hn,
    fun n => rfl, rfl, ?_, divB_zero m etaCoeff aCoeff hA1, hcovClause, ?_⟩
  · have hAe : euclideanNorm (A.mulVec (unitVector first)) ≤ C₁ := by
      rw [← hA1]; exact haC _
    exact le_trans (div_total_bound hΛ0 hC₁.le hmΛ hηC hχ hAe haC) hCsC
  · intro lam h₀ h₁ hsmall Y hY ell η hvel hclk
    obtain ⟨hH2, hH1⟩ := hexp lam h₀ h₁ hsmall Y hY ell η hvel hclk
    obtain ⟨hη1, hη2, -⟩ := hclkLam lam (abs_pos.mp h₀) Y hY η hclk
    have hΛ₀pos : 0 < Λ₀ := by linarith
    have hη1' : Λ⁻¹ ≤ η := le_trans (inv_anti₀ hΛ₀pos (le_max_left _ _)) hη1
    have hη2' : η ≤ Λ := le_trans hη2 (le_max_left _ _)
    exact division_nine hC₁ hΛ1 hK₀C hK₁C h16 hΛC hscal hvec hm_low haC hηC hχ hA1 h₀ hsmall
      hη1' hη2' hH2 hH1

end EinsteinFull.Blueprint
