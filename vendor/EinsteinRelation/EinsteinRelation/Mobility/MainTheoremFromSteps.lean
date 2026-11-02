import EinsteinRelation.Diffusion.VelocityTimeChangeGMP
import EinsteinRelation.External.GMPPhysicalInputs
import EinsteinRelation.External.GMPReducedInputs
import EinsteinRelation.Environment.SourceReducedBoundSupport
import EinsteinRelation.Mobility.MainRateAssembly
import EinsteinRelation.Mobility.MainSteps

/-! # Theorem 1.2 from the internal steps

Source: `paper/main.tex`, Theorem 1.2 (`t.main`, lines 93-99) and its proof (lines 1187-1196).
`mobilityRate_of_steps` has the statement of the frozen Theorem 1.2 (`Frozen/MainRateV4.lean`,
`mobilityRateV4`), with the three internal steps of `Mobility.MainSteps` and the cited inputs of
`EinsteinRelation.External` as explicit hypotheses.

The bound hypothesis `hBounds` gives the a-priori ranges of `ā e₁` and of the mean clock. The
constant is `Λ = sourceReducedBound Λ₀ = exp(2Λ₀)(3Λ₀² + Λ₀ + 1)`, the reduced ellipticity and
clock bound of `paper/main.tex` 204-206. It dominates `exp(2Λ₀)`, the pointwise bound on the clock
rate `η`, and it is at least `1`.
-/

open MeasureTheory Filter
open scoped NNReal Topology

namespace EinsteinRelation

/-- The first homogenized column is the first column of `ā`: `ā e₁ = E[a(e₁ + ∇χ₁)]`. -/
theorem abar_mulVec_unitVector_zero {d : ℕ} {Λ₀ r₀ : ℝ} (hd : 2 ≤ d)
    (Q : EnvironmentLaw d Λ₀ r₀) :
    (abar Q).mulVec (unitVector (⟨0, by omega⟩ : Fin d)) = abarE1 hd Q := by
  rw [unitVector, Matrix.mulVec_single_one]
  rfl

/-- Theorem 1.2 from the internal steps. Given the reduced velocity rate (`hV`), the clock
estimate (`hC`), the covariance identity (`hS`), and the cited GMP inputs (`hRF`, `hRV`, `hTC`,
`hPos`), the physical mobility error is `O(lam)` for all `0 < lam ≤ lamStar`, with constants
depending only on `d`, `Λ₀` and `r₀`. -/
theorem mobilityRate_of_steps (hV : VelocityRateStep) (hC : ClockEstimateStep)
    (hS : CovarianceIdentityStep)
    (hRF : External.GMPReducedFamilyExistence) (hRV : External.GMPReducedVelocityExistence)
    (hTC : External.GMPTimeChangeLaw) (hPos : External.GMPPhysicalVelocityPositive)
    (hBounds : ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) (Q : EnvironmentLaw d Λ₀ r₀),
      euclideanNorm (abarE1 hd Q) ≤ sourceReducedBound Λ₀ ∧
        (sourceReducedBound Λ₀)⁻¹ ≤ meanMu Q ∧ meanMu Q ≤ sourceReducedBound Λ₀) :
    ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ), ∃ C lamStar : ℝ, 0 < lamStar ∧
      ∀ (Q : EnvironmentLaw d Λ₀ r₀) (P : DiffusionFamily d),
      IsGMPPhysicalFamily hd Q.ellipticity_parameter Q P →
      ∀ (covariance : Mat d), HasDiffusivity Q.measure (originLaw (P 0)) covariance →
      ∀ (lam : ℝ), 0 < lam → lam ≤ lamStar →
      ∀ (velocity : Vec d), HasQuenchedVelocity Q.measure (originLaw (P lam)) velocity →
      euclideanNorm ((lam⁻¹ • velocity) - covariance.mulVec (unitVector (⟨0, by omega⟩ : Fin d)))
        ≤ C * lam := by
  intro d hd Λ₀ r₀
  obtain ⟨C₁, lamV, hlamV, hlamV1, hV'⟩ := hV d hd Λ₀ r₀
  obtain ⟨C₂, lamC, hlamC, _, hC'⟩ := hC d hd Λ₀ r₀
  obtain ⟨Λ, hΛdef⟩ : ∃ Λ : ℝ, Λ = sourceReducedBound Λ₀ := ⟨_, rfl⟩
  refine ⟨Λ * C₁ + Λ ^ 3 * C₂, min lamV lamC, lt_min hlamV hlamC, ?_⟩
  intro Q P hP covariance hcov lam hlam0 hlam velocity hvel
  have hlamV' : lam ≤ lamV := hlam.trans (min_le_left _ _)
  have hlamC' : lam ≤ lamC := hlam.trans (min_le_right _ _)
  have hl1 : lam ≤ 1 := hlamV'.trans hlamV1
  have hΛ₀ : 1 ≤ Λ₀ := Q.ellipticity_parameter
  -- the reduced family and its velocity, the positivity of both first coordinates, and the
  -- time change between the physical and reduced origin laws
  obtain ⟨P', hP'⟩ := hRF d hd Λ₀ r₀ Q
  obtain ⟨vY, hvY, hvYpos⟩ := hRV d hd Λ₀ r₀ Q P' hP' lam hlam0 hl1
  have hvXpos : 0 < dot (unitVector (⟨0, by omega⟩ : Fin d)) velocity :=
    hPos d hd Λ₀ r₀ Q P hP lam hlam0 hl1 velocity hvel
  have hTC' := hTC d hd Λ₀ r₀ Q P P' hP hP'
  obtain ⟨hvX, hIcc⟩ := gmp_physical_velocity_eq_inv_clockRate_smul hd Q P P' hP hP' hTC'
    hlam0 hl1 hvel hvY hvXpos hvYpos
  obtain ⟨_, hlim⟩ := gmp_velocity_timeChange hd Q P P' hP hP' hTC' hlam0 hl1 hvel hvY hvXpos
  -- name the clock rate `η`, the ratio of the first coordinates of `vY` and `velocity`
  obtain ⟨η, hηdef⟩ : ∃ η : ℝ, η = dot (unitVector (⟨0, by omega⟩ : Fin d)) vY /
      dot (unitVector (⟨0, by omega⟩ : Fin d)) velocity := ⟨_, rfl⟩
  have hvX' : velocity = η⁻¹ • vY := by
    rw [hηdef]
    exact hvX
  have hIcc' : η ∈ Set.Icc (Real.exp (-2 * Λ₀)) (Real.exp (2 * Λ₀)) := by
    rw [hηdef]
    exact hIcc
  have hlim' : ∀ᵐ ω ∂Q.measure, ∀ᵐ γ ∂(P' lam (0, ω)),
      Tendsto (fun t : ℝ≥0 => (Clock.physicalPathClock ω γ t : ℝ) / t) atTop (𝓝 η) := by
    rw [hηdef]
    exact hlim
  have hvelRate : euclideanNorm (lam⁻¹ • vY - abarE1 hd Q) ≤ C₁ * lam :=
    hV' Q P' hP' lam hlam0 hlamV' vY hvY
  have hclock : |η - meanMu Q| ≤ C₂ * lam := hC' Q P' hP' lam hlam0 hlamC' η hlim'
  -- the ranges of `η`, `𝔼μ` and `ā e₁` inside `[Λ⁻¹, Λ]`
  obtain ⟨hA, hm1, hm2⟩ := hBounds d hd Λ₀ r₀ Q
  obtain ⟨hη1, hη2⟩ := Set.mem_Icc.mp hIcc'
  have hL1 : 1 ≤ Real.exp (2 * Λ₀) := Real.one_le_exp (by linarith)
  have hL0 : 0 < Real.exp (2 * Λ₀) := Real.exp_pos _
  have hLΛ : Real.exp (2 * Λ₀) ≤ Λ := by
    rw [hΛdef]
    unfold sourceReducedBound
    exact le_mul_of_one_le_right hL0.le (by nlinarith [sq_nonneg Λ₀])
  have hΛ1 : 1 ≤ Λ := hL1.trans hLΛ
  have hinvL : (Real.exp (2 * Λ₀))⁻¹ = Real.exp (-2 * Λ₀) := by
    rw [← Real.exp_neg, neg_mul]
  have hΛinv : Λ⁻¹ ≤ Real.exp (-2 * Λ₀) := by
    rw [← hinvL]
    exact inv_anti₀ hL0 hLΛ
  have hΛA : euclideanNorm (abarE1 hd Q) ≤ Λ := by
    rw [hΛdef]
    exact hA
  have hη : Λ⁻¹ ≤ η ∧ η ≤ Λ := ⟨hΛinv.trans hη1, hη2.trans hLΛ⟩
  have hm : Λ⁻¹ ≤ meanMu Q ∧ meanMu Q ≤ Λ := by
    rw [hΛdef]
    exact ⟨hm1, hm2⟩
  -- the covariance identity and the time change `velocity = η⁻¹ vY` give the assembled error
  rw [hS d hd Λ₀ r₀ Q P hP covariance hcov, Matrix.smul_mulVec,
    abar_mulVec_unitVector_zero hd Q, hvX']
  exact main_rate_assembly hlam0 hΛ1 hη hm hΛA hvelRate hclock

end EinsteinRelation
