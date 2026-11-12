import EinsteinRelation.Sharpness.SharpEnvironmentDischarge
import EinsteinRelation.Sharpness.SharpClockFromFukushima
import EinsteinRelation.Sharpness.SharpA11Limit

/-! # Proposition 7.1 with the remaining scalar-decomposition obligation explicit

Source: `paper/main.tex` 1212–1280. The velocity, clock and environment steps are proved from
white noise and the cited Fukushima/GMP inputs. The only internal hypothesis left below is
`SharpA11LimitStep`, discharged in the second theorem from Proposition 6.1
(`ScalarDecompositionTwin`). These conditional assemblies do not certify that proposition.
-/

open MeasureTheory Filter Topology
open scoped NNReal

namespace EinsteinRelation.Sharpness

private theorem sharp_dot_smul_left {d : ℕ} (c : ℝ) (x z : Vec d) :
    dot (c • x) z = c * dot x z := by
  simp only [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

private theorem sharp_dot_comm {d : ℕ} (x y : Vec d) : dot x y = dot y x := by
  unfold dot
  exact Finset.sum_congr rfl fun i _ => mul_comm (x i) (y i)

private theorem sharp_dot_unitVector_self {d : ℕ} (i : Fin d) :
    dot (unitVector i) (unitVector i) = 1 := by
  simp [dot, unitVector, Pi.single_apply]

/-- Proposition 7.1 from the cited inputs and the zero-force continuity of the diagonal
coefficient averages (`paper/main.tex` 1266–1267). All other sharpness steps are supplied by
proved theorems, for the same constructed environment and positive constant. -/
theorem sharpExample_of_a11Limit (d : ℕ) (hd : 2 ≤ d) (hW : External.WhiteNoiseExistence d)
    (hFOT : FukushimaDecompositionInput)
    (hRF : External.GMPReducedFamilyExistence) (hRV : External.GMPReducedVelocityExistence)
    (hPF : External.GMPPhysicalFamilyExistence) (hVX : External.GMPVelocityExistence)
    (hTC : External.GMPTimeChangeLaw) (hErg : External.GMPEnvironmentProcessErgodic)
    (hIP : External.GMPReducedInvarianceAbar) (hPos : External.GMPPhysicalVelocityPositive)
    (hLimit : SharpA11LimitStep hd) :
    ∃ (Λ₀ r₀ : ℝ) (Q : EnvironmentLaw d Λ₀ r₀),
    (∀ᵐ ω ∂Q.measure, IsSmoothFieldPair ω) ∧ ∃ c : ℝ, 0 < c ∧
    ∀ (P : DiffusionFamily d), IsGMPPhysicalFamily hd Q.ellipticity_parameter Q P →
    ∀ (covariance : Mat d), HasDiffusivity Q.measure (originLaw (P 0)) covariance →
    ∀ (velocity : ℝ → Vec d),
      (∀ lam : ℝ, 0 < lam → lam ≤ 1 →
        HasQuenchedVelocity Q.measure (originLaw (P lam)) (velocity lam)) →
      Tendsto (fun lam : ℝ =>
          dot ((lam⁻¹ • velocity lam) - covariance.mulVec (unitVector (⟨0, by omega⟩ : Fin d)))
            (unitVector (⟨0, by omega⟩ : Fin d)) / lam)
        (𝓝[>] (0 : ℝ)) (𝓝 c) := by
  obtain ⟨Λ₀, r₀, δ, Q, hsharp, hsmooth, hEnv⟩ :=
    exists_sharp_environmentLaw_with_input d hd hW
  have hδ := hsharp.1
  have hVel := sharpVelocityStep_of_fukushima hFOT hd
  have hClock := sharpClockIdentityStep_of_inputs hFOT hPF hTC hVX hPos hRV hd
  obtain ⟨-, -, hmean, hpos, hmu, hab⟩ := hEnv
  -- Positivity of the constant `c = δ (𝔼 a₁₁ - 1)`, which is `δ` times the positive sharp energy.
  have hc : 0 < δ * ((∫ ω, sharpA11 hd ω 0 ∂Q.measure) - 1) := by
    rw [hmean]
    exact mul_pos hδ hpos
  refine ⟨Λ₀, r₀, Q, hsmooth, δ * ((∫ ω, sharpA11 hd ω 0 ∂Q.measure) - 1), hc, ?_⟩
  intro P hP covariance hcov velocity hvel
  -- Covariance identity: `Σ_X = (𝔼μ)⁻¹ ā`, with `𝔼μ = 1` and `ā e₁ = e₁`.
  have hcovEq : covariance = (meanMu Q)⁻¹ • abar Q :=
    (covarianceIdentityStep_of_gmpInputs hRF hTC hErg hIP) d hd Λ₀ r₀ Q P hP covariance hcov
  have hcovE : covariance.mulVec (unitVector (⟨0, by omega⟩ : Fin d)) =
      unitVector (⟨0, by omega⟩ : Fin d) := by
    rw [hcovEq, hmu, inv_one, one_smul]
    exact hab
  -- The reduced family and the clock identity at every force.
  obtain ⟨P', hP'⟩ := hRF d hd Λ₀ r₀ Q
  have hAex : ∀ lam : ℝ, ∃ A : ℝ, 0 < lam → lam ≤ 1 → SharpClockAt hd δ Q P' lam A := by
    intro lam
    by_cases hlam : 0 < lam ∧ lam ≤ 1
    · obtain ⟨A, hA⟩ := hClock Λ₀ r₀ δ Q hsharp P' hP' lam hlam.1 hlam.2
      exact ⟨A, fun _ _ => hA⟩
    · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ hlam⟩
  choose A hA using hAex
  have hprob : ∀ lam : ℝ, 0 < lam → lam ≤ 1 →
      ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (P' lam (0, ω)) := by
    intro lam hl0 hl1
    filter_upwards [isProbabilityMeasure_of_isGMPReducedOriginLaw hd Q.ellipticity_parameter Q lam
      hl0.le hl1 (originLaw (P' lam))
      ((isGMPReducedFamily_iff hd Q.ellipticity_parameter Q P').1 hP' lam hl0.le hl1)] with ω hω
    simpa only [originLaw_apply] using hω
  -- The velocity relation `ℓ_X(λ)·e₁ = λ η(λ)⁻¹`, with `η(λ)` the clock identity's rate.
  have hkey : ∀ lam : ℝ, 0 < lam → lam ≤ 1 →
      dot (velocity lam) (unitVector (⟨0, by omega⟩ : Fin d)) =
        lam * (1 - δ * lam * (A lam - 1))⁻¹ := by
    intro lam hl0 hl1
    obtain ⟨vY, hvY, -⟩ := hRV d hd Λ₀ r₀ Q P' hP' lam hl0 hl1
    have hY1 : dot vY (unitVector (⟨0, by omega⟩ : Fin d)) = lam :=
      hVel Λ₀ r₀ δ Q hsharp P' hP' lam hl0 hl1 vY hvY
    -- `gmp_velocity_timeChange` states its clock rate with the unit vector on the left of `dot`.
    have hXpos : 0 < dot (unitVector (⟨0, by omega⟩ : Fin d)) (velocity lam) :=
      hPos d hd Λ₀ r₀ Q P hP lam hl0 hl1 (velocity lam) (hvel lam hl0 hl1)
    obtain ⟨-, hlim⟩ := gmp_velocity_timeChange hd Q P P' hP hP'
      (hTC d hd Λ₀ r₀ Q P P' hP hP') hl0 hl1 (hvel lam hl0 hl1) hvY hXpos
    obtain ⟨-, hAclock⟩ := hA lam hl0 hl1
    have hη : dot (unitVector (⟨0, by omega⟩ : Fin d)) vY /
        dot (unitVector (⟨0, by omega⟩ : Fin d)) (velocity lam) =
          1 - δ * lam * (A lam - 1) := by
      obtain ⟨ω, hωlim, hωclock, hωprob⟩ :=
        (hlim.and (hAclock.and (hprob lam hl0 hl1))).exists
      haveI := hωprob
      obtain ⟨γ, hγ1, hγ2⟩ := (hωlim.and hωclock).exists
      exact tendsto_nhds_unique hγ1 hγ2
    have hY1' : dot (unitVector (⟨0, by omega⟩ : Fin d)) vY = lam :=
      (sharp_dot_comm _ _).trans hY1
    rw [hY1'] at hη
    have hlne : lam ≠ 0 := hl0.ne'
    -- `hη` now reads `lam / X = η` for `X` the physical first coordinate, so `X = lam * η⁻¹`.
    rw [sharp_dot_comm, ← hη, inv_div, mul_div_assoc', mul_comm lam, mul_div_assoc,
      div_self hlne, mul_one]
  -- Scalar and vector limits.
  have hpos01 : Set.Ioc (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) := Ioc_mem_nhdsGT (by norm_num)
  have hlamT : Tendsto (fun lam : ℝ => lam) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have hAlim : Tendsto A (𝓝[>] (0 : ℝ)) (𝓝 (∫ ω, sharpA11 hd ω 0 ∂Q.measure)) :=
    hLimit Λ₀ r₀ δ Q hsharp P' hP' A (fun lam hl0 hl1 => (hA lam hl0 hl1).1)
  have hprodA : Tendsto (fun lam : ℝ => δ * lam * (A lam - 1)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h := (hlamT.const_mul δ).mul (hAlim.sub_const 1)
    rw [mul_zero, zero_mul] at h
    exact h
  have hT : Tendsto (fun lam : ℝ => 1 - δ * lam * (A lam - 1)) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have h := (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ)) (𝓝[>] (0 : ℝ)) (𝓝 1)).sub
      hprodA
    rw [sub_zero] at h
    exact h
  have hne : ∀ᶠ lam in 𝓝[>] (0 : ℝ), 1 - δ * lam * (A lam - 1) ≠ 0 :=
    hT.eventually_ne one_ne_zero
  have hE1 : dot (unitVector (⟨0, by omega⟩ : Fin d)) (unitVector (⟨0, by omega⟩ : Fin d)) = 1 :=
    sharp_dot_unitVector_self _
  have hvec := sharp_expansion_vector_limit hδ
    (fun lam : ℝ => if lam ≤ 1 then 1 - δ * lam * (A lam - 1) else 1) A
    (fun lam _ hl1 => if_pos hl1) hAlim
    (by
      filter_upwards [hpos01, hne] with lam h1 h2
      simp only [if_pos h1.2]
      exact h2)
    (unitVector (⟨0, by omega⟩ : Fin d))
    (fun lam : ℝ => if lam ≤ 1 then velocity lam else lam • unitVector (⟨0, by omega⟩ : Fin d))
    (fun lam hl0 => by
      by_cases hle : lam ≤ 1
      · simp only [if_pos hle]
        exact hkey lam hl0 hle
      · simp [hle, sharp_dot_smul_left, hE1])
    (unitVector (⟨0, by omega⟩ : Fin d)) hE1
  refine hvec.congr' ?_
  filter_upwards [hpos01] with lam hlam
  simp only [if_pos hlam.2, hcovE]

/-- Proposition 7.1 conditional on Proposition 6.1 and the listed cited inputs.
Source: `paper/main.tex` 1212–1280. The scalar decomposition is an internal proof obligation,
not an external assumption. -/
theorem sharpExample_of_scalarDecomposition (d : ℕ) (hd : 2 ≤ d)
    (hW : External.WhiteNoiseExistence d) (hFOT : FukushimaDecompositionInput)
    (H61 : ScalarDecompositionTwin)
    (hRF : External.GMPReducedFamilyExistence) (hRV : External.GMPReducedVelocityExistence)
    (hPF : External.GMPPhysicalFamilyExistence) (hVX : External.GMPVelocityExistence)
    (hTC : External.GMPTimeChangeLaw) (hErg : External.GMPEnvironmentProcessErgodic)
    (hIP : External.GMPReducedInvarianceAbar) (hPos : External.GMPPhysicalVelocityPositive) :
    ∃ (Λ₀ r₀ : ℝ) (Q : EnvironmentLaw d Λ₀ r₀),
    (∀ᵐ ω ∂Q.measure, IsSmoothFieldPair ω) ∧ ∃ c : ℝ, 0 < c ∧
    ∀ (P : DiffusionFamily d), IsGMPPhysicalFamily hd Q.ellipticity_parameter Q P →
    ∀ (covariance : Mat d), HasDiffusivity Q.measure (originLaw (P 0)) covariance →
    ∀ (velocity : ℝ → Vec d),
      (∀ lam : ℝ, 0 < lam → lam ≤ 1 →
        HasQuenchedVelocity Q.measure (originLaw (P lam)) (velocity lam)) →
      Tendsto (fun lam : ℝ =>
          dot ((lam⁻¹ • velocity lam) - covariance.mulVec (unitVector (⟨0, by omega⟩ : Fin d)))
            (unitVector (⟨0, by omega⟩ : Fin d)) / lam)
        (𝓝[>] (0 : ℝ)) (𝓝 c) := by
  exact sharpExample_of_a11Limit d hd hW hFOT hRF hRV hPF hVX hTC hErg hIP hPos
    (sharpA11LimitStep_of_scalarDecomposition H61 hd)

end EinsteinRelation.Sharpness
