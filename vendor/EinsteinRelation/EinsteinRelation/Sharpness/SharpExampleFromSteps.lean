import EinsteinRelation.Sharpness.SharpPhysicalLaw
import EinsteinRelation.Sharpness.ExpansionLimit
import EinsteinRelation.Sharpness.ConstantPositive
import EinsteinRelation.Mobility.CovarianceIdentityStepProof
import EinsteinRelation.Diffusion.VelocityTimeChangeGMP
import EinsteinRelation.External.GMPReducedInputs
import EinsteinRelation.External.GMPPhysicalInputs

/-! # The sharpness example (Proposition 7.1) from its step propositions

Source `paper/main.tex` 1202–1270. The sharp environment law `Q` is the image of a white-noise
law under the physical pair (`exists_sharp_environmentLaw`). This file states the three
stochastic-calculus steps of the proof as propositions about that law and its GMP reduced family,
and assembles the conclusion of Proposition 7.1 from them:

* the covariance identity `Σ_X = (𝔼μ)⁻¹ ā`, with `𝔼μ = 1` and `ā e₁ = e₁`;
* the velocity relation `ℓ_X(λ)·e₁ = λ η(λ)⁻¹`, from the GMP velocity time change;
* the clock identity `η(λ) = 1 - δ λ (A(λ) - 1)` with `A(λ) → 𝔼 a₁₁`;
* the scalar and vector limits `sharp_expansion_scalar_limit` and `sharp_expansion_vector_limit`,
  giving the constant `c = δ (𝔼 a₁₁ - 1) > 0`.

The environment-level facts of the sharp law that the three steps do not supply are carried by
`SharpEnvironmentInput`, stated for the local gradient field `sharpLocalGradient`. The sign of the
physical velocity is the cited input `External.GMPPhysicalVelocityPositive`.
-/

open MeasureTheory Filter Topology
open scoped NNReal

namespace EinsteinRelation.Sharpness

/-- The `(0,0)` entry `a₁₁` of the reduced coefficient at a spatial point. -/
noncomputable def sharpA11 {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (x : Vec d) : ℝ :=
  reducedCoefficient ω x ⟨0, by omega⟩ ⟨0, by omega⟩

/-- The running time average `t⁻¹ ∫₀ᵗ a₁₁(Y_u) du` of `a₁₁` along a path. -/
noncomputable def sharpTimeAverageA11 {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (γ : Path d)
    (t : ℝ≥0) : ℝ :=
  (∫ u in (0 : ℝ)..(t : ℝ), sharpA11 hd ω (γ u.toNNReal)) / (t : ℝ)

/-- The environment law `Q` is the law of the sharpness pair of Step 1: the image of a white-noise
law under the physical pair built from scales `δ, ε > 0`. -/
def IsSharpLaw {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (δ : ℝ) (Q : EnvironmentLaw d Λ₀ r₀) : Prop :=
  0 < δ ∧ ∃ (ε : ℝ) (P : Measure (NoiseSample d))
    (hgrad : ∀ (W : NoiseSample d) (x : Vec d),
      euclideanNorm (gradient (fun y => ε * seedField d W y) x) ≤ (1 / 4 : ℝ))
    (hμ : ∀ (W : NoiseSample d) (x : Vec d),
      (3 / 4 : ℝ) ≤ densityField ⟨0, by omega⟩ δ (fun y => ε * seedField d W y) x ∧
      densityField ⟨0, by omega⟩ δ (fun y => ε * seedField d W y) x ≤ (5 / 4 : ℝ)),
    0 < ε ∧ Q.measure = P.map (sharpPhysicalPair ⟨0, by omega⟩ δ ε hgrad hμ)

/-- The clock identity at one force `λ` for the reduced family `P'`, with time-average limit `A`.
Almost surely, the time averages of `a₁₁` along the reduced path converge to `A`, and the clock
rate `t⁻¹ ∫ μ` of the physical time change converges to `1 - δ λ (A - 1)`. -/
def SharpClockAt {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (δ : ℝ) (Q : EnvironmentLaw d Λ₀ r₀)
    (P' : DiffusionFamily d) (lam A : ℝ) : Prop :=
  (∀ᵐ ω ∂Q.measure, ∀ᵐ γ ∂(P' lam (0, ω)),
      Tendsto (fun t : ℝ≥0 => sharpTimeAverageA11 hd ω γ t) atTop (𝓝 A)) ∧
    (∀ᵐ ω ∂Q.measure, ∀ᵐ γ ∂(P' lam (0, ω)),
      Tendsto (fun t : ℝ≥0 => (Clock.physicalPathClock ω γ t : ℝ) / (t : ℝ)) atTop
        (𝓝 (1 - δ * lam * (A - 1))))

/-- Step 2 of Proposition 7.1 (`paper/main.tex` 1234–1240). For the sharp law `Q` and every GMP
reduced family `P'`, each reduced quenched velocity at force `0 < λ ≤ 1` has first coordinate `λ`. -/
def SharpVelocityStep {d : ℕ} (hd : 2 ≤ d) : Prop :=
  ∀ (Λ₀ r₀ δ : ℝ) (Q : EnvironmentLaw d Λ₀ r₀), IsSharpLaw hd δ Q →
    ∀ P' : DiffusionFamily d, IsGMPReducedFamily hd Q.ellipticity_parameter Q P' →
    ∀ lam : ℝ, 0 < lam → lam ≤ 1 → ∀ v : Vec d,
      HasQuenchedVelocity Q.measure (originLaw (P' lam)) v →
      dot v (unitVector (⟨0, by omega⟩ : Fin d)) = lam

/-- Step 3 of Proposition 7.1, eq. `sharp-clock` (`paper/main.tex` 1245–1257). For the sharp law
and every GMP reduced family, each force `0 < λ ≤ 1` has a deterministic time-average limit
`A(λ)` of `a₁₁`, and the clock identity `SharpClockAt` holds with this `A(λ)`. -/
def SharpClockIdentityStep {d : ℕ} (hd : 2 ≤ d) : Prop :=
  ∀ (Λ₀ r₀ δ : ℝ) (Q : EnvironmentLaw d Λ₀ r₀), IsSharpLaw hd δ Q →
    ∀ P' : DiffusionFamily d, IsGMPReducedFamily hd Q.ellipticity_parameter Q P' →
    ∀ lam : ℝ, 0 < lam → lam ≤ 1 → ∃ A : ℝ, SharpClockAt hd δ Q P' lam A

/-- End of Step 3 of Proposition 7.1 (`paper/main.tex` 1256–1257). If the time averages of `a₁₁`
along the reduced paths converge to `A(λ)` for every `0 < λ ≤ 1`, then `A(λ) → 𝔼 a₁₁` as
`λ ↓ 0`. -/
def SharpA11LimitStep {d : ℕ} (hd : 2 ≤ d) : Prop :=
  ∀ (Λ₀ r₀ δ : ℝ) (Q : EnvironmentLaw d Λ₀ r₀), IsSharpLaw hd δ Q →
    ∀ P' : DiffusionFamily d, IsGMPReducedFamily hd Q.ellipticity_parameter Q P' →
    ∀ A : ℝ → ℝ,
      (∀ lam : ℝ, 0 < lam → lam ≤ 1 → ∀ᵐ ω ∂Q.measure, ∀ᵐ γ ∂(P' lam (0, ω)),
        Tendsto (fun t : ℝ≥0 => sharpTimeAverageA11 hd ω γ t) atTop (𝓝 (A lam))) →
      Tendsto A (𝓝[>] (0 : ℝ)) (𝓝 (∫ ω, sharpA11 hd ω 0 ∂Q.measure))

/-- The local gradient field of the sharp law at the origin, `G(w) = a(w)⁻¹ e₁ - e₁`, where
`a(w) = reducedCoefficient w 0`. Since `a(w) (e₁ + G(w)) = e₁`, the field `G` is the rank-one
coefficient's gradient at `0`, and it is a function of the environment itself, with no stationary
scalar potential needed. -/
noncomputable def sharpLocalGradient {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) : Vec d :=
  ((reducedCoefficient ω 0)⁻¹).mulVec (unitVector (⟨0, by omega⟩ : Fin d)) -
    unitVector (⟨0, by omega⟩ : Fin d)

/-- Environment-level facts of the sharp law beyond the three steps, for the local gradient field
`sharpLocalGradient`. Its values have Euclidean norm at most `1/4` almost surely. The Step 4
identity `𝔼 a₁₁ - 1 = 𝔼 [|G|² / (1 + G₁)]` holds, since `a₁₁ = 1 - G₁ + |G|² / (1 + G₁)` and
`𝔼 G₁ = 0`. This energy is strictly positive. The clock density has mean one, `meanMu Q = 1`, and
the reduced flux column is the unit vector, `ā e₁ = e₁`. -/
def SharpEnvironmentInput {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) : Prop :=
  Measurable (sharpLocalGradient hd) ∧
    (∀ᵐ ω ∂Q.measure, euclideanNorm (sharpLocalGradient hd ω) ≤ 1 / 4) ∧
    ((∫ ω, sharpA11 hd ω 0 ∂Q.measure) - 1 =
      ∫ ω, sharpEnergy (⟨0, by omega⟩ : Fin d) (sharpLocalGradient hd ω) ∂Q.measure) ∧
    0 < ∫ ω, sharpEnergy (⟨0, by omega⟩ : Fin d) (sharpLocalGradient hd ω) ∂Q.measure ∧
    meanMu Q = 1 ∧
    (abar Q).mulVec (unitVector (⟨0, by omega⟩ : Fin d)) = unitVector (⟨0, by omega⟩ : Fin d)

private theorem sharp_dot_smul_left {d : ℕ} (c : ℝ) (x z : Vec d) :
    dot (c • x) z = c * dot x z := by
  simp only [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

private theorem sharp_dot_comm {d : ℕ} (x y : Vec d) : dot x y = dot y x := by
  unfold dot
  exact Finset.sum_congr rfl fun i _ => mul_comm (x i) (y i)

private theorem sharp_dot_unitVector_self {d : ℕ} (i : Fin d) :
    dot (unitVector i) (unitVector i) = 1 := by
  simp [dot, unitVector, Pi.single_apply]

/-- Proposition 7.1 (`paper/main.tex` 1202–1209), assembled from the three step propositions, the
white-noise input, the GMP inputs of the covariance and velocity time-change theorems, the physical
velocity sign, and the environment-level facts of the sharp law. -/
theorem sharpExample_of_steps (d : ℕ) (hd : 2 ≤ d) (hW : External.WhiteNoiseExistence d)
    (hRF : External.GMPReducedFamilyExistence) (hRV : External.GMPReducedVelocityExistence)
    (hTC : External.GMPTimeChangeLaw) (hErg : External.GMPEnvironmentProcessErgodic)
    (hIP : External.GMPReducedInvarianceAbar)
    (hVel : SharpVelocityStep hd) (hClock : SharpClockIdentityStep hd)
    (hLimit : SharpA11LimitStep hd) (hPos : External.GMPPhysicalVelocityPositive)
    (hEnv : ∀ (Λ₀ r₀ δ : ℝ) (Q : EnvironmentLaw d Λ₀ r₀), IsSharpLaw hd δ Q →
      SharpEnvironmentInput hd Q) :
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
  obtain ⟨Λ₀, r₀, δ, ε, P₀, Q, hgrad, hμ, hδ, hε, hQ, hsmooth⟩ :=
    exists_sharp_environmentLaw d hd hW
  have hsharp : IsSharpLaw hd δ Q := by
    unfold IsSharpLaw
    exact ⟨hδ, ε, P₀, hgrad, hμ, hε, hQ⟩
  obtain ⟨-, -, hmean, hpos, hmu, hab⟩ := hEnv Λ₀ r₀ δ Q hsharp
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

end EinsteinRelation.Sharpness
