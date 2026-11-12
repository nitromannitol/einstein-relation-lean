import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
import Mathlib.Probability.ConditionalProbability
import EinsteinRelationAudit.MobilityRate.Vocabulary.Diffusion.Basic
import EinsteinRelationAudit.MobilityRate.Vocabulary.Diffusion.GMPFamily
import EinsteinRelationAudit.MobilityRate.Vocabulary.Regeneration.Construction
import EinsteinRelationAudit.MobilityRate.Vocabulary.Regeneration.Coupling

/-! Restated from the library module `EinsteinRelation.Regeneration.RenewalCarriers`:
the declarations of that module that the statement of
`EinsteinRelationAudit.MobilityRate.mobility_rate` depends on, in their module context. -/

open MeasureTheory
open scoped NNReal ENNReal
noncomputable section
namespace EinsteinRelation.Regeneration.Renewal
/-- The force coordinate `e₁`, the index zero of `Fin d` (`regen.hitting`, `regen.D`,
paper/main.tex lines 285–311). -/
def forceCoord {d : ℕ} (hd : 2 ≤ d) : Fin d := ⟨0, by omega⟩
/-- The grid spacing `Δ = λ⁻²` (`regen.scales`, paper/main.tex lines 266–268), as the
nonnegative real that the construction takes. -/
noncomputable def regenDelta (lam : ℝ) : ℝ≥0 := Real.toNNReal ((lam ^ 2)⁻¹)
/-- The `k`-th cycle record `𝒴_k` (`regen.future`, paper/main.tex lines 337–346): the
output of `futureRecord` at the `k`-th regeneration time `τ_k` (`regen.times`, lines
318–321), with radius `R = l / λ`. `cycleRecord hd lam l 0` is `𝒴_0`, since `τ_0 = 0`.
Where `τ_k = ∞` the value is the record at time zero. That set is null, because
`τ_k < ∞` almost surely by `regen.tails` (lines 329–335). -/
noncomputable def cycleRecord {d : ℕ} (hd : 2 ≤ d) (lam l : ℝ) (k : ℕ)
    (ωz : FieldPair d × CoupledSample d) : FutureState d (forceCoord hd) (l / lam) :=
  futureRecord (regenDelta lam) (l / lam) ωz.1 ωz.2 (forceCoord hd)
    (regenerationTime (regenDelta lam) lam (l / lam) ωz.2 (forceCoord hd) k).toNNReal
/-- The killed diffusion segment from `z` in environment `ω` (paper/main.tex line 383): the
quenched law `P (z, ω)` restricted to the paths that stay in `U^z` on `[0, Δ]`, where
`U^z = couplingRegion i R z` (line 268). -/
noncomputable def killedSegmentLaw {d : ℕ} (Δ : ℝ≥0) (R : ℝ) (i : Fin d)
    (P : QuenchedPathLaws d) (z : Vec d) (ω : FieldPair d) : Measure (Path d) :=
  (P (z, ω)).restrict {γ : Path d | ∀ t : ℝ≥0, t ≤ Δ → γ t ∈ couplingRegion i R z}
/-- The mixture of diffusion bridges killed upon leaving `U^z`, with endpoint uniform on
`B^z = endpointBall i R z` (paper/main.tex line 383, with line 268). Its bridges are the
disintegration of `killedSegmentLaw` over the endpoint `γ Δ`. The mixture is the
reweighting of the killed segment whose endpoint law is the uniform law
`ProbabilityTheory.cond volume B^z`, so its integral of a segment functional is the uniform
average of the bridge expectations. -/
noncomputable def killedBridgeMixture {d : ℕ} (Δ : ℝ≥0) (R : ℝ) (i : Fin d)
    (P : QuenchedPathLaws d) (z : Vec d) (ω : FieldPair d) : Measure (Path d) :=
  (killedSegmentLaw Δ R i P z ω).withDensity fun γ : Path d =>
    (ProbabilityTheory.cond (volume : Measure (Vec d)) (endpointBall i R z)).rnDeriv
      ((killedSegmentLaw Δ R i P z ω).map fun γ' : Path d => γ' Δ) (γ Δ)
/-- One-interval kernel at one starting point (paper/main.tex line 383, the one-interval
description in Step 2). Let `z = Y_{nΔ}`, and let `F` be a bounded measurable
functional of the path on `[0, Δ]`, applied to the shift at `nΔ`. Let `H` be bounded and
measurable for the finite history `finiteHistorySigma Δ n`, which is the path through `nΔ`
and the bits before `n`. On `{β_n = 1}` the segment law from `z` is `killedBridgeMixture`.
On `{β_n = 0}` it is `(unrestricted diffusion − δ · mixture) / (1 − δ)`. Multiplying the
second by `P(β_n = 0 | past) = 1 − δ` (line 272) gives the second identity. Each identity
is preceded by the integrability of its integrands under `K xω` (for the second identity also
of the `P`-integral term), so the identities do not hold vacuously when a Bochner integral
defaults to zero. -/
def OneIntervalKernelAt {d : ℕ} (Δ : ℝ≥0) (δ R : ℝ) (i : Fin d)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d) (xω : Vec d × FieldPair d) : Prop :=
  ∀ (n : ℕ) (H : CoupledSample d → ℝ) (F : Path d → ℝ),
    @Measurable (CoupledSample d) ℝ (finiteHistorySigma Δ n) inferInstance H →
    BoundedRealTest H → Measurable F → BoundedRealTest F →
    (∀ γ γ' : Path d, (∀ t : ℝ≥0, t ≤ Δ → γ t = γ' t) → F γ = F γ') →
    Integrable (fun z : CoupledSample d =>
        H z * (if z.2 n = true then (1 : ℝ) else 0) * F (pathTimeShift z.1 ((n : ℝ≥0) * Δ)))
      (K xω) ∧
    Integrable (fun z : CoupledSample d =>
        H z * (∫ γ, F γ ∂(killedBridgeMixture Δ R i P (z.1 ((n : ℝ≥0) * Δ)) xω.2)))
      (K xω) ∧
    (∫ z, H z * (if z.2 n = true then (1 : ℝ) else 0) *
        F (pathTimeShift z.1 ((n : ℝ≥0) * Δ)) ∂K xω) =
      δ * (∫ z, H z *
        (∫ γ, F γ ∂(killedBridgeMixture Δ R i P (z.1 ((n : ℝ≥0) * Δ)) xω.2)) ∂K xω) ∧
    Integrable (fun z : CoupledSample d =>
        H z * (if z.2 n = true then (0 : ℝ) else 1) * F (pathTimeShift z.1 ((n : ℝ≥0) * Δ)))
      (K xω) ∧
    Integrable (fun z : CoupledSample d =>
        H z * ((∫ γ, F γ ∂(P (z.1 ((n : ℝ≥0) * Δ), xω.2))) -
          δ * (∫ γ, F γ ∂(killedBridgeMixture Δ R i P (z.1 ((n : ℝ≥0) * Δ)) xω.2))))
      (K xω) ∧
    Integrable (fun z : CoupledSample d =>
        H z * (∫ γ, F γ ∂(P (z.1 ((n : ℝ≥0) * Δ), xω.2))))
      (K xω) ∧
    (∫ z, H z * (if z.2 n = true then (0 : ℝ) else 1) *
        F (pathTimeShift z.1 ((n : ℝ≥0) * Δ)) ∂K xω) =
      (∫ z, H z *
        ((∫ γ, F γ ∂(P (z.1 ((n : ℝ≥0) * Δ), xω.2))) -
          δ * (∫ γ, F γ ∂(killedBridgeMixture Δ R i P (z.1 ((n : ℝ≥0) * Δ)) xω.2)))
        ∂K xω)
/-- The one-interval kernel structure of the coupled law, at the origin and product-a.e.,
in the form used by the other coupling predicates (paper/main.tex lines 383–384). -/
def HasOneIntervalKernel {d : ℕ} (Q : Measure (FieldPair d)) (Δ : ℝ≥0) (δ R : ℝ)
    (i : Fin d) (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d) : Prop :=
  (∀ᵐ ω ∂Q, OneIntervalKernelAt Δ δ R i P K (0, ω)) ∧
  ∀ᵐ xω ∂((volume : Measure (Vec d)).prod Q), OneIntervalKernelAt Δ δ R i P K xω
/-- The coupling of Gantert–Mathieu–Piatnitski (2012), Proposition 5.4 (p. 23), with the
environment law `Q`. The diffusion is the GMP Section 7 process. Section 7 carries
the regeneration construction of Section 5 and its upper bounds on `τ₁` (Lemmas 5.7 and 5.8,
pp. 25–26) to measurable coefficients: "the construction of regeneration times we gave in
Section 5 and all the upper bounds on τ₁ are still valid with measurable coefficients" (p. 32).
The one-interval kernel is the kernel form of Shen (2003), Theorem 2.1, equations (2.8)–(2.9),
pp. 844–845. Validity for
measurable coefficients rests on the GMP p. 32 extension, not on Shen's Lipschitz hypotheses.
The conjuncts are those of `IsGMPCoupling`, read on `Q.measure`, except that the product-a.e.
reduced martingale law is replaced by `IsGMPReducedKernel`, which identifies the reduced
quenched kernel with the path law of a GMP Section 7 realization of the zero-potential pair
from every starting point. -/
def IsGMPCouplingV2 {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (hΛ₀ : 1 ≤ Λ₀)
    (Q : EnvironmentLaw d Λ₀ r₀) (lam l δ : ℝ) (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d) : Prop :=
  HasProbabilityLaws Q.measure K ∧
  HasPathMarginals Q.measure K P ∧
  IsGMPReducedKernel hd hΛ₀ Q lam hl0 hl1 P ∧
  HasFreshBits Q.measure (regenDelta lam) δ K ∧
  HasDeterministicRestart Q.measure (regenDelta lam) K ∧
  HasSuccessfulBridgeSupport Q.measure (regenDelta lam) (forceCoord hd) (l / lam) K ∧
  HasUniformSuccessfulEndpoint Q.measure (regenDelta lam) δ (l / lam) (forceCoord hd) K ∧
  HasOneIntervalKernel Q.measure (regenDelta lam) δ (l / lam) (forceCoord hd) P K
end EinsteinRelation.Regeneration.Renewal
end
