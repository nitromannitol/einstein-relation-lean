import EinsteinFull.Calculus.SbxAKMGrowthFromRemainderR09
import EinsteinFull.Calculus.SbxAUniformKMAssemblerR07

open MeasureTheory
open scoped NNReal ENNReal Topology
noncomputable section
namespace EinsteinFull.Blueprint.SbxAKMSemigroupAssociationR10
open EinsteinRelation
open EinsteinFull.Blueprint.SbxAKMGrowthFromRemainderR09
open EinsteinFull.Blueprint.SbxAUniformKMAssemblerR07

/-- The original remainder estimate gives a uniform endpoint moment threshold
for identifying the semigroup pairing with the supplied coupled covariance. -/
theorem a_uniform_supplied_covariance_eq_semigroup_of_remainder
    (hrem : node_rt_u3A_remainder_u2D_momentStmt) :
    ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) (hΛ : 1 ≤ Λ₀) (hr : 1 ≤ r₀),
    ∃ l₀ p : ℝ, 0 < l₀ ∧ r₀ < 2 * l₀ ∧ 2 ≤ p ∧
    ∀ (β : ℕ → ℝ) (hβ : ∀ k, 1 ≤ k → 0 < β k),
    let D : StructuralData d := ⟨Λ₀, r₀, β, hΛ, hr, hβ⟩
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange), HasSmoothBounds D Q →
    ∀ (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
      (l δ : ℝ), l₀ ≤ l → 0 < δ → δ < 1 →
    ∀ (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
      (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
      (_hD : Regeneration.annealedCoupledLaw Q.measure K
        (regenerationNoReturn hd (l / lam)) ≠ 0)
      (S : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
    IsComplexEnvironmentSemigroup Q (Regeneration.Renewal.forceCoord hd) (lam : ℂ) S →
    ∀ F G : Lp ℂ 2 (reducedLaw Q),
    MemLp (G : FieldPair d → ℂ) (ENNReal.ofReal (2 * p)) (reducedLaw Q) →
    ∀ t : ℝ≥0,
    Integrable (fun w => F (reduce w.1) * G (sbxS4CoupledEndpoint t w))
      (Regeneration.annealedCoupledLaw Q.measure K) ∧
    (∫ ω, F ω * S t G ω ∂reducedLaw Q) =
      ∫ w, F (reduce w.1) * G (sbxS4CoupledEndpoint t w)
        ∂Regeneration.annealedCoupledLaw Q.measure K := by
  intro d hd Λ₀ r₀ hΛ hr
  obtain ⟨l₀, p, C, hl₀, hsep, hp, hC, hgrowth⟩ :=
    a_uniform_coupled_endpoint_memLp_two_of_remainder hrem d hd Λ₀ r₀ hΛ hr
  refine ⟨l₀, p, hl₀, hsep, hp, ?_⟩
  intro β hβ
  dsimp only
  intro Q hQ lam h₀ h₁ l δ hl hδ₀ hδ₁ P K hK hD S hS F G hGp t
  have hGp' : MemLp (G : FieldPair d → ℂ) (2 * ENNReal.ofReal p) (reducedLaw Q) := by
    simpa only [ENNReal.ofReal_mul (show (0 : ℝ) ≤ 2 by norm_num), ENNReal.ofReal_ofNat] using hGp
  have hend := (hgrowth β hβ Q hQ lam h₀ h₁ l δ hl hδ₀ hδ₁ P K hK hD G
    (Lp.stronglyMeasurable G).measurable hGp' t).1
  have hint := (sbxS4_L2_pairing_eq_supplied hd Q lam l δ h₀.le h₁ P K hK t
    (Lp.memLp F) (Lp.stronglyMeasurable G).measurable hend).1
  refine ⟨hint, ?_⟩
  rw [hS.eq_forcedComplexEvolution]
  exact supplied_covariance_eq_forced_of_endpoint_memLp hd Q lam l δ h₀.le h₁ P K hK t F G hend

#print axioms a_uniform_supplied_covariance_eq_semigroup_of_remainder

end EinsteinFull.Blueprint.SbxAKMSemigroupAssociationR10
