import EinsteinRelationAudit.SharpExample.Vocabulary.Diffusion.Basic
import EinsteinRelationAudit.SharpExample.Vocabulary.Diffusion.GMPFamily

/-! Restated from the library module `EinsteinRelation.External.GMPPhysicalInputs`:
the declarations of that module that the statement of
`EinsteinRelationAudit.SharpExample.mobility_rate_sharp` depends on, in their module context. -/

open MeasureTheory
namespace EinsteinRelation.External
/-- Existence of a physical diffusion family of the GMP Section 7 form (Gantert, Mathieu and
Piatnitski 2012, Section 7, p. 32). The Feller semigroup of the weak operator is a conservative
Hunt process with continuous paths, and the annealed law is (2.5), p. 4. -/
def GMPPhysicalFamilyExistence : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) (Q : EnvironmentLaw d Λ₀ r₀),
    ∃ P : DiffusionFamily d, IsGMPPhysicalFamily hd Q.ellipticity_parameter Q P
/-- Law of large numbers for the GMP Section 7 physical family with force `0 < lam ≤ 1` (Gantert,
Mathieu and Piatnitski 2012, Section 2.3, p. 5, citing Shen [25]; Section 7, p. 32). -/
def GMPVelocityExistence : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) (Q : EnvironmentLaw d Λ₀ r₀) (P : DiffusionFamily d),
    IsGMPPhysicalFamily hd Q.ellipticity_parameter Q P →
    ∀ lam : ℝ, 0 < lam → lam ≤ 1 → ∃ v : Vec d, HasQuenchedVelocity Q.measure (originLaw (P lam)) v
/-- Positive first velocity component of the GMP Section 7 physical family (Gantert, Mathieu and
Piatnitski 2012, Section 2.3, p. 5). Every quenched velocity `ℓ(lam)` at force `0 < lam ≤ 1`
satisfies `λ̂ · ℓ(lam) > 0` with `λ̂ = lam e₁`, that is, `0 < e₁ · ℓ(lam)`. -/
def GMPPhysicalVelocityPositive : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) (Q : EnvironmentLaw d Λ₀ r₀) (P : DiffusionFamily d),
    IsGMPPhysicalFamily hd Q.ellipticity_parameter Q P →
    ∀ lam : ℝ, 0 < lam → lam ≤ 1 → ∀ v : Vec d,
      HasQuenchedVelocity Q.measure (originLaw (P lam)) v →
        0 < dot (unitVector (⟨0, by omega⟩ : Fin d)) v
end EinsteinRelation.External
