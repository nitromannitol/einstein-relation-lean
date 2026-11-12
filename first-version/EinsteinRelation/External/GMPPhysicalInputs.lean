import EinsteinRelation.Diffusion.GMPFamily
import EinsteinRelation.Diffusion.Velocity

/-! # Cited inputs for the GMP Section 7 physical diffusion family

Four named propositions, one for each cited input of the physical diffusion family
`IsGMPPhysicalFamily`. That family is bound to the fixed-environment realizations of the
heat-kernel construction of Gantert, Mathieu and Piatnitski (2012, Comm. Pure Appl. Math. 65),
Section 7. Each proposition quantifies over every dimension `2 ≤ d` and every environment law
`Q : EnvironmentLaw d Λ₀ r₀`; the regularity hypothesis of `IsGMPPhysicalFamily` is supplied by
the field `Q.ellipticity_parameter : 1 ≤ Λ₀`, and the force direction is the first coordinate
`e₁`. These propositions are externally cited inputs and are not proved in this development.
-/

open MeasureTheory

namespace EinsteinRelation.External

/-- Existence of a physical diffusion family of the GMP Section 7 form (Gantert, Mathieu and
Piatnitski 2012, Section 7, p. 32). The Feller semigroup of the weak operator is a conservative
Hunt process with continuous paths, and the annealed law is (2.5), p. 4. -/
def GMPPhysicalFamilyExistence : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) (Q : EnvironmentLaw d Λ₀ r₀),
    ∃ P : DiffusionFamily d, IsGMPPhysicalFamily hd Q.ellipticity_parameter Q P

/-- Invariance principle for the GMP Section 7 physical family at zero force (Gantert, Mathieu
and Piatnitski 2012, Definition 2.1, p. 4, and Section 7, p. 32, citing [20] Proposition 1). The
annealed form stated here is the one the cited quenched principle yields for the origin law
`P 0`. -/
def GMPDiffusivityExistence : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) (Q : EnvironmentLaw d Λ₀ r₀) (P : DiffusionFamily d),
    IsGMPPhysicalFamily hd Q.ellipticity_parameter Q P →
    ∃ covariance : Mat d, HasDiffusivity Q.measure (originLaw (P 0)) covariance

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
