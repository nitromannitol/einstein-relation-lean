import EinsteinRelation.Diffusion.Basic

/-! # Uniqueness of the deterministic quenched velocity

The almost-sure limit for almost every environment determines one vector. These
lemmas do not assert the law of large numbers; its existence input is separate.
-/

open MeasureTheory

namespace EinsteinRelation

theorem HasQuenchedVelocity.unique {d : ℕ} {Q : Measure (FieldPair d)}
    [IsProbabilityMeasure Q] {P : ProbabilityTheory.Kernel (FieldPair d) (Path d)}
    (hP : ∀ᵐ ω ∂Q, IsProbabilityMeasure (P ω)) {v w : Vec d}
    (hv : HasQuenchedVelocity Q P v) (hw : HasQuenchedVelocity Q P w) : v = w := by
  obtain ⟨ω, hωP, hωv, hωw⟩ := (hP.and (hv.and hw)).exists
  letI : IsProbabilityMeasure (P ω) := hωP
  obtain ⟨γ, hγv, hγw⟩ := (hωv.and hωw).exists
  exact hγv.unique hγw

/-- A genuine law of large numbers supplies existence; the limit is then unique. -/
theorem existsUnique_quenchedVelocity_of_exists {d : ℕ} {Q : Measure (FieldPair d)}
    [IsProbabilityMeasure Q] {P : ProbabilityTheory.Kernel (FieldPair d) (Path d)}
    (hP : ∀ᵐ ω ∂Q, IsProbabilityMeasure (P ω))
    (hex : ∃ v : Vec d, HasQuenchedVelocity Q P v) :
    ∃! v : Vec d, HasQuenchedVelocity Q P v := by
  obtain ⟨v, hv⟩ := hex
  exact ⟨v, hv, fun w hw => hw.unique hP hv⟩

/-- The actual martingale problem supplies the nonzero probability laws needed
for uniqueness; the almost-sure velocity statement alone would be vacuous for
a zero kernel. Source: `eq.velocity-definition`, `paper/main.tex:86–91`. -/
theorem IsPhysicalDiffusionFamily.probability {d : ℕ} {Λ₀ r₀ : ℝ} {i : Fin d}
    {Q : EnvironmentLaw d Λ₀ r₀} {P : DiffusionFamily d}
    (hP : IsPhysicalDiffusionFamily i Q P) {lam : ℝ} (hlam : 0 ≤ lam) :
    ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw (P lam) ω) := by
  filter_upwards [hP lam hlam] with ω hω
  exact hω.1

/-- Deterministic velocities of one physical diffusion family agree. -/
theorem IsPhysicalDiffusionFamily.velocity_unique {d : ℕ} {Λ₀ r₀ : ℝ}
    {i : Fin d} {Q : EnvironmentLaw d Λ₀ r₀} {P : DiffusionFamily d}
    (hP : IsPhysicalDiffusionFamily i Q P) {lam : ℝ} (hlam : 0 ≤ lam)
    {v w : Vec d}
    (hv : HasQuenchedVelocity Q.measure (originLaw (P lam)) v)
    (hw : HasQuenchedVelocity Q.measure (originLaw (P lam)) w) : v = w := by
  letI : IsProbabilityMeasure Q.measure := Q.probability
  exact HasQuenchedVelocity.unique (hP.probability hlam) hv hw

end EinsteinRelation
