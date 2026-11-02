import EinsteinFull.Frozen.HomogenizedCoefficient

namespace EinsteinFull

open EinsteinRelation

/-- The actual unforced commutator Xi_{ji}=(a-A)_{jk}(delta_{ki}+D_k phi_i),
on the reduced environment. No representative is selected by choice here. -/
noncomputable def commutatorObservation {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (j i : Fin d) (ω : FieldPair d) : ℝ :=
  ∑ k : Fin d, (ω.1 0 j k - homogenizedCoefficient Q j k) *
    ((unitVector i) k + correctorGradient Q i ω k)

end EinsteinFull
