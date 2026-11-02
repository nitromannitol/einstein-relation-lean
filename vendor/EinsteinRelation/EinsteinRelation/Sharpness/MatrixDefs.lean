import EinsteinRelation.Environment.Basic

/-! # Rank-one matrices for the sharpness construction

Literal finite-dimensional algebra from `paper/main.tex`, `eq.sharp-map` and
`eq.sharp-coefficients`, lines 1217–1230. Here `g` will be the actual gradient
of the bounded stationary corrector. These definitions assert no field existence.
-/

namespace EinsteinRelation.Sharpness

/-- The rank-one tensor with entries `u k * v l`. -/
def outer {d : ℕ} (u v : Vec d) : Mat d := fun k l => u k * v l

/-- The Jacobian `I + eᵢ ⊗ g`, in the manuscript's row convention. -/
def jacobian {d : ℕ} (i : Fin d) (g : Vec d) : Mat d :=
  1 + outer (unitVector i) g

/-- The scalar `1 + gᵢ`; its equality to the determinant is a proof obligation. -/
def jacobianFactor {d : ℕ} (i : Fin d) (g : Vec d) : ℝ := 1 + g i

/-- Candidate inverse from the rank-one inverse formula. -/
noncomputable def inverseCandidate {d : ℕ} (i : Fin d) (g : Vec d) : Mat d :=
  1 - (jacobianFactor i g)⁻¹ • outer (unitVector i) g

/-- Explicit coefficient `j B Bᵀ`; identification with the true inverse is proved
separately, rather than built into this definition as an assumption. -/
noncomputable def coefficient {d : ℕ} (i : Fin d) (g : Vec d) : Mat d :=
  jacobianFactor i g • (inverseCandidate i g * (inverseCandidate i g).transpose)

end EinsteinRelation.Sharpness
