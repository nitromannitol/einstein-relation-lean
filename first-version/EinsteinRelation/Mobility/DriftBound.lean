import EinsteinRelation.Mobility.DriftBoundStepProof
import EinsteinRelation.Mobility.DriftBoundPointwise
import EinsteinRelation.Mobility.DriftWeakDivergence

/-! # The drift bound

Source: `paper/main.tex` 1134 and 1154-1156. `DriftBoundStep` holds: the classical column divergence
`DriftH5.cdiv i` is a weak horizontal divergence of the `i`-th column of the reduced coefficient
(`DriftH5.hasWeakHorizontalDivergence_reducedColumn`), it is bounded by `d` times the reduced Lipschitz
constant (`ae_abs_cdiv_le_reduced`), and the first-row entry is bounded by `sourceReducedBound Λ₀`
(`reduced_entry_bound_ae`). `driftBoundStep_of_cdiv` assembles these.
-/

namespace EinsteinRelation

/-- **`DriftBoundStep`**: for `0 < λ ≤ 1` and every weak horizontal divergence `D·(a e_i)`, the drift
`b_i^λ = ½ D·(a e_i) + λ e₁·a e_i` is essentially bounded under the reduced reference law. -/
theorem driftBoundStep : DriftBoundStep :=
  driftBoundStep_of_cdiv (fun {_} i => DriftH5.cdiv i)
    (fun _ _ _ _ Q hQ i => DriftH5.hasWeakHorizontalDivergence_reducedColumn Q hQ i)
    (fun _ Λ₀ _ Q i => ⟨reducedLipschitzConstant Λ₀, ae_abs_cdiv_le_reduced Q i⟩)
    (fun _ hd _ _ Q i => exists_reduced_entry_bound hd Q i)

end EinsteinRelation
