import EinsteinFull.Blueprint.Roots.node_p_u3A_late
import EinsteinFull.Blueprint.G3.node_p_u3A_late_u23_cauchy
import EinsteinFull.Calculus.ComplexSemigroupUniquenessSupport
import EinsteinFull.Calculus.ComplexTransposeSupport

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- The Cauchy flux family gives late force replacement for every actual forward
semigroup and its bilinear transpose, by uniqueness of these operators. -/
theorem node_p_u3A_late_of_deps
    (hCauchy : node_p_u3A_late_u23_cauchyStmt) : node_p_u3A_lateStmt := by
  intro d hd D
  obtain ⟨C, M, hC, hbound⟩ := hCauchy d hd D
  refine ⟨C, M, hC, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P Pdag P₀ P₀dag hP hPdag hP₀ hP₀dag
  have ePdag := hPdag.eq_complexL2Transpose
  rw [hP.eq_forcedComplexEvolution] at ePdag
  have eP₀dag := hP₀dag.eq_complexL2Transpose
  rw [hP₀.eq_forcedComplexEvolution] at eP₀dag
  rw [hP.eq_forcedComplexEvolution, ePdag, hP₀.eq_forcedComplexEvolution, eP₀dag]
  obtain ⟨G, F, hflux, hav, _, hdiff⟩ := hbound Q hQ β a μ hβ ha hμ
    (fun z => forcedComplexEvolution Q ⟨0, by omega⟩ z)
    (fun z t => complexL2Transpose (reducedLaw Q)
      (forcedComplexEvolution Q ⟨0, by omega⟩ z t))
    (fun z => isComplexEnvironmentSemigroup_forcedComplexEvolution Q ⟨0, by omega⟩ z)
    (fun z => isComplexTransposeSemigroup_complexL2Transpose Q
      (forcedComplexEvolution Q ⟨0, by omega⟩ z))
  refine ⟨G ζ, F ζ, G 0, F 0, hflux ζ, hflux 0, ?_⟩
  intro t ht hz ν
  exact ⟨hav t ht ν ζ (hz.trans (by norm_num)), hdiff t ht ν ζ hz⟩

end EinsteinFull.Blueprint
