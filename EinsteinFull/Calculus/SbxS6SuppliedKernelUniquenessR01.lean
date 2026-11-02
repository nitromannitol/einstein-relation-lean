import EinsteinFull.Calculus.U2GMPFinalEnvironment
import EinsteinFull.Calculus.U2GMPEnvironmentRealization

open EinsteinRelation EinsteinFull MeasureTheory ProbabilityTheory
open EinsteinRelation.External.GantertSection7Support
open scoped NNReal

namespace EinsteinFull

/-- Supplied reduced GMP kernels have the same path law at every start on one
conull environment event. The transition kernels need not be identified. -/
theorem s6_supplied_reduced_kernel_pathLaw_unique
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (P P' : QuenchedPathLaws d)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q lam h0 h1 P)
    (hP' : IsGMPReducedKernel hd Q.ellipticity_parameter Q lam h0 h1 P') :
    ∀ᵐ ω ∂Q.measure, ∀ x : Vec d, P (x, ω) = P' (x, ω) := by
  filter_upwards [hP, hP'] with ω hω hω'
  obtain ⟨hreg, R, hR⟩ := hω
  obtain ⟨hreg', R', hR'⟩ := hω'
  let : IsMarkovKernel R.pathLaw := R.pathLaw_isMarkovKernel
  let : IsMarkovKernel R'.pathLaw := R'.pathLaw_isMarkovKernel
  have hflatpos : 0 < sourceReducedBound Λ₀ :=
    lt_of_lt_of_le zero_lt_one (one_le_sourceReducedBound Q.ellipticity_parameter)
  intro x
  have hmarg : ∀ t : ℝ≥0, 0 < t →
      (R.pathLaw x).map (pathPosition t) ≪ (volume : Measure (Vec d)) := by
    intro t ht
    rw [R.pathLaw_endpoint, R.transitionKernel_eq_heatKernel t ht x]
    exact withDensity_absolutelyContinuous _ _
  have hmarg' : ∀ t : ℝ≥0, 0 < t →
      (R'.pathLaw x).map (pathPosition t) ≪ (volume : Measure (Vec d)) := by
    intro t ht
    rw [R'.pathLaw_endpoint, R'.transitionKernel_eq_heatKernel t ht x]
    exact withDensity_absolutelyContinuous _ _
  have hphys := foundation_arbitrary_supplied_gmp_physical_MP hd (sourceReducedBound Λ₀)
    (one_le_sourceReducedBound Q.ellipticity_parameter) (zeroPotentialReducedPair ω)
    hreg lam h0 h1 R x
  have hphys' := foundation_arbitrary_supplied_gmp_physical_MP hd (sourceReducedBound Λ₀)
    (one_le_sourceReducedBound Q.ellipticity_parameter) (zeroPotentialReducedPair ω)
    hreg' lam h0 h1 R' x
  have htext := c4_textbook_solves_of_physical_and_averaged_occupation
    hflatpos hreg (firstCoordinateIndex hd) lam hphys
    (u2_averaged_occupation_ac_of_marginals (R.pathLaw x) hmarg)
  have htext' := c4_textbook_solves_of_physical_and_averaged_occupation
    hflatpos hreg' (firstCoordinateIndex hd) lam hphys'
    (u2_averaged_occupation_ac_of_marginals (R'.pathLaw x) hmarg')
  obtain ⟨hc, hs, hb, he, hm, hbd⟩ :=
    physical_svHypotheses hflatpos hreg (firstCoordinateIndex hd) lam
  obtain ⟨S, _, hu⟩ := foundation_textbook_well_posed d (by omega)
    (⇑(zeroPotentialReducedPair ω).1)
    (physicalDrift (zeroPotentialReducedPair ω) (firstCoordinateIndex hd) lam)
    hc hs hb he hm hbd x
  rw [hR x, hR' x]
  exact (hu _ htext).trans (hu _ htext').symm

#print axioms s6_supplied_reduced_kernel_pathLaw_unique

end EinsteinFull
