import EinsteinFull.Calculus.U5ReducedAllStartKernel
import EinsteinFull.Calculus.U6RegularSignedPathRealization

open EinsteinRelation EinsteinFull MeasureTheory ProbabilityTheory
open EinsteinRelation.External.GantertSection7Support
open scoped NNReal

namespace SbxS3Section3R01

/-- A jointly measurable reduced path kernel realizes the regular law at every start. -/
theorem joint_reduced_kernel_exists
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EinsteinRelation.EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) :
    ∃ P : QuenchedPathLaws d,
      IsGMPReducedKernel hd Q.ellipticity_parameter Q lam h0 h1 P := by
  have hΛpos : 0 < Λ₀ := lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter
  obtain ⟨K, hK, hsel⟩ := u5_reduced_textbook_kernel_all_starts
    (by omega : 1 ≤ d) hΛpos (firstCoordinateIndex hd) lam
  letI : IsMarkovKernel K := hK
  let P : QuenchedPathLaws d := K.comap (fun p => (p.2, p.1))
    (measurable_snd.prodMk measurable_fst)
  refine ⟨P, ?_⟩
  filter_upwards [Q.regular] with ω hω
  have hreg := isRegular_zeroPotentialReducedPair Q.ellipticity_parameter hω
  obtain ⟨L, hL, hfdd⟩ := u6_regular_signed_continuous_kernel_exists
    hd (zeroPotentialReducedPair ω) lam (sourceReducedBound Λ₀)
    (one_le_sourceReducedBound Q.ellipticity_parameter) hreg
  letI : IsMarkovKernel L := hL
  have hac := fun t ht x => u7_regular_signed_kernel_absolutelyContinuous
    hd (zeroPotentialReducedPair ω) lam (sourceReducedBound Λ₀)
    (one_le_sourceReducedBound Q.ellipticity_parameter) hreg t ht x
  obtain ⟨⟨R, hRL, hRP⟩, hMP⟩ :=
    u2_regular_fixed_environment_realization_and_mp_of_ac_fdd
      hd (zeroPotentialReducedPair ω) lam (sourceReducedBound Λ₀)
      (one_le_sourceReducedBound Q.ellipticity_parameter) hreg h0 h1 L hfdd hac
  refine ⟨hreg, R, ?_⟩
  intro x
  have ht := hsel ω hω x
  have hoccK := foundation_reduced_textbook_averaged_occupation_ac_of_two_le
    hd hΛpos hω (firstCoordinateIndex hd) lam ht
  have hred := c16_reduced_solves_of_textbook_and_averaged_occupation
    hΛpos hω (firstCoordinateIndex hd) lam ht hoccK
  have hgen : physicalGenerator (firstCoordinateIndex hd) (zeroPotentialReducedPair ω) lam =
      reducedGenerator (firstCoordinateIndex hd) ω lam := by
    funext f x
    unfold physicalGenerator reducedGenerator
    simp_rw [reducedCoefficient_zeroPotentialReducedPair]
    change Real.exp (2 * (0 : ℝ)) / 2 * _ + _ = _
    rw [mul_zero, Real.exp_zero]
    rfl
  have hphysK : SolvesMartingaleProblem
      (physicalGenerator (firstCoordinateIndex hd) (zeroPotentialReducedPair ω) lam)
      x (K (ω, x)) := by rw [hgen]; exact hred
  have hflatpos : 0 < sourceReducedBound Λ₀ :=
    lt_of_lt_of_le zero_lt_one (one_le_sourceReducedBound Q.ellipticity_parameter)
  have htextK := c4_textbook_solves_of_physical_and_averaged_occupation
    hflatpos hreg (firstCoordinateIndex hd) lam hphysK hoccK
  letI : IsProbabilityMeasure (R.pathLaw x) := by rw [hRL]; infer_instance
  have hmarg : ∀ t : ℝ≥0, 0 < t →
      (R.pathLaw x).map (pathPosition t) ≪ (volume : Measure (Vec d)) := by
    intro t ht
    rw [R.pathLaw_endpoint, hRP]
    exact hac t ht x
  have hoccR := u2_averaged_occupation_ac_of_marginals (R.pathLaw x) hmarg
  have hphysR : SolvesMartingaleProblem
      (physicalGenerator (firstCoordinateIndex hd) (zeroPotentialReducedPair ω) lam)
      x (R.pathLaw x) := by rw [hRL]; exact hMP x
  have htextR := c4_textbook_solves_of_physical_and_averaged_occupation
    hflatpos hreg (firstCoordinateIndex hd) lam hphysR hoccR
  obtain ⟨hc, hs, hb, he, hm, hbd⟩ :=
    physical_svHypotheses hflatpos hreg (firstCoordinateIndex hd) lam
  obtain ⟨S, _, hu⟩ := foundation_textbook_well_posed d (by omega)
    (⇑(zeroPotentialReducedPair ω).1)
    (physicalDrift (zeroPotentialReducedPair ω) (firstCoordinateIndex hd) lam)
    hc hs hb he hm hbd x
  change K (ω, x) = R.pathLaw x
  exact (hu _ htextK).trans (hu _ htextR).symm

end SbxS3Section3R01
