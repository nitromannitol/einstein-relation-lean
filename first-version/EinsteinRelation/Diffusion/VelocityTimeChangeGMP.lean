import EinsteinRelation.Diffusion.GMPFamily
import EinsteinRelation.Diffusion.GMPFamilyAPI
import EinsteinRelation.Diffusion.VelocityTimeChange

/-! # The velocity time-change identity for the GMP families

`paper/main.tex` 215-233. This module instantiates the generic quenched time-change lemma
`quenchedVelocity_timeChange` for the diffusion families bound to the GMP Section 7
realizations. The origin laws of both families are probability kernels, because each
realization carries a Markov path law. The pathwise time change between the two families
enters as the hypothesis `hTC`: it is the cited input `EinsteinRelation.External.TimeChangeLaw`
restricted to the given environment law and families.
-/

open MeasureTheory Filter
open scoped NNReal Topology

namespace EinsteinRelation

/-- The GMP velocity time-change identity (main.tex 228-233). Let `P` and `P'` be the physical
and reduced families of the GMP Section 7 construction, with origin laws related by the time
change `hTC`. If the physical quenched velocity `vX` has positive first coordinate, then the
reduced quenched velocity is `vY = η • vX` with `η = vY₁ / vX₁`, and for almost every
environment and almost every reduced path the physical clock has rate `η`. The first
coordinate is the index `⟨0, _⟩ : Fin d`, which exists since `2 ≤ d`. -/
theorem gmp_velocity_timeChange {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (P P' : DiffusionFamily d)
    (hP : IsGMPPhysicalFamily hd Q.ellipticity_parameter Q P)
    (hP' : IsGMPReducedFamily hd Q.ellipticity_parameter Q P')
    (hTC : ∀ lam : ℝ, 0 ≤ lam → lam ≤ 1 → ∀ᵐ ω ∂Q.measure, ∀ hω : IsRegular Λ₀ ω,
      P lam (0, ω) = Measure.map (fun γ => Clock.InverseMeaningV3.inverseClockPath ω γ Λ₀ hω)
        (P' lam (0, ω)))
    {lam : ℝ} (hl0 : 0 < lam) (hl1 : lam ≤ 1) {vX vY : Vec d}
    (hX : HasQuenchedVelocity Q.measure (originLaw (P lam)) vX)
    (hY : HasQuenchedVelocity Q.measure (originLaw (P' lam)) vY)
    (hpos : 0 < dot (unitVector (⟨0, by omega⟩ : Fin d)) vX) :
    vY = (dot (unitVector (⟨0, by omega⟩ : Fin d)) vY /
        dot (unitVector (⟨0, by omega⟩ : Fin d)) vX) • vX ∧
      ∀ᵐ ω ∂Q.measure, ∀ᵐ γ ∂(P' lam (0, ω)),
        Tendsto (fun t : ℝ≥0 => (Clock.physicalPathClock ω γ t : ℝ) / t) atTop
          (𝓝 (dot (unitVector (⟨0, by omega⟩ : Fin d)) vY /
            dot (unitVector (⟨0, by omega⟩ : Fin d)) vX)) := by
  -- each realization has a Markov path law, so its origin law is a probability measure
  have hPprob : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw (P lam) ω) := by
    filter_upwards [hP lam hl0.le hl1] with ω hω
    obtain ⟨_, r, hr⟩ := hω
    haveI := r.pathLaw_isMarkovKernel
    rw [originLaw_apply, hr]
    infer_instance
  have hPprob' : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw (P' lam) ω) := by
    filter_upwards [hP' lam hl0.le hl1] with ω hω
    obtain ⟨_, r, hr⟩ := hω
    haveI := r.pathLaw_isMarkovKernel
    rw [originLaw_apply, hr]
    infer_instance
  -- the origin-law form of the time change is definitionally the hypothesis `hTC`
  have hTC' : ∀ᵐ ω ∂Q.measure, ∀ hω : IsRegular Λ₀ ω,
      originLaw (P lam) ω = Measure.map
        (fun γ => Clock.InverseMeaningV3.inverseClockPath ω γ Λ₀ hω) (originLaw (P' lam) ω) :=
    hTC lam hl0.le hl1
  exact quenchedVelocity_timeChange Q.measure Λ₀ (originLaw (P lam)) (originLaw (P' lam))
    Q.regular hPprob hPprob' hTC' hX hY hpos

/-- The physical velocity is the inverse clock rate times the reduced velocity, and the clock
rate lies in `[exp(-2Λ₀), exp(2Λ₀)]` (`paper/main.tex` 220-229). With `η = vY₁ / vX₁`, which is
positive since both first coordinates are, `vY = η • vX` gives `vX = η⁻¹ • vY`. The bounds
pass the clock sandwich of a regular environment, `|V| ≤ Λ₀`, to the limit `A(t) / t → η`
supplied by `gmp_velocity_timeChange`. -/
theorem gmp_physical_velocity_eq_inv_clockRate_smul {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (P P' : DiffusionFamily d)
    (hP : IsGMPPhysicalFamily hd Q.ellipticity_parameter Q P)
    (hP' : IsGMPReducedFamily hd Q.ellipticity_parameter Q P')
    (hTC : ∀ lam : ℝ, 0 ≤ lam → lam ≤ 1 → ∀ᵐ ω ∂Q.measure, ∀ hω : IsRegular Λ₀ ω,
      P lam (0, ω) = Measure.map (fun γ => Clock.InverseMeaningV3.inverseClockPath ω γ Λ₀ hω)
        (P' lam (0, ω)))
    {lam : ℝ} (hl0 : 0 < lam) (hl1 : lam ≤ 1) {vX vY : Vec d}
    (hX : HasQuenchedVelocity Q.measure (originLaw (P lam)) vX)
    (hY : HasQuenchedVelocity Q.measure (originLaw (P' lam)) vY)
    (hpos : 0 < dot (unitVector (⟨0, by omega⟩ : Fin d)) vX)
    (hYpos : 0 < dot (unitVector (⟨0, by omega⟩ : Fin d)) vY) :
    vX = (dot (unitVector (⟨0, by omega⟩ : Fin d)) vY /
        dot (unitVector (⟨0, by omega⟩ : Fin d)) vX)⁻¹ • vY ∧
      dot (unitVector (⟨0, by omega⟩ : Fin d)) vY /
        dot (unitVector (⟨0, by omega⟩ : Fin d)) vX ∈
        Set.Icc (Real.exp (-2 * Λ₀)) (Real.exp (2 * Λ₀)) := by
  obtain ⟨hvY, hlim⟩ := gmp_velocity_timeChange hd Q P P' hP hP' hTC hl0 hl1 hX hY hpos
  -- name the clock rate, which is positive, so that `vY = η • vX` reads as a scalar relation
  obtain ⟨η, hη⟩ : ∃ η : ℝ, η = dot (unitVector (⟨0, by omega⟩ : Fin d)) vY /
      dot (unitVector (⟨0, by omega⟩ : Fin d)) vX := ⟨_, rfl⟩
  have hηpos : 0 < η := by
    rw [hη]
    exact div_pos hYpos hpos
  rw [← hη] at hvY hlim ⊢
  have hvX : vX = η⁻¹ • vY := by
    rw [hvY, smul_smul, inv_mul_cancel₀ hηpos.ne', one_smul]
  refine ⟨hvX, ?_⟩
  -- one regular environment whose reduced origin law is a probability measure and carries a
  -- path realizing the clock-rate limit
  have hprob : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw (P' lam) ω) :=
    isProbabilityMeasure_of_isGMPReducedOriginLaw hd Q.ellipticity_parameter Q lam hl0.le hl1
      (originLaw (P' lam))
      ((isGMPReducedFamily_iff hd Q.ellipticity_parameter Q P').1 hP' lam hl0.le hl1)
  obtain ⟨ω, hωreg, hωprob, hωlim⟩ := (Q.regular.and (hprob.and hlim)).exists
  haveI : IsProbabilityMeasure (P' lam (0, ω)) := by
    simpa only [originLaw_apply] using hωprob
  obtain ⟨γ, hγlim⟩ := hωlim.exists
  have hlo : ∀ᶠ t : ℝ≥0 in atTop,
      Real.exp (-2 * Λ₀) ≤ (Clock.physicalPathClock ω γ t : ℝ) / t := by
    filter_upwards [eventually_gt_atTop (0 : ℝ≥0)] with t ht
    rw [le_div_iff₀ (NNReal.coe_pos.mpr ht)]
    exact (Clock.InverseMeaningV3.physicalPathClock_bounds ω γ Λ₀ hωreg.2.1 t).1
  have hhi : ∀ᶠ t : ℝ≥0 in atTop,
      (Clock.physicalPathClock ω γ t : ℝ) / t ≤ Real.exp (2 * Λ₀) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ≥0)] with t ht
    rw [div_le_iff₀ (NNReal.coe_pos.mpr ht)]
    exact (Clock.InverseMeaningV3.physicalPathClock_bounds ω γ Λ₀ hωreg.2.1 t).2
  exact Set.mem_Icc.mpr ⟨ge_of_tendsto hγlim hlo, le_of_tendsto hγlim hhi⟩

end EinsteinRelation
