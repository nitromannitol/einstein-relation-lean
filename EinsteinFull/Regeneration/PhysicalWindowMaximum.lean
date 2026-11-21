import EinsteinFull.PhysicalRegeneration.Regeneration.ReducedWindowMaximum
import EinsteinFull.Regeneration.AbsoluteWindowMaximum

/-!
# The absolute window maximum of the physical diffusion

Over one regeneration interval of length `λ⁻²`, the absolute coordinate displacement of the
physical diffusion, in units of `λ⁻¹`, has an exponential moment bounded uniformly in the
environment, the force and the starting point. The capped slab clock controls both directions.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation EinsteinRelation.Regeneration
open EinsteinRelation.External.GantertSection7Support
open scoped NNReal ENNReal

namespace EinsteinFull.Regeneration

/-- Uniform exponential moment of the absolute window maximum of the physical diffusion over one
regeneration interval. -/
theorem uniform_physical_window_absolute_maximum_moment {d : ℕ} (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) :
    ∃ b C : ℝ, 0 < b ∧ 0 < C ∧
      ∀ (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1)
        (P : QuenchedPathLaws d),
        EinsteinFull.Regeneration.IsGMPPhysicalKernelReducedBound hd Q.ellipticity_parameter Q lam h0.le h1 P →
        ∀ᵐ ω ∂Q.measure, ∀ (x : Vec d) (i : Fin d),
          Integrable (fun γ : Path d => Real.exp (b * (lam *
            absoluteCoordinateMaximum i (Renewal.regenDelta lam) γ))) (P (x, ω)) ∧
          (∫ γ, Real.exp (b * (lam * absoluteCoordinateMaximum i (Renewal.regenDelta lam) γ))
            ∂P (x, ω)) ≤ C := by
  obtain ⟨ε₀, hε₀, hε₀1, hsurv⟩ := reduced_centered_survival_phys hd Λ₀ r₀ 1 one_pos
  let ε : ℝ := min ε₀ (1 / 2)
  have hε : 0 < ε := lt_min hε₀ (by norm_num)
  have hε1 : ε < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hεε : ε ≤ ε₀ := min_le_left _ _
  let C : ℝ := Real.exp ε * Real.exp (ε / 4) / (1 - Real.exp (ε / 4 - ε / 2))
  have hC : 0 < C := by
    have hlt : Real.exp (ε / 4 - ε / 2) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    exact div_pos (by positivity) (sub_pos.mpr hlt)
  refine ⟨ε / 4, C, by positivity, hC, ?_⟩
  intro Q lam h0 h1 P hP
  have hlamabs : |lam| = lam := abs_of_pos h0
  have hP' : EinsteinFull.Regeneration.IsGMPPhysicalKernelReducedBound hd Q.ellipticity_parameter Q |lam|
      (abs_pos.mpr h0.ne').le (by rw [hlamabs]; exact h1) P := by
    simpa only [hlamabs] using hP
  filter_upwards [hP, hsurv Q lam (abs_pos.mpr h0.ne') (by rw [hlamabs]; exact h1) P hP']
    with ω hreal hloc
  obtain ⟨hω, G, hrow⟩ := hreal
  have : IsMarkovKernel G.pathLaw := G.pathLaw_isMarkovKernel
  intro x i
  have hr : 0 < 1 / lam := one_div_pos.mpr h0
  have hfdd := foundation_arbitrary_supplied_gmp_canonical_FDD hd (sourceReducedBound Λ₀)
    (one_le_sourceReducedBound Q.ellipticity_parameter) ω
    hω lam h0.le h1 G
  have hstep : ∀ y, ENNReal.ofReal ε ≤ G.pathLaw y {γ |
      Renewal.regenDelta lam ≤ cappedCoordinateSlabExit γ i (1 / lam) (Renewal.regenDelta lam)} := by
    intro y
    have hy := hloc y
    rw [hrow y] at hy
    simp only [hlamabs] at hy
    have hsub : {γ : Path d | ∀ s ∈ Set.Icc (0 : ℝ≥0) (Renewal.regenDelta lam),
          euclideanNorm (γ s - y) ≤ (1 / lam) / 2} ∩ {γ | γ 0 = y} ⊆
        {γ | Renewal.regenDelta lam ≤
          cappedCoordinateSlabExit γ i (1 / lam) (Renewal.regenDelta lam)} := by
      rintro γ ⟨hγ, hγ0⟩
      apply le_cappedCoordinateSlabExit_of_forall_mem
      intro s hs
      have hn := hγ s ⟨zero_le, hs⟩
      have hc := coordinate_abs_le_euclideanNorm (γ s - y) i
      change |γ s i - γ 0 i| < 1 / lam
      rw [hγ0]
      have hc' : |γ s i - y i| ≤ (1 / lam) / 2 := by
        simpa only [Pi.sub_apply] using hc.trans hn
      linarith
    have hstart : G.pathLaw y {γ | γ 0 = y}ᶜ = 0 := by
      have h := G.pathLaw_starts_at y
      rw [MeasureTheory.ae_iff] at h
      exact h
    calc ENNReal.ofReal ε ≤ ENNReal.ofReal ε₀ := ENNReal.ofReal_le_ofReal hεε
      _ ≤ G.pathLaw y {γ : Path d | ∀ s ∈ Set.Icc (0 : ℝ≥0) (Renewal.regenDelta lam),
          euclideanNorm (γ s - y) ≤ (1 / lam) / 2} := by simpa only [one_div] using hy
      _ = G.pathLaw y ({γ : Path d | ∀ s ∈ Set.Icc (0 : ℝ≥0) (Renewal.regenDelta lam),
          euclideanNorm (γ s - y) ≤ (1 / lam) / 2} ∩ {γ | γ 0 = y}) :=
          (measure_inter_conull hstart).symm
      _ ≤ _ := measure_mono hsub
  have hmom := window_absolute_maximum_exponential_moment hd ω lam
    (sourceReducedBound Λ₀) (one_le_sourceReducedBound Q.ellipticity_parameter) hω
    G.pathLaw hfdd i (1 / lam) hr (Renewal.regenDelta lam) ε hε hε1 hstep x
  have hfun : (fun γ : Path d => Real.exp ((ε / 4) *
      (absoluteCoordinateMaximum i (Renewal.regenDelta lam) γ / (1 / lam)))) =
      fun γ => Real.exp (ε / 4 * (lam * absoluteCoordinateMaximum i (Renewal.regenDelta lam) γ)) := by
    funext γ
    rw [one_div, div_inv_eq_mul, mul_comm (absoluteCoordinateMaximum i _ γ) lam]
  rw [hfun] at hmom
  rw [hrow x]
  exact hmom

end EinsteinFull.Regeneration
