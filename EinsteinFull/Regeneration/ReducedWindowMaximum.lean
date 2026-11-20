import EinsteinFull.Regeneration.WindowDisplacement
import EinsteinFull.Regeneration.ReducedCenteredSurvival
import EinsteinFull.Calculus.SunaSuppliedLawIdentification

/-!
# Uniform window maxima of the reduced diffusion

Over one regeneration interval `Δ = λ⁻²`, the coordinate maximum of a supplied
reduced diffusion, measured in units of `λ⁻¹`, has an exponential moment that is
uniform in the environment law, the force, the environment and the start. The
proof combines the centered survival estimate with the capped slab clock of
radius `λ⁻¹`.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation EinsteinRelation.Regeneration
open EinsteinRelation.External.GantertSection7Support
open scoped NNReal ENNReal

namespace EinsteinFull.Regeneration

/-- A path that stays in a set up to time `g` leaves it no earlier than `g`. -/
theorem le_exitTime_of_forall_mem {d : ℕ} (U : Set (Vec d)) (γ : Path d) (g : ℝ≥0)
    (h : ∀ s : ℝ≥0, s ≤ g → γ s ∈ U) :
    (g : ℝ≥0∞) ≤ MarkovProcess.ContinuousPath.exitTime U γ := by
  by_contra hlt'
  have hlt := lt_of_not_ge hlt'
  obtain ⟨s, hs, hsU⟩ : ∃ s : ℝ≥0, (s : ℝ≥0∞) < g ∧ γ s ∉ U := by
    by_contra hall
    simp only [not_exists, not_and, not_not] at hall
    apply (not_le_of_gt hlt)
    unfold MarkovProcess.ContinuousPath.exitTime
    apply le_sInf
    rintro _ ⟨s, rfl, hs⟩
    by_contra hsg
    exact hs (hall s (lt_of_not_ge hsg))
  exact hsU (h s (ENNReal.coe_le_coe.mp hs.le))

/-- Staying within a coordinate slab up to the horizon makes the capped step last
the whole horizon. -/
theorem le_cappedCoordinateSlabExit_of_forall_mem {d : ℕ} (γ : Path d) (i : Fin d)
    (r : ℝ) (g : ℝ≥0) (h : ∀ s : ℝ≥0, s ≤ g → |γ s i - γ 0 i| < r) :
    g ≤ cappedCoordinateSlabExit γ i r g := by
  have hle := le_exitTime_of_forall_mem (coordinateSlab i (γ 0) r) γ g h
  unfold cappedCoordinateSlabExit
  split_ifs with htop
  · exact le_rfl
  · apply le_min _ le_rfl
    have hle' : (g : ℝ≥0∞) ≤ coordinateSlabExit γ i r := hle
    rw [← ENNReal.coe_toNNReal htop] at hle'
    exact ENNReal.coe_le_coe.mp hle'

/-- Uniform exponential moment of the reduced window maximum over one
regeneration interval. -/
theorem uniform_reduced_window_maximum_moment {d : ℕ} (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) :
    ∃ b C : ℝ, 0 < b ∧ 0 < C ∧
      ∀ (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1)
        (P : QuenchedPathLaws d),
        IsGMPReducedKernel hd Q.ellipticity_parameter Q lam h0.le h1 P →
        ∀ᵐ ω ∂Q.measure, ∀ (x : Vec d) (i : Fin d),
          Integrable (fun γ : Path d => Real.exp (b * (lam *
            coordinateMaximum γ i (Renewal.regenDelta lam)))) (P (x, ω)) ∧
          (∫ γ, Real.exp (b * (lam * coordinateMaximum γ i (Renewal.regenDelta lam)))
            ∂P (x, ω)) ≤ C := by
  obtain ⟨ε₀, hε₀, hε₀1, hsurv⟩ := reduced_centered_survival hd Λ₀ r₀ 1 one_pos
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
  have hP' : IsGMPReducedKernel hd Q.ellipticity_parameter Q |lam|
      (abs_pos.mpr h0.ne').le (by rw [hlamabs]; exact h1) P := by
    simpa only [hlamabs] using hP
  filter_upwards [hP, hsurv Q lam (abs_pos.mpr h0.ne') (by rw [hlamabs]; exact h1) P hP']
    with ω hreal hloc
  obtain ⟨hω, G, hrow⟩ := hreal
  have : IsMarkovKernel G.pathLaw := G.pathLaw_isMarkovKernel
  intro x i
  have hr : 0 < 1 / lam := one_div_pos.mpr h0
  have hfdd := foundation_arbitrary_supplied_gmp_canonical_FDD hd (sourceReducedBound Λ₀)
    (one_le_sourceReducedBound Q.ellipticity_parameter) (zeroPotentialReducedPair ω)
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
  have hmom := window_maximum_exponential_moment hd (zeroPotentialReducedPair ω) lam
    (sourceReducedBound Λ₀) (one_le_sourceReducedBound Q.ellipticity_parameter) hω
    G.pathLaw hfdd i (1 / lam) hr (Renewal.regenDelta lam) ε hε hε1 hstep x
  have hfun : (fun γ : Path d => Real.exp ((ε / 4) *
      (coordinateMaximum γ i (Renewal.regenDelta lam) / (1 / lam)))) =
      fun γ => Real.exp (ε / 4 * (lam * coordinateMaximum γ i (Renewal.regenDelta lam))) := by
    funext γ
    rw [one_div, div_inv_eq_mul, mul_comm (coordinateMaximum γ i _) lam]
  rw [hfun] at hmom
  rw [hrow x]
  exact hmom

end EinsteinFull.Regeneration
