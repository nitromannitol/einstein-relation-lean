import EinsteinFull.Regeneration.UniformFirstCandidate
import EinsteinFull.Regeneration.PhysicalKernelPredicate
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.Proofs.SbxS7ConditionalTrialExhaustion
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.node_app_u3A_factorization_u23_coupling_u2D_scope
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.node_app_u3A_factorization_u23_past_u2D_kernel
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.node_app_u3A_regen_u2D_tails
import EinsteinFull.PhysicalRegeneration.Calculus.SbxAGlobalReducedKernelR04
import EinsteinFull.PhysicalRegeneration.Calculus.SbxBCenteredLocalReturnClosureR15
import EinsteinFull.PhysicalRegeneration.Calculus.SbxBCenteredLocalReturnR13
import EinsteinFull.PhysicalRegeneration.Calculus.SbxBCenteredSurvivalR12
import EinsteinFull.PhysicalRegeneration.Calculus.SbxBCenteredTubeChainR03
import EinsteinFull.PhysicalRegeneration.Calculus.SbxS3JointReducedKernelR01
import EinsteinFull.PhysicalRegeneration.Calculus.SbxS6SuppliedKernelUniquenessR01
import EinsteinFull.PhysicalRegeneration.Frozen.RegenerationCoupling
import EinsteinFull.PhysicalRegeneration.Regeneration.ReducedCenteredSurvival
import EinsteinFull.PhysicalRegeneration.Regeneration.ReducedWindowMaximum
import EinsteinFull.PhysicalRegeneration.Vendor.Diffusion.GMPFamilyAPI
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.AnnealedUniformEndpointRestart
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.DeterministicEndpointNullSets
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.FirstRegenerationSliceFubini
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.RenewalCarriers

/-!
# Physical-kernel version of
`EinsteinFull.Regeneration.UniformFirstCandidate`

The declarations of that module that concern the reduced quenched kernel, stated and
proved for the physical quenched kernel of GMP Section 7: the zero-potential pair
`(exp(-2V) a₀, 0)` is replaced by the physical pair `ω = (a₀, V)`, regular at the same
bound `sourceReducedBound Λ₀` (`IsGMPPhysicalKernelReducedBound`).
-/


open MeasureTheory ProbabilityTheory EinsteinRelation EinsteinRelation.Regeneration
open EinsteinRelation.External.GantertSection7Support
open scoped NNReal ENNReal
namespace EinsteinFull.Regeneration
/-- The physical-kernel version of `EinsteinFull.Regeneration.uniform_failed_window_weight`. -/
theorem uniform_failed_window_weight_phys {d : ℕ} (hd : 2 ≤ d) (Λ₀ r₀ l : ℝ) (hl : 0 < l) :
    ∃ b ρ : ℝ, 0 < b ∧ 0 ≤ ρ ∧ ρ < 1 ∧
      ∀ (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1)
        (P : QuenchedPathLaws d),
        EinsteinFull.Regeneration.IsGMPPhysicalKernelReducedBound hd Q.ellipticity_parameter Q lam h0.le h1 P →
        ∀ᵐ ω ∂Q.measure, ∀ (y : Vec d) (i : Fin d),
          ∫⁻ η, failedWindowWeight (Renewal.regenDelta lam) lam (l / lam) b i η ∂P (y, ω) ≤
            ENNReal.ofReal ρ := by
  obtain ⟨ε₀, hε₀, hε₀1, hsurv⟩ := reduced_centered_survival_phys hd Λ₀ r₀ l hl
  obtain ⟨b₁, C, hb₁, hC, hwin⟩ := uniform_reduced_window_maximum_moment_phys hd Λ₀ r₀
  let ε : ℝ := min ε₀ (1 / 2)
  have hε : 0 < ε := lt_min hε₀ (by norm_num)
  have hε1 : ε ≤ 1 / 2 := min_le_right _ _
  have hεε : ε ≤ ε₀ := min_le_left _ _
  let q : ℝ := 1 - ε / 2
  have hq : 0 < q := by dsimp [q]; linarith
  have hq1 : q < 1 := by dsimp [q]; linarith
  let θ₁ : ℝ := min 1 (ε / (2 * C))
  have hθ₁ : 0 < θ₁ := lt_min one_pos (div_pos hε (by positivity))
  let θ : ℝ := min θ₁ (Real.log (1 / q) / (2 * (b₁ * l)))
  have hlogpos : 0 < Real.log (1 / q) := Real.log_pos (by rw [one_div]; exact one_lt_inv_iff₀.mpr ⟨hq, hq1⟩)
  have hθ : 0 < θ := lt_min hθ₁ (div_pos hlogpos (by positivity))
  have hθ1 : θ ≤ 1 := (min_le_left _ _).trans (min_le_left _ _)
  have hθle : θ ≤ ε / (2 * C) :=
    (min_le_left θ₁ (Real.log (1 / q) / (2 * (b₁ * l)))).trans (min_le_right (1 : ℝ) _)
  have hθC : θ * C ≤ ε / 2 := by
    calc θ * C ≤ ε / (2 * C) * C := mul_le_mul_of_nonneg_right hθle hC.le
      _ = ε / 2 := by field_simp
  let ρ : ℝ := Real.exp (θ * b₁ * l) * q
  have hρ1 : ρ < 1 := by
    have hexp : θ * b₁ * l ≤ Real.log (1 / q) / 2 := by
      have h := min_le_right θ₁ (Real.log (1 / q) / (2 * (b₁ * l)))
      have hbl : 0 < b₁ * l := mul_pos hb₁ hl
      calc θ * b₁ * l = θ * (b₁ * l) := by ring
        _ ≤ Real.log (1 / q) / (2 * (b₁ * l)) * (b₁ * l) :=
          mul_le_mul_of_nonneg_right h hbl.le
        _ = Real.log (1 / q) / 2 := by field_simp
    have hlt : Real.exp (θ * b₁ * l) < 1 / q := by
      calc Real.exp (θ * b₁ * l) ≤ Real.exp (Real.log (1 / q) / 2) := Real.exp_le_exp.mpr hexp
        _ < Real.exp (Real.log (1 / q)) := Real.exp_lt_exp.mpr (by linarith)
        _ = 1 / q := Real.exp_log (by positivity)
    have := mul_lt_mul_of_pos_right hlt hq
    simpa [ρ, div_mul_cancel₀, hq.ne'] using this
  refine ⟨θ * b₁, ρ, mul_pos hθ hb₁, by positivity, hρ1, ?_⟩
  intro Q lam h0 h1 P hP
  have hlamabs : |lam| = lam := abs_of_pos h0
  have hP' : EinsteinFull.Regeneration.IsGMPPhysicalKernelReducedBound hd Q.ellipticity_parameter Q |lam|
      (abs_pos.mpr h0.ne').le (by rw [hlamabs]; exact h1) P := by
    simpa only [hlamabs] using hP
  filter_upwards [hP, hsurv Q lam (abs_pos.mpr h0.ne') (by rw [hlamabs]; exact h1) P hP',
    hwin Q lam h0 h1 P hP] with ω hreal hloc hmom
  obtain ⟨hω, G, hrow⟩ := hreal
  have : IsMarkovKernel G.pathLaw := G.pathLaw_isMarkovKernel
  intro y i
  let Δ := Renewal.regenDelta lam
  let R := l / lam
  have hRl : lam * R = l := by dsimp [R]; field_simp
  -- the escape probability
  have hesc : P (y, ω) (windowEscape Δ R i) ≤ ENNReal.ofReal (1 - ε) := by
    have hy := hloc y
    simp only [hlamabs] at hy
    rw [hrow y] at hy ⊢
    have hstart : G.pathLaw y {γ | γ 0 = y}ᶜ = 0 := by
      have h := G.pathLaw_starts_at y
      rw [MeasureTheory.ae_iff] at h
      exact h
    let S : Set (Path d) := {γ | ∀ s ∈ Set.Icc (0 : ℝ≥0) Δ, euclideanNorm (γ s - y) ≤ R / 2}
    have hsub : S ∩ {γ | γ 0 = y} ⊆ (windowEscape Δ R i)ᶜ := by
      rintro γ ⟨hγ, hγ0⟩ ⟨s, hs, hlt⟩
      have hn := hγ s ⟨zero_le, hs⟩
      have hc := coordinate_abs_le_euclideanNorm (γ s - y) i
      rw [hγ0] at hlt
      have hc' : |γ s i - y i| ≤ R / 2 := by simpa only [Pi.sub_apply] using hc.trans hn
      linarith
    have hSprob : ENNReal.ofReal ε ≤ G.pathLaw y S := by
      calc ENNReal.ofReal ε ≤ ENNReal.ofReal ε₀ := ENNReal.ofReal_le_ofReal hεε
        _ ≤ G.pathLaw y S := by simpa only [S, R, one_div] using hy
    have hcompl : ENNReal.ofReal ε ≤ G.pathLaw y (windowEscape Δ R i)ᶜ := by
      calc ENNReal.ofReal ε ≤ G.pathLaw y S := hSprob
        _ = G.pathLaw y (S ∩ {γ | γ 0 = y}) := (measure_inter_conull hstart).symm
        _ ≤ _ := measure_mono hsub
    rw [prob_compl_eq_one_sub (measurableSet_windowEscape Δ R i)] at hcompl
    rw [ENNReal.ofReal_sub _ hε.le, ENNReal.ofReal_one]
    calc G.pathLaw y (windowEscape Δ R i)
        = 1 - (1 - G.pathLaw y (windowEscape Δ R i)) := by
          rw [ENNReal.sub_sub_cancel ENNReal.one_ne_top prob_le_one]
      _ ≤ 1 - ENNReal.ofReal ε := tsub_le_tsub_left hcompl 1
  -- the window moment as a lower integral
  have hmom' : ∫⁻ η, ENNReal.ofReal (Real.exp (b₁ * (lam * coordinateMaximum η i Δ))) ∂P (y, ω)
      ≤ ENNReal.ofReal C := by
    obtain ⟨hint, hle⟩ := hmom y i
    rw [← ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun η => (Real.exp_pos _).le)]
    exact ENNReal.ofReal_le_ofReal hle
  let e : ℝ := Real.exp (θ * b₁ * l)
  have hpoint : ∀ η : Path d, failedWindowWeight Δ lam R (θ * b₁) i η ≤
      ENNReal.ofReal e * ((windowEscape Δ R i).indicator 1 η +
        ENNReal.ofReal θ * ENNReal.ofReal (Real.exp (b₁ * (lam * coordinateMaximum η i Δ)))) := by
    intro η
    by_cases hη : η ∈ windowEscape Δ R i
    · simp only [failedWindowWeight, Set.indicator_of_mem hη, Pi.one_apply]
      rw [← ENNReal.ofReal_mul hθ.le, ← ENNReal.ofReal_one,
        ← ENNReal.ofReal_add zero_le_one (mul_nonneg hθ.le (Real.exp_pos _).le),
        ← ENNReal.ofReal_mul (Real.exp_pos _).le]
      apply ENNReal.ofReal_le_ofReal
      have htilt := exp_mul_le_one_add_mul_exp θ (b₁ * (lam * coordinateMaximum η i Δ))
        hθ.le hθ1
      have hsplit : θ * b₁ * lam * (coordinateMaximum η i Δ + R) =
          θ * b₁ * l + θ * (b₁ * (lam * coordinateMaximum η i Δ)) := by
        rw [← hRl]
        ring
      rw [hsplit, Real.exp_add]
      exact mul_le_mul_of_nonneg_left htilt (Real.exp_pos _).le
    · simp only [failedWindowWeight, Set.indicator_of_notMem hη]
      exact zero_le
  have hWm : Measurable fun η : Path d =>
      ENNReal.ofReal (Real.exp (b₁ * (lam * coordinateMaximum η i Δ))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul
      (measurable_const.mul ((measurable_coordinateMaximum i).comp
        (measurable_const.prodMk measurable_id)))))
  calc ∫⁻ η, failedWindowWeight Δ lam R (θ * b₁) i η ∂P (y, ω)
      ≤ ∫⁻ η, ENNReal.ofReal e * ((windowEscape Δ R i).indicator 1 η +
          ENNReal.ofReal θ * ENNReal.ofReal (Real.exp (b₁ * (lam * coordinateMaximum η i Δ))))
          ∂P (y, ω) := lintegral_mono hpoint
    _ = ENNReal.ofReal e * (P (y, ω) (windowEscape Δ R i) + ENNReal.ofReal θ *
          ∫⁻ η, ENNReal.ofReal (Real.exp (b₁ * (lam * coordinateMaximum η i Δ))) ∂P (y, ω)) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_add_left (measurable_one.indicator (measurableSet_windowEscape Δ R i)),
          lintegral_indicator_one (measurableSet_windowEscape Δ R i),
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal e * (ENNReal.ofReal (1 - ε) + ENNReal.ofReal θ * ENNReal.ofReal C) := by
        gcongr
    _ = ENNReal.ofReal (e * ((1 - ε) + θ * C)) := by
        rw [← ENNReal.ofReal_mul hθ.le, ← ENNReal.ofReal_add (by linarith)
          (mul_nonneg hθ.le hC.le), ← ENNReal.ofReal_mul (Real.exp_pos _).le]
    _ ≤ ENNReal.ofReal ρ := by
        apply ENNReal.ofReal_le_ofReal
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        dsimp [q]
        linarith

/-- The physical-kernel version of `EinsteinFull.Regeneration.uniform_first_candidate_height`. -/
theorem uniform_first_candidate_height_phys {d : ℕ} (hd : 2 ≤ d) (Λ₀ r₀ l : ℝ) (hl : 0 < l) :
    ∃ b D : ℝ, 0 < b ∧ 0 < D ∧
      ∀ (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1)
        (P : QuenchedPathLaws d),
        EinsteinFull.Regeneration.IsGMPPhysicalKernelReducedBound hd Q.ellipticity_parameter Q lam h0.le h1 P →
        ∀ᵐ ω ∂Q.measure, ∀ (x : Vec d) (i : Fin d) (a : ℝ), 0 ≤ a →
          ∫⁻ γ, {γ : Path d |
              firstRoundedCandidate (Renewal.regenDelta lam) lam (l / lam) a γ i ≠ ⊤}.indicator
            (fun γ => ENNReal.ofReal (Real.exp (b * lam *
              (γ (firstRoundedCandidate (Renewal.regenDelta lam) lam (l / lam) a γ i).toNNReal i -
                γ 0 i - a / lam)))) γ ∂P (x, ω) ≤ ENNReal.ofReal D := by
  obtain ⟨b, ρ, hb, hρ0, hρ1, hwin⟩ := uniform_failed_window_weight_phys hd Λ₀ r₀ l hl
  refine ⟨b, Real.exp (b * (l / 2)) / (1 - ρ), hb,
    div_pos (Real.exp_pos _) (sub_pos.mpr hρ1), ?_⟩
  intro Q lam h0 h1 P hP
  filter_upwards [hP, hwin Q lam h0 h1 P hP] with ω hreal hw
  obtain ⟨hω, G, hrow⟩ := hreal
  intro x i a ha
  have hRpos : 0 < l / lam := div_pos hl h0
  have hwinG : ∀ y, ∫⁻ η, failedWindowWeight (Renewal.regenDelta lam) lam (l / lam) b i η
      ∂G.pathLaw y ≤ ENNReal.ofReal ρ := by
    intro y
    rw [← hrow y]
    exact hw y i
  have h := first_candidate_height_lintegral_le hd ω lam
    (sourceReducedBound Λ₀) (one_le_sourceReducedBound Q.ellipticity_parameter) hω
    h0.le h1 G (Renewal.regenDelta lam) (EinsteinRelation.regenDelta_pos h0) lam (l / lam) a b
    h0 hRpos (div_nonneg ha h0.le) hb.le i ρ hρ0 hρ1 hwinG x
  have hexp : b * lam * (l / lam / 2) = b * (l / 2) := by
    field_simp
  rw [hexp] at h
  rw [hrow x]
  exact h

end EinsteinFull.Regeneration
