import EinsteinFull.Calculus.C10LocalTimeForwardGradientMoment
import EinsteinFull.Calculus.C10LocalTimeStationaryAverage
import Mathlib.Probability.ConditionalProbability
import EinsteinFull.Calculus.C9LocalTimeTransposeMomentAssembly

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinFull

/-- The literal transpose elliptic equation controls the normalized terminal
 gradient by its solution and generator-output masses. The constant is fixed
 before the environment law and force. -/
theorem local_time_transpose_terminal_gradient_average
    (d : ℕ) [Fact (2 ≤ d)] (Λ₀ : ℝ) (hΛ : 1 ≤ Λ₀) :
    ∃ C : ℝ, 0 < C ∧
    ∀ {r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
      {f g : Lp ℂ 2 (reducedLaw Q)},
      IsComplexTransposeGeneratorPair Q i ζ f g →
    ∀ G : Fin d → Lp ℂ 2 (reducedLaw Q),
      HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G →
    ∀ (t : ℝ) (_ht : 0 < t) (ρ : ℝ) (_hρ : Real.sqrt t ≤ ρ) (z : Vec d),
      ∀ᵐ ω ∂reducedLaw Q,
        (⨍ x in {x | euclideanNorm (x - z) < ρ}, ∑ j, ‖G j (translate x ω)‖ ^ 2) ≤
          C * ((1 + ‖ζ‖ * Real.sqrt t) ^ 2 / t *
            (⨍ x in {x | euclideanNorm (x - z) < 4 * ρ}, ‖f (translate x ω)‖ ^ 2) +
            t * (⨍ x in {x | euclideanNorm (x - z) < 4 * ρ}, ‖g (translate x ω)‖ ^ 2)) := by
  let L := Real.exp (2 * Λ₀) * Λ₀
  let A := 10 * L ^ 3
  let B := Classical.choose (exists_physical_gap_euclidean_cutoff d)
  let H := 1 / 2 + A * (1 + (d : ℝ) * B ^ 2)
  let C := 4 * L * (4 : ℝ) ^ d * (H + 1)
  have hL : 0 < L := mul_pos (Real.exp_pos _) (lt_of_lt_of_le zero_lt_one hΛ)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hH : 0 < H := by dsimp [H]; positivity
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro r₀ Q i ζ f g hfg G hG t ht ρ hρ z
  have hρpos : 0 < ρ := (Real.sqrt_pos.mpr ht).trans_le hρ
  let q := 1 + ‖ζ‖ * Real.sqrt t
  have hq : 1 ≤ q := le_add_of_nonneg_right (mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))
  have htρ : t ≤ ρ ^ 2 := by
    calc
      t = (Real.sqrt t) ^ 2 := (Real.sq_sqrt ht.le).symm
      _ ≤ ρ ^ 2 := (sq_le_sq₀ (Real.sqrt_nonneg _) hρpos.le).mpr hρ
  have hz : ‖ζ‖ ^ 2 ≤ q ^ 2 / t := by
    apply (le_div_iff₀ ht).mpr
    have hh : ‖ζ‖ * Real.sqrt t ≤ q := by dsimp [q]; linarith
    have hh' := (sq_le_sq₀ (by positivity : 0 ≤ ‖ζ‖ * Real.sqrt t)
      (by linarith : 0 ≤ q)).mpr hh
    rwa [mul_pow, Real.sq_sqrt ht.le] at hh'
  have hiρ : 1 / ρ ^ 2 ≤ q ^ 2 / t := by
    calc
      _ ≤ 1 / t := one_div_le_one_div_of_le ht htρ
      _ ≤ q ^ 2 / t := div_le_div_of_nonneg_right (by nlinarith) ht.le
  have hcoeff : 1 / (2 * t) + A * (‖ζ‖ ^ 2 + (d : ℝ) * B ^ 2 / (2 * ρ - ρ) ^ 2) ≤
      H * q ^ 2 / t := by
    rw [show 2 * ρ - ρ = ρ by ring]
    calc
      _ = (1 / 2 : ℝ) * (1 / t) + A * (‖ζ‖ ^ 2 + (d : ℝ) * B ^ 2 * (1 / ρ ^ 2)) := by ring
      _ ≤ (1 / 2 : ℝ) * (q ^ 2 / t) + A * (q ^ 2 / t + (d : ℝ) * B ^ 2 * (q ^ 2 / t)) := by
        gcongr; nlinarith
      _ = _ := by dsimp [H]; ring
  have hlocal (u : Lp ℂ 2 (reducedLaw Q)) :=
    ae_complex_orbit_memLp_on_all_compacts (reducedLaw Q) (reducedLaw_stationary Q) u
  filter_upwards [local_time_transpose_physical_ball_gradient hfg hG,
    hlocal f, hlocal g, ae_all_iff.mpr (fun j => hlocal (G j))] with ω hg hf hgout hgl
  have hi (u : Lp ℂ 2 (reducedLaw Q))
      (hu : ∀ K, IsCompact K → MemLp (fun x => u (translate x ω)) 2 (volume.restrict K)) :
      IntegrableOn (fun x => ‖u (translate x ω)‖ ^ 2)
        {x | euclideanNorm (x - z) ≤ 4 * ρ} volume :=
    (memLp_two_iff_integrable_sq_norm
      (hu _ (isCompact_physical_euclidean_closedBall z (4 * ρ))).aestronglyMeasurable).mp
      (hu _ (isCompact_physical_euclidean_closedBall z (4 * ρ)))
  have henlarge (u : Lp ℂ 2 (reducedLaw Q))
      (hu : ∀ K, IsCompact K → MemLp (fun x => u (translate x ω)) 2 (volume.restrict K)) :
      (∫ x in {x | euclideanNorm (x - z) ≤ 2 * ρ}, ‖u (translate x ω)‖ ^ 2) ≤
        ∫ x in {x | euclideanNorm (x - z) < 4 * ρ}, ‖u (translate x ω)‖ ^ 2 := by
    apply setIntegral_mono_set ((hi u hu).mono_set (fun x hx =>
      show euclideanNorm (x - z) ≤ 4 * ρ from hx.le))
      (ae_of_all _ fun _ => sq_nonneg _)
    exact ae_of_all _ fun x (hx : euclideanNorm (x - z) ≤ 2 * ρ) =>
      show euclideanNorm (x - z) < 4 * ρ from lt_of_le_of_lt hx (by linarith)
  have hgrad := hg z ρ (2 * ρ) hρpos (by linarith) t ht
  change (L⁻¹ / 4) * _ ≤ _ at hgrad
  have hb := hgrad.trans (add_le_add
    (mul_le_mul hcoeff (henlarge f hf) (integral_nonneg fun _ => sq_nonneg _) (by positivity))
    (mul_le_mul_of_nonneg_left (henlarge g hgout) (by positivity : 0 ≤ t / 2)))
  have hLinv : 4 * L * (L⁻¹ / 4) = 1 := by field_simp
  have hb := mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ 4 * L)
  rw [← mul_assoc, hLinv, one_mul] at hb
  have hgi := integrable_finsetSum Finset.univ (fun j _ =>
    (memLp_two_iff_integrable_sq_norm
      (hgl j _ (isCompact_physical_euclidean_closedBall z ρ)).aestronglyMeasurable).mp
        (hgl j _ (isCompact_physical_euclidean_closedBall z ρ)))
  have hopen : (∫ x in {x | euclideanNorm (x - z) < ρ}, ∑ j, ‖G j (translate x ω)‖ ^ 2) ≤
      ∫ x in {x | euclideanNorm (x - z) ≤ ρ}, ∑ j, ‖G j (translate x ω)‖ ^ 2 :=
    setIntegral_mono_set hgi (ae_of_all _ fun _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
      (ae_of_all _ fun x (hx : euclideanNorm (x - z) < ρ) =>
        show euclideanNorm (x - z) ≤ ρ from hx.le)
  have hb := hopen.trans hb
  have hv := localSpatialEnergy_window_volume z ρ hρpos
  have hs := local_time_window_volume_dilation z hρpos (show (0 : ℝ) < 4 by norm_num)
  have hb := mul_le_mul_of_nonneg_left hb (le_of_lt (inv_pos.mpr hv))
  simp only [average_eq, measureReal_restrict_apply_univ, smul_eq_mul]
  rw [hs]
  have hfm : 0 ≤ ∫ x in {x | euclideanNorm (x - z) < 4 * ρ}, ‖f (translate x ω)‖ ^ 2 :=
    integral_nonneg fun _ => sq_nonneg _
  have hgm : 0 ≤ ∫ x in {x | euclideanNorm (x - z) < 4 * ρ}, ‖g (translate x ω)‖ ^ 2 :=
    integral_nonneg fun _ => sq_nonneg _
  apply hb.trans
  calc
    _ ≤ (volume.real {x | euclideanNorm (x - z) < ρ})⁻¹ *
        (4 * L * (((H + 1) * q ^ 2 / t) *
          (∫ x in {x | euclideanNorm (x - z) < 4 * ρ}, ‖f (translate x ω)‖ ^ 2) +
          ((H + 1) * t) *
          (∫ x in {x | euclideanNorm (x - z) < 4 * ρ}, ‖g (translate x ω)‖ ^ 2))) := by
      gcongr
      · exact le_add_of_nonneg_right (by norm_num)
      · nlinarith
    _ = _ := by
      dsimp only [C, q]
      field_simp [hv.ne']

/-- Transfer terminal scalar mass bounds to the actual transpose gradient in
finite p. The output bound includes the time weight in localSpatialEnergy. -/
theorem local_time_transpose_terminal_gradient_moment
    (d : ℕ) [Fact (2 ≤ d)] (Λ₀ : ℝ) (hΛ : 1 ≤ Λ₀) :
    ∃ C : ℝ, 0 < C ∧
    ∀ {r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
      {f g : Lp ℂ 2 (reducedLaw Q)},
      IsComplexTransposeGeneratorPair Q i ζ f g →
    ∀ G : Fin d → Lp ℂ 2 (reducedLaw Q),
      HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G →
    ∀ (t : ℝ≥0) (ht : 0 < (t : ℝ)) (ρ : ℝ) (hρ : Real.sqrt (t : ℝ) ≤ ρ)
      (z : Vec d) {p : ℝ≥0∞}, 1 ≤ p →
    ∀ N M : FieldPair d → ℝ,
      MemLp N p (reducedLaw Q) → MemLp M p (reducedLaw Q) →
      (∀ᵐ ω ∂reducedLaw Q, 0 ≤ N ω ∧ 0 ≤ M ω) →
      (∀ᵐ ω ∂reducedLaw Q,
        (⨍ x in {x | euclideanNorm (x - z) < 4 * ρ}, ‖f (translate x ω)‖ ^ 2) ≤ N ω ^ 2 ∧
        (t : ℝ) * (⨍ x in {x | euclideanNorm (x - z) < 4 * ρ},
          ‖g (translate x ω)‖ ^ 2) ≤ M ω ^ 2) →
      MemLp (localSpatialEnergy Q t ρ ((Real.sqrt_pos.mpr ht).trans_le hρ) z G 0)
        p (reducedLaw Q) ∧
      eLpNorm (localSpatialEnergy Q t ρ ((Real.sqrt_pos.mpr ht).trans_le hρ) z G 0)
        p (reducedLaw Q) ≤ ENNReal.ofReal (Real.sqrt C) *
        (ENNReal.ofReal ((1 + ‖ζ‖ * Real.sqrt (t : ℝ)) / Real.sqrt (t : ℝ)) *
          eLpNorm N p (reducedLaw Q) + eLpNorm M p (reducedLaw Q)) := by
  obtain ⟨C, hC, hterminal⟩ := local_time_transpose_terminal_gradient_average d Λ₀ hΛ
  refine ⟨C, hC, ?_⟩
  intro r₀ Q i ζ f g hfg G hG t ht ρ hρ z p hp N M hN hM hpos hmass
  let α := (1 + ‖ζ‖ * Real.sqrt (t : ℝ)) / Real.sqrt (t : ℝ)
  have hα : 0 ≤ α := by dsimp [α]; positivity
  have hαsq : α ^ 2 = (1 + ‖ζ‖ * Real.sqrt (t : ℝ)) ^ 2 / (t : ℝ) := by
    dsimp [α]
    rw [div_pow, Real.sq_sqrt ht.le]
  have hNM := (hN.const_mul α).add hM
  have hbound : ∀ᵐ ω ∂reducedLaw Q,
      (⨍ x in {x | euclideanNorm (x - z) < ρ}, ∑ j, ‖G j (translate x ω)‖ ^ 2) ≤
        C * (α * N ω + M ω) ^ 2 := by
    filter_upwards [hterminal hfg G hG t ht ρ hρ z, hmass, hpos] with ω hterm hm hp
    apply hterm.trans
    apply mul_le_mul_of_nonneg_left _ hC.le
    rw [← hαsq]
    have he := add_le_add (mul_le_mul_of_nonneg_left hm.1 (sq_nonneg α)) hm.2
    apply he.trans
    nlinarith [mul_nonneg (mul_nonneg hα hp.1) hp.2]
  obtain ⟨hmem, hnorm⟩ := local_time_zero_derivative_moment_of_sq_bound
    Q t ρ ((Real.sqrt_pos.mpr ht).trans_le hρ) z G hNM
    (hpos.mono fun ω hω => add_nonneg (mul_nonneg hα hω.1) hω.2) hC.le hbound
  refine ⟨hmem, hnorm.trans (mul_le_mul_of_nonneg_left ?_ zero_le)⟩
  have hscale : eLpNorm (fun ω => α * N ω) p (reducedLaw Q) ≤
      ENNReal.ofReal α * eLpNorm N p (reducedLaw Q) := by
    apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul (hN.const_mul α).aestronglyMeasurable
    exact ae_of_all _ fun ω => by rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hα]
  exact (eLpNorm_add_le hp).trans (add_le_add hscale (le_refl _))

/-- The transpose terminal gradient is controlled by the global solution
moment and the literal local derivative energy. No generator graph for the
output is required. -/
theorem local_time_transpose_gradient_from_local_output
    (d : ℕ) [Fact (2 ≤ d)] (Λ₀ : ℝ) (hΛ : 1 ≤ Λ₀) :
    ∃ C : ℝ, 0 < C ∧
    ∀ {r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
      {f g : Lp ℂ 2 (reducedLaw Q)},
      IsComplexTransposeGeneratorPair Q i ζ f g →
    ∀ G : Fin d → Lp ℂ 2 (reducedLaw Q),
      HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G →
    ∀ (t : ℝ≥0) (ht : 0 < (t : ℝ)) (ρ : ℝ) (hρ : Real.sqrt (t : ℝ) ≤ ρ)
      (z : Vec d) (p : ℝ), 2 ≤ p →
      MemLp f (ENNReal.ofReal p) (reducedLaw Q) →
      MemLp (localSpatialEnergy Q t (4 * ρ)
        (by have := (Real.sqrt_pos.mpr ht).trans_le hρ; positivity) z 0 g)
        (ENNReal.ofReal p) (reducedLaw Q) →
      MemLp (localSpatialEnergy Q t ρ ((Real.sqrt_pos.mpr ht).trans_le hρ) z G 0)
        (ENNReal.ofReal p) (reducedLaw Q) ∧
      (eLpNorm (localSpatialEnergy Q t ρ ((Real.sqrt_pos.mpr ht).trans_le hρ) z G 0)
        (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤ Real.sqrt C *
        (((1 + ‖ζ‖ * Real.sqrt (t : ℝ)) / Real.sqrt (t : ℝ)) *
          (eLpNorm f (ENNReal.ofReal p) (reducedLaw Q)).toReal +
          (eLpNorm (localSpatialEnergy Q t (4 * ρ)
            (by have := (Real.sqrt_pos.mpr ht).trans_le hρ; positivity) z 0 g)
            (ENNReal.ofReal p) (reducedLaw Q)).toReal) := by
  obtain ⟨C, hC, htransfer⟩ := local_time_transpose_terminal_gradient_moment d Λ₀ hΛ
  refine ⟨C, hC, ?_⟩
  intro r₀ Q i ζ f g hfg G hG t ht ρ hρ z p hp hf hg
  have hr : 0 < ρ := (Real.sqrt_pos.mpr ht).trans_le hρ
  have h4r : 0 < 4 * ρ := by positivity
  let S := {x : Vec d | euclideanNorm (x - z) < 4 * ρ}
  have hv := localSpatialEnergy_window_volume z (4 * ρ) h4r
  have hv' := ENNReal.toReal_pos_iff.mp hv
  let κ := ProbabilityTheory.cond (volume : Measure (Vec d)) S
  let : IsProbabilityMeasure κ :=
    ProbabilityTheory.cond_isProbabilityMeasure_of_finite hv'.1.ne' hv'.2.ne
  let N := fun ω : FieldPair d => Real.sqrt (⨍ x in S, ‖f (translate x ω)‖ ^ 2)
  let M := localSpatialEnergy Q t (4 * ρ) h4r z 0 g
  have hN := local_time_stationary_square_average_memLp Q
    (Measure.dirac (0 : ℝ)) κ p (eLpNorm f (ENNReal.ofReal p) (reducedLaw Q)).toReal
    hp ENNReal.toReal_nonneg (fun q : ℝ × FieldPair d => f q.2)
    ((Lp.stronglyMeasurable f).measurable.comp measurable_snd)
    (ae_of_all _ fun _ => ⟨hf, le_refl _⟩)
  have heq : (fun ω : FieldPair d => Real.sqrt
      (∫ s : ℝ, ∫ x, ‖f (translate x ω)‖ ^ 2 ∂κ ∂Measure.dirac (0 : ℝ))) = N := by
    funext ω
    simp only [integral_const, measureReal_def, Measure.dirac_apply_of_mem (mem_univ _),
      ENNReal.toReal_one, one_smul]
    congr 1
    rw [show κ = (volume S)⁻¹ • volume.restrict S from rfl, integral_smul_measure]
    simp only [average_eq, smul_eq_mul, ENNReal.toReal_inv, Measure.real,
      Measure.restrict_apply_univ]
  rw [heq] at hN
  have hp' : 1 ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  obtain ⟨hmem, hnorm⟩ := htransfer hfg G hG t ht ρ hρ z hp' N M hN.1 hg
    (ae_of_all _ fun _ => ⟨Real.sqrt_nonneg _, Real.sqrt_nonneg _⟩) (by
      filter_upwards [local_time_zero_gradient_energy_sq Q t (4 * ρ) h4r z g] with ω hω
      exact ⟨by dsimp [N]; rw [Real.sq_sqrt (average_nonneg fun _ => sq_nonneg _)], hω.ge⟩)
  refine ⟨hmem, ?_⟩
  have hn := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hN.1.ne_top,
        hg.ne_top⟩)) hnorm
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.sqrt_nonneg C),
    ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hN.1.ne_top) hg.ne_top,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at hn
  exact hn.trans (mul_le_mul_of_nonneg_left
    (add_le_add (mul_le_mul_of_nonneg_left hN.2 (by positivity)) (le_refl _))
    (Real.sqrt_nonneg C))

set_option linter.unusedVariables false in
/-- The transpose gradient moment with the exact early slice and actual
shared endpoint witnesses, obtained from the derivative moment. -/
theorem local_time_transpose_gradient_moment_of_deps
  (h0 : EinsteinFull.Blueprint.node_l_u3A_forced_u2D_local_u23_centered_u2D_sourceStmt)
  (h1 : EinsteinFull.Blueprint.node_e_u3A_lp_u2D_growthStmt) :
∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d),
    ∀ p : ℝ, 2 ≤ p → ∃ C Cp : ℝ, 1 ≤ C ∧ 0 < Cp ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ ζ : ℂ,
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
      IsComplexTransposeSemigroup Q P Pdag → ∀ ν : EndpointIndex d, ν = .inr true →
    ∃ G : ℝ≥0 → Fin d → Lp ℂ 2 (reducedLaw Q),
    ∃ V : ℝ≥0 → Lp ℂ 2 (reducedLaw Q),
    (∀ t : ℝ≥0, 0 < (t : ℝ) →
      HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
        (indexedEndpoint hd Q ν ζ P Pdag β a μ t) (G t) ∧
      HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
        (uncenteredEndpoint hd Q ν ζ P Pdag β a μ t) (G t) ∧
      HasDerivAt (fun r : ℝ => indexedEndpoint hd Q ν ζ P Pdag β a μ r.toNNReal)
        (V t) (t : ℝ)) ∧
    (∀ (t : ℝ≥0) (ht : 0 < (t : ℝ)),
      let U := indexedEndpoint hd Q ν ζ P Pdag β a μ t
      let U₈ := indexedEndpoint hd Q ν ζ P Pdag β a μ (t / 8)
      MemLp (U₈ : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) ∧
      (∀ (ρ : ℝ) (x : Vec d) (hρ : Real.sqrt (t : ℝ) ≤ ρ),
        MemLp (localSpatialEnergy Q t ρ (lt_of_lt_of_le (Real.sqrt_pos.mpr ht) hρ) x (G t) (0)) (ENNReal.ofReal p) (reducedLaw Q) ∧
        (eLpNorm (localSpatialEnergy Q t ρ (lt_of_lt_of_le (Real.sqrt_pos.mpr ht) hρ) x (G t) (0))
          (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
        C * (1 + ‖ζ‖ * Real.sqrt (t : ℝ)) ^ C * (t : ℝ) ^ (-(1 / 2 : ℝ)) *
          Real.exp (Cp * ‖ζ‖ ^ 2 * (t : ℝ)) *
          (eLpNorm (U₈ : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal)) := by
  intro d hd D p hp
  let : Fact (2 ≤ d) := ⟨hd⟩
  obtain ⟨K, hK, hterminal⟩ := local_time_transpose_gradient_from_local_output
    d D.ellipticity D.one_le_ellipticity
  obtain ⟨A, B, hA, hB, hderivative⟩ :=
    local_time_transpose_derivative_moment_of_deps h0 h1 d hd D p hp
  obtain ⟨E, hE, hgrowth⟩ := local_time_transpose_slice_moment_of_growth
    h1 d hd D.ellipticity D.dependenceRange p hp
  let C := max A (max 1 (Real.sqrt K * (1 + A)))
  let Cp := max B E
  have hAC : A ≤ C := le_max_left _ _
  have hC1 : 1 ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hKC : Real.sqrt K * (1 + A) ≤ C :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hBC : B ≤ Cp := le_max_left _ _
  have hEC : E ≤ Cp := le_max_right _ _
  refine ⟨C, Cp, hC1, hB.trans_le hBC, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P T hP hT ν hν
  subst ν
  obtain ⟨G, V, hGV, hmoment⟩ := hderivative Q hQ β a μ hβ ha hμ ζ P T hP hT
    (.inr true) rfl
  obtain ⟨g, _, hfg, _, hder, _⟩ :=
    local_time_transpose_endpoint_orbit_witnesses hd Q hQ β a μ hβ ζ P T hP hT
  refine ⟨G, V, hGV, ?_⟩
  intro t ht U U₈
  obtain ⟨hu8, hdv⟩ := hmoment t ht
  refine ⟨hu8, ?_⟩
  have hgraph : IsComplexTransposeGeneratorPair Q ⟨0, by omega⟩ ζ U (V t) := by
    have he : V t = T t g := (hGV t ht).2.2.unique (hder t ht)
    rw [he]
    exact hT.map_generator hP hfg t
  have h8 : t / 8 ≤ t := div_le_self zero_le (by norm_num)
  obtain ⟨hu, hunorm⟩ := hgrowth Q ⟨0, by omega⟩ ζ P T hP hT
    (β ⟨0, by omega⟩) (t / 8) t t h8 le_rfl hu8
  intro ρ z hρ
  have h4ρ : Real.sqrt (t : ℝ) ≤ 4 * ρ := by
    have hr := (Real.sqrt_pos.mpr ht).trans_le hρ
    linarith
  obtain ⟨hvm, hvnorm⟩ := hdv (4 * ρ) z h4ρ
  obtain ⟨hgm, hgnorm⟩ := hterminal hgraph (G t) (hGV t ht).1 t ht ρ hρ z p hp hu hvm
  refine ⟨hgm, ?_⟩
  let q := 1 + ‖ζ‖ * Real.sqrt (t : ℝ)
  let n := (eLpNorm (U₈ : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal
  have hq : 1 ≤ q := le_add_of_nonneg_right (mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))
  have hqpow : q ≤ q ^ C := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hq hC1
  have hApow : q ^ A ≤ q ^ C := Real.rpow_le_rpow_of_exponent_le hq hAC
  have hBexp : Real.exp (B * ‖ζ‖ ^ 2 * (t : ℝ)) ≤
      Real.exp (Cp * ‖ζ‖ ^ 2 * (t : ℝ)) := by gcongr
  have hEexp : Real.exp (E * ‖ζ‖ ^ 2 * (t : ℝ)) ≤
      Real.exp (Cp * ‖ζ‖ ^ 2 * (t : ℝ)) := by gcongr
  have hinv : (t : ℝ) ^ (-(1 / 2 : ℝ)) = (Real.sqrt (t : ℝ))⁻¹ := by
    rw [Real.rpow_neg ht.le, ← Real.sqrt_eq_rpow]
  have hsolution : q / Real.sqrt (t : ℝ) * (eLpNorm U (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
      q ^ C * (t : ℝ) ^ (-(1 / 2 : ℝ)) * Real.exp (Cp * ‖ζ‖ ^ 2 * (t : ℝ)) * n := by
    calc
      _ ≤ q / Real.sqrt (t : ℝ) * (Real.exp (E * ‖ζ‖ ^ 2 * (t : ℝ)) * n) :=
        mul_le_mul_of_nonneg_left hunorm (by positivity)
      _ ≤ q ^ C / Real.sqrt (t : ℝ) * (Real.exp (Cp * ‖ζ‖ ^ 2 * (t : ℝ)) * n) := by
        gcongr
      _ = _ := by rw [hinv]; ring
  have houtput : (eLpNorm (localSpatialEnergy Q t (4 * ρ)
      ((Real.sqrt_pos.mpr ht).trans_le h4ρ) z 0 (V t)) (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
      A * q ^ C * (t : ℝ) ^ (-(1 / 2 : ℝ)) * Real.exp (Cp * ‖ζ‖ ^ 2 * (t : ℝ)) * n := by
    apply hvnorm.trans
    gcongr
  apply hgnorm.trans
  calc
    _ ≤ Real.sqrt K *
        (q ^ C * (t : ℝ) ^ (-(1 / 2 : ℝ)) * Real.exp (Cp * ‖ζ‖ ^ 2 * (t : ℝ)) * n +
         A * q ^ C * (t : ℝ) ^ (-(1 / 2 : ℝ)) * Real.exp (Cp * ‖ζ‖ ^ 2 * (t : ℝ)) * n) :=
      mul_le_mul_of_nonneg_left (add_le_add hsolution houtput) (Real.sqrt_nonneg K)
    _ = (Real.sqrt K * (1 + A)) * q ^ C * (t : ℝ) ^ (-(1 / 2 : ℝ)) *
        Real.exp (Cp * ‖ζ‖ ^ 2 * (t : ℝ)) * n := by ring
    _ ≤ _ := by gcongr

set_option linter.unusedVariables false in
/-- The full gradient part of the local-time estimate, with common constants
for every endpoint and the exact source dependency statements. -/
theorem local_time_gradient_moment_of_deps
  (h0 : EinsteinFull.Blueprint.node_l_u3A_forced_u2D_local_u23_centered_u2D_sourceStmt)
  (h1 : EinsteinFull.Blueprint.node_e_u3A_lp_u2D_growthStmt) :
∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d),
    ∀ p : ℝ, 2 ≤ p → ∃ C Cp : ℝ, 1 ≤ C ∧ 0 < Cp ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ ζ : ℂ,
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
      IsComplexTransposeSemigroup Q P Pdag → ∀ ν : EndpointIndex d,
    ∃ G : ℝ≥0 → Fin d → Lp ℂ 2 (reducedLaw Q),
    ∃ V : ℝ≥0 → Lp ℂ 2 (reducedLaw Q),
    (∀ t : ℝ≥0, 0 < (t : ℝ) →
      HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
        (indexedEndpoint hd Q ν ζ P Pdag β a μ t) (G t) ∧
      HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
        (uncenteredEndpoint hd Q ν ζ P Pdag β a μ t) (G t) ∧
      HasDerivAt (fun r : ℝ => indexedEndpoint hd Q ν ζ P Pdag β a μ r.toNNReal)
        (V t) (t : ℝ)) ∧
    (∀ (t : ℝ≥0) (ht : 0 < (t : ℝ)),
      let U := indexedEndpoint hd Q ν ζ P Pdag β a μ t
      let U₈ := indexedEndpoint hd Q ν ζ P Pdag β a μ (t / 8)
      MemLp (U₈ : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) ∧
      (∀ (ρ : ℝ) (x : Vec d) (hρ : Real.sqrt (t : ℝ) ≤ ρ),
        MemLp (localSpatialEnergy Q t ρ (lt_of_lt_of_le (Real.sqrt_pos.mpr ht) hρ) x (G t) (0)) (ENNReal.ofReal p) (reducedLaw Q) ∧
        (eLpNorm (localSpatialEnergy Q t ρ (lt_of_lt_of_le (Real.sqrt_pos.mpr ht) hρ) x (G t) (0))
          (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
        C * (1 + ‖ζ‖ * Real.sqrt (t : ℝ)) ^ C * (t : ℝ) ^ (-(1 / 2 : ℝ)) *
          Real.exp (Cp * ‖ζ‖ ^ 2 * (t : ℝ)) *
          (eLpNorm (U₈ : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal)) := by
  intro d hd D p hp
  obtain ⟨Cf, Bf, hCf, hBf, hforward⟩ :=
    local_time_forward_gradient_moment_of_deps h0 h1 d hd D p hp
  obtain ⟨Ct, Bt, hCt, hBt, htranspose⟩ :=
    local_time_transpose_gradient_moment_of_deps h0 h1 d hd D p hp
  let C := max Cf Ct
  let Cp := max Bf Bt
  have hfC : Cf ≤ C := le_max_left _ _
  have htC : Ct ≤ C := le_max_right _ _
  have hfB : Bf ≤ Cp := le_max_left _ _
  have htB : Bt ≤ Cp := le_max_right _ _
  refine ⟨C, Cp, hCf.trans hfC, hBf.trans_le hfB, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P T hP hT ν
  have hmono (A B : ℝ) (hA : 0 ≤ A) (hAC : A ≤ C) (hBC : B ≤ Cp)
      (t : ℝ≥0) :
      A * (1 + ‖ζ‖ * Real.sqrt (t : ℝ)) ^ A * (t : ℝ) ^ (-(1 / 2 : ℝ)) *
        Real.exp (B * ‖ζ‖ ^ 2 * (t : ℝ)) ≤
      C * (1 + ‖ζ‖ * Real.sqrt (t : ℝ)) ^ C * (t : ℝ) ^ (-(1 / 2 : ℝ)) *
        Real.exp (Cp * ‖ζ‖ ^ 2 * (t : ℝ)) := by
    have hq : 1 ≤ 1 + ‖ζ‖ * Real.sqrt (t : ℝ) :=
      le_add_of_nonneg_right (mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))
    have hpow := Real.rpow_le_rpow_of_exponent_le hq hAC
    have hexp : Real.exp (B * ‖ζ‖ ^ 2 * (t : ℝ)) ≤
        Real.exp (Cp * ‖ζ‖ ^ 2 * (t : ℝ)) := by gcongr
    gcongr
  by_cases hν : ν = .inr true
  · obtain ⟨G, V, hGV, hmoment⟩ := htranspose Q hQ β a μ hβ ha hμ ζ P T hP hT ν hν
    refine ⟨G, V, hGV, ?_⟩
    intro t ht U U₈
    obtain ⟨hu8, hgradient⟩ := hmoment t ht
    refine ⟨hu8, ?_⟩
    intro ρ x hρ
    obtain ⟨hm, hn⟩ := hgradient ρ x hρ
    exact ⟨hm, hn.trans (mul_le_mul_of_nonneg_right
      (hmono Ct Bt (by linarith) htC htB t) ENNReal.toReal_nonneg)⟩
  · obtain ⟨G, V, hGV, hmoment⟩ := hforward Q hQ β a μ hβ ha hμ ζ P T hP hT ν hν
    refine ⟨G, V, hGV, ?_⟩
    intro t ht U U₈
    obtain ⟨hu8, hgradient⟩ := hmoment t ht
    refine ⟨hu8, ?_⟩
    intro ρ x hρ
    obtain ⟨hm, hn⟩ := hgradient ρ x hρ
    exact ⟨hm, hn.trans (mul_le_mul_of_nonneg_right
      (hmono Cf Bf (by linarith) hfC hfB t) ENNReal.toReal_nonneg)⟩

end EinsteinFull.Blueprint
