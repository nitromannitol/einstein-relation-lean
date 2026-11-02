import EinsteinFull.Calculus.C1LocalTimeGradientMoment
import EinsteinFull.Calculus.C4LocalTimeDerivativeMoment

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinFull
/-- The corrected solution and its actual generator output control the terminal
Euclidean gradient, with constants fixed before the law and force. -/
theorem local_time_corrected_gradient_mass_largeRadius
    (d : ℕ) [Fact (2 ≤ d)] (Λ₀ : ℝ) (hΛ : 1 ≤ Λ₀) :
    ∃ C : ℝ, 0 < C ∧
    ∀ {r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (f : Lp ℂ 2 (reducedLaw Q)) {t a b : ℝ}
    (_ht : 0 < t) (_ha : 0 < a) (_hab : a < b) (_hb : b < t / 4),
    let w := fun s : ℝ => centeredComplexLp Q (P s.toNNReal (centeredComplexLp Q f)) +
      Lp.const 2 (reducedLaw Q) (∫ v in (t / 4)..s, hP.centeringSource f v)
    ∀ U : ℝ × FieldPair d → ℂ, Measurable U →
      (∀ s, 0 < s → (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] w s) →
    ∀ G : Fin d → Lp ℂ 2 (reducedLaw Q),
      HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) (w t) G →
    ∀ z : Vec d, ∀ ρ : ℝ, Real.sqrt t ≤ ρ → ∀ᵐ ω ∂reducedLaw Q,
      (∫ x in {x | euclideanNorm (x - z) ≤ ρ}, ∑ j, ‖G j (translate x ω)‖ ^ 2) ≤
        (C * (1 + ‖ζ‖ * Real.sqrt t) ^ 6 / t ^ 2) *
          (∫ s in Icc (t / 4) t,
            ∫ x in {x | euclideanNorm (x - z) < 16 * ρ}, ‖U (s, translate x ω)‖ ^ 2) := by
  obtain ⟨Cm, hCm, hmass⟩ := local_time_uniform_corrected_orbit_mass_largeRadius d Λ₀ hΛ
  obtain ⟨Cd, hCd, hderiv⟩ :=
    local_time_uniform_corrected_orbit_derivative_largeRadius d Λ₀ hΛ
  let L := Real.exp (2 * Λ₀) * Λ₀
  let A := 2 * (d : ℝ) * ((d : ℝ) + 1) * L ^ 3
  let B := Classical.choose (exists_physical_gap_euclidean_cutoff d)
  let H := 1 / 2 + A * (1 + (d : ℝ) * B ^ 2)
  let C := 4 * L * (H * Cm + Cd / 2)
  have hL : 0 < L := mul_pos (Real.exp_pos _) (lt_of_lt_of_le zero_lt_one hΛ)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hH : 0 < H := by dsimp [H]; positivity
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro r₀ Q i ζ P hP f t a b ht ha hab hb w U hU heU G hG z ρ hρ
  let := reducedLaw_probability Q
  have hρpos : 0 < ρ := (Real.sqrt_pos.mpr ht).trans_le hρ
  have h2ρ : Real.sqrt t ≤ 2 * ρ := by linarith
  obtain ⟨Wm, hWm, heWm, hmb⟩ := hmass hP f ht ha (hab.trans hb)
  obtain ⟨g, Wd, V, hWd, _, heWd, _, hreg, hdb⟩ := hderiv hP f ht ha hab
  have hgrad := local_time_physical_ball_gradient (hreg t (by linarith)).2 hG
  have hu : Continuous (fun s : ℝ =>
      centeredComplexLp Q (P s.toNNReal (centeredComplexLp Q f))) := by
    simpa only [Function.comp_def, centeredComplexLpCLM_apply] using
      (centeredComplexLpCLM Q).continuous.comp
        ((hP.2.2.1 (centeredComplexLp Q f)).comp continuous_real_toNNReal)
  have hw : Continuous w := hu.add ((Lp.constL 2 (reducedLaw Q) ℂ).continuous.comp
    (Blueprint.continuous_centered_source_primitive hP f (t / 4)))
  have hlocal (W : ℝ × FieldPair d → ℂ) (hW : Measurable W)
      (heW : ∀ s, (fun ω => W (s, ω)) =ᵐ[reducedLaw Q] w s) :=
    ae_locally_memLp_joint_spatial_translate (reducedLaw Q) (reducedLaw_stationary Q) hW
      (integrable_sq_joint_l2_representative
        ((hw.norm.pow 2).continuousOn.integrableOn_compact
          (μ := (volume : Measure ℝ)) (K := Icc (t / 4) t) isCompact_Icc) hW heW)
  have heqm := local_time_physical_cylinder_integral_congr_on (Q := Q) (J := Icc (t / 4) t)
    hWm hU measurableSet_Icc
    (fun s hs => (heWm s).trans (heU s (by linarith [hs.1])).symm)
    {x | euclideanNorm (x - z) < 16 * ρ}
  have heqd := local_time_physical_cylinder_integral_congr_on (Q := Q) (J := Icc (t / 4) t)
    hWd hU measurableSet_Icc
    (fun s hs => (heWd s).trans (heU s (by linarith [hs.1])).symm)
    {x | euclideanNorm (x - z) < 16 * ρ}
  filter_upwards [hmb z (2 * ρ) h2ρ, hdb hb z (2 * ρ) h2ρ, hgrad,
    hlocal Wm hWm heWm, hlocal Wd hWd heWd, heqm, heqd]
    with ω hm hd hg hlm hld heqm heqd
  have henlarge (W : ℝ × FieldPair d → ℂ)
      (hl : ∀ K, IsCompact K → MemLp
        (fun p : Vec d × ℝ => W (p.2, translate p.1 ω)) 2
          ((volume.restrict K).prod (volume.restrict (Icc (t / 4) t))))
      {k : ℝ} (hk : k < 16 * ρ) :
      (∫ s in Icc (t / 4) t, ∫ x in {x | euclideanNorm (x - z) ≤ k},
        ‖W (s, translate x ω)‖ ^ 2) ≤
      ∫ s in Icc (t / 4) t, ∫ x in {x | euclideanNorm (x - z) < 16 * ρ},
        ‖W (s, translate x ω)‖ ^ 2 := by
    have hi := (memLp_two_iff_integrable_sq_norm
      (hl _ (isCompact_physical_euclidean_closedBall z (16 * ρ))).aestronglyMeasurable).mp
      (hl _ (isCompact_physical_euclidean_closedBall z (16 * ρ)))
    have hiopen := hi.mono_measure (Measure.prod_mono
      (Measure.restrict_mono (fun x (hx : euclideanNorm (x - z) < 16 * ρ) =>
        show euclideanNorm (x - z) ≤ 16 * ρ from hx.le) le_rfl) le_rfl)
    exact local_time_cylinder_integral_mono
      (fun x (hx : euclideanNorm (x - z) ≤ k) => hx.trans_lt hk)
      (Subset.refl _) hiopen (fun _ => sq_nonneg _)
  have hm' := henlarge Wm hlm (k := 2 * (2 * ρ)) (by linarith)
  rw [heqm] at hm'
  have hm := hm.trans (mul_le_mul_of_nonneg_left hm' (by positivity))
  have hd' := henlarge Wd hld (k := 4 * (2 * ρ)) (by linarith)
  rw [heqd] at hd'
  have hd := hd.trans (mul_le_mul_of_nonneg_left hd' (by positivity))
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
  have hg := hg z ρ (2 * ρ) hρpos (by linarith) t ht
  change (L⁻¹ / 4) * _ ≤ _ at hg
  have hbound := hg.trans (add_le_add
    (mul_le_mul hcoeff hm (by positivity) (by positivity))
    (mul_le_mul_of_nonneg_left hd (by positivity : 0 ≤ t / 2)))
  have hq46 : q ^ 4 ≤ q ^ 6 := pow_le_pow_right₀ (by linarith) (by omega)
  have hnonneg : 0 ≤ ∫ s in Icc (t / 4) t,
      ∫ x in {x | euclideanNorm (x - z) < 16 * ρ}, ‖U (s, translate x ω)‖ ^ 2 :=
    integral_nonneg fun _ => integral_nonneg fun _ => sq_nonneg _
  have hcoeff' : (H * q ^ 2 / t) * (Cm * q ^ 2 / t) +
      (t / 2) * (Cd * q ^ 6 / t ^ 3) ≤ (H * Cm + Cd / 2) * q ^ 6 / t ^ 2 := by
    calc
      _ = H * Cm / t ^ 2 * q ^ 4 + (Cd / 2) / t ^ 2 * q ^ 6 := by field_simp
      _ ≤ H * Cm / t ^ 2 * q ^ 6 + (Cd / 2) / t ^ 2 * q ^ 6 := by gcongr
      _ = _ := by ring
  have hfinal := hbound.trans (by
    calc
      _ = ((H * q ^ 2 / t) * (Cm * q ^ 2 / t) +
          (t / 2) * (Cd * q ^ 6 / t ^ 3)) *
          (∫ s in Icc (t / 4) t, ∫ x in {x | euclideanNorm (x - z) < 16 * ρ},
            ‖U (s, translate x ω)‖ ^ 2) := by dsimp [q]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hcoeff' hnonneg)
  have hLinv : 4 * L * (L⁻¹ / 4) = 1 := by field_simp
  have hh := mul_le_mul_of_nonneg_left hfinal (by positivity : 0 ≤ 4 * L)
  rw [← mul_assoc, hLinv, one_mul] at hh
  convert hh using 1; dsimp only [C, q]; ring

/-- Normalize the terminal gradient estimate using the exact Euclidean window
volume and the actual cylinder representative. -/
theorem local_time_corrected_gradient_normalized_cylinder
    (d : ℕ) [Fact (2 ≤ d)] (Λ₀ : ℝ) (hΛ : 1 ≤ Λ₀) :
    ∃ C : ℝ, 0 < C ∧
    ∀ {r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (f : Lp ℂ 2 (reducedLaw Q)) {t a b : ℝ}
    (_ht : 0 < t) (_ha : 0 < a) (_hab : a < b) (_hb : b < t / 4),
    let w := fun s : ℝ => centeredComplexLp Q (P s.toNNReal (centeredComplexLp Q f)) +
      Lp.const 2 (reducedLaw Q) (∫ v in (t / 4)..s, hP.centeringSource f v)
    ∀ U : ℝ × FieldPair d → ℂ, Measurable U →
      (∀ s, 0 < s → (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] w s) →
    ∀ G : Fin d → Lp ℂ 2 (reducedLaw Q),
      HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) (w t) G →
    ∀ z : Vec d, ∀ ρ : ℝ, Real.sqrt t ≤ ρ → ∀ᵐ ω ∂reducedLaw Q,
      (⨍ x in {x | euclideanNorm (x - z) < ρ}, ∑ j, ‖G j (translate x ω)‖ ^ 2) ≤
        (C * (1 + ‖ζ‖ * Real.sqrt t) ^ 6 / t) *
          (⨍ s in Icc (t / 4) t,
            ⨍ x in {x | euclideanNorm (x - z) < 16 * ρ}, ‖U (s, translate x ω)‖ ^ 2) := by
  obtain ⟨C₀, hC₀, hraw⟩ := local_time_corrected_gradient_mass_largeRadius d Λ₀ hΛ
  refine ⟨3 * (16 : ℝ) ^ d * C₀ / 4, by positivity, ?_⟩
  intro r₀ Q i ζ P hP f t a b ht ha hab hb w U hU heU G hG z ρ hρ
  let := reducedLaw_probability Q
  have hρpos : 0 < ρ := (Real.sqrt_pos.mpr ht).trans_le hρ
  have hlocal := ae_all_iff.mpr fun j : Fin d => ae_complex_orbit_memLp_on_all_compacts
    (reducedLaw Q) (reducedLaw_stationary Q) (G j)
  filter_upwards [hraw hP f ht ha hab hb U hU heU G hG z ρ hρ, hlocal]
    with ω hraw hlocal
  have hi := integrable_finsetSum Finset.univ (fun j _ =>
    (memLp_two_iff_integrable_sq_norm
      (hlocal j _ (isCompact_physical_euclidean_closedBall z ρ)).aestronglyMeasurable).mp
        (hlocal j _ (isCompact_physical_euclidean_closedBall z ρ)))
  have hopen : (∫ x in {x | euclideanNorm (x - z) < ρ}, ∑ j, ‖G j (translate x ω)‖ ^ 2) ≤
      ∫ x in {x | euclideanNorm (x - z) ≤ ρ}, ∑ j, ‖G j (translate x ω)‖ ^ 2 :=
    setIntegral_mono_set hi (ae_of_all _ fun _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
      (ae_of_all _ fun x (hx : euclideanNorm (x - z) < ρ) =>
        show euclideanNorm (x - z) ≤ ρ from hx.le)
  have hbound := hopen.trans hraw
  have hv := localSpatialEnergy_window_volume z ρ hρpos
  have hscale := local_time_window_volume_dilation z hρpos (show (0 : ℝ) < 16 by norm_num)
  have havg :
      (⨍ s in Icc (t / 4) t, ⨍ x in {x | euclideanNorm (x - z) < 16 * ρ},
        ‖U (s, translate x ω)‖ ^ 2) =
      (3 * t / 4)⁻¹ *
        ((16 : ℝ) ^ d * volume.real {x | euclideanNorm (x - z) < ρ})⁻¹ *
          (∫ s in Icc (t / 4) t, ∫ x in {x | euclideanNorm (x - z) < 16 * ρ},
            ‖U (s, translate x ω)‖ ^ 2) := by
    simp only [average_eq, measureReal_restrict_apply_univ, smul_eq_mul]
    rw [Real.volume_real_Icc_of_le (by linarith), show t - t / 4 = 3 * t / 4 by ring,
      hscale, integral_const_mul]
    ring
  calc
    _ = (volume.real {x | euclideanNorm (x - z) < ρ})⁻¹ *
        (∫ x in {x | euclideanNorm (x - z) < ρ}, ∑ j, ‖G j (translate x ω)‖ ^ 2) := by
      rw [average_eq, measureReal_restrict_apply_univ, smul_eq_mul]
    _ ≤ (volume.real {x | euclideanNorm (x - z) < ρ})⁻¹ *
        ((C₀ * (1 + ‖ζ‖ * Real.sqrt t) ^ 6 / t ^ 2) *
          (∫ s in Icc (t / 4) t, ∫ x in {x | euclideanNorm (x - z) < 16 * ρ},
            ‖U (s, translate x ω)‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = _ := by
      rw [havg]
      field_simp [ht.ne', hv.ne']

/-- Source cylinder moments control the actual forward gradient; scalar source
primitives leave this gradient unchanged. -/
theorem local_time_forward_gradient_moment_of_source_dependency
    (h0 : node_l_u3A_forced_u2D_local_u23_centered_u2D_sourceStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ p : ℝ, 2 ≤ p → ∃ Cp : ℝ, 0 < Cp ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q) (ζ : ℂ)
    (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P)
    (f : Lp ℂ 2 (reducedLaw Q)),
    MemLp f (ENNReal.ofReal p) (reducedLaw Q) →
    ∀ (t : ℝ≥0) (ht : 0 < (t : ℝ)),
    let u := fun r : ℝ => centeredComplexLp Q (P r.toNNReal (centeredComplexLp Q f))
    ∀ G : Fin d → Lp ℂ 2 (reducedLaw Q),
      HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) (u t) G →
    MemLp (u ((t : ℝ) / 8)) (ENNReal.ofReal p) (reducedLaw Q) ∧
      ∀ (ρ : ℝ) (z : Vec d) (hρ : Real.sqrt (t : ℝ) ≤ ρ),
        MemLp (localSpatialEnergy Q t ρ ((Real.sqrt_pos.mpr ht).trans_le hρ)
          z G 0) (ENNReal.ofReal p) (reducedLaw Q) ∧
        eLpNorm (localSpatialEnergy Q t ρ ((Real.sqrt_pos.mpr ht).trans_le hρ)
          z G 0) (ENNReal.ofReal p) (reducedLaw Q) ≤
          ENNReal.ofReal (Real.sqrt (C₀ * (1 + ‖ζ‖ * Real.sqrt (t : ℝ)) ^ 6 / (t : ℝ))) *
            (ENNReal.ofReal (Cp * (1 + ‖ζ‖ * Real.sqrt (t : ℝ)) *
              Real.exp (Cp * ‖ζ‖ ^ 2 * (t : ℝ))) *
              eLpNorm (u ((t : ℝ) / 8)) (ENNReal.ofReal p) (reducedLaw Q)) := by
  let : Fact (2 ≤ d) := ⟨hd⟩
  obtain ⟨C₀, hC₀, hgrad⟩ :=
    local_time_corrected_gradient_normalized_cylinder d D.ellipticity D.one_le_ellipticity
  obtain ⟨_, _, hsource⟩ := local_time_corrected_cylinder_of_source_dependency h0 d hd D
  refine ⟨C₀, hC₀, ?_⟩
  intro p hp
  obtain ⟨Cp, hCp, hsource⟩ := hsource p hp
  refine ⟨Cp, hCp, ?_⟩
  intro Q hQ ζ P hP f hf t ht u G hG
  obtain ⟨hu8, _, _, U, hU, heU, hUmoment⟩ := hsource Q hQ ζ P hP f hf t ht
  refine ⟨hu8, ?_⟩
  let w := fun r : ℝ => u r +
    Lp.const 2 (reducedLaw Q) (∫ v in ((t : ℝ) / 4)..r, hP.centeringSource f v)
  have hGw : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) (w t) G := by
    intro j
    simpa only [add_zero] using (hG j).add
      (hasComplexHorizontalGradient_const (reducedLaw Q) (reducedLaw_stationary Q)
        (∫ v in ((t : ℝ) / 4)..(t : ℝ), hP.centeringSource f v) j)
  intro ρ z hρ
  have hρpos : 0 < ρ := (Real.sqrt_pos.mpr ht).trans_le hρ
  let N := fun ω : FieldPair d => Real.sqrt
    (⨍ s in Icc ((t : ℝ) / 4) (t : ℝ),
      ⨍ x in {x | euclideanNorm (x - z) < 16 * ρ}, ‖U (s, translate x ω)‖ ^ 2)
  have hNsq : ∀ ω, N ω ^ 2 =
      ⨍ s in Icc ((t : ℝ) / 4) (t : ℝ),
        ⨍ x in {x | euclideanNorm (x - z) < 16 * ρ}, ‖U (s, translate x ω)‖ ^ 2 := by
    intro ω
    exact Real.sq_sqrt (average_nonneg fun _ => average_nonneg fun _ => sq_nonneg _)
  have hN := hUmoment z (16 * ρ) (by positivity)
  have hbound : ∀ᵐ ω ∂reducedLaw Q,
      (⨍ x in {x | euclideanNorm (x - z) < ρ}, ∑ j, ‖G j (translate x ω)‖ ^ 2) ≤
        (C₀ * (1 + ‖ζ‖ * Real.sqrt (t : ℝ)) ^ 6 / (t : ℝ)) * N ω ^ 2 := by
    simpa only [hNsq] using hgrad hP f ht
      (a := (t : ℝ) / 16) (b := (t : ℝ) / 8) (by positivity) (by linarith) (by linarith)
      U hU.measurable heU G hGw z ρ hρ
  obtain ⟨hmem, hnorm⟩ := local_time_zero_derivative_moment_of_sq_bound
    Q t ρ hρpos z G hN.1 (ae_of_all _ fun _ => Real.sqrt_nonneg _) (by positivity) hbound
  exact ⟨hmem, hnorm.trans (mul_le_mul le_rfl hN.2 zero_le zero_le)⟩

private theorem forward_gradient_endpoint_restarts
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
    (ζ : ℂ) (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P)
    (ν : EndpointIndex d) (hν : ν ≠ .inr true) (t : ℝ≥0) :
    indexedEndpoint hd Q ν ζ P Pdag β a μ t =
      centeredComplexLp Q (P t (indexedEndpoint hd Q ν ζ P Pdag β a μ 0)) := by
  cases ν with
  | inl k =>
    simp only [indexedEndpoint, velocityEndpoint, hP.1, ContinuousLinearMap.id_apply,
      hP.centered_apply]
  | inr b =>
    cases b with
    | true => exact False.elim (hν rfl)
    | false =>
      simp only [indexedEndpoint, clockEndpoint, hP.1, ContinuousLinearMap.id_apply]
      rw [map_smul, ← centeredComplexLpCLM_apply Q (ζ • P t (centeredComplexLp Q μ)),
        map_smul, centeredComplexLpCLM_apply, hP.centered_apply]

theorem local_time_forward_gradient_moment_of_deps
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
      IsComplexTransposeSemigroup Q P Pdag → ∀ ν : EndpointIndex d, ν ≠ .inr true →
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
          (eLpNorm (U₈ : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal))
 := by
  intro d hd D p hp
  obtain ⟨C₀, hC₀, hmoment⟩ := local_time_forward_gradient_moment_of_source_dependency h0 d hd D
  obtain ⟨Cp, hCp, hmoment⟩ := hmoment p hp
  let C := max 4 (Real.sqrt C₀ * Cp)
  have hC4 : 4 ≤ C := le_max_left _ _
  have hCA : Real.sqrt C₀ * Cp ≤ C := le_max_right _ _
  refine ⟨C, Cp, by linarith, hCp, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν hν
  obtain ⟨G, V, hGV⟩ := local_time_gradient_endpoint_witnesses hd Q hQ β a μ hβ ha hμ
    ζ P Pdag hP hPdag ν
  refine ⟨G, V, hGV, ?_⟩
  intro t ht U U₈
  let f := indexedEndpoint hd Q ν ζ P Pdag β a μ 0
  have hf := local_time_gradient_endpoint_memLp h1 hd p hp Q hQ β a μ hβ ha hμ
    ζ P Pdag hP hPdag ν 0
  have horbit (r : ℝ) :
      centeredComplexLp Q (P r.toNNReal (centeredComplexLp Q f)) =
        indexedEndpoint hd Q ν ζ P Pdag β a μ r.toNNReal := by
    rw [hP.centered_apply]
    exact (forward_gradient_endpoint_restarts hd Q β a μ ζ P Pdag hP ν hν r.toNNReal).symm
  have hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
      (centeredComplexLp Q (P (t : ℝ).toNNReal (centeredComplexLp Q f))) (G t) := by
    rw [horbit, Real.toNNReal_coe]
    exact (hGV t ht).1
  obtain ⟨hu8, hgm⟩ := hmoment Q hQ ζ P hP f hf t ht (G t) hG
  have ht8 : ((t : ℝ) / 8).toNNReal = t / 8 := by
    apply NNReal.coe_injective
    rw [Real.coe_toNNReal _ (by positivity)]
    simp
  have hu8eq : centeredComplexLp Q (P ((t : ℝ) / 8).toNNReal
      (centeredComplexLp Q f)) = U₈ := by rw [horbit, ht8]
  dsimp only at hu8
  rw [hu8eq] at hu8
  refine ⟨hu8, ?_⟩
  intro ρ x hρ
  obtain ⟨hm, hnorm⟩ := hgm ρ x hρ
  dsimp only at hnorm
  rw [hu8eq, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)] at hnorm
  refine ⟨hm, ?_⟩
  let s := Real.sqrt (t : ℝ)
  let k := 1 + ‖ζ‖ * s
  have hs : 0 < s := Real.sqrt_pos.mpr ht
  have hk : 1 ≤ k := le_add_of_nonneg_right (mul_nonneg (norm_nonneg ζ) hs.le)
  have hroot : Real.sqrt (C₀ * k ^ 6 / (t : ℝ)) = Real.sqrt C₀ * k ^ 3 / s := by
    rw [Real.sqrt_div (by positivity), Real.sqrt_mul hC₀.le,
      show k ^ 6 = (k ^ 3) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  have hpows : k ^ 4 ≤ k ^ C := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hk hC4
  have hinv : (t : ℝ) ^ (-(1 / 2 : ℝ)) = s⁻¹ := by
    rw [Real.rpow_neg ht.le, ← Real.sqrt_eq_rpow]
  have hcoef : Real.sqrt (C₀ * k ^ 6 / (t : ℝ)) *
      (Cp * k * Real.exp (Cp * ‖ζ‖ ^ 2 * (t : ℝ))) ≤
      C * k ^ C * (t : ℝ) ^ (-(1 / 2 : ℝ)) * Real.exp (Cp * ‖ζ‖ ^ 2 * (t : ℝ)) := by
    rw [hroot, hinv]
    calc
      _ = (Real.sqrt C₀ * Cp) * k ^ 4 / s * Real.exp (Cp * ‖ζ‖ ^ 2 * (t : ℝ)) := by ring
      _ ≤ C * k ^ C / s * Real.exp (Cp * ‖ζ‖ ^ 2 * (t : ℝ)) := by gcongr
      _ = _ := by ring
  have hreal := ENNReal.toReal_mono
    (show ENNReal.ofReal _ * eLpNorm (U₈ : FieldPair d → ℂ)
      (ENNReal.ofReal p) (reducedLaw Q) ≠ ∞ from
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top hu8.eLpNorm_ne_top) hnorm
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at hreal
  exact hreal.trans (mul_le_mul_of_nonneg_right hcoef ENNReal.toReal_nonneg)

#print axioms local_time_forward_gradient_moment_of_deps
#print axioms local_time_corrected_gradient_mass_largeRadius
#print axioms local_time_corrected_gradient_normalized_cylinder
#print axioms local_time_forward_gradient_moment_of_source_dependency
#print axioms forward_gradient_endpoint_restarts
end EinsteinFull.Blueprint

#lint


-- Check every declaration generated by this file, including private match
-- auxiliaries, rather than relying only on the exported theorem checks.
run_cmd do
  let env ← Lean.getEnv
  let mut checked : Nat := 0
  for (name, _) in env.constants.toList do
    unless env.isImportedConst name do
      let axioms ← Lean.collectAxioms name
      for ax in axioms do
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
          Lean.logError m!"Unexpected axiom {ax} in {name}"
      checked := checked + 1
  Lean.logInfo m!"Owned/generated transitive axiom audit: {checked} declarations checked"
