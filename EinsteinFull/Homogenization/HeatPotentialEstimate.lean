import EinsteinFull.Homogenization.HeatPotentialSmallTime
import EinsteinFull.Homogenization.HighContrastSourceBounds

/-!
# Oscillation of the heat-selected flux potential

Let `F` have a pairing bound at the scales above `R₀` with decay exponent `κ`, amplitude `A`, and
energy growth `∫_{B_R} F² ≤ M R^d` for `R ≥ R₀`. For `r ≥ R₀` split the time window of the
truncated heat gradient `∫_ε^T ∂ᵢΦ_t * F dt` at `λ r²` and `r²` with `λ = (r/R₀)^(-2ϑ)`,
`ϑ = κ/(3 + d/2)`. The small-time part is bounded in `L²(B_r)` by `C √(M λ) r |B_r|^(1/2)`, the
intermediate part pointwise by `C A λ^(-(1+d/4)) r (r/R₀)^(-κ)`, and the large-time part in
oscillation by `C A κ⁻¹ r (r/R₀)^(-κ) |B_r|^(1/2)`; with this choice of `λ` the three bounds are of
the same order `r (r/R₀)^(-ϑ)`. Passing to the limit of the truncations gives the same bound for
the oscillation of the heat-selected flux potential on `B_r`. This is the proof of the flux
corrector estimate (6.13) of Armstrong, Kuusi and Mourrat, *Quantitative Stochastic
Homogenization and Large-Scale Regularity*, from the energy and pairing bounds of the flux.
-/

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace EinsteinFull.Homogenization

open EinsteinRelation EinsteinRelation.Correctors EinsteinRelation.External.AKM

variable {d : ℕ}

section BallNorms

/-- The square-integral norm on the ball `B_r`. -/
noncomputable def l2Ball (r : ℝ) (u : Vec d → ℝ) : ℝ :=
  Real.sqrt (∫ x in ball 0 r, |u x| ^ 2)

/-- The oscillation of `u` on the ball `B_r`, in square integral. -/
noncomputable def oscBall (r : ℝ) (u : Vec d → ℝ) : ℝ :=
  Real.sqrt (∫ x in ball 0 r, |u x - ⨍ y in ball 0 r, u y| ^ 2)

theorem toReal_eLpNorm_two_eq {μ : Measure (Vec d)} {u : Vec d → ℝ} (hu : MemLp u 2 μ) :
    (eLpNorm u 2 μ).toReal = Real.sqrt (∫ x, |u x| ^ 2 ∂μ) := by
  have h := hu.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top
  simp only [ENNReal.toReal_ofNat, Real.norm_eq_abs, Real.rpow_two] at h
  rw [h, ENNReal.toReal_ofReal (Real.rpow_nonneg (integral_nonneg fun x => by positivity) _),
    Real.sqrt_eq_rpow, one_div]

theorem l2Ball_add_le {r : ℝ} {u v : Vec d → ℝ} (hu : MemLp u 2 (volume.restrict (ball 0 r)))
    (hv : MemLp v 2 (volume.restrict (ball 0 r))) :
    l2Ball r (u + v) ≤ l2Ball r u + l2Ball r v := by
  unfold l2Ball
  rw [← toReal_eLpNorm_two_eq (hu.add hv), ← toReal_eLpNorm_two_eq hu,
    ← toReal_eLpNorm_two_eq hv, ← ENNReal.toReal_add hu.eLpNorm_ne_top hv.eLpNorm_ne_top]
  exact ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hu.eLpNorm_ne_top, hv.eLpNorm_ne_top⟩)
    (eLpNorm_add_le (by norm_num))

theorem l2Ball_sub_le {r : ℝ} {u v : Vec d → ℝ} (hu : MemLp u 2 (volume.restrict (ball 0 r)))
    (hv : MemLp v 2 (volume.restrict (ball 0 r))) :
    l2Ball r (u - v) ≤ l2Ball r u + l2Ball r v := by
  unfold l2Ball
  rw [← toReal_eLpNorm_two_eq (hu.sub hv), ← toReal_eLpNorm_two_eq hu,
    ← toReal_eLpNorm_two_eq hv, ← ENNReal.toReal_add hu.eLpNorm_ne_top hv.eLpNorm_ne_top]
  exact ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hu.eLpNorm_ne_top, hv.eLpNorm_ne_top⟩)
    (eLpNorm_sub_le (by norm_num))

theorem setAverage_add_fun {s : Set (Vec d)} {u v : Vec d → ℝ} (hu : IntegrableOn u s volume)
    (hv : IntegrableOn v s volume) :
    ⨍ x in s, (u x + v x) = (⨍ x in s, u x) + ⨍ x in s, v x := by
  rw [setAverage_eq, setAverage_eq, setAverage_eq, integral_add hu hv, smul_add]

theorem setAverage_sub_fun {s : Set (Vec d)} {u v : Vec d → ℝ} (hu : IntegrableOn u s volume)
    (hv : IntegrableOn v s volume) :
    ⨍ x in s, (u x - v x) = (⨍ x in s, u x) - ⨍ x in s, v x := by
  rw [setAverage_eq, setAverage_eq, setAverage_eq, integral_sub hu hv, smul_sub]

theorem oscBall_add_le {r : ℝ} {u v : Vec d → ℝ} (hu : MemLp u 2 (volume.restrict (ball 0 r)))
    (hv : MemLp v 2 (volume.restrict (ball 0 r))) :
    oscBall r (fun x => u x + v x) ≤ oscBall r u + oscBall r v := by
  have hfin := isFiniteMeasure_restrict_ball (d := d) r
  have hu' : MemLp (fun x => u x - ⨍ y in ball 0 r, u y) 2 (volume.restrict (ball 0 r)) :=
    hu.sub (memLp_const _)
  have hv' : MemLp (fun x => v x - ⨍ y in ball 0 r, v y) 2 (volume.restrict (ball 0 r)) :=
    hv.sub (memLp_const _)
  have heq : oscBall r (fun x => u x + v x) = l2Ball r ((fun x => u x - ⨍ y in ball 0 r, u y) +
      (fun x => v x - ⨍ y in ball 0 r, v y)) := by
    unfold oscBall l2Ball
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply]
    rw [setAverage_add_fun (hu.integrable one_le_two) (hv.integrable one_le_two)]
    congr 2
    ring
  rw [heq]
  exact l2Ball_add_le hu' hv'

theorem oscBall_sub_le {r : ℝ} {u v : Vec d → ℝ} (hu : MemLp u 2 (volume.restrict (ball 0 r)))
    (hv : MemLp v 2 (volume.restrict (ball 0 r))) :
    oscBall r (fun x => u x - v x) ≤ oscBall r u + oscBall r v := by
  have hfin := isFiniteMeasure_restrict_ball (d := d) r
  have hu' : MemLp (fun x => u x - ⨍ y in ball 0 r, u y) 2 (volume.restrict (ball 0 r)) :=
    hu.sub (memLp_const _)
  have hv' : MemLp (fun x => v x - ⨍ y in ball 0 r, v y) 2 (volume.restrict (ball 0 r)) :=
    hv.sub (memLp_const _)
  have heq : oscBall r (fun x => u x - v x) = l2Ball r ((fun x => u x - ⨍ y in ball 0 r, u y) -
      (fun x => v x - ⨍ y in ball 0 r, v y)) := by
    unfold oscBall l2Ball
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [Pi.sub_apply]
    rw [setAverage_sub_fun (hu.integrable one_le_two) (hv.integrable one_le_two)]
    congr 2
    ring
  rw [heq]
  exact l2Ball_sub_le hu' hv'

theorem oscBall_sub_const {r : ℝ} (hr : 0 < r) {u : Vec d → ℝ}
    (hu : IntegrableOn u (ball 0 r) volume) (c : ℝ) :
    oscBall r (fun x => u x - c) = oscBall r u := by
  unfold oscBall
  rw [setAverage_sub_const (volume_ball_ne_zero hr) (volume_ball_ne_top hr) hu c]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  ring_nf

theorem oscBall_le_l2Ball {r : ℝ} (hr : 0 < r) {u : Vec d → ℝ}
    (hu : MemLp u 2 (volume.restrict (ball 0 r))) : oscBall r u ≤ l2Ball r u := by
  unfold oscBall l2Ball
  refine Real.sqrt_le_sqrt ?_
  have h := setAverage_sq_sub_setAverage_le (volume_ball_ne_zero hr) (volume_ball_ne_top hr) hu 0
  simp only [sub_zero, setAverage_eq, smul_eq_mul] at h
  have hV : 0 < (volume.real (ball (0 : Vec d) r))⁻¹ :=
    inv_pos.mpr (ENNReal.toReal_pos (volume_ball_ne_zero hr) (volume_ball_ne_top hr))
  simp only [sq_abs, setAverage_eq, smul_eq_mul]
  exact le_of_mul_le_mul_left h hV

theorem l2Ball_le_of_abs_le {r b : ℝ} (hb : 0 ≤ b) {u : Vec d → ℝ}
    (hu : ∀ x ∈ ball (0 : Vec d) r, |u x| ≤ b) :
    l2Ball r u ≤ b * Real.sqrt (volume.real (ball (0 : Vec d) r)) := by
  have hfin := isFiniteMeasure_restrict_ball (d := d) r
  unfold l2Ball
  rw [← Real.sqrt_sq hb, ← Real.sqrt_mul (sq_nonneg b)]
  refine Real.sqrt_le_sqrt ?_
  have h := integral_mono_of_nonneg (μ := volume.restrict (ball (0 : Vec d) r))
    (f := fun x => |u x| ^ 2) (g := fun _ => b ^ 2)
    (Eventually.of_forall fun x => by positivity) (integrable_const _) ?_
  · refine h.trans (le_of_eq ?_)
    rw [integral_const, smul_eq_mul, measureReal_def, measureReal_def,
      Measure.restrict_apply_univ]
    ring
  · filter_upwards [ae_restrict_mem (measurableSet_ball_zero r)] with x hx
    exact pow_le_pow_left₀ (abs_nonneg _) (hu x hx) 2

theorem l2Ball_le_of_lintegral {r Q : ℝ} (hQ : 0 ≤ Q) {u : Vec d → ℝ}
    (hu : MemLp u 2 (volume.restrict (ball 0 r)))
    (h : ∫⁻ x in ball 0 r, ‖u x‖ₑ ^ 2 ≤ ENNReal.ofReal Q) : l2Ball r u ≤ Real.sqrt Q := by
  unfold l2Ball
  refine Real.sqrt_le_sqrt ?_
  have hint := integral_eq_lintegral_of_nonneg_ae (μ := volume.restrict (ball (0 : Vec d) r))
    (f := fun x => |u x| ^ 2) (Eventually.of_forall fun x => by positivity)
    ((continuous_pow 2).comp_aestronglyMeasurable hu.aestronglyMeasurable.norm)
  rw [hint]
  have hl : ∫⁻ x in ball 0 r, ENNReal.ofReal (|u x| ^ 2) = ∫⁻ x in ball 0 r, ‖u x‖ₑ ^ 2 :=
    lintegral_congr fun x => by
      rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_pow (abs_nonneg _)]
  rw [hl]
  calc (∫⁻ x in ball 0 r, ‖u x‖ₑ ^ 2).toReal ≤ (ENNReal.ofReal Q).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top h
    _ = Q := ENNReal.toReal_ofReal hQ

end BallNorms

section Window

/-- The decay exponent `κ/(3 + d/2)` of the flux potential estimate. -/
noncomputable def fluxDecayExponent (d : ℕ) (κ : ℝ) : ℝ := κ / (3 + (d : ℝ) / 2)

theorem fluxDecayExponent_pos {κ : ℝ} (hκ : 0 < κ) : 0 < fluxDecayExponent d κ := by
  unfold fluxDecayExponent
  positivity

theorem fluxDecayExponent_le {κ : ℝ} (hκ : 0 ≤ κ) : fluxDecayExponent d κ ≤ κ := by
  unfold fluxDecayExponent
  rw [div_le_iff₀ (by positivity)]
  have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  nlinarith

theorem fluxDecayExponent_identity {κ : ℝ} :
    2 * fluxDecayExponent d κ * (1 + (d : ℝ) / 4) - κ = -fluxDecayExponent d κ := by
  unfold fluxDecayExponent
  have : (0 : ℝ) < 3 + (d : ℝ) / 2 := by positivity
  field_simp
  ring

/-- **Oscillation of the truncated heat potential.** If `F` has a pairing bound at the scales
above `R₀` with exponent `κ` and amplitude `A`, and `∫_{B_R} F² ≤ M R^d` for `R ≥ R₀`, then for
`r ≥ R₀`, `ε ≤ (r/R₀)^(-2ϑ) r²` and `T ≥ r²` the truncation `∫_ε^T ∂ᵢΦ_t * F dt` oscillates on
`B_r` by at most `C (√M + A + A/κ) r (r/R₀)^(-ϑ) |B_r|^(1/2)`, `ϑ = κ/(3 + d/2)`. -/
theorem exists_osc_heatGradWindow_le (d : ℕ) (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {F : Vec d → ℝ} {R₀ A κ M : ℝ}, HasScalePairingBound F R₀ A κ →
      0 < R₀ → 0 ≤ A → 0 < κ → 0 ≤ M → Measurable F → HasGaussianMoments F →
      (∀ R : ℝ, R₀ ≤ R → ∫⁻ y in ball 0 R, ‖F y‖ₑ ^ 2 ≤ ENNReal.ofReal (M * R ^ d)) →
      ∀ (i : Fin d) {r ε T : ℝ}, R₀ ≤ r → 0 < ε →
        ε ≤ (r / R₀) ^ (-(2 * fluxDecayExponent d κ)) * r ^ 2 → r ^ 2 ≤ T →
        oscBall r (heatGradWindow ε T i F) ≤
          C * (Real.sqrt M + A + A / κ) * r * (r / R₀) ^ (-fluxDecayExponent d κ) *
            Real.sqrt (volume.real (ball (0 : Vec d) r)) := by
  obtain ⟨Cl, hCl, hlarge⟩ := exists_osc_heatGradWindow_large_le d hd
  obtain ⟨Cm, hCm, hmid⟩ := exists_abs_heatGradWindow_mid_le d
  have hV₁0 : 0 < volume.real (ball (0 : Vec d) 1) :=
    ENNReal.toReal_pos (volume_ball_ne_zero one_pos) (volume_ball_ne_top one_pos)
  have hsTC := smallTimeConst_nonneg d
  refine ⟨Real.sqrt (smallTimeConst d / volume.real (ball (0 : Vec d) 1)) + Cm + Cl,
    by positivity, ?_⟩
  intro F R₀ A κ M hF hR₀ hA hκ hM hFm hmom hgrowth i r ε T hr hε hεl hrT
  have hr0 : 0 < r := lt_of_lt_of_le hR₀ hr
  have hθ0 : 0 < fluxDecayExponent d κ := fluxDecayExponent_pos hκ
  have hρ1 : 1 ≤ r / R₀ := by rw [le_div_iff₀ hR₀]; linarith
  have hρ0 : 0 < r / R₀ := by linarith
  have hlam0 : 0 < (r / R₀) ^ (-(2 * fluxDecayExponent d κ)) := Real.rpow_pos_of_pos hρ0 _
  have hlam1 : (r / R₀) ^ (-(2 * fluxDecayExponent d κ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hρ1 (by linarith)
  set lam := (r / R₀) ^ (-(2 * fluxDecayExponent d κ)) with hlam
  have hl1 : lam * r ^ 2 ≤ r ^ 2 := mul_le_of_le_one_left (sq_nonneg r) hlam1
  have hlr0 : 0 < lam * r ^ 2 := by positivity
  have hsplit : heatGradWindow ε T i F = heatGradWindow ε (lam * r ^ 2) i F +
      heatGradWindow (lam * r ^ 2) (r ^ 2) i F + heatGradWindow (r ^ 2) T i F := by
    funext x
    simp only [Pi.add_apply]
    rw [hmom.heatGradWindow_add hFm hε hεl hl1 i x,
      hmom.heatGradWindow_add hFm hε (hεl.trans hl1) hrT i x]
  have hmS := hmom.memLp_heatGradWindow hε hεl i hFm r
  have hmM := hmom.memLp_heatGradWindow hlr0 hl1 i hFm r
  have hmL := hmom.memLp_heatGradWindow (by positivity) hrT i hFm r
  have hosc : oscBall r (heatGradWindow ε T i F) ≤ l2Ball r (heatGradWindow ε (lam * r ^ 2) i F) +
      l2Ball r (heatGradWindow (lam * r ^ 2) (r ^ 2) i F) +
      oscBall r (heatGradWindow (r ^ 2) T i F) := by
    rw [hsplit]
    calc oscBall r (heatGradWindow ε (lam * r ^ 2) i F +
          heatGradWindow (lam * r ^ 2) (r ^ 2) i F + heatGradWindow (r ^ 2) T i F)
        ≤ oscBall r (heatGradWindow ε (lam * r ^ 2) i F +
            heatGradWindow (lam * r ^ 2) (r ^ 2) i F) +
          oscBall r (heatGradWindow (r ^ 2) T i F) := oscBall_add_le (hmS.add hmM) hmL
      _ ≤ oscBall r (heatGradWindow ε (lam * r ^ 2) i F) +
            oscBall r (heatGradWindow (lam * r ^ 2) (r ^ 2) i F) +
          oscBall r (heatGradWindow (r ^ 2) T i F) := by
          gcongr
          exact oscBall_add_le hmS hmM
      _ ≤ _ := by
          gcongr
          · exact oscBall_le_l2Ball hr0 hmS
          · exact oscBall_le_l2Ball hr0 hmM
  have hVr : volume.real (ball (0 : Vec d) r) = r ^ d * volume.real (ball (0 : Vec d) 1) := by
    rw [volume_real_ball hr0, volume_real_ball one_pos, one_pow, one_mul]
  have hV₁ne : volume.real (ball (0 : Vec d) 1) ≠ 0 := hV₁0.ne'
  have hS0 : 0 ≤ Real.sqrt (volume.real (ball (0 : Vec d) r)) := Real.sqrt_nonneg _
  have hρθ : 0 ≤ (r / R₀) ^ (-fluxDecayExponent d κ) := Real.rpow_nonneg hρ0.le _
  -- the small-time term
  have h1 : l2Ball r (heatGradWindow ε (lam * r ^ 2) i F) ≤
      Real.sqrt (smallTimeConst d / volume.real (ball (0 : Vec d) 1)) * Real.sqrt M * r *
        (r / R₀) ^ (-fluxDecayExponent d κ) * Real.sqrt (volume.real (ball (0 : Vec d) r)) := by
    refine (l2Ball_le_of_lintegral (by positivity) hmS
      (lintegral_heatGradWindow_sq_le hFm hM hR₀ hgrowth i hr hε hεl hl1)).trans (le_of_eq ?_)
    have key : smallTimeConst d * M * (lam * r ^ 2) * r ^ d =
        (Real.sqrt (smallTimeConst d / volume.real (ball (0 : Vec d) 1)) * Real.sqrt M * r *
          (r / R₀) ^ (-fluxDecayExponent d κ) *
            Real.sqrt (volume.real (ball (0 : Vec d) r))) ^ 2 := by
      rw [mul_pow, mul_pow, mul_pow, mul_pow, Real.sq_sqrt (div_nonneg hsTC hV₁0.le),
        Real.sq_sqrt hM, Real.sq_sqrt measureReal_nonneg, hVr,
        ← Real.rpow_natCast ((r / R₀) ^ (-fluxDecayExponent d κ)) 2, ← Real.rpow_mul hρ0.le,
        hlam, show -fluxDecayExponent d κ * ((2 : ℕ) : ℝ) = -(2 * fluxDecayExponent d κ) by
          push_cast; ring]
      field_simp
    rw [key, Real.sqrt_sq (by positivity)]
  -- the intermediate-time term
  have h2 : l2Ball r (heatGradWindow (lam * r ^ 2) (r ^ 2) i F) ≤
      Cm * A * r * (r / R₀) ^ (-fluxDecayExponent d κ) *
        Real.sqrt (volume.real (ball (0 : Vec d) r)) := by
    have hb := l2Ball_le_of_abs_le (r := r) (u := heatGradWindow (lam * r ^ 2) (r ^ 2) i F)
      (b := Cm * A * lam ^ (-(1 + (d : ℝ) / 4)) * r * (r / R₀) ^ (-κ)) (by positivity)
      (fun x hx => hmid hF hR₀ hA hκ.le hFm hmom i hr hlam0 hlam1 x (by
        have hx' : euclideanNorm (x - 0) < r := hx
        rw [sub_zero] at hx'
        exact hx'.le))
    refine hb.trans (le_of_eq ?_)
    have hexp : lam ^ (-(1 + (d : ℝ) / 4)) * (r / R₀) ^ (-κ) =
        (r / R₀) ^ (-fluxDecayExponent d κ) := by
      rw [hlam, ← Real.rpow_mul hρ0.le, ← Real.rpow_add hρ0]
      congr 1
      rw [← fluxDecayExponent_identity (d := d) (κ := κ)]
      ring
    calc Cm * A * lam ^ (-(1 + (d : ℝ) / 4)) * r * (r / R₀) ^ (-κ) *
          Real.sqrt (volume.real (ball (0 : Vec d) r))
        = Cm * A * r * (lam ^ (-(1 + (d : ℝ) / 4)) * (r / R₀) ^ (-κ)) *
          Real.sqrt (volume.real (ball (0 : Vec d) r)) := by ring
      _ = _ := by rw [hexp]
  -- the large-time term
  have h3 : oscBall r (heatGradWindow (r ^ 2) T i F) ≤
      Cl * (A / κ) * r * (r / R₀) ^ (-fluxDecayExponent d κ) *
        Real.sqrt (volume.real (ball (0 : Vec d) r)) := by
    refine (hlarge hF hR₀ hA hκ hFm hmom i hr le_rfl hrT).trans ?_
    have hR : R₀ ^ κ * r ^ (1 - κ) = r * (r / R₀) ^ (-κ) := by
      rw [Real.rpow_sub hr0, Real.rpow_one, Real.rpow_neg hρ0.le,
        Real.div_rpow hr0.le hR₀.le, inv_div]
      ring
    have hmono : (r / R₀) ^ (-κ) ≤ (r / R₀) ^ (-fluxDecayExponent d κ) :=
      Real.rpow_le_rpow_of_exponent_le hρ1 (neg_le_neg (fluxDecayExponent_le hκ.le))
    calc Cl / κ * A * R₀ ^ κ * r ^ (1 - κ) * Real.sqrt (volume.real (ball (0 : Vec d) r))
        = Cl * (A / κ) * (R₀ ^ κ * r ^ (1 - κ)) *
          Real.sqrt (volume.real (ball (0 : Vec d) r)) := by ring
      _ = Cl * (A / κ) * r * (r / R₀) ^ (-κ) *
          Real.sqrt (volume.real (ball (0 : Vec d) r)) := by rw [hR]; ring
      _ ≤ _ := by gcongr
  have hX : 0 ≤ r * (r / R₀) ^ (-fluxDecayExponent d κ) *
      Real.sqrt (volume.real (ball (0 : Vec d) r)) := by positivity
  have hsq := Real.sqrt_nonneg (smallTimeConst d / volume.real (ball (0 : Vec d) 1))
  have hsM := Real.sqrt_nonneg M
  have hAκ : 0 ≤ A / κ := div_nonneg hA hκ.le
  have hcoef : Real.sqrt (smallTimeConst d / volume.real (ball (0 : Vec d) 1)) * Real.sqrt M +
      Cm * A + Cl * (A / κ) ≤
      (Real.sqrt (smallTimeConst d / volume.real (ball (0 : Vec d) 1)) + Cm + Cl) *
        (Real.sqrt M + A + A / κ) := by
    nlinarith [mul_nonneg hsq hA, mul_nonneg hsq hAκ, mul_nonneg hCm hsM, mul_nonneg hCm hAκ,
      mul_nonneg hCl hsM, mul_nonneg hCl hA]
  calc oscBall r (heatGradWindow ε T i F)
      ≤ (Real.sqrt (smallTimeConst d / volume.real (ball (0 : Vec d) 1)) * Real.sqrt M +
          Cm * A + Cl * (A / κ)) * (r * (r / R₀) ^ (-fluxDecayExponent d κ) *
            Real.sqrt (volume.real (ball (0 : Vec d) r))) := by
        nlinarith
    _ ≤ (Real.sqrt (smallTimeConst d / volume.real (ball (0 : Vec d) 1)) + Cm + Cl) *
          (Real.sqrt M + A + A / κ) * (r * (r / R₀) ^ (-fluxDecayExponent d κ) *
            Real.sqrt (volume.real (ball (0 : Vec d) r))) :=
        mul_le_mul_of_nonneg_right hcoef hX
    _ = _ := by ring

end Window

section Potential

/-- **Oscillation of the heat-selected flux potential.** Let `g` satisfy the hypotheses of the heat
formula (6.7), and let `c` be a vector such that every component of `g - c` has Gaussian moments,
a pairing bound at the scales above `R₀` with exponent `κ` and amplitude `A`, and energy growth
`∫_{B_R} |g_k - c_k|² ≤ M R^d` for `R ≥ R₀`. Then every entry of the heat-selected flux potential
oscillates on `B_r`, `r ≥ R₀`, by at most `C (√M + A + A/κ) r (r/R₀)^(-ϑ) |B_r|^(1/2)`,
`ϑ = κ/(3 + d/2)`. -/
theorem exists_osc_heatSelectedPotential_le (d : ℕ) (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {g : Vec d → Vec d}, HeatFormulaHypotheses g → ∀ (c : Vec d)
      {R₀ A κ M : ℝ}, 0 < R₀ → 0 ≤ A → 0 < κ → 0 ≤ M →
      (∀ k, HasGaussianMoments (fun y => g y k - c k)) →
      (∀ k, HasScalePairingBound (fun y => g y k - c k) R₀ A κ) →
      (∀ k (R : ℝ), R₀ ≤ R →
        ∫⁻ y in ball 0 R, ‖g y k - c k‖ₑ ^ 2 ≤ ENNReal.ofReal (M * R ^ d)) →
      ∀ (j k : Fin d) {r : ℝ}, R₀ ≤ r →
        oscBall r (fun x => heatSelectedPotential g x j k) ≤
          C * (Real.sqrt M + A + A / κ) * r * (r / R₀) ^ (-fluxDecayExponent d κ) *
            Real.sqrt (volume.real (ball (0 : Vec d) r)) := by
  obtain ⟨Cw, hCw, hW⟩ := exists_osc_heatGradWindow_le d hd
  refine ⟨2 * Cw, by positivity, ?_⟩
  intro g hg c R₀ A κ M hR₀ hA hκ hM hmom hpair hgrowth j k r hr
  have hr0 : 0 < r := lt_of_lt_of_le hR₀ hr
  have hfin := isFiniteMeasure_restrict_ball (d := d) r
  set B := Cw * (Real.sqrt M + A + A / κ) * r * (r / R₀) ^ (-fluxDecayExponent d κ) *
    Real.sqrt (volume.real (ball (0 : Vec d) r)) with hB
  have hFm : ∀ k, Measurable (fun y => g y k - c k) := fun k => (hg.measurable k).sub_const _
  have hshift : ∀ (ε T : ℝ), 0 < ε → ∀ i l : Fin d,
      heatGradWindow ε T i (fun y => g y l) = heatGradWindow ε T i (fun y => g y l - c l) := by
    intro ε T hε i l
    funext x
    have h := (hmom l).heatGradWindow_add_const (hFm l) (ε₂ := T) hε i (c l) x
    simp only [sub_add_cancel] at h
    exact h
  have hlam : 0 < (r / R₀) ^ (-(2 * fluxDecayExponent d κ)) * r ^ 2 := by
    have : 0 < r / R₀ := div_pos hr0 hR₀
    positivity
  obtain ⟨N₁, hN₁⟩ := exists_nat_ge ((r / R₀) ^ (-(2 * fluxDecayExponent d κ)) * r ^ 2)⁻¹
  obtain ⟨N₂, hN₂⟩ := exists_nat_ge (r ^ 2)
  have hev : ∀ᶠ p : ℕ in atTop, oscBall r (centeredHeatPotential g p j k) ≤ 2 * B := by
    filter_upwards [eventually_ge_atTop (max N₁ N₂)] with p hp
    have hpN₁ : (N₁ : ℝ) ≤ ((p + 1 : ℕ) : ℝ) := by
      have := le_trans (le_max_left N₁ N₂) hp
      exact_mod_cast this.trans (Nat.le_succ p)
    have hpN₂ : (N₂ : ℝ) ≤ ((p + 1 : ℕ) : ℝ) := by
      have := le_trans (le_max_right N₁ N₂) hp
      exact_mod_cast this.trans (Nat.le_succ p)
    have hp1 : ((p + 1 : ℕ) : ℝ)⁻¹ ≤ (r / R₀) ^ (-(2 * fluxDecayExponent d κ)) * r ^ 2 :=
      inv_le_of_inv_le₀ hlam (hN₁.trans hpN₁)
    have hp2 : r ^ 2 ≤ ((p + 1 : ℕ) : ℝ) := hN₂.trans hpN₂
    have hε := natCast_succ_inv_pos p
    have htr : IntegrableOn (heatPotentialTruncation g p j k) (ball 0 r) volume :=
      (hg.memLp_heatPotentialTruncation p j k r).integrable one_le_two
    have e1 : oscBall r (centeredHeatPotential g p j k) =
        oscBall r (heatPotentialTruncation g p j k) :=
      oscBall_sub_const hr0 htr _
    rw [e1]
    have e2 : heatPotentialTruncation g p j k = fun x =>
        heatGradWindow ((p + 1 : ℕ) : ℝ)⁻¹ ((p + 1 : ℕ) : ℝ) j (fun y => g y k - c k) x -
          heatGradWindow ((p + 1 : ℕ) : ℝ)⁻¹ ((p + 1 : ℕ) : ℝ) k (fun y => g y j - c j) x := by
      funext x
      unfold heatPotentialTruncation
      rw [hshift _ _ hε j k, hshift _ _ hε k j]
    rw [e2]
    have hm1 := (hmom k).memLp_heatGradWindow hε (natCast_succ_inv_le_natCast_succ p p) j (hFm k) r
    have hm2 := (hmom j).memLp_heatGradWindow hε (natCast_succ_inv_le_natCast_succ p p) k (hFm j) r
    calc oscBall r (fun x =>
          heatGradWindow ((p + 1 : ℕ) : ℝ)⁻¹ ((p + 1 : ℕ) : ℝ) j (fun y => g y k - c k) x -
            heatGradWindow ((p + 1 : ℕ) : ℝ)⁻¹ ((p + 1 : ℕ) : ℝ) k (fun y => g y j - c j) x)
        ≤ oscBall r (heatGradWindow ((p + 1 : ℕ) : ℝ)⁻¹ ((p + 1 : ℕ) : ℝ) j
              (fun y => g y k - c k)) +
            oscBall r (heatGradWindow ((p + 1 : ℕ) : ℝ)⁻¹ ((p + 1 : ℕ) : ℝ) k
              (fun y => g y j - c j)) := oscBall_sub_le hm1 hm2
      _ ≤ B + B := add_le_add
          (hW (hpair k) hR₀ hA hκ hM (hFm k) (hmom k) (hgrowth k) j hr hε hp1 hp2)
          (hW (hpair j) hR₀ hA hκ hM (hFm j) (hmom j) (hgrowth j) k hr hε hp1 hp2)
      _ = 2 * B := by ring
  have hU := hg.memLp_heatSelectedPotential hd j k r
  have hbound : ∀ p : ℕ, oscBall r (fun x => heatSelectedPotential g x j k) ≤
      oscBall r (centeredHeatPotential g p j k) +
        (eLpNorm (fun x => centeredHeatPotential g p j k x - heatSelectedPotential g x j k) 2
          (volume.restrict (ball 0 r))).toReal := by
    intro p
    have hup := hg.memLp_centeredHeatPotential p j k r
    have hdiff : MemLp (fun x => centeredHeatPotential g p j k x - heatSelectedPotential g x j k)
        2 (volume.restrict (ball 0 r)) := hup.sub hU
    have hfun : (fun x => heatSelectedPotential g x j k) = fun x =>
        centeredHeatPotential g p j k x -
          (centeredHeatPotential g p j k x - heatSelectedPotential g x j k) := by
      funext x
      ring
    rw [hfun]
    refine (oscBall_sub_le hup hdiff).trans (add_le_add le_rfl ?_)
    refine (oscBall_le_l2Ball hr0 hdiff).trans (le_of_eq ?_)
    unfold l2Ball
    rw [toReal_eLpNorm_two_eq hdiff]
  have htend : Tendsto (fun p : ℕ => 2 * B +
      (eLpNorm (fun x => centeredHeatPotential g p j k x - heatSelectedPotential g x j k) 2
        (volume.restrict (ball 0 r))).toReal) atTop (𝓝 (2 * B)) := by
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
      (hg.tendsto_eLpNorm_centeredHeatPotential hd j k r)
    have h2 := tendsto_const_nhds (x := 2 * B) |>.add h
    simpa using h2
  have hfinal : oscBall r (fun x => heatSelectedPotential g x j k) ≤ 2 * B := by
    refine ge_of_tendsto htend ?_
    filter_upwards [hev] with p hp
    exact (hbound p).trans (add_le_add hp le_rfl)
  calc oscBall r (fun x => heatSelectedPotential g x j k) ≤ 2 * B := hfinal
    _ = _ := by rw [hB]; ring

end Potential

end EinsteinFull.Homogenization
