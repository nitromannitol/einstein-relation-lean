import EinsteinRelation.Correctors.CenteredBallDilation
import EinsteinRelation.Correctors.SpatialLocalL2Dilation
import EinsteinRelation.Correctors.SpatialBallLocalL2
import EinsteinRelation.Correctors.FrobeniusDilation

/-!
# Physical local L² bounds under positive dilation

Source: `paper/main.tex:722-731`. A radius at most four in physical
coordinates maps inside a normalized radius-four ball when the range
is at least one. The bounds retain the Haar Jacobian and amplitude.
-/
open MeasureTheory
open scoped ENNReal
noncomputable section
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- A nonnegative locally integrable density on normalized balls controls
its physical local integral. All Bochner integrals are genuine under the
stated hypothesis. -/
theorem local_integral_inv_dilation_le_ball_four {d : ℕ}
    (F : Vec d → ℝ) (hF : ∀ x, 0 ≤ F x)
    (hi : ∀ z : Vec d, IntegrableOn F (ball z 4) volume)
    (r c R : ℝ) (hr : 1 ≤ r) (hc : 0 ≤ c) (hR : R ≤ 4) (z : Vec d) :
    (∫ x in ball z R, c * F (r⁻¹ • x) ∂volume) ≤
      c * r ^ d * ∫ x in ball (r⁻¹ • z) 4, F x ∂volume := by
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have hrad : r⁻¹ * R ≤ 4 := by
    calc
      _ ≤ r⁻¹ * 4 := mul_le_mul_of_nonneg_left hR (inv_nonneg.mpr hr0.le)
      _ ≤ 1 * 4 := mul_le_mul_of_nonneg_right (inv_le_one_of_one_le₀ hr) (by norm_num)
      _ = _ := by norm_num
  have hsub : ball (r⁻¹ • z) (r⁻¹ * R) ⊆ ball (r⁻¹ • z) 4 :=
    fun _ hx => lt_of_lt_of_le hx hrad
  rw [integral_const_mul, setIntegral_euclideanBall_inv_smul F r R hr0 z]
  calc
    _ = (c * r ^ d) * ∫ x in ball (r⁻¹ • z) (r⁻¹ * R), F x ∂volume := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (setIntegral_mono_set (hi (r⁻¹ • z))
        (ae_of_all _ fun x => hF x) (Filter.Eventually.of_forall hsub)) (by positivity)

/-- Root-integral moments on normalized radius-four balls transport to
physical balls of radius at most four. The constant is independent of the
physical center. -/
theorem root_integral_local_moment_inv_dilation {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) {d : ℕ}
    (F : Ω → Vec d → ℝ) (hF : ∀ ω x, 0 ≤ F ω x)
    (hi : ∀ᵐ ω ∂P, ∀ z : Vec d, IntegrableOn (F ω) (ball z 4) volume)
    (r c R p : ℝ) (hr : 1 ≤ r) (hc : 0 ≤ c) (hR : R ≤ 4) (hp : 0 ≤ p)
    (B : ℝ≥0∞)
    (hb : ∀ z : Vec d, (∫⁻ ω, ENNReal.ofReal
      ((Real.sqrt (∫ x in ball z 4, F ω x ∂volume)) ^ p) ∂P) ≤ B)
    (z : Vec d) :
    (∫⁻ ω, ENNReal.ofReal ((Real.sqrt
      (∫ x in ball z R, c * F ω (r⁻¹ • x) ∂volume)) ^ p) ∂P) ≤
      ENNReal.ofReal ((Real.sqrt (c * r ^ d)) ^ p) * B := by
  apply le_trans ?_ (mul_le_mul_right (hb (r⁻¹ • z)) _)
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono_ae
  filter_upwards [hi] with ω hω
  have hlocal := local_integral_inv_dilation_le_ball_four
    (F ω) (hF ω) hω r c R hr hc hR z
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (Real.sqrt (c * r ^ d)) ^ p)]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ (Real.sqrt (c * r ^ d *
        ∫ x in ball (r⁻¹ • z) 4, F ω x ∂volume)) ^ p :=
      Real.rpow_le_rpow (Real.sqrt_nonneg _) (Real.sqrt_le_sqrt hlocal) hp
    _ = (Real.sqrt (c * r ^ d)) ^ p *
        (Real.sqrt (∫ x in ball (r⁻¹ • z) 4, F ω x ∂volume)) ^ p := by
      rw [Real.sqrt_mul (by positivity : 0 ≤ c * r ^ d),
        Real.mul_rpow (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)]

/-- Transport the random law and physical coordinates simultaneously.
Joint measurability makes the spatial root-integral a measurable random
variable, so the expectation is taken on the actual transported law. -/
theorem root_integral_local_moment_measurePreserving_inv_dilation
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {P : Measure Ω} {Q : Measure Ξ} {T : Ω → Ξ}
    (hT : MeasurePreserving T P Q) {d : ℕ}
    (F : Ξ → Vec d → ℝ) (hm : Measurable (Function.uncurry F))
    (hF : ∀ ω x, 0 ≤ F ω x)
    (hi : ∀ᵐ ω ∂Q, ∀ z : Vec d, IntegrableOn (F ω) (ball z 4) volume)
    (r c R p : ℝ) (hr : 1 ≤ r) (hc : 0 ≤ c) (hR : R ≤ 4) (hp : 0 ≤ p)
    (B : ℝ≥0∞)
    (hb : ∀ z : Vec d, (∫⁻ ω, ENNReal.ofReal
      ((Real.sqrt (∫ x in ball z 4, F ω x ∂volume)) ^ p) ∂Q) ≤ B)
    (z : Vec d) :
    (∫⁻ ω, ENNReal.ofReal ((Real.sqrt
      (∫ x in ball z R, c * F (T ω) (r⁻¹ • x) ∂volume)) ^ p) ∂P) ≤
      ENNReal.ofReal ((Real.sqrt (c * r ^ d)) ^ p) * B := by
  apply root_integral_local_moment_inv_dilation P
    (fun ω x => F (T ω) x) (fun ω x => hF (T ω) x)
    (hT.quasiMeasurePreserving.ae hi) r c R p hr hc hR hp B ?_ z
  intro z'
  have hmeas : Measurable (fun ω => ENNReal.ofReal
      ((Real.sqrt (∫ x in ball z' 4, F ω x ∂volume)) ^ p)) :=
    (((hm.stronglyMeasurable.integral_prod_right'
      (ν := volume.restrict (ball z' 4))).measurable.sqrt).pow_const p).ennreal_ofReal
  rw [hT.lintegral_comp hmeas]
  exact hb z'

/-- Local L² on origin balls gives genuine L² on every centered
Euclidean ball, with no stationarity assumption. -/
theorem memLp_two_on_centered_euclideanBall {d : ℕ}
    (u : Vec d → ℝ)
    (hu : ∀ R : ℝ, 0 < R → MemLp u 2 (volume.restrict (ball 0 R)))
    (z : Vec d) (R : ℝ) (hR : 0 ≤ R) :
    MemLp u 2 (volume.restrict (ball z R)) := by
  apply (memLp_on_compacts_of_euclidean_balls u hu
    (Metric.closedBall z R) (isCompact_closedBall _ _)).mono_measure
  apply Measure.restrict_mono_set
  intro x hx
  rw [Metric.mem_closedBall, dist_pi_le_iff hR]
  intro j
  rw [Real.dist_eq]
  exact (Regeneration.coordinate_abs_le_euclideanNorm (x - z) j).trans hx.le

/-- The scalar unit-scale L² moment after both the spatial and law
transport. The amplitude can have either sign, and all ball centers share
the same source bound. -/
theorem scalar_local_L2_moment_measurePreserving_inv_dilation
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {P : Measure Ω} {Q : Measure Ξ} {T : Ω → Ξ}
    (hT : MeasurePreserving T P Q) {d : ℕ}
    (u : Ξ → Vec d → ℝ) (hm : Measurable (Function.uncurry u))
    (hu : ∀ᵐ ω ∂Q, ∀ R : ℝ, 0 < R →
      MemLp (u ω) 2 (volume.restrict (ball 0 R)))
    (r c R p : ℝ) (hr : 1 ≤ r) (hR : R ≤ 4) (hp : 0 ≤ p)
    (B : ℝ≥0∞)
    (hb : ∀ z : Vec d, (∫⁻ ω, ENNReal.ofReal
      ((Real.sqrt (∫ x in ball z 4, |u ω x| ^ 2 ∂volume)) ^ p) ∂Q) ≤ B)
    (z : Vec d) :
    (∫⁻ ω, ENNReal.ofReal ((Real.sqrt
      (∫ x in ball z R, |c * u (T ω) (r⁻¹ • x)| ^ 2 ∂volume)) ^ p) ∂P) ≤
      ENNReal.ofReal ((Real.sqrt (c ^ 2 * r ^ d)) ^ p) * B := by
  have hi : ∀ᵐ ω ∂Q, ∀ z : Vec d,
      IntegrableOn (fun x => |u ω x| ^ 2) (ball z 4) volume := by
    filter_upwards [hu] with ω hω
    intro z'
    simpa only [sq_abs] using
      (memLp_two_on_centered_euclideanBall (u ω) hω z' 4 (by norm_num)).integrable_sq
  simpa only [sq_abs, mul_pow] using
    root_integral_local_moment_measurePreserving_inv_dilation hT
      (fun ω x => |u ω x| ^ 2) ((continuous_abs.measurable.comp hm).pow_const 2)
      (fun ω x => sq_nonneg _) hi r (c ^ 2) R p hr (sq_nonneg _) hR hp B hb z

/-- The tensor version retains the Frobenius norm and uses the genuine
entrywise local Sobolev membership of the source flux corrector. -/
theorem flux_local_L2_moment_measurePreserving_inv_dilation
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {P : Measure Ω} {Q : Measure Ξ} {T : Ω → Ξ}
    (hT : MeasurePreserving T P Q) {d : ℕ}
    (S : Ξ → Vec d → Mat d) (hm : Measurable (Function.uncurry S))
    (hu : ∀ᵐ ω ∂Q, ∀ R : ℝ, 0 < R → ∀ j k,
      MemLp (fun x => S ω x j k) 2 (volume.restrict (ball 0 R)))
    (r c R p : ℝ) (hr : 1 ≤ r) (hR : R ≤ 4) (hp : 0 ≤ p)
    (B : ℝ≥0∞)
    (hb : ∀ z : Vec d, (∫⁻ ω, ENNReal.ofReal
      ((Real.sqrt (∫ x in ball z 4, frobeniusNorm (S ω x) ^ 2 ∂volume)) ^ p) ∂Q) ≤ B)
    (z : Vec d) :
    (∫⁻ ω, ENNReal.ofReal ((Real.sqrt
      (∫ x in ball z R, frobeniusNorm (c • S (T ω) (r⁻¹ • x)) ^ 2 ∂volume)) ^ p)
      ∂P) ≤ ENNReal.ofReal ((Real.sqrt (c ^ 2 * r ^ d)) ^ p) * B := by
  let F := fun ω x => frobeniusNorm (S ω x) ^ 2
  have hFm : Measurable (Function.uncurry F) := by
    simp only [F, Function.uncurry_def, frobeniusNorm_sq_eq_sum]
    exact Finset.measurable_sum _ fun j _ => Finset.measurable_sum _ fun k _ =>
      (((continuous_apply k).comp (continuous_apply j)).measurable.comp hm).pow_const 2
  have hi : ∀ᵐ ω ∂Q, ∀ z : Vec d, IntegrableOn (F ω) (ball z 4) volume := by
    filter_upwards [hu] with ω hω
    intro z'
    simp only [F, frobeniusNorm_sq_eq_sum]
    exact integrable_finset_sum _ fun j _ => integrable_finset_sum _ fun k _ =>
      (memLp_two_on_centered_euclideanBall (fun x => S ω x j k)
        (fun R hR => hω R hR j k) z' 4 (by norm_num)).integrable_sq
  simpa only [F, frobeniusNorm_smul, mul_pow, sq_abs] using
    root_integral_local_moment_measurePreserving_inv_dilation hT F hFm
      (fun ω x => sq_nonneg _) hi r (c ^ 2) R p hr (sq_nonneg _) hR hp B hb z

end EinsteinRelation.Correctors
