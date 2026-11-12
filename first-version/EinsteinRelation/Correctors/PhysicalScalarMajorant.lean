import EinsteinRelation.Correctors.PhysicalCenteredLocalL2
import EinsteinRelation.Correctors.SpatialBallLocalL2Support
open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM
/-- Source: `paper/main.tex:718-723`. A measurable majorant for a raw
local root-integral gives a physical majorant, without potential measurability. -/
theorem physical_scalar_L2_majorant_of_raw_majorant
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {P : Measure Ω} {Q : Measure Ξ} {T : Ω → Ξ}
    (hT : MeasurePreserving T P Q) {d : ℕ}
    (u : Ξ → Vec d → ℝ) (b : Ξ → ℝ)
    (hu : ∀ᵐ a ∂Q, ∀ R : ℝ, 0 < R → MemLp (u a) 2 (volume.restrict (ball 0 R)))
    (r c p : ℝ) (hr : 1 ≤ r) (hp : 0 ≤ p) (z : Vec d)
    (M : Ξ → ℝ) (hM : AEMeasurable M Q) (hM0 : ∀ a, 0 ≤ M a)
    (hMb : ∀ᵐ a ∂Q, Real.sqrt (∫ x in ball (r⁻¹ • z) 4,
      |u a x - b a| ^ 2 ∂volume) ≤ M a)
    (B : ℝ) (hb : (∫⁻ a, ENNReal.ofReal (M a ^ p) ∂Q) ≤ ENNReal.ofReal B) :
    ∃ N : Ω → ℝ, AEMeasurable N P ∧ (∀ ω, 0 ≤ N ω) ∧
      (∀ᵐ ω ∂P, Real.sqrt (∫ x in ball z 4,
        |c * u (T ω) (r⁻¹ • x) - c * b (T ω)| ^ 2 ∂volume) ≤ N ω) ∧
      (∫⁻ ω, ENNReal.ofReal (N ω ^ p) ∂P) ≤
        ENNReal.ofReal ((Real.sqrt (c ^ 2 * r ^ d)) ^ p * max B 0) := by
  let A := Real.sqrt (c ^ 2 * r ^ d)
  have hA : 0 ≤ A := Real.sqrt_nonneg _
  let N := fun ω => A * M (T ω)
  have hNm : AEMeasurable N P :=
    aemeasurable_const.mul (hM.comp_quasiMeasurePreserving hT.quasiMeasurePreserving)
  have hN0 : ∀ ω, 0 ≤ N ω := fun ω => mul_nonneg hA (hM0 (T ω))
  refine ⟨N, hNm, hN0, ?_, ?_⟩
  · filter_upwards [hT.quasiMeasurePreserving.ae hu,
      hT.quasiMeasurePreserving.ae hMb] with ω hl hbnd
    let F := fun x => |u (T ω) x - b (T ω)| ^ 2
    have hi (w : Vec d) : IntegrableOn F (ball w 4) volume := by
      letI := isFiniteMeasure_restrict_euclideanBall w 4 (by norm_num)
      have hlocal := memLp_on_euclideanBall_of_origin_balls (u (T ω)) hl w 4 (by norm_num)
      simpa only [F, sq_abs] using (hlocal.sub (memLp_const (b (T ω)))).integrable_sq
    have h := local_integral_inv_dilation_le_ball_four F (fun _ => sq_nonneg _)
      hi r (c ^ 2) 4 hr (sq_nonneg _) le_rfl z
    have hpoint : (∫ x in ball z 4, |c * u (T ω) (r⁻¹ • x) - c * b (T ω)| ^ 2
        ∂volume) ≤ (c ^ 2 * r ^ d) * ∫ x in ball (r⁻¹ • z) 4, F x ∂volume := by
      simpa only [F, ← mul_sub, abs_mul, mul_pow, sq_abs] using h
    calc
      _ ≤ Real.sqrt ((c ^ 2 * r ^ d) * ∫ x in ball (r⁻¹ • z) 4, F x ∂volume) :=
        Real.sqrt_le_sqrt hpoint
      _ = A * Real.sqrt (∫ x in ball (r⁻¹ • z) 4, F x ∂volume) := by
        rw [Real.sqrt_mul (by positivity : 0 ≤ c ^ 2 * r ^ d)]
      _ ≤ N ω := mul_le_mul_of_nonneg_left hbnd hA
  · have hm : AEMeasurable (fun a => ENNReal.ofReal (M a ^ p)) Q :=
      (hM.pow_const p).ennreal_ofReal
    have heq : (∫⁻ ω, ENNReal.ofReal (M (T ω) ^ p) ∂P) =
        ∫⁻ a, ENNReal.ofReal (M a ^ p) ∂Q := by
      rw [← hT.map_eq] at hm ⊢
      exact (lintegral_map' hm hT.measurable.aemeasurable).symm
    simp_rw [N, Real.mul_rpow hA (hM0 _),
      ENNReal.ofReal_mul (Real.rpow_nonneg hA p)]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, heq]
    apply (mul_le_mul_right hb _).trans
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hA p)]
    exact ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_left (le_max_left _ _) (Real.rpow_nonneg hA p))
end EinsteinRelation.Correctors
