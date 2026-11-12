import EinsteinRelation.Correctors.SemigroupZeroPotential
import EinsteinRelation.Correctors.SemigroupGradientTailSlices

/-! # Euclidean initial energy of the actual column gradient

Source: `paper/main.tex:800–808`. The local energy class through time zero
also holds on normalized spatial volume and in the Euclidean carrier used
by the stationary variational corrector.
-/

open MeasureTheory Set
open scoped ENNReal
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- Initial energy on normalized ball volume, in the actual Euclidean
carrier. Source: `paper/main.tex:800–808`. -/
theorem semigroup_initial_euclidean_energy
    {d : ℕ} {K : ℝ} (hK : 0 < K)
    {A : Coefficient d K} {g : Vec d → Vec d}
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hsol : IsSemigroupSolution A g u G) (hG : Measurable G)
    {B : ℝ} (hb : ∀ t, 0 < t → ∀ x, |u (t,x)| ≤ B)
    {T R : ℝ} (hT : 0 < T) (hR : 0 < R) :
    MemLp (fun z => (WithLp.toLp 2 (G z) : EuclideanSpace ℝ (Fin d))) 2
      ((volume.restrict (Ioo 0 T)).prod
        ((volume (originBall d R))⁻¹ • volume.restrict (originBall d R))) := by
  let J := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm
  have hn := (semigroup_initial_strip_memLp hK hsol hb hT hR).2
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at hn
  have hj : MemLp (fun z => J (G z)) 2
      ((volume.restrict (Ioo 0 T)).prod (volume.restrict (originBall d R))) := by
    apply hn.mono' (J.continuous.measurable.comp hG).aestronglyMeasurable
    exact ae_of_all _ fun z => by
      change ‖WithLp.toLp 2 (G z)‖ ≤ euclideanNorm (G z)
      rw [TimeChange.euclideanNorm_eq_norm_toLp]
  have hv : volume (originBall d R) ≠ 0 :=
    (ENNReal.toReal_pos_iff.mp (by
      simpa only [originBall,ball,sub_zero] using ball_volume_pos_finite d R hR)).1.ne'
  rw [Measure.prod_smul_right]
  exact hj.smul_measure (ENNReal.inv_ne_top.mpr hv)

/-- Every literal Euclidean initial integral has the coordinate values of
the original gradient, almost everywhere in space. One initial energy
class justifies every smaller upper endpoint simultaneously.
Source: `paper/main.tex:800–808`. -/
theorem initial_euclidean_integral_coordinates
    {X : Type*} [MeasurableSpace X] {d : ℕ}
    (ν : Measure X) [IsProbabilityMeasure ν]
    {G : ℝ × X → Vec d} {S : ℝ}
    (hG : MemLp (fun z => (WithLp.toLp 2 (G z) : EuclideanSpace ℝ (Fin d))) 2
      ((volume.restrict (Ioo 0 S)).prod ν)) :
    ∀ᵐ x ∂ν, ∀ T : ℝ, T ≤ S →
      (∫ t in Ioo 0 T, (WithLp.toLp 2 (G (t,x)) : EuclideanSpace ℝ (Fin d))).ofLp =
        fun j => ∫ t in Ioo 0 T, G (t,x) j := by
  filter_upwards [(hG.integrable (by norm_num)).prod_left_ae] with x hx
  intro T hTS
  have hi : IntegrableOn (fun t => (WithLp.toLp 2 (G (t,x)) :
      EuclideanSpace ℝ (Fin d))) (Ioo 0 T) :=
    IntegrableOn.mono_set hx (Ioo_subset_Ioo le_rfl hTS)
  funext j
  exact eval_integral_piLp (fun j => hi.eval_piLp j) j

/-- The coordinate identities hold on full spatial volume by exhaustion
with normalized balls. Source: `paper/main.tex:800–808`. -/
theorem semigroup_initial_euclidean_coordinates
    {d : ℕ} {K : ℝ} (hK : 0 < K)
    {A : Coefficient d K} {g : Vec d → Vec d}
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hsol : IsSemigroupSolution A g u G) (hG : Measurable G)
    {B : ℝ} (hb : ∀ t, 0 < t → ∀ x, |u (t,x)| ≤ B)
    {S : ℝ} (hS : 0 < S) :
    ∀ᵐ x ∂(volume : Measure (Vec d)), ∀ T : ℝ, T ≤ S →
      (∫ t in Ioo 0 T, (WithLp.toLp 2 (G (t,x)) : EuclideanSpace ℝ (Fin d))).ofLp =
        fun j => ∫ t in Ioo 0 T, G (t,x) j := by
  have hballs (n : ℕ) : ∀ᵐ x ∂(volume : Measure (Vec d)),
      x ∈ originBall d ((n : ℝ)+1) → ∀ T : ℝ, T ≤ S →
      (∫ t in Ioo 0 T, (WithLp.toLp 2 (G (t,x)) : EuclideanSpace ℝ (Fin d))).ofLp =
        fun j => ∫ t in Ioo 0 T, G (t,x) j := by
    let R : ℝ := (n : ℝ)+1
    have hR : 0 < R := by positivity
    have hv := ENNReal.toReal_pos_iff.mp (show 0 < (volume (originBall d R)).toReal by
      simpa only [originBall,ball,sub_zero] using ball_volume_pos_finite d R hR)
    let ν : Measure (Vec d) := (volume (originBall d R))⁻¹ • volume.restrict (originBall d R)
    letI : IsProbabilityMeasure ν := ⟨by
      simp only [ν,Measure.smul_apply,smul_eq_mul,Measure.restrict_apply_univ]
      exact ENNReal.inv_mul_cancel hv.1.ne' hv.2.ne⟩
    have hc := initial_euclidean_integral_coordinates ν
      (semigroup_initial_euclidean_energy hK hsol hG hb hS hR)
    have hc' := (Measure.ae_smul_measure_iff (ENNReal.inv_ne_zero.mpr hv.2.ne)).mp hc
    apply (ae_restrict_iff' (measurableSet_lt (by
      unfold euclideanNorm euclideanSq dot
      fun_prop) measurable_const)).mp hc'
  filter_upwards [ae_all_iff.mpr hballs] with x hx
  obtain ⟨n,hn⟩ := exists_nat_gt (euclideanNorm x)
  exact hx n (show euclideanNorm x < (n : ℝ)+1 by linarith)

end EinsteinRelation.Correctors
