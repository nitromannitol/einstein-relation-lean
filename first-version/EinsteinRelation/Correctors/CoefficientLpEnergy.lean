import EinsteinRelation.Correctors.RegularizedGradientEnergy
import EinsteinRelation.Correctors.EllipticOperatorBound
import EinsteinRelation.TimeChange.EuclideanTransport
import EinsteinRelation.Mobility.DriftBoundPointwise

open MeasureTheory
namespace EinsteinRelation.Correctors
open Environment.AKMTestIntegralSupport

/-- Actual L² vector energy in the Euclidean coordinate carrier.
Source: `paper/main.tex:798–806`; localized energy estimates. -/
theorem integral_euclideanSq_Lp {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {d : ℕ} (f : Lp (EuclideanSpace ℝ (Fin d)) 2 μ) :
    (∫ x, euclideanSq (f x).ofLp ∂μ) = ‖f‖^2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards with x
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,euclideanSq,dot]

/-- Coefficient flux coordinates belong to the actual local L² space.
Source: `paper/main.tex:798–806`; symmetric coefficient energy. -/
theorem coefficient_mulVec_memLp {d : ℕ} {K : ℝ} (hK : 0 ≤ K)
    (A : Coefficient d K) (U : Set (Vec d))
    (f : Lp (EuclideanSpace ℝ (Fin d)) 2 (volume.restrict U)) (i : Fin d) :
    MemLp (fun x => (A x).mulVec (f x).ofLp i) 2 (volume.restrict U) := by
  have hf j := (memLp_euclidean_iff_coordinates _ _).mp (Lp.memLp f) j
  have hA j : MemLp (fun x => A x i j) ⊤ (volume.restrict U) := by
    apply memLp_top_of_bound
      ((A.locally_integrable i j).aestronglyMeasurable.mono_measure Measure.restrict_le_self) K
    filter_upwards with x
    rw [Real.norm_eq_abs]
    apply abs_entry_le_of_quadratic_bounds hK (A x) (A.symmetric x)
    · intro ξ
      exact (show 0 ≤ euclideanSq ξ from by
        unfold euclideanSq dot
        exact Finset.sum_nonneg fun j _ => mul_self_nonneg _).trans (A.elliptic x ξ).1
    · exact fun ξ => (A.elliptic x ξ).2
  simpa only [Matrix.mulVec,dotProduct,mul_comm] using
    memLp_finset_sum Finset.univ (fun j _ => (hf j).mul' (r := 2) (hA j))

/-- The actual localized coefficient energy is nonnegative and bounded above
by the uniform ellipticity constant. Source: `paper/main.tex:798–806`. -/
theorem coefficient_cutoff_energy_bounds {d : ℕ} {K : ℝ} (hK : 0 ≤ K)
    (A : Coefficient d K) {U : Set (Vec d)} {χ : Vec d → ℝ}
    (hχ : IsSpatialTest U χ) (hχb : ∀ x, |χ x| ≤ 1)
    (f : Lp (EuclideanSpace ℝ (Fin d)) 2 (volume.restrict U)) :
    (∫ x in U, χ x^2 * euclideanSq (f x).ofLp) ≤
      (∫ x in U, χ x^2 * dot ((A x).mulVec (f x).ofLp) (f x).ofLp) ∧
    (∫ x in U, χ x^2 * dot ((A x).mulVec (f x).ofLp) (f x).ofLp) ≤ K * ‖f‖^2 := by
  have hG j := (memLp_euclidean_iff_coordinates _ _).mp (Lp.memLp f) j
  have hF := coefficient_mulVec_memLp hK A U f
  obtain ⟨_,_,_,he⟩ := localized_H1_energy_products_integrable hχ
    (MemLp.zero' : MemLp (fun _ : Vec d => (0 : ℝ)) 2 (volume.restrict U)) hF hG
  have hsq : Integrable (fun x => euclideanSq (f x).ofLp) (volume.restrict U) := by
    simpa only [euclideanSq,dot,← pow_two] using
      integrable_finset_sum Finset.univ (fun j _ => (hG j).integrable_sq)
  have hχm : MemLp (fun x => χ x^2) ⊤ (volume.restrict U) :=
    memLp_top_of_bound (hχ.1.continuous.aestronglyMeasurable.pow 2) 1
      (Filter.Eventually.of_forall fun x => by
        simpa only [Real.norm_eq_abs,abs_sq,sq_abs,one_pow] using
          pow_le_pow_left₀ (abs_nonneg _) (hχb x) 2)
  have hsqχ : Integrable (fun x => χ x^2 * euclideanSq (f x).ofLp) (volume.restrict U) := by
    simpa only [mul_comm] using hsq.mul_of_top_right hχm
  have hpos x : 0 ≤ euclideanSq (f x).ofLp := by
    unfold euclideanSq dot
    exact Finset.sum_nonneg fun j _ => mul_self_nonneg _
  have hcomm x : dot ((A x).mulVec (f x).ofLp) (f x).ofLp =
      dot (f x).ofLp ((A x).mulVec (f x).ofLp) := by
    unfold dot
    apply Finset.sum_congr rfl
    intros
    ring
  constructor
  · apply integral_mono hsqχ he
    intro x
    dsimp only
    rw [hcomm]
    exact mul_le_mul_of_nonneg_left (A.elliptic x (f x).ofLp).1 (sq_nonneg _)
  · rw [← integral_euclideanSq_Lp (volume.restrict U) f, ← integral_const_mul]
    apply integral_mono he (hsq.const_mul K)
    intro x
    dsimp only
    rw [hcomm]
    calc
      _ ≤ χ x^2 * (K * euclideanSq (f x).ofLp) :=
        mul_le_mul_of_nonneg_left (A.elliptic x (f x).ofLp).2 (sq_nonneg _)
      _ ≤ 1 * (K * euclideanSq (f x).ofLp) :=
        mul_le_mul_of_nonneg_right (by
          simpa only [sq_abs,one_pow] using
            pow_le_pow_left₀ (abs_nonneg _) (hχb x) 2) (mul_nonneg hK (hpos x))
      _ = _ := one_mul _

/-- The localized flux error is bounded by the actual gradient L² energy.
Source: `paper/main.tex:798–806`; AKM Lemma 8.2. -/
theorem coefficient_cutoff_flux_error_le {d : ℕ} {K : ℝ} (hK : 0 < K)
    (A : Coefficient d K) {U : Set (Vec d)} {χ : Vec d → ℝ}
    (hχ : IsSpatialTest U χ) {L : ℝ} (_hL : 0 ≤ L)
    (hχb : ∀ x, euclideanNorm (gradient χ x) ≤ L)
    (f : Lp (EuclideanSpace ℝ (Fin d)) 2 (volume.restrict U)) :
    (∫ x in U, (dot ((A x).mulVec (f x).ofLp) (gradient χ x))^2) ≤
      K^2 * L^2 * ‖f‖^2 := by
  have hG j := (memLp_euclidean_iff_coordinates _ _).mp (Lp.memLp f) j
  have hF := coefficient_mulVec_memLp hK.le A U f
  obtain ⟨hw,_,_,_⟩ := localized_H1_energy_products_integrable hχ
    (MemLp.zero' : MemLp (fun _ : Vec d => (0 : ℝ)) 2 (volume.restrict U)) hF hG
  have hn : (∫ x in U, ‖f x‖^2) = ‖f‖^2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    simp_rw [real_inner_self_eq_norm_sq]
  rw [← hn, ← integral_const_mul]
  apply integral_mono hw.integrable_sq (((Lp.memLp f).norm.integrable_sq).const_mul _)
  intro x
  dsimp only
  have hop := mulVec_euclideanNorm_le_of_quadratic (A x) hK (A.symmetric x)
    (fun ξ => (show 0 ≤ euclideanSq ξ from by
      unfold euclideanSq dot
      exact Finset.sum_nonneg fun j _ => mul_self_nonneg _).trans (A.elliptic x ξ).1)
    (fun ξ => (A.elliptic x ξ).2) (f x).ofLp
  rw [TimeChange.euclideanNorm_eq_norm_toLp (f x).ofLp,WithLp.toLp_ofLp] at hop
  have habs : |dot ((A x).mulVec (f x).ofLp) (gradient χ x)| ≤
      euclideanNorm ((A x).mulVec (f x).ofLp) * euclideanNorm (gradient χ x) := by
    have hi := abs_real_inner_le_norm
      (WithLp.toLp 2 ((A x).mulVec (f x).ofLp) : EuclideanSpace ℝ (Fin d))
      (WithLp.toLp 2 (gradient χ x) : EuclideanSpace ℝ (Fin d))
    simpa only [TimeChange.euclideanNorm_eq_norm_toLp,PiLp.inner_apply,
      RCLike.inner_apply,conj_trivial,WithLp.ofLp_toLp,dot,mul_comm] using hi
  have hb : |dot ((A x).mulVec (f x).ofLp) (gradient χ x)| ≤ K * ‖f x‖ * L :=
    habs.trans (mul_le_mul hop (hχb x) (Real.sqrt_nonneg _) (by positivity))
  calc
    _ ≤ (K * ‖f x‖ * L)^2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hb 2
    _ = _ := by ring

end EinsteinRelation.Correctors
