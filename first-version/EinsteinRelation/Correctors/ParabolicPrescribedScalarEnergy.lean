import EinsteinRelation.Correctors.ParabolicLocalStripEnergy
import EinsteinRelation.Correctors.SemigroupPrescribedGradient

open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- Prescribed local gradient energy is controlled by a scalar cylinder
energy, uniformly over solutions. Source: `paper/main.tex:798–806,850`. -/
theorem parabolicFamily_prescribed_local_scalar_energy {d : ℕ} {K t R : ℝ}
    (hK : 0 < K) (ht : 0 < t) (hR : 0 < R) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (A : Coefficient d K)
      (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d) (J : Vec d → Vec d),
      ContinuousOn u (Set.Ioi 0 ×ˢ Set.univ) →
      (∀ a b r : ℝ, 0 < a → a < b → 0 < r →
        IsParabolicSolution A (Set.Ioo a b) (originBall d r) u G) →
      MemLp (fun x => u (t,x)) 2 (volume.restrict (originBall d R)) →
      HasWeakGradient Set.univ (fun x => u (t,x)) J →
      MemLp (fun x => euclideanNorm (J x)) 2 (volume.restrict (originBall d R)) ∧
      (∫ x in originBall d R, euclideanNorm (J x)^2) ≤
        D * ∫ z in Set.Ioo (t/4) (5*t/4) ×ˢ originBall d (4*R), (u z)^2 := by
  obtain ⟨χ,L,hL,hχ,hχb,hχ1,hχD⟩ := exists_prescribed_spatial_ball_cutoff d R hR
  obtain ⟨E,hE,henergy⟩ := parabolicSolution_local_strip_gradient_energy hK
    (half_pos ht) (by linarith : t/2 < t) (by positivity : 0 < 2*R)
  let B := 2*K/(t-t/2)+2*K^2*L^2
  have hdiff : 0 < t-t/2 := by linarith
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  refine ⟨(d : ℝ)*B*E,by positivity,?_⟩
  intro A u G J hu hsol hub hJ
  have hopen (r : ℝ) : IsOpen (originBall d r) := by
    unfold originBall euclideanNorm euclideanSq dot
    exact isOpen_lt (by fun_prop) continuous_const
  have hU := isCompact_closure_originBall d (2*R)
  have hV := isCompact_closure_originBall d R
  letI : IsFiniteMeasure (volume.restrict (originBall d (2*R))) :=
    isFiniteMeasure_restrict.mpr (ne_top_of_le_ne_top
      (hU.measure_ne_top (μ := volume)) (measure_mono subset_closure))
  letI : IsFiniteMeasure (volume.restrict (originBall d R)) :=
    isFiniteMeasure_restrict.mpr (ne_top_of_le_ne_top
      (hV.measure_ne_top (μ := volume)) (measure_mono subset_closure))
  obtain ⟨H,hw,hHL,hHb⟩ := parabolicSolution_prescribed_gradient_energy hK
    (half_pos ht) (by linarith : t/2 < t) (hopen (2*R))
    (show originBall d R ⊆ originBall d (2*R) from fun x hx =>
      lt_of_lt_of_le (show euclideanNorm x < R from hx) (by linarith only [hR]))
    (hopen R).measurableSet hu
    (hsol (t/2) t (2*R) (half_pos ht) (by linarith) (by positivity)) hub
    hχ hχb hχ1 hL hχD
  have heq : H =ᵐ[volume.restrict (originBall d R)] J := by
    filter_upwards [ae_all_iff.mpr fun j => weakPartialDerivative_ae_eq_on_open (hopen R)
      (hw j) (hasWeakGradient_mono (Set.subset_univ _) hJ j)] with x hx
    exact funext hx
  have hJL := (memLp_congr_ae (heq.mono fun x hx => congrArg euclideanNorm hx)).mp hHL
  refine ⟨hJL,?_⟩
  have heL : (∫ x in originBall d R, euclideanNorm (J x)^2) =
      (eLpNorm (fun x => euclideanNorm (H x)) 2
        (volume.restrict (originBall d R))).toReal^2 := by
    rw [← Lp.norm_toLp _ hHL,← real_inner_self_eq_norm_sq,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hHL.coeFn_toLp,heq] with x hx he
    simp only [hx,he,RCLike.inner_apply,conj_trivial,pow_two]
  rw [heL]
  have hEn : 0 ≤ ∫ z in Set.Ioo (t/2) t ×ˢ originBall d (2*R), euclideanSq (G z) :=
    integral_nonneg fun z => euclideanSq_nonneg_fisher _
  have hh := pow_le_pow_left₀ ENNReal.toReal_nonneg hHb 2
  rw [mul_pow,Real.sq_sqrt (Nat.cast_nonneg d),Real.sq_sqrt (mul_nonneg hB hEn)] at hh
  apply hh.trans
  have hgc := henergy A u G (by
    convert hsol (t/4) (5*t/4) (4*R) (by positivity) (by linarith) (by positivity) using 1 <;> congr 1 <;> ring)
  have heG : (∫ z in Set.Ioo (t/2) t ×ˢ originBall d (2*R), euclideanSq (G z)) =
      ∫ z in Set.Ioo (t/2) t ×ˢ originBall d (2*R), euclideanNorm (G z)^2 := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun z => (Real.sq_sqrt (euclideanSq_nonneg_fisher (G z))).symm
  rw [heG]
  have hb := mul_le_mul_of_nonneg_left hgc (mul_nonneg (Nat.cast_nonneg d) hB)
  simpa only [B,mul_assoc,show t/2/2 = t/4 by ring,
    show t+t/4 = 5*t/4 by ring,show 2*(2*R) = 4*R by ring] using hb

end EinsteinRelation.Correctors
