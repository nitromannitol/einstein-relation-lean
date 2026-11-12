import EinsteinRelation.Correctors.ParabolicSpatialEnergyPrimitive
import EinsteinRelation.Correctors.ParabolicWeightedEnergyContinuity
import EinsteinRelation.Correctors.PairedPDECoercivity
import EinsteinRelation.Correctors.PrescribedBallCutoff
import EinsteinRelation.Correctors.SemigroupPrescribedGradient
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! # Initial-layer energy of the actual scalar semigroup

Source: `paper/main.tex:800–808,842–844`. A bounded scalar flow has uniformly
bounded gradient energy on positive strips down to time zero. The estimate
uses the actual weak equation and positive-time scalar continuity.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- A bounded scalar flow controls its spatially localized gradient energy
uniformly in the lower positive endpoint. Source: `paper/main.tex:800–808,842–844`. -/
theorem semigroup_cutoff_energy_le
    {d : ℕ} {K : ℝ} (hK : 0 < K)
    {A : Coefficient d K} {g : Vec d → Vec d}
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hsol : IsSemigroupSolution A g u G)
    {B : ℝ} (hb : ∀ t, 0 < t → ∀ x, |u (t,x)| ≤ B)
    {a b R : ℝ} (ha : 0 < a) (hab : a < b) (hR : 0 < R)
    {χ : Vec d → ℝ} (hχ : IsSpatialTest (originBall d R) χ)
    (hχb : ∀ x, |χ x| ≤ 1)
    {D : ℝ} (hχD : ∀ x, euclideanSq (gradient χ x) ≤ D) :
    (∫ z in Set.Ioo a b ×ˢ originBall d R, χ z.2 ^ 2 * euclideanSq (G z)) ≤
      B^2 * volume.real (originBall d R) +
        4*K^2*B^2*D*volume.real (Set.Ioo a b ×ˢ originBall d R) := by
  let U := originBall d R
  let S := Set.Ioo a b ×ˢ U
  have hUc := isCompact_closure_originBall d R
  letI : IsFiniteMeasure (volume.restrict U) := isFiniteMeasure_restrict.mpr
    (ne_top_of_le_ne_top (hUc.measure_ne_top (μ := volume)) (measure_mono subset_closure))
  have hprod : (volume : Measure (ℝ × Vec d)).restrict S =
      (volume.restrict (Set.Ioo a b)).prod (volume.restrict U) := by
    simp only [S, Measure.volume_eq_prod, Measure.prod_restrict]
  letI : IsFiniteMeasure (volume.restrict S) := by rw [hprod]; infer_instance
  have hlocal := hsol.2.1 a b R ha hab hR
  let P := fun z : ℝ × Vec d => dot ((A z.2).mulVec (G z)) (fun j =>
    χ z.2 ^ 2 * G z j + 2*χ z.2*u z*coordinateDerivative j χ z.2)
  let E := fun z : ℝ × Vec d => χ z.2 ^ 2 * euclideanSq (G z)
  let Err := fun z : ℝ × Vec d => u z ^ 2 * euclideanSq (gradient χ z.2)
  let f := fun t : ℝ => ∫ x in U, χ x^2*u (t,x)^2
  have hPi : Integrable P (volume.restrict S) :=
    parabolicSolution_spatial_energy_flux_integrable hK A hlocal hχ.1 hχ.2.1
  have hEi : Integrable E (volume.restrict S) := by
    have hm : MemLp (fun z : ℝ × Vec d => χ z.2) ∞ (volume.restrict S) :=
      memLp_top_of_bound (hχ.1.continuous.measurable.comp measurable_snd).aestronglyMeasurable 1
        (ae_of_all _ fun z => by rw [Real.norm_eq_abs]; exact hχb _)
    convert (hlocal.2.2.1.mul' hm).integrable_sq using 1
    funext z
    simp only [E, mul_pow, euclideanNorm, Real.sq_sqrt (euclideanSq_nonneg_fisher _)]
  have hErri : Integrable Err (volume.restrict S) := by
    have hd : Continuous (fun x : Vec d => euclideanSq (gradient χ x)) := by
      have hc : Continuous (gradient χ) := continuous_pi fun j =>
        (hχ.1.continuous_fderiv (by simp)).clm_apply continuous_const
      unfold euclideanSq dot
      fun_prop
    apply hlocal.1.integrable_sq.mul_bdd
      (hd.measurable.comp measurable_snd).aestronglyMeasurable
    exact ae_of_all _ fun z => by
      change ‖euclideanSq (gradient χ z.2)‖ ≤ D
      rw [Real.norm_eq_abs, abs_of_nonneg (euclideanSq_nonneg_fisher _)]
      exact hχD _
  have hcont : ContinuousOn f (Set.Ioi 0) := by
    obtain ⟨v,hv,hr⟩ := semigroupSolution_exists_continuous_local_L2 hsol hUc
    apply (continuousOn_weighted_square_integral_of_L2
      (hχ.1.continuous.memLp_top_of_hasCompactSupport hχ.2.1 _) hv).congr
    intro t ht
    exact integral_congr_ae ((hr t ht).mono fun x hx => by dsimp only [f]; rw [hx])
  have heq := parabolicSolution_spatial_energy_integral_eq_sub hK hab
    (show IsOpen U from by
      unfold U originBall euclideanNorm euclideanSq dot
      exact isOpen_lt (by fun_prop) continuous_const)
    hlocal hχ.1 hχ.2.1 hχ.2.2
    (hcont.mono (fun t ht => ha.trans_le ht.1))
  have hPint : 2*(∫ z in S, P z) = f a - f b := by
    rw [hprod, integral_prod _ (hprod ▸ hPi)]
    rw [integral_const_mul, integral_Icc_eq_integral_Ioo] at heq
    dsimp only [P, f] at *
    linarith
  have hpoint (z : ℝ × Vec d) : E z ≤ 2*P z + 4*K^2*Err z := by
    have hh := paired_cutoff_coercivity hK A z.2 (χ z.2 • G z) (gradient χ z.2)
      (u z) 1 zero_le_one 1 (by decide)
    have hs : euclideanSq (χ z.2 • G z) = χ z.2^2 * euclideanSq (G z) := by
      simp only [euclideanSq, dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    have hdot (c : ℝ) (v w : Vec d) : dot (c • v) w = c * dot v w :=
      smul_dotProduct c v w
    have hdot' (c : ℝ) (v w : Vec d) : dot v (c • w) = c * dot v w :=
      dotProduct_smul c v w
    simp only [Matrix.mulVec_smul, hs, hdot, hdot',
      Nat.cast_one, Nat.reduceSub, one_pow, mul_one, one_mul] at hh
    have hp : P z = χ z.2^2*dot (G z) ((A z.2).mulVec (G z)) +
        2*χ z.2*u z*dot ((A z.2).mulVec (G z)) (gradient χ z.2) := by
      simp only [P, dot, gradient, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hp]
    dsimp only [E, Err]
    change χ z.2^2 * euclideanSq (G z) ≤ _ at hh
    norm_num only [Nat.cast_ofNat] at hh
    nlinarith only [hh]
  have hint := integral_mono hEi ((hPi.const_mul 2).add (hErri.const_mul (4*K^2))) hpoint
  change (∫ z in S, E z) ≤ ∫ z in S, 2*P z + 4*K^2*Err z at hint
  rw [integral_add (hPi.const_mul 2) (hErri.const_mul (4*K^2)),
    integral_const_mul, integral_const_mul, hPint] at hint
  have hfa : f a ≤ B^2*volume.real U := by
    have hχm := hχ.1.continuous.memLp_top_of_hasCompactSupport hχ.2.1 (volume.restrict U)
    have hfi := ((semigroupSolution_scalar_memLp_on_precompact hsol hUc ha).mul' hχm).integrable_sq
    have hfii : Integrable (fun x => χ x^2*u (a,x)^2) (volume.restrict U) := by
      simpa only [mul_pow] using hfi
    have hh := integral_mono hfii (integrable_const (B^2)) (fun x => by
      have hχsq : χ x^2 ≤ 1 := by nlinarith only [(abs_le.mp (hχb x)).1, (abs_le.mp (hχb x)).2]
      have husq : u (a,x)^2 ≤ B^2 := by
        simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hb a ha x) 2
      exact (mul_le_mul_of_nonneg_left husq (sq_nonneg _)).trans
        (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hχsq (sq_nonneg B)))
    simpa only [integral_const, measureReal_restrict_apply_univ, smul_eq_mul, mul_comm] using hh
  have hErrb : (∫ z in S, Err z) ≤ B^2*D*volume.real S := by
    have hh := integral_mono_ae hErri (integrable_const (B^2*D)) (by
      filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod (by
        unfold U originBall euclideanNorm euclideanSq dot
        exact measurableSet_lt (by fun_prop) measurable_const))] with z hz
      have husq : u z^2 ≤ B^2 := by
        simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hb z.1 (ha.trans hz.1.1) z.2) 2
      exact mul_le_mul husq (hχD _) (euclideanSq_nonneg_fisher _) (sq_nonneg B))
    simpa only [integral_const, measureReal_restrict_apply_univ, smul_eq_mul, mul_comm] using hh
  have hfb : 0 ≤ f b := integral_nonneg fun _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hh := mul_le_mul_of_nonneg_left hErrb (show 0 ≤ 4*K^2 by positivity)
  dsimp only [E] at hint
  dsimp only [S, U] at *
  nlinarith only [hint, hfa, hfb, hh]

/-- Local gradient energy of a bounded scalar semigroup is integrable through
time zero. Source: `paper/main.tex:800–808,842–844`. -/
theorem semigroup_gradient_energy_integrable_through_zero
    {d : ℕ} {K : ℝ} (hK : 0 < K)
    {A : Coefficient d K} {g : Vec d → Vec d}
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hsol : IsSemigroupSolution A g u G)
    {B : ℝ} (hb : ∀ t, 0 < t → ∀ x, |u (t,x)| ≤ B)
    {T R : ℝ} (hT : 0 < T) (hR : 0 < R) :
    IntegrableOn (fun z => euclideanSq (G z)) (Set.Ioo 0 T ×ˢ originBall d R) := by
  obtain ⟨χ,D,hD,hχ,hχb,hχr,hχD⟩ := exists_prescribed_spatial_ball_cutoff d R hR
  let U := originBall d (2*R)
  let S := Set.Ioo 0 T ×ˢ U
  let E := fun z : ℝ × Vec d => χ z.2^2 * euclideanSq (G z)
  have hU : MeasurableSet U := by
    unfold U originBall euclideanNorm euclideanSq dot
    exact measurableSet_lt (by fun_prop) measurable_const
  have hS : MeasurableSet S := measurableSet_Ioo.prod hU
  have hUc := isCompact_closure_originBall d (2*R)
  letI : IsFiniteMeasure (volume.restrict U) := isFiniteMeasure_restrict.mpr
    (ne_top_of_le_ne_top (hUc.measure_ne_top (μ := volume)) (measure_mono subset_closure))
  have hprod : (volume : Measure (ℝ × Vec d)).restrict S =
      (volume.restrict (Set.Ioo 0 T)).prod (volume.restrict U) := by
    simp only [S, Measure.volume_eq_prod, Measure.prod_restrict]
  letI : IsFiniteMeasure (volume.restrict S) := by rw [hprod]; infer_instance
  let a : ℕ → ℝ := fun n => T / ((n : ℝ)+2)
  have hap (n : ℕ) : 0 < a n := div_pos hT (by positivity)
  have haT (n : ℕ) : a n < T := div_lt_self hT (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
  have ha0 : Tendsto a atTop (𝓝 0) := by
    have hh := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
      (tendsto_add_atTop_nat 1)
    have heq : (fun n : ℕ => T*((1:ℝ)/(((n+1:ℕ):ℝ)+1))) = a := by
      funext n
      dsimp only [a]
      push_cast
      ring
    have hm := hh.const_mul T
    dsimp only [Function.comp_def] at hm
    rw [heq, mul_zero] at hm
    exact hm
  let Sn := fun n => Set.Ioo (a n) T ×ˢ U
  have hSn (n : ℕ) : MeasurableSet (Sn n) := measurableSet_Ioo.prod hU
  have hsub (n : ℕ) : Sn n ⊆ S := Set.prod_mono
    (Set.Ioo_subset_Ioo (hap n).le le_rfl) Set.Subset.rfl
  have hcover : AECover (volume.restrict S) atTop Sn := by
    refine ⟨?_,hSn⟩
    filter_upwards [ae_restrict_mem hS] with z hz
    exact (ha0.eventually (gt_mem_nhds hz.1.1)).mono fun n hn => ⟨⟨hn,hz.1.2⟩,hz.2⟩
  have hi (n : ℕ) : IntegrableOn E (Sn n) := by
    change Integrable E (volume.restrict (Sn n))
    have hm : MemLp (fun z : ℝ × Vec d => χ z.2) ∞ (volume.restrict (Sn n)) :=
      memLp_top_of_bound (hχ.1.continuous.measurable.comp measurable_snd).aestronglyMeasurable 1
        (ae_of_all _ fun z => by rw [Real.norm_eq_abs]; exact hχb _)
    convert ((hsol.2.1 (a n) T (2*R) (hap n) (haT n) (by positivity)).2.2.1.mul' hm).integrable_sq using 1
    funext z
    simp only [E, mul_pow, euclideanNorm, Real.sq_sqrt (euclideanSq_nonneg_fisher _)]
  have hbound (n : ℕ) : (∫ z in Sn n, E z) ≤
      B^2 * volume.real U + 4*K^2*B^2*D^2*volume.real S := by
    have hh := semigroup_cutoff_energy_le hK hsol hb (hap n) (haT n)
      (show 0 < 2*R by positivity) hχ hχb (D := D^2) (fun x => by
        have hh := pow_le_pow_left₀ (Real.sqrt_nonneg _) (hχD x) 2
        simpa only [euclideanNorm, Real.sq_sqrt (euclideanSq_nonneg_fisher _)] using hh)
    apply hh.trans
    have hv : volume.real (Sn n) ≤ volume.real S :=
      measureReal_mono (hsub n) (by simpa only [Measure.restrict_apply_univ] using
        (measure_ne_top (volume.restrict S) Set.univ))
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hv
      (show 0 ≤ 4*K^2*B^2*D^2 by positivity))
  have hEi : Integrable E (volume.restrict S) := by
    apply hcover.integrable_of_integral_bounded_of_nonneg_ae
      (B^2 * volume.real U + 4*K^2*B^2*D^2*volume.real S)
      (fun n => (hi n).restrict) (ae_of_all _ fun _ => mul_nonneg (sq_nonneg _) (euclideanSq_nonneg_fisher _))
    exact .of_forall fun n => by
      rw [Measure.restrict_restrict (hSn n), Set.inter_eq_left.mpr (hsub n)]
      exact hbound n
  have hs : Set.Ioo 0 T ×ˢ originBall d R ⊆ S := Set.prod_mono Set.Subset.rfl
    (fun x hx => by change euclideanNorm x < 2*R; exact lt_of_lt_of_le hx (by linarith only [hR]))
  apply (hEi.mono_measure (Measure.restrict_mono hs le_rfl)).congr
  filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod (show MeasurableSet (originBall d R) by
    unfold originBall euclideanNorm euclideanSq dot
    exact measurableSet_lt (by fun_prop) measurable_const))] with z hz
  simp only [E, hχr z.2 hz.2, one_pow, one_mul]

end EinsteinRelation.Correctors
