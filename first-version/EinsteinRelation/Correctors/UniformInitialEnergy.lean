import EinsteinRelation.Correctors.SemigroupZeroPotential
import EinsteinRelation.Correctors.EuclideanTimeSpaceCauchy

/-! # Uniform local gradient energy through time zero

Source: `paper/main.tex:800–808,842–844`. The cutoff inequality has a
constant independent of the coefficient field and the lower time endpoint.
Passing to zero retains that bound, in addition to local integrability.
-/

open MeasureTheory Filter Topology
open scoped ENNReal
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- Integration in a finite time interval maps the actual space-time L2
field to spatial L2, with its Cauchy--Schwarz energy bound.
Source: `paper/main.tex:844–849`. -/
theorem time_integral_memLp_two {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (ν : Measure X) [SigmaFinite ν] {T : ℝ} (hT : 0 ≤ T)
    {g : ℝ × X → E} (hg : MemLp g 2 ((volume.restrict (Set.Ioo 0 T)).prod ν)) :
    MemLp (fun x => ∫ t in Set.Ioo 0 T, g (t,x)) 2 ν ∧
      (∫ x, ‖∫ t in Set.Ioo 0 T, g (t,x)‖^2 ∂ν) ≤
        T * ∫ z, ‖g z‖^2 ∂((volume.restrict (Set.Ioo 0 T)).prod ν) := by
  let μ := volume.restrict (Set.Ioo 0 T)
  have hsq : Integrable (fun z => ‖g z‖^2) (μ.prod ν) :=
    (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mp hg
  have hslice : ∀ᵐ x ∂ν, MemLp (fun t => g (t,x)) 2 μ := by
    filter_upwards [hg.aestronglyMeasurable.prodMk_right,hsq.prod_left_ae] with x hx hs
    exact (memLp_two_iff_integrable_sq_norm hx).mpr hs
  have hbound : ∀ᵐ x ∂ν,
      ‖∫ t in Set.Ioo 0 T, g (t,x)‖^2 ≤ T * ∫ t in Set.Ioo 0 T, ‖g (t,x)‖^2 := by
    filter_upwards [hslice] with x hx
    dsimp only [μ] at hx
    rw [restrict_Ioo_eq_restrict_Icc] at hx
    simpa only [integral_Icc_eq_integral_Ioo] using norm_time_integral_sq_le_energy hT _ hx
  have hi := hsq.integral_prod_right.const_mul T
  have hm : AEStronglyMeasurable (fun x => ∫ t in Set.Ioo 0 T, g (t,x)) ν :=
    hg.aestronglyMeasurable.prod_swap.integral_prod_right'
  have hli : Integrable (fun x => ‖∫ t in Set.Ioo 0 T, g (t,x)‖^2) ν :=
    hi.mono' (hm.norm.pow 2) (by
      filter_upwards [hbound] with x hx
      simpa only [Real.norm_of_nonneg (sq_nonneg _)] using hx)
  refine ⟨(memLp_two_iff_integrable_sq_norm hm).mpr hli,?_⟩
  calc
    _ ≤ ∫ x, T * ∫ t, ‖g (t,x)‖^2 ∂μ ∂ν := integral_mono_ae hli hi hbound
    _ = T * ∫ x, ∫ t, ‖g (t,x)‖^2 ∂μ ∂ν := integral_const_mul _ _
    _ = _ := congrArg (fun a => T*a) (integral_prod_symm _ hsq).symm

/-- The local initial-layer energy bound depends only on ellipticity, the
uniform scalar bound, time and radius. Source: `paper/main.tex:842–844`. -/
theorem exists_uniform_initial_gradient_energy_bound
    {d : ℕ} {K B T R : ℝ} (hK : 0 < K) (hT : 0 < T) (hR : 0 < R) :
    ∃ C : ℝ, ∀ (A : Coefficient d K) (g : Vec d → Vec d)
      (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
      IsSemigroupSolution A g u G →
      (∀ t, 0 < t → ∀ x, |u (t,x)| ≤ B) →
      (∫ z in Set.Ioo 0 T ×ˢ originBall d R, euclideanSq (G z)) ≤ C := by
  obtain ⟨χ,D,_hD,hχ,hχb,hχr,hχD⟩ := exists_prescribed_spatial_ball_cutoff d R hR
  let U := originBall d (2*R)
  let S := Set.Ioo 0 T ×ˢ U
  have hU : MeasurableSet U := by
    unfold U originBall euclideanNorm euclideanSq dot
    exact measurableSet_lt (by fun_prop) measurable_const
  have hS : MeasurableSet S := measurableSet_Ioo.prod hU
  letI : IsFiniteMeasure (volume.restrict U) := isFiniteMeasure_restrict.mpr
    (ne_top_of_le_ne_top ((isCompact_closure_originBall d (2*R)).measure_ne_top (μ := volume))
      (measure_mono subset_closure))
  have hprod : (volume : Measure (ℝ × Vec d)).restrict S =
      (volume.restrict (Set.Ioo 0 T)).prod (volume.restrict U) := by
    simp only [S,Measure.volume_eq_prod,Measure.prod_restrict]
  letI : IsFiniteMeasure (volume.restrict S) := by rw [hprod]; infer_instance
  refine ⟨B^2 * volume.real U + 4*K^2*B^2*D^2*volume.real S,?_⟩
  intro A g u G hsol hb
  let E := fun z : ℝ × Vec d => χ z.2^2 * euclideanSq (G z)
  have hEi : Integrable E (volume.restrict S) := by
    have hm : MemLp (fun z : ℝ × Vec d => χ z.2) ∞ (volume.restrict S) :=
      memLp_top_of_bound (hχ.1.continuous.measurable.comp measurable_snd).aestronglyMeasurable 1
        (ae_of_all _ fun z => by rw [Real.norm_eq_abs]; exact hχb _)
    convert ((semigroup_initial_strip_memLp hK hsol hb hT
      (show 0 < 2*R by positivity)).2.mul' hm).integrable_sq using 1
    funext z
    simp only [E,mul_pow,euclideanNorm,Real.sq_sqrt (euclideanSq_nonneg_fisher _)]
  let a : ℕ → ℝ := fun n => T / ((n : ℝ)+2)
  have hap (n : ℕ) : 0 < a n := div_pos hT (by positivity)
  have haT (n : ℕ) : a n < T :=
    div_lt_self hT (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
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
    rwa [heq,mul_zero] at hm
  let Sn := fun n => Set.Ioo (a n) T ×ˢ U
  have hSn (n : ℕ) : MeasurableSet (Sn n) := measurableSet_Ioo.prod hU
  have hsub (n : ℕ) : Sn n ⊆ S :=
    Set.prod_mono (Set.Ioo_subset_Ioo (hap n).le le_rfl) Set.Subset.rfl
  have hcover : AECover (volume.restrict S) atTop Sn := by
    refine ⟨?_,hSn⟩
    filter_upwards [ae_restrict_mem hS] with z hz
    exact (ha0.eventually (gt_mem_nhds hz.1.1)).mono fun n hn => ⟨⟨hn,hz.1.2⟩,hz.2⟩
  have hlim := hcover.integral_tendsto_of_countably_generated hEi
  have hEb : (∫ z in S, E z) ≤
      B^2 * volume.real U + 4*K^2*B^2*D^2*volume.real S := by
    apply le_of_tendsto hlim
    filter_upwards with n
    rw [Measure.restrict_restrict (hSn n),Set.inter_eq_left.mpr (hsub n)]
    have hh := semigroup_cutoff_energy_le hK hsol hb (hap n) (haT n)
      (show 0 < 2*R by positivity) hχ hχb (D := D^2) (fun x => by
        have hh := pow_le_pow_left₀ (Real.sqrt_nonneg _) (hχD x) 2
        simpa only [euclideanNorm,Real.sq_sqrt (euclideanSq_nonneg_fisher _)] using hh)
    apply hh.trans
    have hv : volume.real (Sn n) ≤ volume.real S :=
      measureReal_mono (hsub n) (by simpa only [Measure.restrict_apply_univ] using
        (measure_ne_top (volume.restrict S) Set.univ))
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hv (by positivity))
  have hs : Set.Ioo 0 T ×ˢ originBall d R ⊆ S := Set.prod_mono Set.Subset.rfl
    (fun x hx => by
      change euclideanNorm x < 2*R
      exact lt_of_lt_of_le hx (by linarith only [hR]))
  have hsmall : (∫ z in Set.Ioo 0 T ×ˢ originBall d R, euclideanSq (G z)) =
      ∫ z in Set.Ioo 0 T ×ˢ originBall d R, E z := by
    apply setIntegral_congr_fun (measurableSet_Ioo.prod (by
      unfold originBall euclideanNorm euclideanSq dot
      exact measurableSet_lt (by fun_prop) measurable_const))
    intro z hz
    simp only [E,hχr z.2 hz.2,one_pow,one_mul]
  rw [hsmall]
  exact (integral_mono_measure (Measure.restrict_mono hs le_rfl)
    (ae_of_all _ fun _ => mul_nonneg (sq_nonneg _) (euclideanSq_nonneg_fisher _)) hEi).trans hEb

/-- The zero-based integrated gradient has a uniform local coordinate L2
bound, with integrability established before its integral is estimated.
Source: `paper/main.tex:800–808,844–849`. -/
theorem exists_uniform_integrated_gradient_coordinate_energy_bound
    {d : ℕ} {K B T R : ℝ} (hK : 0 < K) (hT : 0 < T) (hR : 0 < R) :
    ∃ C : ℝ, ∀ (A : Coefficient d K) (g : Vec d → Vec d)
      (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
      IsSemigroupSolution A g u G →
      (∀ t, 0 < t → ∀ x, |u (t,x)| ≤ B) → ∀ j : Fin d,
      MemLp (fun x => ∫ t in Set.Ioo 0 T, G (t,x) j) 2
        (volume.restrict (originBall d R)) ∧
      (∫ x in originBall d R, (∫ t in Set.Ioo 0 T, G (t,x) j)^2) ≤ C := by
  obtain ⟨C,hC⟩ := exists_uniform_initial_gradient_energy_bound (B := B) hK hT hR
  refine ⟨T*C,?_⟩
  intro A g u G hsol hb j
  let μ := (volume : Measure (ℝ × Vec d)).restrict (Set.Ioo 0 T ×ˢ originBall d R)
  have hp : μ = (volume.restrict (Set.Ioo 0 T)).prod
      (volume.restrict (originBall d R)) := by
    simp only [μ,Measure.volume_eq_prod,Measure.prod_restrict]
  have hGm := (semigroup_initial_strip_data hsol hT hR).2.1
  have hj : MemLp (fun z : ℝ × Vec d => G z j) 2 μ :=
    (semigroup_initial_strip_memLp hK hsol hb hT hR).2.mono'
      ((continuous_apply j).comp_aestronglyMeasurable hGm)
      (ae_of_all _ fun z => by
        rw [Real.norm_eq_abs]
        exact Regeneration.coordinate_abs_le_euclideanNorm (G z) j)
  have hsq : Integrable (fun z => (G z j)^2) μ := hj.integrable_sq
  have hsqG := semigroup_gradient_energy_integrable_through_zero hK hsol hb hT hR
  have hle : (∫ z, (G z j)^2 ∂μ) ≤ C := by
    apply le_trans (integral_mono_ae hsq hsqG (ae_of_all _ fun z => ?_)) (hC A g u G hsol hb)
    have hh := pow_le_pow_left₀ (abs_nonneg _) (Regeneration.coordinate_abs_le_euclideanNorm (G z) j) 2
    simpa only [sq_abs,euclideanNorm,Real.sq_sqrt (euclideanSq_nonneg_fisher _)] using hh
  rw [hp] at hj
  have ht := time_integral_memLp_two (volume.restrict (originBall d R)) hT.le hj
  refine ⟨ht.1,?_⟩
  have he := ht.2
  rw [← hp] at he
  simp only [Real.norm_eq_abs,sq_abs] at he
  exact he.trans (mul_le_mul_of_nonneg_left hle hT.le)

end EinsteinRelation.Correctors
