import EinsteinRelation.Correctors.AKMHeatKernelGaussianEnergy
import EinsteinRelation.Correctors.AKMHeatKernelPrescribedGradient
import EinsteinRelation.Correctors.GaussianWeightedProduct
import EinsteinRelation.Correctors.WeightedParameterIntegralL2
import EinsteinRelation.Correctors.ParabolicIntegral
import EinsteinRelation.Correctors.ParabolicSignedScaling
import EinsteinRelation.Correctors.EuclideanCoordinateCharacterization
import EinsteinRelation.Correctors.ScaledGaussianIntegrability
import EinsteinRelation.Correctors.AKMHeatKernelScalarInitialTrace

open MeasureTheory Filter
open scoped Topology
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- The bounded scalar-data evolution of the specified E.1 kernel is an
actual energy solution on every positive bounded cylinder. This constructs
the equation, rather than assuming it as part of a kernel representation.
Source: AKM E.1 (E.1), (E.7)–(E.8); `paper/main.tex:787–792,850`. -/
theorem akm_heatKernel_bounded_data_parabolic_evolution
    {d : ℕ} {K : ℝ} (hK : 0 < K) {A : Coefficient d K}
    {P : ℝ → Vec d → Vec d → ℝ}
    {X Y : ℝ → Vec d → Vec d → Vec d}
    {H : ℝ → Vec d → Vec d → Mat d} {C : ℝ → ℝ}
    (hP : HeatKernelProperties A P X Y H C)
    {f : Vec d → ℝ} (hf : Measurable f) {B : ℝ}
    (hB : 0 ≤ B) (hfb : ∀ y, |f y| ≤ B) :
    ∃ G : ℝ × Vec d → Vec d, Measurable G ∧
      ∀ a b R : ℝ, 0 < a → a < b → 0 < R →
        IsParabolicSolution A (Set.Ioo a b) (originBall d R)
          (fun z => ∫ y, P z.1 z.2 y*f y ∂volume) G := by
  classical
  obtain ⟨Z,hZm,hZsol,hZw⟩ := akm_heatKernel_exists_measurable_prescribed_gradient hK hP
  let p : ℝ × (Vec d × Vec d) → ℝ := fun z =>
    if 0 < z.1 then P z.1 z.2.1 z.2.2 else 0
  have hpm : Measurable p := by
    convert hP.1.measurable_piecewise (g := fun _ => (0 : ℝ)) continuousOn_const
      (measurableSet_Ioi.prod MeasurableSet.univ) using 1
    funext z
    change (if 0 < z.1 then P z.1 z.2.1 z.2.2 else 0) =
      (if z ∈ Set.Ioi 0 ×ˢ Set.univ then P z.1 z.2.1 z.2.2 else 0)
    simp only [Set.mem_prod,Set.mem_Ioi,Set.mem_univ,and_true]
  let u : Vec d → ℝ × Vec d → ℝ := fun y z => p (z.1,(z.2,y))*f y
  let V : Vec d → ℝ × Vec d → Vec d := fun y z => f y • Z z.1 z.2 y
  let G : ℝ × Vec d → Vec d := fun z j => ∫ y, V y z j ∂volume
  have hum : Measurable (fun z : Vec d × (ℝ × Vec d) => u z.1 z.2) :=
    (hpm.comp (measurable_snd.fst.prodMk (measurable_snd.snd.prodMk measurable_fst))).mul
      (hf.comp measurable_fst)
  have hVm : Measurable (fun z : Vec d × (ℝ × Vec d) => V z.1 z.2) :=
    (hf.comp measurable_fst).smul
      (hZm.comp (measurable_snd.fst.prodMk (measurable_snd.snd.prodMk measurable_fst)))
  have hGm : Measurable G := by
    apply measurable_pi_lambda
    intro j
    exact ((measurable_pi_apply j).comp hVm).stronglyMeasurable.integral_prod_left'.measurable
  refine ⟨G,hGm,?_⟩
  intro a b R ha hab hR
  let S := Set.Ioo a b ×ˢ originBall d R
  let ν : Measure (ℝ × Vec d) := volume.restrict S
  have hopen : IsOpen (originBall d R) := by
    unfold originBall euclideanNorm euclideanSq dot
    exact isOpen_lt (by fun_prop) continuous_const
  have hcomp := isCompact_closure_originBall d R
  letI : IsFiniteMeasure (volume.restrict (originBall d R)) :=
    isFiniteMeasure_restrict.mpr (ne_top_of_le_ne_top
      (hcomp.measure_ne_top (μ := volume)) (measure_mono subset_closure))
  letI : IsFiniteMeasure ν := by
    dsimp only [ν,S]
    rw [Measure.volume_eq_prod,← Measure.prod_restrict]
    infer_instance
  obtain ⟨D₁,κ₁,hD₁,hκ₁,he₁⟩ := akm_heatKernel_local_scalar_gaussian_energy hK hP ha hab hR
  obtain ⟨D₂,κ₂,hD₂,hκ₂,he₂⟩ := akm_heatKernel_local_solution_gradient_gaussian_energy hK hP hZsol ha hab hR
  let κ := min κ₁ κ₂
  have hκ : 0 < κ := lt_min hκ₁ hκ₂
  have hg := integrable_scaled_gaussian_origin (d := d) hκ
  let w : Vec d → ℝ := fun y => Real.exp (-κ*euclideanSq y)
  have hwm : Measurable w := by unfold w euclideanSq dot; fun_prop
  have hwp (y : Vec d) : 0 < w y := Real.exp_pos _
  have hpsol (y : Vec d) : IsFundamentalSolution A y
      (fun z => p (z.1,(z.2,y))) (fun z => Z z.1 z.2 y) := by
    apply fundamentalSolution_scalar_congr_positive (hZsol y)
    intro t ht x
    simp only [p,if_pos ht]
  have hsp (y : Vec d) : MemLp (fun z => p (z.1,(z.2,y))) 2 ν :=
    ((hpsol y).1 a b R ha hab hR).1
  have hpe (y : Vec d) : (∫ z, p (z.1,(z.2,y))^2 ∂ν) ≤
      D₁*Real.exp (-(2*κ)*euclideanSq y) := by
    calc
      _ = ∫ z in S, P z.1 z.2 y^2 := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod hopen.measurableSet)] with z hz
        simp only [p,if_pos (ha.trans hz.1.1)]
      _ ≤ D₁*Real.exp (-(2*κ₁)*euclideanSq y) := he₁ y
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ hD₁
        apply Real.exp_le_exp.mpr
        have hk : κ ≤ κ₁ := min_le_left _ _
        have hn := euclideanSq_nonneg_fisher y
        nlinarith
  have hpu := memLp_gaussian_weighted_product ν hκ hD₁ hB hg
    (hpm.comp (measurable_snd.fst.prodMk (measurable_snd.snd.prodMk measurable_fst)))
    hsp hpe hf hfb
  have huavg := memLp_two_integral_of_weighted_product volume ν hwm hg hwp hum hpu
  have hGj (j : Fin d) : MemLp (fun z => ∫ y, V y z j ∂volume) 2 ν ∧
      Integrable (fun z : Vec d × (ℝ × Vec d) => V z.1 z.2 j) (volume.prod ν) := by
    have hsec (y : Vec d) : MemLp (fun z => Z z.1 z.2 y j) 2 ν :=
      parabolicSolution_gradient_coordinate_memLp ((hZsol y).1 a b R ha hab hR) j
    have he (y : Vec d) : (∫ z, (Z z.1 z.2 y j)^2 ∂ν) ≤
        D₂*Real.exp (-(2*κ)*euclideanSq y) := by
      calc
        _ ≤ ∫ z, euclideanNorm (Z z.1 z.2 y)^2 ∂ν := by
          apply integral_mono_ae (hsec y).integrable_sq
            (((hZsol y).1 a b R ha hab hR).2.2.1.integrable_sq)
          filter_upwards with z
          simp only [euclideanNorm,Real.sq_sqrt (euclideanSq_nonneg_fisher _)]
          simpa only [pow_two] using Finset.single_le_sum
            (fun k (_ : k ∈ Finset.univ) => mul_self_nonneg (Z z.1 z.2 y k)) (Finset.mem_univ j)
        _ ≤ D₂*Real.exp (-(2*κ₂)*euclideanSq y) := he₂ y
        _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left _ hD₂
          apply Real.exp_le_exp.mpr
          have hk : κ ≤ κ₂ := min_le_right _ _
          have hn := euclideanSq_nonneg_fisher y
          nlinarith
    have hm : Measurable (fun z : Vec d × (ℝ × Vec d) => Z z.2.1 z.2.2 z.1 j) :=
      (measurable_pi_apply j).comp
        (hZm.comp (measurable_snd.fst.prodMk (measurable_snd.snd.prodMk measurable_fst)))
    have hprod := memLp_gaussian_weighted_product ν hκ hD₂ hB hg hm hsec he hf hfb
    apply memLp_two_integral_of_weighted_product volume ν hwm hg hwp
      ((measurable_pi_apply j).comp hVm)
    simpa only [Function.comp_apply,V,Pi.smul_apply,smul_eq_mul,mul_comm,w] using hprod
  have hG2 : MemLp (fun z => euclideanNorm (G z)) 2 ν := by
    have he := (memLp_euclidean_iff_coordinates ν
      (fun z => (WithLp.toLp 2 (G z) : EuclideanSpace ℝ (Fin d)))).mpr (fun j => (hGj j).1)
    simpa only [← TimeChange.euclideanNorm_eq_norm_toLp] using he.norm
  have hs (y : Vec d) : IsParabolicSolution A (Set.Ioo a b) (originBall d R) (u y) (V y) := by
    simpa only [u,V,mul_comm] using
      parabolicSolution_signed_const_mul ((hpsol y).1 a b R ha hab hR) (f y)
  have hw (y : Vec d) (t : ℝ) (ht : t ∈ Set.Ioo a b) :
      HasWeakGradient (originBall d R) (fun x => u y (t,x)) (fun x => V y (t,x)) := by
    have ht0 := ha.trans ht.1
    have hh := hasWeakGradient_const_mul
      (hasWeakGradient_mono (Set.subset_univ (originBall d R)) (hZw y t ht0)) (f y)
    simpa only [u,V,p,if_pos ht0,mul_comm] using hh
  have hsol := parabolicSolution_integral volume hK measurableSet_Ioo hopen u V hum hVm
    huavg.2 (fun j => (hGj j).2) huavg.1 hG2 hs hw
  apply parabolicSolution_congr_ae hopen hsol
  · filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod hopen.measurableSet)] with z hz
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun y => by simp only [u,p,if_pos (ha.trans hz.1.1)]
  · exact Filter.EventuallyEq.rfl

end EinsteinRelation.Correctors
