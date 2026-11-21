import EinsteinFull.Homogenization.HeatSelectedFluxPotential
import EinsteinFull.Homogenization.LocalL2LimitMeasurable
import EinsteinFull.Homogenization.HeatKernelThirdDerivative

/-!
# The heat formula for fields depending measurably on a parameter

The heat Hessian `∂ⱼ∂ᵢΦ_t` has integral zero, so the truncations of the heat formula (6.7) of
Armstrong, Kuusi and Mourrat, *Quantitative Stochastic Homogenization and Large-Scale
Regularity*, do not see constants, and large-time decay of the heat Hessian passes to constant
shifts. If the field depends jointly measurably on a parameter and the space variable, the
truncations of (6.7), the truncated potentials and their selected limits, the heat-selected flux
gradient and potential, are jointly measurable. The heat selection is unchanged by null-set
modifications of the field.
-/

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace EinsteinFull.Homogenization

open EinsteinRelation EinsteinRelation.Correctors EinsteinRelation.External.AKM
open EinsteinRelation.Correctors.HeatSelectedSkewMeaning

variable {d : ℕ}

section Constants

theorem integrable_heatGrad {t : ℝ} (ht : 0 < t) (i : Fin d) :
    Integrable (coordinateDerivative i (euclideanHeatKernel (d := d) t)) volume := by
  refine ((integrable_euclideanHeatKernel (d := d) (by positivity : 0 < 2 * t)).const_mul
    ((2 : ℝ) ^ ((d : ℝ) / 2) * (2 / Real.sqrt t))).mono'
    (contDiff_heatGrad t i).continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs]
  exact abs_heatGrad_le ht i z

theorem integrable_heatHessian {t : ℝ} (ht : 0 < t) (i j : Fin d) :
    Integrable (coordinateDerivative j (coordinateDerivative i
      (euclideanHeatKernel (d := d) t))) volume := by
  refine ((integrable_euclideanHeatKernel (d := d) (by positivity : 0 < 2 * t)).const_mul
    ((2 : ℝ) ^ ((d : ℝ) / 2) * (2 / t))).mono'
    (contDiff_heatHessian t i j).continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs]
  exact abs_heatHessian_le ht i j z

/-- The heat Hessian has integral zero. -/
theorem integral_heatHessian_eq_zero {t : ℝ} (ht : 0 < t) (i j : Fin d) :
    ∫ z, coordinateDerivative j (coordinateDerivative i (euclideanHeatKernel (d := d) t)) z =
      0 := by
  have hΨ := (contDiff_heatGrad (d := d) t i).differentiable (by simp)
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    (f := fun _ : Vec d => (1 : ℝ)) (g := coordinateDerivative i (euclideanHeatKernel t))
    (v := unitVector j) (by simp) (by simp only [one_mul]; exact integrable_heatHessian ht i j)
    (by simp only [one_mul]; exact integrable_heatGrad ht i) (fun x _ => differentiableAt_const _)
    (fun x _ => hΨ x)
  simpa [coordinateDerivative] using h

/-- The heat Hessian does not see constants. -/
theorem heatHessianConv_add_const {t : ℝ} (ht : 0 < t) (i j : Fin d) {f : Vec d → ℝ}
    (x : Vec d) (hf : Integrable (fun y => coordinateDerivative j (coordinateDerivative i
      (euclideanHeatKernel t)) (x - y) * f y) volume) (c : ℝ) :
    heatHessianConv t i j (fun y => f y + c) x = heatHessianConv t i j f x := by
  unfold heatHessianConv
  have hK := (integrable_heatHessian (d := d) ht i j).comp_sub_left x
  simp_rw [mul_add]
  rw [integral_add hf (hK.mul_const c), integral_mul_const,
    integral_sub_left_eq_self (fun z => coordinateDerivative j (coordinateDerivative i
      (euclideanHeatKernel (d := d) t)) z) (μ := volume) x, integral_heatHessian_eq_zero ht,
    zero_mul, add_zero]

/-- Large-time decay of the heat Hessian passes to constant shifts. -/
theorem HasHeatHessianDecay.add_const {f : Vec d → ℝ} {i j : Fin d}
    (hdec : HasHeatHessianDecay f i j) (hmom : HasGaussianMoments f) (hfm : Measurable f)
    (c : ℝ) : HasHeatHessianDecay (fun y => f y + c) i j := by
  obtain ⟨A, κ, T₀, hA, hκ, hT₀, h⟩ := hdec
  refine ⟨A, κ, T₀, hA, hκ, hT₀, fun t ht x hx => ?_⟩
  have ht0 : 0 < t := lt_of_lt_of_le hT₀ ht
  rw [heatHessianConv_add_const ht0 i j x (hmom.integrable_heatHessian_mul ht0 i j hfm x) c]
  exact h t ht x hx

end Constants

section Congruence

/-- Spatial null-set changes of the field preserve the heat selection. -/
theorem isHeatSelectedFluxGradient_congr_ae {g h : Vec d → Vec d}
    {G : Fin d → Fin d → Vec d → Vec d} (hgh : g =ᵐ[volume] h)
    (hG : IsHeatSelectedFluxGradient g G) : IsHeatSelectedFluxGradient h G := by
  have hdensity (t : ℝ) (j k l : Fin d) (x : Vec d) :
      akmHeatGradientDensity g t j k l x =ᵐ[volume] akmHeatGradientDensity h t j k l x := by
    filter_upwards [hgh] with y hy
    simp only [akmHeatGradientDensity, hy]
  have hspace (t : ℝ) (j k l : Fin d) (x : Vec d) :
      akmHeatGradientSpaceIntegral g t j k l x = akmHeatGradientSpaceIntegral h t j k l x :=
    integral_congr_ae (hdensity t j k l x)
  have htrunc (m n : ℕ) (j k l : Fin d) :
      iteratedAKMHeatGradientTruncation g m n j k l =
        iteratedAKMHeatGradientTruncation h m n j k l := by
    funext x
    simp only [iteratedAKMHeatGradientTruncation, hspace]
  intro j k l R
  have hsel := hG j k l R
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro m n
    filter_upwards [hsel.1 m n] with x hx
    refine ⟨?_, ?_⟩
    · filter_upwards [hx.1] with t ht
      exact ht.congr (hdensity t j k l x)
    · simpa only [hspace] using hx.2
  · simpa only [htrunc] using hsel.2.1
  · exact hsel.2.2.1
  · simpa only [htrunc] using hsel.2.2.2

end Congruence

section Parameter

variable {Ω : Type*} [MeasurableSpace Ω] {G : Ω → Vec d → Vec d}

theorem akmHeatGradientDensity_eq_ite (g : Vec d → Vec d) (t : ℝ) (j k l : Fin d)
    (x y : Vec d) :
    akmHeatGradientDensity g t j k l x y =
      if 0 < t then g y k * heatHessianKernel t j l (x - y) -
        g y j * heatHessianKernel t k l (x - y) else 0 := by
  by_cases ht : 0 < t
  · simp only [ht, ↓reduceIte]
    rw [akmHeatGradientDensity_eq_mixedHessian g t ht, heatHessian_eq ht, heatHessian_eq ht]
    rfl
  · simp [akmHeatGradientDensity, ht]

theorem measurable_akmHeatGradientDensity_param
    (hG : ∀ k, Measurable (fun p : Ω × Vec d => G p.1 p.2 k)) (j k l : Fin d) :
    Measurable (fun q : ((Ω × Vec d) × ℝ) × Vec d =>
      akmHeatGradientDensity (G q.1.1.1) q.1.2 j k l q.1.1.2 q.2) := by
  simp_rw [akmHeatGradientDensity_eq_ite]
  have hk (k : Fin d) : Measurable (fun q : ((Ω × Vec d) × ℝ) × Vec d => G q.1.1.1 q.2 k) :=
    (hG k).comp ((measurable_fst.comp (measurable_fst.comp measurable_fst)).prodMk measurable_snd)
  have hker (i j : Fin d) : Measurable (fun q : ((Ω × Vec d) × ℝ) × Vec d =>
      heatHessianKernel q.1.2 i j (q.1.1.2 - q.2)) :=
    (measurable_heatHessianKernel i j).comp ((measurable_snd.comp measurable_fst).prodMk
      ((measurable_snd.comp (measurable_fst.comp measurable_fst)).sub measurable_snd))
  refine Measurable.ite ?_ (((hk k).mul (hker j l)).sub ((hk j).mul (hker k l))) measurable_const
  exact measurableSet_lt measurable_const (measurable_snd.comp measurable_fst)

/-- The truncations of (6.7) are jointly measurable in the parameter and the space variable. -/
theorem measurable_iteratedAKMHeatGradientTruncation_param
    (hG : ∀ k, Measurable (fun p : Ω × Vec d => G p.1 p.2 k)) (m n : ℕ) (j k l : Fin d) :
    Measurable (fun p : Ω × Vec d =>
      iteratedAKMHeatGradientTruncation (G p.1) m n j k l p.2) := by
  have h1 : StronglyMeasurable (fun q : (Ω × Vec d) × ℝ =>
      akmHeatGradientSpaceIntegral (G q.1.1) q.2 j k l q.1.2) :=
    (measurable_akmHeatGradientDensity_param hG j k l).stronglyMeasurable.integral_prod_right'
  exact (h1.integral_prod_right' (ν := volume.restrict (iteratedHeatTimeWindow m n))).measurable

theorem measurable_heatGradWindow_param {f : Ω → Vec d → ℝ}
    (hf : Measurable (fun p : Ω × Vec d => f p.1 p.2)) (ε₁ ε₂ : ℝ) (i : Fin d) :
    Measurable (fun p : Ω × Vec d => heatGradWindow ε₁ ε₂ i (f p.1) p.2) := by
  have h0 : Measurable (fun q : ((Ω × Vec d) × ℝ) × Vec d =>
      heatGradKernel q.1.2 i (q.1.1.2 - q.2) * f q.1.1.1 q.2) :=
    ((measurable_heatGradKernel i).comp ((measurable_snd.comp measurable_fst).prodMk
      ((measurable_snd.comp (measurable_fst.comp measurable_fst)).sub measurable_snd))).mul
      (hf.comp ((measurable_fst.comp (measurable_fst.comp measurable_fst)).prodMk measurable_snd))
  have h1 := h0.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure (Vec d)))
  have h2 := h1.integral_prod_right' (ν := volume.restrict (Icc ε₁ ε₂))
  have heq : (fun p : Ω × Vec d => heatGradWindow ε₁ ε₂ i (f p.1) p.2) =
      fun p => ∫ t in Icc ε₁ ε₂, ∫ y, heatGradKernel t i (p.2 - y) * f p.1 y := by
    funext p
    simp only [heatGradWindow, heatGradConv_eq_kernel]
  rw [heq]
  exact h2.measurable

theorem measurable_heatPotentialTruncation_param
    (hG : ∀ k, Measurable (fun p : Ω × Vec d => G p.1 p.2 k)) (q : ℕ) (j k : Fin d) :
    Measurable (fun p : Ω × Vec d => heatPotentialTruncation (G p.1) q j k p.2) :=
  (measurable_heatGradWindow_param (f := fun ω y => G ω y k) (hG k) _ _ j).sub
    (measurable_heatGradWindow_param (f := fun ω y => G ω y j) (hG j) _ _ k)

theorem measurable_centeredHeatPotential_param
    (hG : ∀ k, Measurable (fun p : Ω × Vec d => G p.1 p.2 k)) (q : ℕ) (j k : Fin d) :
    Measurable (fun p : Ω × Vec d => centeredHeatPotential (G p.1) q j k p.2) := by
  have h := measurable_heatPotentialTruncation_param hG q j k
  have havg : Measurable (fun ω : Ω => ⨍ y in ball (0 : Vec d) 1,
      heatPotentialTruncation (G ω) q j k y) := by
    simp_rw [setAverage_eq, smul_eq_mul]
    exact measurable_const.mul
      (h.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (ball 0 1))).measurable
  exact h.sub (havg.comp measurable_fst)

/-- **The heat-selected flux gradient is jointly measurable in the parameter.** -/
theorem measurable_heatSelectedGradient_param
    (hG : ∀ k, Measurable (fun p : Ω × Vec d => G p.1 p.2 k)) (j k : Fin d) :
    Measurable (fun p : Ω × Vec d => heatSelectedGradient (G p.1) j k p.2) := by
  refine measurable_pi_iff.mpr fun l => ?_
  exact measurable_locL2Limit_param (D := fun ω p x =>
    iteratedAKMHeatGradientTruncation (G ω) p p j k l x)
    fun p => measurable_iteratedAKMHeatGradientTruncation_param hG p p j k l

/-- A matrix-valued map with measurable entries is measurable for the Borel sigma algebra. -/
theorem measurable_borel_mat {α : Type*} [MeasurableSpace α] {f : α → Mat d}
    (h : @Measurable α (Fin d → Fin d → ℝ) _ MeasurableSpace.pi f) :
    @Measurable α (Mat d) _ (borel (Mat d)) f := by
  rw [(Pi.borelSpace (X := fun _ : Fin d => Fin d → ℝ)).measurable_eq] at h
  exact h

/-- **The heat-selected flux potential is jointly measurable in the parameter.** -/
theorem measurable_heatSelectedPotential_param
    (hG : ∀ k, Measurable (fun p : Ω × Vec d => G p.1 p.2 k)) :
    @Measurable (Ω × Vec d) (Mat d) _ (borel (Mat d))
      (fun p : Ω × Vec d => heatSelectedPotential (G p.1) p.2) := by
  have h : Measurable (fun p : Ω × Vec d =>
      (fun j k => heatSelectedPotential (G p.1) p.2 j k : Fin d → Fin d → ℝ)) := by
    refine measurable_pi_iff.mpr fun j => measurable_pi_iff.mpr fun k => ?_
    simp_rw [heatSelectedPotential_apply]
    exact measurable_locL2Limit_param (D := fun ω p x => centeredHeatPotential (G ω) p j k x)
      fun p => measurable_centeredHeatPotential_param hG p j k
  exact measurable_borel_mat h

end Parameter

end EinsteinFull.Homogenization
