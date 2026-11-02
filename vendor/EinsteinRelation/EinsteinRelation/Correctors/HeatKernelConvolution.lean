import EinsteinRelation.Correctors.HeatTransferBands
import EinsteinRelation.Correctors.HeatSmoothingContraction
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Heat smoothing of compact spatial kernels

The deterministic kernel identity underlying `paper/main.tex:1018–1031`.
The convolution uses `p_t(x-y)`; the heat kernel is even.
-/

open MeasureTheory Filter
open scoped Topology

noncomputable section
namespace EinsteinRelation.Correctors
variable {d : ℕ}

/-- Spatial continuity of the heat kernel, including the algebraic extension to all times. -/
theorem continuous_euclideanHeatKernel (t : ℝ) :
    Continuous (euclideanHeatKernel (d := d) t) := by
  unfold euclideanHeatKernel euclideanSq dot
  fun_prop

/-- Nonnegativity of the Euclidean heat kernel. -/
theorem euclideanHeatKernel_nonneg {t : ℝ} (ht : 0 ≤ t) (x : Vec d) :
    0 ≤ euclideanHeatKernel t x := by
  exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.exp_pos _).le

/-- Product representation of the Euclidean heat kernel. -/
theorem euclideanHeatKernel_eq_prod (t : ℝ) (z : Vec d) :
    euclideanHeatKernel t z =
      (4 * Real.pi * t) ^ (-(d : ℝ) / 2) * ∏ i, Real.exp (-(z i * z i) / (4 * t)) := by
  unfold euclideanHeatKernel
  rw [← Real.exp_sum]
  congr 2
  simp only [euclideanSq, dot, neg_div, Finset.sum_div, Finset.sum_neg_distrib]

/-- Absolute integrability of the heat kernel at positive times. -/
theorem integrable_euclideanHeatKernel {t : ℝ} (ht : 0 < t) :
    Integrable (euclideanHeatKernel (d := d) t) := by
  have hg : Integrable (fun x : ℝ => Real.exp (-(x * x) / (4 * t))) := by
    convert integrable_exp_neg_mul_sq (b := 1 / (4 * t)) (by positivity) using 1
    ext x
    congr 1
    ring
  have hp : Integrable (fun z : Vec d => ∏ i, Real.exp (-(z i * z i) / (4 * t))) := by
    rw [volume_pi]
    exact Integrable.fintype_prod (fun _ => hg)
  convert hp.const_mul ((4 * Real.pi * t) ^ (-(d : ℝ) / 2)) using 1
  ext z
  exact euclideanHeatKernel_eq_prod t z

/-- Normalization of the Euclidean heat kernel. -/
theorem integral_euclideanHeatKernel {t : ℝ} (ht : 0 < t) :
    ∫ z : Vec d, euclideanHeatKernel t z = 1 := by
  have hg : ∫ x : ℝ, Real.exp (-(x * x) / (4 * t)) = Real.sqrt (4 * Real.pi * t) := by
    convert integral_gaussian (1 / (4 * t)) using 1
    · congr 1
      ext x
      congr 1
      ring
    · congr 1
      field_simp
  simp only [euclideanHeatKernel_eq_prod]
  rw [integral_const_mul, integral_fintype_prod_volume_eq_prod
    (fun (_ : Fin d) (x : ℝ) => Real.exp (-(x * x) / (4 * t)))]
  simp only [hg, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hx : 0 < 4 * Real.pi * t := by positivity
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hx.le,
    ← Real.rpow_add hx, show -(d : ℝ) / 2 + 1 / 2 * (d : ℝ) = 0 by ring,
    Real.rpow_zero]

/-- Evenness fixes the reflection convention in horizontal convolution. -/
theorem euclideanHeatKernel_neg (t : ℝ) (x : Vec d) :
    euclideanHeatKernel t (-x) = euclideanHeatKernel t x := by
  simp [euclideanHeatKernel, euclideanSq, dot]

/-- Heat smoothing of a spatial kernel, with its actual initial value at time zero
(`paper/main.tex:1018–1022`). -/
def heatKernelConvolution (t : ℝ) (K : Vec d → ℝ) (y : Vec d) : ℝ :=
  if t = 0 then K y else ∫ x, K x * euclideanHeatKernel t (x - y)

/-- Gaussian scaling in the spatial variable. -/
theorem euclideanHeatKernel_sqrt_smul {t : ℝ} (ht : 0 < t) (z : Vec d) :
    euclideanHeatKernel t (Real.sqrt t • z) =
      (Real.sqrt t ^ d)⁻¹ * euclideanHeatKernel 1 z := by
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have he : euclideanSq (Real.sqrt t • z) = t * euclideanSq z := by
    simp only [euclideanSq, dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    nlinarith [Real.sq_sqrt ht.le]
  have hp : (4 * Real.pi * t) ^ (-(d : ℝ) / 2) =
      (Real.sqrt t ^ d)⁻¹ * (4 * Real.pi) ^ (-(d : ℝ) / 2) := by
    rw [Real.mul_rpow (by positivity) ht.le, Real.sqrt_eq_rpow,
      ← Real.rpow_natCast, ← Real.rpow_mul ht.le, ← Real.rpow_neg ht.le]
    rw [show -(1 / 2 * (d : ℝ)) = -(d : ℝ) / 2 by ring]
    ring
  simp only [euclideanHeatKernel, he, mul_one]
  rw [hp, show -(t * euclideanSq z) / (4 * t) = -(euclideanSq z) / 4 by field_simp]
  ring

/-- A fixed Gaussian measure represents smoothing at every positive time. This change of
variables is also the domination used for the initial-time limit. -/
theorem heatKernelConvolution_eq_scaled {t : ℝ} (ht : 0 < t) (K : Vec d → ℝ) (y : Vec d) :
    heatKernelConvolution t K y =
      ∫ z, euclideanHeatKernel 1 z * K (Real.sqrt t • z + y) := by
  rw [heatKernelConvolution, if_neg ht.ne']
  have htrans := integral_add_right_eq_self (μ := (volume : Measure (Vec d))) (fun x : Vec d =>
    K x * euclideanHeatKernel t (x - y)) y
  simp only [add_sub_cancel_right] at htrans
  rw [← htrans]
  have hscale := Measure.integral_comp_smul (volume : Measure (Vec d))
    (fun x => K (x + y) * euclideanHeatKernel t x) (Real.sqrt t)
  simp only [Module.finrank_pi, Fintype.card_fin, smul_eq_mul] at hscale
  rw [abs_of_pos (inv_pos.2 (pow_pos (Real.sqrt_pos.2 ht) d))] at hscale
  simp_rw [euclideanHeatKernel_sqrt_smul ht] at hscale
  rw [show (fun x => K (Real.sqrt t • x + y) *
      ((Real.sqrt t ^ d)⁻¹ * euclideanHeatKernel 1 x)) =
    fun x => (Real.sqrt t ^ d)⁻¹ *
      (euclideanHeatKernel 1 x * K (Real.sqrt t • x + y)) by funext x; ring,
    integral_const_mul] at hscale
  exact (mul_left_cancel₀ (inv_ne_zero (ne_of_gt (pow_pos (Real.sqrt_pos.2 ht) d))) hscale).symm

/-- Smoothing of a continuous compact kernel converges to its initial value at each point.
This proves the initial-time passage in `paper/main.tex:1018–1022` by dominated convergence. -/
theorem tendsto_heatKernelConvolution_zero {K : Vec d → ℝ}
    (hK : Continuous K) (hKc : HasCompactSupport K) (y : Vec d) :
    Tendsto (fun t => heatKernelConvolution t K y) (𝓝[>] 0) (𝓝 (K y)) := by
  obtain ⟨B, hB⟩ := hKc.exists_bound_of_continuous hK
  have hdom := tendsto_integral_filter_of_dominated_convergence
    (μ := (volume : Measure (Vec d))) (l := 𝓝[>] (0 : ℝ))
    (F := fun t z => euclideanHeatKernel 1 z * K (Real.sqrt t • z + y))
    (f := fun z => euclideanHeatKernel 1 z * K y)
    (fun z => euclideanHeatKernel 1 z * B)
    (Eventually.of_forall fun t => ((continuous_euclideanHeatKernel 1).mul
      (hK.comp (by fun_prop : Continuous fun z : Vec d => Real.sqrt t • z + y))).aestronglyMeasurable)
    (Eventually.of_forall fun t => ae_of_all _ fun z => by
      rw [norm_mul, Real.norm_of_nonneg (euclideanHeatKernel_nonneg zero_le_one _)]
      exact mul_le_mul_of_nonneg_left (hB _) (euclideanHeatKernel_nonneg zero_le_one _))
    ((integrable_euclideanHeatKernel (d := d) zero_lt_one).mul_const B)
    (ae_of_all _ fun z => by
      have ht : Tendsto (fun t : ℝ => Real.sqrt t • z + y) (𝓝[>] 0) (𝓝 y) := by
        have h0 : Tendsto (fun t : ℝ => Real.sqrt t) (𝓝[>] 0) (𝓝 0) := by
          simpa only [Real.sqrt_zero] using
            (Real.continuous_sqrt.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
        simpa only [zero_smul, zero_add] using (h0.smul_const z).add_const y
      exact tendsto_const_nhds.mul (hK.continuousAt.tendsto.comp ht))
  simp only [integral_mul_const, integral_euclideanHeatKernel zero_lt_one, one_mul] at hdom
  exact hdom.congr' (eventually_mem_nhdsWithin.mono fun _ ht =>
    (heatKernelConvolution_eq_scaled ht K y).symm)

/-- The fixed Gaussian representation also holds at zero for continuous compact kernels. -/
theorem heatKernelConvolution_eq_scaled_nonneg {t : ℝ} (ht : 0 ≤ t)
    (K : Vec d → ℝ) (y : Vec d) :
    heatKernelConvolution t K y =
      ∫ z, euclideanHeatKernel 1 z * K (Real.sqrt t • z + y) := by
  rcases ht.eq_or_lt with rfl | ht
  · simp [heatKernelConvolution, integral_mul_const, integral_euclideanHeatKernel zero_lt_one]
  · exact heatKernelConvolution_eq_scaled ht K y

/-- Continuity in time of a smoothed compact continuous kernel, up to the initial time. -/
theorem continuousOn_heatKernelConvolution {K : Vec d → ℝ}
    (hK : Continuous K) (hKc : HasCompactSupport K) (y : Vec d) :
    ContinuousOn (fun t => heatKernelConvolution t K y) (Set.Ici 0) := by
  obtain ⟨B, hB⟩ := hKc.exists_bound_of_continuous hK
  have hc : Continuous (fun t : ℝ =>
      ∫ z : Vec d, euclideanHeatKernel 1 z * K (Real.sqrt t • z + y)) := by
    apply continuous_of_dominated (bound := fun z => euclideanHeatKernel 1 z * B)
    · exact fun t => ((continuous_euclideanHeatKernel 1).mul
        (hK.comp (by fun_prop : Continuous fun z : Vec d => Real.sqrt t • z + y))).aestronglyMeasurable
    · exact fun t => ae_of_all _ fun z => by
        rw [norm_mul, Real.norm_of_nonneg (euclideanHeatKernel_nonneg zero_le_one _)]
        exact mul_le_mul_of_nonneg_left (hB _) (euclideanHeatKernel_nonneg zero_le_one _)
    · exact (integrable_euclideanHeatKernel (d := d) zero_lt_one).mul_const B
    · exact ae_of_all _ fun z => continuous_const.mul
        (hK.comp (by fun_prop : Continuous fun t : ℝ => Real.sqrt t • z + y))
  exact hc.continuousOn.congr fun t ht => heatKernelConvolution_eq_scaled_nonneg ht K y

/-- Translation commutes with the coordinate Laplacian. -/
theorem coordLaplacian_comp_sub (φ : Vec d → ℝ) (y x : Vec d) :
    coordLaplacian (fun z => φ (z - y)) x = coordLaplacian φ (x - y) := by
  unfold coordLaplacian
  apply Finset.sum_congr rfl
  intro i _
  simp_rw [fderiv_comp_sub]
  exact congrArg (fun A : Vec d →L[ℝ] ℝ => A (unitVector i))
    (fderiv_comp_sub (f := fun z => fderiv ℝ φ z (unitVector i)) y)

/-- The Gaussian is twice continuously differentiable in space. -/
theorem contDiff_two_euclideanHeatKernel (t : ℝ) :
    ContDiff ℝ 2 (euclideanHeatKernel (d := d) t) := by
  unfold euclideanHeatKernel euclideanSq dot
  fun_prop

/-- Joint continuity of the heat-kernel time derivative away from time zero. -/
theorem continuousOn_coordLaplacian_heatKernel :
    ContinuousOn (fun p : ℝ × Vec d => coordLaplacian (euclideanHeatKernel p.1) p.2)
      (Set.Ioi 0 ×ˢ Set.univ) := by
  simp_rw [coordLaplacian_euclideanHeatKernel]
  intro p hp
  apply ContinuousAt.continuousWithinAt
  have hp1 : 0 < p.1 := hp.1
  have ht : p.1 ≠ 0 := ne_of_gt hp1
  have hsq : Continuous (fun q : ℝ × Vec d => euclideanSq q.2) := by
    unfold euclideanSq dot
    fun_prop
  have hlin : Continuous (fun q : ℝ × Vec d => 4 * Real.pi * q.1) := by fun_prop
  have h4 : 4 * Real.pi * p.1 ≠ 0 := (mul_pos (mul_pos (by norm_num) Real.pi_pos) hp1).ne'
  have h4' : 4 * p.1 ≠ 0 := (mul_pos (by norm_num) hp1).ne'
  have hA : ContinuousAt (fun q : ℝ × Vec d => (4 * Real.pi * q.1) ^ (-(d : ℝ) / 2)) p :=
    hlin.continuousAt.rpow_const (Or.inl h4)
  have hden : ContinuousAt (fun q : ℝ × Vec d => -(euclideanSq q.2) / (4 * q.1)) p :=
    hsq.neg.continuousAt.div (by fun_prop) h4'
  have hB : ContinuousAt (fun q : ℝ × Vec d => Real.exp (-(euclideanSq q.2) / (4 * q.1))) p :=
    Real.continuous_exp.continuousAt.comp hden
  have hc : ContinuousAt (fun q : ℝ × Vec d => euclideanHeatKernel q.1 q.2) p := hA.mul hB
  have hs2 : ContinuousAt (fun q : ℝ × Vec d =>
      euclideanSq q.2 / (4 * q.1 ^ 2) - (d : ℝ) / (2 * q.1)) p :=
    (hsq.continuousAt.div (by fun_prop) (mul_ne_zero (by norm_num) (pow_ne_zero 2 ht))).sub
      (continuousAt_const.div (by fun_prop) (mul_ne_zero two_ne_zero ht))
  exact hc.mul hs2

/-- Differentiation under the compact spatial integral, followed by two integrations by
parts, gives the heat equation on a compact kernel (`paper/main.tex:1018–1022`). -/
theorem hasDerivAt_heatKernelConvolution {K : Vec d → ℝ} (hK : ContDiff ℝ 2 K)
    (hKc : HasCompactSupport K) (y : Vec d) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => heatKernelConvolution s K y)
      (heatKernelConvolution t (coordLaplacian K) y) t := by
  have he : 0 < t / 2 := by positivity
  have hsub : Continuous (fun x : Vec d => x - y) := by fun_prop
  let S : Set (ℝ × Vec d) := Set.Icc (t / 2) (t + t / 2) ×ˢ tsupport K
  have hS : IsCompact S := isCompact_Icc.prod hKc
  have hc : ContinuousOn (fun p : ℝ × Vec d =>
      coordLaplacian (euclideanHeatKernel p.1) (p.2 - y)) S := by
    apply continuousOn_coordLaplacian_heatKernel.comp
      (by fun_prop : Continuous fun p : ℝ × Vec d => (p.1, p.2 - y)).continuousOn
    intro p hp
    exact ⟨lt_of_lt_of_le he hp.1.1, Set.mem_univ _⟩
  obtain ⟨B, hB⟩ := hS.exists_bound_of_continuousOn hc
  have hdiff := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := (volume : Measure (Vec d))) (x₀ := t) (s := Metric.ball t (t / 2))
    (F := fun s x => K x * euclideanHeatKernel s (x - y))
    (F' := fun s x => K x * coordLaplacian (euclideanHeatKernel s) (x - y))
    (bound := fun x => ‖K x‖ * B) (Metric.ball_mem_nhds t he)
    (Eventually.of_forall fun s => (hK.continuous.mul
      ((continuous_euclideanHeatKernel s).comp hsub)).aestronglyMeasurable)
    (integrable_mul_of_compact_support hK.continuous hKc
      ((continuous_euclideanHeatKernel t).comp hsub))
    (hK.continuous.mul ((continuous_coordLaplacian (contDiff_two_euclideanHeatKernel t)).comp
      hsub)).aestronglyMeasurable
    (ae_of_all _ fun x s hs => by
      rw [norm_mul]
      by_cases hx : x ∈ tsupport K
      · apply mul_le_mul_of_nonneg_left (hB (s, x) ⟨?_, hx⟩) (norm_nonneg _)
        rw [Metric.mem_ball, Real.dist_eq] at hs
        constructor <;> linarith [(abs_lt.mp hs).1, (abs_lt.mp hs).2]
      · simp [image_eq_zero_of_notMem_tsupport hx])
    ((hK.continuous.integrable_of_hasCompactSupport hKc).norm.mul_const B)
    (ae_of_all _ fun x s hs => by
      have hspos : 0 < s := by
        rw [Metric.mem_ball, Real.dist_eq] at hs
        linarith [(abs_lt.mp hs).1]
      exact (hasDerivAt_euclideanHeatKernel_heat (x - y) hspos).const_mul (K x))
  have hibp : (∫ x, K x * coordLaplacian (euclideanHeatKernel t) (x - y)) =
      ∫ x, coordLaplacian K x * euclideanHeatKernel t (x - y) := by
    simp_rw [← coordLaplacian_comp_sub]
    exact integral_mul_coordLaplacian_eq hK hKc
      ((contDiff_two_euclideanHeatKernel t).comp
        (by fun_prop : ContDiff ℝ 2 fun x : Vec d => x - y))
  rw [hibp] at hdiff
  rw [heatKernelConvolution, if_neg ht.ne']
  apply hdiff.2.congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds ht.ne'] with s hs
  simp only [heatKernelConvolution, if_neg hs]

/-- The coordinate Laplacian preserves compact support. -/
theorem hasCompactSupport_coordLaplacian {K : Vec d → ℝ} (hKc : HasCompactSupport K) :
    HasCompactSupport (coordLaplacian K) := by
  unfold coordLaplacian
  have hh : ∀ (s : Finset (Fin d)), HasCompactSupport
      (fun x => ∑ i ∈ s, fderiv ℝ (fun y => fderiv ℝ K y (unitVector i)) x (unitVector i)) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      exact HasCompactSupport.zero
    | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      exact ((hKc.fderiv_apply ℝ (unitVector i)).fderiv_apply ℝ (unitVector i)).add ih
  simpa using hh Finset.univ

/-- The integrated heat identity for the actual spatial kernels, including time zero
(`paper/main.tex:1018–1022`). -/
theorem heatKernelConvolution_sub_initial {K : Vec d → ℝ} (hK : ContDiff ℝ 2 K)
    (hKc : HasCompactSupport K) (y : Vec d) {T : ℝ} (hT : 0 ≤ T) :
    heatKernelConvolution T K y - K y =
      ∫ t in (0 : ℝ)..T, heatKernelConvolution t (coordLaplacian K) y := by
  have hc := continuousOn_heatKernelConvolution hK.continuous hKc y
  have hlc := continuousOn_heatKernelConvolution (continuous_coordLaplacian hK)
    (hasCompactSupport_coordLaplacian hKc) y
  have hi := (hlc.mono (show Set.uIcc 0 T ⊆ Set.Ici 0 by
    rw [Set.uIcc_of_le hT]; exact fun _ hx => hx.1)).intervalIntegrable (μ := volume)
  have h0 : heatKernelConvolution 0 K y = K y := by simp [heatKernelConvolution]
  have h : (∫ t in (0 : ℝ)..T, heatKernelConvolution t (coordLaplacian K) y) =
      heatKernelConvolution T K y - heatKernelConvolution 0 K y :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT
      (hc.mono (fun _ hx => hx.1))
      (fun _ ht => hasDerivAt_heatKernelConvolution hK hKc y ht.1) hi
  rw [h0] at h
  exact h.symm

end EinsteinRelation.Correctors
