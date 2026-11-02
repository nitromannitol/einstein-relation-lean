import EinsteinFull.Blueprint.G3.node_e_u3A_sublinear_u2D_pair
import EinsteinFull.Calculus.C3SublinearPairSupport
import EinsteinRelation.Correctors.AKMCenteredFluxTransfer
import EinsteinRelation.Correctors.CurlPoissonDivergence
import EinsteinRelation.Correctors.HeatGradientConvolution
import EinsteinRelation.Correctors.HeatGradientTranslation
import EinsteinRelation.Correctors.SpatialBallTranslation
import EinsteinRelation.Correctors.PairedParabolicEquation
import EinsteinRelation.Correctors.SpatialWeakDilation
import EinsteinRelation.Correctors.SpatialWeakCongruence
import EinsteinRelation.Calculus.ZeroWeakGradientConstant
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinRelation.External.AKM
open EinsteinRelation.Correctors
open EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinRelation.Correctors.HeatSelectedSkewMeaning

private theorem c6_hasWeakGradient_const_mul {d : ℕ}
    {u : Vec d → ℝ} {G : Vec d → Vec d}
    (hu : HasWeakGradient Set.univ u G) (c : ℝ) :
    HasWeakGradient Set.univ (fun x => c * u x) (fun x => c • G x) := by
  intro j
  refine ⟨fun x hx => ((hu j).1 x hx).smul c,
    fun x hx => ((hu j).2.1 x hx).smul c, ?_⟩
  intro ψ hψ
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]
  rw [(hu j).2.2 ψ hψ, mul_neg]

/-- The literal heat formula is skew before its two cutoff limits are taken. -/
theorem c6_heatTruncation_swap {d : ℕ} (g : Vec d → Vec d)
    (m n : ℕ) (j k l : Fin d) (x : Vec d) :
    iteratedAKMHeatGradientTruncation g m n k j l x =
      -iteratedAKMHeatGradientTruncation g m n j k l x := by
  have hdensity (t : ℝ) (y : Vec d) :
      akmHeatGradientDensity g t k j l x y = -akmHeatGradientDensity g t j k l x y := by
    unfold akmHeatGradientDensity
    split
    · ring
    · exact (neg_zero).symm
  have hspace (t : ℝ) : akmHeatGradientSpaceIntegral g t k j l x =
      -akmHeatGradientSpaceIntegral g t j k l x := by
    simp only [akmHeatGradientSpaceIntegral, hdensity, integral_neg]
  simp only [iteratedAKMHeatGradientTruncation, hspace, integral_neg]

/-- Uniqueness of the local L² heat limit gives spatial antisymmetry. -/
theorem c6_heatSelectedFluxGradient_ae_swap {d : ℕ} {g : Vec d → Vec d}
    {G : Fin d → Fin d → Vec d → Vec d} (h : IsHeatSelectedFluxGradient g G)
    (j k l : Fin d) :
    (fun x => G k j x l) =ᵐ[volume] (fun x => -G j k x l) := by
  have hlocal (R : ℕ) :
      (fun x => G k j x l) =ᵐ[volume.restrict (ball 0 ((R : ℝ) + 1))]
        (fun x => -G j k x l) := by
    obtain ⟨_, hT, hG, hlim⟩ := h k j l R
    obtain ⟨_, _, hG', hlim'⟩ := h j k l R
    have hlimneg : Tendsto (fun mn : ℕ × ℕ => eLpNorm
        (fun x => iteratedAKMHeatGradientTruncation g mn.1 mn.2 k j l x -
          (-G j k x l)) 2 (volume.restrict (ball 0 ((R : ℝ) + 1))))
        atTop (𝓝 0) := by
      convert hlim' using 1
      ext mn
      rw [show (fun x => iteratedAKMHeatGradientTruncation g mn.1 mn.2 k j l x -
          (-G j k x l)) = -(fun x =>
            iteratedAKMHeatGradientTruncation g mn.1 mn.2 j k l x - G j k x l) by
        funext x
        rw [c6_heatTruncation_swap]
        simp only [Pi.neg_apply]
        ring]
      exact eLpNorm_neg _ _ _
    exact tendstoInMeasure_ae_unique
      (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0) hlim)
      (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0) hlimneg)
  have hcover : (⋃ R : ℕ, ball (0 : Vec d) ((R : ℝ) + 1)) = Set.univ := by
    apply Set.iUnion_eq_univ_iff.mpr
    intro x
    obtain ⟨N, hN⟩ := exists_nat_gt (euclideanNorm x)
    refine ⟨N, ?_⟩
    change euclideanNorm (x - 0) < (N : ℝ) + 1
    rw [sub_zero]
    linarith
  have hu := (ae_restrict_iUnion_iff _ _).mpr hlocal
  rwa [hcover, Measure.restrict_univ] at hu

/-- The mixed coordinate Hessian of the heat kernel is symmetric in its two indices. -/
theorem c6_heatSelectedCyclic_coordinateDerivative_comm {d : ℕ} (t : ℝ) (ht : 0 < t)
    (a b : Fin d) (z : Vec d) :
    coordinateDerivative a (coordinateDerivative b (euclideanHeatKernel (d := d) t)) z =
      coordinateDerivative b (coordinateDerivative a (euclideanHeatKernel (d := d) t)) z := by
  rw [coordinateDerivative_two_euclideanHeatKernel t ht,
    coordinateDerivative_two_euclideanHeatKernel t ht, mul_comm (z b) (z a)]
  by_cases h : a = b
  · subst h
    rfl
  · rw [if_neg h, if_neg (Ne.symm h)]

/-- The three source densities of a cyclic triple sum to zero pointwise for `t > 0`. -/
theorem c6_heatSelectedCyclic_density_sum {d : ℕ} (g : Vec d → Vec d) (t : ℝ) (ht : 0 < t)
    (j k l : Fin d) (x y : Vec d) :
    akmHeatGradientDensity g t j k l x y + akmHeatGradientDensity g t k l j x y +
      akmHeatGradientDensity g t l j k x y = 0 := by
  rw [akmHeatGradientDensity_eq_mixedHessian g t ht, akmHeatGradientDensity_eq_mixedHessian g t ht,
    akmHeatGradientDensity_eq_mixedHessian g t ht]
  linear_combination (g y k) * c6_heatSelectedCyclic_coordinateDerivative_comm t ht l j (x - y)
    - (g y j) * c6_heatSelectedCyclic_coordinateDerivative_comm t ht l k (x - y)
    + (g y l) * c6_heatSelectedCyclic_coordinateDerivative_comm t ht j k (x - y)

/-- On a window of positive times, the cyclic sum of the three iterated truncations
vanishes, provided the integrability clauses hold. -/
theorem c6_heatSelectedCyclic_truncation_sum {d : ℕ} (g : Vec d → Vec d) (m n : ℕ)
    (j k l : Fin d) (x : Vec d)
    (hD₁ : ∀ᵐ t ∂(volume.restrict (Set.Icc (((m + 1 : ℕ) : ℝ)⁻¹) ((n + 1 : ℕ) : ℝ))),
      Integrable (fun y => akmHeatGradientDensity g t j k l x y) volume)
    (hD₂ : ∀ᵐ t ∂(volume.restrict (Set.Icc (((m + 1 : ℕ) : ℝ)⁻¹) ((n + 1 : ℕ) : ℝ))),
      Integrable (fun y => akmHeatGradientDensity g t k l j x y) volume)
    (hD₃ : ∀ᵐ t ∂(volume.restrict (Set.Icc (((m + 1 : ℕ) : ℝ)⁻¹) ((n + 1 : ℕ) : ℝ))),
      Integrable (fun y => akmHeatGradientDensity g t l j k x y) volume)
    (hA₁ : Integrable (fun t => akmHeatGradientSpaceIntegral g t j k l x)
      (volume.restrict (Set.Icc (((m + 1 : ℕ) : ℝ)⁻¹) ((n + 1 : ℕ) : ℝ))))
    (hA₂ : Integrable (fun t => akmHeatGradientSpaceIntegral g t k l j x)
      (volume.restrict (Set.Icc (((m + 1 : ℕ) : ℝ)⁻¹) ((n + 1 : ℕ) : ℝ))))
    (hA₃ : Integrable (fun t => akmHeatGradientSpaceIntegral g t l j k x)
      (volume.restrict (Set.Icc (((m + 1 : ℕ) : ℝ)⁻¹) ((n + 1 : ℕ) : ℝ)))) :
    iteratedAKMHeatGradientTruncation g m n j k l x +
      iteratedAKMHeatGradientTruncation g m n k l j x +
      iteratedAKMHeatGradientTruncation g m n l j k x = 0 := by
  have hWm : MeasurableSet (Set.Icc (((m + 1 : ℕ) : ℝ)⁻¹) ((n + 1 : ℕ) : ℝ)) :=
    measurableSet_Icc
  have hzero : ∀ᵐ t ∂(volume.restrict (Set.Icc (((m + 1 : ℕ) : ℝ)⁻¹) ((n + 1 : ℕ) : ℝ))),
      akmHeatGradientSpaceIntegral g t j k l x + akmHeatGradientSpaceIntegral g t k l j x +
        akmHeatGradientSpaceIntegral g t l j k x = 0 := by
    filter_upwards [ae_restrict_mem hWm, hD₁, hD₂, hD₃] with t ht h₁ h₂ h₃
    have hpos : 0 < t := lt_of_lt_of_le (by positivity) ht.1
    have h₁₂ : Integrable (fun y => akmHeatGradientDensity g t j k l x y +
        akmHeatGradientDensity g t k l j x y) volume := h₁.add h₂
    have key : ∫ y, (akmHeatGradientDensity g t j k l x y + akmHeatGradientDensity g t k l j x y +
        akmHeatGradientDensity g t l j k x y) =
        (∫ y, akmHeatGradientDensity g t j k l x y) + (∫ y, akmHeatGradientDensity g t k l j x y) +
          ∫ y, akmHeatGradientDensity g t l j k x y := by
      rw [integral_add h₁₂ h₃, integral_add h₁ h₂]
    simp only [c6_heatSelectedCyclic_density_sum g t hpos j k l x, integral_zero] at key
    exact key.symm
  have hint : ∫ t, (akmHeatGradientSpaceIntegral g t j k l x +
      akmHeatGradientSpaceIntegral g t k l j x + akmHeatGradientSpaceIntegral g t l j k x)
      ∂(volume.restrict (Set.Icc (((m + 1 : ℕ) : ℝ)⁻¹) ((n + 1 : ℕ) : ℝ))) =
      ∫ t, (0 : ℝ) ∂(volume.restrict (Set.Icc (((m + 1 : ℕ) : ℝ)⁻¹) ((n + 1 : ℕ) : ℝ))) :=
    integral_congr_ae hzero
  have hA₁₂ : Integrable (fun t => akmHeatGradientSpaceIntegral g t j k l x +
      akmHeatGradientSpaceIntegral g t k l j x)
      (volume.restrict (Set.Icc (((m + 1 : ℕ) : ℝ)⁻¹) ((n + 1 : ℕ) : ℝ))) := hA₁.add hA₂
  rw [integral_add hA₁₂ hA₃, integral_add hA₁ hA₂, integral_zero] at hint
  unfold iteratedAKMHeatGradientTruncation
  exact hint

/-- The Euclidean origin balls of integer radius cover space. -/
theorem c6_heatSelectedCyclic_iUnion_ball_nat_eq_univ {d : ℕ} :
    (⋃ R : ℕ, ball (0 : Vec d) ((R : ℝ) + 1)) = Set.univ := by
  apply Set.iUnion_eq_univ_iff.mpr
  intro x
  obtain ⟨N, hN⟩ := exists_nat_gt (euclideanNorm x)
  refine ⟨N, ?_⟩
  change euclideanNorm (x - 0) < (N : ℝ) + 1
  rw [sub_zero]
  linarith

/-- Three local L² approximating families whose cyclic sums vanish almost everywhere
have an almost-everywhere vanishing cyclic limit. -/
theorem c6_heatSelectedCyclic_of_L2_limits {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (T₁ T₂ T₃ : ℕ × ℕ → Ω → ℝ) (G₁ G₂ G₃ : Ω → ℝ)
    (hc₁ : Tendsto (fun n => eLpNorm (T₁ n - G₁) 2 μ) atTop (𝓝 0))
    (hc₂ : Tendsto (fun n => eLpNorm (T₂ n - G₂) 2 μ) atTop (𝓝 0))
    (hc₃ : Tendsto (fun n => eLpNorm (T₃ n - G₃) 2 μ) atTop (𝓝 0))
    (hsum : ∀ n, ∀ᵐ x ∂μ, T₁ n x + T₂ n x + T₃ n x = 0) :
    ∀ᵐ x ∂μ, G₁ x + G₂ x + G₃ x = 0 := by
  have hTg : Tendsto (fun n => eLpNorm ((fun x => T₁ n x + T₂ n x + T₃ n x) - 0) 2 μ)
      atTop (𝓝 0) := by
    have hz : ∀ n, eLpNorm ((fun x => T₁ n x + T₂ n x + T₃ n x) - 0) 2 μ = 0 := fun n => by
      have hae : (fun x => T₁ n x + T₂ n x + T₃ n x) =ᵐ[μ] 0 := hsum n
      rw [sub_zero]
      exact (eLpNorm_congr_ae hae).trans eLpNorm_zero
    simp only [hz]
    exact tendsto_const_nhds
  have hTf : Tendsto (fun n => eLpNorm ((fun x => T₁ n x + T₂ n x + T₃ n x) -
      (fun x => G₁ x + G₂ x + G₃ x)) 2 μ) atTop (𝓝 0) := by
    have hbd : ∀ n, eLpNorm ((fun x => T₁ n x + T₂ n x + T₃ n x) -
        (fun x => G₁ x + G₂ x + G₃ x)) 2 μ ≤
        eLpNorm (T₁ n - G₁) 2 μ + (eLpNorm (T₂ n - G₂) 2 μ + eLpNorm (T₃ n - G₃) 2 μ) := by
      intro n
      have e : (fun x => T₁ n x + T₂ n x + T₃ n x) - (fun x => G₁ x + G₂ x + G₃ x) =
          (T₁ n - G₁) + (T₂ n - G₂) + (T₃ n - G₃) := by
        funext x
        simp only [Pi.sub_apply, Pi.add_apply]
        ring
      rw [e]
      calc eLpNorm ((T₁ n - G₁) + (T₂ n - G₂) + (T₃ n - G₃)) 2 μ
          ≤ eLpNorm ((T₁ n - G₁) + (T₂ n - G₂)) 2 μ + eLpNorm (T₃ n - G₃) 2 μ :=
            eLpNorm_add_le one_le_two
        _ ≤ (eLpNorm (T₁ n - G₁) 2 μ + eLpNorm (T₂ n - G₂) 2 μ) + eLpNorm (T₃ n - G₃) 2 μ := by
            gcongr
            exact eLpNorm_add_le one_le_two
        _ = eLpNorm (T₁ n - G₁) 2 μ + (eLpNorm (T₂ n - G₂) 2 μ + eLpNorm (T₃ n - G₃) 2 μ) :=
            add_assoc _ _ _
    have hlim := hc₁.add (hc₂.add hc₃)
    rw [add_zero, add_zero] at hlim
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun _ => bot_le) hbd
  exact tendstoInMeasure_ae_unique
    (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0) hTf)
    (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0) hTg)

/-- The heat-selected flux-corrector gradient is closed: its cyclic sum vanishes
almost everywhere. Source: AKM (6.7), `paper/main.tex:732-748`. -/
theorem c6_isHeatSelectedFluxGradient_cyclic {d : ℕ} {g : Vec d → Vec d}
    {G : Fin d → Fin d → Vec d → Vec d} (h : IsHeatSelectedFluxGradient g G)
    (j k l : Fin d) :
    ∀ᵐ x ∂(volume : Measure (Vec d)), G j k x l + G k l x j + G l j x k = 0 := by
  have hball : ∀ R : ℕ, ∀ᵐ x ∂(volume.restrict (ball (0 : Vec d) ((R : ℝ) + 1))),
      G j k x l + G k l x j + G l j x k = 0 := by
    intro R
    obtain ⟨hD₁, _, _, hC₁⟩ := h j k l R
    obtain ⟨hD₂, _, _, hC₂⟩ := h k l j R
    obtain ⟨hD₃, _, _, hC₃⟩ := h l j k R
    have hae : ∀ᵐ x ∂(volume.restrict (ball (0 : Vec d) ((R : ℝ) + 1))), ∀ m n : ℕ,
        iteratedAKMHeatGradientTruncation g m n j k l x +
          iteratedAKMHeatGradientTruncation g m n k l j x +
          iteratedAKMHeatGradientTruncation g m n l j k x = 0 := by
      rw [ae_all_iff]
      intro m
      rw [ae_all_iff]
      intro n
      filter_upwards [hD₁ m n, hD₂ m n, hD₃ m n] with x hx₁ hx₂ hx₃
      exact c6_heatSelectedCyclic_truncation_sum g m n j k l x hx₁.1 hx₂.1 hx₃.1 hx₁.2 hx₂.2 hx₃.2
    exact c6_heatSelectedCyclic_of_L2_limits (volume.restrict (ball (0 : Vec d) ((R : ℝ) + 1)))
      (fun mn x => iteratedAKMHeatGradientTruncation g mn.1 mn.2 j k l x)
      (fun mn x => iteratedAKMHeatGradientTruncation g mn.1 mn.2 k l j x)
      (fun mn x => iteratedAKMHeatGradientTruncation g mn.1 mn.2 l j k x)
      (fun x => G j k x l) (fun x => G k l x j) (fun x => G l j x k)
      hC₁ hC₂ hC₃ (fun n => hae.mono fun x hx => hx n.1 n.2)
  have hu := (ae_restrict_iUnion_iff _ _).mpr hball
  rwa [c6_heatSelectedCyclic_iUnion_ball_nat_eq_univ, Measure.restrict_univ] at hu


/-- Closedness holds for the literal source gradient on one full-measure set
of coefficient samples and spatial points, simultaneously for all indices. -/
theorem c6_sourceFluxGradient_closed {d : ℕ} {K : ℝ}
    {P : Measure (Coefficient d K)} {e : Vec d} {φ : Corrector P e}
    (S : FluxCorrector φ) :
    ∀ᵐ a ∂P, ∀ᵐ x ∂(volume : Measure (Vec d)), ∀ j k l : Fin d,
      S.grad a j k x l + S.grad a k l x j + S.grad a l j x k = 0 := by
  filter_upwards [S.heat_selected] with a ha
  exact ae_all_iff.mpr fun j => ae_all_iff.mpr fun k => ae_all_iff.mpr fun l =>
    c6_isHeatSelectedFluxGradient_cyclic ha j k l

/-- Fix the symmetric additive gauge of the actual source potential. -/
def c6SkewSourcePotential {d : ℕ} {K : ℝ} {P : Measure (Coefficient d K)}
    {e : Vec d} {φ : Corrector P e} (S : FluxCorrector φ)
    (a : Coefficient d K) (x : Vec d) : Mat d :=
  (1 / 2 : ℝ) • (S.potential a x - (S.potential a x).transpose)

/-- Antisymmetry holds at every point, including exceptional source samples. -/
theorem c6SkewSourcePotential_transpose {d : ℕ} {K : ℝ}
    {P : Measure (Coefficient d K)} {e : Vec d} {φ : Corrector P e}
    (S : FluxCorrector φ) (a : Coefficient d K) (x : Vec d) :
    (c6SkewSourcePotential S a x).transpose = -c6SkewSourcePotential S a x := by
  ext j k
  simp only [c6SkewSourcePotential, Matrix.transpose_apply, Matrix.smul_apply,
    Matrix.sub_apply, Matrix.neg_apply, smul_eq_mul]
  ring

/-- Heat selection makes taking the skew part preserve the literal weak gradient. -/
theorem c6SkewSourcePotential_weak_gradient {d : ℕ} {K : ℝ}
    {P : Measure (Coefficient d K)} {e : Vec d} {φ : Corrector P e}
    (S : FluxCorrector φ) :
    ∀ᵐ a ∂P, ∀ j k,
      HasWeakGradient Set.univ (fun x => c6SkewSourcePotential S a x j k)
        (S.grad a j k) := by
  filter_upwards [S.weak_gradient, S.heat_selected] with a hweak hheat
  intro j k
  have h := c6_hasWeakGradient_const_mul (hasWeakGradient_sub (hweak j k) (hweak k j))
    (1 / 2 : ℝ)
  apply hasWeakGradient_congr_ae isOpen_univ h (Filter.EventuallyEq.rfl) ?_
  rw [Measure.restrict_univ]
  have hswap : ∀ᵐ x ∂(volume : Measure (Vec d)),
      ∀ l, S.grad a k j x l = -S.grad a j k x l :=
    ae_all_iff.mpr fun l => c6_heatSelectedFluxGradient_ae_swap hheat j k l
  filter_upwards [hswap] with x hx
  ext l
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, hx l]
  ring

/-- The skew gauge retains the entire source flux-corrector carrier. In
particular, the gradient and its literal heat selection are unchanged. -/
def c6SkewSourceFluxCorrector {d : ℕ} {K : ℝ}
    {P : Measure (Coefficient d K)} {e : Vec d} {φ : Corrector P e}
    (S : FluxCorrector φ) : FluxCorrector φ where
  potential := c6SkewSourcePotential S
  grad := S.grad
  measurable_potential := by
    have hc : Continuous (fun A : Mat d => (1 / 2 : ℝ) • (A - A.transpose)) := by
      fun_prop
    exact hc.measurable.comp S.measurable_potential
  measurable_grad := S.measurable_grad
  weak_gradient := c6SkewSourcePotential_weak_gradient S
  locally_square_integrable := by
    filter_upwards [S.locally_square_integrable] with a ha
    intro R hR j k
    exact ⟨((ha R hR j k).1.sub (ha R hR k j).1).const_mul (1 / 2 : ℝ),
      (ha R hR j k).2⟩
  heat_selected := S.heat_selected

/-- The skew gauge changes the original potential only by entrywise constants. -/
theorem c6SkewSourcePotential_matrix_gauge {d : ℕ} (hd : 0 < d) {K : ℝ}
    {P : Measure (Coefficient d K)} {e : Vec d} {φ : Corrector P e}
    (S : FluxCorrector φ) :
    ∀ᵐ a ∂P, ∃ C : Mat d,
      c6SkewSourcePotential S a =ᵐ[volume] (fun x => S.potential a x + C) := by
  filter_upwards [c6SkewSourcePotential_weak_gradient S, S.weak_gradient]
    with a hskew hweak
  have hgauge (j k : Fin d) : ∃ c : ℝ,
      (fun x => c6SkewSourcePotential S a x j k) =ᵐ[volume]
        (fun x => S.potential a x j k + c) := by
    have hdiff := hasWeakGradient_sub (hskew j k) (hweak j k)
    have hzero (l : Fin d) (ψ : Vec d → ℝ) (hψ : IsSpatialTest Set.univ ψ) :
        (∫ x, (c6SkewSourcePotential S a x j k - S.potential a x j k) *
          coordinateDerivative l ψ x) = 0 := by
      have heq := (hdiff l).2.2 ψ hψ
      simpa only [Measure.restrict_univ, Pi.sub_apply, sub_self, zero_mul,
        integral_zero, neg_zero] using heq
    obtain ⟨c, hc⟩ := ae_eq_const_of_zero_weak_gradient
      (locallyIntegrableOn_univ.mp (hdiff ⟨0, hd⟩).1) hzero
    refine ⟨c, hc.mono fun x hx => ?_⟩
    change c6SkewSourcePotential S a x j k - S.potential a x j k = c at hx
    linarith
  choose C hC using hgauge
  refine ⟨C, ?_⟩
  have hentries := ae_all_iff.mpr fun j => ae_all_iff.mpr fun k => hC j k
  filter_upwards [hentries] with x hx
  ext j k
  exact hx j k

/-- Every local Frobenius oscillation is retained by shifting its comparison
matrix by the same source gauge, with no loss in the source constants. -/
theorem c6SkewSourcePotential_local_oscillation {d : ℕ} (hd : 0 < d) {K : ℝ}
    {P : Measure (Coefficient d K)} {e : Vec d} {φ : Corrector P e}
    (S : FluxCorrector φ) :
    ∀ᵐ a ∂P, ∃ C : Mat d, ∀ (b : Mat d) (U : Set (Vec d)),
      (∫ x in U, frobeniusNorm (c6SkewSourcePotential S a x - (b + C)) ^ 2) =
        ∫ x in U, frobeniusNorm (S.potential a x - b) ^ 2 := by
  filter_upwards [c6SkewSourcePotential_matrix_gauge hd S] with a ha
  obtain ⟨C, hC⟩ := ha
  refine ⟨C, fun b U => integral_congr_ae ?_⟩
  filter_upwards [ae_restrict_of_ae hC] with x hx
  rw [hx]
  congr 2
  abel

/-- Centering on a ball removes the source matrix gauge exactly. Thus the
literal normalized Frobenius oscillation, rather than only an oscillation
around a freely chosen comparison matrix, survives skew selection. -/
theorem c6SkewSourcePotential_centered_oscillation {d : ℕ} (hd : 0 < d) {K : ℝ}
    {P : Measure (Coefficient d K)} {e : Vec d} {φ : Corrector P e}
    (S : FluxCorrector φ) :
    ∀ᵐ a ∂P, ∀ R : ℝ, 0 < R →
      (⨍ x in ball 0 R, frobeniusNorm (c6SkewSourcePotential S a x -
        (Matrix.of fun j k => ⨍ y in ball 0 R, c6SkewSourcePotential S a y j k)) ^ 2) =
      ⨍ x in ball 0 R, frobeniusNorm (S.potential a x -
        (Matrix.of fun j k => ⨍ y in ball 0 R, S.potential a y j k)) ^ 2 := by
  filter_upwards [c6SkewSourcePotential_matrix_gauge hd S, S.locally_square_integrable]
    with a hga hl
  obtain ⟨C, hC⟩ := hga
  intro R hR
  let μ := volume.restrict (ball (0 : Vec d) R)
  have hvol := ENNReal.toReal_pos_iff.mp (ball_volume_pos_finite d R hR)
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr hvol.2.ne
  have havg (j k : Fin d) :
      (⨍ y in ball 0 R, c6SkewSourcePotential S a y j k) =
        (⨍ y in ball 0 R, S.potential a y j k) + C j k := by
    have heq : (fun y => c6SkewSourcePotential S a y j k) =ᵐ[μ]
        (fun y => S.potential a y j k + C j k) :=
      (ae_restrict_of_ae hC).mono fun y hy => congrArg (fun M => M j k) hy
    rw [average_congr heq]
    rw [average_fun_add ((hl R hR j k).1.integrable (by norm_num)) (integrable_const _)]
    rw [setAverage_const hvol.1.ne' hvol.2.ne]
  apply average_congr
  filter_upwards [ae_restrict_of_ae hC] with x hx
  congr 2
  ext j k
  simp only [Matrix.sub_apply, Matrix.of_apply, havg, hx, Matrix.add_apply]
  ring

/-- The actual range and amplitude rescaling of the skew source potential. -/
def c6PhysicalSourcePotential {d : ℕ} {K : ℝ} {P : Measure (Coefficient d K)}
    {e : Vec d} {φ : Corrector P e} (S : FluxCorrector φ)
    (r κ : ℝ) (a : Coefficient d K) (x : Vec d) : Mat d :=
  (r / κ) • c6SkewSourcePotential S a (r⁻¹ • x)

/-- Physical dilation preserves pointwise antisymmetry, also on exceptional
source samples. -/
theorem c6PhysicalSourcePotential_transpose {d : ℕ} {K : ℝ}
    {P : Measure (Coefficient d K)} {e : Vec d} {φ : Corrector P e}
    (S : FluxCorrector φ) (r κ : ℝ) (a : Coefficient d K) (x : Vec d) :
    (c6PhysicalSourcePotential S r κ a x).transpose =
      -c6PhysicalSourcePotential S r κ a x := by
  simp only [c6PhysicalSourcePotential, Matrix.transpose_smul,
    c6SkewSourcePotential_transpose, smul_neg]

/-- Range dilation cancels its amplitude in the literal source weak gradient.
This retains the selected source gradient rather than choosing new derivatives. -/
theorem c6PhysicalSourcePotential_weak_gradient {d : ℕ} {K : ℝ}
    {P : Measure (Coefficient d K)} {e : Vec d} {φ : Corrector P e}
    (S : FluxCorrector φ) (r κ : ℝ) (hr : 0 < r) :
    ∀ᵐ a ∂P, ∀ j k : Fin d,
      HasWeakGradient Set.univ (fun x => c6PhysicalSourcePotential S r κ a x j k)
        (fun x => κ⁻¹ • S.grad a j k (r⁻¹ • x)) := by
  filter_upwards [(c6SkewSourceFluxCorrector S).weak_gradient,
    (c6SkewSourceFluxCorrector S).locally_square_integrable] with a hw hl
  intro j k
  have h := hasWeakGradient_dilation
    (fun x => c6SkewSourcePotential S a x j k) (S.grad a j k)
    (fun R hR => (hl R hR j k).1) (fun R hR => (hl R hR j k).2)
    (hw j k) r⁻¹ (r / κ) (inv_pos.mpr hr)
  have hscale : r / κ * r⁻¹ = κ⁻¹ := by
    rw [div_eq_mul_inv, mul_right_comm, mul_inv_cancel₀ hr.ne', one_mul]
  simpa only [hscale, c6PhysicalSourcePotential, Matrix.smul_apply, smul_eq_mul] using h

/-- The rescaled potential and the same rescaled source gradient retain local
L² membership on every Euclidean ball. -/
theorem c6PhysicalSourcePotential_locally_square_integrable {d : ℕ} {K : ℝ}
    {P : Measure (Coefficient d K)} {e : Vec d} {φ : Corrector P e}
    (S : FluxCorrector φ) (r κ : ℝ) (hr : 0 < r) :
    ∀ᵐ a ∂P, ∀ R : ℝ, 0 < R → ∀ j k : Fin d,
      MemLp (fun x => c6PhysicalSourcePotential S r κ a x j k)
        2 (volume.restrict (ball 0 R)) ∧
      MemLp (fun x => κ⁻¹ • S.grad a j k (r⁻¹ • x))
        2 (volume.restrict (ball 0 R)) := by
  filter_upwards [(c6SkewSourceFluxCorrector S).locally_square_integrable] with a hl
  intro R hR j k
  constructor
  · simpa only [c6PhysicalSourcePotential, Matrix.smul_apply, smul_eq_mul] using
      memLp_two_on_euclidean_balls_dilation
        (fun x => c6SkewSourcePotential S a x j k)
        (fun T hT => (hl T hT j k).1) r⁻¹ (r / κ) (inv_pos.mpr hr) R hR
  · exact memLp_two_on_euclidean_balls_dilation (S.grad a j k)
      (fun T hT => (hl T hT j k).2) r⁻¹ κ⁻¹ (inv_pos.mpr hr) R hR

private theorem c6_contDiff_coordinateDerivative {d : ℕ} {f : Vec d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (i : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (coordinateDerivative i f) := by
  exact ((contDiff_infty_iff_fderiv.mp hf).2).clm_apply contDiff_const

private theorem c6_hasCompactSupport_coordinateDerivative {d : ℕ} {f : Vec d → ℝ}
    (hf : HasCompactSupport f) (i : Fin d) :
    HasCompactSupport (coordinateDerivative i f) := by
  exact hf.fderiv_apply ℝ (unitVector i)

private theorem c6_coordinateDerivative_comm {d : ℕ} {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (i j : Fin d) :
    coordinateDerivative i (coordinateDerivative j ψ) =
      coordinateDerivative j (coordinateDerivative i ψ) := by
  ext x
  have hinner : (2 : ℕ∞) ≤ (⊤ : ℕ∞) := le_top
  have hn : minSmoothness ℝ 2 ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞) := by
    rw [minSmoothness_of_isRCLikeNormedField]
    change (↑(2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
    exact_mod_cast hinner
  have hs := (hψ.contDiffAt (x := x)).isSymmSndFDerivAt hn
  have hd : DifferentiableAt ℝ (fun y => fderiv ℝ ψ y) x := by
    have hbound : (1 : WithTop ℕ∞) + 1 ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞) := by
      change (↑(2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
      exact_mod_cast hinner
    exact ((hψ.contDiffAt (x := x)).fderiv_right hbound).differentiableAt (by norm_num)
  have happly (v w : Vec d) :
      fderiv ℝ (fun y => fderiv ℝ ψ y v) x w =
        (fderiv ℝ (fderiv ℝ ψ) x w) v := by
    have h := fderiv_clm_apply hd (differentiableAt_const (x := x) v)
    have h' := congrArg (fun L : Vec d →L[ℝ] ℝ => L w) h
    simpa using h'
  have hswap := hs.iteratedFDeriv_cons (v := unitVector i) (w := unitVector j)
  change fderiv ℝ (coordinateDerivative j ψ) x (unitVector i) =
    fderiv ℝ (coordinateDerivative i ψ) x (unitVector j)
  rw [show coordinateDerivative j ψ = fun y => fderiv ℝ ψ y (unitVector j) by rfl,
      show coordinateDerivative i ψ = fun y => fderiv ℝ ψ y (unitVector i) by rfl]
  rw [happly (unitVector j) (unitVector i), happly (unitVector i) (unitVector j)]
  simpa [iteratedFDeriv_two_apply] using hswap


private theorem c6_integrable_mul_test {d : ℕ} {h : Vec d → ℝ} (hh : LocallyIntegrable h volume)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ) :
    Integrable (fun x => h x * φ x) volume := by
  simpa only [smul_eq_mul] using
    hh.integrable_smul_right_of_hasCompactSupport hφ.continuous hφc

private theorem c6_isSpatialTest_univ {d : ℕ} {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ) : IsSpatialTest Set.univ φ :=
  ⟨hφ, hφc, Set.subset_univ _⟩

/-- The weak derivative identity on all of space, without restrictions. -/
private theorem c6_integral_mul_coordinateDerivative_of_weak {d : ℕ} {u v : Vec d → ℝ} {c : Fin d}
    (h : HasWeakPartialDerivative Set.univ c u v) {φ : Vec d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ) :
    (∫ x, u x * coordinateDerivative c φ x) = -∫ x, v x * φ x := by
  have h' := h.2.2 φ (c6_isSpatialTest_univ hφ hφc)
  simpa only [Measure.restrict_univ] using h'

section C6ClosedSkewPoisson
variable {d : ℕ} {σ : Vec d → Mat d} {f : Fin d → Fin d → Fin d → Vec d → ℝ} {g : Vec d → Vec d}

/-- Exchanging the derivative index with the test derivative, through the potential. -/
private theorem c6_integral_closedGradient_swap
    (hweak : ∀ a b, HasWeakGradient Set.univ (fun x => σ x a b) (fun x c => f a b c x))
    {ψ : Vec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) (a l j : Fin d) :
    (∫ x, f a l j x * coordinateDerivative l ψ x) =
      ∫ x, f a l l x * coordinateDerivative j ψ x := by
  have h1 := c6_integral_mul_coordinateDerivative_of_weak (hweak a l j)
    (c6_contDiff_coordinateDerivative hψ l) (c6_hasCompactSupport_coordinateDerivative hψc l)
  have h2 := c6_integral_mul_coordinateDerivative_of_weak (hweak a l l)
    (c6_contDiff_coordinateDerivative hψ j) (c6_hasCompactSupport_coordinateDerivative hψc j)
  rw [c6_coordinateDerivative_comm hψ j l] at h1
  linarith

private theorem c6_locallyIntegrable_closedGradient
    (hweak : ∀ a b, HasWeakGradient Set.univ (fun x => σ x a b) (fun x c => f a b c x))
    (a b c : Fin d) : LocallyIntegrable (f a b c) volume :=
  locallyIntegrableOn_univ.mp (hweak a b c).2.1

private theorem c6_locallyIntegrable_potential
    (hweak : ∀ a b, HasWeakGradient Set.univ (fun x => σ x a b) (fun x c => f a b c x))
    (hd : 0 < d) (a b : Fin d) : LocallyIntegrable (fun x => σ x a b) volume :=
  locallyIntegrableOn_univ.mp (hweak a b ⟨0, hd⟩).1

private theorem c6_locallyIntegrable_rowDivergence
    (hweak : ∀ a b, HasWeakGradient Set.univ (fun x => σ x a b) (fun x c => f a b c x))
    (hdiv : ∀ a, ∀ᵐ x ∂(volume : Measure (Vec d)), ∑ c, f a c c x = g x a) (a : Fin d) :
    LocallyIntegrable (fun x => g x a) volume := by
  have hsum : LocallyIntegrable (fun x => ∑ c, f a c c x) volume := by
    have h := locallyIntegrable_finset_sum (Finset.univ : Finset (Fin d))
      (fun c _ => c6_locallyIntegrable_closedGradient hweak a c c)
    simpa only [Finset.sum_apply] using h
  refine hsum.mono (hsum.aestronglyMeasurable.congr (hdiv a)) ?_
  filter_upwards [hdiv a] with x hx
  rw [hx]

/-- The curl Poisson equation `-Δσ_{jk} = ∂_j g_k - ∂_k g_j` of a closed skew
corrector. Source: AKM (6.5), `paper/main.tex:732-735`. -/
private theorem c6_closedSkew_poisson_identity (hd : 0 < d)
    (hweak : ∀ a b, HasWeakGradient Set.univ (fun x => σ x a b) (fun x c => f a b c x))
    (hswap : ∀ a b c, ∀ᵐ x ∂(volume : Measure (Vec d)), f b a c x = -f a b c x)
    (hcyc : ∀ a b c, ∀ᵐ x ∂(volume : Measure (Vec d)),
      f a b c x + f b c a x + f c a b x = 0)
    (hdiv : ∀ a, ∀ᵐ x ∂(volume : Measure (Vec d)), ∑ c, f a c c x = g x a)
    {ψ : Vec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) (j k : Fin d) :
    Integrable (fun x => σ x j k *
        (-∑ l, coordinateDerivative l (coordinateDerivative l ψ) x)) volume ∧
      Integrable (fun x => g x k * coordinateDerivative j ψ x) volume ∧
      Integrable (fun x => g x j * coordinateDerivative k ψ x) volume ∧
      (∫ x, σ x j k * (-∑ l, coordinateDerivative l (coordinateDerivative l ψ) x)) =
        -(∫ x, g x k * coordinateDerivative j ψ x) + ∫ x, g x j * coordinateDerivative k ψ x := by
  have hD (l : Fin d) := c6_contDiff_coordinateDerivative hψ l
  have hDc (l : Fin d) := c6_hasCompactSupport_coordinateDerivative hψc l
  have hDD (l : Fin d) := c6_contDiff_coordinateDerivative (hD l) l
  have hDDc (l : Fin d) := c6_hasCompactSupport_coordinateDerivative (hDc l) l
  have hσl (l : Fin d) : Integrable (fun x => σ x j k *
      coordinateDerivative l (coordinateDerivative l ψ) x) volume :=
    c6_integrable_mul_test (c6_locallyIntegrable_potential hweak hd j k) (hDD l) (hDDc l)
  have hfl (a b c l : Fin d) : Integrable (fun x => f a b c x * coordinateDerivative l ψ x)
      volume :=
    c6_integrable_mul_test (c6_locallyIntegrable_closedGradient hweak a b c) (hD l) (hDc l)
  have hgk : Integrable (fun x => g x k * coordinateDerivative j ψ x) volume :=
    c6_integrable_mul_test (c6_locallyIntegrable_rowDivergence hweak hdiv k) (hD j) (hDc j)
  have hgj : Integrable (fun x => g x j * coordinateDerivative k ψ x) volume :=
    c6_integrable_mul_test (c6_locallyIntegrable_rowDivergence hweak hdiv j) (hD k) (hDc k)
  have hlap : Integrable (fun x => σ x j k *
      (-∑ l, coordinateDerivative l (coordinateDerivative l ψ) x)) volume := by
    have h := (integrable_finset_sum (Finset.univ : Finset (Fin d)) fun l _ => hσl l).neg
    refine h.congr (ae_of_all _ fun x => ?_)
    simp only [Pi.neg_apply, mul_neg, Finset.mul_sum]
  refine ⟨hlap, hgk, hgj, ?_⟩
  -- the Laplacian pairing is the pairing of the gradient with the test gradient
  have hstep1 : (∫ x, σ x j k * (-∑ l, coordinateDerivative l (coordinateDerivative l ψ) x)) =
      ∑ l, ∫ x, f j k l x * coordinateDerivative l ψ x := by
    have h : (fun x => σ x j k * (-∑ l, coordinateDerivative l (coordinateDerivative l ψ) x)) =
        fun x => -∑ l, σ x j k * coordinateDerivative l (coordinateDerivative l ψ) x := by
      funext x
      rw [mul_neg, Finset.mul_sum]
    rw [h, integral_neg, integral_finset_sum _ fun l _ => hσl l, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [c6_integral_mul_coordinateDerivative_of_weak (hweak j k l) (hD l) (hDc l), neg_neg]
  -- closedness and antisymmetry
  have hsplit (l : Fin d) : (∫ x, f j k l x * coordinateDerivative l ψ x) =
      -(∫ x, f k l l x * coordinateDerivative j ψ x) +
        ∫ x, f j l l x * coordinateDerivative k ψ x := by
    have hae : (fun x => f j k l x * coordinateDerivative l ψ x) =ᵐ[volume]
        fun x => -(f k l j x * coordinateDerivative l ψ x) +
          f j l k x * coordinateDerivative l ψ x := by
      filter_upwards [hcyc j k l, hswap j l k] with x h1 h2
      have : f j k l x = -f k l j x + f j l k x := by linarith
      rw [this]
      ring
    have hneg : Integrable (fun x => -(f k l j x * coordinateDerivative l ψ x)) volume :=
      (hfl k l j l).neg
    rw [integral_congr_ae hae, integral_add hneg (hfl j l k l), integral_neg,
      c6_integral_closedGradient_swap hweak hψ hψc k l j,
      c6_integral_closedGradient_swap hweak hψ hψc j l k]
  rw [hstep1, Finset.sum_congr rfl fun l _ => hsplit l, Finset.sum_add_distrib,
    Finset.sum_neg_distrib, ← integral_finset_sum _ fun l _ => hfl k l l j,
    ← integral_finset_sum _ fun l _ => hfl j l l k]
  congr 1
  · congr 1
    refine integral_congr_ae ?_
    filter_upwards [hdiv k] with x hx
    rw [← Finset.sum_mul, hx]
  · refine integral_congr_ae ?_
    filter_upwards [hdiv j] with x hx
    rw [← Finset.sum_mul, hx]

end C6ClosedSkewPoisson

/-- The literal trace of the selected source gradient. Identifying this with
`centeredFlux` requires the heat-divergence argument; it is not built into this definition. -/
def c6SourceRowDivergence {d : ℕ} {K : ℝ} {P : Measure (Coefficient d K)}
    {e : Vec d} {φ : Corrector P e} (S : FluxCorrector φ)
    (a : Coefficient d K) (x : Vec d) : Vec d :=
  fun j => ∑ k, S.grad a j k x k

/-- The actual skew potential satisfies the weak curl-Poisson equation with
its literal row divergence. No identification or regularity premise is added. -/
theorem c6_sourcePotential_poisson_flux {d : ℕ} (hd : 0 < d) {K : ℝ}
    {P : Measure (Coefficient d K)} {e : Vec d} {φ : Corrector P e}
    (S : FluxCorrector φ) :
    ∀ᵐ a ∂P, ∀ j k : Fin d, HasWeakDivergence Set.univ
      (fun x => S.grad a j k x -
        (c6SourceRowDivergence S a x j • unitVector k -
          c6SourceRowDivergence S a x k • unitVector j)) (fun _ => 0) := by
  filter_upwards [c6SkewSourcePotential_weak_gradient S, S.heat_selected,
    c6_sourceFluxGradient_closed S] with a hw hheat hclosed
  have hswap (j k l : Fin d) := c6_heatSelectedFluxGradient_ae_swap hheat j k l
  have hcyclic (j k l : Fin d) := hclosed.mono fun x hx => hx j k l
  have hdiv (j : Fin d) : ∀ᵐ x ∂(volume : Measure (Vec d)),
      ∑ k, S.grad a j k x k = c6SourceRowDivergence S a x j :=
    ae_of_all _ fun _ => rfl
  have hloc (j : Fin d) : LocallyIntegrable
      (fun x => c6SourceRowDivergence S a x j) volume :=
    c6_locallyIntegrable_rowDivergence hw hdiv j
  intro j k
  apply hasWeakDivergence_gradient_sub_curl_of_poisson j k (hw j k) hloc
  intro ψ hψ hc
  exact (c6_closedSkew_poisson_identity hd hw hswap hcyclic hdiv hψ hc j k).2.2.2

/-- The weak Poisson flux is locally square integrable on the same source
samples, as a finite linear combination of the selected gradient entries. -/
theorem c6_sourcePoissonFlux_locally_square_integrable {d : ℕ} {K : ℝ}
    {P : Measure (Coefficient d K)} {e : Vec d} {φ : Corrector P e}
    (S : FluxCorrector φ) :
    ∀ᵐ a ∂P, ∀ R : ℝ, 0 < R → ∀ j k : Fin d,
      MemLp (fun x => S.grad a j k x -
        (c6SourceRowDivergence S a x j • unitVector k -
          c6SourceRowDivergence S a x k • unitVector j))
        2 (volume.restrict (ball 0 R)) := by
  filter_upwards [S.locally_square_integrable] with a hl
  intro R hR j k
  have htrace (b : Fin d) : MemLp
      (fun x => c6SourceRowDivergence S a x b) 2 (volume.restrict (ball 0 R)) := by
    exact memLp_finsetSum Finset.univ fun c _ => (hl R hR b c).2.eval c
  apply memLp_pi_iff.mpr
  intro l
  simpa only [Pi.sub_def, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_comm] using
    ((hl R hR j k).2.eval l).sub
      (((htrace j).const_mul (unitVector k l)).sub ((htrace k).const_mul (unitVector j l)))

/-- The actual physical rescaling retains the weak Poisson equation, with
precisely the inverse coefficient-amplitude factor in its gradient and curl source. -/
theorem c6_physicalSourcePotential_poisson_flux {d : ℕ} (hd : 0 < d) {K : ℝ}
    {P : Measure (Coefficient d K)} {e : Vec d} {φ : Corrector P e}
    (S : FluxCorrector φ) (r κ : ℝ) (hr : 0 < r) :
    ∀ᵐ a ∂P, ∀ j k : Fin d, HasWeakDivergence Set.univ
      (fun x => κ⁻¹ • S.grad a j k (r⁻¹ • x) -
        ((κ⁻¹ * c6SourceRowDivergence S a (r⁻¹ • x) j) • unitVector k -
          (κ⁻¹ * c6SourceRowDivergence S a (r⁻¹ • x) k) • unitVector j))
      (fun _ => 0) := by
  filter_upwards [c6_sourcePotential_poisson_flux hd S,
    c6_sourcePoissonFlux_locally_square_integrable S] with a hw hl
  intro j k
  have h := hasWeakDivergence_zero_dilation
    (fun x => S.grad a j k x -
      (c6SourceRowDivergence S a x j • unitVector k -
        c6SourceRowDivergence S a x k • unitVector j))
    (fun R hR => hl R hR j k) (hw j k) r⁻¹ κ⁻¹ (inv_pos.mpr hr)
  simpa only [smul_sub, smul_smul, smul_eq_mul] using h

/-- Half of a concrete unit-direction corrector, on the identical source law.
Only the direction binder changes; its gradient is literally halved. -/
private def c6HalfUnitCorrector {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (φ : Corrector (actualCoefficientLaw Q) (correctorUnitVector i).ofLp) :
    Corrector (actualCoefficientLaw Q) (halfDirection i) where
  potential := (scaledAKMCorrector φ (1 / 2)).potential
  grad := (scaledAKMCorrector φ (1 / 2)).grad
  measurable_grad := (scaledAKMCorrector φ (1 / 2)).measurable_grad
  weak_gradient := (scaledAKMCorrector φ (1 / 2)).weak_gradient
  locally_square_integrable := (scaledAKMCorrector φ (1 / 2)).locally_square_integrable
  stationary := (scaledAKMCorrector φ (1 / 2)).stationary
  harmonic := by
    simpa only [correctorUnitVector, WithLp.ofLp_toLp, halfDirection, unitVector,
      scaledAKMCorrector] using
      (scaledAKMCorrector φ (1 / 2)).harmonic
  sublinear := (scaledAKMCorrector φ (1 / 2)).sublinear
  cell_integrable := by
    simpa only [correctorUnitVector, WithLp.ofLp_toLp, halfDirection, unitVector,
      scaledAKMCorrector] using
      (scaledAKMCorrector φ (1 / 2)).cell_integrable

open ReductionImageV3

/-- The actual unit-direction source flux has precisely the coefficient
amplitude factor, with no residual half-direction factor. -/
theorem c6_unitCenteredFlux_eq_canonical {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (φ : Corrector (actualCoefficientLaw Q) (correctorUnitVector i).ofLp)
    (hid : ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ y ∂(volume : Measure (Vec d)),
      (correctorUnitVector i).ofLp + φ.grad
        (project (r₀ := r₀) Q.ellipticity_parameter ω) y =
      (correctorUnitVector i + (canonicalCorrectorGradient Q i :
        Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
          (translate (r₀ • y) (reduce ω.1))).ofLp) :
    ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ y ∂(volume : Measure (Vec d)),
      centeredFlux φ (project (r₀ := r₀) Q.ellipticity_parameter ω) y =
        ellipticityScale L •
          ((canonicalCorrectorFlux Q i (translate (r₀ • y) (reduce ω.1))).ofLp -
            (expectedCorrectorFlux Q i).ofLp) := by
  have hhalf : ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ y ∂(volume : Measure (Vec d)),
      (2 : ℝ) • (halfDirection i + (c6HalfUnitCorrector Q i φ).grad
        (project (r₀ := r₀) Q.ellipticity_parameter ω) y) =
      (correctorUnitVector i + (canonicalCorrectorGradient Q i :
        Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
          (translate (r₀ • y) (reduce ω.1))).ofLp := by
    filter_upwards [hid] with ω hω
    filter_upwards [hω] with y hy
    simpa only [c6HalfUnitCorrector, scaledAKMCorrector, smul_add,
      EinsteinFull.Calculus.C4HalfDirectionCorrector.two_smul_halfDirection,
      smul_smul, show (2 : ℝ) * (1 / 2) = 1 by norm_num, one_smul] using hy
  have hcenter (a : Coefficient d (AKMUpperEllipticity L)) (y : Vec d) :
      centeredFlux (c6HalfUnitCorrector Q i φ) a y = (1 / 2 : ℝ) • centeredFlux φ a y := by
    simpa only [centeredFlux, meanFlux, c6HalfUnitCorrector, scaledAKMCorrector,
      correctorUnitVector, WithLp.ofLp_toLp, halfDirection, unitVector] using
      centeredFlux_scaledAKMCorrector φ (1 / 2) a y
  filter_upwards [ae_akmCenteredFlux_eq_scaled_canonicalCenteredFlux Q i
    (c6HalfUnitCorrector Q i φ) hhalf] with ω hω
  filter_upwards [hω] with y hy
  rw [hcenter] at hy
  have h := congrArg (fun v : Vec d => (2 : ℝ) • v) hy
  simpa only [smul_smul, show (2 : ℝ) * (1 / 2) = 1 by norm_num, one_smul,
    show (2 : ℝ) * (ellipticityScale L / 2) = ellipticityScale L by ring] using h

/-- The same identification in the physical coordinate, with the source
range dilation canceled almost everywhere. -/
theorem c6_unitCenteredFlux_physical {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (φ : Corrector (actualCoefficientLaw Q) (correctorUnitVector i).ofLp)
    (hid : ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ y ∂(volume : Measure (Vec d)),
      (correctorUnitVector i).ofLp + φ.grad
        (project (r₀ := r₀) Q.ellipticity_parameter ω) y =
      (correctorUnitVector i + (canonicalCorrectorGradient Q i :
        Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
          (translate (r₀ • y) (reduce ω.1))).ofLp) :
    ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ x ∂(volume : Measure (Vec d)),
      centeredFlux φ (project (r₀ := r₀) Q.ellipticity_parameter ω) (r₀⁻¹ • x) =
        ellipticityScale L •
          ((canonicalCorrectorFlux Q i (translate x (reduce ω.1))).ofLp -
            (expectedCorrectorFlux Q i).ofLp) := by
  have hr : 0 < r₀ := zero_lt_one.trans_le Q.range_parameter
  filter_upwards [c6_unitCenteredFlux_eq_canonical Q i φ hid] with ω hω
  have h := (Measure.quasiMeasurePreserving_smul (volume : Measure (Vec d))
    (inv_ne_zero hr.ne')).ae hω
  simpa only [smul_smul, mul_inv_cancel₀ hr.ne', one_smul] using h

/-- The normalized physical source flux is the literal right-hand side of
the required column-divergence identity. Both identifications hold almost everywhere. -/
theorem c6_unitCenteredFlux_physical_target {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (φ : Corrector (actualCoefficientLaw Q) (correctorUnitVector i).ofLp)
    (hid : ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ y ∂(volume : Measure (Vec d)),
      (correctorUnitVector i).ofLp + φ.grad
        (project (r₀ := r₀) Q.ellipticity_parameter ω) y =
      (correctorUnitVector i + (canonicalCorrectorGradient Q i :
        Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
          (translate (r₀ • y) (reduce ω.1))).ofLp) :
    ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ x ∂(volume : Measure (Vec d)), ∀ j : Fin d,
      (ellipticityScale L)⁻¹ *
        centeredFlux φ (project (r₀ := r₀) Q.ellipticity_parameter ω) (r₀⁻¹ • x) j =
      (((reduce ω.1).1 x).mulVec (unitVector i +
        WithLp.ofLp (correctorGradient Q i (translate x (reduce ω.1))))) j -
        homogenizedCoefficient Q j i := by
  have hsp := (measurePreserving_physicalReduction Q).quasiMeasurePreserving.ae
    (ae_spatial_canonicalCorrectorFlux Q i measurable_id)
  have hκ : ellipticityScale L ≠ 0 :=
    (ellipticityScale_pos Q.ellipticity_parameter).ne'
  filter_upwards [c6_unitCenteredFlux_physical Q i φ hid, hsp] with ω hω hs
  filter_upwards [hω, hs] with x hx hsx
  intro j
  simp only [id_eq] at hsx
  rw [hx, hsx]
  change (ellipticityScale L)⁻¹ * (ellipticityScale L *
    ((((reduce ω.1).1 x).mulVec _ ) j - (expectedCorrectorFlux Q i).ofLp j)) = _
  rw [← mul_assoc, inv_mul_cancel₀ hκ, one_mul]
  simp only [WithLp.ofLp_add, correctorUnitVector, WithLp.ofLp_toLp, unitVector]
  rfl

/-- Summing the genuine diagonal weak derivatives gives a weak divergence. -/
private theorem c6_hasWeakDivergence_of_partials {d : ℕ}
    {F : Vec d → Vec d} {G : Fin d → Vec d → ℝ}
    (h : ∀ k : Fin d, HasWeakPartialDerivative Set.univ k (fun x => F x k) (G k)) :
    HasWeakDivergence Set.univ F (fun x => ∑ k, G k x) := by
  have hsum : LocallyIntegrable (fun x => ∑ k, G k x) volume := by
    have hs := locallyIntegrable_finsetSum (Finset.univ : Finset (Fin d))
      (fun k _ => locallyIntegrableOn_univ.mp (h k).2.1)
    simpa only [Finset.sum_apply] using hs
  refine ⟨fun k => (h k).1, hsum.locallyIntegrableOn _, ?_⟩
  intro ψ hψ
  have hF (k : Fin d) : Integrable
      (fun x => F x k * coordinateDerivative k ψ x) volume :=
    c6_integrable_mul_test (locallyIntegrableOn_univ.mp (h k).1)
      (c6_contDiff_coordinateDerivative hψ.1 k)
      (c6_hasCompactSupport_coordinateDerivative hψ.2.1 k)
  have hG (k : Fin d) : Integrable (fun x => G k x * ψ x) volume :=
    c6_integrable_mul_test (locallyIntegrableOn_univ.mp (h k).2.1) hψ.1 hψ.2.1
  simp only [Measure.restrict_univ, dot, gradient, Finset.sum_mul]
  rw [integral_finsetSum _ fun k _ => hF k,
    integral_finsetSum _ fun k _ => hG k, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun k _ => by
    simpa only [Measure.restrict_univ] using (h k).2.2 ψ hψ

/-- The rescaled actual source potential has its literal weak row divergence,
with the inverse coefficient-amplitude factor and the same selected gradient. -/
theorem c6_physicalSourcePotential_rowDivergence {d : ℕ} {K : ℝ}
    {P : Measure (Coefficient d K)} {e : Vec d} {φ : Corrector P e}
    (S : FluxCorrector φ) (r κ : ℝ) (hr : 0 < r) :
    ∀ᵐ a ∂P, HasWeakRowDivergence Set.univ
      (c6PhysicalSourcePotential S r κ a)
      (fun x => κ⁻¹ • c6SourceRowDivergence S a (r⁻¹ • x)) := by
  filter_upwards [c6PhysicalSourcePotential_weak_gradient S r κ hr] with a ha
  intro j
  have h := c6_hasWeakDivergence_of_partials (fun k => ha j k k)
  simpa only [Pi.smul_apply, smul_eq_mul, c6SourceRowDivergence, Finset.mul_sum] using h

/-- Negating the actual physical source potential converts its row convention
into the column convention of the target. This is an actual weak equation;
identification of its literal trace with the centered flux remains separate. -/
theorem c6_physicalSourcePotential_columnDivergence {d : ℕ} {K : ℝ}
    {P : Measure (Coefficient d K)} {e : Vec d} {φ : Corrector P e}
    (S : FluxCorrector φ) (r κ : ℝ) (hr : 0 < r) :
    ∀ᵐ a ∂P, ∀ j : Fin d, HasWeakDivergence Set.univ
      (fun x k => -c6PhysicalSourcePotential S r κ a x k j)
      (fun x => κ⁻¹ * c6SourceRowDivergence S a (r⁻¹ • x) j) := by
  filter_upwards [c6_physicalSourcePotential_rowDivergence S r κ hr] with a ha
  intro j
  have heq : (fun x k => -c6PhysicalSourcePotential S r κ a x k j) =
      (fun x k => c6PhysicalSourcePotential S r κ a x j k) := by
    funext x k
    have hskew := congrArg (fun M : Mat d => M k j)
      (c6PhysicalSourcePotential_transpose S r κ a x)
    simpa only [Matrix.transpose_apply, Matrix.neg_apply, neg_neg] using hskew.symm
  rw [heq]
  exact ha j

/-- The literal source row trace is jointly measurable; no evaluation at a
distinguished spatial point is used to manufacture a stationary field. -/
theorem c6SourceRowDivergence_measurable {d : ℕ} {K : ℝ}
    {P : Measure (Coefficient d K)} {e : Vec d} {φ : Corrector P e}
    (S : FluxCorrector φ) :
    Measurable (fun p : Coefficient d K × Vec d => c6SourceRowDivergence S p.1 p.2) := by
  apply measurable_pi_lambda
  intro j
  exact Finset.measurable_sum _ fun k _ =>
    (measurable_pi_apply k).comp (S.measurable_grad j k)

/-- Local square integrability of the actual row trace follows from the
source gradient, on one common full-measure set for all radii and rows. -/
theorem c6SourceRowDivergence_locally_square_integrable {d : ℕ} {K : ℝ}
    {P : Measure (Coefficient d K)} {e : Vec d} {φ : Corrector P e}
    (S : FluxCorrector φ) :
    ∀ᵐ a ∂P, ∀ R : ℝ, 0 < R → ∀ j : Fin d,
      MemLp (fun x => c6SourceRowDivergence S a x j) 2
        (volume.restrict (ball 0 R)) := by
  filter_upwards [S.locally_square_integrable] with a ha
  intro R hR j
  exact memLp_finsetSum Finset.univ fun k _ => (ha R hR j k).2.eval k

/-- Summing the diagonal heat truncations converges to the literal source
row trace in local L². Both time cutoffs still tend independently to infinity. -/
theorem c6SourceRowDivergence_heat_limit {d : ℕ} {K : ℝ}
    {P : Measure (Coefficient d K)} {e : Vec d} {φ : Corrector P e}
    (S : FluxCorrector φ) :
    ∀ᵐ a ∂P, ∀ j : Fin d, ∀ R : ℕ,
      Tendsto (fun mn : ℕ × ℕ => eLpNorm
        (fun x => (∑ k : Fin d, iteratedAKMHeatGradientTruncation
          (centeredFlux φ a) mn.1 mn.2 j k k x) - c6SourceRowDivergence S a x j)
        2 (volume.restrict (ball 0 ((R : ℝ) + 1)))) atTop (𝓝 0) := by
  filter_upwards [S.heat_selected] with a ha
  intro j R
  let μ := volume.restrict (ball (0 : Vec d) ((R : ℝ) + 1))
  let E (mn : ℕ × ℕ) (k : Fin d) : Vec d → ℝ := fun x =>
    iteratedAKMHeatGradientTruncation (centeredFlux φ a) mn.1 mn.2 j k k x -
      S.grad a j k x k
  have hlim : Tendsto (fun mn => ∑ k : Fin d, eLpNorm (E mn k) 2 μ)
      atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using
      tendsto_finset_sum Finset.univ (fun k _ => (ha j k k R).2.2.2)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ => bot_le)
  intro mn
  have heq : (fun x => (∑ k : Fin d, iteratedAKMHeatGradientTruncation
      (centeredFlux φ a) mn.1 mn.2 j k k x) - c6SourceRowDivergence S a x j) =
      ∑ k : Fin d, E mn k := by
    funext x
    simp only [c6SourceRowDivergence, Finset.sum_apply, E, Finset.sum_sub_distrib]
  dsimp only
  rw [heq]
  exact eLpNorm_sum_le one_le_two

/-- The actual source row trace is divergence free in the weak sense. The
two spatial derivatives cancel by skewness and commutation of test derivatives;
no centered-flux identification is used. -/
theorem c6SourceRowDivergence_divergence_free {d : ℕ} {K : ℝ}
    {P : Measure (Coefficient d K)} {e : Vec d} {φ : Corrector P e}
    (S : FluxCorrector φ) :
    ∀ᵐ a ∂P, HasWeakDivergence Set.univ
      (c6SourceRowDivergence S a) (fun _ => 0) := by
  filter_upwards [c6SkewSourcePotential_weak_gradient S, S.heat_selected] with a hw hh
  have hdiv (j : Fin d) : ∀ᵐ x ∂(volume : Measure (Vec d)),
      ∑ k, S.grad a j k x k = c6SourceRowDivergence S a x j :=
    ae_of_all _ fun _ => rfl
  have hloc (j : Fin d) : LocallyIntegrable
      (fun x => c6SourceRowDivergence S a x j) volume :=
    c6_locallyIntegrable_rowDivergence hw hdiv j
  refine ⟨fun j => (hloc j).locallyIntegrableOn _, locallyIntegrableOn_zero, ?_⟩
  intro ψ hψ
  let I (j k : Fin d) : ℝ :=
    ∫ x, S.grad a j k x k * coordinateDerivative j ψ x
  have hI (j k : Fin d) : Integrable
      (fun x => S.grad a j k x k * coordinateDerivative j ψ x) volume :=
    c6_integrable_mul_test (locallyIntegrableOn_univ.mp (hw j k k).2.1)
      (c6_contDiff_coordinateDerivative hψ.1 j)
      (c6_hasCompactSupport_coordinateDerivative hψ.2.1 j)
  have hswap (j k : Fin d) : I j k = -I k j := by
    dsimp only [I]
    rw [← c6_integral_closedGradient_swap hw hψ.1 hψ.2.1 j k j,
      ← integral_neg]
    apply integral_congr_ae
    filter_upwards [c6_heatSelectedFluxGradient_ae_swap hh k j j] with x hx
    rw [hx]
    ring
  have hsum : (∑ j, ∑ k, I j k) = -(∑ j, ∑ k, I j k) := by
    calc
      (∑ j, ∑ k, I j k) = ∑ j, ∑ k, -I k j := by
        apply Finset.sum_congr rfl
        intro j _
        exact Finset.sum_congr rfl fun k _ => hswap j k
      _ = -(∑ j, ∑ k, I j k) := by
        simp only [Finset.sum_neg_distrib]
        rw [Finset.sum_comm]
  have hzero : (∑ j, ∑ k, I j k) = 0 := by linarith
  simp only [Measure.restrict_univ, zero_mul, integral_zero, neg_zero, dot, gradient]
  rw [integral_finsetSum _ fun j _ => c6_integrable_mul_test (hloc j)
    (c6_contDiff_coordinateDerivative hψ.1 j)
    (c6_hasCompactSupport_coordinateDerivative hψ.2.1 j)]
  have hrow (j : Fin d) :
      (∫ x, c6SourceRowDivergence S a x j * coordinateDerivative j ψ x) =
        ∑ k, I j k := by
    simp only [c6SourceRowDivergence, Finset.sum_mul]
    exact integral_finsetSum _ fun k _ => hI j k
  simpa only [hrow] using hzero

/-- The force-free physical dilation preserves the zero divergence of the
literal source trace, with the same coefficient-amplitude normalization. -/
theorem c6PhysicalSourceRowDivergence_divergence_free {d : ℕ} {K : ℝ}
    {P : Measure (Coefficient d K)} {e : Vec d} {φ : Corrector P e}
    (S : FluxCorrector φ) (r κ : ℝ) (hr : 0 < r) :
    ∀ᵐ a ∂P, HasWeakDivergence Set.univ
      (fun x => κ⁻¹ • c6SourceRowDivergence S a (r⁻¹ • x)) (fun _ => 0) := by
  filter_upwards [c6SourceRowDivergence_divergence_free S,
    c6SourceRowDivergence_locally_square_integrable S] with a hd hl
  exact hasWeakDivergence_zero_dilation (c6SourceRowDivergence S a)
    (fun R hR => memLp_pi_iff.mpr (hl R hR)) hd r⁻¹ κ⁻¹ (inv_pos.mpr hr)

private theorem c6_tendsto_testPairing_of_L2 {α ι : Type*} [MeasurableSpace α]
    {μ : Measure α} {l : Filter ι} {f : ι → α → ℝ} {g ψ : α → ℝ}
    (hf : ∀ i, MemLp (f i) 2 μ) (hg : MemLp g 2 μ) (hψ : MemLp ψ 2 μ)
    (hlim : Tendsto (fun i => eLpNorm (fun x => f i x - g x) 2 μ) l (𝓝 0)) :
    Tendsto (fun i => ∫ x, f i x * ψ x ∂μ) l (𝓝 (∫ x, g x * ψ x ∂μ)) := by
  have hLp : Tendsto (fun i => (hf i).toLp (f i)) l (𝓝 (hg.toLp g)) := by
    rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
    refine hlim.congr fun i => eLpNorm_congr_ae ?_
    filter_upwards [(hf i).coeFn_toLp, hg.coeFn_toLp] with x hx hy
    simp only [Pi.sub_apply, hx, hy]
  have hcont : Continuous (fun v : Lp ℝ 2 μ => ∫ x, v x * ψ x ∂μ) := by
    have heq : (fun v : Lp ℝ 2 μ => ∫ x, v x * ψ x ∂μ) =
        (fun v => inner ℝ v (hψ.toLp ψ)) := by
      funext v
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hψ.coeFn_toLp] with x hx
      simp only [hx, RCLike.inner_apply, conj_trivial, mul_comm]
    rw [heq]
    exact continuous_inner.comp (continuous_id.prodMk continuous_const)
  have hT := (hcont.tendsto _).comp hLp
  have hrw (v : α → ℝ) (hv : MemLp v 2 μ) :
      (∫ x, hv.toLp v x * ψ x ∂μ) = ∫ x, v x * ψ x ∂μ :=
    integral_congr_ae (hv.coeFn_toLp.mono fun x hx => by
      dsimp only
      rw [hx])
  simpa only [Function.comp_def, hrw] using hT

/-- The literal diagonal heat sums converge against every compactly supported
continuous spatial test to the actual source row trace. This is samplewise and
does not replace the selected gradient by an origin evaluation. -/
theorem c6SourceRowDivergence_tested_heat_limit {d : ℕ} {K : ℝ}
    {P : Measure (Coefficient d K)} {e : Vec d} {φ : Corrector P e}
    (S : FluxCorrector φ) :
    ∀ᵐ a ∂P, ∀ ψ : Vec d → ℝ, Continuous ψ → HasCompactSupport ψ → ∀ j : Fin d,
      Tendsto (fun mn : ℕ × ℕ => ∫ x,
        (∑ k : Fin d, iteratedAKMHeatGradientTruncation
          (centeredFlux φ a) mn.1 mn.2 j k k x) * ψ x)
        atTop (𝓝 (∫ x, c6SourceRowDivergence S a x j * ψ x)) := by
  filter_upwards [S.heat_selected, c6SourceRowDivergence_heat_limit S] with a hs hl
  intro ψ hψ hψc j
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Vec d)).mp
    hψc.isCompact.isBounded
  obtain ⟨N, hN⟩ := exists_nat_gt (Real.sqrt d * R)
  have hsupp : tsupport ψ ⊆ ball 0 ((N : ℝ) + 1) := by
    intro x hx
    have hxR := hR hx
    rw [Metric.mem_closedBall, dist_zero_right] at hxR
    change euclideanNorm (x - 0) < (N : ℝ) + 1
    rw [sub_zero]
    have hsq : euclideanSq x ≤ d * ‖x‖ ^ 2 := by
      unfold euclideanSq dot
      calc (∑ i, x i * x i) ≤ ∑ _i : Fin d, ‖x‖ ^ 2 := by
            apply Finset.sum_le_sum
            intro i _
            have hi := norm_le_pi_norm x i
            rw [Real.norm_eq_abs] at hi
            nlinarith [abs_nonneg (x i), abs_mul_abs_self (x i)]
        _ = d * ‖x‖ ^ 2 := by simp
    have hnorm : euclideanNorm x ≤ Real.sqrt d * ‖x‖ := by
      unfold euclideanNorm
      rw [← Real.sqrt_sq (norm_nonneg x), ← Real.sqrt_mul (Nat.cast_nonneg d)]
      exact Real.sqrt_le_sqrt hsq
    calc euclideanNorm x ≤ Real.sqrt d * ‖x‖ := hnorm
      _ ≤ Real.sqrt d * R := mul_le_mul_of_nonneg_left hxR (Real.sqrt_nonneg _)
      _ < (N : ℝ) + 1 := by linarith
  let U := ball (0 : Vec d) ((N : ℝ) + 1)
  have hT := c6_tendsto_testPairing_of_L2
    (fun mn : ℕ × ℕ => memLp_finsetSum Finset.univ
      (fun k _ => (hs j k k N).2.1 mn.1 mn.2))
    (memLp_finsetSum Finset.univ (fun k _ => (hs j k k N).2.2.1))
    ((hψ.memLp_of_hasCompactSupport hψc : MemLp ψ 2 volume).restrict (s := U)) (hl j N)
  have hrw (v : Vec d → ℝ) : (∫ x in U, v x * ψ x) = ∫ x, v x * ψ x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hzero : ψ x = 0 := image_eq_zero_of_notMem_tsupport fun hxs => hx (hsupp hxs)
    rw [hzero, mul_zero]
  dsimp only [U] at hrw
  simpa only [Finset.sum_apply, c6SourceRowDivergence, hrw] using hT

/-- Spatial null-set changes in the source flux preserve the literal heat
selection, including both integrability clauses of its iterated formula. -/
theorem c6_isHeatSelectedFluxGradient_congr_ae {d : ℕ} {g h : Vec d → Vec d}
    {G : Fin d → Fin d → Vec d → Vec d} (hgh : g =ᵐ[volume] h)
    (hG : IsHeatSelectedFluxGradient g G) : IsHeatSelectedFluxGradient h G := by
  have hdensity (t : ℝ) (j k l : Fin d) (x : Vec d) :
      akmHeatGradientDensity g t j k l x =ᵐ[volume]
        akmHeatGradientDensity h t j k l x := by
    filter_upwards [hgh] with y hy
    simp only [akmHeatGradientDensity, hy]
  have hspace (t : ℝ) (j k l : Fin d) (x : Vec d) :
      akmHeatGradientSpaceIntegral g t j k l x =
        akmHeatGradientSpaceIntegral h t j k l x :=
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

/-- The literal heat formula has a unique locally square-integrable gradient
limit, independently of the choice of potential representative. -/
theorem c6_isHeatSelectedFluxGradient_ae_unique {d : ℕ} {g : Vec d → Vec d}
    {F G : Fin d → Fin d → Vec d → Vec d}
    (hF : IsHeatSelectedFluxGradient g F) (hG : IsHeatSelectedFluxGradient g G) :
    ∀ᵐ x ∂(volume : Measure (Vec d)), ∀ j k l, F j k x l = G j k x l := by
  refine ae_all_iff.mpr fun j => ae_all_iff.mpr fun k => ae_all_iff.mpr fun l => ?_
  have hlocal (R : ℕ) : (fun x => F j k x l) =ᵐ[
      volume.restrict (ball 0 ((R : ℝ) + 1))] (fun x => G j k x l) := by
    have hFl := hF j k l R
    have hGl := hG j k l R
    exact tendstoInMeasure_ae_unique
      (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
        hFl.2.2.2)
      (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
        hGl.2.2.2)
  have h := (ae_restrict_iUnion_iff _ _).mpr hlocal
  simpa only [c6_heatSelectedCyclic_iUnion_ball_nat_eq_univ, Measure.restrict_univ] using h

/-- Two flux potentials selected for the same actual scalar corrector differ
only by spatial constants. No stationarity of either potential is assumed. -/
theorem c6_sourcePotentials_differ_by_constants {d : ℕ} (hd : 0 < d) {K : ℝ}
    {P : Measure (Coefficient d K)} {e : Vec d} {φ : Corrector P e}
    (S T : FluxCorrector φ) :
    ∀ᵐ a ∂P, ∀ j k, ∃ c : ℝ,
      (fun x => S.potential a x j k) =ᵐ[volume]
        (fun x => T.potential a x j k + c) := by
  filter_upwards [S.heat_selected, T.heat_selected, S.weak_gradient,
    T.weak_gradient] with a hS hT hwS hwT
  have hgrad := c6_isHeatSelectedFluxGradient_ae_unique hS hT
  intro j k
  have hweakT : HasWeakGradient Set.univ (fun x => T.potential a x j k)
      (S.grad a j k) := by
    apply hasWeakGradient_congr_ae isOpen_univ (hwT j k) (ae_eq_refl _)
    rw [Measure.restrict_univ]
    filter_upwards [hgrad] with x hx
    ext l
    exact (hx j k l).symm
  have hweak := hasWeakGradient_sub (hwS j k) hweakT
  have hloc : LocallyIntegrable (fun x => S.potential a x j k - T.potential a x j k)
      volume := locallyIntegrableOn_univ.mp (hweak ⟨0, hd⟩).1
  obtain ⟨c, hc⟩ := EinsteinRelation.ae_eq_const_of_zero_weak_gradient hloc
    (fun l ψ hψ => by
      have h := (hweak l).2.2 ψ hψ
      simpa only [Measure.restrict_univ, Pi.sub_apply, sub_self, zero_mul,
        integral_zero, neg_zero] using h)
  refine ⟨c, ?_⟩
  filter_upwards [hc] with x hx
  change S.potential a x j k - T.potential a x j k = c at hx
  linarith

/-- Translate the literal selected field with its full iterated-integrability
and local L² assertions; the composition is written explicitly for v4.35. -/
private theorem c6_isHeatSelectedFluxGradient_translate {d : ℕ}
    {g : Vec d → Vec d} {G : Fin d → Fin d → Vec d → Vec d}
    (h : IsHeatSelectedFluxGradient g G) (z : Vec d) :
    IsHeatSelectedFluxGradient (fun x => g (x + z))
      (fun j k x => G j k (x + z)) := by
  intro j k l R
  obtain ⟨N, hN⟩ := exists_nat_gt ((R : ℝ) + 1 + euclideanNorm z)
  have hRS : (R : ℝ) + 1 + euclideanNorm z ≤ (N : ℝ) + 1 := by linarith
  have hsub : ball z ((R : ℝ) + 1) ⊆ ball (0 : Vec d) ((N : ℝ) + 1) := by
    intro x hx
    have htri := TimeChange.euclideanNorm_add_le (x - z) z
    rw [sub_add_cancel] at htri
    change euclideanNorm (x - z) < (R : ℝ) + 1 at hx
    change euclideanNorm (x - 0) < (N : ℝ) + 1
    rw [sub_zero]
    linarith
  have hm := Measure.restrict_mono_set (volume : Measure (Vec d)) hsub
  have hmp := measurePreserving_add_center_ball z ((R : ℝ) + 1)
  obtain ⟨hi, hT, hG, hlim⟩ := h j k l N
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro m n
    filter_upwards [hmp.quasiMeasurePreserving.ae (ae_mono hm (hi m n))] with x hx
    refine ⟨?_, ?_⟩
    · filter_upwards [hx.1] with t ht
      have hc := ((measurePreserving_add_right (volume : Measure (Vec d)) z).integrable_comp_emb
        (Homeomorph.addRight z).measurableEmbedding).mpr ht
      change Integrable (fun y => akmHeatGradientDensity g t j k l (x + z) (y + z))
        volume at hc
      simpa only [← akmHeatGradientDensity_translation] using hc
    · simpa only [akmHeatGradientSpaceIntegral_translation] using hx.2
  · intro m n
    simpa only [Function.comp_def, iteratedAKMHeatGradientTruncation_translation] using
      ((hT m n).mono_measure hm).comp_measurePreserving hmp
  · exact (hG.mono_measure hm).comp_measurePreserving hmp
  · apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun _ => zero_le) ?_
    intro mn
    simpa only [iteratedAKMHeatGradientTruncation_translation] using
      eLpNorm_add_center_ball_le
        (fun x => iteratedAKMHeatGradientTruncation g mn.1 mn.2 j k l x - G j k x l)
        z ((R : ℝ) + 1) ((N : ℝ) + 1) hRS ((hT mn.1 mn.2).sub hG).aestronglyMeasurable

/-- The literal heat selection transfers the scalar corrector's lattice
stationarity to the actual source flux gradient, without origin evaluation. -/
theorem c6_sourceFluxGradient_lattice_stationary {d : ℕ} {K : ℝ}
    {P : Measure (Coefficient d K)} {e : Vec d} {φ : Corrector P e}
    (S : FluxCorrector φ) (hP : LawHypotheses P) (z : LatticeIndex d) :
    ∀ᵐ a ∂P, ∀ᵐ x ∂(volume : Measure (Vec d)), ∀ j k l,
      S.grad a j k (x + latticeShift z) l =
        S.grad (translateCoefficient (latticeShift z) a) j k x l := by
  have hpres : MeasurePreserving (translateCoefficient (latticeShift z)) P P :=
    ⟨measurable_translateCoefficient _, hP.2.1 z⟩
  filter_upwards [S.heat_selected, hpres.quasiMeasurePreserving.ae S.heat_selected,
    φ.stationary z] with a hS hT hφ
  have hflux : (fun x => centeredFlux φ a (x + latticeShift z)) =ᵐ[volume]
      centeredFlux φ (translateCoefficient (latticeShift z) a) := by
    filter_upwards [hφ] with x hx
    simp only [centeredFlux, hx]
    congr 2
    exact congrArg a (add_comm x (latticeShift z))
  exact c6_isHeatSelectedFluxGradient_ae_unique
    (c6_isHeatSelectedFluxGradient_congr_ae hflux
      (c6_isHeatSelectedFluxGradient_translate hS (latticeShift z))) hT

/-- Lattice stationarity also holds for the actual source row trace. -/
theorem c6SourceRowDivergence_lattice_stationary {d : ℕ} {K : ℝ}
    {P : Measure (Coefficient d K)} {e : Vec d} {φ : Corrector P e}
    (S : FluxCorrector φ) (hP : LawHypotheses P) (z : LatticeIndex d) :
    ∀ᵐ a ∂P, ∀ᵐ x ∂(volume : Measure (Vec d)),
      c6SourceRowDivergence S a (x + latticeShift z) =
        c6SourceRowDivergence S (translateCoefficient (latticeShift z) a) x := by
  filter_upwards [c6_sourceFluxGradient_lattice_stationary S hP z] with a ha
  filter_upwards [ha] with x hx
  funext j
  exact Finset.sum_congr rfl fun k _ => hx j k k

/-- Subtraction of homogeneous weak divergences, including the actual test
integrability on all of space. -/
private theorem c6_hasWeakDivergence_sub_zero {d : ℕ} {F G : Vec d → Vec d}
    (hF : HasWeakDivergence Set.univ F (fun _ => 0))
    (hG : HasWeakDivergence Set.univ G (fun _ => 0)) :
    HasWeakDivergence Set.univ (fun x => F x - G x) (fun _ => 0) := by
  refine ⟨fun i => (hF.1 i).sub (hG.1 i), locallyIntegrableOn_zero, ?_⟩
  intro ψ hψ
  have hint (V : Vec d → Vec d)
      (hV : ∀ i, LocallyIntegrableOn (fun x => V x i) Set.univ volume) :
      Integrable (fun x => dot (V x) (gradient ψ x)) volume := by
    exact integrable_finsetSum _ fun i _ =>
      c6_integrable_mul_test (locallyIntegrableOn_univ.mp (hV i))
        (c6_contDiff_coordinateDerivative hψ.1 i)
        (c6_hasCompactSupport_coordinateDerivative hψ.2.1 i)
  have heq : (fun x => dot (F x - G x) (gradient ψ x)) =
      (fun x => dot (F x) (gradient ψ x) - dot (G x) (gradient ψ x)) := by
    funext x
    simp only [dot, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
  have hF0 := hF.2.2 ψ hψ
  have hG0 := hG.2.2 ψ hψ
  simp only [Measure.restrict_univ, zero_mul, integral_zero, neg_zero] at hF0 hG0 ⊢
  rw [heq, integral_sub (hint F hF.1) (hint G hG.1), hF0, hG0, sub_self]

/-- Constant vector fields have zero weak divergence; compact support of the
test supplies all integrability, without global integrability of the constant. -/
private theorem c6_hasWeakDivergence_const {d : ℕ} (c : Vec d) :
    HasWeakDivergence Set.univ (fun _ => c) (fun _ => 0) := by
  refine ⟨fun _ => locallyIntegrableOn_const _, locallyIntegrableOn_zero, ?_⟩
  intro ψ hψ
  have hD (i : Fin d) : Integrable (coordinateDerivative i ψ) volume :=
    (c6_contDiff_coordinateDerivative hψ.1 i).continuous.integrable_of_hasCompactSupport
      (c6_hasCompactSupport_coordinateDerivative hψ.2.1 i)
  have h0 (i : Fin d) : ∫ x, coordinateDerivative i ψ x = 0 := by
    have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      (μ := (volume : Measure (Vec d))) (f := fun _ => (1 : ℝ)) (g := ψ)
      (v := unitVector i)
      (by exact ((hD i).sub (hD i)).congr (ae_of_all _ fun x => by
        simp only [sub_self, fderiv_const_apply, zero_apply, zero_mul, Pi.zero_apply]))
      (by change Integrable (fun x => 1 * coordinateDerivative i ψ x) volume
          simpa only [one_mul] using hD i)
      (by simpa only [one_mul] using hψ.1.continuous.integrable_of_hasCompactSupport hψ.2.1)
      (fun _ _ => differentiableAt_const _) (fun x _ => hψ.1.differentiable (by simp) x)
    simpa only [one_mul, fderiv_const_apply, zero_apply,
      zero_mul, integral_zero, neg_zero, coordinateDerivative] using h
  simp only [Measure.restrict_univ, dot, gradient, zero_mul, integral_zero, neg_zero]
  rw [integral_finsetSum _ fun i _ => (hD i).const_mul (c i)]
  exact Finset.sum_eq_zero fun i _ => by rw [integral_const_mul, h0 i, mul_zero]

/-- The actual centered source flux is weakly divergence free: centering
subtracts precisely the constant mean flux from the scalar harmonic equation. -/
theorem c6_centeredFlux_divergence_free {d : ℕ} {K : ℝ}
    {P : Measure (Coefficient d K)} {e : Vec d} (φ : Corrector P e) :
    ∀ᵐ a ∂P, HasWeakDivergence Set.univ (centeredFlux φ a) (fun _ => 0) := by
  filter_upwards [φ.harmonic] with a ha
  exact c6_hasWeakDivergence_sub_zero ha (c6_hasWeakDivergence_const (meanFlux φ))

/-- The literal heat-selected trace defect is divergence free before any
identification of that trace with the centered source flux. -/
theorem c6_sourceTraceDefect_divergence_free {d : ℕ} {K : ℝ}
    {P : Measure (Coefficient d K)} {e : Vec d} {φ : Corrector P e}
    (S : FluxCorrector φ) :
    ∀ᵐ a ∂P, HasWeakDivergence Set.univ
      (fun x => centeredFlux φ a x - c6SourceRowDivergence S a x) (fun _ => 0) := by
  filter_upwards [c6_centeredFlux_divergence_free φ,
    c6SourceRowDivergence_divergence_free S] with a hg htrace
  exact c6_hasWeakDivergence_sub_zero hg htrace

/-- Centering on the actual AKM unit cell has zero expectation, with
integrability of the cell integral inherited from the actual scalar corrector. -/
theorem c6_centeredFlux_cell_mean_zero {d : ℕ} {K : ℝ}
    {P : Measure (Coefficient d K)} [IsProbabilityMeasure P] {e : Vec d}
    (φ : Corrector P e) :
    Integrable (fun a => ∫ x in unitCell d, centeredFlux φ a x ∂volume) P ∧
      (∫ a, ∫ x in unitCell d, centeredFlux φ a x ∂volume ∂P) = 0 := by
  have hvol := volume_akm_unitCell d
  have : IsFiniteMeasure (volume.restrict (unitCell d)) :=
    ⟨by rw [Measure.restrict_apply_univ, hvol]; exact ENNReal.one_lt_top⟩
  have hcell : unitCell d ⊆ Set.Icc (fun _ => (-1 / 2 : ℝ)) (fun _ => (1 / 2 : ℝ)) := by
    intro x hx
    exact ⟨fun i => (hx i (Set.mem_univ i)).1, fun i => (hx i (Set.mem_univ i)).2.le⟩
  have heq : (fun a => ∫ x in unitCell d, centeredFlux φ a x ∂volume) =ᵐ[P]
      (fun a => (∫ x in unitCell d, (a x).mulVec (e + φ.grad a x) ∂volume) - meanFlux φ) := by
    filter_upwards [φ.harmonic] with a ha
    have hi : IntegrableOn (fun x => (a x).mulVec (e + φ.grad a x)) (unitCell d) volume := by
      apply integrable_pi_iff.mpr
      intro i
      exact ((locallyIntegrableOn_univ.mp (ha.1 i)).integrableOn_isCompact
        isCompact_Icc).mono_set hcell
    rw [show (fun x => centeredFlux φ a x) =
      (fun x => (a x).mulVec (e + φ.grad a x) - meanFlux φ) from rfl,
      integral_sub hi (integrable_const _), integral_const]
    simp only [Measure.real, Measure.restrict_apply_univ, hvol, ENNReal.toReal_one, one_smul]
  have hi := φ.cell_integrable.sub (integrable_const (meanFlux φ))
  refine ⟨hi.congr heq.symm, ?_⟩
  rw [integral_congr_ae heq, integral_sub φ.cell_integrable (integrable_const _),
    integral_const, probReal_univ, one_smul]
  exact sub_self _

/- SUPERVISOR EXACT TARGET; replace with its proved declaration.
theorem sublinear_pair_smooth_flux_representatives :
∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
  (Q : EnvironmentLaw d D.ellipticity D.dependenceRange), HasSmoothBounds D Q →
∃ S : Fin d → FieldPair d → Vec d → Mat d,
  ∀ᵐ ω ∂reducedLaw Q, ∀ i : Fin d,
    (∀ j k : Fin d, ContDiff ℝ (⊤ : ℕ∞) (fun x => S i ω x j k)) ∧
    (∀ x, (S i ω x).transpose = -(S i ω x)) ∧
    ∀ᵐ x ∂(volume : Measure (Vec d)), ∀ j : Fin d,
      (∑ k : Fin d, fderiv ℝ (fun y => S i ω y k j) x (unitVector k)) =
        ((ω.1 x).mulVec (unitVector i +
          WithLp.ofLp (correctorGradient Q i (translate x ω)))) j -
            homogenizedCoefficient Q j i := by
-/

end EinsteinFull.Blueprint
