import EinsteinRelation.Correctors.HeatGradientConvolution
import EinsteinRelation.Correctors.HeatSelectedSkewGaugeUniqueness
import EinsteinRelation.External.AKMCorrectorOscillation

/-!
# Closedness of the heat-selected flux-corrector gradient

Source: `paper/main.tex:740-756`, AKM (6.7). The heat-kernel Hessian is symmetric,
so the cyclic sums of the literal truncations vanish; their local `L²` limit, the
selected gradient, has vanishing cyclic sums almost everywhere.
-/
open MeasureTheory Filter Topology
namespace EinsteinRelation.Correctors
open External.AKM HeatSelectedSkewMeaning

/-- The mixed coordinate Hessian of the heat kernel is symmetric in its two indices. -/
theorem heatSelectedCyclic_coordinateDerivative_comm {d : ℕ} (t : ℝ) (ht : 0 < t)
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
theorem heatSelectedCyclic_density_sum {d : ℕ} (g : Vec d → Vec d) (t : ℝ) (ht : 0 < t)
    (j k l : Fin d) (x y : Vec d) :
    akmHeatGradientDensity g t j k l x y + akmHeatGradientDensity g t k l j x y +
      akmHeatGradientDensity g t l j k x y = 0 := by
  rw [akmHeatGradientDensity_eq_mixedHessian g t ht, akmHeatGradientDensity_eq_mixedHessian g t ht,
    akmHeatGradientDensity_eq_mixedHessian g t ht]
  linear_combination (g y k) * heatSelectedCyclic_coordinateDerivative_comm t ht l j (x - y)
    - (g y j) * heatSelectedCyclic_coordinateDerivative_comm t ht l k (x - y)
    + (g y l) * heatSelectedCyclic_coordinateDerivative_comm t ht j k (x - y)

/-- On a window of positive times, the cyclic sum of the three iterated truncations
vanishes, provided the integrability clauses hold. -/
theorem heatSelectedCyclic_truncation_sum {d : ℕ} (g : Vec d → Vec d) (m n : ℕ)
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
    simp only [heatSelectedCyclic_density_sum g t hpos j k l x, integral_zero] at key
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
theorem heatSelectedCyclic_iUnion_ball_nat_eq_univ {d : ℕ} :
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
theorem heatSelectedCyclic_of_L2_limits {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (T₁ T₂ T₃ : ℕ × ℕ → Ω → ℝ) (G₁ G₂ G₃ : Ω → ℝ)
    (hT₁ : ∀ n, MemLp (T₁ n) 2 μ) (hT₂ : ∀ n, MemLp (T₂ n) 2 μ)
    (hT₃ : ∀ n, MemLp (T₃ n) 2 μ)
    (hG₁ : MemLp G₁ 2 μ) (hG₂ : MemLp G₂ 2 μ) (hG₃ : MemLp G₃ 2 μ)
    (hc₁ : Tendsto (fun n => eLpNorm (T₁ n - G₁) 2 μ) atTop (𝓝 0))
    (hc₂ : Tendsto (fun n => eLpNorm (T₂ n - G₂) 2 μ) atTop (𝓝 0))
    (hc₃ : Tendsto (fun n => eLpNorm (T₃ n - G₃) 2 μ) atTop (𝓝 0))
    (hsum : ∀ n, ∀ᵐ x ∂μ, T₁ n x + T₂ n x + T₃ n x = 0) :
    ∀ᵐ x ∂μ, G₁ x + G₂ x + G₃ x = 0 := by
  have hf : MemLp (fun x => G₁ x + G₂ x + G₃ x) 2 μ := (hG₁.add hG₂).add hG₃
  have hT : ∀ n, MemLp (fun x => T₁ n x + T₂ n x + T₃ n x) 2 μ :=
    fun n => ((hT₁ n).add (hT₂ n)).add (hT₃ n)
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
      have m₁ : AEStronglyMeasurable (T₁ n - G₁) μ := ((hT₁ n).sub hG₁).aestronglyMeasurable
      have m₂ : AEStronglyMeasurable (T₂ n - G₂) μ := ((hT₂ n).sub hG₂).aestronglyMeasurable
      have m₃ : AEStronglyMeasurable (T₃ n - G₃) μ := ((hT₃ n).sub hG₃).aestronglyMeasurable
      rw [e]
      calc eLpNorm ((T₁ n - G₁) + (T₂ n - G₂) + (T₃ n - G₃)) 2 μ
          ≤ eLpNorm ((T₁ n - G₁) + (T₂ n - G₂)) 2 μ + eLpNorm (T₃ n - G₃) 2 μ :=
            eLpNorm_add_le (m₁.add m₂) m₃ one_le_two
        _ ≤ (eLpNorm (T₁ n - G₁) 2 μ + eLpNorm (T₂ n - G₂) 2 μ) + eLpNorm (T₃ n - G₃) 2 μ := by
            gcongr
            exact eLpNorm_add_le m₁ m₂ one_le_two
        _ = eLpNorm (T₁ n - G₁) 2 μ + (eLpNorm (T₂ n - G₂) 2 μ + eLpNorm (T₃ n - G₃) 2 μ) :=
            add_assoc _ _ _
    have hlim := hc₁.add (hc₂.add hc₃)
    rw [add_zero, add_zero] at hlim
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun n => zero_le _) hbd
  exact ae_eq_of_common_L2_limit μ (fun n x => T₁ n x + T₂ n x + T₃ n x)
    (fun x => G₁ x + G₂ x + G₃ x) 0 hT hf MemLp.zero hTf hTg

/-- The heat-selected flux-corrector gradient is closed: its cyclic sum vanishes
almost everywhere. Source: AKM (6.7), `paper/main.tex:740-756`. -/
theorem isHeatSelectedFluxGradient_cyclic {d : ℕ} {g : Vec d → Vec d}
    {G : Fin d → Fin d → Vec d → Vec d} (h : IsHeatSelectedFluxGradient g G)
    (j k l : Fin d) :
    ∀ᵐ x ∂(volume : Measure (Vec d)), G j k x l + G k l x j + G l j x k = 0 := by
  have hball : ∀ R : ℕ, ∀ᵐ x ∂(volume.restrict (ball (0 : Vec d) ((R : ℝ) + 1))),
      G j k x l + G k l x j + G l j x k = 0 := by
    intro R
    obtain ⟨hD₁, hT₁, hG₁, hC₁⟩ := h j k l R
    obtain ⟨hD₂, hT₂, hG₂, hC₂⟩ := h k l j R
    obtain ⟨hD₃, hT₃, hG₃, hC₃⟩ := h l j k R
    have hae : ∀ᵐ x ∂(volume.restrict (ball (0 : Vec d) ((R : ℝ) + 1))), ∀ m n : ℕ,
        iteratedAKMHeatGradientTruncation g m n j k l x +
          iteratedAKMHeatGradientTruncation g m n k l j x +
          iteratedAKMHeatGradientTruncation g m n l j k x = 0 := by
      rw [ae_all_iff]
      intro m
      rw [ae_all_iff]
      intro n
      filter_upwards [hD₁ m n, hD₂ m n, hD₃ m n] with x hx₁ hx₂ hx₃
      exact heatSelectedCyclic_truncation_sum g m n j k l x hx₁.1 hx₂.1 hx₃.1 hx₁.2 hx₂.2 hx₃.2
    exact heatSelectedCyclic_of_L2_limits (volume.restrict (ball (0 : Vec d) ((R : ℝ) + 1)))
      (fun mn x => iteratedAKMHeatGradientTruncation g mn.1 mn.2 j k l x)
      (fun mn x => iteratedAKMHeatGradientTruncation g mn.1 mn.2 k l j x)
      (fun mn x => iteratedAKMHeatGradientTruncation g mn.1 mn.2 l j k x)
      (fun x => G j k x l) (fun x => G k l x j) (fun x => G l j x k)
      (fun n => hT₁ n.1 n.2) (fun n => hT₂ n.1 n.2) (fun n => hT₃ n.1 n.2)
      hG₁ hG₂ hG₃ hC₁ hC₂ hC₃ (fun n => hae.mono fun x hx => hx n.1 n.2)
  have hu := (ae_restrict_iUnion_iff _ _).mpr hball
  rwa [heatSelectedCyclic_iUnion_ball_nat_eq_univ, Measure.restrict_univ] at hu

end EinsteinRelation.Correctors
