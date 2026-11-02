import EinsteinRelation.Correctors.AKMParabolicIntegrability
import EinsteinRelation.Correctors.SpatialWeakProduct
import EinsteinRelation.TimeChange.EuclideanTransport

/-! # The equation for two locally agreeing coefficient fields

Source: `paper/main.tex:807–830`. If two coefficient fields agree on the
spatial domain, subtracting their actual parabolic solutions gives a
homogeneous parabolic equation with their gradient difference. Every test
integral is integrable; subtraction does not use the total-integral zero
convention. This is the PDE entering the paired weighted energy argument.
-/

open MeasureTheory Filter
open scoped Topology

namespace EinsteinRelation.Correctors

open External.AKM Environment.AKMTestIntegralSupport

/-- Subtracting two actual weak partial derivatives preserves the weak
equation and local integrability. Source: `paper/main.tex:812–830`. -/
theorem hasWeakPartialDerivative_sub {d : ℕ} {U : Set (Vec d)} {j : Fin d}
    {f₁ f₂ g₁ g₂ : Vec d → ℝ}
    (h₁ : HasWeakPartialDerivative U j f₁ g₁)
    (h₂ : HasWeakPartialDerivative U j f₂ g₂) :
    HasWeakPartialDerivative U j (fun x => f₁ x - f₂ x) (fun x => g₁ x - g₂ x) := by
  refine ⟨h₁.1.sub h₂.1, h₁.2.1.sub h₂.2.1, ?_⟩
  intro ψ hψ
  have hdψ : IsSpatialTest U (coordinateDerivative j ψ) := by
    refine ⟨(contDiff_infty_iff_fderiv.mp hψ.1).2.clm_apply contDiff_const,
      hψ.2.1.fderiv_apply ℝ (unitVector j), ?_⟩
    apply Set.Subset.trans ?_ hψ.2.2
    apply closure_minimal ?_ isClosed_closure
    intro x hx
    by_contra hxs
    exact hx (by simp [coordinateDerivative, fderiv_of_notMem_tsupport (𝕜 := ℝ) hxs])
  simp only [sub_mul]
  rw [integral_sub (integrableOn_mul_spatialTest h₁.1 hdψ)
      (integrableOn_mul_spatialTest h₂.1 hdψ),
    integral_sub (integrableOn_mul_spatialTest h₁.2.1 hψ)
      (integrableOn_mul_spatialTest h₂.2.1 hψ), h₁.2.2 ψ hψ, h₂.2.2 ψ hψ]
  ring

/-- The actual gradient of the difference is the difference of gradients.
Source: `paper/main.tex:812–830`. -/
theorem hasWeakGradient_sub {d : ℕ} {U : Set (Vec d)}
    {f₁ f₂ : Vec d → ℝ} {G₁ G₂ : Vec d → Vec d}
    (h₁ : HasWeakGradient U f₁ G₁) (h₂ : HasWeakGradient U f₂ G₂) :
    HasWeakGradient U (fun x => f₁ x - f₂ x) (fun x => G₁ x - G₂ x) := by
  intro j
  exact hasWeakPartialDerivative_sub (h₁ j) (h₂ j)

/-- Changing a coefficient field outside the spatial domain leaves the
parabolic weak equation unchanged. Source: `paper/main.tex:807–817`. -/
theorem parabolicSolution_of_coefficient_eqOn {d : ℕ} {K : ℝ}
    {A₁ A₂ : Coefficient d K} {I : Set ℝ} {U : Set (Vec d)}
    (hI : MeasurableSet I) (hU : MeasurableSet U)
    (hA : Set.EqOn A₁ A₂ U) {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (h : IsParabolicSolution A₁ I U u G) : IsParabolicSolution A₂ I U u G := by
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, ?_⟩
  intro ψ hψ hψc hψU
  calc
    _ = ∫ z in I ×ˢ U, -(u z) * fderiv ℝ ψ z (1, 0) +
        dot ((A₁ z.2).mulVec (G z))
          (fun j => fderiv ℝ ψ z (0, unitVector j)) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (hI.prod hU)] with z hz
      rw [hA hz.2]
    _ = 0 := h.2.2.2.2 ψ hψ hψc hψU

/-- Two homogeneous parabolic solutions with the same coefficient have a
homogeneous difference. Source: `paper/main.tex:812–830`. -/
theorem parabolicSolution_sub {d : ℕ} {K : ℝ} (hK : 0 < K)
    {A : Coefficient d K} {I : Set ℝ} {U : Set (Vec d)}
    {u₁ u₂ : ℝ × Vec d → ℝ} {G₁ G₂ : ℝ × Vec d → Vec d}
    (h₁ : IsParabolicSolution A I U u₁ G₁)
    (h₂ : IsParabolicSolution A I U u₂ G₂) :
    IsParabolicSolution A I U (fun z => u₁ z - u₂ z) (fun z => G₁ z - G₂ z) := by
  have hGm := h₁.2.1.sub h₂.2.1
  have hnormm : AEStronglyMeasurable (fun z => euclideanNorm (G₁ z - G₂ z))
      (volume.restrict (I ×ˢ U)) := by
    have hc : Continuous (fun v : Vec d => euclideanNorm v) := by
      simp_rw [TimeChange.euclideanNorm_eq_norm_toLp]
      exact (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin d => ℝ)).norm
    exact hc.comp_aestronglyMeasurable hGm
  have hnorm : MemLp (fun z => euclideanNorm (G₁ z - G₂ z)) 2
      (volume.restrict (I ×ˢ U)) := by
    apply (h₁.2.2.1.add h₂.2.2.1).of_le hnormm
    exact Eventually.of_forall fun z => by
      simp only [Pi.add_apply, TimeChange.euclideanNorm_eq_norm_toLp, norm_norm,
        Real.norm_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
      exact norm_sub_le _ _
  refine ⟨h₁.1.sub h₂.1, hGm, hnorm, ?_, ?_⟩
  · filter_upwards [h₁.2.2.2.1, h₂.2.2.2.1] with t ht₁ ht₂
    exact hasWeakGradient_sub ht₁ ht₂
  · intro ψ hψ hψc hψU
    have htest₁ := parabolicSolution_test_integrable hK A h₁ hψ hψc
    have htest₂ := parabolicSolution_test_integrable hK A h₂ hψ hψc
    have hsplit (z : ℝ × Vec d) :
        -(u₁ z - u₂ z) * fderiv ℝ ψ z (1, 0) +
          dot ((A z.2).mulVec (G₁ z - G₂ z))
            (fun j => fderiv ℝ ψ z (0, unitVector j)) =
        (-(u₁ z) * fderiv ℝ ψ z (1, 0) +
          dot ((A z.2).mulVec (G₁ z)) (fun j => fderiv ℝ ψ z (0, unitVector j))) -
        (-(u₂ z) * fderiv ℝ ψ z (1, 0) +
          dot ((A z.2).mulVec (G₂ z)) (fun j => fderiv ℝ ψ z (0, unitVector j))) := by
      simp only [Matrix.mulVec_sub, dot, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
      ring
    simp_rw [hsplit]
    rw [integral_sub htest₁ htest₂, h₁.2.2.2.2 ψ hψ hψc hψU,
      h₂.2.2.2.2 ψ hψ hψc hψU, sub_self]

/-- The homogeneous paired equation follows from local coefficient
agreement, rather than being an extra PDE premise.
Source: `paper/main.tex:807–830`. -/
theorem paired_parabolicSolution {d : ℕ} {K : ℝ} (hK : 0 < K)
    {A₁ A₂ : Coefficient d K} {I : Set ℝ} {U : Set (Vec d)}
    (hI : MeasurableSet I) (hU : MeasurableSet U) (hA : Set.EqOn A₁ A₂ U)
    {u₁ u₂ : ℝ × Vec d → ℝ} {G₁ G₂ : ℝ × Vec d → Vec d}
    (h₁ : IsParabolicSolution A₁ I U u₁ G₁)
    (h₂ : IsParabolicSolution A₂ I U u₂ G₂) :
    IsParabolicSolution A₁ I U (fun z => u₁ z - u₂ z) (fun z => G₁ z - G₂ z) :=
  parabolicSolution_sub hK h₁ (parabolicSolution_of_coefficient_eqOn hI hU hA.symm h₂)


/-- At positive time, the continuous source representative can be paired
integrably with every compact spatial test. Source:
`paper/main.tex:807–817`; AKM (9.1), (9.2), pp. 347–349. -/
theorem semigroupSolution_test_integrable {d : ℕ} {K : ℝ}
    {A : Coefficient d K} {g : Vec d → Vec d}
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (h : IsSemigroupSolution A g u G) {t : ℝ} (ht : 0 < t)
    {ψ : Vec d → ℝ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) :
    Integrable (fun x => u (t, x) * ψ x) volume := by
  have hu : Continuous (fun x => u (t, x)) :=
    h.1.comp_continuous (continuous_const.prodMk continuous_id)
      (fun _ => ⟨ht, Set.mem_univ _⟩)
  exact (hu.mul hψ).integrable_of_hasCompactSupport hψc.mul_left

/-- Agreement of the initial vector fields on the test domain gives zero
local initial trace of the paired flow, as an actual distributional limit.
Source: `paper/main.tex:807–817`. -/
theorem paired_semigroupSolution_initial_zero {d : ℕ} {K : ℝ}
    {A₁ A₂ : Coefficient d K} {g₁ g₂ : Vec d → Vec d}
    {u₁ u₂ : ℝ × Vec d → ℝ} {G₁ G₂ : ℝ × Vec d → Vec d}
    (h₁ : IsSemigroupSolution A₁ g₁ u₁ G₁)
    (h₂ : IsSemigroupSolution A₂ g₂ u₂ G₂)
    {U : Set (Vec d)} (hg : Set.EqOn g₁ g₂ U)
    {ψ : Vec d → ℝ} (hψ : IsSpatialTest U ψ) :
    Tendsto (fun t => ∫ x, (u₁ (t, x) - u₂ (t, x)) * ψ x ∂volume)
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := by
  have hψall : IsSpatialTest Set.univ ψ := ⟨hψ.1, hψ.2.1, Set.subset_univ _⟩
  have hdata : (∫ x, dot (g₁ x) (gradient ψ x) ∂volume) =
      ∫ x, dot (g₂ x) (gradient ψ x) ∂volume := by
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      dsimp only
      by_cases hx : x ∈ U
      · rw [hg hx]
      · have hxs : x ∉ tsupport ψ := fun h => hx (hψ.2.2 h)
        simp [dot, gradient, coordinateDerivative, fderiv_of_notMem_tsupport (𝕜 := ℝ) hxs]
  have hlim := (h₁.2.2 ψ hψall).sub (h₂.2.2 ψ hψall)
  rw [hdata, sub_self] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  simp only [Set.mem_Ioi] at ht
  simp only [sub_mul]
  exact (integral_sub
    (semigroupSolution_test_integrable h₁ ht hψ.1.continuous hψ.2.1)
    (semigroupSolution_test_integrable h₂ ht hψ.1.continuous hψ.2.1)).symm

end EinsteinRelation.Correctors
