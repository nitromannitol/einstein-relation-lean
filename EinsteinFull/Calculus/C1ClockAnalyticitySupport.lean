import EinsteinFull.Calculus.ComplexGradientAnalyticSupport
import EinsteinFull.Calculus.ComplexEndpointAnalyticSupport
import EinsteinFull.Frozen.ReducedCoefficientObservation
import EinsteinFull.Frozen.EndpointWeakFlux

/-! Actual shared clock gradient and flux, including force zero. -/

open MeasureTheory Filter
open scoped NNReal

noncomputable section
namespace EinsteinFull.ClockAnalyticity
open EinsteinRelation

variable {d : ℕ} {Λ R : ℝ} {Q : EnvironmentLaw d Λ R} {i : Fin d}

/-- The anisotropic forward weak flux as an actual L2 class. -/
def flux (Q : EnvironmentLaw d Λ R)
    (G : Fin d → Lp ℂ 2 (reducedLaw Q)) (j : Fin d) : Lp ℂ 2 (reducedLaw Q) :=
  ∑ k, (complexCoefficientMul Q j k (G k) -
    (homogenizedCoefficient Q j k : ℂ) • G k)

/-- The multiplier formula agrees with every actual coefficient observation. -/
theorem fluxCoe (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q))
    (ha : IsReducedCoefficientObservation Q a)
    (G : Fin d → Lp ℂ 2 (reducedLaw Q)) (j : Fin d) :
    (flux Q G j : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
      fun ω => ∑ k, (a j k ω - (homogenizedCoefficient Q j k : ℂ)) * G k ω := by
  have he : (flux Q G j : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
      fun ω => ∑ k, (complexCoefficientMul Q j k (G k) -
        (homogenizedCoefficient Q j k : ℂ) • G k) ω :=
    Lp.coeFn_fun_finsetSum _ _
  filter_upwards [he, ae_all_iff.mpr (fun k => complexCoefficientMul_coe Q j k (G k)),
    ae_all_iff.mpr (fun k => Lp.coeFn_sub (complexCoefficientMul Q j k (G k))
      ((homogenizedCoefficient Q j k : ℂ) • G k)),
    ae_all_iff.mpr (fun k => Lp.coeFn_smul (homogenizedCoefficient Q j k : ℂ) (G k)),
    ae_all_iff.mpr (fun k => ha j k)] with ω he hm hd hs haω
  rw [he]
  apply Finset.sum_congr rfl
  intro k _
  simp only [hd, hm, hs, haω, Pi.smul_apply, smul_eq_mul, sub_mul, Pi.sub_apply]

/-- The clock weak-flux predicate commutes with multiplication by any force. -/
theorem weakFluxSmul (hd : 2 ≤ d) (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q))
    {ζ : ℂ} {U : Lp ℂ 2 (reducedLaw Q)} {G J : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (h : IsEndpointWeakFlux hd Q (.inr false) ζ a U G J) (c : ℂ) :
    IsEndpointWeakFlux hd Q (.inr false) ζ a (c • U)
      (fun j => c • G j) (fun j => c • J j) := by
  refine ⟨fun j => (h.1 j).smul c, fun j => ?_⟩
  filter_upwards [Lp.coeFn_smul c (J j), h.2 j,
    ae_all_iff.mpr (fun k => Lp.coeFn_smul c (G k))] with ω hJ hf hG
  simp only [hJ, hf, hG, Pi.smul_apply, smul_eq_mul, sub_zero]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- The shared gradient is defined at every time, without division by force. -/
def gradient
    {P : ℂ → ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : ∀ ζ, IsComplexEnvironmentSemigroup Q i ζ (P ζ))
    (μ : Lp ℂ 2 (reducedLaw Q)) (ζ : ℂ) (r : ℝ≥0) (j : Fin d) :
    Lp ℂ 2 (reducedLaw Q) :=
  if hr : 0 < r then (hP ζ).forcedGradient r hr μ j else 0

/-- These same witnesses realize both W and the literal force-factored endpoint. -/
theorem sharedWeakFlux (hd : 2 ≤ d)
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q))
    (ha : IsReducedCoefficientObservation Q a)
    {P : ℂ → ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : ∀ ζ, IsComplexEnvironmentSemigroup Q i ζ (P ζ))
    (μ : Lp ℂ 2 (reducedLaw Q)) (ζ : ℂ) (r : ℝ≥0) (hr : 0 < r) :
    IsEndpointWeakFlux hd Q (.inr false) ζ a
      (centeredComplexLp Q (P ζ r μ)) (gradient hP μ ζ r) (flux Q (gradient hP μ ζ r)) ∧
    IsEndpointWeakFlux hd Q (.inr false) ζ a
      (clockEndpoint Q ζ (P ζ) μ r)
      (fun j => ζ • gradient hP μ ζ r j) (fun j => ζ • flux Q (gradient hP μ ζ r) j) := by
  have hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
      (centeredComplexLp Q (P ζ r μ)) (gradient hP μ ζ r) := by
    intro j
    simpa only [gradient, dite_eq_left hr] using (((hP ζ).forcedGradient_spec r hr μ).centered j)
  have hf : IsEndpointWeakFlux hd Q (.inr false) ζ a
      (centeredComplexLp Q (P ζ r μ)) (gradient hP μ ζ r) (flux Q (gradient hP μ ζ r)) := by
    refine ⟨hG, fun j => ?_⟩
    simpa only [sub_zero] using fluxCoe a ha (gradient hP μ ζ r) j
  exact ⟨hf, weakFluxSmul hd a hf ζ⟩

/-- Each coordinate of the actual shared gradient is entire as an L2 class. -/
theorem analyticGradient
    {P : ℂ → ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : ∀ ζ, IsComplexEnvironmentSemigroup Q i ζ (P ζ))
    (μ : Lp ℂ 2 (reducedLaw Q)) (r : ℝ≥0) (hr : 0 < r) (j : Fin d) (z : ℂ) :
    AnalyticAt ℂ (fun ζ => gradient hP μ ζ r j) z := by
  have ha := ((ContinuousLinearMap.apply ℂ _).analyticAt_bilinear _).comp₂
    (analyticAt_const (v := μ)) (analyticAt_forcedGradient hP r hr z)
  have hb := ((PiLp.proj (𝕜 := ℂ) 2
    (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)) j).analyticAt _).comp ha
  change AnalyticAt ℂ (fun ζ => (hP ζ).forcedGradient r hr μ j) z at hb
  simpa only [gradient, dite_eq_left hr] using hb

/-- Each coordinate of the same anisotropic weak flux is entire in L2. -/
theorem analyticFlux
    {P : ℂ → ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : ∀ ζ, IsComplexEnvironmentSemigroup Q i ζ (P ζ))
    (μ : Lp ℂ 2 (reducedLaw Q)) (r : ℝ≥0) (hr : 0 < r) (j : Fin d) (z : ℂ) :
    AnalyticAt ℂ (fun ζ => flux Q (gradient hP μ ζ r) j) z := by
  exact Finset.univ.analyticAt_fun_sum (fun k _ =>
    (((complexCoefficientMul Q j k).analyticAt _).comp (analyticGradient hP μ r hr k z)).sub
      ((analyticGradient hP μ r hr k z).const_smul (c := (homogenizedCoefficient Q j k : ℂ))))

end EinsteinFull.ClockAnalyticity
