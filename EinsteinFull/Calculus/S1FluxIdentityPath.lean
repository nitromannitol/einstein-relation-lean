import EinsteinFull.Calculus.S1FluxIdentityWeak2
import EinsteinFull.Calculus.ComplexCommonSpatialSupport
import EinsteinFull.Calculus.ComplexHorizontalIntegrationSupport
import EinsteinFull.Calculus.ComplexHorizontalMeanSupport
import EinsteinFull.Frozen.ReducedCoefficientObservation
import EinsteinFull.Frozen.ReducedLawProbability
import EinsteinFull.Frozen.ReducedLawStationary
import EinsteinFull.Work.W6.HorizontalPhysicalRealizationProof

/-!
# Pathwise facts for the endpoint part of `e:flux-identity`
-/

open MeasureTheory
open scoped BigOperators

namespace EinsteinFull

open EinsteinRelation

variable {d : ℕ} {Λ r : ℝ}

private instance fluxId_reducedProbability (Q : EnvironmentLaw d Λ r) :
    IsProbabilityMeasure (reducedLaw Q) :=
  reducedLaw_probability Q

theorem fluxId_ae_locInt (Q : EnvironmentLaw d Λ r) (f : Lp ℂ 2 (reducedLaw Q)) :
    ∀ᵐ ω ∂reducedLaw Q, LocallyIntegrable (fun x => f (translate x ω)) volume := by
  filter_upwards [ae_complex_orbit_memLp_on_all_compacts (reducedLaw Q)
    (reducedLaw_stationary Q) f] with ω hω
  exact fluxId_locInt_of_memLp hω

/-- The horizontal gradient relation holds pathwise against every smooth compact complex test. -/
theorem fluxId_ae_gradient (Q : EnvironmentLaw d Λ r) (U : Lp ℂ 2 (reducedLaw Q))
    (G : Fin d → Lp ℂ 2 (reducedLaw Q))
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) U G) :
    ∀ᵐ ω ∂reducedLaw Q, ∀ m : Fin d, ∀ θ : Vec d → ℂ, FSC θ →
      ∫ x, G m (translate x ω) * θ x =
        -∫ x, U (translate x ω) * fderiv ℝ θ x (unitVector m) := by
  refine ae_all_iff.mpr fun m => ?_
  have hFm : ∀ j, Measurable (fun ω : FieldPair d => (if j = m then (1 : ℂ) else 0) * U ω) :=
    fun j => measurable_const.mul (Lp.stronglyMeasurable U).measurable
  have hhm : Measurable (fun ω : FieldPair d => G m ω) := (Lp.stronglyMeasurable (G m)).measurable
  have hF : ∀ j, MemLp (fun ω : FieldPair d => (if j = m then (1 : ℂ) else 0) * U ω) 2
      (reducedLaw Q) := fun j => (Lp.memLp U).const_mul _
  have hh : MemLp (fun ω : FieldPair d => G m ω) 2 (reducedLaw Q) := Lp.memLp (G m)
  have hw : ∀ (v : Lp ℂ 2 (reducedLaw Q)) (V : Fin d → Lp ℂ 2 (reducedLaw Q)),
      HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) v V →
      (∫ ω, ∑ j, (if j = m then (1 : ℂ) else 0) * U ω * V j ω ∂reducedLaw Q) =
        -(∫ ω, G m ω * v ω ∂reducedLaw Q) := by
    intro v V hV
    have h1 := (complexHorizontalDerivatives_integration_by_parts (hG m) (hV m)).2.2
    have e : (fun ω : FieldPair d => ∑ j, (if j = m then (1 : ℂ) else 0) * U ω * V j ω) =
        fun ω => U ω * V m ω := by
      funext ω
      simp [ite_mul, Finset.sum_ite_eq']
    rw [e, h1, neg_neg]
  have hreal := ae_complex_spatial_divergence_all_tests (reducedLaw Q) (reducedLaw_stationary Q)
    (fun j ω => (if j = m then (1 : ℂ) else 0) * U ω) (fun ω => G m ω) hFm hhm hF hh hw
  filter_upwards [hreal, fluxId_ae_locInt Q U, fluxId_ae_locInt Q (G m)] with ω hr hU hGm θ hθ
  have hLIF : ∀ j, LocallyIntegrable
      (fun x => (if j = m then (1 : ℂ) else 0) * U (translate x ω)) volume :=
    fun j => hU.smul (if j = m then (1 : ℂ) else 0)
  have hreal' : ∀ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      ∫ x, G m (translate x ω) * (φ x : ℂ) =
        -∑ j, ∫ x, (if j = m then (1 : ℂ) else 0) * U (translate x ω) *
          (fderiv ℝ φ x (unitVector j) : ℂ) := by
    intro φ hφ hφc
    have h : ∫ x, G m (translate x ω) * (φ x : ℂ) =
        -∫ x, ∑ j, (if j = m then (1 : ℂ) else 0) * U (translate x ω) *
          (fderiv ℝ φ x (unitVector j) : ℂ) := hr φ hφ hφc
    have hint : ∀ j, Integrable (fun x => (if j = m then (1 : ℂ) else 0) * U (translate x ω) *
        (fderiv ℝ φ x (unitVector j) : ℂ)) := fun j =>
      fluxId_intT (hLIF j)
        (Complex.continuous_ofReal.comp ((hφ.continuous_fderiv (by simp)).clm_apply
          continuous_const))
        ((hφc.fderiv_apply ℝ (unitVector j)).comp_left (g := ((↑) : ℝ → ℂ)) (by simp))
    rw [h, integral_finsetSum _ (fun j _ => hint j)]
  have key := fluxId_complexify (fun x => G m (translate x ω))
    (fun j x => (if j = m then (1 : ℂ) else 0) * U (translate x ω)) hGm hLIF hreal' θ hθ.1 hθ.2
  rw [key]
  congr 1
  rw [Finset.sum_eq_single m]
  · simp
  · intro j _ hj
    simp [hj]
  · intro h
    exact absurd (Finset.mem_univ m) h

/-- The mean of the flux `J = (a - A) G` is the mean of `a G`, since `G` has mean zero. -/
theorem fluxId_meanJ (Q : EnvironmentLaw d Λ r) (e0 : Fin d)
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (ha : IsReducedCoefficientObservation Q a)
    (hsymm : ∀ᵐ ω ∂reducedLaw Q, (ω.1 0).transpose = ω.1 0) (A : Mat d)
    (G : Fin d → Lp ℂ 2 (reducedLaw Q)) (hmean : ∀ k, ∫ ω, G k ω ∂reducedLaw Q = 0)
    (Je : Lp ℂ 2 (reducedLaw Q))
    (hJ : (Je : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
      fun ω => ∑ k, (a e0 k ω - (A e0 k : ℂ)) * G k ω) :
    ∫ ω, Je ω ∂reducedLaw Q = ∫ ω, ∑ k, a k e0 ω * G k ω ∂reducedLaw Q := by
  have iag : ∀ j k l, Integrable (fun ω => a j k ω * G l ω) (reducedLaw Q) := fun j k l =>
    (Lp.memLp (a j k)).integrable_mul (Lp.memLp (G l))
  have iG : ∀ k, Integrable (fun ω => G k ω) (reducedLaw Q) := fun k =>
    (Lp.memLp (G k)).integrable (by norm_num)
  have e1 : ∫ ω, Je ω ∂reducedLaw Q = ∑ k, ∫ ω, a e0 k ω * G k ω ∂reducedLaw Q := by
    rw [integral_congr_ae hJ]
    have e : (fun ω => ∑ k, (a e0 k ω - (A e0 k : ℂ)) * G k ω) =
        fun ω => ∑ k, (a e0 k ω * G k ω - (A e0 k : ℂ) * G k ω) := by
      funext ω
      exact Finset.sum_congr rfl fun k _ => by ring
    have iterm : ∀ k, Integrable (fun ω => a e0 k ω * G k ω - (A e0 k : ℂ) * G k ω)
        (reducedLaw Q) := fun k => (iag e0 k k).sub ((iG k).const_mul _)
    rw [e, integral_finsetSum _ (fun k _ => iterm k)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_sub (iag e0 k k) ((iG k).const_mul _), integral_const_mul, hmean k]
    ring
  have e2 : ∫ ω, ∑ k, a k e0 ω * G k ω ∂reducedLaw Q =
      ∑ k, ∫ ω, a k e0 ω * G k ω ∂reducedLaw Q :=
    integral_finsetSum _ fun k _ => iag k e0 k
  rw [e1, e2]
  refine Finset.sum_congr rfl fun k _ => integral_congr_ae ?_
  filter_upwards [ha e0 k, ha k e0, hsymm] with ω h1 h2 h3
  have h4 := congrFun (congrFun h3 k) e0
  simp only [Matrix.transpose_apply] at h4
  rw [h1, h2, h4]

end EinsteinFull
