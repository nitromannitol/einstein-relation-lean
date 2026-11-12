import EinsteinRelation.Correctors.CanonicalKernelRepresentationOperations
import EinsteinRelation.Correctors.AKMInitialFluxObservation
import EinsteinRelation.Correctors.ParabolicGradientRepresentative
import EinsteinRelation.Correctors.AKMStretchedExponentialMoments

open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- The kernel version of Theorem 9.1 gives all scalar moments of the same
specified canonical coefficient-column flow. Source: AKM (9.2), (9.7);
`paper/main.tex:787–792,850–852`. -/
theorem parabolicSemigroupKernelDecay_canonical_column_moments
    (hAKM : ParabolicSemigroupKernelDecay)
    (d : ℕ) (hd : 2 ≤ d) (K s : ℝ) (hK : 1 < K) (hs : 0 < s) (hs2 : s < 2) :
    ∃ F : ℝ → ℝ, (∀ m : ℝ, 0 < m → 0 < F m) ∧
      ∀ P : Measure (Coefficient d K), IsAdmissibleLaw P → ∀ i : Fin d,
        ∀ (u : Coefficient d K → ℝ × Vec d → ℝ)
          (G : Coefficient d K → ℝ × Vec d → Vec d),
          Measurable (fun z : Coefficient d K × (ℝ × Vec d) => u z.1 z.2) →
          (∀ᵐ A ∂P, IsSemigroupSolution A (fun x => (A x).mulVec (unitVector i)) (u A) (G A) ∧
            HasCanonicalKernelRepresentation A (fun x => (A x).mulVec (unitVector i)) (u A)) →
          ∀ m : ℝ, 0 < m → ∀ t : ℝ, 1 ≤ t → ∀ x : Vec d,
            MemLp (fun A => u A (t,x)) (ENNReal.ofReal m) P ∧
            eLpNorm (fun A => u A (t,x)) (ENNReal.ofReal m) P ≤
              ENNReal.ofReal (F m*t^(-(1 : ℝ)/2-(d : ℝ)/4)) := by
  let c : ℝ := ((d : ℝ)+1)*K
  have hc : 0 < c := by dsimp only [c]; positivity
  obtain ⟨C,hC,hsource⟩ := hAKM d hd K s hK hs hs2
  let F : ℝ → ℝ := fun m => c*((2*(m/s)^(m/s))^(1/m)*C)
  refine ⟨F,fun m hm => by dsimp only [F]; positivity,?_⟩
  intro P hP i u G hum hflow
  let v : Coefficient d K → ℝ × Vec d → ℝ := fun A z => c⁻¹*u A z
  let W : Coefficient d K → ℝ × Vec d → Vec d := fun A z => c⁻¹ • G A z
  have hnorm : ∀ᵐ A ∂P, IsSemigroupSolution A (initialFluxObservation i A) (v A) (W A) ∧
      HasCanonicalKernelRepresentation A (initialFluxObservation i A) (v A) := by
    filter_upwards [hflow] with A hA
    have hobs : (fun x => c⁻¹ • (A x).mulVec (unitVector i)) =ᵐ[volume]
        initialFluxObservation i A := by
      filter_upwards [initialFluxObservation_eq_column_ae i A] with x hx
      exact hx.symm
    exact ⟨semigroupSolution_initialFlux_congr_ae
      (semigroupSolution_const_mul hA.1 (inv_nonneg.mpr hc.le)) hobs,
      canonicalKernelRepresentation_initialFlux_congr_ae
        (canonicalKernelRepresentation_const_mul hA.2 c⁻¹) hobs⟩
  have hvm : Measurable (fun z : Coefficient d K × (ℝ × Vec d) => v z.1 z.2) :=
    measurable_const.mul hum
  have hstoch := hsource P hP (initialFluxObservation i)
    (initialFluxObservation_stationary P i)
    (Filter.Eventually.of_forall fun A => initialFluxObservation_norm_le_ae
      (zero_lt_one.trans hK) i A) (measurable_initialFluxObservation_local i) v W hvm hnorm
  intro m hm t ht x
  have hθ : 0 < C*t^(-(1 : ℝ)/2-(d : ℝ)/4) :=
    mul_pos hC (Real.rpow_pos_of_pos (zero_lt_one.trans_le ht) _)
  have he := eLpNorm_le_of_stretchedExponential P hs hθ hm
    (Filter.Eventually.of_forall fun A => abs_nonneg (v A (t,x))) (hstoch t ht x)
  have hev : eLpNorm (fun A => v A (t,x)) (ENNReal.ofReal m) P ≤
      ENNReal.ofReal (((2*(m/s)^(m/s))^(1/m)*C)*t^(-(1 : ℝ)/2-(d : ℝ)/4)) := by
    simpa only [← Real.norm_eq_abs,eLpNorm_norm,mul_assoc] using he
  have heq : (fun A => u A (t,x)) = c • (fun A => v A (t,x)) := by
    funext A
    dsimp only [Pi.smul_apply,smul_eq_mul,v]
    rw [← mul_assoc,mul_inv_cancel₀ hc.ne',one_mul]
  have hb : eLpNorm (fun A => u A (t,x)) (ENNReal.ofReal m) P ≤
      ENNReal.ofReal (F m*t^(-(1 : ℝ)/2-(d : ℝ)/4)) := by
    rw [heq,eLpNorm_const_smul]
    apply (mul_le_mul_right hev _).trans
    rw [Real.enorm_eq_ofReal hc.le,← ENNReal.ofReal_mul hc.le]
    apply le_of_eq
    congr 1
    dsimp only [F]
    ring
  exact ⟨⟨(hum.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable,
    hb.trans_lt ENNReal.ofReal_lt_top⟩,hb⟩

end EinsteinRelation.Correctors
