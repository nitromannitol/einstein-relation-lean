import Mathlib.Analysis.Calculus.Deriv.Support
import EinsteinRelation.Correctors.SpatialWeakLocalization
import EinsteinRelation.Correctors.ParabolicSeparatedTests
import EinsteinRelation.Correctors.CoordinatePairingIntegrals

open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- A compact temporal test of an actual parabolic solution gives its actual
elliptic weak divergence equation. Source: `paper/main.tex:798–806`;
AKM Lemma 8.2, printed pp. 305–307. -/
theorem parabolicSolution_temporal_weakDivergence {d : ℕ} {K a b : ℝ}
    (hK : 0 < K) {A : Coefficient d K} {U : Set (Vec d)}
    [IsFiniteMeasure (volume.restrict U)]
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hsol : IsParabolicSolution A (Set.Ioo a b) U u G)
    {ρ : ℝ → ℝ} (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ)
    (hρc : HasCompactSupport ρ) (hρs : tsupport ρ ⊆ Set.Ioo a b) :
    HasWeakDivergence U
      (fun x j => ∫ s in Set.Ioo a b, ρ s * ((A x).mulVec (G (s,x))) j)
      (fun x => -(∫ s in Set.Ioo a b, deriv ρ s * u (s,x))) := by
  let I := Set.Ioo a b
  let μ := volume.restrict I
  let ν := volume.restrict U
  have hprod : volume.restrict (I ×ˢ U) = μ.prod ν := by
    simp only [μ,ν,Measure.volume_eq_prod,Measure.prod_restrict]
  haveI : IsFiniteMeasure μ := by dsimp only [μ,I]; infer_instance
  haveI : IsFiniteMeasure ν := inferInstanceAs (IsFiniteMeasure (volume.restrict U))
  haveI : IsFiniteMeasure (volume.restrict (I ×ˢ U)) := by
    rw [hprod]
    infer_instance
  have hmul {f : ℝ × Vec d → ℝ} (hf : Integrable f (μ.prod ν))
      {η : ℝ → ℝ} (hc : Continuous η) (hs : HasCompactSupport η) :
      Integrable (fun z : ℝ × Vec d => η z.1 * f z) (μ.prod ν) := by
    obtain ⟨C,hC⟩ := hs.exists_bound_of_continuous hc
    simpa only [mul_comm] using hf.mul_bdd
      (hc.measurable.comp measurable_fst).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => hC z.1)
  have hu0 : Integrable u (μ.prod ν) := by
    rw [← hprod]
    exact hsol.1.integrable (by norm_num)
  have hF0 j : Integrable (fun z : ℝ × Vec d => (A z.2).mulVec (G z) j) (μ.prod ν) := by
    rw [← hprod]
    exact (parabolicSolution_flux_coordinate_memLp hK A hsol j).integrable (by norm_num)
  have hu := hmul hu0 (hρ.continuous_deriv (by norm_num)) hρc.deriv
  have hF j := hmul (hF0 j) hρ.continuous hρc
  have hsmul {f : ℝ × Vec d → ℝ} (hf : Integrable f (μ.prod ν))
      {ψ : Vec d → ℝ} (hc : Continuous ψ) (hs : HasCompactSupport ψ) :
      Integrable (fun z : ℝ × Vec d => f z * ψ z.2) (μ.prod ν) := by
    obtain ⟨C,hC⟩ := hs.exists_bound_of_continuous hc
    exact hf.mul_bdd (hc.measurable.comp measurable_snd).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => hC z.2)
  refine ⟨fun j => IntegrableOn.locallyIntegrableOn (hF j).integral_prod_right,
    IntegrableOn.locallyIntegrableOn hu.integral_prod_right.neg,?_⟩
  intro ψ hψ
  have hp : Integrable (fun z : ℝ × Vec d =>
      dot (fun j => ρ z.1 * (A z.2).mulVec (G z) j) (gradient ψ z.2)) (μ.prod ν) := by
    unfold dot gradient
    exact integrable_finset_sum Finset.univ fun j _ => hsmul (hF j)
      (isSpatialTest_coordinateDerivative hψ j).1.continuous
      (isSpatialTest_coordinateDerivative hψ j).2.1
  have hr := hsmul hu hψ.1.continuous hψ.2.1
  have hleft : (∫ x in U, dot
      (fun j => ∫ s in I, ρ s * (A x).mulVec (G (s,x)) j) (gradient ψ x)) =
      ∫ s in I, ρ s * ∫ x in U, dot ((A x).mulVec (G (s,x))) (gradient ψ x) := by
    calc
      _ = ∫ x in U, ∫ s in I,
          dot (fun j => ρ s * (A x).mulVec (G (s,x)) j) (gradient ψ x) := by
        apply integral_congr_ae
        filter_upwards [ae_all_iff.mpr (fun j => (hF j).prod_left_ae)] with x hx
        exact dot_integral_components μ _ _ hx
      _ = ∫ s in I, ∫ x in U,
          dot (fun j => ρ s * (A x).mulVec (G (s,x)) j) (gradient ψ x) :=
        (integral_integral_swap hp).symm
      _ = _ := by
        apply integral_congr_ae
        filter_upwards with s
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards with x
        simp only [dot,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
  have hright : (∫ x in U, (∫ s in I, deriv ρ s * u (s,x)) * ψ x) =
      ∫ s in I, (∫ x in U, u (s,x) * ψ x) * deriv ρ s := by
    calc
      _ = ∫ x in U, ∫ s in I, (deriv ρ s * u (s,x)) * ψ x := by
        simp_rw [integral_mul_const]
      _ = ∫ s in I, ∫ x in U, (deriv ρ s * u (s,x)) * ψ x :=
        (integral_integral_swap hr).symm
      _ = _ := by
        apply integral_congr_ae
        filter_upwards with s
        rw [← integral_mul_const]
        apply integral_congr_ae
        filter_upwards with x
        ring
  have he := parabolicSolution_separated_time_test hK A hsol hρ hρc
    (by simpa only [I,isOpen_Ioo.interior_eq] using hρs) hψ
  change (∫ x in U, dot (fun j => ∫ s in I, ρ s * (A x).mulVec (G (s,x)) j)
      (gradient ψ x)) = -(∫ x in U, -(∫ s in I, deriv ρ s * u (s,x)) * ψ x)
  simp only [neg_mul,integral_neg,neg_neg]
  rw [hleft,hright]
  exact he.symm

end EinsteinRelation.Correctors
