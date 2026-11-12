import EinsteinRelation.Correctors.AKMParabolicIntegrability
import EinsteinRelation.Correctors.WeakEquationAveraging
import EinsteinRelation.Mobility.DriftBoundPointwise

open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- A locally integrable family of actual parabolic solutions can be
integrated once its averaged scalar and gradient have finite energy.
Source: `paper/main.tex:787–792,850`. -/
theorem parabolicSolution_integral {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [SFinite μ] {d : ℕ} {K : ℝ}
    (hK : 0 < K) {A : Coefficient d K} {I : Set ℝ} {U : Set (Vec d)}
    (hI : MeasurableSet I) (_hU : IsOpen U)
    (u : Ω → ℝ × Vec d → ℝ) (G : Ω → ℝ × Vec d → Vec d)
    (_hum : Measurable (fun z : Ω × (ℝ × Vec d) => u z.1 z.2))
    (hGm : Measurable (fun z : Ω × (ℝ × Vec d) => G z.1 z.2))
    (hu : Integrable (fun z : Ω × (ℝ × Vec d) => u z.1 z.2)
      (μ.prod (volume.restrict (I ×ˢ U))))
    (hG : ∀ j : Fin d, Integrable (fun z : Ω × (ℝ × Vec d) => G z.1 z.2 j)
      (μ.prod (volume.restrict (I ×ˢ U))))
    (hu2 : MemLp (fun z => ∫ ω, u ω z ∂μ) 2 (volume.restrict (I ×ˢ U)))
    (hG2 : MemLp (fun z => euclideanNorm (fun j => ∫ ω, G ω z j ∂μ)) 2
      (volume.restrict (I ×ˢ U)))
    (hsol : ∀ ω, IsParabolicSolution A I U (u ω) (G ω))
    (hw : ∀ ω t, t ∈ I → HasWeakGradient U
      (fun x => u ω (t,x)) (fun x => G ω (t,x))) :
    IsParabolicSolution A I U (fun z => ∫ ω, u ω z ∂μ)
      (fun z j => ∫ ω, G ω z j ∂μ) := by
  let ν := volume.restrict (I ×ˢ U)
  have hν : ν = (volume.restrict I).prod (volume.restrict U) := by
    simp only [ν,Measure.prod_restrict,← Measure.volume_eq_prod]
  have hsections (f : Ω × (ℝ × Vec d) → ℝ) (hf : Integrable f (μ.prod ν)) :
      ∀ᵐ t ∂volume.restrict I, Integrable (fun z : Ω × Vec d => f (z.1,(t,z.2)))
        (μ.prod (volume.restrict U)) := by
    rw [hν] at hf
    have he := MeasurePreserving.symm MeasurableEquiv.prodAssoc
      (measurePreserving_prodAssoc (volume.restrict I) (volume.restrict U) μ)
    have hi := he.integrable_comp_of_integrable hf.swap
    filter_upwards [hi.prod_right_ae] with t ht
    exact ht.swap
  have hgrad : ∀ᵐ t ∂volume.restrict I, HasWeakGradient U
      (fun x => ∫ ω, u ω (t,x) ∂μ) (fun x j => ∫ ω, G ω (t,x) j ∂μ) := by
    filter_upwards [hsections _ hu,ae_all_iff.mpr (fun j => hsections _ (hG j)),
      ae_restrict_mem hI] with t hut hGt ht
    exact hasWeakGradient_integral μ U _ _ hut hGt (ae_of_all μ fun ω => hw ω t ht)
  have hgm : AEStronglyMeasurable (fun z j => ∫ ω, G ω z j ∂μ) ν := by
    apply Measurable.aestronglyMeasurable
    apply measurable_pi_lambda
    intro j
    exact ((measurable_pi_apply j).comp hGm).stronglyMeasurable.integral_prod_left'.measurable
  refine ⟨hu2,hgm,hG2,hgrad,?_⟩
  intro ψ hψ hψc hψs
  let D : (ℝ × Vec d) → (ℝ × Vec d) → ℝ := fun v z => fderiv ℝ ψ z v
  have hDm (v : ℝ × Vec d) : Continuous (D v) :=
    (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hDb (v : ℝ × Vec d) : ∃ B : ℝ, ∀ z, ‖D v z‖ ≤ B :=
    (hψc.fderiv_apply ℝ v).exists_bound_of_continuous (hDm v)
  have hAi (j k : Fin d) : AEStronglyMeasurable
      (fun z : Ω × (ℝ × Vec d) => A z.2.2 j k) (μ.prod ν) :=
    ((A.locally_integrable j k).aestronglyMeasurable.comp_snd.mono_measure
      (show ν ≤ volume from Measure.restrict_le_self)).comp_snd
  have hAb (j k : Fin d) (x : Vec d) : |A x j k| ≤ K := by
    apply abs_entry_le_of_quadratic_bounds hK.le (A x) (A.symmetric x)
    · intro ξ
      exact (show 0 ≤ euclideanSq ξ from by
        unfold euclideanSq dot
        exact Finset.sum_nonneg fun l _ => mul_self_nonneg _).trans (A.elliptic x ξ).1
    · exact fun ξ => (A.elliptic x ξ).2
  have hterm (j k : Fin d) : Integrable (fun z : Ω × (ℝ × Vec d) =>
      A z.2.2 j k * G z.1 z.2 k * D (0,unitVector j) z.2) (μ.prod ν) := by
    obtain ⟨B,hB⟩ := hDb (0,unitVector j)
    exact ((hG k).bdd_mul (hAi j k) (ae_of_all _ fun z => by
      simpa only [Real.norm_eq_abs] using hAb j k z.2.2)).mul_bdd
        ((hDm _).measurable.comp measurable_snd).aestronglyMeasurable
        (ae_of_all _ fun z => hB z.2)
  have htime : Integrable (fun z : Ω × (ℝ × Vec d) => -u z.1 z.2*D (1,0) z.2)
      (μ.prod ν) := by
    obtain ⟨B,hB⟩ := hDb (1,0)
    exact hu.neg.mul_bdd ((hDm _).measurable.comp measurable_snd).aestronglyMeasurable
      (ae_of_all _ fun z => hB z.2)
  let F : Ω × (ℝ × Vec d) → ℝ := fun z => -u z.1 z.2*D (1,0) z.2 +
    ∑ j : Fin d, ∑ k : Fin d, A z.2.2 j k*G z.1 z.2 k*D (0,unitVector j) z.2
  have hFi : Integrable F (μ.prod ν) := htime.add
    (integrable_finset_sum Finset.univ fun j _ =>
      integrable_finset_sum Finset.univ fun k _ => hterm j k)
  have hFzero (ω : Ω) : (∫ z, F (ω,z) ∂ν) = 0 := by
    convert (hsol ω).2.2.2.2 ψ hψ hψc hψs using 1
    apply integral_congr_ae
    filter_upwards with z
    simp only [F,D,dot,Matrix.mulVec,dotProduct,Finset.sum_mul]
  have havg : (fun z => -(∫ ω, u ω z ∂μ)*D (1,0) z +
      dot ((A z.2).mulVec (fun k => ∫ ω, G ω z k ∂μ))
        (fun j => D (0,unitVector j) z)) =ᵐ[ν] fun z => ∫ ω, F (ω,z) ∂μ := by
    filter_upwards [htime.prod_left_ae,ae_all_iff.mpr (fun j =>
      ae_all_iff.mpr (fun k => (hterm j k).prod_left_ae))] with z htz htzs
    dsimp only [F]
    rw [integral_add htz (integrable_finset_sum Finset.univ fun j _ =>
      integrable_finset_sum Finset.univ fun k _ => htzs j k),
      integral_mul_const,integral_neg]
    simp only [dot,Matrix.mulVec,dotProduct,Finset.sum_mul]
    congr 1
    rw [integral_finset_sum Finset.univ (fun j _ =>
      integrable_finset_sum Finset.univ fun k _ => htzs j k)]
    apply Finset.sum_congr rfl
    intro j _
    rw [integral_finset_sum Finset.univ (fun k _ => htzs j k)]
    apply Finset.sum_congr rfl
    intro k _
    rw [integral_mul_const,integral_const_mul]
  calc
    _ = ∫ z, (∫ ω, F (ω,z) ∂μ) ∂ν := integral_congr_ae havg
    _ = ∫ ω, (∫ z, F (ω,z) ∂ν) ∂μ := (integral_integral_swap hFi).symm
    _ = 0 := by simp_rw [hFzero]; simp

end EinsteinRelation.Correctors
