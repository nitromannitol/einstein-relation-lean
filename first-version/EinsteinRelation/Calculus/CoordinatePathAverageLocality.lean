import EinsteinRelation.Calculus.CoordinatePathLocality
import EinsteinRelation.Calculus.CoordinatePathAverage
import EinsteinRelation.Correctors.AnisotropicKernelLocality

/-! # Locality of the concrete small-scale path average

Source: `paper/main.tex:1021–1029,1079–1084`. Averaging a coordinate
path against a compact kernel observes only the enlarged source window.
-/

open MeasureTheory
noncomputable section
namespace EinsteinRelation

/-- The actual compact path average is local on the union of the
translated source windows (`paper/main.tex:1021–1029,1079–1084`). -/
theorem measurable_localSigma_coordinatePathAverage {d : ℕ}
    {L : ℝ} {U W : Set (Vec d)}
    (hwindow : ∀ x : Vec d, euclideanNorm x < L → ∀ y ∈ U, x + y ∈ W)
    {K : Vec d → ℝ} (hK : Measurable K)
    (hKt : ∀ z, L ≤ euclideanNorm z → K z = 0)
    {f : FieldPair d → ℝ} (hf : Measurable[localSigma U] f) :
    Measurable[localSigma W] (coordinatePathAverage K f) := by
  let S : Set (Vec d) := {z | euclideanNorm z < L}
  have hS : MeasurableSet S := measurableSet_lt Entropy.continuous_euclideanNorm'.measurable measurable_const
  letI : MeasurableSpace (FieldPair d) := localSigma W
  have hpath := measurable_localSigma_coordinatePathFlux_ball hwindow hf
  let ν : Measure ↥S := Measure.comap Subtype.val volume
  haveI : SigmaFinite ν := SigmaFinite.of_map ν measurable_subtype_coe.aemeasurable (by
    dsimp only [ν]
    rw [map_comap_subtype_coe hS]
    infer_instance)
  apply measurable_pi_lambda
  intro i
  have hm : Measurable (fun q : ↥S × FieldPair d => K q.1 * coordinatePathFlux f q.1 q.2 i) :=
    (hK.comp (measurable_subtype_coe.comp measurable_fst)).mul ((measurable_pi_apply i).comp hpath)
  have hi := hm.stronglyMeasurable.integral_prod_left' (μ := ν)
  have he : (fun ω => coordinatePathAverage K f ω i) =
      fun ω => -(∫ z : ↥S, K z * coordinatePathFlux f z ω i ∂ν) := by
    funext ω
    unfold coordinatePathAverage
    congr 1
    dsimp only [ν]
    rw [integral_subtype_comap hS (fun z => K z * coordinatePathFlux f z ω i)]
    apply (setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => ?_).symm
    rw [hKt z (le_of_not_gt hz), zero_mul]
  rw [he]
  exact hi.measurable.neg

/-- The normalized anisotropic small-scale average has the same final
observation window as all bands (`paper/main.tex:1079–1084`). -/
theorem measurable_localSigma_anisotropicPathAverage {d : ℕ}
    (T : Vec d ≃L[ℝ] Vec d) {L R : ℝ} (hL : 0 < L) (hR : 1 ≤ R)
    (hT : ∀ x, euclideanNorm (T.symm x) ≤ L * euclideanNorm x)
    {f : FieldPair d → ℝ}
    (hf : Measurable[localSigma {x : Vec d | euclideanNorm x < 33 * R}] f) :
    Measurable[localSigma {x : Vec d | euclideanNorm x < (33 + 2 * L) * R}]
      (coordinatePathAverage (Correctors.anisotropicAverage T 1) f) := by
  apply measurable_localSigma_coordinatePathAverage (L := L) ?_
    (Correctors.anisotropicAverage_contDiff T (by norm_num)).continuous.measurable
    (fun z hz => Correctors.anisotropicAverage_tail T hL (by norm_num) hT (by simpa using hz)) hf
  intro x hx y hy
  change euclideanNorm (x + y) < (33 + 2 * L) * R
  change euclideanNorm y < 33 * R at hy
  have ht := TimeChange.euclideanNorm_add_le x y
  nlinarith [mul_le_mul_of_nonneg_left hR hL.le]

end EinsteinRelation
