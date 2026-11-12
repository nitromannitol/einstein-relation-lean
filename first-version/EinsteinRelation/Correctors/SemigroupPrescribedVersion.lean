import EinsteinRelation.Correctors.AKMJointGradientVersion
import EinsteinRelation.Correctors.LocalWeakGradientUniqueness

/-! # Prescribed-time representatives preserve the semigroup equation

Source: `paper/main.tex:798–806`. Equality of weak derivatives and Fubini
transfer every original energy cylinder to the prescribed-time gradient.
-/

open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- A jointly measurable field representing all positive-time weak gradients
of the scalar solution is itself its semigroup gradient.
Source: `paper/main.tex:798–806`. -/
theorem semigroupSolution_prescribed_gradient_version {d : ℕ} {K : ℝ}
    {A : Coefficient d K} {v : Vec d → Vec d}
    {u : ℝ × Vec d → ℝ} {G H : ℝ × Vec d → Vec d}
    (hsol : IsSemigroupSolution A v u G)
    (hHm : AEStronglyMeasurable H volume)
    (hH : ∀ t : ℝ, 0 < t →
      HasWeakGradient Set.univ (fun x => u (t,x)) (fun x => H (t,x))) :
    IsSemigroupSolution A v u H := by
  apply semigroupSolution_gradient_congr_ae hsol
  intro a b R ha hab hR
  let μ : Measure ℝ := volume.restrict (Set.Ioo a b)
  let ν : Measure (Vec d) := volume.restrict (originBall d R)
  have hGm : AEStronglyMeasurable G (μ.prod ν) := by
    simpa only [μ,ν,Measure.prod_restrict,← Measure.volume_eq_prod] using
      (hsol.2.1 a b R ha hab hR).2.1
  have hHm' : AEStronglyMeasurable H (μ.prod ν) := by
    simpa only [μ,ν,Measure.prod_restrict,← Measure.volume_eq_prod] using
      hHm.restrict (s := Set.Ioo a b ×ˢ originBall d R)
  have hopen : IsOpen (originBall d R) := by
    unfold originBall euclideanNorm euclideanSq dot
    exact isOpen_lt (by fun_prop) continuous_const
  have heq : ∀ᵐ t ∂μ, ∀ᵐ x ∂ν, G (t,x) = H (t,x) := by
    filter_upwards [(hsol.2.1 a b R ha hab hR).2.2.2.1,
      ae_restrict_mem measurableSet_Ioo] with t htG ht
    have hw := hasWeakGradient_mono (Set.subset_univ (originBall d R))
      (hH t (ha.trans ht.1))
    filter_upwards [ae_all_iff.mpr fun j =>
      weakPartialDerivative_ae_eq_on_open hopen (htG j) (hw j)] with x hx
    exact funext hx
  have hmk : hGm.mk G =ᵐ[μ.prod ν] hHm'.mk H := by
    apply (Measure.ae_prod_iff_ae_ae
      (hGm.stronglyMeasurable_mk.measurableSet_eq_fun hHm'.stronglyMeasurable_mk)).mpr
    filter_upwards [Measure.ae_ae_of_ae_prod hGm.ae_eq_mk,
      Measure.ae_ae_of_ae_prod hHm'.ae_eq_mk,heq] with t htG htH ht
    filter_upwards [htG,htH,ht] with x hxG hxH hx
    exact hxG.symm.trans (hx.trans hxH)
  have hGH := hGm.ae_eq_mk.trans (hmk.trans hHm'.ae_eq_mk.symm)
  simpa only [μ,ν,Measure.prod_restrict,← Measure.volume_eq_prod] using hGH

end EinsteinRelation.Correctors
