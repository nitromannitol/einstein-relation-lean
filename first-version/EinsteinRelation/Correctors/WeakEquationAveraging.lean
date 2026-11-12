import EinsteinRelation.Calculus.Weak
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Group.Bounded

/-! # Averaging spatial weak equations

Source: `paper/main.tex:913–925`. Conditioning a Sobolev field on the
coefficients in a ball must commute with spatial weak derivatives. This
module proves the underlying integration statement for an arbitrary
averaging measure. In particular it applies to a conditional probability
kernel at every parameter where its sections have the stated integrability
and almost sure weak equations. It does not select joint conditional
versions or assume that any canonical corrector already has these properties.
-/

open MeasureTheory

namespace EinsteinRelation.Correctors

/-- Multiplying a jointly integrable field by a fixed compactly supported
continuous spatial test preserves joint integrability. -/
private theorem integrable_mul_spatial_test {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} {μ : Measure Ω} {ν : Measure (Vec d)} {f : Ω → Vec d → ℝ}
    (hf : Integrable (Function.uncurry f) (μ.prod ν))
    {ψ : Vec d → ℝ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) :
    Integrable (fun z : Ω × Vec d => f z.1 z.2 * ψ z.2) (μ.prod ν) := by
  obtain ⟨C, hC⟩ := hψc.exists_bound_of_continuous hψ
  exact hf.mul_bdd (hψ.measurable.comp measurable_snd).aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => hC z.2)

/-- Spatial weak partial derivatives commute with averaging jointly
integrable fields. Source: `paper/main.tex:913–925`. The hypotheses are
ordinary product integrability and the actual weak derivative identity;
they do not contain any conditional derivative conclusion. -/
theorem hasWeakPartialDerivative_integral {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} (μ : Measure Ω) [SFinite μ] (U : Set (Vec d)) (j : Fin d)
    (u g : Ω → Vec d → ℝ)
    (hu : Integrable (Function.uncurry u) (μ.prod (volume.restrict U)))
    (hg : Integrable (Function.uncurry g) (μ.prod (volume.restrict U)))
    (hweak : ∀ᵐ ω ∂μ, HasWeakPartialDerivative U j (u ω) (g ω)) :
    HasWeakPartialDerivative U j (fun x => ∫ ω, u ω x ∂μ)
      (fun x => ∫ ω, g ω x ∂μ) := by
  refine ⟨IntegrableOn.locallyIntegrableOn hu.integral_prod_right,
    IntegrableOn.locallyIntegrableOn hg.integral_prod_right, ?_⟩
  intro ψ hψ
  have hdψ : Continuous (coordinateDerivative j ψ) := by
    unfold coordinateDerivative
    exact (hψ.1.continuous_fderiv (mod_cast le_top)).clm_apply continuous_const
  have hdψc : HasCompactSupport (coordinateDerivative j ψ) :=
    hψ.2.1.fderiv_apply ℝ (unitVector j)
  have huid := integrable_mul_spatial_test hu hdψ hdψc
  have hgip := integrable_mul_spatial_test hg hψ.1.continuous hψ.2.1
  calc
    (∫ x in U, (∫ ω, u ω x ∂μ) * coordinateDerivative j ψ x) =
        ∫ x in U, (∫ ω, u ω x * coordinateDerivative j ψ x ∂μ) := by
      congr 1
      funext x
      exact (integral_mul_const _ _).symm
    _ = ∫ ω, (∫ x in U, u ω x * coordinateDerivative j ψ x) ∂μ :=
      (integral_integral_swap huid).symm
    _ = ∫ ω, -(∫ x in U, g ω x * ψ x) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hweak] with ω hω
      exact hω.2.2 ψ hψ
    _ = -(∫ x in U, (∫ ω, g ω x * ψ x ∂μ)) := by
      rw [integral_neg, integral_integral_swap hgip]
    _ = -(∫ x in U, (∫ ω, g ω x ∂μ) * ψ x) := by
      congr 2
      funext x
      exact integral_mul_const _ _

/-- The vector form of `hasWeakPartialDerivative_integral`, using actual
coordinate weak derivatives. Source: `paper/main.tex:913–925`. -/
theorem hasWeakGradient_integral {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} (μ : Measure Ω) [SFinite μ] (U : Set (Vec d))
    (u : Ω → Vec d → ℝ) (G : Ω → Vec d → Vec d)
    (hu : Integrable (Function.uncurry u) (μ.prod (volume.restrict U)))
    (hG : ∀ j : Fin d,
      Integrable (fun z : Ω × Vec d => G z.1 z.2 j) (μ.prod (volume.restrict U)))
    (hweak : ∀ᵐ ω ∂μ, HasWeakGradient U (u ω) (G ω)) :
    HasWeakGradient U (fun x => ∫ ω, u ω x ∂μ)
      (fun x j => ∫ ω, G ω x j ∂μ) := by
  intro j
  exact hasWeakPartialDerivative_integral μ U j u (fun ω x => G ω x j) hu (hG j)
    (hweak.mono fun _ hω => hω j)

/-- Spatial weak divergence commutes with averaging jointly integrable
fields. This supplies the distributional equation for averaged fluxes,
without requiring pointwise classical derivatives.
Source: `paper/main.tex:913–925`. -/
theorem hasWeakDivergence_integral {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} (μ : Measure Ω) [SFinite μ] (U : Set (Vec d))
    (F : Ω → Vec d → Vec d) (h : Ω → Vec d → ℝ)
    (hF : ∀ j : Fin d,
      Integrable (fun z : Ω × Vec d => F z.1 z.2 j) (μ.prod (volume.restrict U)))
    (hh : Integrable (Function.uncurry h) (μ.prod (volume.restrict U)))
    (hweak : ∀ᵐ ω ∂μ, HasWeakDivergence U (F ω) (h ω)) :
    HasWeakDivergence U (fun x j => ∫ ω, F ω x j ∂μ)
      (fun x => ∫ ω, h ω x ∂μ) := by
  refine ⟨fun j => IntegrableOn.locallyIntegrableOn (hF j).integral_prod_right,
    IntegrableOn.locallyIntegrableOn hh.integral_prod_right, ?_⟩
  intro ψ hψ
  have hcoord (j : Fin d) : Integrable
      (fun z : Ω × Vec d => F z.1 z.2 j * coordinateDerivative j ψ z.2)
      (μ.prod (volume.restrict U)) := by
    apply integrable_mul_spatial_test (f := fun ω x => F ω x j) (hF j)
    · unfold coordinateDerivative
      exact (hψ.1.continuous_fderiv (mod_cast le_top)).clm_apply continuous_const
    · exact hψ.2.1.fderiv_apply ℝ (unitVector j)
  have htest : Integrable
      (fun z : Ω × Vec d => dot (F z.1 z.2) (gradient ψ z.2))
      (μ.prod (volume.restrict U)) := by
    simpa only [dot, gradient] using integrable_finset_sum Finset.univ (fun j _ => hcoord j)
  have hdot : ∀ᵐ x ∂volume.restrict U,
      dot (fun j => ∫ ω, F ω x j ∂μ) (gradient ψ x) =
        ∫ ω, dot (F ω x) (gradient ψ x) ∂μ := by
    have hsections : ∀ᵐ x ∂volume.restrict U, ∀ j : Fin d,
        Integrable (fun ω => F ω x j * coordinateDerivative j ψ x) μ :=
      (ae_all_iff.mpr fun j => (hcoord j).prod_left_ae)
    filter_upwards [hsections] with x hx
    simp only [dot, gradient]
    rw [integral_finset_sum Finset.univ (fun j _ => hx j)]
    exact Finset.sum_congr rfl (fun j _ => (integral_mul_const _ _).symm)
  have hhip := integrable_mul_spatial_test hh hψ.1.continuous hψ.2.1
  calc
    (∫ x in U, dot (fun j => ∫ ω, F ω x j ∂μ) (gradient ψ x)) =
        ∫ x in U, (∫ ω, dot (F ω x) (gradient ψ x) ∂μ) := integral_congr_ae hdot
    _ = ∫ ω, (∫ x in U, dot (F ω x) (gradient ψ x)) ∂μ :=
      (integral_integral_swap htest).symm
    _ = ∫ ω, -(∫ x in U, h ω x * ψ x) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hweak] with ω hω
      exact hω.2.2 ψ hψ
    _ = -(∫ x in U, (∫ ω, h ω x * ψ x ∂μ)) := by
      rw [integral_neg, integral_integral_swap hhip]
    _ = -(∫ x in U, (∫ ω, h ω x ∂μ) * ψ x) := by
      congr 2
      funext x
      exact integral_mul_const _ _

/-- Weak row divergence commutes with averaging each actual matrix entry.
Source: `paper/main.tex:913–925`. -/
theorem hasWeakRowDivergence_integral {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} (μ : Measure Ω) [SFinite μ] (U : Set (Vec d))
    (S : Ω → Vec d → Mat d) (h : Ω → Vec d → Vec d)
    (hS : ∀ j k : Fin d,
      Integrable (fun z : Ω × Vec d => S z.1 z.2 j k) (μ.prod (volume.restrict U)))
    (hh : ∀ j : Fin d,
      Integrable (fun z : Ω × Vec d => h z.1 z.2 j) (μ.prod (volume.restrict U)))
    (hweak : ∀ᵐ ω ∂μ, HasWeakRowDivergence U (S ω) (h ω)) :
    HasWeakRowDivergence U (fun x j k => ∫ ω, S ω x j k ∂μ)
      (fun x j => ∫ ω, h ω x j ∂μ) := by
  intro j
  exact hasWeakDivergence_integral μ U (fun ω x k => S ω x j k)
    (fun ω x => h ω x j) (hS j) (hh j) (hweak.mono fun _ hω => hω j)

end EinsteinRelation.Correctors
