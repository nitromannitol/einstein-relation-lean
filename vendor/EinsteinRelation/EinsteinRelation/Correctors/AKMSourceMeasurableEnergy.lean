import EinsteinRelation.Environment.AKMMeasurableRepresentative
import EinsteinRelation.External.AKMEnergyDensitySources
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Measurability of source flux and energy integrals

Source: `paper/main.tex:693-698,727-729`; AKM (3.93), p. 101, and
(4.4), p. 124. Raw coefficients are replaced only inside spatial integrals,
using a representative valid for each coefficient separately. No continuous
stationarity or canonical-law hypothesis is used.
-/

open MeasureTheory
noncomputable section
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- A jointly measurable version of the raw affine-corrector flux. -/
def sourceFluxRepresentative {d : ℕ} {K : ℝ}
    (g : Coefficient d K → Vec d → Vec d) (e : Vec d)
    (a : Coefficient d K) (x : Vec d) : Vec d :=
  (coefficientRepresentative a x).mulVec (e + g a x)

/-- Joint measurability follows from the original coefficient observations. -/
theorem measurable_sourceFluxRepresentative {d : ℕ} {K : ℝ}
    (g : Coefficient d K → Vec d → Vec d)
    (hg : Measurable (fun p : Coefficient d K × Vec d => g p.1 p.2)) (e : Vec d) :
    Measurable (fun p : Coefficient d K × Vec d => sourceFluxRepresentative g e p.1 p.2) := by
  exact (show Continuous (fun p : Mat d × Vec d => p.1.mulVec p.2) from
    continuous_fst.matrix_mulVec continuous_snd).measurable.comp
      (measurable_coefficientRepresentative.prodMk (measurable_const.add hg))

/-- The measurable flux agrees spatially almost everywhere for every coefficient. -/
theorem sourceFluxRepresentative_ae_eq {d : ℕ} {K : ℝ}
    (g : Coefficient d K → Vec d → Vec d) (e : Vec d) (a : Coefficient d K) :
    sourceFluxRepresentative g e a =ᵐ[volume] fun x => (a x).mulVec (e + g a x) := by
  filter_upwards [coefficientRepresentative_ae_eq a] with x hx
  exact congrArg (fun A : Mat d => A.mulVec (e + g a x)) hx

/-- The jointly measurable Gaussian energy density used for Tonelli and Fubini. -/
def sourceEnergyRepresentative {d : ℕ} {K : ℝ}
    (g : Coefficient d K → Vec d → Vec d) (e z : Vec d) (r : ℝ)
    (a : Coefficient d K) (x : Vec d) : ℝ :=
  heatKernel z r x * ((1 / 2 : ℝ) * dot (e + g a x) (sourceFluxRepresentative g e a x))

/-- Joint measurability of the Gaussian energy density. -/
theorem measurable_sourceEnergyRepresentative {d : ℕ} {K : ℝ}
    (g : Coefficient d K → Vec d → Vec d)
    (hg : Measurable (fun p : Coefficient d K × Vec d => g p.1 p.2))
    (e z : Vec d) (r : ℝ) :
    Measurable (fun p : Coefficient d K × Vec d => sourceEnergyRepresentative g e z r p.1 p.2) := by
  have hk : Measurable (fun x : Vec d => heatKernel z r x) := by
    unfold heatKernel euclideanHeatKernel euclideanSq dot
    fun_prop
  have hd : Continuous (fun p : Vec d × Vec d => dot p.1 p.2) := by
    unfold dot
    fun_prop
  exact (hk.comp measurable_snd).mul (measurable_const.mul
    (hd.measurable.comp ((measurable_const.add hg).prodMk
      (measurable_sourceFluxRepresentative g hg e))))

/-- The Gaussian representative agrees with the literal source integrand. -/
theorem sourceEnergyRepresentative_ae_eq {d : ℕ} {K : ℝ}
    (g : Coefficient d K → Vec d → Vec d) (e z : Vec d) (r : ℝ)
    (a : Coefficient d K) :
    sourceEnergyRepresentative g e z r a =ᵐ[volume] fun x => heatKernel z r x *
      ((1 / 2 : ℝ) * dot (e + g a x) ((a x).mulVec (e + g a x))) := by
  filter_upwards [sourceFluxRepresentative_ae_eq g e a] with x hx
  exact congrArg (fun v => heatKernel z r x * ((1 / 2 : ℝ) * dot (e + g a x) v)) hx

/-- Ordinary source energy integrals are measurable on the raw AKM carrier. -/
theorem measurable_rawGaussianEnergy {d : ℕ} {K : ℝ}
    (g : Coefficient d K → Vec d → Vec d)
    (hg : Measurable (fun p : Coefficient d K × Vec d => g p.1 p.2))
    (e z : Vec d) (r : ℝ) :
    Measurable (fun a : Coefficient d K => ∫ x, heatKernel z r x *
      ((1 / 2 : ℝ) * dot (e + g a x) ((a x).mulVec (e + g a x))) ∂volume) := by
  have heq : (fun a => ∫ x, sourceEnergyRepresentative g e z r a x ∂volume) =
      (fun a => ∫ x, heatKernel z r x *
        ((1 / 2 : ℝ) * dot (e + g a x) ((a x).mulVec (e + g a x))) ∂volume) := by
    funext a
    exact integral_congr_ae (sourceEnergyRepresentative_ae_eq g e z r a)
  rw [← heq]
  exact (measurable_sourceEnergyRepresentative g hg e z r).stronglyMeasurable.integral_prod_right'.measurable

/-- Ordinary flux integrals on any spatial region are measurable on the source carrier. -/
theorem measurable_rawCellFlux {d : ℕ} {K : ℝ}
    (g : Coefficient d K → Vec d → Vec d)
    (hg : Measurable (fun p : Coefficient d K × Vec d => g p.1 p.2))
    (e : Vec d) (U : Set (Vec d)) :
    Measurable (fun a : Coefficient d K => ∫ x in U, (a x).mulVec (e + g a x) ∂volume) := by
  have heq : (fun a => ∫ x in U, sourceFluxRepresentative g e a x ∂volume) =
      (fun a => ∫ x in U, (a x).mulVec (e + g a x) ∂volume) := by
    funext a
    exact integral_congr_ae (ae_restrict_of_ae (sourceFluxRepresentative_ae_eq g e a))
  rw [← heq]
  exact (measurable_sourceFluxRepresentative g hg e).stronglyMeasurable.integral_prod_right'.measurable

/-- Ellipticity makes the literal Gaussian energy nonnegative. -/
theorem rawGaussianEnergy_nonneg {d : ℕ} {K : ℝ}
    (g : Coefficient d K → Vec d → Vec d) (e z : Vec d) (r : ℝ)
    (a : Coefficient d K) (x : Vec d) :
    0 ≤ heatKernel z r x * ((1 / 2 : ℝ) *
      dot (e + g a x) ((a x).mulVec (e + g a x))) := by
  have hs : 0 ≤ euclideanSq (e + g a x) := by
    unfold euclideanSq dot
    exact Finset.sum_nonneg fun _ _ => mul_self_nonneg _
  exact mul_nonneg (by unfold heatKernel euclideanHeatKernel; positivity)
    (mul_nonneg (by norm_num) (hs.trans (a.elliptic x (e + g a x)).1))

/-- Spatially almost-everywhere gradient identification preserves Gaussian
energy integrals almost surely. -/
theorem rawGaussianEnergy_congr_grad_ae {d : ℕ} {K : ℝ}
    (P : Measure (Coefficient d K)) (g h : Coefficient d K → Vec d → Vec d)
    (e z : Vec d) (r : ℝ) (hgh : ∀ᵐ a ∂P, g a =ᵐ[volume] h a) :
    (fun a => ∫ x, heatKernel z r x *
      ((1 / 2 : ℝ) * dot (e + g a x) ((a x).mulVec (e + g a x))) ∂volume) =ᵐ[P]
    (fun a => ∫ x, heatKernel z r x *
      ((1 / 2 : ℝ) * dot (e + h a x) ((a x).mulVec (e + h a x))) ∂volume) := by
  filter_upwards [hgh] with a ha
  apply integral_congr_ae
  filter_upwards [ha] with x hx
  rw [hx]

/-- Gradient identification preserves expected raw flux on every spatial set.
This equality does not replace any needed Fubini integrability assertion. -/
theorem expected_rawCellFlux_congr_grad_ae {d : ℕ} {K : ℝ}
    (P : Measure (Coefficient d K)) (g h : Coefficient d K → Vec d → Vec d)
    (e : Vec d) (U : Set (Vec d)) (hgh : ∀ᵐ a ∂P, g a =ᵐ[volume] h a) :
    (∫ a, ∫ x in U, (a x).mulVec (e + g a x) ∂volume ∂P) =
      ∫ a, ∫ x in U, (a x).mulVec (e + h a x) ∂volume ∂P := by
  apply integral_congr_ae
  filter_upwards [hgh] with a ha
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae ha] with x hx
  rw [hx]

/-- Nonnegative slice integrals control the joint integral, with all
integrability premises made explicit. -/
theorem integrable_prod_of_nonnegative_slices
    {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    (P : Measure Ω) (μ : Measure A) [SFinite μ] (J : Ω → A → ℝ)
    (hJ : Measurable (Function.uncurry J))
    (hi : ∀ᵐ a ∂P, Integrable (J a) μ)
    (hn : ∀ᵐ a ∂P, ∀ᵐ x ∂μ, 0 ≤ J a x)
    (hm : Integrable (fun a => ∫ x, J a x ∂μ) P) :
    Integrable (Function.uncurry J) (P.prod μ) := by
  apply (integrable_prod_iff hJ.stronglyMeasurable.aestronglyMeasurable).mpr
  refine ⟨hi, hm.congr ?_⟩
  filter_upwards [hn] with a ha
  exact integral_congr_ae (ha.mono fun x hx => (Real.norm_of_nonneg hx).symm)

/-- Source stationarity remains valid for the measurable flux representative. -/
theorem sourceFluxRepresentative_stationary {d : ℕ} {K : ℝ}
    (P : Measure (Coefficient d K)) (g : Coefficient d K → Vec d → Vec d)
    (e : Vec d)
    (hs : ∀ z : LatticeIndex d, ∀ᵐ a ∂P, ∀ᵐ x ∂(volume : Measure (Vec d)),
      g a (x + latticeShift z) = g (translateCoefficient (latticeShift z) a) x) :
    ∀ z : LatticeIndex d, ∀ᵐ a ∂P, ∀ᵐ x ∂(volume : Measure (Vec d)),
      sourceFluxRepresentative g e a (x + latticeShift z) =
      sourceFluxRepresentative g e (translateCoefficient (latticeShift z) a) x := by
  intro z
  filter_upwards [hs z] with a ha
  have hm := measurePreserving_add_right (volume : Measure (Vec d)) (latticeShift z)
  have ht := hm.quasiMeasurePreserving.ae (sourceFluxRepresentative_ae_eq g e a)
  filter_upwards [ha, ht,
    sourceFluxRepresentative_ae_eq g e (translateCoefficient (latticeShift z) a)] with x hx ht hx'
  rw [ht, hx', hx]
  simp only [translateCoefficient, add_comm]

end EinsteinRelation.Correctors
