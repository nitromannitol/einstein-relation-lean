import EinsteinRelation.Correctors.HeatConvolutionMeasurability
import EinsteinRelation.External.AKMCorrectorOscillation
import EinsteinRelation.Correctors.PhysicalLocalL2Moments
open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM
/-- Source: `paper/main.tex:718-745`. A measurable scalar field has
measurable local root-integrals in every measurable random gauge. -/
theorem measurable_scalar_local_root {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} (u : Ω → Vec d → ℝ) (c : Ω → ℝ)
    (hu : Measurable (Function.uncurry u)) (hc : Measurable c)
    (z : Vec d) (R : ℝ) :
    Measurable (fun ω => Real.sqrt (∫ x in ball z R, |u ω x - c ω| ^ 2 ∂volume)) := by
  have hs : Measurable (fun q : Ω × Vec d => |u q.1 q.2 - c q.1| ^ 2) :=
    (continuous_abs.measurable.comp (hu.sub (hc.comp measurable_fst))).pow_const 2
  exact (hs.stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (ball z R))).measurable.sqrt
/-- Source: `paper/main.tex:733-745`. Frobenius local root-integrals are
measurable without any new matrix norm instance. -/
theorem measurable_tensor_local_root {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} (S : Ω → Vec d → Mat d) (c : Ω → Mat d)
    (hS : Measurable (Function.uncurry S)) (hc : Measurable c)
    (z : Vec d) (R : ℝ) :
    Measurable (fun ω => Real.sqrt (∫ x in ball z R,
      frobeniusNorm (S ω x - c ω) ^ 2 ∂volume)) := by
  have hentry (j k : Fin d) : Measurable (fun q : Ω × Vec d => S q.1 q.2 j k - c q.1 j k) :=
    ((show Continuous (fun A : Mat d => A j k) by fun_prop).measurable.comp hS).sub
      (((show Continuous (fun A : Mat d => A j k) by fun_prop).measurable.comp hc).comp measurable_fst)
  have hF : Measurable (fun q : Ω × Vec d => frobeniusNorm (S q.1 q.2 - c q.1)) := by
    unfold frobeniusNorm frobeniusSq
    apply Measurable.sqrt
    exact Finset.measurable_sum _ fun j _ => Finset.measurable_sum _ fun k _ =>
      (hentry j k).mul (hentry j k)
  exact ((hF.pow_const 2).stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (ball z R))).measurable.sqrt
/-- Source: `paper/main.tex:733-745`. Frobenius local root-averages are
measurable without any new matrix norm instance. -/
theorem measurable_tensor_local_average_root {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} (S : Ω → Vec d → Mat d) (c : Ω → Mat d)
    (hS : Measurable (Function.uncurry S)) (hc : Measurable c)
    (z : Vec d) (R : ℝ) :
    Measurable (fun ω => Real.sqrt (⨍ x in ball z R,
      frobeniusNorm (S ω x - c ω) ^ 2 ∂volume)) := by
  have hentry (j k : Fin d) : Measurable (fun q : Ω × Vec d => S q.1 q.2 j k - c q.1 j k) :=
    ((show Continuous (fun A : Mat d => A j k) by fun_prop).measurable.comp hS).sub
      (((show Continuous (fun A : Mat d => A j k) by fun_prop).measurable.comp hc).comp measurable_fst)
  have hF : Measurable (fun q : Ω × Vec d => frobeniusNorm (S q.1 q.2 - c q.1)) := by
    unfold frobeniusNorm frobeniusSq
    apply Measurable.sqrt
    exact Finset.measurable_sum _ fun j _ => Finset.measurable_sum _ fun k _ =>
      (hentry j k).mul (hentry j k)
  simp only [average_eq, smul_eq_mul]
  exact (measurable_const.mul ((hF.pow_const 2).stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (ball z R))).measurable).sqrt
/-- Source: `paper/main.tex:718-723`. Parameterized heat averages of a
jointly measurable scalar field are measurable. -/
theorem measurable_scalarHeatAverage {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} (u : Ω → Vec d → ℝ) (hu : Measurable (Function.uncurry u))
    (z : Vec d) (R : ℝ) :
    Measurable (fun ω => scalarHeatAverage (u ω) z R) := by
  have hK : Measurable (fun x : Vec d => heatKernel z R x) := by
    unfold heatKernel
    exact measurable_euclideanHeatKernel_joint.comp
      (measurable_const.prodMk (measurable_id.sub measurable_const))
  exact ((hK.comp measurable_snd).mul hu).stronglyMeasurable.integral_prod_right'.measurable
/-- Source: `paper/main.tex:733-745`. The tensor heat gauge is measurable
entry by entry. -/
theorem measurable_fluxHeatAverage {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} (S : Ω → Vec d → Mat d) (hS : Measurable (Function.uncurry S))
    (z : Vec d) (R : ℝ) :
    Measurable (fun ω => fluxHeatAverage (S ω) z R) := by
  change @Measurable Ω (Fin d → Fin d → ℝ) _ (borel _) _
  rw [← (Pi.borelSpace (X := fun _ : Fin d => Fin d → ℝ)).measurable_eq]
  apply measurable_pi_lambda
  intro j
  apply measurable_pi_lambda
  intro k
  exact measurable_scalarHeatAverage (fun ω x => S ω x j k)
    ((show Continuous (fun A : Mat d => A j k) by fun_prop).measurable.comp hS) z R
end EinsteinRelation.Correctors
