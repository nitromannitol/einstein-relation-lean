import EinsteinRelation.Correctors.HeatTransferConvolution
import EinsteinRelation.Probability.LocalSigma
import Mathlib.Analysis.Convolution

/-!
# Fubini for signed stationary convolutions

The absolute-integrability justification for the convolution and time changes of order in
`paper/main.tex:1018–1022`. Only stationarity and an integrable environment observable are used.
-/

open MeasureTheory
noncomputable section
namespace EinsteinRelation.Correctors
variable {d : ℕ}

/-- An integrable weight times any measurable translate of an integrable stationary
observable is integrable jointly in the weight parameter and the environment. -/
@[nolint unusedArguments]
theorem integrable_stationary_weight {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [SigmaFinite ν]
    (Q : Measure (FieldPair d)) [SFinite Q] (hQ : IsStationary Q)
    {w : X → ℝ} (hw : Measurable w) (hwi : Integrable w ν)
    {a : X → Vec d} (ha : Measurable a)
    {f : FieldPair d → ℝ} (hf : Measurable f) (hfi : Integrable f Q) :
    Integrable (fun p : X × FieldPair d => w p.1 * f (translate (a p.1) p.2))
      (ν.prod Q) := by
  have hj : Measurable (fun p : X × FieldPair d => w p.1 * f (translate (a p.1) p.2)) :=
    (hw.comp measurable_fst).mul (hf.comp
      (Probability.continuous_translate.measurable.comp
        ((ha.comp measurable_fst).prodMk measurable_snd)))
  apply (integrable_prod_iff hj.aestronglyMeasurable).2
  refine ⟨ae_of_all _ fun x =>
    ((measurePreserving_translate Q hQ (a x)).integrable_comp_of_integrable hfi).const_mul (w x), ?_⟩
  have hn : (fun x => ∫ ω, ‖w x * f (translate (a x) ω)‖ ∂Q) =
      fun x => ‖w x‖ * ∫ ω, ‖f ω‖ ∂Q := by
    funext x
    simp only [norm_mul, integral_const_mul]
    rw [Probability.integral_translate Q hQ (a x) (fun ω => ‖f ω‖) hf.norm]
  rw [hn]
  exact hwi.norm.mul_const _

/-- Associativity of actual horizontal convolution with two signed integrable kernels,
justified by absolute integrability under the stationary law (`paper/main.tex:1018–1022`). -/
theorem horizontalMollify_comp_ae
    (Q : Measure (FieldPair d)) [SFinite Q] (hQ : IsStationary Q)
    {K L : Vec d → ℝ} (hK : Measurable K) (hKi : Integrable K)
    (hL : Measurable L) (hLi : Integrable L)
    {f : FieldPair d → ℝ} (hf : Measurable f) (hfi : Integrable f Q) :
    horizontalMollify K (horizontalMollify L f) =ᵐ[Q]
      horizontalMollify (fun y => ∫ x, K x * L (y - x)) f := by
  have hw : Measurable (fun p : Vec d × Vec d => K p.2 * L (p.1 - p.2)) :=
    (hK.comp measurable_snd).mul (hL.comp (measurable_fst.sub measurable_snd))
  have hwi : Integrable (fun p : Vec d × Vec d => K p.2 * L (p.1 - p.2)) := by
    simpa only [ContinuousLinearMap.lsmul_apply, smul_eq_mul] using!
      hKi.convolution_integrand (ContinuousLinearMap.lsmul ℝ ℝ) hLi
  have hi := integrable_stationary_weight ((volume : Measure (Vec d)).prod volume)
    Q hQ hw hwi measurable_fst hf hfi
  filter_upwards [hi.prod_left_ae] with ω hω
  have hω' : Integrable (fun p : Vec d × Vec d =>
      K p.2 * L (p.1 - p.2) * f (translate p.1 ω)) := hω
  unfold horizontalMollify
  simp only [← integral_const_mul, translate_add]
  calc
    (∫ x, ∫ z, K x * (L z * f (translate (z + x) ω))) =
        ∫ x, ∫ y, K x * L (y - x) * f (translate y ω) := by
      apply integral_congr_ae
      exact ae_of_all _ fun x => by
        have h := integral_add_right_eq_self (μ := (volume : Measure (Vec d)))
          (fun y => K x * L (y - x) * f (translate y ω)) x
        simpa only [add_sub_cancel_right, mul_assoc] using h
    _ = ∫ y, ∫ x, K x * L (y - x) * f (translate y ω) :=
      integral_integral_swap hω'.swap
    _ = ∫ y, (∫ x, K x * L (y - x)) * f (translate y ω) := by
      simp only [integral_mul_const]

end EinsteinRelation.Correctors
