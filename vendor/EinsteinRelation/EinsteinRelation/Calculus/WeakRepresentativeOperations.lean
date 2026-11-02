import EinsteinRelation.Correctors.WeakEquationAeTransport
import EinsteinRelation.External.GilbargTrudinger

/-!
# Restricting and replacing spatial weak representatives

Source: `paper/main.tex:693-698,727-729`. These operations retain the
distributional equations when replacing representatives on null sets or
restricting their spatial domain.
-/

open MeasureTheory Filter

namespace EinsteinRelation

private theorem locallyIntegrableOn_congr_ae {d : ℕ} {U : Set (Vec d)}
    {f g : Vec d → ℝ} (hf : LocallyIntegrableOn f U volume)
    (hfg : f =ᵐ[volume.restrict U] g) : LocallyIntegrableOn g U volume := by
  intro x hx
  obtain ⟨s, hs, hi⟩ := hf x hx
  refine ⟨s ∩ U, inter_mem hs self_mem_nhdsWithin, ?_⟩
  exact (hi.mono_set Set.inter_subset_left).congr
    (hfg.filter_mono (ae_mono (Measure.restrict_mono_set volume Set.inter_subset_right)))

/-- Replacing both representatives preserves a spatial weak partial derivative. -/
theorem HasWeakPartialDerivative.congr_ae {d : ℕ} {U : Set (Vec d)} {i : Fin d}
    {f g f' g' : Vec d → ℝ} (h : HasWeakPartialDerivative U i f g)
    (hf : f =ᵐ[volume.restrict U] f') (hg : g =ᵐ[volume.restrict U] g') :
    HasWeakPartialDerivative U i f' g' := by
  refine ⟨locallyIntegrableOn_congr_ae h.1 hf,
    locallyIntegrableOn_congr_ae h.2.1 hg, ?_⟩
  intro φ hφ
  have hfint := integral_congr_ae (hf.mono fun x hx => congrArg (· * coordinateDerivative i φ x) hx)
  have hgint := integral_congr_ae (hg.mono fun x hx => congrArg (· * φ x) hx)
  rw [← hfint, ← hgint]
  exact h.2.2 φ hφ

/-- Replacing both representatives preserves a spatial weak divergence. -/
theorem HasWeakDivergence.congr_ae {d : ℕ} {U : Set (Vec d)}
    {F G : Vec d → Vec d} {h k : Vec d → ℝ}
    (hw : HasWeakDivergence U F h)
    (hF : F =ᵐ[volume.restrict U] G) (hh : h =ᵐ[volume.restrict U] k) :
    HasWeakDivergence U G k := by
  refine ⟨fun i => locallyIntegrableOn_congr_ae (hw.1 i)
    (hF.mono fun x hx => congrArg (fun z : Vec d => z i) hx),
    locallyIntegrableOn_congr_ae hw.2.1 hh, ?_⟩
  intro φ hφ
  rw [← integral_congr_ae (hF.mono fun x hx => congrArg (fun z => dot z (gradient φ x)) hx),
    ← integral_congr_ae (hh.mono fun x hx => congrArg (· * φ x) hx)]
  exact hw.2.2 φ hφ

private theorem test_eq_zero_outside {d : ℕ} {U : Set (Vec d)} {φ : Vec d → ℝ}
    (hφ : IsSpatialTest U φ) {x : Vec d} (hx : x ∉ U) : φ x = 0 :=
  (notMem_tsupport_iff_eventuallyEq.mp (fun ht => hx (hφ.2.2 ht))).self_of_nhds

private theorem test_derivative_eq_zero_outside {d : ℕ} {U : Set (Vec d)} {φ : Vec d → ℝ}
    (hφ : IsSpatialTest U φ) (i : Fin d) {x : Vec d} (hx : x ∉ U) :
    coordinateDerivative i φ x = 0 := by
  simp only [coordinateDerivative, fderiv_of_notMem_tsupport ℝ (fun ht => hx (hφ.2.2 ht)),
    ContinuousLinearMap.zero_apply]

/-- Restrict a weak partial derivative; the derivative of a test vanishes
outside its support, so the larger-domain equation has the same integrals. -/
theorem HasWeakPartialDerivative.restrict_subset {d : ℕ} {U V : Set (Vec d)}
    (hUV : U ⊆ V) (hV : MeasurableSet V)
    {i : Fin d} {f g : Vec d → ℝ} (h : HasWeakPartialDerivative V i f g) :
    HasWeakPartialDerivative U i f g := by
  refine ⟨h.1.mono_set hUV, h.2.1.mono_set hUV, ?_⟩
  intro φ hφ
  have hl := setIntegral_eq_of_subset_of_forall_diff_eq_zero (μ := volume) hV hUV
    (f := fun x => f x * coordinateDerivative i φ x)
    (fun x hx => by
      change f x * coordinateDerivative i φ x = 0
      rw [test_derivative_eq_zero_outside hφ i hx.2, mul_zero])
  have hr := setIntegral_eq_of_subset_of_forall_diff_eq_zero (μ := volume) hV hUV
    (f := fun x => g x * φ x)
    (fun x hx => by
      rw [test_eq_zero_outside hφ hx.2, mul_zero])
  rw [← hl, ← hr]
  exact h.2.2 φ ⟨hφ.1, hφ.2.1, hφ.2.2.trans hUV⟩

/-- Restrict a weak divergence using the support of the scalar test. -/
theorem HasWeakDivergence.restrict_subset {d : ℕ} {U V : Set (Vec d)}
    (hUV : U ⊆ V) (hV : MeasurableSet V)
    {F : Vec d → Vec d} {h : Vec d → ℝ} (hw : HasWeakDivergence V F h) :
    HasWeakDivergence U F h := by
  refine ⟨fun i => (hw.1 i).mono_set hUV, hw.2.1.mono_set hUV, ?_⟩
  intro φ hφ
  have hl := setIntegral_eq_of_subset_of_forall_diff_eq_zero (μ := volume) hV hUV
    (f := fun x => dot (F x) (gradient φ x)) (fun x hx => by
      have hg : gradient φ x = 0 := funext fun i => test_derivative_eq_zero_outside hφ i hx.2
      simp only [hg, dot, Pi.zero_apply, mul_zero, Finset.sum_const_zero])
  have hr := setIntegral_eq_of_subset_of_forall_diff_eq_zero (μ := volume) hV hUV
    (f := fun x => h x * φ x)
    (fun x hx => by
      rw [test_eq_zero_outside hφ hx.2, mul_zero])
  rw [← hl, ← hr]
  exact hw.2.2 φ ⟨hφ.1, hφ.2.1, hφ.2.2.trans hUV⟩

namespace Correctors

open External.GilbargTrudinger

/-- Restriction preserves the actual scalar Sobolev weak solution. -/
theorem weakSolution_restrict_subset {d : ℕ} {U V : Set (Vec d)}
    (hU : MeasurableSet U) (hVU : V ⊆ U)
    {a : Vec d → Mat d} {u : Vec d → ℝ} {g : Vec d → Vec d}
    (hw : WeakSolution U a u g) : WeakSolution V a u g :=
  ⟨hw.1.mono_measure (Measure.restrict_mono_set volume hVU),
    hw.2.1.mono_measure (Measure.restrict_mono_set volume hVU),
    fun i => (hw.2.2.1 i).restrict_subset hVU hU, hw.2.2.2.restrict_subset hVU hU⟩

end Correctors

end EinsteinRelation
