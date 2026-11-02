import EinsteinRelation.Calculus.Weak

open MeasureTheory
namespace EinsteinRelation

/-- Restriction of a spatial weak derivative to a smaller measurable domain
(`paper/main.tex:693–698,727–729`). -/
theorem HasWeakPartialDerivative.restrict {d : ℕ} {U V : Set (Vec d)}
    (hUV : U ⊆ V) (hU : MeasurableSet U) (hV : MeasurableSet V)
    {i : Fin d} {f g : Vec d → ℝ} (h : HasWeakPartialDerivative V i f g) :
    HasWeakPartialDerivative U i f g := by
  refine ⟨h.1.mono_set hUV, h.2.1.mono_set hUV, ?_⟩
  intro φ hφ
  have hl := setIntegral_eq_of_subset_of_forall_diff_eq_zero (μ := volume) hV hUV
    (f := fun x => f x * coordinateDerivative i φ x)
    (fun x hx => by
      have hderiv : coordinateDerivative i φ x = 0 := by
        rw [coordinateDerivative, fderiv_of_notMem_tsupport ℝ (fun ht => hx.2 (hφ.2.2 ht)),
          ContinuousLinearMap.zero_apply]
      rw [hderiv, mul_zero])
  have hr := setIntegral_eq_of_subset_of_forall_diff_eq_zero (μ := volume) hV hUV
    (f := fun x => g x * φ x)
    (fun x hx => by
      have hφzero : φ x = 0 :=
        (notMem_tsupport_iff_eventuallyEq.mp (fun ht => hx.2 (hφ.2.2 ht))).self_of_nhds
      rw [hφzero, mul_zero])
  rw [← hl, ← hr]
  exact h.2.2 φ ⟨hφ.1, hφ.2.1, hφ.2.2.trans hUV⟩

end EinsteinRelation
