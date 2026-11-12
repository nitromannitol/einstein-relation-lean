import EinsteinRelation.Correctors.AKMParabolicIntegrability
import EinsteinRelation.Correctors.ParabolicCutoffGlobalWeakGradient
import EinsteinRelation.Correctors.ParabolicTimeReflection

open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- Reversing time in a weak forward equation gives the backward equation.
Source: `paper/main.tex:787–792,850`; AKM Proposition E.1 proof. -/
theorem parabolicSolution_time_reverse_weak {d : ℕ} {K : ℝ}
    (hK : 0 < K) {A : Coefficient d K} {a b T : ℝ} {U : Set (Vec d)}
    {v : ℝ × Vec d → ℝ} {H : ℝ × Vec d → Vec d}
    (hv : IsParabolicSolution A (Set.Ioo (T-b) (T-a)) U v H)
    {ψ : ℝ × Vec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) (hψs : tsupport ψ ⊆ Set.Ioo a b ×ˢ U) :
    Integrable (fun z => v (T-z.1,z.2) * fderiv ℝ ψ z (1,0) +
      dot ((A z.2).mulVec (H (T-z.1,z.2)))
        (fun j => fderiv ℝ ψ z (0,unitVector j)))
      (volume.restrict (Set.Ioo a b ×ˢ U)) ∧
    (∫ z in Set.Ioo a b ×ˢ U, v (T-z.1,z.2) * fderiv ℝ ψ z (1,0) +
      dot ((A z.2).mulVec (H (T-z.1,z.2)))
        (fun j => fderiv ℝ ψ z (0,unitVector j))) = 0 := by
  let e : (ℝ × Vec d) ≃ₜ (ℝ × Vec d) :=
    (Homeomorph.subLeft T).prodCongr (Homeomorph.refl _)
  have he (z : ℝ × Vec d) : e z = (T-z.1,z.2) := rfl
  have hei (z : ℝ × Vec d) : e (e z) = z := by simp [he]
  have heD : ContDiff ℝ (⊤ : ℕ∞) (e : (ℝ × Vec d) → (ℝ × Vec d)) := by
    change ContDiff ℝ (⊤ : ℕ∞) (fun z : ℝ × Vec d => (T-z.1,z.2))
    fun_prop
  let Ψ := ψ ∘ e
  have hΨ := hψ.comp heD
  have hΨc : HasCompactSupport Ψ := hψc.comp_homeomorph e
  have hΨs : tsupport Ψ ⊆ interior (Set.Ioo (T-b) (T-a)) ×ˢ U := by
    rw [interior_Ioo]
    intro z hz
    have hz' : e z ∈ tsupport ψ := by
      simpa only [Ψ, tsupport_comp_eq_preimage] using hz
    have hs := hψs hz'
    exact ⟨⟨by change T-b < z.1; have := hs.1.2; rw [he] at this; dsimp at this; linarith,
      by change z.1 < T-a; have := hs.1.1; rw [he] at this; dsimp at this; linarith⟩, hs.2⟩
  have hDt (z : ℝ × Vec d) : fderiv ℝ Ψ z (1,0) = -fderiv ℝ ψ (e z) (1,0) := by
    dsimp [Ψ]
    rw [fderiv_comp z (hψ.differentiable (by simp) _) (heD.differentiable (by simp) _)]
    change (fderiv ℝ ψ (e z)) ((fderiv ℝ (fun z : ℝ × Vec d => (T-z.1,z.2)) z) (1,0)) = _
    have hp : DifferentiableAt ℝ (fun w : ℝ × Vec d => T-w.1) z := by fun_prop
    have hs : DifferentiableAt ℝ (fun w : ℝ × Vec d => w.2) z := differentiableAt_snd
    rw [hp.fderiv_prodMk hs]
    simp only [fderiv_const_sub, fderiv_fst, fderiv_snd,
      ContinuousLinearMap.prod_apply, ContinuousLinearMap.neg_apply,
      ]
    change (fderiv ℝ ψ (e z)) (-1,0) = _
    rw [show ((-1 : ℝ),(0 : Vec d)) = -((1 : ℝ),(0 : Vec d)) by simp]
    exact map_neg _ _
  have hDx (z : ℝ × Vec d) (j : Fin d) :
      fderiv ℝ Ψ z (0,unitVector j) = fderiv ℝ ψ (e z) (0,unitVector j) := by
    dsimp [Ψ]
    rw [fderiv_comp z (hψ.differentiable (by simp) _) (heD.differentiable (by simp) _)]
    change (fderiv ℝ ψ (e z)) ((fderiv ℝ (fun z : ℝ × Vec d => (T-z.1,z.2)) z) (0,unitVector j)) = _
    have hp : DifferentiableAt ℝ (fun w : ℝ × Vec d => T-w.1) z := by fun_prop
    have hs : DifferentiableAt ℝ (fun w : ℝ × Vec d => w.2) z := differentiableAt_snd
    rw [hp.fderiv_prodMk hs]
    simp [fderiv_const_sub, fderiv_fst, fderiv_snd]
  let f := fun z => -(v z) * fderiv ℝ Ψ z (1,0) +
    dot ((A z.2).mulVec (H z)) (fun j => fderiv ℝ Ψ z (0,unitVector j))
  have hf := parabolicSolution_test_integrable hK A hv hΨ hΨc
  have hzero := hv.2.2.2.2 Ψ hΨ hΨc hΨs
  have htrans (z : ℝ × Vec d) : f (e z) =
      v (T-z.1,z.2) * fderiv ℝ ψ z (1,0) +
      dot ((A z.2).mulVec (H (T-z.1,z.2)))
        (fun j => fderiv ℝ ψ z (0,unitVector j)) := by
    dsimp only [f]
    simp_rw [hDt, hDx, hei, he]
    ring
  have hmp := akm_time_reflection_cylinder_measurePreserving d T a b U
  refine ⟨?_, ?_⟩
  · have hh : Integrable (fun z => f (e z)) (volume.restrict (Set.Ioo a b ×ˢ U)) :=
      hmp.integrable_comp_of_integrable hf
    simpa only [htrans] using hh
  · calc
      _ = ∫ z in Set.Ioo a b ×ˢ U, f (e z) := integral_congr_ae (Filter.Eventually.of_forall fun z => (htrans z).symm)
      _ = ∫ z in Set.Ioo (T-b) (T-a) ×ˢ U, f z := hmp.integral_comp e.toMeasurableEquiv.measurableEmbedding f
      _ = 0 := hzero

end EinsteinRelation.Correctors
