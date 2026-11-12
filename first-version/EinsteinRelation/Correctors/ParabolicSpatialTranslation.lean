import EinsteinRelation.Correctors.ParabolicSpatialRestriction
import EinsteinRelation.Correctors.AKMHeatKernelEnergySlices
import EinsteinRelation.Calculus.WeakGradientTranslation
import Mathlib.MeasureTheory.Group.Prod

open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- Translation of an energy solution with actual whole-space weak
spatial gradients. Source: `paper/main.tex:787–806,850`. -/
theorem parabolicSolution_translate_space_of_global_gradient {d : ℕ} {K : ℝ}
    {A : Coefficient d K} {I : Set ℝ} {U : Set (Vec d)}
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hsol : IsParabolicSolution A I U u G)
    (hw : ∀ᵐ t ∂volume.restrict I,
      HasWeakGradient Set.univ (fun x => u (t,x)) (fun x => G (t,x)))
    (a : Vec d) :
    IsParabolicSolution (translateCoefficient a A) I
      ((fun x => a+x) ⁻¹' U)
      (fun z => u (z.1,a+z.2)) (fun z => G (z.1,a+z.2)) := by
  letI : Measure.IsAddHaarMeasure (volume : Measure (ℝ × Vec d)) :=
    Measure.prod.instIsAddHaarMeasure volume volume
  let T : ℝ × Vec d → ℝ × Vec d := fun z => (0,a)+z
  have hT (z : ℝ × Vec d) : T z = (z.1,a+z.2) := by ext <;> simp [T]
  have hTp : MeasurePreserving T volume volume := measurePreserving_add_left volume (0,a)
  have hTe : MeasurableEmbedding T :=
    (MeasurableEquiv.addLeft ((0 : ℝ),a)).measurableEmbedding
  have hpre : T ⁻¹' (I ×ˢ U) = I ×ˢ ((fun x => a+x) ⁻¹' U) := by
    ext z
    simp only [Set.mem_preimage,Set.mem_prod,hT]
  have hTr : MeasurePreserving T
      (volume.restrict (I ×ˢ ((fun x => a+x) ⁻¹' U)))
      (volume.restrict (I ×ˢ U)) := by
    simpa only [hpre] using hTp.restrict_preimage_emb hTe (I ×ˢ U)
  refine ⟨?_,?_,?_,?_,?_⟩
  · simpa only [Function.comp_def,hT] using hsol.1.comp_measurePreserving hTr
  · simpa only [Function.comp_def,hT] using hsol.2.1.comp_measurePreserving hTr
  · simpa only [Function.comp_def,hT] using hsol.2.2.1.comp_measurePreserving hTr
  · filter_upwards [hw] with t ht
    exact hasWeakGradient_mono (Set.subset_univ _) (HasWeakGradient.translated ht a)
  · intro ψ hψ hψc hψs
    let φ : ℝ × Vec d → ℝ := fun z => ψ ((0,-a)+z)
    have hφ : ContDiff ℝ (⊤ : ℕ∞) φ := hψ.comp (contDiff_const.add contDiff_id)
    have hφc : HasCompactSupport φ :=
      hψc.comp_homeomorph (Homeomorph.addLeft ((0 : ℝ),-a))
    have hs : tsupport φ ⊆ (fun z : ℝ × Vec d => (0,-a)+z) ⁻¹' tsupport ψ := by
      apply closure_minimal ?_ ((isClosed_tsupport ψ).preimage (continuous_const.add continuous_id))
      intro z hz
      exact subset_tsupport ψ hz
    have hφs : tsupport φ ⊆ interior I ×ˢ U := by
      intro z hz
      obtain ⟨ht,hx⟩ := hψs (hs hz)
      simpa only [Prod.fst_add,Prod.snd_add,zero_add,Set.mem_preimage,
        add_neg_cancel_left] using And.intro ht hx
    have hD (z v : ℝ × Vec d) : fderiv ℝ φ (T z) v = fderiv ℝ ψ z v := by
      dsimp only [φ]
      rw [fderiv_comp_add_left]
      have he : ((0 : ℝ),-a)+T z = z := by ext <;> simp [T]
      rw [he]
    have hid := hTr.integral_comp hTe
      (fun z => -(u z)*fderiv ℝ φ z (1,0) +
        dot ((A z.2).mulVec (G z)) (fun j => fderiv ℝ φ z (0,unitVector j)))
    have heq := hsol.2.2.2.2 φ hφ hφc hφs
    rw [← hid] at heq
    have hD' (z w : ℝ × Vec d) : fderiv ℝ φ (z.1,a+z.2) w = fderiv ℝ ψ z w := by
      rw [← hT z]
      exact hD z w
    simpa only [hT,hD',translateCoefficient] using heq

/-- Every positive bounded cylinder of a whole-space energy solution may
be centered at any spatial point. Source: `paper/main.tex:787–806,850`. -/
theorem parabolicFamily_translate_space {d : ℕ} {K : ℝ}
    {A : Coefficient d K} {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hsol : ∀ a b R : ℝ, 0 < a → a < b → 0 < R →
      IsParabolicSolution A (Set.Ioo a b) (originBall d R) u G)
    (v : Vec d) :
    ∀ a b R : ℝ, 0 < a → a < b → 0 < R →
      IsParabolicSolution (translateCoefficient v A) (Set.Ioo a b) (originBall d R)
        (fun z => u (z.1,v+z.2)) (fun z => G (z.1,v+z.2)) := by
  intro a b R ha hab hR
  have hv : 0 ≤ euclideanNorm v := Real.sqrt_nonneg _
  let S := euclideanNorm v+R+1
  have hS : 0 < S := by dsimp only [S]; linarith
  have hw : ∀ᵐ t ∂volume.restrict (Set.Ioo a b),
      HasWeakGradient Set.univ (fun x => u (t,x)) (fun x => G (t,x)) := by
    have hsub : Set.Ioo a b ⊆ Set.Ioi 0 := fun t ht => ha.trans ht.1
    exact ((akm_fundamental_energy_slices hsol).filter_mono
      (ae_mono (Measure.restrict_mono hsub le_rfl))).mono fun _ ht => ht.1
  have hh := parabolicSolution_translate_space_of_global_gradient
    (hsol a b S ha hab hS) hw v
  apply parabolicSolution_restrict_space (hsol := hh)
  intro x hx
  change euclideanNorm (v+x) < S
  change euclideanNorm x < R at hx
  exact (TimeChange.euclideanNorm_add_le v x).trans_lt (by dsimp only [S]; linarith)

end EinsteinRelation.Correctors
