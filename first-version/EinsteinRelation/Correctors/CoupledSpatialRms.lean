import EinsteinRelation.Correctors.SpatialGradientTimeMinkowski

/-! # Passing a spatial RMS approximation bound to a coupling

Source: `paper/main.tex:842–854`. The coupled norm of the limiting field
is controlled by the coupled approximant and the two marginal errors.
The spatial L2 memberships are proved before real RMS norms are used.
-/

open MeasureTheory
open scoped ENNReal
noncomputable section
namespace EinsteinRelation.Correctors

/-- A coupled finite-time estimate and marginal spatial approximation
estimates control the coupled limiting spatial energy.
Source: `paper/main.tex:842–854`. -/
theorem coupled_spatial_rms_approximation
    {Ω Z X E : Type*} [MeasurableSpace Ω] [MeasurableSpace Z] [MeasurableSpace X]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E]
    (Q : Measure Ω) (P : Measure Z) (ν : Measure X) [SFinite ν]
    (π₁ π₂ : Z → Ω) (hπ₁ : MeasurePreserving π₁ P Q) (hπ₂ : MeasurePreserving π₂ P Q)
    (f g : Ω × X → E) (hf : Measurable f) (hg : Measurable g)
    {p : ℝ≥0∞} (hp : 1 ≤ p) {B K : ℝ} (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hlocal : ∀ᵐ ω ∂Q, MemLp (fun x => f (ω,x)-g (ω,x)) 2 ν)
    (hpaired : ∀ᵐ z ∂P, MemLp (fun x => g (π₁ z,x)-g (π₂ z,x)) 2 ν)
    (hb : eLpNorm (fun ω => Real.sqrt (∫ x, ‖f (ω,x)-g (ω,x)‖^2 ∂ν)) p Q ≤
      ENNReal.ofReal K)
    (hbp : eLpNorm (fun z => Real.sqrt (∫ x, ‖g (π₁ z,x)-g (π₂ z,x)‖^2 ∂ν)) p P ≤
      ENNReal.ofReal B) :
    (∀ᵐ z ∂P, MemLp (fun x => f (π₁ z,x)-f (π₂ z,x)) 2 ν) ∧
      MemLp (fun z => Real.sqrt (∫ x, ‖f (π₁ z,x)-f (π₂ z,x)‖^2 ∂ν)) p P ∧
      eLpNorm (fun z => Real.sqrt (∫ x, ‖f (π₁ z,x)-f (π₂ z,x)‖^2 ∂ν)) p P ≤
        ENNReal.ofReal (B+2*K) := by
  let e : Ω → ℝ := fun ω => Real.sqrt (∫ x, ‖f (ω,x)-g (ω,x)‖^2 ∂ν)
  let a : Z → ℝ := fun z => Real.sqrt (∫ x, ‖g (π₁ z,x)-g (π₂ z,x)‖^2 ∂ν)
  let b : Z → ℝ := fun z => Real.sqrt (∫ x, ‖f (π₁ z,x)-f (π₂ z,x)‖^2 ∂ν)
  have hem : Measurable e :=
    (((hf.sub hg).norm.pow_const 2).stronglyMeasurable.integral_prod_right').measurable.sqrt
  have ham : Measurable a :=
    ((((hg.comp (hπ₁.measurable.prodMap measurable_id)).sub
      (hg.comp (hπ₂.measurable.prodMap measurable_id))).norm.pow_const 2).stronglyMeasurable.integral_prod_right').measurable.sqrt
  have hbm : Measurable b :=
    ((((hf.comp (hπ₁.measurable.prodMap measurable_id)).sub
      (hf.comp (hπ₂.measurable.prodMap measurable_id))).norm.pow_const 2).stronglyMeasurable.integral_prod_right').measurable.sqrt
  have hpoint : ∀ᵐ z ∂P, MemLp (fun x => f (π₁ z,x)-f (π₂ z,x)) 2 ν ∧
      b z ≤ a z+e (π₁ z)+e (π₂ z) := by
    filter_upwards [hpaired,hπ₁.quasiMeasurePreserving.ae hlocal,
      hπ₂.quasiMeasurePreserving.ae hlocal] with z hz h₁ h₂
    have heq : (fun x => f (π₁ z,x)-f (π₂ z,x)) =
        fun x => (g (π₁ z,x)-g (π₂ z,x)) +
          (f (π₁ z,x)-g (π₁ z,x)) - (f (π₂ z,x)-g (π₂ z,x)) := by
      funext x
      abel
    have hm : MemLp (fun x => f (π₁ z,x)-f (π₂ z,x)) 2 ν :=
      heq ▸ (hz.add h₁).sub h₂
    refine ⟨hm,?_⟩
    have he : eLpNorm (fun x => f (π₁ z,x)-f (π₂ z,x)) 2 ν ≤
        eLpNorm (fun x => g (π₁ z,x)-g (π₂ z,x)) 2 ν +
          eLpNorm (fun x => f (π₁ z,x)-g (π₁ z,x)) 2 ν +
          eLpNorm (fun x => f (π₂ z,x)-g (π₂ z,x)) 2 ν := by
      rw [heq]
      exact (eLpNorm_sub_le (p := 2) (hz.add h₁).1 h₂.1 (by norm_num)).trans
        (add_le_add (eLpNorm_add_le (p := 2) hz.1 h₁.1 (by norm_num)) le_rfl)
    rw [eLpNorm_two_eq_ofReal_spatial_rms ν hm,
      eLpNorm_two_eq_ofReal_spatial_rms ν hz,eLpNorm_two_eq_ofReal_spatial_rms ν h₁,
      eLpNorm_two_eq_ofReal_spatial_rms ν h₂,
      ← ENNReal.ofReal_add (Real.sqrt_nonneg _) (Real.sqrt_nonneg _),
      ← ENNReal.ofReal_add (by positivity) (Real.sqrt_nonneg _)] at he
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp he
  have h₁ : AEStronglyMeasurable (e ∘ π₁) P :=
    (hem.comp hπ₁.measurable).aestronglyMeasurable
  have h₂ : AEStronglyMeasurable (e ∘ π₂) P :=
    (hem.comp hπ₂.measurable).aestronglyMeasurable
  have hnorm : eLpNorm b p P ≤ ENNReal.ofReal (B+2*K) := by
    calc
      _ ≤ eLpNorm (fun z => a z+e (π₁ z)+e (π₂ z)) p P := by
        apply eLpNorm_mono_ae
        filter_upwards [hpoint] with z hz
        simpa only [Real.norm_of_nonneg (show 0 ≤ b z by dsimp [b]; positivity),
          Real.norm_of_nonneg (show 0 ≤ a z+e (π₁ z)+e (π₂ z) by dsimp [a,e]; positivity)]
          using hz.2
      _ ≤ (eLpNorm a p P+eLpNorm (e ∘ π₁) p P)+eLpNorm (e ∘ π₂) p P :=
        (eLpNorm_add_le (ham.aestronglyMeasurable.add h₁) h₂ hp).trans
          (add_le_add (eLpNorm_add_le ham.aestronglyMeasurable h₁ hp) le_rfl)
      _ ≤ ENNReal.ofReal B+ENNReal.ofReal K+ENNReal.ofReal K := by
        rw [eLpNorm_comp_measurePreserving hem.aestronglyMeasurable hπ₁,
          eLpNorm_comp_measurePreserving hem.aestronglyMeasurable hπ₂]
        exact add_le_add (add_le_add hbp hb) hb
      _ = _ := by rw [← ENNReal.ofReal_add hB hK,← ENNReal.ofReal_add (by positivity) hK]; congr 1; ring
  exact ⟨hpoint.mono fun _ hz => hz.1,
    ⟨hbm.aestronglyMeasurable,hnorm.trans_lt ENNReal.ofReal_lt_top⟩,hnorm⟩

end EinsteinRelation.Correctors
