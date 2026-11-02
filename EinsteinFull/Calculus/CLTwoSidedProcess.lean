import EinsteinFull.Calculus.CLEnvironmentKernel
import EinsteinFull.Calculus.CLDisplacementInverse

/-!
# The two-sided environment process

The two-sided process lives on `TwoSidedSpace d`: an aperiodic environment at time zero and a
continuous two-sided displacement path. Its state at time `t` is the environment seen from the
particle, `translate (y t) ω₀`, and the displacement between two times is a Borel function of
the two states (`displacementInv`). Time shifts and reflections act on the space.

The law glues, at time zero, two conditionally independent forward paths of the environment
kernel from the environment law. A product of observables at times before and after zero then
integrates to the product of the two multi-time kernel means.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinFull EinsteinRelation

variable {d : ℕ}

/-- Aperiodic environment at time zero and two-sided displacement path. -/
abbrev TwoSidedSpace (d : ℕ) := aperiodicSet d × C(ℝ, Vec d)

/-- The environment seen from the particle at time `t`. -/
def tsState (t : ℝ) (ω : TwoSidedSpace d) : FieldPair d := translate (ω.2 t) ω.1

/-- The displacement between times `a` and `b`. -/
def tsDisp (a b : ℝ) (ω : TwoSidedSpace d) : Vec d := ω.2 b - ω.2 a

theorem tsDisp_eq_displacementInv (a b : ℝ) (ω : TwoSidedSpace d) :
    tsDisp a b ω = displacementInv (tsState a ω, tsState b ω) :=
  (displacementInv_translate_translate ω.1.2 _ _).symm

theorem tsDisp_add (a b c : ℝ) (ω : TwoSidedSpace d) :
    tsDisp a b ω + tsDisp b c ω = tsDisp a c ω := by
  simp only [tsDisp]
  abel

/-- The two-sided path seen from time `τ`. -/
def tsShiftPath (τ : ℝ) (y : C(ℝ, Vec d)) : C(ℝ, Vec d) :=
  ⟨fun t => y (t + τ) - y τ,
    (y.continuous.comp (continuous_id.add continuous_const)).sub continuous_const⟩

/-- The two-sided path reflected about time `τ`, seen from time `2τ`. -/
def tsReflPath (τ : ℝ) (y : C(ℝ, Vec d)) : C(ℝ, Vec d) :=
  ⟨fun t => y (2 * τ - t) - y (2 * τ),
    (y.continuous.comp (continuous_const.sub continuous_id)).sub continuous_const⟩

/-- Time shift by `τ`. -/
def tsShift (τ : ℝ) (ω : TwoSidedSpace d) : TwoSidedSpace d :=
  (⟨translate (ω.2 τ) ω.1, (translate_mem_aperiodicSet_iff _ _).2 ω.1.2⟩, tsShiftPath τ ω.2)

/-- Time reflection about `τ`. -/
def tsRefl (τ : ℝ) (ω : TwoSidedSpace d) : TwoSidedSpace d :=
  (⟨translate (ω.2 (2 * τ)) ω.1, (translate_mem_aperiodicSet_iff _ _).2 ω.1.2⟩,
    tsReflPath τ ω.2)

theorem tsState_shift (τ t : ℝ) (ω : TwoSidedSpace d) :
    tsState t (tsShift τ ω) = tsState (t + τ) ω := by
  simp only [tsState, tsShift, tsShiftPath, ContinuousMap.coe_mk]
  rw [translate_add, sub_add_cancel]

theorem tsState_refl (τ t : ℝ) (ω : TwoSidedSpace d) :
    tsState t (tsRefl τ ω) = tsState (2 * τ - t) ω := by
  simp only [tsState, tsRefl, tsReflPath, ContinuousMap.coe_mk]
  rw [translate_add, sub_add_cancel]

theorem tsDisp_shift (τ a b : ℝ) (ω : TwoSidedSpace d) :
    tsDisp a b (tsShift τ ω) = tsDisp (a + τ) (b + τ) ω := by
  simp only [tsDisp, tsShift, tsShiftPath, ContinuousMap.coe_mk]
  abel

theorem tsDisp_refl_mid (a b : ℝ) (ω : TwoSidedSpace d) :
    tsDisp a b (tsRefl ((a + b) / 2) ω) = -tsDisp a b ω := by
  simp only [tsDisp, tsRefl, tsReflPath, ContinuousMap.coe_mk]
  rw [show 2 * ((a + b) / 2) - b = a by ring, show 2 * ((a + b) / 2) - a = b by ring]
  abel

theorem measurable_tsPath_eval :
    Measurable fun p : ℝ × TwoSidedSpace d => p.2.2 p.1 :=
  measurable_uncurry_of_continuous_of_measurable (u := fun t (ω : TwoSidedSpace d) => ω.2 t)
    (fun ω => ω.2.continuous) fun t => (ContinuousMap.measurable_eval t).comp measurable_snd

theorem measurable_tsState_joint :
    Measurable fun p : ℝ × TwoSidedSpace d => tsState p.1 p.2 :=
  Localization.physicalTranslation_jointlyMeasurable.comp
    (measurable_tsPath_eval.prodMk (measurable_subtype_coe.comp (measurable_fst.comp measurable_snd)))

theorem measurable_tsState (t : ℝ) : Measurable (tsState (d := d) t) :=
  measurable_tsState_joint.comp (measurable_const.prodMk measurable_id)

theorem measurable_tsShift (τ : ℝ) : Measurable (tsShift (d := d) τ) := by
  refine Measurable.prodMk ?_ ?_
  · exact (measurable_tsState τ).subtype_mk
  · refine ContinuousMap.measurable_iff_eval.2 fun t => ?_
    exact ((ContinuousMap.measurable_eval _).comp measurable_snd).sub
      ((ContinuousMap.measurable_eval _).comp measurable_snd)

theorem measurable_tsRefl (τ : ℝ) : Measurable (tsRefl (d := d) τ) := by
  refine Measurable.prodMk ?_ ?_
  · exact (measurable_tsState (2 * τ)).subtype_mk
  · refine ContinuousMap.measurable_iff_eval.2 fun t => ?_
    exact ((ContinuousMap.measurable_eval _).comp measurable_snd).sub
      ((ContinuousMap.measurable_eval _).comp measurable_snd)

/-- Two forward paths glued at time zero into a two-sided path vanishing at zero. -/
def gluePath (p : Path d × Path d) : C(ℝ, Vec d) :=
  ⟨fun t => (p.1 t.toNNReal - p.1 0) + (p.2 (-t).toNNReal - p.2 0),
    ((p.1.continuous.comp continuous_real_toNNReal).sub continuous_const).add
      ((p.2.continuous.comp (continuous_real_toNNReal.comp continuous_neg)).sub continuous_const)⟩

theorem gluePath_zero (p : Path d × Path d) : gluePath p 0 = 0 := by
  simp [gluePath]

theorem gluePath_nnreal (p : Path d × Path d) (t : ℝ≥0) :
    gluePath p (t : ℝ) = p.1 t - p.1 0 := by
  have h : (-(t : ℝ)).toNNReal = 0 := Real.toNNReal_of_nonpos (by simp)
  simp [gluePath, Real.toNNReal_coe, h]

theorem gluePath_neg_nnreal (p : Path d × Path d) (t : ℝ≥0) :
    gluePath p (-(t : ℝ)) = p.2 t - p.2 0 := by
  have h : (-(t : ℝ)).toNNReal = 0 := Real.toNNReal_of_nonpos (by simp)
  simp [gluePath, Real.toNNReal_coe, h]

theorem measurable_gluePath : Measurable (gluePath (d := d)) := by
  refine ContinuousMap.measurable_iff_eval.2 fun t => ?_
  exact ((((continuous_eval_const _).measurable.comp measurable_fst).sub
    ((continuous_eval_const _).measurable.comp measurable_fst)).add
    (((continuous_eval_const _).measurable.comp measurable_snd).sub
    ((continuous_eval_const _).measurable.comp measurable_snd)))

section Law

variable {Λ₀ r₀ : ℝ}

/-- The environment law on the aperiodic environments. -/
def apLaw (Q : EnvironmentLaw d Λ₀ r₀) : Measure (aperiodicSet d) :=
  Q.measure.comap Subtype.val

theorem map_val_apLaw (Q : EnvironmentLaw d Λ₀ r₀)
    (hap : ∀ᵐ ω ∂Q.measure, ω ∈ aperiodicSet d) :
    (apLaw Q).map Subtype.val = Q.measure := by
  rw [apLaw, map_comap_subtype_coe (measurableSet_aperiodicSet d),
    Measure.restrict_eq_self_of_ae_mem hap]

theorem apLaw_isProbability (Q : EnvironmentLaw d Λ₀ r₀)
    (hap : ∀ᵐ ω ∂Q.measure, ω ∈ aperiodicSet d) : IsProbabilityMeasure (apLaw Q) := by
  constructor
  rw [apLaw, comap_subtype_coe_apply (measurableSet_aperiodicSet d), Set.image_univ,
    Subtype.range_coe]
  exact (prob_compl_eq_zero_iff (measurableSet_aperiodicSet d)).1 (mem_ae_iff.1 hap)

theorem integral_apLaw (Q : EnvironmentLaw d Λ₀ r₀)
    (hap : ∀ᵐ ω ∂Q.measure, ω ∈ aperiodicSet d) (g : FieldPair d → ℝ) :
    ∫ ω : aperiodicSet d, g ω ∂apLaw Q = ∫ ω, g ω ∂Q.measure := by
  rw [← map_val_apLaw Q hap,
    (MeasurableEmbedding.subtype_coe (measurableSet_aperiodicSet d)).integral_map]

theorem ae_apLaw (Q : EnvironmentLaw d Λ₀ r₀) (hap : ∀ᵐ ω ∂Q.measure, ω ∈ aperiodicSet d)
    {P : FieldPair d → Prop} (h : ∀ᵐ ω ∂Q.measure, P ω) : ∀ᵐ ω : aperiodicSet d ∂apLaw Q, P ω := by
  rw [← map_val_apLaw Q hap] at h
  exact ae_of_ae_map measurable_subtype_coe.aemeasurable h

/-- The environment kernel from the origin, on aperiodic environments. -/
def apOriginKernel (K : Kernel (FieldPair d × Vec d) (Path d)) :
    Kernel (aperiodicSet d) (Path d) :=
  K.comap (fun ω => ((ω : FieldPair d), (0 : Vec d)))
    (measurable_subtype_coe.prodMk measurable_const)

instance (K : Kernel (FieldPair d × Vec d) (Path d)) [IsMarkovKernel K] :
    IsMarkovKernel (apOriginKernel K) := by
  unfold apOriginKernel
  infer_instance

/-- The law of the two-sided process: two conditionally independent forward paths from the
same environment, glued at time zero. -/
def tsLaw (Q : EnvironmentLaw d Λ₀ r₀) (K : Kernel (FieldPair d × Vec d) (Path d)) :
    Measure (TwoSidedSpace d) :=
  ((apLaw Q) ⊗ₘ (apOriginKernel K ×ₖ apOriginKernel K)).map fun z => (z.1, gluePath z.2)

theorem measurable_tsGlue :
    Measurable fun z : aperiodicSet d × (Path d × Path d) => (z.1, gluePath z.2) :=
  measurable_fst.prodMk (measurable_gluePath.comp measurable_snd)

theorem tsLaw_isProbability (Q : EnvironmentLaw d Λ₀ r₀)
    (hap : ∀ᵐ ω ∂Q.measure, ω ∈ aperiodicSet d)
    (K : Kernel (FieldPair d × Vec d) (Path d)) [IsMarkovKernel K] :
    IsProbabilityMeasure (tsLaw Q K) := by
  have := apLaw_isProbability Q hap
  unfold tsLaw
  infer_instance

theorem tsState_zero_glue (ω₀ : aperiodicSet d) (p : Path d × Path d) :
    tsState 0 (ω₀, gluePath p) = ω₀ := by
  simp [tsState, gluePath_zero]

end Law

/-- Product of observables at the times after `t`, with the gaps of the list. -/
def tsFwdProd : List (ℝ≥0 × (FieldPair d → ℝ)) → ℝ → TwoSidedSpace d → ℝ
  | [], _, _ => 1
  | (s, f) :: L, t, ω => f (tsState (t + s) ω) * tsFwdProd L (t + s) ω

/-- Product of observables at the times before `t`, with the gaps of the list. -/
def tsBwdProd : List (ℝ≥0 × (FieldPair d → ℝ)) → ℝ → TwoSidedSpace d → ℝ
  | [], _, _ => 1
  | (s, f) :: L, t, ω => f (tsState (t - s) ω) * tsBwdProd L (t - s) ω

private theorem abs_mul_le_one' {u v : ℝ} (hu : |u| ≤ 1) (hv : |v| ≤ 1) : |u * v| ≤ 1 := by
  rw [abs_mul]
  exact (mul_le_mul hu hv (abs_nonneg _) zero_le_one).trans (by norm_num)

theorem tsFwdProd_measurable_bound :
    ∀ (L : List (ℝ≥0 × (FieldPair d → ℝ))), IsUnitObservables L → ∀ t : ℝ,
      Measurable (tsFwdProd L t) ∧ ∀ ω, |tsFwdProd L t ω| ≤ 1
  | [], _, _ => ⟨measurable_const, fun _ => by simp [tsFwdProd]⟩
  | (s, f) :: L, h, t => by
    obtain ⟨hm, hb⟩ := tsFwdProd_measurable_bound L
      (fun p hp => h p (List.mem_cons_of_mem _ hp)) (t + s)
    obtain ⟨hfm, hfb⟩ := h (s, f) (List.mem_cons_self ..)
    exact ⟨(hfm.comp (measurable_tsState _)).mul hm, fun ω => abs_mul_le_one' (hfb _) (hb ω)⟩

theorem tsBwdProd_measurable_bound :
    ∀ (L : List (ℝ≥0 × (FieldPair d → ℝ))), IsUnitObservables L → ∀ t : ℝ,
      Measurable (tsBwdProd L t) ∧ ∀ ω, |tsBwdProd L t ω| ≤ 1
  | [], _, _ => ⟨measurable_const, fun _ => by simp [tsBwdProd]⟩
  | (s, f) :: L, h, t => by
    obtain ⟨hm, hb⟩ := tsBwdProd_measurable_bound L
      (fun p hp => h p (List.mem_cons_of_mem _ hp)) (t - s)
    obtain ⟨hfm, hfb⟩ := h (s, f) (List.mem_cons_self ..)
    exact ⟨(hfm.comp (measurable_tsState _)).mul hm, fun ω => abs_mul_le_one' (hfb _) (hb ω)⟩

theorem tsFwdProd_glue :
    ∀ (L : List (ℝ≥0 × (FieldPair d → ℝ))) (t₀ : ℝ≥0) (ω₀ : aperiodicSet d)
      (p : Path d × Path d), p.1 0 = 0 →
      tsFwdProd L (t₀ : ℝ) (ω₀, gluePath p) = chainProd L t₀ p.1 ω₀
  | [], _, _, _, _ => rfl
  | (s, f) :: L, t₀, ω₀, p, h0 => by
    have hc : (t₀ : ℝ) + (s : ℝ) = ((t₀ + s : ℝ≥0) : ℝ) := by push_cast; rfl
    simp only [tsFwdProd, chainProd]
    rw [hc, tsFwdProd_glue L (t₀ + s) ω₀ p h0]
    simp only [tsState, gluePath_nnreal, h0, sub_zero]

theorem tsBwdProd_glue :
    ∀ (L : List (ℝ≥0 × (FieldPair d → ℝ))) (t₀ : ℝ≥0) (ω₀ : aperiodicSet d)
      (p : Path d × Path d), p.2 0 = 0 →
      tsBwdProd L (-(t₀ : ℝ)) (ω₀, gluePath p) = chainProd L t₀ p.2 ω₀
  | [], _, _, _, _ => rfl
  | (s, f) :: L, t₀, ω₀, p, h0 => by
    have hc : -(t₀ : ℝ) - (s : ℝ) = -((t₀ + s : ℝ≥0) : ℝ) := by push_cast; ring
    simp only [tsBwdProd, chainProd]
    rw [hc, tsBwdProd_glue L (t₀ + s) ω₀ p h0]
    simp only [tsState, gluePath_neg_nnreal, h0, sub_zero]

section Annealed

variable (hd : 2 ≤ d) (D : StructuralData d)
  (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
  (hap : ∀ᵐ ω ∂Q.measure, ω ∈ aperiodicSet d)
  {K : Kernel (FieldPair d × Vec d) (Path d)} [IsMarkovKernel K]
  (hK : ∀ ω : FieldPair d, IsRegular D.ellipticity ω → ∀ x : Vec d,
    SolvesMartingaleProblem (External.Draft.svGenerator (reducedCoefficient ω)
      (forcedDrift (reducedCoefficient ω) (⟨0, by omega⟩ : Fin d) 0)) x (K (ω, x)))

include hap hK in
/-- Split formula: observables at times before and after zero integrate to the product of the two
multi-time kernel means. -/
theorem integral_tsLaw_split {F₀ : FieldPair d → ℝ} (hF₀ : Measurable F₀)
    (hF₀b : ∀ ω, |F₀ ω| ≤ 1) {Lb Lf : List (ℝ≥0 × (FieldPair d → ℝ))}
    (hLb : IsUnitObservables Lb) (hLf : IsUnitObservables Lf) :
    ∫ ω, F₀ (tsState 0 ω) * tsBwdProd Lb 0 ω * tsFwdProd Lf 0 ω ∂tsLaw Q K =
      ∫ ω, F₀ ω * chainMean K Lb ω * chainMean K Lf ω ∂Q.measure := by
  have := apLaw_isProbability Q hap
  have hΛ : 0 < D.ellipticity := lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter
  obtain ⟨hbm, hbb⟩ := tsBwdProd_measurable_bound Lb hLb 0
  obtain ⟨hfm, hfb⟩ := tsFwdProd_measurable_bound Lf hLf 0
  let Φ : TwoSidedSpace d → ℝ := fun ω => F₀ (tsState 0 ω) * tsBwdProd Lb 0 ω * tsFwdProd Lf 0 ω
  have hΦm : Measurable Φ := ((hF₀.comp (measurable_tsState 0)).mul hbm).mul hfm
  have hΦb : ∀ ω, |Φ ω| ≤ 1 := fun ω => abs_mul_le_one' (abs_mul_le_one' (hF₀b _) (hbb ω)) (hfb ω)
  have hint : Integrable (fun z : aperiodicSet d × (Path d × Path d) => Φ (z.1, gluePath z.2))
      ((apLaw Q) ⊗ₘ (apOriginKernel K ×ₖ apOriginKernel K)) :=
    Integrable.of_bound (hΦm.comp measurable_tsGlue).aestronglyMeasurable 1
      (ae_of_all _ fun z => by simpa only [Real.norm_eq_abs] using hΦb _)
  change ∫ ω, Φ ω ∂tsLaw Q K = _
  rw [tsLaw, integral_map measurable_tsGlue.aemeasurable hΦm.aestronglyMeasurable,
    Measure.integral_compProd hint, ← integral_apLaw Q hap]
  apply integral_congr_ae
  filter_upwards [ae_apLaw Q hap Q.regular] with ω₀ hreg
  have hK0 := hK ω₀ hreg 0
  rw [Kernel.prod_apply]
  have h0 : ∀ᵐ γ ∂(apOriginKernel K ω₀), γ 0 = 0 := hK0.2.1
  have h1 : ∀ᵐ z ∂((apOriginKernel K ω₀).prod (apOriginKernel K ω₀)), z.1 0 = 0 := by
    have hmap : ((apOriginKernel K ω₀).prod (apOriginKernel K ω₀)).map Prod.fst =
        apOriginKernel K ω₀ := by rw [Measure.map_fst_prod, measure_univ, one_smul]
    rw [← hmap] at h0
    exact ae_of_ae_map measurable_fst.aemeasurable h0
  have h2 : ∀ᵐ z ∂((apOriginKernel K ω₀).prod (apOriginKernel K ω₀)), z.2 0 = 0 := by
    have h0' : ∀ᵐ γ ∂(apOriginKernel K ω₀), γ 0 = 0 := hK0.2.1
    have hmap : ((apOriginKernel K ω₀).prod (apOriginKernel K ω₀)).map Prod.snd =
        apOriginKernel K ω₀ := by rw [Measure.map_snd_prod, measure_univ, one_smul]
    rw [← hmap] at h0'
    exact ae_of_ae_map measurable_snd.aemeasurable h0'
  have hcongr : (fun p : Path d × Path d => Φ (ω₀, gluePath p)) =ᵐ[(apOriginKernel K ω₀).prod
      (apOriginKernel K ω₀)] fun p => F₀ ω₀ * (chainProd Lf 0 p.1 ω₀ * chainProd Lb 0 p.2 ω₀) := by
    filter_upwards [h1, h2] with p hp1 hp2
    simp only [Φ, tsState_zero_glue]
    have hb := tsBwdProd_glue Lb 0 ω₀ p hp2
    have hf := tsFwdProd_glue Lf 0 ω₀ p hp1
    simp only [NNReal.coe_zero, neg_zero] at hb hf
    rw [hb, hf]
    ring
  rw [integral_congr_ae hcongr, integral_const_mul]
  have hpm := integral_prod_mul (μ := apOriginKernel K ω₀) (ν := apOriginKernel K ω₀)
    (fun Y : Path d => chainProd Lf 0 Y (ω₀ : FieldPair d))
    (fun Y : Path d => chainProd Lb 0 Y (ω₀ : FieldPair d))
  rw [hpm]
  simp only [apOriginKernel, Kernel.comap_apply]
  rw [integral_chainProd hd hΛ hK Lf hLf _ hreg, integral_chainProd hd hΛ hK Lb hLb _ hreg]
  ring

end Annealed

end EinsteinFull.Blueprint
