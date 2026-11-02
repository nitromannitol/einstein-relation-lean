import EinsteinFull.Calculus.C6EndpointSpatialLpContinuity
import Mathlib.MeasureTheory.Integral.Average
import EinsteinFull.Calculus.S1SharpBoundSupport
import EinsteinFull.Calculus.S3LocalAvSupport
import Mathlib.MeasureTheory.Integral.Prod
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinFull

private theorem cylinder_norm_average_sub_le
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E]
    (μ : Measure α) [IsFiniteMeasure μ] [NeZero μ]
    (f : α → E) (z : E) (C : ℝ) (hi : Integrable f μ)
    (hb : ∀ᵐ x ∂μ, ‖f x - z‖ ≤ C) :
    ‖(⨍ x, f x ∂μ) - z‖ ≤ C := by
  have he : (⨍ x, f x ∂μ) - z = ⨍ x, f x - z ∂μ := by
    rw [average_fun_sub hi (integrable_const z), average_const]
  rw [he, average]
  simpa only [measureReal_def, measure_univ, ENNReal.toReal_one, mul_one] using
    norm_integral_le_of_norm_le_const
      (hb.filter_mono (Measure.ae_smul_measure_le (μ univ)⁻¹))

private theorem cylinder_integrable {d : ℕ} {E : Type*}
    [NormedAddCommGroup E]
    (f : ℝ × Vec d → E) (hf : Continuous f) (t r : ℝ) :
    Integrable f ((volume.restrict (Icc (t - r ^ 2) t)).prod
      (volume.restrict {x : Vec d | euclideanNorm x < r})) := by
  rw [Measure.prod_restrict]
  apply (hf.continuousOn.integrableOn_compact
    (isCompact_Icc.prod (isCompact_closedBall (0 : Vec d) r))).mono_set
  rintro ⟨s, x⟩ ⟨hs, hx⟩
  refine ⟨hs, ?_⟩
  simpa only [Metric.mem_closedBall, dist_zero_right] using
    (Calculus.S1.norm_le_euclideanNorm x).trans hx.le

private theorem cylinder_inner_integrable {d : ℕ} {E : Type*}
    [NormedAddCommGroup E]
    (f : ℝ × Vec d → E) (hf : Continuous f) (s r : ℝ) :
    Integrable (fun x => f (s, x))
      (volume.restrict {x : Vec d | euclideanNorm x < r}) := by
  apply ((hf.comp (continuous_const.prodMk continuous_id)).continuousOn.integrableOn_compact
    (isCompact_closedBall (0 : Vec d) r)).mono_set
  intro x hx
  simpa only [Metric.mem_closedBall, dist_zero_right] using
    (Calculus.S1.norm_le_euclideanNorm x).trans hx.le

private theorem cylinder_average_tendsto {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : ℝ × Vec d → E) (hf : Continuous f) (t : ℝ) :
    Tendsto (fun r : ℝ => ⨍ s in Icc (t - r ^ 2) t,
      ⨍ x in {x : Vec d | euclideanNorm x < r}, f (s, x))
      (𝓝[>] (0 : ℝ)) (𝓝 (f (t, 0))) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hc0 : ContinuousAt f (t, 0) := hf.continuousAt
  obtain ⟨δ, hδ, hnear⟩ := Metric.continuousAt_iff.mp hc0 (ε / 2) (by positivity)
  filter_upwards [Ioo_mem_nhdsGT (lt_min zero_lt_one hδ)] with r hr
  let A := Icc (t - r ^ 2) t
  let B := {x : Vec d | euclideanNorm x < r}
  have hBm : MeasurableSet B := by
    simpa only [sub_zero] using S3LocalAv.measurableSet_euclideanBall (0 : Vec d) r
  have hBfin : volume B ≠ ∞ := by
    simpa only [sub_zero] using S3LocalAv.measure_euclideanBall_ne_top (0 : Vec d) hr.1.le
  have hBpos : volume B ≠ 0 := by
    apply ne_of_gt
    have hBo : IsOpen B := isOpen_lt S3LocalAv.continuous_euclideanNorm' continuous_const
    apply hBo.measure_pos volume
    exact ⟨0, by simpa [B, euclideanNorm, euclideanSq, dot] using hr.1⟩
  letI : Fact (volume B < ∞) := ⟨hBfin.lt_top⟩
  letI : NeZero (volume.restrict B) := ⟨by simpa using hBpos⟩
  have hApos : volume A ≠ 0 := by
    rw [Real.volume_Icc]
    exact (ENNReal.ofReal_pos.mpr (by nlinarith [sq_pos_of_pos hr.1])).ne'
  letI : NeZero (volume.restrict A) := ⟨by simpa using hApos⟩
  have hprod := cylinder_integrable f hf t r
  have ho : Integrable (fun s => ⨍ x in B, f (s, x)) (volume.restrict A) := by
    rw [show (fun s => ⨍ x in B, f (s, x)) =
      ((volume.restrict B).real univ)⁻¹ • (fun s => ∫ x in B, f (s, x)) by
        funext s; exact average_eq _ _]
    exact hprod.integral_prod_left.smul ((volume.restrict B).real univ)⁻¹
  have hb (s : ℝ) (hs : s ∈ A) (x : Vec d) (hx : x ∈ B) :
      ‖f (s, x) - f (t, 0)‖ ≤ ε / 2 := by
    rw [← dist_eq_norm]
    apply (hnear ?_).le
    rw [Prod.dist_eq, dist_zero_right, Real.dist_eq, max_lt_iff]
    refine ⟨?_, (Calculus.S1.norm_le_euclideanNorm x).trans_lt (hx.trans (lt_min_iff.mp hr.2).2)⟩
    have hr1 : r < 1 := (lt_min_iff.mp hr.2).1
    have hsq : r ^ 2 ≤ r := by nlinarith [hr.1]
    rw [abs_of_nonpos (sub_nonpos.mpr hs.2)]
    dsimp [A] at hs
    linarith [hs.1, (lt_min_iff.mp hr.2).2]
  have hbound : ‖(⨍ s in A, ⨍ x in B, f (s, x)) - f (t, 0)‖ ≤ ε / 2 := by
    apply cylinder_norm_average_sub_le (volume.restrict A) _ _ _ ho
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    apply cylinder_norm_average_sub_le (volume.restrict B) _ _ _
      (cylinder_inner_integrable f hf s r)
    filter_upwards [ae_restrict_mem hBm] with x hx
    exact hb s hs x hx
  exact lt_of_le_of_lt (by simpa only [dist_eq_norm] using hbound) (by linarith)

private theorem cylinder_map_average
    {α E F : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (L : E →L[ℝ] F) (μ : Measure α) (f : α → E) (hi : Integrable f μ) :
    L (⨍ x, f x ∂μ) = ⨍ x, L (f x) ∂μ := by
  rw [average_eq, average_eq, L.map_smul, ← L.integral_comp_comm hi]

/-- Backward space-time cylinder means converge to the actual endpoint in every finite
Lp exponent at least two. -/
@[nolint unusedArguments] -- The exact contract retains h1 and ht.
theorem endpoint_backward_cylinder_average_tendsto
    (h1 : node_e_u3A_lp_u2D_growthStmt)
    {d : ℕ} (hd : 2 ≤ d) {D : StructuralData d} (p : ℝ) (hp : 2 ≤ p)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q))
    (μ : Lp ℂ 2 (reducedLaw Q))
    (hβ : IsReducedDriftObservation Q hQ β)
    (ha : IsReducedCoefficientObservation Q a)
    (hμ : IsReducedClockObservation Q μ) (ζ : ℂ)
    (P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P)
    (hT : IsComplexTransposeSemigroup Q P T)
    (ν : EndpointIndex d) (t : ℝ≥0) (ht : 0 < (t : ℝ)) :
    Tendsto (fun r : ℝ =>
      eLpNorm (fun ω : FieldPair d =>
        ((⨍ s in Icc ((t : ℝ) - r ^ 2) (t : ℝ),
          ⨍ x in {x : Vec d | euclideanNorm x < r},
            complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x
              (indexedEndpoint hd Q ν ζ P T β a μ s.toNNReal)) :
            Lp ℂ 2 (reducedLaw Q)) ω -
          (indexedEndpoint hd Q ν ζ P T β a μ t) ω)
        (ENNReal.ofReal p) (reducedLaw Q)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  letI := reducedLaw_probability Q
  letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr (by linarith)⟩
  have hp2 : 2 ≤ ENNReal.ofReal p := by
    exact_mod_cast ENNReal.ofReal_le_ofReal hp
  let lift (f : Lp ℂ 2 (reducedLaw Q))
      (hf : MemLp f (ENNReal.ofReal p) (reducedLaw Q)) := hf.toLp f
  have hlift (f : Lp ℂ 2 (reducedLaw Q))
      (hf : MemLp f (ENNReal.ofReal p) (reducedLaw Q)) :
      complexLpToL2 (reducedLaw Q) hp2 (lift f hf) = f := by
    apply Lp.ext
    exact hf.coeFn_toLp
  have hforward (f : Lp ℂ 2 (reducedLaw Q))
      (hf : MemLp f (ENNReal.ofReal p) (reducedLaw Q)) :
      ∃ F : ℝ≥0 → Lp ℂ (ENNReal.ofReal p) (reducedLaw Q),
        Continuous F ∧ ∀ t, (F t : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
          centeredComplexLp Q (P t f) := by
    let F := fun t => hP.lpRestriction hp t (lift f hf)
    have hF : Continuous F := (hP.lpRestriction_c0 hp).2.2 _
    have he (t) : (F t : FieldPair d → ℂ) =ᵐ[reducedLaw Q] P t f := by
      have hh := hP.lpRestriction_apply hp t (lift f hf)
      rw [hlift] at hh
      exact Filter.EventuallyEq.of_eq (congrArg (fun g : Lp ℂ 2 (reducedLaw Q) => (g : FieldPair d → ℂ)) hh)
    exact ⟨fun t => EndpointFiniteP.center (F t),
      EndpointFiniteP.center.continuous.comp hF,
      fun t => EndpointFiniteP.center_ae_l2 Q (F t) (P t f) (he t)⟩
  obtain ⟨K, _hK, hobs⟩ := EndpointFiniteP.observation_bounds d D
  obtain ⟨hb, ha', hm⟩ := hobs Q hQ β a μ hβ ha hμ
  have hβp (j) : MemLp (β j) (ENNReal.ofReal p) (reducedLaw Q) :=
    MemLp.of_bound (Lp.memLp (β j)).aestronglyMeasurable K (hb j)
  have hap (j k) : MemLp (a j k) (ENNReal.ofReal p) (reducedLaw Q) :=
    MemLp.of_bound (Lp.memLp (a j k)).aestronglyMeasurable K (ha' j k)
  have hμp : MemLp μ (ENNReal.ofReal p) (reducedLaw Q) :=
    MemLp.of_bound (Lp.memLp μ).aestronglyMeasurable K hm
  have hw : ∃ F : ℝ≥0 → Lp ℂ (ENNReal.ofReal p) (reducedLaw Q),
      Continuous F ∧ ∀ t, (F t : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
        indexedEndpoint hd Q ν ζ P T β a μ t := by
    cases ν with
    | inl j =>
      have hf : MemLp (β j + ζ • a ⟨0, by omega⟩ j)
          (ENNReal.ofReal p) (reducedLaw Q) :=
        (memLp_congr_ae (Lp.coeFn_add _ _)).2 ((hβp j).add
          ((memLp_congr_ae (Lp.coeFn_smul _ _)).2 ((hap _ j).const_smul ζ)))
      exact hforward _ hf
    | inr b =>
      cases b with
      | false =>
        obtain ⟨F, hF, he⟩ := hforward μ hμp
        refine ⟨fun t => ζ • F t, hF.const_smul ζ, fun t => ?_⟩
        exact (Lp.coeFn_smul ζ (F t)).trans
          (((he t).const_smul ζ).trans (Lp.coeFn_smul ζ _).symm)
      | true =>
        refine ⟨fun t => hT.lpRestriction hp hP t (lift (β ⟨0, by omega⟩) (hβp _)),
          (hT.lpRestriction_c0 hp hP).2.2 _, fun t => ?_⟩
        have hh := hT.lpRestriction_apply hp hP t (lift (β ⟨0, by omega⟩) (hβp _))
        rw [hlift] at hh
        exact Filter.EventuallyEq.of_eq (congrArg (fun g : Lp ℂ 2 (reducedLaw Q) => (g : FieldPair d → ℂ)) hh)
  obtain ⟨F, hF, he⟩ := hw
  letI : PolishSpace (CoefficientField d) := Localization.coefficientField_polish d
  letI : PolishSpace (FieldPair d) := inferInstance
  let G : ℝ × Vec d → Lp ℂ (ENNReal.ofReal p) (reducedLaw Q) := fun u =>
    Lp.compMeasurePreserving (translate u.2)
      (measurePreserving_translate (reducedLaw Q) (reducedLaw_stationary Q) u.2)
      (F u.1.toNNReal)
  let g : ℝ × Vec d → C(FieldPair d, FieldPair d) := fun u =>
    ⟨translate u.2, Probability.continuous_translate.comp (continuous_const.prodMk continuous_id)⟩
  have hg : Continuous g := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact Probability.continuous_translate.comp (continuous_fst.snd.prodMk continuous_snd)
  have hG : Continuous G :=
    (hF.comp (continuous_real_toNNReal.comp continuous_fst)).compMeasurePreservingLp hg
      (fun u => measurePreserving_translate (reducedLaw Q) (reducedLaw_stationary Q) u.2)
      ENNReal.ofReal_ne_top
  let L := (complexLpToL2CLM (reducedLaw Q) hp2).restrictScalars ℝ
  have hmap (s : ℝ) (x : Vec d) : L (G (s, x)) =
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x
        (indexedEndpoint hd Q ν ζ P T β a μ s.toNNReal) := by
    apply Lp.ext
    have hm := measurePreserving_translate (reducedLaw Q) (reducedLaw_stationary Q) x
    exact ((Lp.coeFn_compMeasurePreserving (F s.toNNReal) hm).trans
      (hm.quasiMeasurePreserving.ae (he s.toNNReal))).trans
        (coeFn_complexTranslation _ _ _ _).symm
  let H : ℝ → Lp ℂ (ENNReal.ofReal p) (reducedLaw Q) := fun r =>
    ⨍ s in Icc ((t : ℝ) - r ^ 2) (t : ℝ),
      ⨍ x in {x : Vec d | euclideanNorm x < r}, G (s, x)
  have hmean (r : ℝ) (hr : 0 < r) : L (H r) =
      ⨍ s in Icc ((t : ℝ) - r ^ 2) (t : ℝ),
        ⨍ x in {x : Vec d | euclideanNorm x < r},
          complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x
            (indexedEndpoint hd Q ν ζ P T β a μ s.toNNReal) := by
    let A := Icc ((t : ℝ) - r ^ 2) (t : ℝ)
    let B := {x : Vec d | euclideanNorm x < r}
    have hprod := cylinder_integrable G hG (t : ℝ) r
    have ho : Integrable (fun s => ⨍ x in B, G (s, x)) (volume.restrict A) := by
      rw [show (fun s => ⨍ x in B, G (s, x)) =
        ((volume.restrict B).real univ)⁻¹ • (fun s => ∫ x in B, G (s, x)) by
          funext s; exact average_eq (volume.restrict B) (fun x => G (s, x))]
      exact hprod.integral_prod_left.smul ((volume.restrict B).real univ)⁻¹
    change L (⨍ s in A, ⨍ x in B, G (s, x)) = _
    rw [cylinder_map_average L _ _ ho]
    apply average_congr
    apply Filter.Eventually.of_forall
    intro s
    change L (⨍ x in {x : Vec d | euclideanNorm x < r}, G (s, x)) = _
    rw [cylinder_map_average L _ _ (cylinder_inner_integrable G hG s r)]
    apply average_congr
    apply Filter.Eventually.of_forall
    intro x
    exact hmap s x
  have hz : L (G ((t : ℝ), 0)) = indexedEndpoint hd Q ν ζ P T β a μ t := by
    simpa only [Real.toNNReal_coe, complexTranslation_zero] using hmap (t : ℝ) 0
  have hc := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' H (G ((t : ℝ), 0))).mp
    (cylinder_average_tendsto G hG (t : ℝ))
  apply hc.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  apply eLpNorm_congr_ae
  have hm := Filter.EventuallyEq.of_eq (l := ae (reducedLaw Q))
    (congrArg (fun f : Lp ℂ 2 (reducedLaw Q) => (f : FieldPair d → ℂ)) (hmean r hr))
  have h0 := Filter.EventuallyEq.of_eq (l := ae (reducedLaw Q))
    (congrArg (fun f : Lp ℂ 2 (reducedLaw Q) => (f : FieldPair d → ℂ)) hz)
  exact hm.sub h0
end EinsteinFull.Blueprint
