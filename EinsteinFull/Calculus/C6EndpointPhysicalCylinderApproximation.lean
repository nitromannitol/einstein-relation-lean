import PDEFoundation.Geometry.EuclideanBall.Basic
import EinsteinFull.Calculus.C6EndpointCylinderApproximation
import EinsteinFull.Work.W6.SamplewiseTemporalFubiniProof
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinFull

private theorem physical_norm_average_sub_le
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

private theorem physical_integrable {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] (f : ℝ × Vec d → E) (hf : Continuous f)
    (t r : ℝ) (x : Vec d) :
    Integrable f (volume.restrict (Ioo (t-r^2) t ×ˢ {y | euclideanNorm (y-x) < r})) := by
  apply (hf.continuousOn.integrableOn_compact
    (isCompact_Icc.prod (isCompact_closedBall x r))).mono_set
  rintro ⟨s,y⟩ ⟨hs,hy⟩
  refine ⟨⟨hs.1.le, hs.2.le⟩, ?_⟩
  simpa only [Metric.mem_closedBall, dist_eq_norm] using
    (Calculus.S1.norm_le_euclideanNorm (y-x)).trans hy.le

private theorem physical_average_tendsto {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : ℝ × Vec d → E) (hf : Continuous f) (t : ℝ) (x : Vec d) :
    Tendsto (fun r : ℝ => ⨍ z in Ioo (t-r^2) t ×ˢ {y | euclideanNorm (y-x) < r}, f z)
      (𝓝[>] (0 : ℝ)) (𝓝 (f (t,x))) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hnear⟩ := Metric.continuousAt_iff.mp hf.continuousAt (ε/2) (by positivity)
  filter_upwards [Ioo_mem_nhdsGT (lt_min zero_lt_one hδ)] with r hr
  let A := Ioo (t-r^2) t
  let B := {y : Vec d | euclideanNorm (y-x) < r}
  have hBm : MeasurableSet B := S3LocalAv.measurableSet_euclideanBall x r
  have hBfin : volume B ≠ ∞ := S3LocalAv.measure_euclideanBall_ne_top x hr.1.le
  have hBpos : volume B ≠ 0 := by
    apply ne_of_gt
    apply (isOpen_lt (S3LocalAv.continuous_euclideanNorm'.comp
      (continuous_id.sub continuous_const)) continuous_const).measure_pos volume
    exact ⟨x, by simpa [B, euclideanNorm, euclideanSq, dot] using hr.1⟩
  have hAfin : volume A ≠ ∞ := by simp [A, Real.volume_Ioo]
  have hApos : volume A ≠ 0 := by
    rw [Real.volume_Ioo]
    exact (ENNReal.ofReal_pos.mpr (by nlinarith [sq_pos_of_pos hr.1])).ne'
  let m := volume.restrict (A ×ˢ B)
  have hmfin : m univ ≠ ∞ := by
    simp only [m, Measure.restrict_apply_univ, Measure.volume_eq_prod, Measure.prod_prod]
    exact ENNReal.mul_ne_top hAfin hBfin
  let : IsFiniteMeasure m := ⟨hmfin.lt_top⟩
  let : NeZero m := ⟨by
    intro he
    have : m univ = 0 := by rw [he]; rfl
    simpa only [m, Measure.restrict_apply_univ, Measure.volume_eq_prod, Measure.prod_prod,
      mul_eq_zero, hApos, hBpos, or_self] using this⟩
  have hbound : ‖(⨍ z, f z ∂m) - f (t,x)‖ ≤ ε/2 := by
    apply physical_norm_average_sub_le m _ _ _ (physical_integrable f hf t r x)
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod hBm)] with z hz
    rw [← dist_eq_norm]
    apply (hnear ?_).le
    rw [Prod.dist_eq, Real.dist_eq, dist_eq_norm, max_lt_iff]
    refine ⟨?_, (Calculus.S1.norm_le_euclideanNorm (z.2-x)).trans_lt
      (hz.2.trans (lt_min_iff.mp hr.2).2)⟩
    rw [abs_of_nonpos (sub_nonpos.mpr hz.1.2.le)]
    have hr1 : r < 1 := (lt_min_iff.mp hr.2).1
    have hsq : r^2 ≤ r := by nlinarith [hr.1]
    have hs := hz.1.1
    linarith [(lt_min_iff.mp hr.2).2]
  exact lt_of_le_of_lt (by simpa only [dist_eq_norm] using hbound) (by linarith)

@[nolint unusedArguments]
theorem endpoint_corrected_physical_cylinder_average_tendsto
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
    (ν : EndpointIndex d) (t : ℝ≥0) (ht : 0 < (t : ℝ))
    (c : ℝ → ℂ) (hc : Continuous c)
    (W : ℝ × FieldPair d → ℂ) (hW : Measurable W)
    (heW : ∀ s : ℝ,
      (fun ω => W (s, ω)) =ᵐ[reducedLaw Q]
        (fun ω => (indexedEndpoint hd Q ν ζ P T β a μ s.toNNReal) ω + c s))
    (x : Vec d) :
    Tendsto (fun r : ℝ =>
      eLpNorm (fun ω : FieldPair d =>
        (⨍ z in Ioo ((t : ℝ) - r ^ 2) (t : ℝ) ×ˢ PDE.euclideanBall x r,
          W (z.1, translate z.2 ω)) -
        (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x
          (indexedEndpoint hd Q ν ζ P T β a μ t)) ω - c (t : ℝ))
        (ENNReal.ofReal p) (reducedLaw Q)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  let := reducedLaw_probability Q
  let : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr (by linarith)⟩
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
  let : PolishSpace (CoefficientField d) := Localization.coefficientField_polish d
  let : PolishSpace (FieldPair d) := inferInstance
  let G : ℝ × Vec d → Lp ℂ (ENNReal.ofReal p) (reducedLaw Q) := fun u =>
    Lp.compMeasurePreserving (translate u.2)
      (measurePreserving_translate (reducedLaw Q) (reducedLaw_stationary Q) u.2)
      (F u.1.toNNReal)
  let g : ℝ × Vec d → C(FieldPair d, FieldPair d) := fun u =>
    ⟨translate u.2, Probability.continuous_translate.comp (continuous_const.prodMk continuous_id)⟩
  have hg : Continuous g := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact Probability.continuous_translate.comp (continuous_fst.snd.prodMk continuous_snd)
  have hG₀ : Continuous G :=
    (hF.comp (continuous_real_toNNReal.comp continuous_fst)).compMeasurePreservingLp hg
      (fun u => measurePreserving_translate (reducedLaw Q) (reducedLaw_stationary Q) u.2)
      ENNReal.ofReal_ne_top
  let J : ℝ × Vec d → Lp ℂ (ENNReal.ofReal p) (reducedLaw Q) :=
    fun u => G u + Lp.const (ENNReal.ofReal p) (reducedLaw Q) (c u.1)
  have hJ : Continuous J := hG₀.add
    ((Lp.constL (ENNReal.ofReal p) (reducedLaw Q) ℂ).continuous.comp (hc.comp continuous_fst))
  let L := (complexLpToL2CLM (reducedLaw Q) hp2).restrictScalars ℝ
  have hrep (u : ℝ × Vec d) :
      (fun ω => W (u.1, translate u.2 ω)) =ᵐ[reducedLaw Q] L (J u) := by
    have hm := measurePreserving_translate (reducedLaw Q) (reducedLaw_stationary Q) u.2
    filter_upwards [hm.quasiMeasurePreserving.ae (heW u.1),
      Lp.coeFn_compMeasurePreserving (F u.1.toNNReal) hm,
      hm.quasiMeasurePreserving.ae (he u.1.toNNReal),
      Lp.coeFn_add (G u) (Lp.const (ENNReal.ofReal p) (reducedLaw Q) (c u.1)),
      Lp.coeFn_const (ENNReal.ofReal p) (reducedLaw Q) (c u.1)] with ω hw hg he hj hc
    change W (u.1, translate u.2 ω) = (J u) ω
    rw [hj]
    change W (u.1, translate u.2 ω) = (G u) ω + (Lp.const (ENNReal.ofReal p) (reducedLaw Q) (c u.1)) ω
    rw [hc, hg]
    change W (u.1, translate u.2 ω) = (F u.1.toNNReal) (translate u.2 ω) + c u.1
    rw [he, hw]
  let H : ℝ → Lp ℂ (ENNReal.ofReal p) (reducedLaw Q) := fun r =>
    ⨍ z in Ioo ((t:ℝ)-r^2) (t:ℝ) ×ˢ {y | euclideanNorm (y-x) < r}, J z
  have hphys (r : ℝ) :
      (fun ω => L (H r) ω) =ᵐ[reducedLaw Q] fun ω =>
        ⨍ z in Ioo ((t:ℝ)-r^2) (t:ℝ) ×ˢ {y | euclideanNorm (y-x) < r},
          W (z.1, translate z.2 ω) := by
    let m := volume.restrict
      (Ioo ((t:ℝ)-r^2) (t:ℝ) ×ˢ {y | euclideanNorm (y-x) < r})
    have hi : Integrable J m := physical_integrable J hJ (t:ℝ) r x
    have hm : Measurable (fun z : (ℝ × Vec d) × FieldPair d =>
        W (z.1.1, translate z.1.2 z.2)) :=
      hW.comp (measurable_fst.fst.prodMk
        (Probability.continuous_translate.measurable.comp (measurable_fst.snd.prodMk measurable_snd)))
    have hh := coeFn_integral_joint_l2_representative (L.integrable_comp hi) hm hrep
    have hmap : L (H r) = (m.real univ)⁻¹ • ∫ z, L (J z) ∂m := by
      change L (⨍ z, J z ∂m) = _
      rw [average_eq, L.map_smul, L.integral_comp_comm hi]
    filter_upwards [hh, Lp.coeFn_smul ((m.real univ)⁻¹) (∫ z, L (J z) ∂m)] with ω hh hs
    change L (H r) ω = _
    rw [hmap, hs]
    change (m.real univ)⁻¹ • (∫ z, L (J z) ∂m) ω = _
    rw [hh, average_eq]
  have hzero : (fun ω => L (J ((t:ℝ),x)) ω) =ᵐ[reducedLaw Q]
      fun ω => (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x
        (indexedEndpoint hd Q ν ζ P T β a μ t)) ω + c (t:ℝ) := by
    have hm := measurePreserving_translate (reducedLaw Q) (reducedLaw_stationary Q) x
    filter_upwards [hrep ((t:ℝ),x), hm.quasiMeasurePreserving.ae (heW (t:ℝ)),
      coeFn_complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x
        (indexedEndpoint hd Q ν ζ P T β a μ t)] with ω hr hw hc
    exact hr.symm.trans (by simpa only [Real.toNNReal_coe, hc] using hw)
  have hlim := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' H (J ((t:ℝ),x))).mp
    (physical_average_tendsto J hJ (t:ℝ) x)
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hball : PDE.euclideanBall x r = {y | euclideanNorm (y-x) < r} := by
    ext y
    exact PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hr
  rw [hball]
  apply eLpNorm_congr_ae
  filter_upwards [hphys r, hzero] with ω hm hz
  change (H r) ω - (J ((t:ℝ),x)) ω = _
  change L (H r) ω - L (J ((t:ℝ),x)) ω = _
  rw [hm, hz]
  ring
end EinsteinFull.Blueprint
