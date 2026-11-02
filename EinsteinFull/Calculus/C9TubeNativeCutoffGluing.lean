import EinsteinFull.Blueprint.Foundation.Proofs.SbxS3UniformCrossHeat

open EinsteinRelation MeasureTheory PDE Filter EinsteinFull.External.Source.GMP
open EinsteinFull.Blueprint.TubeProbability
open EinsteinFull.Blueprint.SbxS3UniformCrossHeat
open scoped Topology NNReal ENNReal

namespace EinsteinFull.Calculus

/-- The native spectral heat flow converges strongly to its actual datum at zero. -/
theorem c9_native_heat_initial_L2 {d : ℕ} {R : ℝ}
    {ρ : PDE.Vec d → ℝ} {α : PDE.Vec d → EinsteinRelation.Mat d}
    (s : DirichletSpectralResolution ρ α R)
    (f : Lp ℝ 2 (dirichletVolume ρ R)) :
    Tendsto (fun t : ℝ≥0 => SpectralHeat.heatOperator (spectralHeatBasis s)
      s.eigenvalue (fun n => (s.eigenvalue_pos n).le) t f) (𝓝 0) (𝓝 f) := by
  have hcont := (SpectralHeat.heatOperator_continuous (spectralHeatBasis s) s.eigenvalue
    (fun n => (s.eigenvalue_pos n).le) f).continuousAt (x := (0 : ℝ≥0))
  unfold ContinuousAt at hcont
  simpa only [SpectralHeat.heatOperator_zero, ContinuousLinearMap.id_apply] using hcont

/-- The actual bounded spatial cutoff is a datum for the native weighted heat flow. -/
theorem c9_cutoff_memLp_dirichletVolume {d : ℕ} {κ R : ℝ}
    (hR : 0 < R) {ρ : PDE.Vec d → ℝ} {α : PDE.Vec d → EinsteinRelation.Mat d}
    (h : IsUniformlyElliptic κ ρ α) (φ : PDE.Vec d → ℝ)
    (hφ : IsSpatialTest (sourceBall 0 R) φ)
    (hφbounds : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1) :
    MemLp φ 2 (dirichletVolume ρ R) := by
  letI : IsFiniteMeasure (dirichletVolume ρ R) :=
    dirichletVolume_isFinite ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
  apply MemLp.of_bound hφ.1.continuous.aestronglyMeasurable 1
  filter_upwards with x
  simpa only [Real.norm_eq_abs, abs_of_nonneg (hφbounds x).1] using (hφbounds x).2

/-- At every positive time, the native flow of the cutoff is represented by the
literal kernel integral, with equality in the weighted spatial measure. -/
theorem c9_cutoff_heat_kernel_action {d : ℕ} (hd : 2 ≤ d)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    {ρ : PDE.Vec d → ℝ} {α : PDE.Vec d → EinsteinRelation.Mat d}
    (h : IsUniformlyElliptic κ ρ α) (s : DirichletSpectralResolution ρ α R)
    (φ : PDE.Vec d → ℝ) (hφ : IsSpatialTest (sourceBall 0 R) φ)
    (hφbounds : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    (t : ℝ≥0) (ht : 0 < (t : ℝ)) :
    let hmem := c9_cutoff_memLp_dirichletVolume hR h φ hφ hφbounds
    (fun x => SpectralHeat.heatOperator (spectralHeatBasis s) s.eigenvalue
      (fun n => (s.eigenvalue_pos n).le) t (hmem.toLp φ) x)
      =ᵐ[dirichletVolume ρ R] fun x => ∫ y,
        (∑' n, Real.exp (-s.eigenvalue n * (t : ℝ)) * s.eigenfunction n x *
          s.eigenfunction n y) * φ y ∂dirichletVolume ρ R := by
  dsimp only
  let hmem := c9_cutoff_memLp_dirichletVolume hR h φ hφ hφbounds
  filter_upwards [spectral_heat_operator_ae_kernel_action hd hκ h hR s t ht
    (hmem.toLp φ)] with x hx
  rw [hx]
  apply integral_congr_ae
  filter_upwards [hmem.coeFn_toLp] with y hy
  rw [hy]

/-- The same cutoff datum has a native Dirichlet energy representative, with
its actual spatial derivatives. -/
theorem c9_cutoff_native_dirichlet_datum {d : ℕ} {κ R : ℝ}
    (hR : 0 < R) {ρ : PDE.Vec d → ℝ} {α : PDE.Vec d → EinsteinRelation.Mat d}
    (h : IsUniformlyElliptic κ ρ α) (φ : PDE.Vec d → ℝ)
    (hφ : IsSpatialTest (sourceBall 0 R) φ)
    (hφbounds : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1) :
    let hmem := c9_cutoff_memLp_dirichletVolume hR h φ hφ hφbounds
    ∃ v : DirichletHilbertSpace (d := d) R hR,
      dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) v =
        hmem.toLp φ ∧
      ∀ i : Fin d, (fun x => v.val (some i) x) =ᵐ[volume.restrict (sourceBall 0 R)]
        (fun x => fderiv ℝ φ x (unitVector i)) := by
  dsimp only
  let v : Homogenization.H10Function (sourceBall (0 : PDE.Vec d) R) :=
    Homogenization.H10Function.ofContDiff (dirichletBall R).isOpen hφ.1 hφ.2.1 hφ.2.2
  obtain ⟨w, hw, hwg⟩ := exists_dirichletHilbert_of_nativeH10_weighted
    ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) v
  refine ⟨w, ?_, ?_⟩
  · apply Lp.ext
    filter_upwards [hw, (c9_cutoff_memLp_dirichletVolume hR h φ hφ hφbounds).coeFn_toLp] with x hx hy
    simpa only [v, Homogenization.H10Function.ofContDiff,
      Homogenization.H1Function.ofContDiff] using hx.trans hy.symm
  · intro i
    simpa only [v, Homogenization.H10Function.ofContDiff,
      Homogenization.H1Function.ofContDiff, Homogenization.basisVec, unitVector] using hwg i

/-- The native heat flow dissipates its weighted squared norm at the actual
Dirichlet energy, for every positive time. -/
theorem c9_native_heat_energy_dissipation {d : ℕ} (hd : 2 ≤ d)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    {ρ : PDE.Vec d → ℝ} {α : PDE.Vec d → EinsteinRelation.Mat d}
    (h : IsUniformlyElliptic κ ρ α) (s : DirichletSpectralResolution ρ α R)
    (u : ℕ → DirichletHilbertSpace (d := d) R hR)
    (hb : ∀ n, spectralHeatBasis s n = dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (h.2.2 x).2.1) (u n))
    (hv : ∀ n w, (∫ x in sourceBall (0 : PDE.Vec d) R,
      dot ((α x).mulVec (fun i => (u n).val (some i) x))
        (fun i => w.val (some i) x)) = s.eigenvalue n * inner ℝ
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) (u n))
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) w)) :
    let J := dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
    ∃ Q : (t : ℝ≥0) → 0 < t →
      Lp ℝ 2 (dirichletVolume ρ R) →L[ℝ] DirichletHilbertSpace (d := d) R hR,
      (∀ f, Continuous (fun t : {t : ℝ≥0 // 0 < t} => Q t.val t.property f)) ∧
      ∀ t ht,
        J.comp (Q t ht) = SpectralHeat.heatOperator (spectralHeatBasis s) s.eigenvalue
          (fun n => (s.eigenvalue_pos n).le) t ∧
        ∀ f, HasDerivAt
          (fun r : ℝ => ‖SpectralHeat.heatOperator (spectralHeatBasis s) s.eigenvalue
            (fun n => (s.eigenvalue_pos n).le) r.toNNReal f‖ ^ 2)
          (-2 * (∫ x in sourceBall (0 : PDE.Vec d) R,
            dot ((α x).mulVec (fun i => (Q t ht f).val (some i) x))
              (fun i => (Q t ht f).val (some i) x))) (t : ℝ) := by
  dsimp only
  let J := dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
  obtain ⟨Q, hcont, hQ⟩ := spectral_heat_native_lift hd hκ h R hR s u hb hv
  refine ⟨Q, hcont, ?_⟩
  intro t ht
  obtain ⟨hfactor, hform, _⟩ := hQ t ht
  refine ⟨hfactor, ?_⟩
  intro f
  have hnorm := (SpectralHeat.heatOperator_hasDerivAt (spectralHeatBasis s)
    s.eigenvalue s.eigenvalue_pos t ht f).norm_sq
  have hJ := congrArg (fun T : _ →L[ℝ] _ => T f) hfactor
  change J (Q t ht f) = _ at hJ
  have hi : inner ℝ
      (SpectralHeat.heatOperator (spectralHeatBasis s) s.eigenvalue
        (fun n => (s.eigenvalue_pos n).le) t f)
      (SpectralHeat.firstMoment (spectralHeatBasis s) s.eigenvalue s.eigenvalue_pos t ht f) =
      (∫ x in sourceBall (0 : PDE.Vec d) R,
        dot ((α x).mulVec (fun i => (Q t ht f).val (some i) x))
          (fun i => (Q t ht f).val (some i) x)) := by
    rw [real_inner_comm, ← hJ]
    exact (hform f (Q t ht f)).symm
  simpa only [Real.toNNReal_coe, inner_neg_right, hi, mul_neg, neg_mul] using hnorm

/-- The native heat flow has finite total Dirichlet energy all the way down
 to its initial time. -/
theorem c9_native_heat_finite_energy {d : ℕ} (hd : 2 ≤ d)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    {ρ : PDE.Vec d → ℝ} {α : PDE.Vec d → EinsteinRelation.Mat d}
    (h : IsUniformlyElliptic κ ρ α) (s : DirichletSpectralResolution ρ α R)
    (u : ℕ → DirichletHilbertSpace (d := d) R hR)
    (hb : ∀ n, spectralHeatBasis s n = dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (h.2.2 x).2.1) (u n))
    (hv : ∀ n w, (∫ x in sourceBall (0 : PDE.Vec d) R,
      dot ((α x).mulVec (fun i => (u n).val (some i) x))
        (fun i => w.val (some i) x)) = s.eigenvalue n * inner ℝ
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) (u n))
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) w)) :
    let J := dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
    ∃ Q : (t : ℝ≥0) → 0 < t →
      Lp ℝ 2 (dirichletVolume ρ R) →L[ℝ] DirichletHilbertSpace (d := d) R hR,
      (∀ f, Continuous (fun t : {t : ℝ≥0 // 0 < t} => Q t.val t.property f)) ∧
      (∀ t ht, J.comp (Q t ht) =
        SpectralHeat.heatOperator (spectralHeatBasis s) s.eigenvalue
          (fun n => (s.eigenvalue_pos n).le) t) ∧
      ∀ (f : Lp ℝ 2 (dirichletVolume ρ R)) (T : ℝ),
        IntegrableOn (fun t : ℝ => if ht : 0 < t then
          ∫ x in sourceBall (0 : PDE.Vec d) R,
            dot ((α x).mulVec (fun i => (Q t.toNNReal (Real.toNNReal_pos.mpr ht) f).val (some i) x))
              (fun i => (Q t.toNNReal (Real.toNNReal_pos.mpr ht) f).val (some i) x)
          else 0) (Set.Ioo 0 T) := by
  dsimp only
  let J := dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
  obtain ⟨Q, hcont, hQ⟩ := c9_native_heat_energy_dissipation hd hκ hR h s u hb hv
  refine ⟨Q, hcont, fun t ht => (hQ t ht).1, ?_⟩
  intro f T
  let E : ℝ → ℝ := fun t => if ht : 0 < t then
    ∫ x in sourceBall (0 : PDE.Vec d) R,
      dot ((α x).mulVec (fun i => (Q t.toNNReal (Real.toNNReal_pos.mpr ht) f).val (some i) x))
        (fun i => (Q t.toNNReal (Real.toNNReal_pos.mpr ht) f).val (some i) x)
    else 0
  change IntegrableOn E (Set.Ioo 0 T)
  have hE (t : ℝ) (ht : 0 < t) : 0 ≤ E t := by
    simp only [E, dite_eq_left ht]
    apply integral_nonneg
    intro x
    let v : PDE.Vec d := fun i => (Q t.toNNReal (Real.toNNReal_pos.mpr ht) f).val (some i) x
    have hv0 : 0 ≤ euclideanSq v := by
      unfold euclideanSq dot
      exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (v i))
    have hl := (h.2.2 x).2.2.2 v
    have hc : 0 ≤ dot v ((α x).mulVec v) := (mul_nonneg hκ.le hv0).trans hl.1
    change 0 ≤ dot ((α x).mulVec v) v
    unfold dot at hc ⊢
    simpa only [mul_comm] using hc
  let F : ℝ → ℝ := -(fun t : ℝ =>
    ‖SpectralHeat.heatOperator (spectralHeatBasis s) s.eigenvalue
      (fun n => (s.eigenvalue_pos n).le) t.toNNReal f‖ ^ 2)
  have hF : Continuous F := by
    exact (((SpectralHeat.heatOperator_continuous (spectralHeatBasis s) s.eigenvalue
      (fun n => (s.eigenvalue_pos n).le) f).comp continuous_real_toNNReal).norm.pow 2).neg
  have hdF (t : ℝ) (ht : 0 < t) : HasDerivAt F (2 * E t) t := by
    have hd := ((hQ t.toNNReal (Real.toNNReal_pos.mpr ht)).2 f).neg
    simpa only [F, E, dite_eq_left ht, Real.coe_toNNReal t ht.le, neg_mul, neg_neg, Pi.neg_apply] using hd
  have hi : IntegrableOn (fun t => 2 * E t) (Set.Ioc 0 T) :=
    intervalIntegral.integrableOn_deriv_of_nonneg hF.continuousOn
      (fun t ht => hdF t ht.1) (fun t ht => mul_nonneg (by norm_num) (hE t ht.1))
  rw [integrableOn_Ioc_iff_integrableOn_Ioo] at hi
  change Integrable (fun t => E t) (volume.restrict (Set.Ioo 0 T))
  simpa only [← mul_assoc, show (2 : ℝ)⁻¹ * 2 = 1 by norm_num, one_mul]
    using hi.const_mul ((2 : ℝ)⁻¹)

/-- The ellipticity lower bound controls Lebesgue measure on the native ball
by the actual weighted Dirichlet measure. -/
theorem c9_native_lebesgue_measure_le {d : ℕ} {κ R : ℝ}
    (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ} {α : PDE.Vec d → EinsteinRelation.Mat d}
    (h : IsUniformlyElliptic κ ρ α) :
    volume.restrict (sourceBall (0 : PDE.Vec d) R) ≤
      ENNReal.ofReal κ⁻¹ • dirichletVolume ρ R := by
  have hl : ∀ x, 1 ≤ κ⁻¹ * ρ x := by
    intro x
    have hx : κ * κ⁻¹ ≤ ρ x * κ⁻¹ :=
      mul_le_mul_of_nonneg_right (h.2.2 x).1 (inv_nonneg.mpr hκ.le)
    simpa only [mul_inv_cancel₀ hκ.ne', mul_comm] using hx
  conv_lhs => rw [← one_smul ℝ≥0∞ (volume.restrict (sourceBall (0 : PDE.Vec d) R)),
    ← withDensity_const]
  unfold dirichletVolume
  rw [← withDensity_smul _ h.1.ennreal_ofReal]
  apply withDensity_mono
  filter_upwards with x
  change (1 : ℝ≥0∞) ≤ ENNReal.ofReal κ⁻¹ * ENNReal.ofReal (ρ x)
  rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hκ.le)]
  simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (hl x)

/-- The actual native heat flow reaches its datum strongly in unweighted
Lebesgue L² on the whole Dirichlet ball. -/
theorem c9_native_heat_initial_lebesgue_L2 {d : ℕ} {κ R : ℝ}
    (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ} {α : PDE.Vec d → EinsteinRelation.Mat d}
    (h : IsUniformlyElliptic κ ρ α) (s : DirichletSpectralResolution ρ α R)
    (f : Lp ℝ 2 (dirichletVolume ρ R)) :
    let M : Lp ℝ 2 (dirichletVolume ρ R) →L[ℝ]
        Lp ℝ 2 (volume.restrict (sourceBall (0 : PDE.Vec d) R)) :=
      Lp.LpToLpOfMeasureLeSMul ENNReal.ofReal_ne_top (c9_native_lebesgue_measure_le hκ h)
    ((∀ v, M v =ᵐ[volume.restrict (sourceBall (0 : PDE.Vec d) R)] v) ∧
      Tendsto (fun t : ℝ => M (SpectralHeat.heatOperator (spectralHeatBasis s)
        s.eigenvalue (fun n => (s.eigenvalue_pos n).le) t.toNNReal f))
        (𝓝 0) (𝓝 (M f))) := by
  dsimp only
  constructor
  · exact fun v => Lp.coeFn_LpToLpOfMeasureLeSMul ENNReal.ofReal_ne_top
      (c9_native_lebesgue_measure_le hκ h) v
  · have ht := (c9_native_heat_initial_L2 s f).comp
      (show Tendsto (fun t : ℝ => t.toNNReal) (𝓝 0) (𝓝 (0 : ℝ≥0)) by
        simpa using continuous_real_toNNReal.tendsto (0 : ℝ))
    exact (Lp.LpToLpOfMeasureLeSMul ENNReal.ofReal_ne_top
      (c9_native_lebesgue_measure_le hκ h)).continuous.continuousAt.tendsto.comp ht

/-- The literal kernel action has zero local L² trace on the cutoff plateau. -/
theorem c9_cutoff_kernel_zero_trace {d : ℕ} (hd : 2 ≤ d)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    {ρ : PDE.Vec d → ℝ} {α : PDE.Vec d → EinsteinRelation.Mat d}
    (h : IsUniformlyElliptic κ ρ α) (s : DirichletSpectralResolution ρ α R)
    (φ : PDE.Vec d → ℝ) (hφ : IsSpatialTest (sourceBall 0 R) φ)
    (hφbounds : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    (y : PDE.Vec d) (r : ℝ) (hr : 0 < r)
    (hinside : closure (sourceBall y (2*r)) ⊆ sourceBall 0 R)
    (hplateau : ∀ x ∈ sourceBall y (2*r), φ x = 1) :
    Tendsto (fun t : ℝ => ∫ x in sourceBall y r, |(∫ z,
      (∑' n, Real.exp (-s.eigenvalue n * t) * s.eigenfunction n x *
        s.eigenfunction n z) * φ z ∂dirichletVolume ρ R) - 1|^2)
      (𝓝[>] 0) (𝓝 0) := by
  have hsmall : sourceBall y r ⊆ sourceBall y (2*r) := by
    intro x hx
    change euclideanNorm (x - y) < r at hx
    change euclideanNorm (x - y) < 2*r
    linarith
  have hsub : sourceBall y r ⊆ sourceBall 0 R :=
    hsmall.trans (subset_closure.trans hinside)
  have hle : volume.restrict (sourceBall y r) ≤
      ENNReal.ofReal κ⁻¹ • dirichletVolume ρ R :=
    (Measure.restrict_mono hsub le_rfl).trans (c9_native_lebesgue_measure_le hκ h)
  let M : Lp ℝ 2 (dirichletVolume ρ R) →L[ℝ] Lp ℝ 2 (volume.restrict (sourceBall y r)) :=
    Lp.LpToLpOfMeasureLeSMul ENNReal.ofReal_ne_top hle
  let f := (c9_cutoff_memLp_dirichletVolume hR h φ hφ hφbounds).toLp φ
  let V : ℝ → Lp ℝ 2 (volume.restrict (sourceBall y r)) := fun t =>
    M (SpectralHeat.heatOperator (spectralHeatBasis s) s.eigenvalue
      (fun n => (s.eigenvalue_pos n).le) t.toNNReal f) - M f
  have ht : Tendsto V (𝓝[>] 0) (𝓝 0) := by
    have h0 := (c9_native_heat_initial_L2 s f).comp
      (show Tendsto (fun t : ℝ => t.toNNReal) (𝓝 0) (𝓝 (0 : ℝ≥0)) by
        simpa using continuous_real_toNNReal.tendsto (0 : ℝ))
    have h1 := M.continuous.continuousAt.tendsto.comp h0
    have h2 := h1.sub (tendsto_const_nhds (x := M f))
    have h3 : Tendsto V (𝓝 0) (𝓝 0) := by simpa [V] using h2
    exact h3.mono_left nhdsWithin_le_nhds
  have hn : Tendsto (fun t => ‖V t‖ ^ 2) (𝓝[>] 0) (𝓝 0) := by
    simpa using (ht.norm.pow 2)
  apply hn.congr'
  filter_upwards [self_mem_nhdsWithin] with t htpos
  have hk := c9_cutoff_heat_kernel_action hd hκ hR h s φ hφ hφbounds t.toNNReal
    (by simpa using htpos)
  have hk' := (Measure.absolutelyContinuous_of_le_smul hle).ae_eq hk
  have hf := (Measure.absolutelyContinuous_of_le_smul hle).ae_eq
    (c9_cutoff_memLp_dirichletVolume hR h φ hφ hφbounds).coeFn_toLp
  have hball : MeasurableSet (sourceBall y r) := by
    have hs : Continuous (fun v : PDE.Vec d => ∑ j, v j * v j) :=
      continuous_finset_sum Finset.univ fun j _ => (continuous_apply j).mul (continuous_apply j)
    have he : Continuous (fun v : PDE.Vec d => euclideanNorm v) := by
      unfold euclideanNorm euclideanSq dot
      exact Real.continuous_sqrt.comp hs
    exact (isOpen_lt (he.comp (continuous_id.sub continuous_const)) continuous_const).measurableSet
  have hV : V t =ᵐ[volume.restrict (sourceBall y r)] fun x =>
      (∫ z, (∑' n, Real.exp (-s.eigenvalue n * t) * s.eigenfunction n x *
        s.eigenfunction n z) * φ z ∂dirichletVolume ρ R) - 1 := by
    filter_upwards [Lp.coeFn_sub (M (SpectralHeat.heatOperator (spectralHeatBasis s)
      s.eigenvalue (fun n => (s.eigenvalue_pos n).le) t.toNNReal f)) (M f),
      Lp.coeFn_LpToLpOfMeasureLeSMul ENNReal.ofReal_ne_top hle
        (SpectralHeat.heatOperator (spectralHeatBasis s) s.eigenvalue
          (fun n => (s.eigenvalue_pos n).le) t.toNNReal f),
      Lp.coeFn_LpToLpOfMeasureLeSMul ENNReal.ofReal_ne_top hle f,
      hk', hf, ae_restrict_mem hball] with x hx hm1 hm2 hkx hfx hxr
    change (M _ - M f) x = _
    rw [hx]
    change M _ x - M f x = _
    rw [hm1, hm2, show f x = φ x from hfx, hplateau x (hsmall hxr), hkx,
      Real.coe_toNNReal t (le_of_lt htpos)]
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hV] with x hx
  rw [hx]
  simp [Real.inner_apply, sq_abs]

/-- The native lift itself is square-integrable in time, including at zero.
Coercivity transfers the already established finite Dirichlet energy. -/
theorem c9_native_heat_lift_time_memLp {d : ℕ} (hd : 2 ≤ d)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    {ρ : PDE.Vec d → ℝ} {α : PDE.Vec d → EinsteinRelation.Mat d}
    (h : IsUniformlyElliptic κ ρ α) (s : DirichletSpectralResolution ρ α R)
    (u : ℕ → DirichletHilbertSpace (d := d) R hR)
    (hb : ∀ n, spectralHeatBasis s n = dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (h.2.2 x).2.1) (u n))
    (hv : ∀ n w, (∫ x in sourceBall (0 : PDE.Vec d) R,
      dot ((α x).mulVec (fun i => (u n).val (some i) x))
        (fun i => w.val (some i) x)) = s.eigenvalue n * inner ℝ
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) (u n))
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) w)) :
    let J := dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
    ∃ Q : (t : ℝ≥0) → 0 < t →
      Lp ℝ 2 (dirichletVolume ρ R) →L[ℝ] DirichletHilbertSpace (d := d) R hR,
      (∀ f, Continuous (fun t : {t : ℝ≥0 // 0 < t} => Q t.val t.property f)) ∧
      (∀ t ht, J.comp (Q t ht) = SpectralHeat.heatOperator (spectralHeatBasis s)
        s.eigenvalue (fun n => (s.eigenvalue_pos n).le) t) ∧
      ∀ (f : Lp ℝ 2 (dirichletVolume ρ R)) (T : ℝ),
        MemLp (fun t : ℝ => if ht : 0 < t then
          Q t.toNNReal (Real.toNNReal_pos.mpr ht) f else 0) 2
          (volume.restrict (Set.Ioo 0 T)) := by
  dsimp only
  obtain ⟨Q, hcont, hJ, henergy⟩ := c9_native_heat_finite_energy hd hκ hR h s u hb hv
  obtain ⟨c, hc, B, hcoerc, hform⟩ := exists_dirichletHilbert_energyForm hd hκ h R hR
  refine ⟨Q, hcont, hJ, ?_⟩
  intro f T
  let V : ℝ → DirichletHilbertSpace (d := d) R hR := fun t =>
    if ht : 0 < t then Q t.toNNReal (Real.toNNReal_pos.mpr ht) f else 0
  have hVc : ContinuousOn V (Set.Ioi 0) := by
    rw [continuousOn_iff_continuous_restrict]
    have ht : Continuous (fun t : Set.Ioi (0 : ℝ) =>
        (⟨t.val.toNNReal, Real.toNNReal_pos.mpr t.property⟩ : {t : ℝ≥0 // 0 < t})) :=
      (continuous_real_toNNReal.comp continuous_subtype_val).subtype_mk _
    change Continuous (fun t : Set.Ioi (0 : ℝ) => V t.val)
    convert (hcont f).comp ht using 1
    funext t
    have hp : 0 < t.val := t.property
    simp only [V, dif_pos hp, Function.comp_apply]
  have hm : AEStronglyMeasurable V (volume.restrict (Set.Ioo 0 T)) :=
    (hVc.aestronglyMeasurable_of_isSeparable measurableSet_Ioi
      (TopologicalSpace.IsSeparable.of_separableSpace _)).mono_measure
      (Measure.restrict_mono (by intro t ht; exact ht.1) le_rfl)
  change MemLp V 2 (volume.restrict (Set.Ioo 0 T))
  apply (memLp_two_iff_integrable_sq_norm hm).2
  have hi := (henergy f T).const_mul c⁻¹
  apply hi.mono' (hm.norm.pow 2)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  have hbnd := hcoerc (V t)
  rw [hform] at hbnd
  have hn : ‖V t‖ ^ 2 ≤ c⁻¹ * (∫ x in sourceBall (0 : PDE.Vec d) R,
      dot ((α x).mulVec (fun i => (V t).val (some i) x))
        (fun i => (V t).val (some i) x)) := by
    exact (le_inv_mul_iff₀ hc).2 hbnd
  change |‖V t‖ ^ 2| ≤ _
  rw [abs_of_nonneg (sq_nonneg ‖V t‖)]
  simpa only [V, dite_eq_left ht.1] using hn

/-- A time-L² path of spatial L² classes has a product-L² representative
whose almost-everywhere time slices represent the original path. -/
theorem c9_time_L2_product_representative {β : Type*} [MeasurableSpace β]
    (μ : Measure ℝ) (ν : Measure β) [SFinite ν]
    (g : ℝ → Lp ℝ 2 ν) (hg : MemLp g 2 μ) :
    ∃ G : Lp ℝ 2 (μ.prod ν),
      ∀ᵐ t ∂μ, (fun x => G (t, x)) =ᵐ[ν] g t := by
  let g' := hg.aestronglyMeasurable.mk g
  have hg' : StronglyMeasurable g' := hg.aestronglyMeasurable.stronglyMeasurable_mk
  have heq : g =ᵐ[μ] g' := hg.aestronglyMeasurable.ae_eq_mk
  have hmem : MemLp g' 2 μ := (memLp_congr_ae heq).mp hg
  letI : MeasurableSpace (Lp ℝ 2 ν) := borel _
  letI : BorelSpace (Lp ℝ 2 ν) := ⟨rfl⟩
  letI : TopologicalSpace.SeparableSpace (Set.range g' ∪ {0} : Set _) :=
    hg'.separableSpace_range_union_singleton
  let F : ℕ → SimpleFunc ℝ (Lp ℝ 2 ν) :=
    SimpleFunc.approxOn g' hg'.measurable (Set.range g' ∪ {0}) 0 (by simp)
  have hf (n : ℕ) : MemLp (fun t => F n t) 2 μ :=
    SimpleFunc.memLp_approxOn_range hg'.measurable hmem n
  have hconv : Tendsto (fun n => eLpNorm (fun t => F n t - g' t) 2 μ)
      atTop (𝓝 0) := by
    simpa only [F, Pi.sub_def] using
      (SimpleFunc.tendsto_approxOn_range_Lp_eLpNorm (p := 2) (μ := μ)
        (by simp) hg'.measurable hmem)
  have hpoint (t : ℝ) : Tendsto (fun n => F n t) atTop (𝓝 (g' t)) :=
    SimpleFunc.tendsto_approxOn hg'.measurable (by simp)
      (subset_closure (show g' t ∈ Set.range g' ∪ {0} from Or.inl ⟨t, rfl⟩))
  obtain ⟨G, hG, _⟩ := simpleFunc_lp_product_limit_slices μ ν F g' hf hmem hconv hpoint
  refine ⟨G, ?_⟩
  filter_upwards [hG, heq] with t ht he
  simpa only [he] using ht

/-- The actual native lift has a jointly measurable spacetime L² gradient. -/
theorem c9_native_heat_gradient_product {d : ℕ} (hd : 2 ≤ d)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    {ρ : PDE.Vec d → ℝ} {α : PDE.Vec d → EinsteinRelation.Mat d}
    (h : IsUniformlyElliptic κ ρ α) (s : DirichletSpectralResolution ρ α R)
    (u : ℕ → DirichletHilbertSpace (d := d) R hR)
    (hb : ∀ n, spectralHeatBasis s n = dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (h.2.2 x).2.1) (u n))
    (hv : ∀ n w, (∫ x in sourceBall (0 : PDE.Vec d) R,
      dot ((α x).mulVec (fun i => (u n).val (some i) x))
        (fun i => w.val (some i) x)) = s.eigenvalue n * inner ℝ
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) (u n))
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) w)) (f : Lp ℝ 2 (dirichletVolume ρ R)) (T : ℝ) :
    let J := dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
    let μ := volume.restrict (Set.Ioo 0 T)
    let ν := volume.restrict ((SubdiffusiveProcess.centeredCube (0 : PDE.Vec d)
      (2 * R) (mul_pos two_pos hR)) : Set (PDE.Vec d))
    ∃ (V : ℝ → DirichletHilbertSpace (d := d) R hR) (G : ℝ × PDE.Vec d → PDE.Vec d),
      (∀ t, 0 < t → J (V t) = SpectralHeat.heatOperator (spectralHeatBasis s)
        s.eigenvalue (fun n => (s.eigenvalue_pos n).le) t.toNNReal f) ∧
      MemLp V 2 μ ∧ AEStronglyMeasurable G (μ.prod ν) ∧
      MemLp (fun z => euclideanNorm (G z)) 2 (μ.prod ν) ∧
      (∀ᵐ t ∂μ, (fun x => G (t, x)) =ᵐ[ν]
        (fun x i => (V t).val (some i) x)) := by
  dsimp only
  obtain ⟨Q, _hcont, hJ, hQmem⟩ := c9_native_heat_lift_time_memLp hd hκ hR h s u hb hv
  let V : ℝ → DirichletHilbertSpace (d := d) R hR := fun t =>
    if ht : 0 < t then Q t.toNNReal (Real.toNNReal_pos.mpr ht) f else 0
  let μ := volume.restrict (Set.Ioo 0 T)
  let ν := volume.restrict ((SubdiffusiveProcess.centeredCube (0 : PDE.Vec d)
    (2 * R) (mul_pos two_pos hR)) : Set (PDE.Vec d))
  have hV : MemLp V 2 μ := hQmem f T
  let P (i : Fin d) := (ContinuousLinearMap.proj i).comp
    ((ContinuousLinearMap.snd ℝ _ _).comp
      ((hilbertToSobolev _).comp (dirichletHilbertSubmodule (d := d) R hR).subtypeL))
  have hP (i : Fin d) : MemLp (fun t => P i (V t)) 2 μ := by
    simpa only [Function.comp_def] using (P i).comp_memLp' hV
  choose H hH using fun i => c9_time_L2_product_representative μ ν (fun t => P i (V t)) (hP i)
  have hvec := lp_coordinates_euclidean_memLp (μ.prod ν) H
  refine ⟨V, (fun z i => H i z), ?_, hV, hvec.1, hvec.2, ?_⟩
  · intro t ht
    simp only [V, dif_pos ht]
    exact congrArg (fun A : _ →L[ℝ] _ => A f) (hJ t.toNNReal (Real.toNNReal_pos.mpr ht))
  · filter_upwards [ae_all_iff.mpr hH] with t ht
    filter_upwards [ae_all_iff.mpr ht] with x hx
    funext i
    exact hx i

/-- The joint gradient lift also satisfies the native weak evolution identity. -/
theorem c9_native_heat_gradient_product_weakFlow {d : ℕ} (hd : 2 ≤ d)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    {ρ : PDE.Vec d → ℝ} {α : PDE.Vec d → EinsteinRelation.Mat d}
    (h : IsUniformlyElliptic κ ρ α) (s : DirichletSpectralResolution ρ α R)
    (u : ℕ → DirichletHilbertSpace (d := d) R hR)
    (hb : ∀ n, spectralHeatBasis s n = dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (h.2.2 x).2.1) (u n))
    (hv : ∀ n w, (∫ x in sourceBall (0 : PDE.Vec d) R,
      dot ((α x).mulVec (fun i => (u n).val (some i) x))
        (fun i => w.val (some i) x)) = s.eigenvalue n * inner ℝ
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) (u n))
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) w)) (f : Lp ℝ 2 (dirichletVolume ρ R)) (T : ℝ) :
    let J := dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
    let μ := volume.restrict (Set.Ioo 0 T)
    let ν := volume.restrict ((SubdiffusiveProcess.centeredCube (0 : PDE.Vec d)
      (2 * R) (mul_pos two_pos hR)) : Set (PDE.Vec d))
    ∃ (V : ℝ → DirichletHilbertSpace (d := d) R hR) (G : ℝ × PDE.Vec d → PDE.Vec d),
      (∀ t, 0 < t → J (V t) = SpectralHeat.heatOperator (spectralHeatBasis s)
        s.eigenvalue (fun n => (s.eigenvalue_pos n).le) t.toNNReal f) ∧
      MemLp V 2 μ ∧ AEStronglyMeasurable G (μ.prod ν) ∧
      MemLp (fun z => euclideanNorm (G z)) 2 (μ.prod ν) ∧
      (∀ᵐ t ∂μ, (fun x => G (t, x)) =ᵐ[ν]
        (fun x i => (V t).val (some i) x)) ∧
      ∀ t, 0 < t → ∀ v, HasDerivAt
        (fun r : ℝ => inner ℝ
          (SpectralHeat.heatOperator (spectralHeatBasis s) s.eigenvalue
            (fun n => (s.eigenvalue_pos n).le) r.toNNReal f) (J v))
        (-(∫ x in sourceBall (0 : PDE.Vec d) R,
          dot ((α x).mulVec (fun i => (V t).val (some i) x))
            (fun i => v.val (some i) x))) t := by
  dsimp only
  obtain ⟨V, G, hJ, hV, hGm, hGl, hslice⟩ :=
    c9_native_heat_gradient_product hd hκ hR h s u hb hv f T
  obtain ⟨Q, _, hQ⟩ := spectral_heat_native_weakFlow hd hκ h R hR s u hb hv
  refine ⟨V, G, hJ, hV, hGm, hGl, hslice, ?_⟩
  intro t ht v
  have heq : V t = Q t.toNNReal (Real.toNNReal_pos.mpr ht) f := by
    apply injective_dirichletHilbertInclusion hκ h R hR
    rw [hJ t ht]
    exact (congrArg (fun A : _ →L[ℝ] _ => A f)
      (hQ t.toNNReal (Real.toNNReal_pos.mpr ht)).1).symm
  have hd := (hQ t.toNNReal (Real.toNNReal_pos.mpr ht)).2.2 f v
  rw [← heq] at hd
  simpa only [Real.coe_toNNReal _ ht.le] using hd

/-- The native flow has joint L² representatives for both value and gradient. -/
theorem c9_native_heat_spacetime_representatives {d : ℕ} (hd : 2 ≤ d)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    {ρ : PDE.Vec d → ℝ} {α : PDE.Vec d → EinsteinRelation.Mat d}
    (h : IsUniformlyElliptic κ ρ α) (s : DirichletSpectralResolution ρ α R)
    (u : ℕ → DirichletHilbertSpace (d := d) R hR)
    (hb : ∀ n, spectralHeatBasis s n = dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (h.2.2 x).2.1) (u n))
    (hv : ∀ n w, (∫ x in sourceBall (0 : PDE.Vec d) R,
      dot ((α x).mulVec (fun i => (u n).val (some i) x))
        (fun i => w.val (some i) x)) = s.eigenvalue n * inner ℝ
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) (u n))
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) w)) (f : Lp ℝ 2 (dirichletVolume ρ R)) (T : ℝ) :
    let J := dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
    let μ := volume.restrict (Set.Ioo 0 T)
    let ν := volume.restrict ((SubdiffusiveProcess.centeredCube (0 : PDE.Vec d)
      (2 * R) (mul_pos two_pos hR)) : Set (PDE.Vec d))
    ∃ (V : ℝ → DirichletHilbertSpace (d := d) R hR) (G : ℝ × PDE.Vec d → PDE.Vec d)
      (U : Lp ℝ 2 (μ.prod ν)),
      (∀ t, 0 < t → J (V t) = SpectralHeat.heatOperator (spectralHeatBasis s)
        s.eigenvalue (fun n => (s.eigenvalue_pos n).le) t.toNNReal f) ∧
      MemLp V 2 μ ∧ AEStronglyMeasurable G (μ.prod ν) ∧
      MemLp (fun z => euclideanNorm (G z)) 2 (μ.prod ν) ∧
      (∀ᵐ t ∂μ, (fun x => G (t, x)) =ᵐ[ν]
        (fun x i => (V t).val (some i) x)) ∧
      (∀ t, 0 < t → ∀ v, HasDerivAt
        (fun r : ℝ => inner ℝ
          (SpectralHeat.heatOperator (spectralHeatBasis s) s.eigenvalue
            (fun n => (s.eigenvalue_pos n).le) r.toNNReal f) (J v))
        (-(∫ x in sourceBall (0 : PDE.Vec d) R,
          dot ((α x).mulVec (fun i => (V t).val (some i) x))
            (fun i => v.val (some i) x))) t) ∧
      (∀ᵐ t ∂μ, (fun x => U (t, x)) =ᵐ[ν] (V t).val none) := by
  dsimp only
  obtain ⟨V, G, hJ, hV, hGm, hGl, hslice, hderiv⟩ :=
    c9_native_heat_gradient_product_weakFlow hd hκ hR h s u hb hv f T
  let P := (ContinuousLinearMap.fst ℝ _ _).comp
    ((hilbertToSobolev _).comp (dirichletHilbertSubmodule (d := d) R hR).subtypeL)
  have hP : MemLp (fun t => P (V t)) 2 (volume.restrict (Set.Ioo 0 T)) := by
    simpa only [Function.comp_def] using P.comp_memLp' hV
  obtain ⟨U, hU⟩ := c9_time_L2_product_representative
    (volume.restrict (Set.Ioo 0 T))
    (volume.restrict ((SubdiffusiveProcess.centeredCube (0 : PDE.Vec d)
      (2 * R) (mul_pos two_pos hR)) : Set (PDE.Vec d))) (fun t => P (V t)) hP
  refine ⟨V, G, U, hJ, hV, hGm, hGl, hslice, hderiv, ?_⟩
  filter_upwards [hU] with t ht
  exact ht

/-- On the Dirichlet ball the native value coordinate is the literal heat
kernel action, for every positive time. -/
theorem c9_native_value_ae_kernel_action {d : ℕ} (hd : 2 ≤ d)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    {ρ : PDE.Vec d → ℝ} {α : PDE.Vec d → EinsteinRelation.Mat d}
    (h : IsUniformlyElliptic κ ρ α) (s : DirichletSpectralResolution ρ α R)
    (f : Lp ℝ 2 (dirichletVolume ρ R)) (t : ℝ) (ht : 0 < t)
    (v : DirichletHilbertSpace (d := d) R hR)
    (hv : dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (h.2.2 x).2.1) v =
        SpectralHeat.heatOperator (spectralHeatBasis s) s.eigenvalue
          (fun n => (s.eigenvalue_pos n).le) t.toNNReal f) :
    (fun x => v.val none x) =ᵐ[volume.restrict (sourceBall (0 : PDE.Vec d) R)]
      fun x => ∫ y, (∑' n, Real.exp (-s.eigenvalue n * t) *
        s.eigenfunction n x * s.eigenfunction n y) * f y ∂dirichletVolume ρ R := by
  have hincl := dirichletHilbertInclusion_coe ρ R hR κ⁻¹
    (fun x _ => (h.2.2 x).2.1) v
  change (dirichletHilbertInclusion ρ R hR κ⁻¹
    (fun x _ => (h.2.2 x).2.1) v) =ᵐ[dirichletVolume ρ R] v.val none at hincl
  rw [hv] at hincl
  have hk := spectral_heat_operator_ae_kernel_action hd hκ h hR s t.toNNReal
    (by simpa using ht) f
  have heq := hincl.symm.trans hk
  have heq' := (Measure.absolutelyContinuous_of_le_smul
    (c9_native_lebesgue_measure_le hκ h)).ae_eq heq
  simpa only [Real.coe_toNNReal t ht.le] using heq'

/-- The joint native value represents the literal kernel on almost every time slice. -/
theorem c9_native_heat_spacetime_kernel_slices {d : ℕ} (hd : 2 ≤ d)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    {ρ : PDE.Vec d → ℝ} {α : PDE.Vec d → EinsteinRelation.Mat d}
    (h : IsUniformlyElliptic κ ρ α) (s : DirichletSpectralResolution ρ α R)
    (u : ℕ → DirichletHilbertSpace (d := d) R hR)
    (hb : ∀ n, spectralHeatBasis s n = dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (h.2.2 x).2.1) (u n))
    (hv : ∀ n w, (∫ x in sourceBall (0 : PDE.Vec d) R,
      dot ((α x).mulVec (fun i => (u n).val (some i) x))
        (fun i => w.val (some i) x)) = s.eigenvalue n * inner ℝ
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) (u n))
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) w)) (f : Lp ℝ 2 (dirichletVolume ρ R)) (T : ℝ) :
    let J := dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
    let μ := volume.restrict (Set.Ioo 0 T)
    let ν := volume.restrict ((SubdiffusiveProcess.centeredCube (0 : PDE.Vec d)
      (2 * R) (mul_pos two_pos hR)) : Set (PDE.Vec d))
    ∃ (V : ℝ → DirichletHilbertSpace (d := d) R hR) (G : ℝ × PDE.Vec d → PDE.Vec d)
      (U : Lp ℝ 2 (μ.prod ν)),
      (∀ t, 0 < t → J (V t) = SpectralHeat.heatOperator (spectralHeatBasis s)
        s.eigenvalue (fun n => (s.eigenvalue_pos n).le) t.toNNReal f) ∧
      MemLp V 2 μ ∧ AEStronglyMeasurable G (μ.prod ν) ∧
      MemLp (fun z => euclideanNorm (G z)) 2 (μ.prod ν) ∧
      (∀ᵐ t ∂μ, (fun x => G (t, x)) =ᵐ[ν]
        (fun x i => (V t).val (some i) x)) ∧
      (∀ t, 0 < t → ∀ v, HasDerivAt
        (fun r : ℝ => inner ℝ
          (SpectralHeat.heatOperator (spectralHeatBasis s) s.eigenvalue
            (fun n => (s.eigenvalue_pos n).le) r.toNNReal f) (J v))
        (-(∫ x in sourceBall (0 : PDE.Vec d) R,
          dot ((α x).mulVec (fun i => (V t).val (some i) x))
            (fun i => v.val (some i) x))) t) ∧
      (∀ᵐ t ∂μ, (fun x => U (t, x)) =ᵐ[ν] (V t).val none) ∧
      (∀ᵐ t ∂μ, (fun x => U (t, x)) =ᵐ[volume.restrict (sourceBall (0 : PDE.Vec d) R)]
        fun x => ∫ y, (∑' n, Real.exp (-s.eigenvalue n * t) *
          s.eigenfunction n x * s.eigenfunction n y) * f y ∂dirichletVolume ρ R) := by
  dsimp only
  obtain ⟨V, G, U, hJ, hV, hGm, hGl, hslice, hderiv, hU⟩ :=
    c9_native_heat_spacetime_representatives hd hκ hR h s u hb hv f T
  refine ⟨V, G, U, hJ, hV, hGm, hGl, hslice, hderiv, hU, ?_⟩
  filter_upwards [hU, ae_restrict_mem measurableSet_Ioo] with t ht htp
  have hUball := ae_restrict_of_ae_restrict_of_subset (sourceBall_subset_cube R hR) ht
  have hk := c9_native_value_ae_kernel_action hd hκ hR h s f t htp.1 (V t) (hJ t htp.1)
  filter_upwards [hUball, hk] with x hx hy
  exact hx.trans hy

/-- The actual kernel action has the spatial weak gradient of its native lift. -/
theorem c9_native_kernel_action_weakGradient {d : ℕ} (hd : 2 ≤ d)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    {ρ : PDE.Vec d → ℝ} {α : PDE.Vec d → EinsteinRelation.Mat d}
    (h : IsUniformlyElliptic κ ρ α) (s : DirichletSpectralResolution ρ α R)
    (f : Lp ℝ 2 (dirichletVolume ρ R)) (t : ℝ) (ht : 0 < t)
    (v : DirichletHilbertSpace (d := d) R hR)
    (hv : dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (h.2.2 x).2.1) v =
        SpectralHeat.heatOperator (spectralHeatBasis s) s.eigenvalue
          (fun n => (s.eigenvalue_pos n).le) t.toNNReal f) :
    HasWeakGradient (sourceBall (0 : PDE.Vec d) R)
      (fun x => ∫ y, (∑' n, Real.exp (-s.eigenvalue n * t) *
        s.eigenfunction n x * s.eigenfunction n y) * f y ∂dirichletVolume ρ R)
      (fun x i => v.val (some i) x) := by
  have hU : IsOpen (sourceBall (0 : PDE.Vec d) R) := (dirichletBall (d := d) R).isOpen
  have hk := c9_native_value_ae_kernel_action hd hκ hR h s f t ht v hv
  apply EinsteinRelation.Correctors.hasWeakGradient_congr_ae hU
    (EinsteinRelation.Correctors.hasWeakGradient_mono (Set.subset_univ _)
      (dirichletHilbert_global_zeroExtension R hR v).2.2)
  · filter_upwards [ae_restrict_mem hU.measurableSet, hk] with x hx hval
    simpa only [dirichletHilbertZeroExtension, Set.indicator_of_mem hx] using hval
  · filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
    exact Set.indicator_of_mem hx _

/-- The joint native gradient represents the kernel action on almost every time slice. -/
theorem c9_native_kernel_action_joint_weakGradient {d : ℕ} (hd : 2 ≤ d)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    {ρ : PDE.Vec d → ℝ} {α : PDE.Vec d → EinsteinRelation.Mat d}
    (h : IsUniformlyElliptic κ ρ α) (s : DirichletSpectralResolution ρ α R)
    (f : Lp ℝ 2 (dirichletVolume ρ R)) (T : ℝ)
    (V : ℝ → DirichletHilbertSpace (d := d) R hR)
    (G : ℝ × PDE.Vec d → PDE.Vec d)
    (hJ : ∀ t, 0 < t → dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (h.2.2 x).2.1) (V t) =
        SpectralHeat.heatOperator (spectralHeatBasis s) s.eigenvalue
          (fun n => (s.eigenvalue_pos n).le) t.toNNReal f)
    (hG : ∀ᵐ t ∂volume.restrict (Set.Ioo 0 T),
      (fun x => G (t, x)) =ᵐ[volume.restrict
        ((SubdiffusiveProcess.centeredCube (0 : PDE.Vec d) (2 * R)
          (mul_pos two_pos hR)) : Set (PDE.Vec d))]
        (fun x i => (V t).val (some i) x)) :
    ∀ᵐ t ∂volume.restrict (Set.Ioo 0 T),
      HasWeakGradient (sourceBall (0 : PDE.Vec d) R)
        (fun x => ∫ y, (∑' n, Real.exp (-s.eigenvalue n * t) *
          s.eigenfunction n x * s.eigenfunction n y) * f y ∂dirichletVolume ρ R)
        (fun x => G (t, x)) := by
  have hball : IsOpen (sourceBall (0 : PDE.Vec d) R) :=
    (dirichletBall (d := d) R).isOpen
  filter_upwards [hG, ae_restrict_mem measurableSet_Ioo] with t ht htime
  have hgrad := c9_native_kernel_action_weakGradient hd hκ hR h s f t htime.1
    (V t) (hJ t htime.1)
  apply EinsteinRelation.Correctors.hasWeakGradient_congr_ae hball hgrad
  · exact Filter.Eventually.of_forall (fun _ => rfl)
  · filter_upwards [ae_restrict_of_ae_restrict_of_subset (sourceBall_subset_cube R hR) ht] with x hx
    exact hx.symm

/-- The actual native heat flow satisfies the product rule along differentiable test paths. -/
theorem c9_native_heat_path_derivative {d : ℕ} (hd : 2 ≤ d)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    {ρ : PDE.Vec d → ℝ} {α : PDE.Vec d → EinsteinRelation.Mat d}
    (h : IsUniformlyElliptic κ ρ α) (s : DirichletSpectralResolution ρ α R)
    (u : ℕ → DirichletHilbertSpace (d := d) R hR)
    (hb : ∀ n, spectralHeatBasis s n = dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (h.2.2 x).2.1) (u n))
    (hv : ∀ n w, (∫ x in sourceBall (0 : PDE.Vec d) R,
      dot ((α x).mulVec (fun i => (u n).val (some i) x))
        (fun i => w.val (some i) x)) = s.eigenvalue n * inner ℝ
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) (u n))
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) w))
    (f : Lp ℝ 2 (dirichletVolume ρ R)) (T : ℝ) :
    let J := dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
    let μ := volume.restrict (Set.Ioo 0 T)
    let ν := volume.restrict ((SubdiffusiveProcess.centeredCube (0 : PDE.Vec d)
      (2 * R) (mul_pos two_pos hR)) : Set (PDE.Vec d))
    ∃ (V : ℝ → DirichletHilbertSpace (d := d) R hR) (G : ℝ × PDE.Vec d → PDE.Vec d),
      (∀ t, 0 < t → J (V t) = SpectralHeat.heatOperator (spectralHeatBasis s)
        s.eigenvalue (fun n => (s.eigenvalue_pos n).le) t.toNNReal f) ∧
      MemLp V 2 μ ∧ AEStronglyMeasurable G (μ.prod ν) ∧
      MemLp (fun z => euclideanNorm (G z)) 2 (μ.prod ν) ∧
      (∀ᵐ t ∂μ, (fun x => G (t, x)) =ᵐ[ν]
        (fun x i => (V t).val (some i) x)) ∧
      ∀ t, 0 < t → ∀ (v : ℝ → DirichletHilbertSpace (d := d) R hR) v',
        HasDerivAt v v' t → HasDerivAt
          (fun r : ℝ => inner ℝ (SpectralHeat.heatOperator (spectralHeatBasis s)
            s.eigenvalue (fun n => (s.eigenvalue_pos n).le) r.toNNReal f) (J (v r)))
          (-(∫ x in sourceBall (0 : PDE.Vec d) R,
            dot ((α x).mulVec (fun i => (V t).val (some i) x))
              (fun i => (v t).val (some i) x)) +
            inner ℝ (SpectralHeat.heatOperator (spectralHeatBasis s)
              s.eigenvalue (fun n => (s.eigenvalue_pos n).le) t.toNNReal f) (J v')) t := by
  dsimp only
  let J := dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
  let H : ℝ → Lp ℝ 2 (dirichletVolume ρ R) := fun t =>
    SpectralHeat.heatOperator (spectralHeatBasis s) s.eigenvalue
      (fun n => (s.eigenvalue_pos n).le) t.toNNReal f
  obtain ⟨V, G, hJ, hV, hGm, hGl, hslice, hderiv⟩ :=
    c9_native_heat_gradient_product_weakFlow hd hκ hR h s u hb hv f T
  obtain ⟨_, _, B, _, hB⟩ := exists_dirichletHilbert_energyForm hd hκ h R hR
  let A := fun t => (innerSL ℝ (H t)).comp J
  have hH : Continuous H :=
    (SpectralHeat.heatOperator_continuous (spectralHeatBasis s) s.eigenvalue
      (fun n => (s.eigenvalue_pos n).le) f).comp continuous_real_toNNReal
  have hAc : Continuous A := by
    apply Continuous.clm_comp _ continuous_const
    exact (innerSL ℝ).continuous.comp hH
  refine ⟨V, G, hJ, hV, hGm, hGl, hslice, ?_⟩
  intro t ht v v' hv'
  have hweak : ∀ w, HasDerivAt (fun r => A r w) (-(B (V t)) w) t := by
    intro w
    simpa only [A, H, ContinuousLinearMap.comp_apply, innerSL_apply_apply, neg_apply, hB]
      using hderiv t ht w
  have hp := hasDerivAt_weak_functional_apply A v v' t hAc.continuousAt hv'
    (-(B (V t))) hweak
  simpa only [A, H, ContinuousLinearMap.comp_apply, innerSL_apply_apply, neg_apply, hB] using hp

/-- The joint native gradient comes from a lift continuous at every positive time. -/
theorem c9_native_heat_continuous_path_derivative {d : ℕ} (hd : 2 ≤ d)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    {ρ : PDE.Vec d → ℝ} {α : PDE.Vec d → EinsteinRelation.Mat d}
    (h : IsUniformlyElliptic κ ρ α) (s : DirichletSpectralResolution ρ α R)
    (u : ℕ → DirichletHilbertSpace (d := d) R hR)
    (hb : ∀ n, spectralHeatBasis s n = dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (h.2.2 x).2.1) (u n))
    (hv : ∀ n w, (∫ x in sourceBall (0 : PDE.Vec d) R,
      dot ((α x).mulVec (fun i => (u n).val (some i) x))
        (fun i => w.val (some i) x)) = s.eigenvalue n * inner ℝ
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) (u n))
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) w))
    (f : Lp ℝ 2 (dirichletVolume ρ R)) (T : ℝ) :
    let J := dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
    let μ := volume.restrict (Set.Ioo 0 T)
    let ν := volume.restrict ((SubdiffusiveProcess.centeredCube (0 : PDE.Vec d)
      (2 * R) (mul_pos two_pos hR)) : Set (PDE.Vec d))
    ∃ (V : ℝ → DirichletHilbertSpace (d := d) R hR) (G : ℝ × PDE.Vec d → PDE.Vec d),
      (∀ t, 0 < t → J (V t) = SpectralHeat.heatOperator (spectralHeatBasis s)
        s.eigenvalue (fun n => (s.eigenvalue_pos n).le) t.toNNReal f) ∧
      ContinuousOn V (Set.Ioi 0) ∧ MemLp V 2 μ ∧ AEStronglyMeasurable G (μ.prod ν) ∧
      MemLp (fun z => euclideanNorm (G z)) 2 (μ.prod ν) ∧
      (∀ᵐ t ∂μ, (fun x => G (t, x)) =ᵐ[ν]
        (fun x i => (V t).val (some i) x)) ∧
      ∀ t, 0 < t → ∀ (v : ℝ → DirichletHilbertSpace (d := d) R hR) v',
        HasDerivAt v v' t → HasDerivAt
          (fun r : ℝ => inner ℝ (SpectralHeat.heatOperator (spectralHeatBasis s)
            s.eigenvalue (fun n => (s.eigenvalue_pos n).le) r.toNNReal f) (J (v r)))
          (-(∫ x in sourceBall (0 : PDE.Vec d) R,
            dot ((α x).mulVec (fun i => (V t).val (some i) x))
              (fun i => (v t).val (some i) x)) +
            inner ℝ (SpectralHeat.heatOperator (spectralHeatBasis s)
              s.eigenvalue (fun n => (s.eigenvalue_pos n).le) t.toNNReal f) (J v')) t := by
  dsimp only
  obtain ⟨V, G, hJ, hV, hGm, hGl, hslice, hderiv⟩ :=
    c9_native_heat_path_derivative hd hκ hR h s u hb hv f T
  obtain ⟨Q, hQc, hQ⟩ := spectral_heat_native_weakFlow hd hκ h R hR s u hb hv
  refine ⟨V, G, hJ, ?_, hV, hGm, hGl, hslice, hderiv⟩
  rw [continuousOn_iff_continuous_restrict]
  have ht : Continuous (fun t : Set.Ioi (0 : ℝ) =>
      (⟨t.val.toNNReal, Real.toNNReal_pos.mpr t.property⟩ : {t : ℝ≥0 // 0 < t})) :=
    (continuous_real_toNNReal.comp continuous_subtype_val).subtype_mk _
  convert (hQc f).comp ht using 1
  funext t
  apply injective_dirichletHilbertInclusion hκ h R hR
  change dirichletHilbertInclusion ρ R hR κ⁻¹ _ (V t.val) =
    dirichletHilbertInclusion ρ R hR κ⁻¹ _
      (Q t.val.toNNReal (Real.toNNReal_pos.mpr t.property) f)
  rw [hJ t.val t.property]
  exact (congrArg (fun A : _ →L[ℝ] _ => A f)
    (hQ t.val.toNNReal (Real.toNNReal_pos.mpr t.property)).1).symm

/-- Compact native test paths satisfy the integrated heat-flow identity. -/
theorem c9_native_heat_compact_path_test {d : ℕ} (hd : 2 ≤ d)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    {ρ : PDE.Vec d → ℝ} {α : PDE.Vec d → EinsteinRelation.Mat d}
    (h : IsUniformlyElliptic κ ρ α) (s : DirichletSpectralResolution ρ α R)
    (u : ℕ → DirichletHilbertSpace (d := d) R hR)
    (hb : ∀ n, spectralHeatBasis s n = dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (h.2.2 x).2.1) (u n))
    (hv : ∀ n w, (∫ x in sourceBall (0 : PDE.Vec d) R,
      dot ((α x).mulVec (fun i => (u n).val (some i) x))
        (fun i => w.val (some i) x)) = s.eigenvalue n * inner ℝ
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) (u n))
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) w))
    (f : Lp ℝ 2 (dirichletVolume ρ R)) (T a b : ℝ) (ha : 0 < a) (hab : a < b) :
    let J := dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
    let μ := volume.restrict (Set.Ioo 0 T)
    let ν := volume.restrict ((SubdiffusiveProcess.centeredCube (0 : PDE.Vec d)
      (2 * R) (mul_pos two_pos hR)) : Set (PDE.Vec d))
    ∃ (V : ℝ → DirichletHilbertSpace (d := d) R hR) (G : ℝ × PDE.Vec d → PDE.Vec d),
      (∀ t, 0 < t → J (V t) = SpectralHeat.heatOperator (spectralHeatBasis s)
        s.eigenvalue (fun n => (s.eigenvalue_pos n).le) t.toNNReal f) ∧
      ContinuousOn V (Set.Ioi 0) ∧ MemLp V 2 μ ∧ AEStronglyMeasurable G (μ.prod ν) ∧
      MemLp (fun z => euclideanNorm (G z)) 2 (μ.prod ν) ∧
      (∀ᵐ t ∂μ, (fun x => G (t, x)) =ᵐ[ν]
        (fun x i => (V t).val (some i) x)) ∧
      ∀ (v v' : ℝ → DirichletHilbertSpace (d := d) R hR),
        Continuous v → Continuous v' → (∀ t, HasDerivAt v (v' t) t) →
        tsupport v ⊆ Set.Ioo a b →
        (∫ t in Set.Ioo a b, inner ℝ
          (SpectralHeat.heatOperator (spectralHeatBasis s) s.eigenvalue
            (fun n => (s.eigenvalue_pos n).le) t.toNNReal f) (J (v' t))) =
        ∫ t in Set.Ioo a b, ∫ x in sourceBall (0 : PDE.Vec d) R,
          dot ((α x).mulVec (fun i => (V t).val (some i) x))
            (fun i => (v t).val (some i) x) := by
  dsimp only
  let J := dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
  let H : ℝ → Lp ℝ 2 (dirichletVolume ρ R) := fun t =>
    SpectralHeat.heatOperator (spectralHeatBasis s) s.eigenvalue
      (fun n => (s.eigenvalue_pos n).le) t.toNNReal f
  obtain ⟨V, G, hJ, hVc, hV, hGm, hGl, hslice, hderiv⟩ :=
    c9_native_heat_continuous_path_derivative hd hκ hR h s u hb hv f T
  obtain ⟨_, _, B, _, hB⟩ := exists_dirichletHilbert_energyForm hd hκ h R hR
  refine ⟨V, G, hJ, hVc, hV, hGm, hGl, hslice, ?_⟩
  intro v v' hvc hv'c hvd hvs
  let E : ℝ → ℝ := fun t => B (V t) (v t)
  let F : ℝ → ℝ := fun t => inner ℝ (H t) (J (v' t))
  have hpos : Set.uIcc a b ⊆ Set.Ioi (0 : ℝ) := by
    intro t ht
    have ht' : t ∈ Set.Icc a b := by simpa only [Set.uIcc_of_le hab.le] using ht
    exact lt_of_lt_of_le ha ht'.1
  have hEc : ContinuousOn E (Set.uIcc a b) :=
    (B.continuous.comp_continuousOn (hVc.mono hpos)).clm_apply hvc.continuousOn
  have hH : Continuous H :=
    (SpectralHeat.heatOperator_continuous (spectralHeatBasis s) s.eigenvalue
      (fun n => (s.eigenvalue_pos n).le) f).comp continuous_real_toNNReal
  have hFc : Continuous F := hH.inner (J.continuous.comp hv'c)
  have hd' : ∀ t ∈ Set.uIcc a b, HasDerivAt
      (fun r => inner ℝ (H r) (J (v r))) (-E t + F t) t := by
    intro t ht
    simpa only [E, F, H, hB] using hderiv t (hpos ht) v (v' t) (hvd t)
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt hd'
    ((hEc.neg.add hFc.continuousOn).intervalIntegrable)
  have hadd := intervalIntegral.integral_add (μ := volume) (a := a) (b := b)
    (f := -E) (g := F) (hEc.neg.intervalIntegrable) (hFc.intervalIntegrable a b)
  change (∫ t in a..b, -E t + F t) = (∫ t in a..b, -E t) +
    ∫ t in a..b, F t at hadd
  rw [intervalIntegral.integral_neg] at hadd
  have hva : v a = 0 := image_eq_zero_of_notMem_tsupport (fun hm => (hvs hm).1.false)
  have hvb : v b = 0 := image_eq_zero_of_notMem_tsupport (fun hm => (hvs hm).2.false)
  simp only [hva, hvb, map_zero, inner_zero_right, sub_self] at hh
  have heq : (∫ t in a..b, F t) = ∫ t in a..b, E t := by linarith
  simp only [F, E, H, hB, intervalIntegral.integral_of_le hab.le,
    ← Measure.restrict_congr_set Ioo_ae_eq_Ioc] at heq
  exact heq


/-- Smooth spacetime tests satisfy the native heat-flow identity. -/
theorem c9_native_heat_spacetime_test {d : ℕ} (hd : 2 ≤ d)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    {ρ : PDE.Vec d → ℝ} {α : PDE.Vec d → EinsteinRelation.Mat d}
    (h : IsUniformlyElliptic κ ρ α) (s : DirichletSpectralResolution ρ α R)
    (u : ℕ → DirichletHilbertSpace (d := d) R hR)
    (hb : ∀ n, spectralHeatBasis s n = dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (h.2.2 x).2.1) (u n))
    (hv : ∀ n w, (∫ x in sourceBall (0 : PDE.Vec d) R,
      dot ((α x).mulVec (fun i => (u n).val (some i) x))
        (fun i => w.val (some i) x)) = s.eigenvalue n * inner ℝ
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) (u n))
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) w))
    (f : Lp ℝ 2 (dirichletVolume ρ R)) (T a b : ℝ) (ha : 0 < a) (hab : a < b) :
    let J := dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
    let μ := volume.restrict (Set.Ioo 0 T)
    let ν := volume.restrict ((SubdiffusiveProcess.centeredCube (0 : PDE.Vec d)
      (2 * R) (mul_pos two_pos hR)) : Set (PDE.Vec d))
    ∃ (V : ℝ → DirichletHilbertSpace (d := d) R hR) (G : ℝ × PDE.Vec d → PDE.Vec d),
      (∀ t, 0 < t → J (V t) = SpectralHeat.heatOperator (spectralHeatBasis s)
        s.eigenvalue (fun n => (s.eigenvalue_pos n).le) t.toNNReal f) ∧
      ContinuousOn V (Set.Ioi 0) ∧ MemLp V 2 μ ∧ AEStronglyMeasurable G (μ.prod ν) ∧
      MemLp (fun z => euclideanNorm (G z)) 2 (μ.prod ν) ∧
      (∀ᵐ t ∂μ, (fun x => G (t, x)) =ᵐ[ν]
        (fun x i => (V t).val (some i) x)) ∧
      ∀ (ψ : ℝ × PDE.Vec d → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ →
        HasCompactSupport ψ →
        tsupport ψ ⊆ Set.Ioo a b ×ˢ sourceBall (0 : PDE.Vec d) R →
        ∃ (φ φt : ℝ → TestFunction (dirichletBall (d := d) R) ℝ ⊤),
          (∀ t, (φ t : PDE.Vec d → ℝ) = fun x => ψ (t, x)) ∧
          (∀ t, (φt t : PDE.Vec d → ℝ) = fun x => fderiv ℝ ψ (t, x) (1, 0)) ∧
          (∫ t in Set.Ioo a b, inner ℝ
            (SpectralHeat.heatOperator (spectralHeatBasis s) s.eigenvalue
              (fun n => (s.eigenvalue_pos n).le) t.toNNReal f)
            (J (dirichletSmoothElement R hR (φt t)))) =
          ∫ t in Set.Ioo a b, ∫ x in sourceBall (0 : PDE.Vec d) R,
            dot ((α x).mulVec (fun i => (V t).val (some i) x))
              (fun i => (dirichletSmoothElement R hR (φ t)).val (some i) x) := by
  dsimp only
  obtain ⟨V, G, hJ, hVc, hV, hGm, hGl, hslice, htest⟩ :=
    c9_native_heat_compact_path_test hd hκ hR h s u hb hv f T a b ha hab
  refine ⟨V, G, hJ, hVc, hV, hGm, hGl, hslice, ?_⟩
  intro ψ hψ hc hs
  obtain ⟨φ, φt, heq, heqt, hφc, hφtc, hφd, hφs⟩ :=
    spacetime_test_native_c1_paths R hR a b ψ hψ hc hs
  exact ⟨φ, φt, heq, heqt, htest _ _ hφc hφtc hφd hφs⟩


/-- Literal kernel and smooth test derivatives represent the native pairings. -/
theorem c9_native_heat_spacetime_slice_pairings {d : ℕ} (hd : 2 ≤ d)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    {ρ : PDE.Vec d → ℝ} {α : PDE.Vec d → EinsteinRelation.Mat d}
    (h : IsUniformlyElliptic κ ρ α) (s : DirichletSpectralResolution ρ α R)
    (f : Lp ℝ 2 (dirichletVolume ρ R)) (t : ℝ) (ht : 0 < t)
    (ψ : ℝ × PDE.Vec d → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (φ φt : TestFunction (dirichletBall (d := d) R) ℝ ⊤)
    (heq : (φ : PDE.Vec d → ℝ) = fun x => ψ (t, x))
    (heqt : (φt : PDE.Vec d → ℝ) = fun x => fderiv ℝ ψ (t, x) (1, 0))
    (v : DirichletHilbertSpace (d := d) R hR) :
    let J := dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
    inner ℝ (SpectralHeat.heatOperator (spectralHeatBasis s) s.eigenvalue
      (fun n => (s.eigenvalue_pos n).le) t.toNNReal f)
      (J (dirichletSmoothElement R hR φt)) =
      (∫ x in sourceBall (0 : PDE.Vec d) R,
        ρ x * (∫ y, (∑' n, Real.exp (-s.eigenvalue n * t) *
          s.eigenfunction n x * s.eigenfunction n y) * f y ∂dirichletVolume ρ R) *
          fderiv ℝ ψ (t, x) (1, 0)) ∧
    (∫ x in sourceBall (0 : PDE.Vec d) R,
      dot ((α x).mulVec (fun i => v.val (some i) x))
        (fun i => (dirichletSmoothElement R hR φ).val (some i) x)) =
      ∫ x in sourceBall (0 : PDE.Vec d) R,
        dot ((α x).mulVec (fun i => v.val (some i) x))
          (fun i => fderiv ℝ ψ (t, x) (0, Pi.single i 1)) := by
  dsimp only
  constructor
  · apply DimensionLift.dirichletVolume_inner_eq_native hκ h
    · have hk := spectral_heat_operator_ae_kernel_action hd hκ h hR s t.toNNReal
        (by simpa using ht) f
      simpa only [Real.coe_toNNReal t ht.le] using hk
    · filter_upwards [dirichletHilbertInclusion_smooth_coe ρ R hR κ⁻¹
        (fun x _ => (h.2.2 x).2.1) φt] with x hx
      simpa only [heqt] using hx
  · apply integral_congr_ae
    filter_upwards [(spacetime_test_native_slice_representatives R hR ψ hψ t φ heq).2]
      with x hx
    rw [funext hx]


/-- The native heat identity on a positive strip, with literal kernel and test derivatives. -/
theorem c9_native_heat_spacetime_iterated_test {d : ℕ} (hd : 2 ≤ d)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    {ρ : PDE.Vec d → ℝ} {α : PDE.Vec d → EinsteinRelation.Mat d}
    (h : IsUniformlyElliptic κ ρ α) (s : DirichletSpectralResolution ρ α R)
    (u : ℕ → DirichletHilbertSpace (d := d) R hR)
    (hb : ∀ n, spectralHeatBasis s n = dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (h.2.2 x).2.1) (u n))
    (hv : ∀ n w, (∫ x in sourceBall (0 : PDE.Vec d) R,
      dot ((α x).mulVec (fun i => (u n).val (some i) x))
        (fun i => w.val (some i) x)) = s.eigenvalue n * inner ℝ
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) (u n))
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) w))
    (f : Lp ℝ 2 (dirichletVolume ρ R)) (T a b : ℝ) (ha : 0 < a) (hab : a < b) :
    let J := dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
    let μ := volume.restrict (Set.Ioo 0 T)
    let ν := volume.restrict ((SubdiffusiveProcess.centeredCube (0 : PDE.Vec d)
      (2 * R) (mul_pos two_pos hR)) : Set (PDE.Vec d))
    ∃ (V : ℝ → DirichletHilbertSpace (d := d) R hR) (G : ℝ × PDE.Vec d → PDE.Vec d),
      (∀ t, 0 < t → J (V t) = SpectralHeat.heatOperator (spectralHeatBasis s)
        s.eigenvalue (fun n => (s.eigenvalue_pos n).le) t.toNNReal f) ∧
      ContinuousOn V (Set.Ioi 0) ∧ MemLp V 2 μ ∧ AEStronglyMeasurable G (μ.prod ν) ∧
      MemLp (fun z => euclideanNorm (G z)) 2 (μ.prod ν) ∧
      (∀ᵐ t ∂μ, (fun x => G (t, x)) =ᵐ[ν]
        (fun x i => (V t).val (some i) x)) ∧
      ∀ (ψ : ℝ × PDE.Vec d → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ →
        HasCompactSupport ψ →
        tsupport ψ ⊆ Set.Ioo a b ×ˢ sourceBall (0 : PDE.Vec d) R →
        (∫ t in Set.Ioo a b, ∫ x in sourceBall (0 : PDE.Vec d) R,
          ρ x * (∫ y, (∑' n, Real.exp (-s.eigenvalue n * t) *
            s.eigenfunction n x * s.eigenfunction n y) * f y ∂dirichletVolume ρ R) *
            fderiv ℝ ψ (t, x) (1, 0)) =
        ∫ t in Set.Ioo a b, ∫ x in sourceBall (0 : PDE.Vec d) R,
          dot ((α x).mulVec (fun i => (V t).val (some i) x))
            (fun i => fderiv ℝ ψ (t, x) (0, Pi.single i 1)) := by
  dsimp only
  obtain ⟨V, G, hJ, hVc, hV, hGm, hGl, hslice, htest⟩ :=
    c9_native_heat_spacetime_test hd hκ hR h s u hb hv f T a b ha hab
  refine ⟨V, G, hJ, hVc, hV, hGm, hGl, hslice, ?_⟩
  intro ψ hψ hc hs
  obtain ⟨φ, φt, heq, heqt, hid⟩ := htest ψ hψ hc hs
  have hpair := fun t (ht : t ∈ Set.Ioo a b) =>
    c9_native_heat_spacetime_slice_pairings hd hκ hR h s f t (ha.trans ht.1)
      ψ hψ (φ t) (φt t) (heq t) (heqt t) (V t)
  have hl : (∫ t in Set.Ioo a b, inner ℝ
      (SpectralHeat.heatOperator (spectralHeatBasis s) s.eigenvalue
        (fun n => (s.eigenvalue_pos n).le) t.toNNReal f)
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
        (dirichletSmoothElement R hR (φt t)))) =
      ∫ t in Set.Ioo a b, ∫ x in sourceBall (0 : PDE.Vec d) R,
        ρ x * (∫ y, (∑' n, Real.exp (-s.eigenvalue n * t) *
          s.eigenfunction n x * s.eigenfunction n y) * f y ∂dirichletVolume ρ R) *
          fderiv ℝ ψ (t, x) (1, 0) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact (hpair t ht).1
  have hr : (∫ t in Set.Ioo a b, ∫ x in sourceBall (0 : PDE.Vec d) R,
      dot ((α x).mulVec (fun i => (V t).val (some i) x))
        (fun i => (dirichletSmoothElement R hR (φ t)).val (some i) x)) =
      ∫ t in Set.Ioo a b, ∫ x in sourceBall (0 : PDE.Vec d) R,
        dot ((α x).mulVec (fun i => (V t).val (some i) x))
          (fun i => fderiv ℝ ψ (t, x) (0, Pi.single i 1)) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact (hpair t ht).2
  exact hl.symm.trans (hid.trans hr)

/-- The actual spectral kernel, masked outside positive times and the two
Dirichlet balls, is jointly measurable. -/
theorem c9_native_spectral_kernel_masked_measurable {d : ℕ} (hd : 2 ≤ d)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    {ρ : PDE.Vec d → ℝ} {α : PDE.Vec d → EinsteinRelation.Mat d}
    (h : IsUniformlyElliptic κ ρ α) (s : DirichletSpectralResolution ρ α R)
    (hs : Tendsto s.eigenvalue atTop atTop) :
    Measurable ((Set.Ioi 0 ×ˢ sourceBall (0 : PDE.Vec d) R ×ˢ
      sourceBall (0 : PDE.Vec d) R).indicator
      (fun z : ℝ × PDE.Vec d × PDE.Vec d => ∑' n,
        Real.exp (-s.eigenvalue n * z.1) * s.eigenfunction n z.2.1 *
          s.eigenfunction n z.2.2)) := by
  classical
  have hB : MeasurableSet (sourceBall (0 : PDE.Vec d) R) :=
    (dirichletBall (d := d) R).isOpen.measurableSet
  have hm : MeasurableSet {z : ℝ × PDE.Vec d × PDE.Vec d |
      0 < z.1 ∧ z.2.1 ∈ sourceBall 0 R ∧ z.2.2 ∈ sourceBall 0 R} :=
    measurableSet_Ioi.prod (hB.prod hB)
  have hc := ContinuousOn.measurable_piecewise
    (spectral_heat_continuousOn hd hκ h hR s hs)
    (continuousOn_const : ContinuousOn (fun _ : ℝ × PDE.Vec d × PDE.Vec d => (0 : ℝ)) _)
    hm
  convert hc using 1
  ext z
  simp only [Set.indicator_apply, Set.piecewise, Set.mem_prod, Set.mem_Ioi,
    Set.mem_ofPred_eq]

/-- The literal native kernel action is jointly measurable on the positive
space-time cylinder. -/
theorem c9_native_kernel_action_spacetime_measurable {d : ℕ} (hd : 2 ≤ d)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    {ρ : PDE.Vec d → ℝ} {α : PDE.Vec d → EinsteinRelation.Mat d}
    (h : IsUniformlyElliptic κ ρ α) (s : DirichletSpectralResolution ρ α R)
    (hs : Tendsto s.eigenvalue atTop atTop) (f : Lp ℝ 2 (dirichletVolume ρ R)) :
    AEStronglyMeasurable (fun z : ℝ × PDE.Vec d => ∫ y,
      (∑' n, Real.exp (-s.eigenvalue n * z.1) * s.eigenfunction n z.2 *
        s.eigenfunction n y) * f y ∂dirichletVolume ρ R)
      (volume.restrict (Set.Ioi 0 ×ˢ sourceBall 0 R)) := by
  let μ := volume.restrict (Set.Ioi (0 : ℝ) ×ˢ sourceBall (0 : PDE.Vec d) R)
  let ν := dirichletVolume ρ R
  letI : IsFiniteMeasure ν :=
    dirichletVolume_isFinite ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
  let S := Set.Ioi (0 : ℝ) ×ˢ sourceBall (0 : PDE.Vec d) R ×ˢ sourceBall (0 : PDE.Vec d) R
  let H : ℝ × PDE.Vec d × PDE.Vec d → ℝ := fun z => ∑' n,
    Real.exp (-s.eigenvalue n * z.1) * s.eigenfunction n z.2.1 * s.eigenfunction n z.2.2
  have hB : MeasurableSet (sourceBall (0 : PDE.Vec d) R) :=
    (dirichletBall (d := d) R).isOpen.measurableSet
  have hk : Measurable (fun z : (ℝ × PDE.Vec d) × PDE.Vec d =>
      S.indicator H (z.1.1, z.1.2, z.2)) :=
    (c9_native_spectral_kernel_masked_measurable hd hκ hR h s hs).comp
      (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))
  have hi : AEStronglyMeasurable (fun z : (ℝ × PDE.Vec d) × PDE.Vec d =>
      S.indicator H (z.1.1, z.1.2, z.2) * f z.2) (μ.prod ν) :=
    hk.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f).comp_snd
  apply hi.integral_prod_right'.congr
  filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod hB)] with z hz
  apply integral_congr_ae
  filter_upwards [(withDensity_absolutelyContinuous _ _).ae_le
    (ae_restrict_mem hB)] with y hy
  simp only [S, H, Set.indicator_of_mem, Set.mem_prod, Set.mem_Ioi, hz.1, hz.2, hy,
    and_self]

/-- Almost-everywhere slice equality lifts to the product when both functions
have product-measurable representatives. -/
theorem c9_ae_eq_prod_of_ae_eq_slices {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SFinite ν]
    (f g : X × Y → ℝ) (hf : AEStronglyMeasurable f (μ.prod ν))
    (hg : AEStronglyMeasurable g (μ.prod ν))
    (hfg : ∀ᵐ x ∂μ, (fun y => f (x, y)) =ᵐ[ν] (fun y => g (x, y))) :
    f =ᵐ[μ.prod ν] g := by
  have hfs := Measure.ae_ae_of_ae_prod hf.ae_eq_mk
  have hgs := Measure.ae_ae_of_ae_prod hg.ae_eq_mk
  have hmk : hf.mk f =ᵐ[μ.prod ν] hg.mk g := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun
      hf.stronglyMeasurable_mk.measurable hg.stronglyMeasurable_mk.measurable)).2
    filter_upwards [hfs, hgs, hfg] with x hfx hgx heq
    filter_upwards [hfx, hgx, heq] with y hyf hyg hye
    exact hyf.symm.trans (hye.trans hyg)
  exact hf.ae_eq_mk.trans (hmk.trans hg.ae_eq_mk.symm)

/-- The literal kernel action has a joint L² representative on the positive
Dirichlet cylinder. -/
theorem c9_native_kernel_action_memLp {d : ℕ} (hd : 2 ≤ d)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    {ρ : PDE.Vec d → ℝ} {α : PDE.Vec d → EinsteinRelation.Mat d}
    (h : IsUniformlyElliptic κ ρ α) (s : DirichletSpectralResolution ρ α R)
    (u : ℕ → DirichletHilbertSpace (d := d) R hR)
    (hs : Tendsto s.eigenvalue atTop atTop)
    (hb : ∀ n, spectralHeatBasis s n = dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (h.2.2 x).2.1) (u n))
    (hv : ∀ n w, (∫ x in sourceBall (0 : PDE.Vec d) R,
      dot ((α x).mulVec (fun i => (u n).val (some i) x))
        (fun i => w.val (some i) x)) = s.eigenvalue n * inner ℝ
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) (u n))
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) w))
    (f : Lp ℝ 2 (dirichletVolume ρ R)) (T : ℝ) :
    MemLp (fun z : ℝ × PDE.Vec d => ∫ y,
      (∑' n, Real.exp (-s.eigenvalue n * z.1) * s.eigenfunction n z.2 *
        s.eigenfunction n y) * f y ∂dirichletVolume ρ R) 2
      (volume.restrict (Set.Ioo 0 T ×ˢ sourceBall 0 R)) := by
  let μ := volume.restrict (Set.Ioo (0 : ℝ) T)
  let ν := volume.restrict (sourceBall (0 : PDE.Vec d) R)
  let η := volume.restrict ((SubdiffusiveProcess.centeredCube (0 : PDE.Vec d)
    (2 * R) (mul_pos two_pos hR)) : Set (PDE.Vec d))
  let F : ℝ × PDE.Vec d → ℝ := fun z => ∫ y,
    (∑' n, Real.exp (-s.eigenvalue n * z.1) * s.eigenfunction n z.2 *
      s.eigenfunction n y) * f y ∂dirichletVolume ρ R
  have hν : ν ≤ η := Measure.restrict_mono_set volume (sourceBall_subset_cube R hR)
  have hprod : μ.prod ν ≤ μ.prod η := Measure.prod_mono le_rfl hν
  obtain ⟨V, G, U, hJ, hV, hGm, hGl, hslice, hderiv, hU, hUF⟩ :=
    c9_native_heat_spacetime_kernel_slices hd hκ hR h s u hb hv f T
  have hmeas : AEStronglyMeasurable F (μ.prod ν) := by
    apply (c9_native_kernel_action_spacetime_measurable hd hκ hR h s hs f).mono_measure
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
    exact Measure.prod_mono (Measure.restrict_mono_set volume (Set.Ioo_subset_Ioi_self)) le_rfl
  have heq : (fun z => U z) =ᵐ[μ.prod ν] F :=
    c9_ae_eq_prod_of_ae_eq_slices μ ν _ _
      ((Lp.aestronglyMeasurable U).mono_measure hprod) hmeas hUF
  have hmem : MemLp F 2 (μ.prod ν) :=
    MemLp.congr_norm ((Lp.memLp U).mono_measure hprod) hmeas
      (heq.mono fun _ hz => congrArg norm hz)
  simpa only [μ, ν, Measure.prod_restrict, ← Measure.volume_eq_prod] using hmem

/-- One native lift and gradient work for every positive test strip. -/
theorem c9_native_heat_all_strips_iterated_test {d : ℕ} (hd : 2 ≤ d)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    {ρ : PDE.Vec d → ℝ} {α : PDE.Vec d → EinsteinRelation.Mat d}
    (h : IsUniformlyElliptic κ ρ α) (s : DirichletSpectralResolution ρ α R)
    (u : ℕ → DirichletHilbertSpace (d := d) R hR)
    (hb : ∀ n, spectralHeatBasis s n = dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (h.2.2 x).2.1) (u n))
    (hv : ∀ n w, (∫ x in sourceBall (0 : PDE.Vec d) R,
      dot ((α x).mulVec (fun i => (u n).val (some i) x))
        (fun i => w.val (some i) x)) = s.eigenvalue n * inner ℝ
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) (u n))
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) w))
    (f : Lp ℝ 2 (dirichletVolume ρ R)) (T : ℝ) :
    let J := dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
    let μ := volume.restrict (Set.Ioo 0 T)
    let ν := volume.restrict ((SubdiffusiveProcess.centeredCube (0 : PDE.Vec d)
      (2 * R) (mul_pos two_pos hR)) : Set (PDE.Vec d))
    ∃ (V : ℝ → DirichletHilbertSpace (d := d) R hR) (G : ℝ × PDE.Vec d → PDE.Vec d),
      (∀ t, 0 < t → J (V t) = SpectralHeat.heatOperator (spectralHeatBasis s)
        s.eigenvalue (fun n => (s.eigenvalue_pos n).le) t.toNNReal f) ∧
      ContinuousOn V (Set.Ioi 0) ∧ MemLp V 2 μ ∧ AEStronglyMeasurable G (μ.prod ν) ∧
      MemLp (fun z => euclideanNorm (G z)) 2 (μ.prod ν) ∧
      (∀ᵐ t ∂μ, (fun x => G (t, x)) =ᵐ[ν]
        (fun x i => (V t).val (some i) x)) ∧
      ∀ (a b : ℝ), 0 < a → a < b → b ≤ T →
      ∀ (ψ : ℝ × PDE.Vec d → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ →
        HasCompactSupport ψ →
        tsupport ψ ⊆ Set.Ioo a b ×ˢ sourceBall (0 : PDE.Vec d) R →
        (∫ t in Set.Ioo a b, ∫ x in sourceBall (0 : PDE.Vec d) R,
          ρ x * (∫ y, (∑' n, Real.exp (-s.eigenvalue n * t) *
            s.eigenfunction n x * s.eigenfunction n y) * f y ∂dirichletVolume ρ R) *
            fderiv ℝ ψ (t, x) (1, 0)) =
        ∫ t in Set.Ioo a b, ∫ x in sourceBall (0 : PDE.Vec d) R,
          dot ((α x).mulVec (G (t, x)))
            (fun i => fderiv ℝ ψ (t, x) (0, Pi.single i 1)) := by
  dsimp only
  obtain ⟨V, G, hJ, hVc, hV, hGm, hGl, hslice, _⟩ :=
    c9_native_heat_spacetime_iterated_test hd hκ hR h s u hb hv f T 1 2 (by norm_num) (by norm_num)
  refine ⟨V, G, hJ, hVc, hV, hGm, hGl, hslice, ?_⟩
  intro a b ha hab hbT ψ hψ hc hs
  obtain ⟨W, _, hW, _, _, _, _, _, htest⟩ :=
    c9_native_heat_spacetime_iterated_test hd hκ hR h s u hb hv f T a b ha hab
  have heq : ∀ t, 0 < t → W t = V t := by
    intro t ht
    apply injective_dirichletHilbertInclusion hκ h R hR
    exact (hW t ht).trans (hJ t ht).symm
  calc
    _ = ∫ t in Set.Ioo a b, ∫ x in sourceBall (0 : PDE.Vec d) R,
          dot ((α x).mulVec (fun i => (W t).val (some i) x))
            (fun i => fderiv ℝ ψ (t, x) (0, Pi.single i 1)) := htest ψ hψ hc hs
    _ = _ := by
      apply integral_congr_ae
      have hsub : Set.Ioo a b ⊆ Set.Ioo 0 T := fun t ht =>
        ⟨ha.trans ht.1, ht.2.trans_le hbT⟩
      have hslice' := hslice.filter_mono
        (Measure.absolutelyContinuous_of_le (Measure.restrict_mono_set volume hsub)).ae_le
      filter_upwards [ae_restrict_mem measurableSet_Ioo, hslice'] with t ht hGt
      rw [heq t (ha.trans ht.1)]
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae_restrict_of_subset (sourceBall_subset_cube R hR) hGt] with x hx
      rw [hx]

/-- A compactly supported cylinder test fits in one strictly positive time strip. -/
theorem c9_compact_test_positive_strip {d : ℕ} {T : ℝ} (hT : 0 < T)
    {U : Set (PDE.Vec d)} (ψ : ℝ × PDE.Vec d → ℝ)
    (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ Set.Ioo 0 T ×ˢ U) :
    ∃ a b : ℝ, 0 < a ∧ a < b ∧ b ≤ T ∧
      tsupport ψ ⊆ Set.Ioo a b ×ˢ U := by
  by_cases hn : (tsupport ψ).Nonempty
  · obtain ⟨z₁, hz₁, hmin⟩ := hc.exists_isMinOn hn continuous_fst.continuousOn
    obtain ⟨z₂, hz₂, hmax⟩ := hc.exists_isMaxOn hn continuous_fst.continuousOn
    have h₁ : 0 < z₁.1 := (hs hz₁).1.1
    have h₂ : z₂.1 < T := (hs hz₂).1.2
    have horder : z₁.1 ≤ z₂.1 := hmin hz₂
    refine ⟨z₁.1 / 2, (z₂.1 + T) / 2, by linarith, by linarith,
      by linarith, ?_⟩
    intro z hz
    have hlow : z₁.1 ≤ z.1 := hmin hz
    have hhigh : z.1 ≤ z₂.1 := hmax hz
    exact ⟨⟨by linarith, by linarith⟩, (hs hz).2⟩
  · refine ⟨T / 3, 2 * T / 3, by linarith, by linarith, by linarith, ?_⟩
    intro z hz
    exact (hn ⟨z, hz⟩).elim

/-- L² fields and ellipticity make both spacetime test pairings integrable. -/
theorem c9_weighted_pairings_integrable {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    {ρ : PDE.Vec d → ℝ} {α : PDE.Vec d → EinsteinRelation.Mat d}
    (h : IsUniformlyElliptic κ ρ α) (I : Set ℝ) (U : Set (PDE.Vec d))
    (u : ℝ × PDE.Vec d → ℝ) (G : ℝ × PDE.Vec d → PDE.Vec d)
    (hu : MemLp u 2 (volume.restrict (I ×ˢ U)))
    (hGm : AEStronglyMeasurable G (volume.restrict (I ×ˢ U)))
    (hG : MemLp (fun z => euclideanNorm (G z)) 2 (volume.restrict (I ×ˢ U)))
    (ψ : ℝ × PDE.Vec d → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hc : HasCompactSupport ψ) :
    Integrable (fun z => (ρ z.2 * u z) * fderiv ℝ ψ z (1, 0))
      (volume.restrict (I ×ˢ U)) ∧
    Integrable (fun z => dot ((α z.2).mulVec (G z))
      (fun i => fderiv ℝ ψ z (0, unitVector i))) (volume.restrict (I ×ˢ U)) := by
  let μ := (volume : Measure (ℝ × PDE.Vec d)).restrict (I ×ˢ U)
  obtain ⟨hρ, hα⟩ := DimensionLift.uniformlyElliptic_coefficients_memLp_top hκ h (Measure.map Prod.snd μ)
  have hρ' : MemLp (fun z : ℝ × PDE.Vec d => ρ z.2) ∞ μ :=
    hρ.comp_of_map measurable_snd.aemeasurable
  have hα' (i j : Fin d) : MemLp (fun z : ℝ × PDE.Vec d => α z.2 i j) ∞ μ :=
    (hα i j).comp_of_map measurable_snd.aemeasurable
  have hvec : MemLp G 2 μ := by
    apply hG.mono' hGm
    exact Filter.Eventually.of_forall (fun z => by
      apply pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _) |>.mpr
      intro i
      change |G z i| ≤ euclideanNorm (G z)
      have hi := PiLp.norm_apply_le
        (WithLp.toLp 2 (G z) : EuclideanSpace ℝ (Fin d)) i
      simpa only [PiLp.toLp_apply, Real.norm_eq_abs, ← TimeChange.euclideanNorm_eq_norm_toLp] using hi)
  have hg : ∀ i, MemLp (fun z => G z i) 2 μ := memLp_pi_iff.mp hvec
  have hf (i : Fin d) : MemLp (fun z => ((α z.2).mulVec (G z)) i) 2 μ := by
    simpa only [Matrix.mulVec, dotProduct, Pi.mul_apply] using
      memLp_finsetSum Finset.univ (fun j _ => (hα' i j).mul (hg j))
  have hder (v : ℝ × PDE.Vec d) : MemLp (fun z => fderiv ℝ ψ z v) 2 μ := by
    have hv : MemLp (fun z => fderiv ℝ ψ z v) 2 volume :=
      ((hψ.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
        (hc.fderiv_apply ℝ v)
    exact hv.mono_measure Measure.restrict_le_self
  have hmass : MemLp (fun z => ρ z.2 * u z) 2 μ := hρ'.mul hu
  refine ⟨hmass.integrable_mul (hder (1, 0)), ?_⟩
  change Integrable (fun z => ∑ i : Fin d, ((α z.2).mulVec (G z)) i *
    fderiv ℝ ψ z (0, unitVector i)) μ
  exact integrable_finsetSum Finset.univ (fun i _ => (hf i).integrable_mul (hder (0, unitVector i)))

end EinsteinFull.Calculus
