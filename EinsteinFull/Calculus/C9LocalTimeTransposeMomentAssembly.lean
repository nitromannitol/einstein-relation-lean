import EinsteinFull.Calculus.C10TransposeDerivativeCylinderAbsorption
import EinsteinFull.Calculus.C10LocalTimeTransposeCylinderAverage

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinFull

/-- The actual transpose derivative at the terminal time is bounded by a
normalized original-orbit cylinder. The constant precedes the law and data. -/
theorem local_time_transpose_derivative_terminal_cylinder_average
    (d : ℕ) [Fact (2 ≤ d)] (Λ₀ : ℝ) (hΛ : 1 ≤ Λ₀) :
    ∃ C : ℝ, 0 < C ∧
    ∀ {r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
      {P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)},
      IsComplexEnvironmentSemigroup Q i ζ P → IsComplexTransposeSemigroup Q P T →
    ∀ {f g : Lp ℂ 2 (reducedLaw Q)}, IsComplexTransposeGeneratorPair Q i ζ f g →
    ∃ W : ℝ × FieldPair d → ℂ, Measurable W ∧
      (∀ s, (fun ω => W (s, ω)) =ᵐ[reducedLaw Q] T s.toNNReal f) ∧
    ∀ (t : ℝ≥0), 0 < (t : ℝ) → ∀ (ρ : ℝ) (z : Vec d),
      Real.sqrt (t : ℝ) ≤ ρ → ∀ᵐ ω ∂reducedLaw Q,
        (⨍ x in {x | euclideanNorm (x - z) ≤ ρ}, ‖(T t g) (translate x ω)‖ ^ 2) ≤
          C * (1 + ‖ζ‖ * Real.sqrt (t : ℝ)) ^ 6 / (t : ℝ) ^ 2 *
            (⨍ s in Icc ((t : ℝ) / 4) (t : ℝ),
              ⨍ x in {x | euclideanNorm (x - z) ≤ 4 * ρ},
                ‖W (s, translate x ω)‖ ^ 2) := by
  obtain ⟨E, hE, hcyl⟩ := C10.local_time_transpose_conditional_derivative_cylinder_absorption d Λ₀ hΛ
  obtain ⟨J, hJ, htrace⟩ := local_time_transpose_terminal_cylinder_average d Λ₀ hΛ
  refine ⟨J * E * (3 / 2) * (2 : ℝ) ^ d, by positivity, ?_⟩
  intro r₀ Q i ζ P T hP hT f g hfg
  obtain ⟨W, hW, heW⟩ := EinsteinFull.StronglyMeasurable.exists_joint_l2_representative
    (((hT.continuous_apply hP f).comp continuous_real_toNNReal).stronglyMeasurable)
  obtain ⟨V, hV, heV, hterminal⟩ := htrace r₀ Q i ζ P T hP hT g
  refine ⟨W, hW, heW, ?_⟩
  intro t ht ρ z hρ
  have hr : 0 < ρ := (Real.sqrt_pos.mpr ht).trans_le hρ
  have htρ : (t : ℝ) ≤ ρ ^ 2 := by
    have hs := (sq_le_sq₀ (Real.sqrt_nonneg (t : ℝ)) hr.le).2 hρ
    rwa [Real.sq_sqrt ht.le] at hs
  let μ := reducedLaw Q
  let : IsProbabilityMeasure μ := reducedLaw_probability Q
  let S := {x : Vec d | euclideanNorm (x - z) ≤ 2 * ρ}
  let U := {x : Vec d | euclideanNorm (x - z) ≤ 4 * ρ}
  let : IsFiniteMeasure (volume.restrict S) := ⟨by
    simpa only [Measure.restrict_apply_univ] using
      (isCompact_physical_euclidean_closedBall z (2 * ρ)).measure_lt_top (μ := volume)⟩
  let : IsFiniteMeasure (volume.restrict U) := ⟨by
    simpa only [Measure.restrict_apply_univ] using
      (isCompact_physical_euclidean_closedBall z (4 * ρ)).measure_lt_top (μ := volume)⟩
  have hi (v : Lp ℂ 2 μ) (a : ℝ) : Integrable (fun s : ℝ => ‖T s.toNNReal v‖ ^ 2)
      (volume.restrict (Icc a (t : ℝ))) :=
    (((hT.continuous_apply hP v).comp continuous_real_toNNReal).norm.pow 2).continuousOn.integrableOn_compact
      isCompact_Icc
  have hWF := local_time_transpose_conditional_cylinder_fubini μ (reducedLaw_stationary Q)
    (volume.restrict (Icc ((t : ℝ) / 4) (t : ℝ))) (volume.restrict U)
    (hi f ((t : ℝ) / 4)) hW heW
  have hVF := local_time_transpose_conditional_cylinder_fubini μ (reducedLaw_stationary Q)
    (volume.restrict (Icc ((t : ℝ) / 2) (t : ℝ))) (volume.restrict S)
    (hi g ((t : ℝ) / 2)) hV heV
  have hc : ∀ᵐ ω ∂μ,
      (∫ s in Icc ((t : ℝ) / 2) (t : ℝ), ∫ x in S, ‖V (s, translate x ω)‖ ^ 2) ≤
        E * (1 + ‖ζ‖ * Real.sqrt (t : ℝ)) ^ 4 / (t : ℝ) ^ 2 *
          (∫ s in Icc ((t : ℝ) / 4) (t : ℝ), ∫ x in U, ‖W (s, translate x ω)‖ ^ 2) := by
    apply ae_le_of_forall_setIntegral_le hVF.1 (hWF.1.const_mul _)
    intro A _ _
    rw [integral_const_mul, hVF.2.2 A, hWF.2.2 A]
    simpa only [S, U, show 2 * (2 * ρ) = 4 * ρ by ring] using
      hcyl hP hT hfg (t : ℝ) ht (2 * ρ) (by linarith) z A
  have hball (a : ℝ) (ha : 0 < a) :
      {x : Vec d | euclideanNorm (x - z) ≤ a} = PDE.euclideanClosedBall z a := by
    ext x
    change Real.sqrt (euclideanSq (x - z)) ≤ a ↔ PDE.vecNormSq (x - z) ≤ a ^ 2
    rw [Real.sqrt_le_iff]
    exact and_iff_right ha.le
  have hvol (a : ℝ) (ha : 0 < a) :
      volume.real {x : Vec d | euclideanNorm (x - z) ≤ a} =
        a ^ d * (volume (PDE.euclideanClosedBall (0 : Vec d) 1)).toReal := by
    rw [hball a ha, PDE.euclideanClosedBall_eq_translateSet_smul_unit_of_pos z ha,
      MeasureTheory.measureReal_def, PDE.volume_translateSet_eq,
      PDE.volume_smul_set_toReal_of_pos ha]
  let v := volume.real {x : Vec d | euclideanNorm (x - z) ≤ 2 * ρ}
  have hv : 0 < v := by
    apply ENNReal.toReal_pos _ (isCompact_physical_euclidean_closedBall z (2 * ρ)).measure_ne_top
    apply ne_of_gt
    exact (PDE.volume_euclideanBall_pos z (by positivity : 0 < 2 * ρ)).trans_le
      (measure_mono (by
        rw [hball (2 * ρ) (by positivity)]
        exact PDE.euclideanBall_subset_euclideanClosedBall z (2 * ρ)))
  have hv4 : volume.real {x : Vec d | euclideanNorm (x - z) ≤ 4 * ρ} = (2 : ℝ) ^ d * v := by
    dsimp [v]
    rw [hvol (4 * ρ) (by positivity), hvol (2 * ρ) (by positivity)]
    have hp : (4 * ρ) ^ d = (2 : ℝ) ^ d * (2 * ρ) ^ d := by
      rw [← mul_pow]; congr 1; ring
    rw [hp]; ring
  have htime (a : ℝ) (ha : a ≤ (t : ℝ)) :
      volume.real (Icc a (t : ℝ)) = (t : ℝ) - a := by
    rw [Real.volume_real_Icc, max_eq_left (sub_nonneg.mpr ha)]
  have hi : volume.real (Icc ((t : ℝ) / 2) (t : ℝ)) = (t : ℝ) / 2 := by
    rw [htime _ (by linarith)]; ring
  have ho : volume.real (Icc ((t : ℝ) / 4) (t : ℝ)) = 3 * (t : ℝ) / 4 := by
    rw [htime _ (by linarith)]; ring
  filter_upwards [hc, hterminal t ht ρ z hρ] with ω hcy hterm
  let MW := ∫ s in Icc ((t : ℝ) / 4) (t : ℝ),
    ∫ x in {x | euclideanNorm (x - z) ≤ 4 * ρ}, ‖W (s, translate x ω)‖ ^ 2
  let MV := ∫ s in Icc ((t : ℝ) / 2) (t : ℝ),
    ∫ x in {x | euclideanNorm (x - z) ≤ 2 * ρ}, ‖V (s, translate x ω)‖ ^ 2
  have hMW : 0 ≤ MW := integral_nonneg fun _ => integral_nonneg fun _ => sq_nonneg _
  have hder : MV ≤ E * (1 + ‖ζ‖ * Real.sqrt (t : ℝ)) ^ 4 / (t : ℝ) ^ 2 * MW :=
    hcy
  have hnorm : (⨍ s in Icc ((t : ℝ) / 2) (t : ℝ),
      ⨍ x in {x | euclideanNorm (x - z) ≤ 2 * ρ}, ‖V (s, translate x ω)‖ ^ 2) =
      ((t : ℝ) / 2)⁻¹ * v⁻¹ * MV := by
    simp only [average_eq, measureReal_restrict_apply_univ, smul_eq_mul, integral_const_mul, hi]
    dsimp [MV, v]; ring
  have hout : (⨍ s in Icc ((t : ℝ) / 4) (t : ℝ),
      ⨍ x in {x | euclideanNorm (x - z) ≤ 4 * ρ}, ‖W (s, translate x ω)‖ ^ 2) =
      (3 * (t : ℝ) / 4)⁻¹ * ((2 : ℝ) ^ d * v)⁻¹ * MW := by
    simp only [average_eq, measureReal_restrict_apply_univ, smul_eq_mul, integral_const_mul, ho, hv4]
    dsimp [MW]; ring
  rw [hnorm] at hterm
  calc
    _ ≤ J * (1 + ‖ζ‖ * Real.sqrt (t : ℝ)) ^ 2 * (((t : ℝ) / 2)⁻¹ * v⁻¹ * MV) := hterm
    _ ≤ J * (1 + ‖ζ‖ * Real.sqrt (t : ℝ)) ^ 2 *
        (((t : ℝ) / 2)⁻¹ * v⁻¹ *
          (E * (1 + ‖ζ‖ * Real.sqrt (t : ℝ)) ^ 4 / (t : ℝ) ^ 2 * MW)) := by gcongr
    _ = (J * E * (3 / 2) * (2 : ℝ) ^ d) *
        (1 + ‖ζ‖ * Real.sqrt (t : ℝ)) ^ 6 / (t : ℝ) ^ 2 *
          ((3 * (t : ℝ) / 4)⁻¹ * ((2 : ℝ) ^ d * v)⁻¹ * MW) := by
      field_simp; ring
    _ = _ := by rw [hout]

/-- Comparing open and closed physical windows needs only a dimension cost. -/
private theorem c9_open_closed_average_le {d : ℕ} (z : Vec d) {ρ : ℝ}
    (hρ : 0 < ρ) {f : Vec d → ℝ}
    (hi : IntegrableOn f {x | euclideanNorm (x - z) ≤ ρ} volume)
    (hf : ∀ x, 0 ≤ f x) :
    (⨍ x in {x | euclideanNorm (x - z) < ρ}, f x) ≤
      (2 : ℝ) ^ d * (⨍ x in {x | euclideanNorm (x - z) ≤ ρ}, f x) := by
  have hv := localSpatialEnergy_window_volume z ρ hρ
  have hfinite := (isCompact_physical_euclidean_closedBall z ρ).measure_ne_top (μ := volume)
  have hsub : {x : Vec d | euclideanNorm (x - z) < ρ} ⊆
      {x | euclideanNorm (x - z) ≤ ρ} := fun _ (hx : euclideanNorm (_ - z) < ρ) => hx.le
  have hvc : 0 < volume.real {x : Vec d | euclideanNorm (x - z) ≤ ρ} :=
    hv.trans_le (measureReal_mono hsub hfinite)
  have hsub2 : {x : Vec d | euclideanNorm (x - z) ≤ ρ} ⊆
      {x | euclideanNorm (x - z) < 2 * ρ} :=
    fun x (hx : euclideanNorm (x - z) ≤ ρ) => lt_of_le_of_lt hx (by linarith)
  have hfinite2 : volume {x : Vec d | euclideanNorm (x - z) < 2 * ρ} ≠ ⊤ :=
    ne_of_lt ((measure_mono (show {x : Vec d | euclideanNorm (x - z) < 2 * ρ} ⊆
      {x | euclideanNorm (x - z) ≤ 2 * ρ} from
        fun x (hx : euclideanNorm (x - z) < 2 * ρ) => hx.le)).trans_lt
      (isCompact_physical_euclidean_closedBall z (2 * ρ)).measure_lt_top)
  have hvc2 := measureReal_mono hsub2 hfinite2
  rw [local_time_window_volume_dilation z hρ (by norm_num : (0 : ℝ) < 2)] at hvc2
  have hcoeff : (volume.real {x : Vec d | euclideanNorm (x - z) < ρ})⁻¹ ≤
      (2 : ℝ) ^ d * (volume.real {x : Vec d | euclideanNorm (x - z) ≤ ρ})⁻¹ := by
    rw [← one_div, ← div_eq_mul_inv]
    exact (div_le_div_iff₀ hv hvc).2 (by simpa using hvc2)
  have hint := setIntegral_mono_set hi (ae_of_all _ hf)
    (ae_of_all _ fun _ hx => hsub hx)
  simp only [average_eq, measureReal_restrict_apply_univ, smul_eq_mul]
  calc
    _ ≤ (volume.real {x : Vec d | euclideanNorm (x - z) < ρ})⁻¹ *
        (∫ x in {x | euclideanNorm (x - z) ≤ ρ}, f x) :=
      mul_le_mul_of_nonneg_left hint (by positivity)
    _ ≤ ((2 : ℝ) ^ d * (volume.real {x : Vec d | euclideanNorm (x - z) ≤ ρ})⁻¹) *
        (∫ x in {x | euclideanNorm (x - z) ≤ ρ}, f x) :=
      mul_le_mul_of_nonneg_right hcoeff (integral_nonneg hf)
    _ = _ := by ring

/-- The exact transpose derivative moment with actual shared endpoint witnesses.
The centered-source input is retained for the assigned common dependency interface;
the transpose proof only consumes the Lp-growth input. -/
@[nolint unusedArguments]
theorem local_time_transpose_derivative_moment_of_deps
  (h0 : EinsteinFull.Blueprint.node_l_u3A_forced_u2D_local_u23_centered_u2D_sourceStmt)
  (h1 : EinsteinFull.Blueprint.node_e_u3A_lp_u2D_growthStmt) :
∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d),
    ∀ p : ℝ, 2 ≤ p → ∃ C Cp : ℝ, 1 ≤ C ∧ 0 < Cp ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ ζ : ℂ,
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
      IsComplexTransposeSemigroup Q P Pdag → ∀ ν : EndpointIndex d, ν = .inr true →
    ∃ G : ℝ≥0 → Fin d → Lp ℂ 2 (reducedLaw Q),
    ∃ V : ℝ≥0 → Lp ℂ 2 (reducedLaw Q),
    (∀ t : ℝ≥0, 0 < (t : ℝ) →
      HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
        (indexedEndpoint hd Q ν ζ P Pdag β a μ t) (G t) ∧
      HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
        (uncenteredEndpoint hd Q ν ζ P Pdag β a μ t) (G t) ∧
      HasDerivAt (fun r : ℝ => indexedEndpoint hd Q ν ζ P Pdag β a μ r.toNNReal)
        (V t) (t : ℝ)) ∧
    (∀ (t : ℝ≥0) (ht : 0 < (t : ℝ)),
      let U := indexedEndpoint hd Q ν ζ P Pdag β a μ t
      let U₈ := indexedEndpoint hd Q ν ζ P Pdag β a μ (t / 8)
      MemLp (U₈ : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) ∧
      (∀ (ρ : ℝ) (x : Vec d) (hρ : Real.sqrt (t : ℝ) ≤ ρ),
        MemLp (localSpatialEnergy Q t ρ (lt_of_lt_of_le (Real.sqrt_pos.mpr ht) hρ) x (0) (V t)) (ENNReal.ofReal p) (reducedLaw Q) ∧
        (eLpNorm (localSpatialEnergy Q t ρ (lt_of_lt_of_le (Real.sqrt_pos.mpr ht) hρ) x (0) (V t))
          (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
        C * (1 + ‖ζ‖ * Real.sqrt (t : ℝ)) ^ C * (t : ℝ) ^ (-(1 / 2 : ℝ)) *
          Real.exp (Cp * ‖ζ‖ ^ 2 * (t : ℝ)) *
          (eLpNorm (U₈ : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal)) := by
  clear h0
  intro d hd D p hp
  let : Fact (2 ≤ d) := ⟨hd⟩
  obtain ⟨C₀, hC₀, hterminal⟩ :=
    local_time_transpose_derivative_terminal_cylinder_average d D.ellipticity D.one_le_ellipticity
  obtain ⟨Cp, hCp, hgrowth⟩ := local_time_transpose_cylinder_moment_of_growth
    h1 d hd D.ellipticity D.dependenceRange p hp
  let A := (2 : ℝ) ^ d * C₀
  have hA : 0 < A := by dsimp [A]; positivity
  let C := 4 + Real.sqrt A
  have hC : 1 ≤ C := by dsimp [C]; linarith [Real.sqrt_nonneg A]
  have hC3 : (3 : ℝ) ≤ C := by dsimp [C]; linarith [Real.sqrt_nonneg A]
  have hCA : Real.sqrt A ≤ C := by dsimp [C]; linarith
  refine ⟨C, Cp, hC, hCp, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P T hP hT ν hν
  subst ν
  obtain ⟨g, G, hfg, hG, hder, _⟩ :=
    local_time_transpose_endpoint_orbit_witnesses hd Q hQ β a μ hβ ζ P T hP hT
  obtain ⟨W, hW, heW, hterm⟩ := hterminal hP hT hfg
  refine ⟨G, fun t => T t g, fun t ht => ⟨(hG t).1, (hG t).2, hder t ht⟩, ?_⟩
  intro t ht U U₈
  have hu8 := local_time_endpoint_memLp h1 hd p hp Q hQ β a μ hβ ha hμ ζ P T hP hT
    (.inr true) (t / 8)
  refine ⟨hu8, ?_⟩
  intro ρ z hρ
  have hr : 0 < ρ := (Real.sqrt_pos.mpr ht).trans_le hρ
  let J := Icc ((t : ℝ) / 4) (t : ℝ)
  let S := {x : Vec d | euclideanNorm (x - z) ≤ 4 * ρ}
  have hvJ : 0 < volume.real J := by
    dsimp [J]
    rw [Real.volume_real_Icc_of_le (by linarith)]
    linarith
  have hvS : 0 < volume.real S := by
    have ho := localSpatialEnergy_window_volume z (4 * ρ) (by positivity)
    exact ho.trans_le (measureReal_mono (fun x (hx : euclideanNorm (x - z) < 4 * ρ) => hx.le)
      (isCompact_physical_euclidean_closedBall z (4 * ρ)).measure_ne_top)
  let ν := ProbabilityTheory.cond (volume : Measure ℝ) J
  let κ := ProbabilityTheory.cond (volume : Measure (Vec d)) S
  let : IsProbabilityMeasure ν := ProbabilityTheory.cond_isProbabilityMeasure_of_finite
    (ENNReal.toReal_pos_iff.mp hvJ).1.ne' (ENNReal.toReal_pos_iff.mp hvJ).2.ne
  let : IsProbabilityMeasure κ := ProbabilityTheory.cond_isProbabilityMeasure_of_finite
    (ENNReal.toReal_pos_iff.mp hvS).1.ne' (ENNReal.toReal_pos_iff.mp hvS).2.ne
  have hsupp : ∀ᵐ s ∂ν, t / 8 ≤ s.toNNReal ∧ s.toNNReal ≤ t := by
    have hj : ∀ᵐ s ∂ν, s ∈ J := by
      exact ProbabilityTheory.ae_cond_mem measurableSet_Icc
    filter_upwards [hj] with s hs
    have hs0 : 0 ≤ s := le_trans (by positivity : 0 ≤ (t : ℝ) / 4) hs.1
    constructor
    · apply NNReal.coe_le_coe.mp
      rw [Real.coe_toNNReal _ hs0]
      change (t : ℝ) / 8 ≤ s
      linarith [hs.1]
    · apply NNReal.coe_le_coe.mp
      rw [Real.coe_toNNReal _ hs0]
      exact hs.2
  have hu8' : MemLp (T (t / 8) (β ⟨0, by omega⟩)) (ENNReal.ofReal p) (reducedLaw Q) := hu8
  obtain ⟨hN, hNnorm⟩ := hgrowth Q ⟨0, by omega⟩ ζ P T hP hT
    (β ⟨0, by omega⟩) (t / 8) t hu8' ν κ hsupp W hW heW
  let N := fun ω : FieldPair d => Real.sqrt (∫ s, ∫ x, ‖W (s, translate x ω)‖ ^ 2 ∂κ ∂ν)
  have hNsq (ω : FieldPair d) : N ω ^ 2 =
      ⨍ s in J, ⨍ x in S, ‖W (s, translate x ω)‖ ^ 2 := by
    dsimp [N]
    rw [Real.sq_sqrt (integral_nonneg fun _ => integral_nonneg fun _ => sq_nonneg _)]
    simp only [ν, κ, ProbabilityTheory.cond, integral_smul_measure, ENNReal.toReal_inv,
      average_eq, smul_eq_mul, Measure.real, Measure.restrict_apply_univ]
  have hlocal := ae_complex_orbit_memLp_on_all_compacts
    (reducedLaw Q) (reducedLaw_stationary Q) (T t g)
  have hbound : ∀ᵐ ω ∂reducedLaw Q,
      (t : ℝ) * (⨍ x in {x | euclideanNorm (x - z) < ρ}, ‖(T t g) (translate x ω)‖ ^ 2) ≤
        (A * (1 + ‖ζ‖ * Real.sqrt (t : ℝ)) ^ 6 / (t : ℝ)) * N ω ^ 2 := by
    filter_upwards [hterm t ht ρ z hρ, hlocal] with ω htm hl
    have hi := (memLp_two_iff_integrable_sq_norm
      (hl _ (isCompact_physical_euclidean_closedBall z ρ)).aestronglyMeasurable).mp
        (hl _ (isCompact_physical_euclidean_closedBall z ρ))
    have hopen := c9_open_closed_average_le z hr hi (fun _ => sq_nonneg _)
    have hm := mul_le_mul_of_nonneg_left
      (hopen.trans (mul_le_mul_of_nonneg_left htm (by positivity : 0 ≤ (2 : ℝ) ^ d))) ht.le
    apply hm.trans_eq
    rw [hNsq]
    dsimp [A, J, S]
    field_simp
  obtain ⟨hmem, hnorm⟩ := local_time_zero_gradient_moment_of_sq_bound Q t ρ hr z (T t g)
    hN (ae_of_all _ fun _ => Real.sqrt_nonneg _) (by positivity) hbound
  refine ⟨hmem, ?_⟩
  have hn := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hN.ne_top) hnorm
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.sqrt_nonneg _)] at hn
  have hn' := hn.trans (mul_le_mul_of_nonneg_left hNnorm (Real.sqrt_nonneg _))
  let k := 1 + ‖ζ‖ * Real.sqrt (t : ℝ)
  have hk : 1 ≤ k := le_add_of_nonneg_right (mul_nonneg (norm_nonneg ζ) (Real.sqrt_nonneg _))
  have hroot : Real.sqrt (A * k ^ 6 / (t : ℝ)) = Real.sqrt A * k ^ 3 / Real.sqrt (t : ℝ) := by
    rw [Real.sqrt_div (by positivity), Real.sqrt_mul hA.le,
      show k ^ 6 = (k ^ 3) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  have hpow : k ^ 3 ≤ k ^ C := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hk hC3
  have hinv : (t : ℝ) ^ (-(1 / 2 : ℝ)) = (Real.sqrt (t : ℝ))⁻¹ := by
    rw [Real.rpow_neg ht.le, ← Real.sqrt_eq_rpow]
  have hcoef : Real.sqrt (A * k ^ 6 / (t : ℝ)) ≤ C * k ^ C * (t : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [hroot, hinv]
    calc
      _ ≤ C * k ^ C / Real.sqrt (t : ℝ) := by gcongr
      _ = _ := by ring
  exact hn'.trans (by
    change _ ≤ C * k ^ C * (t : ℝ) ^ (-(1 / 2 : ℝ)) * _ * _
    simpa only [mul_assoc, k, U₈, indexedEndpoint, transposeEndpoint] using mul_le_mul_of_nonneg_right hcoef
      (mul_nonneg (Real.exp_pos _).le ENNReal.toReal_nonneg))

end EinsteinFull.Blueprint
