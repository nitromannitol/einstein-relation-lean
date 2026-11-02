import EinsteinFull.Calculus.C2BlockCLTSupport
import EinsteinFull.External.AKMBlockChange

/-! Scale comparison for the literal selected matrix-clock block. -/
open MeasureTheory ProbabilityTheory
noncomputable section
namespace EinsteinFull.Calculus.C2BlockChange
open EinsteinRelation EinsteinRelation.External.AKM
open EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinFull.Blueprint EinsteinFull.External.Source.AKM
open EinsteinFull.Calculus.C2BlockBoundary EinsteinFull.Calculus.C2BlockCLT

/-- The source scale comparison retains the actual selected family and the
source base scale, before any physical rescaling. -/
theorem centeredSourceBlock_change_osBound
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (s δ γ η β : ℝ) (h : covarianceWindow d D s δ γ η β)
    (η' β' : ℝ) (hw : blockParameterWindow d s δ γ η')
    (hηβ : η' ≤ β') (hβ : β' < 1) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 < C ∧
      ∀ Q : EnvironmentLaw d D.ellipticity D.dependenceRange,
      ∀ (R r : ℝ), 1 ≤ R → 2 ≤ R ^ η' → R ^ η' ≤ r → r ≤ R ^ β' →
      ∀ (z p q : Vec d), euclideanNorm p < 1 → euclideanNorm q < 1 →
      OsBound (actualCoefficientLaw Q) (fun a =>
        |sourceCenteredBlock (actualCoefficientLaw Q)
          (covarianceSourceLocalizedEnergy d hd D s δ γ η β h Q) a z R r (fun _ => 1) p q -
         sourceCenteredBlock (actualCoefficientLaw Q)
          (covarianceSourceLocalizedEnergy d hd D s δ γ η β h Q) a z R (R ^ η') (fun _ => 1) p q|)
        s (C * R ^ (-(d : ℝ) / 2 - ε)) := by
  obtain ⟨ε, hε, hb⟩ := EinsteinFull.External.akm_block_change d hd s δ γ η' hw β' hηβ hβ
  obtain ⟨C, hC, hc⟩ := hb (AKMUpperEllipticity D.ellipticity) h.1
  refine ⟨ε, C, hε, hC, ?_⟩
  intro Q R r hR hr hlo hhi z p q hp hq
  simpa only [covarianceSourceLocalizedEnergy_eq_sourceSelectedLocalizedEnergy]
    using hc (actualCoefficientLaw Q) (lawHypotheses_actualCoefficientLaw Q)
      R r hR hr hlo hhi z p q hp hq

/-- Genuine source second moments, with the positive gain chosen before the law. -/
theorem centeredSourceBlock_change_L2
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (s δ γ η β : ℝ) (h : covarianceWindow d D s δ γ η β)
    (η' β' : ℝ) (hw : blockParameterWindow d s δ γ η')
    (hηβ : η' ≤ β') (hβ : β' < 1) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 < C ∧
      ∀ Q : EnvironmentLaw d D.ellipticity D.dependenceRange,
      ∀ (R r : ℝ), 1 ≤ R → 2 ≤ R ^ η' → R ^ η' ≤ r → r ≤ R ^ β' →
      ∀ (z p q : Vec d), euclideanNorm p < 1 → euclideanNorm q < 1 →
      let X := fun a => sourceCenteredBlock (actualCoefficientLaw Q)
          (covarianceSourceLocalizedEnergy d hd D s δ γ η β h Q) a z R r (fun _ => 1) p q -
         sourceCenteredBlock (actualCoefficientLaw Q)
          (covarianceSourceLocalizedEnergy d hd D s δ γ η β h Q) a z R (R ^ η') (fun _ => 1) p q
      MemLp X 2 (actualCoefficientLaw Q) ∧
        Real.sqrt (∫ a, (X a) ^ 2 ∂actualCoefficientLaw Q) ≤
          C * R ^ (-(d : ℝ) / 2 - ε) := by
  obtain ⟨ε, C, hε, hC, hb⟩ := centeredSourceBlock_change_osBound d hd D s δ γ η β h
    η' β' hw hηβ hβ
  let M := Real.sqrt (2 * (2 / s) ^ (2 / s))
  have hM : 0 < M := Real.sqrt_pos.2
    (mul_pos (by norm_num) (Real.rpow_pos_of_pos
      (div_pos (by norm_num) (lt_trans zero_lt_one h.2.1)) _))
  refine ⟨ε, M * C, hε, mul_pos hM hC, ?_⟩
  intro Q R r hR hr hlo hhi z p q hp hq
  have hos := hb Q R r hR hr hlo hhi z p q hp hq
  have hm := (centeredSourceBlock_measurable d hd D s δ γ η β h Q z R r p q
    (f := fun _ => 1) measurable_const).sub (centeredSourceBlock_measurable d hd D s δ γ η β h Q z R
      (R ^ η') p q (f := fun _ => 1) measurable_const)
  refine ⟨EinsteinFull.AKM.memLp_two_of_osBound hos hm.aestronglyMeasurable, ?_⟩
  simpa only [M, mul_assoc, sq_abs] using EinsteinFull.AKM.sqrt_integral_sq_le_of_osBound hos

/-- Comparing two admissible scales uses the same source base twice; the
physical base scale need not equal the source power R^etaPrime. -/
theorem centeredSourceBlock_two_scales_L2
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (s δ γ η β : ℝ) (h : covarianceWindow d D s δ γ η β)
    (η' β' : ℝ) (hw : blockParameterWindow d s δ γ η')
    (hηβ : η' ≤ β') (hβ : β' < 1) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 < C ∧
      ∀ Q : EnvironmentLaw d D.ellipticity D.dependenceRange,
      ∀ (R r t : ℝ), 1 ≤ R → 2 ≤ R ^ η' →
        R ^ η' ≤ r → r ≤ R ^ β' → R ^ η' ≤ t → t ≤ R ^ β' →
      ∀ (z p q : Vec d), euclideanNorm p < 1 → euclideanNorm q < 1 →
      let X := fun a => sourceCenteredBlock (actualCoefficientLaw Q)
          (covarianceSourceLocalizedEnergy d hd D s δ γ η β h Q) a z R r (fun _ => 1) p q -
         sourceCenteredBlock (actualCoefficientLaw Q)
          (covarianceSourceLocalizedEnergy d hd D s δ γ η β h Q) a z R t (fun _ => 1) p q
      MemLp X 2 (actualCoefficientLaw Q) ∧
        Real.sqrt (∫ a, (X a) ^ 2 ∂actualCoefficientLaw Q) ≤
          C * R ^ (-(d : ℝ) / 2 - ε) := by
  obtain ⟨ε, C, hε, hC, hb⟩ := centeredSourceBlock_change_L2 d hd D s δ γ η β h
    η' β' hw hηβ hβ
  refine ⟨ε, 2 * C, hε, mul_pos (by norm_num) hC, ?_⟩
  intro Q R r t hR hr hrlo hrhi htlo hthi z p q hp hq
  obtain ⟨hFr, hBr⟩ := hb Q R r hR hr hrlo hrhi z p q hp hq
  obtain ⟨hFt, hBt⟩ := hb Q R t hR hr htlo hthi z p q hp hq
  let F := fun u a => sourceCenteredBlock (actualCoefficientLaw Q)
    (covarianceSourceLocalizedEnergy d hd D s δ γ η β h Q) a z R u (fun _ => 1) p q
  have heq : (fun a => F r a - F t a) =
      (fun a => (F r a - F (R ^ η') a) - (F t a - F (R ^ η') a)) := by
    funext a
    ring
  change MemLp (fun a => F r a - F t a) 2 _ ∧ _
  constructor
  · rw [heq]
    exact hFr.sub hFt
  · change Real.sqrt (∫ a, (F r a - F t a) ^ 2 ∂actualCoefficientLaw Q) ≤ _
    simp_rw [congrFun heq]
    exact (rootSecondMoment_sub_le hFr hFt).trans (by linarith only [hBr, hBt])

/-- Arbitrary real polarization loads retain the common quadratic scaling
in a difference of smoothing scales. -/
theorem centeredSourceBlock_two_scales_real_loads_L2
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (s δ γ η β : ℝ) (h : covarianceWindow d D s δ γ η β)
    (η' β' : ℝ) (hw : blockParameterWindow d s δ γ η')
    (hηβ : η' ≤ β') (hβ : β' < 1) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 < C ∧
      ∀ Q : EnvironmentLaw d D.ellipticity D.dependenceRange,
      ∀ (R r t : ℝ), 1 ≤ R → 2 ≤ R ^ η' →
        R ^ η' ≤ r → r ≤ R ^ β' → R ^ η' ≤ t → t ≤ R ^ β' →
      ∀ (z p q : Vec d),
      let X := fun a => sourceCenteredBlock (actualCoefficientLaw Q)
          (covarianceSourceLocalizedEnergy d hd D s δ γ η β h Q) a z R r (fun _ => 1) p q -
         sourceCenteredBlock (actualCoefficientLaw Q)
          (covarianceSourceLocalizedEnergy d hd D s δ γ η β h Q) a z R t (fun _ => 1) p q
      MemLp X 2 (actualCoefficientLaw Q) ∧
        Real.sqrt (∫ a, (X a) ^ 2 ∂actualCoefficientLaw Q) ≤
          (1 + euclideanNorm p + euclideanNorm q) ^ 2 * C * R ^ (-(d : ℝ) / 2 - ε) := by
  obtain ⟨ε, C, hε, hC, hb⟩ := centeredSourceBlock_two_scales_L2 d hd D s δ γ η β h
    η' β' hw hηβ hβ
  refine ⟨ε, C, hε, hC, ?_⟩
  intro Q R r t hR hr hrlo hrhi htlo hthi z p q
  let v := 1 + euclideanNorm p + euclideanNorm q
  have hv : 0 < v := by dsimp [v, euclideanNorm]; positivity
  have hp : euclideanNorm (v⁻¹ • p) < 1 := by
    rw [TimeChange.euclideanNorm_smul, abs_of_pos (inv_pos.mpr hv), inv_mul_eq_div]
    apply (div_lt_one hv).2
    dsimp [v]
    have hq0 : 0 ≤ euclideanNorm q := Real.sqrt_nonneg _
    linarith
  have hq : euclideanNorm (v⁻¹ • q) < 1 := by
    rw [TimeChange.euclideanNorm_smul, abs_of_pos (inv_pos.mpr hv), inv_mul_eq_div]
    apply (div_lt_one hv).2
    dsimp [v]
    have hp0 : 0 ≤ euclideanNorm p := Real.sqrt_nonneg _
    linarith
  let Y := fun a => sourceCenteredBlock (actualCoefficientLaw Q)
      (covarianceSourceLocalizedEnergy d hd D s δ γ η β h Q) a z R r (fun _ => 1) (v⁻¹ • p) (v⁻¹ • q) -
    sourceCenteredBlock (actualCoefficientLaw Q)
      (covarianceSourceLocalizedEnergy d hd D s δ γ η β h Q) a z R t (fun _ => 1) (v⁻¹ • p) (v⁻¹ • q)
  have hscale (u : ℝ) (a : Coefficient d (AKMUpperEllipticity D.ellipticity)) :
      sourceCenteredBlock (actualCoefficientLaw Q)
        (covarianceSourceLocalizedEnergy d hd D s δ γ η β h Q) a z R u (fun _ => 1) p q =
      v ^ 2 * sourceCenteredBlock (actualCoefficientLaw Q)
        (covarianceSourceLocalizedEnergy d hd D s δ γ η β h Q) a z R u (fun _ => 1) (v⁻¹ • p) (v⁻¹ • q) := by
    simpa only [smul_smul, mul_inv_cancel₀ hv.ne', one_smul] using
      centeredSourceBlock_smul d hd D s δ γ η β h Q (actualCoefficientLaw Q)
        a z R u v (v⁻¹ • p) (v⁻¹ • q) (fun _ => 1)
  have heq (a : Coefficient d (AKMUpperEllipticity D.ellipticity)) :
      sourceCenteredBlock (actualCoefficientLaw Q)
          (covarianceSourceLocalizedEnergy d hd D s δ γ η β h Q) a z R r (fun _ => 1) p q -
        sourceCenteredBlock (actualCoefficientLaw Q)
          (covarianceSourceLocalizedEnergy d hd D s δ γ η β h Q) a z R t (fun _ => 1) p q = v ^ 2 * Y a := by
    rw [hscale r, hscale t]
    exact (mul_sub _ _ _).symm
  obtain ⟨hYm, hYb⟩ := hb Q R r t hR hr hrlo hrhi htlo hthi z (v⁻¹ • p) (v⁻¹ • q) hp hq
  dsimp only
  simp_rw [heq]
  refine ⟨hYm.const_mul (v ^ 2), ?_⟩
  rw [rootSecondMoment_const_mul, abs_of_nonneg (sq_nonneg v)]
  exact (mul_le_mul_of_nonneg_left hYb (sq_nonneg v)).trans_eq (by dsimp [v]; ring)

/-- Strictly separated exponents absorb the fixed physical dilation on both
ends of the source interval, including the literal construction threshold. -/
theorem change_source_scale_threshold
    {r₀ η η' β β' : ℝ} (hr₀ : 1 ≤ r₀) (hη : 0 < η)
    (hη' : 0 < η') (hgap : η' < η) (hβgap : β < β') :
    ∃ L₀ : ℝ, 2 ≤ L₀ ∧ ∀ L : ℝ, L₀ ≤ L →
      1 ≤ L / r₀ ∧ 2 ≤ (L / r₀) ^ η' ∧
      (L / r₀) ^ η' ≤ L ^ η / r₀ ∧ L ^ β / r₀ ≤ (L / r₀) ^ β' := by
  have hr₀0 : 0 < r₀ := lt_of_lt_of_le zero_lt_one hr₀
  obtain ⟨T, hT, ht⟩ := clt_source_scale_threshold hr₀ hη hη'.le hgap
  obtain ⟨A, hA⟩ := Filter.eventually_atTop.1
    ((tendsto_rpow_atTop hη').eventually_ge_atTop (2 * r₀ ^ η'))
  obtain ⟨B, hB⟩ := Filter.eventually_atTop.1
    ((tendsto_rpow_atTop (sub_pos.mpr hβgap)).eventually_ge_atTop (r₀ ^ β'))
  refine ⟨max T (max A B), hT.trans (le_max_left _ _), ?_⟩
  intro L hL
  have hLT := (le_max_left T _).trans hL
  have hAB := (le_max_right T _).trans hL
  have hLA := (le_max_left A B).trans hAB
  have hLB := (le_max_right A B).trans hAB
  have hL0 : 0 < L := by linarith
  obtain ⟨hR, _, hlo⟩ := ht L hLT
  refine ⟨hR, ?_, hlo, ?_⟩
  · rw [Real.div_rpow hL0.le hr₀0.le]
    exact (le_div_iff₀ (Real.rpow_pos_of_pos hr₀0 _)).2 (hA L hLA)
  · apply (div_le_self (Real.rpow_nonneg hL0.le _) hr₀).trans
    rw [Real.div_rpow hL0.le hr₀0.le]
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hr₀0 _)).2
    calc L ^ β * r₀ ^ β' ≤ L ^ β * L ^ (β' - β) :=
          mul_le_mul_of_nonneg_left (hB L hLB) (Real.rpow_nonneg hL0.le _)
      _ = L ^ β' := by rw [← Real.rpow_add hL0]; congr 1; ring

/-- The exact physical cube Jacobian leaves the source gain unchanged. -/
theorem physical_source_change_factor (d : ℕ) (ε : ℝ)
    {L r₀ : ℝ} (hL : 0 < L) (hr₀ : 0 < r₀) :
    (L ^ (-(d : ℝ) / 2) * r₀ ^ d * (L / r₀) ^ d) *
      (L / r₀) ^ (-(d : ℝ) / 2 - ε) =
      r₀ ^ ((d : ℝ) / 2 + ε) * L ^ (-ε) := by
  have he : (1 - (1 - 2 * ε)) / 2 = ε := by ring
  have hneg : -(1 - (1 - 2 * ε)) / 2 = -ε := by ring
  simpa only [he, hneg] using physical_source_boundary_factor d (1 - 2 * ε) hL hr₀

/-- The literal normalized physical energy difference, uniformly over the
law and every smoothing scale in the full prescribed physical interval. -/
theorem physicalSourceBlock_change_L2
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (s δ γ η β : ℝ) (h : covarianceWindow d D s δ γ η β) :
    ∃ ε C L₀ : ℝ, 0 < ε ∧ 0 < C ∧ 2 ≤ L₀ ∧
      ∀ Q : EnvironmentLaw d D.ellipticity D.dependenceRange,
      ∀ L : ℝ, L₀ ≤ L → ∀ r : ℝ, L ^ η ≤ r → r ≤ L ^ β → ∀ (z p q : Vec d),
      let B := fun u a => L ^ (-(d : ℝ) / 2) * ∫ y in sourceBlockCube z L,
        (1 : ℝ) * centeredLocalizedEnergy (actualCoefficientLaw Q)
          (covarianceSourceLocalizedEnergy d hd D s δ γ η β h Q) a
          (D.dependenceRange⁻¹ • y) (u / D.dependenceRange) p q
      let F := fun a => B r a - B (L ^ η) a
      Measurable F ∧ MemLp F 2 (actualCoefficientLaw Q) ∧
        Real.sqrt (∫ a, (F a) ^ 2 ∂actualCoefficientLaw Q) ≤
          (1 + euclideanNorm p + euclideanNorm q) ^ 2 * C * L ^ (-ε) := by
  obtain ⟨η', hη', hη'η, hw⟩ := clt_intermediate_exponent hd h
  have hwindow := h
  obtain ⟨_, _, _, hδ, _, _, _, _, hηhalf, hηβ, hβ⟩ := hwindow
  have hη : 0 < η := by linarith only [hηhalf]
  have hηβ' : η < β := by nlinarith only [hηβ, mul_pos hη hδ]
  obtain ⟨β', hββ', hβ'⟩ := exists_between hβ
  have hη'β' : η' ≤ β' := (hη'η.trans (hηβ'.trans hββ')).le
  obtain ⟨ε, C, hε, hC, hb⟩ := centeredSourceBlock_two_scales_real_loads_L2 d hd D s δ γ η β h
    η' β' hw hη'β' hβ'
  obtain ⟨L₀, hL₀, hscale⟩ := change_source_scale_threshold D.one_le_dependenceRange hη hη'
    hη'η hββ'
  have hr₀ : 0 < D.dependenceRange := lt_of_lt_of_le zero_lt_one D.one_le_dependenceRange
  refine ⟨ε, C * D.dependenceRange ^ ((d : ℝ) / 2 + ε), L₀,
    hε, mul_pos hC (Real.rpow_pos_of_pos hr₀ _), hL₀, ?_⟩
  intro Q L hLL r hrlo hrhi z p q
  have hL : 0 < L := by linarith
  obtain ⟨hR, hbase, hlo, hhi⟩ := hscale L hLL
  have hrlo' : L ^ η / D.dependenceRange ≤ r / D.dependenceRange :=
    div_le_div_of_nonneg_right hrlo hr₀.le
  have hrhi' : r / D.dependenceRange ≤ L ^ β / D.dependenceRange :=
    div_le_div_of_nonneg_right hrhi hr₀.le
  have hηβL : L ^ η / D.dependenceRange ≤ L ^ β / D.dependenceRange :=
    div_le_div_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le (by linarith) hηβ'.le) hr₀.le
  let Y := fun u a => sourceCenteredBlock (actualCoefficientLaw Q)
    (covarianceSourceLocalizedEnergy d hd D s δ γ η β h Q) a
    (D.dependenceRange⁻¹ • z) (L / D.dependenceRange) (u / D.dependenceRange) (fun _ => 1) p q
  have hYm (u : ℝ) : Measurable (Y u) := centeredSourceBlock_measurable d hd D s δ γ η β h Q
    _ _ _ p q measurable_const
  obtain ⟨hY, hYb⟩ := hb Q _ _ _ hR hbase (hlo.trans hrlo') (hrhi'.trans hhi)
    hlo (hηβL.trans hhi) _ p q
  let A := L ^ (-(d : ℝ) / 2) * D.dependenceRange ^ d * (L / D.dependenceRange) ^ d
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have heq (u : ℝ) (a : Coefficient d (AKMUpperEllipticity D.ellipticity)) :
      L ^ (-(d : ℝ) / 2) * (∫ y in sourceBlockCube z L,
        (1 : ℝ) * centeredLocalizedEnergy (actualCoefficientLaw Q)
          (covarianceSourceLocalizedEnergy d hd D s δ γ η β h Q) a
          (D.dependenceRange⁻¹ • y) (u / D.dependenceRange) p q) = A * Y u a := by
    exact normalized_centeredSourceLoad_rescale _ _ a z hL _ (fun _ => 1) p q hr₀
  dsimp only
  simp_rw [heq, ← mul_sub]
  refine ⟨((hYm r).sub (hYm (L ^ η))).const_mul A, hY.const_mul A, ?_⟩
  rw [rootSecondMoment_const_mul, abs_of_nonneg hA]
  calc
    _ ≤ A * ((1 + euclideanNorm p + euclideanNorm q) ^ 2 * C *
        (L / D.dependenceRange) ^ (-(d : ℝ) / 2 - ε)) :=
      mul_le_mul_of_nonneg_left hYb hA
    _ = (1 + euclideanNorm p + euclideanNorm q) ^ 2 * C *
        (A * (L / D.dependenceRange) ^ (-(d : ℝ) / 2 - ε)) := by ring
    _ = _ := by rw [physical_source_change_factor d ε hL hr₀]; ring

/-- The zero-extended physical lift preserves subtraction exactly. -/
theorem covariancePhysicalLift_sub {d : ℕ} {Λ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ r₀)
    (F G : Coefficient d (AKMUpperEllipticity Λ) → ℝ) :
    (fun ω => covariancePhysicalLift Q F ω - covariancePhysicalLift Q G ω) =
      covariancePhysicalLift Q (fun a => F a - G a) := by
  funext ω
  unfold covariancePhysicalLift
  split <;> simp

/-- Physical polarization and actual-law transport retain the source gain
in every literal matrix coordinate. -/
theorem physicalMatrixBlock_change_L2
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (s δ γ η β : ℝ) (h : covarianceWindow d D s δ γ η β) :
    ∃ ε C L₀ : ℝ, 0 < ε ∧ 0 < C ∧ 2 ≤ L₀ ∧
      ∀ Q : EnvironmentLaw d D.ellipticity D.dependenceRange,
      ∀ L : ℝ, L₀ ≤ L → ∀ r : ℝ, L ^ η ≤ r → r ≤ L ^ β →
      ∀ (z : Vec d) (j k : Fin d),
      let F := fun ω => covarianceBlock d hd D s δ γ η β h Q r L L z (fun _ => 1) ω (.inl (j, k)) -
        covarianceBlock d hd D s δ γ η β h Q (L ^ η) L L z (fun _ => 1) ω (.inl (j, k))
      Measurable F ∧ MemLp F 2 (reducedLaw Q) ∧
        Real.sqrt (∫ ω, (F ω) ^ 2 ∂reducedLaw Q) ≤ C * L ^ (-ε) := by
  obtain ⟨ε, C, L₀, hε, hC, hL₀, hb⟩ := physicalSourceBlock_change_L2 d hd D s δ γ η β h
  let t := (ellipticityScale D.ellipticity)⁻¹ / 2
  let W := 3 + ellipticityScale D.ellipticity * sourceReducedBound D.ellipticity
  have ht : 0 < t := by
    dsimp [t]
    exact div_pos (inv_pos.mpr (ellipticityScale_pos D.one_le_ellipticity)) (by norm_num)
  have hW : 0 < W := by
    dsimp [W]
    have := Clock.sourceReducedBound_pos D.one_le_ellipticity
    have := ellipticityScale_pos D.one_le_ellipticity
    positivity
  refine ⟨ε, t * (2 * W ^ 2 * C), L₀, hε, by positivity, hL₀, ?_⟩
  intro Q L hL r hrlo hrhi z j k
  let q := (ellipticityScale D.ellipticity • homogenizedCoefficient Q).mulVec (unitVector j)
  let B := fun p a =>
    (L ^ (-(d : ℝ) / 2) * ∫ y in sourceBlockCube z L,
      (1 : ℝ) * centeredLocalizedEnergy (actualCoefficientLaw Q)
        (covarianceSourceLocalizedEnergy d hd D s δ γ η β h Q) a
        (D.dependenceRange⁻¹ • y) (r / D.dependenceRange) p q) -
    (L ^ (-(d : ℝ) / 2) * ∫ y in sourceBlockCube z L,
      (1 : ℝ) * centeredLocalizedEnergy (actualCoefficientLaw Q)
        (covarianceSourceLocalizedEnergy d hd D s δ γ η β h Q) a
        (D.dependenceRange⁻¹ • y) ((L ^ η) / D.dependenceRange) p q)
  obtain ⟨hpm, hp, hpb⟩ := hb Q L hL r hrlo hrhi z (unitVector j + unitVector k) q
  obtain ⟨hmm, hm, hmb⟩ := hb Q L hL r hrlo hrhi z (unitVector j - unitVector k) q
  have hblock (u : ℝ) := physicalMatrixBlock_eq_lift d hd D s δ γ η β h Q u L L
    (by linarith) z j k (f := fun _ => (1 : ℝ)) measurable_const zero_le_one (by intro y hy; norm_num)
  have he : (fun ω =>
      covarianceBlock d hd D s δ γ η β h Q r L L z (fun _ => 1) ω (.inl (j,k)) -
      covarianceBlock d hd D s δ γ η β h Q (L ^ η) L L z (fun _ => 1) ω (.inl (j,k))) =
      covariancePhysicalLift Q (fun a => t * (B (unitVector j + unitVector k) a -
        B (unitVector j - unitVector k) a)) := by
    simp_rw [congrFun (hblock r), congrFun (hblock (L ^ η))]
    rw [covariancePhysicalLift_sub]
    congr 1
    funext a
    dsimp [B, t, q]
    rw [sourceBlockCube_eq_clockBlockCube]
    ring
  dsimp only
  have he' (ω) := congrFun he ω
  simp_rw [he']
  have hmeas : Measurable (fun a =>
      t * (B (unitVector j + unitVector k) a - B (unitVector j - unitVector k) a)) :=
    (hpm.sub hmm).const_mul t
  refine ⟨covariancePhysicalLift_measurable Q _ hmeas,
    covariancePhysicalLift_memLp Q _ hmeas 2 ((hp.sub hm).const_mul t), ?_⟩
  rw [covariancePhysicalLift_rootSecondMoment Q _ hmeas, rootSecondMoment_const_mul,
    abs_of_pos ht]
  obtain ⟨hwp, hwm⟩ := polarization_load_bound D Q j k
  have hpow : 0 ≤ L ^ (-ε) := Real.rpow_nonneg (by linarith) _
  calc
    _ ≤ t * (Real.sqrt (∫ a, (B (unitVector j + unitVector k) a) ^ 2 ∂actualCoefficientLaw Q) +
        Real.sqrt (∫ a, (B (unitVector j - unitVector k) a) ^ 2 ∂actualCoefficientLaw Q)) :=
      mul_le_mul_of_nonneg_left (rootSecondMoment_sub_le hp hm) ht.le
    _ ≤ t * (((1 + euclideanNorm (unitVector j + unitVector k) + euclideanNorm q) ^ 2 +
        (1 + euclideanNorm (unitVector j - unitVector k) + euclideanNorm q) ^ 2) * C * L ^ (-ε)) := by
      apply mul_le_mul_of_nonneg_left _ ht.le
      linarith only [hpb, hmb]
    _ ≤ t * ((2 * W ^ 2) * C * L ^ (-ε)) := by
      gcongr
      dsimp [q, W] at *
      linarith
    _ = _ := by ring

/-- A general positive-definite Gaussian, with an arbitrary measurable
truncation set, gives a genuine L2 cube pairing. -/
theorem memLp_clockCube_gaussian {d : ℕ} {Λ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ r₀) (A : Mat d) (hA : A.PosDef)
    {r : ℝ} (hr : 0 < r) {T : Set (Vec d)} (hT : MeasurableSet T)
    (x : Vec d) {L : ℝ} (hL : 0 ≤ L) :
    MemLp (fun ω => ∫ y in clockBlockCube x L, ∫ z in T,
      anisotropicGaussian A (r ^ 2) z * centeredClockField Q (y - z) ω)
      2 (reducedLaw Q) := by
  have hs := sq_pos_of_pos hr
  have hk0 (z : Vec d) : 0 ≤ anisotropicGaussian A (r ^ 2) z := by
    unfold anisotropicGaussian
    positivity
  let := clockAveragingMeasure_probability (integrable_anisotropicGaussian A hA (r ^ 2) hs)
    hk0 (integral_anisotropicGaussian A hA (r ^ 2) hs)
  have hfi := (integrableOn_const (by rw [volume_clockBlockCube x hL]; finiteness)
    (C := (1 : ℝ))).integrable_indicator (measurableSet_clockBlockCube x L)
  have h := memLp_clockTest_truncatedAverage Q
    (clockAveragingMeasure (anisotropicGaussian A (r ^ 2))) hT
    (measurable_const.indicator (measurableSet_clockBlockCube x L)) hfi
  have he (ω) :
      (∫ y, (clockBlockCube x L).indicator (fun _ => (1 : ℝ)) y *
        truncatedClockAverage Q (clockAveragingMeasure (anisotropicGaussian A (r ^ 2))) T y ω) =
      ∫ y in clockBlockCube x L, ∫ z in T,
        anisotropicGaussian A (r ^ 2) z * centeredClockField Q (y - z) ω := by
    rw [← integral_indicator (measurableSet_clockBlockCube x L)]
    apply integral_congr_ae
    exact ae_of_all _ fun y => by
      by_cases hy : y ∈ clockBlockCube x L
      · simp only [Set.indicator_of_mem hy, one_mul,
          truncatedClockAverage_eq_kernel Q
            (contDiff_anisotropicGaussian A (r ^ 2)).continuous.measurable hk0 hT]
      · simp only [Set.indicator_of_notMem hy, zero_mul]
  simpa only [he] using h

/-- Smoothing of the literal isotropic clock has the cube surface-area gain.
The Gaussian is exactly 2Id, independently of the homogenized coefficient. -/
theorem clockCube_isotropic_smoothing_variance_le {d : ℕ} {Λ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ r₀) {r : ℝ} (hr : 0 < r)
    (x : Vec d) {L : ℝ} (hL : 0 ≤ L) :
    (∫ ω, ((∫ y in clockBlockCube x L, ∫ z : Vec d,
      anisotropicGaussian ((2 : ℝ) • (1 : Mat d)) (r ^ 2) z * centeredClockField Q (y - z) ω) -
      ∫ y in clockBlockCube x L, centeredClockField Q y ω) ^ 2 ∂reducedLaw Q) ≤
      4 * clockVarianceConstant d Λ r₀ * (d : ℝ) ^ 2 * Real.sqrt 2 * L ^ (d - 1) * r := by
  let A : Mat d := (2 : ℝ) • (1 : Mat d)
  have hA : A.PosDef := S1.two_smul_one_posDef
  have hs := sq_pos_of_pos hr
  have hk0 (z : Vec d) : 0 ≤ anisotropicGaussian A (r ^ 2) z := by
    unfold anisotropicGaussian
    positivity
  let := clockAveragingMeasure_probability (integrable_anisotropicGaussian A hA (r ^ 2) hs)
    hk0 (integral_anisotropicGaussian A hA (r ^ 2) hs)
  have h := clockCube_average_sub_variance_le Q
    (clockAveragingMeasure (anisotropicGaussian A (r ^ 2)))
    (clockGaussian_first_absolute_moment A hA (r ^ 2) hs).1 x hL
  simp_rw [truncatedClockAverage_eq_kernel Q
    (contDiff_anisotropicGaussian A (r ^ 2)).continuous.measurable hk0 MeasurableSet.univ,
    Measure.restrict_univ] at h
  have hmoment := (clockGaussian_first_absolute_moment A hA (r ^ 2) hs).2
  have he : (∑ j : Fin d, Real.sqrt (r ^ 2 * A j j)) = d * Real.sqrt 2 * r := by
    simp only [A, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one,
      Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq_eq_abs, abs_of_pos hr,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [he] at hmoment
  apply h.trans
  convert mul_le_mul_of_nonneg_left hmoment
    (show 0 ≤ clockVarianceConstant d Λ r₀ * (4 * d * L ^ (d - 1)) from
      mul_nonneg (by unfold clockVarianceConstant; positivity [le_trans zero_le_one Q.range_parameter]) (by positivity)) using 1 <;> ring

/-- The unsmoothed cube clock is also a genuine second-moment variable. -/
theorem memLp_clockCube_raw {d : ℕ} {Λ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ r₀) (x : Vec d) {L : ℝ} (hL : 0 ≤ L) :
    MemLp (fun ω => ∫ y in clockBlockCube x L, centeredClockField Q y ω)
      2 (reducedLaw Q) := by
  have hfi := (integrableOn_const (by rw [volume_clockBlockCube x hL]; finiteness)
    (C := (1 : ℝ))).integrable_indicator (measurableSet_clockBlockCube x L)
  have h := memLp_clockTest Q
    (measurable_const.indicator (measurableSet_clockBlockCube x L)) hfi
  have he (ω) : (∫ y, (clockBlockCube x L).indicator (fun _ => (1 : ℝ)) y *
      centeredClockField Q y ω) = ∫ y in clockBlockCube x L, centeredClockField Q y ω := by
    rw [← integral_indicator (measurableSet_clockBlockCube x L)]
    apply integral_congr_ae
    exact ae_of_all _ fun y => by
      by_cases hy : y ∈ clockBlockCube x L
      · simp only [Set.indicator_of_mem hy, one_mul]
      · simp only [Set.indicator_of_notMem hy, zero_mul]
  change MemLp (fun ω => ∫ y, (clockBlockCube x L).indicator (fun _ => (1 : ℝ)) y *
    centeredClockField Q y ω) 2 (reducedLaw Q) at h
  simpa only [he] using h

/-- Two full isotropic clock smoothings are compared through the same raw
clock block, retaining the explicit Euclidean displacement constant. -/
theorem clockCube_isotropic_scaleChange_variance_le {d : ℕ} {Λ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ r₀) {r t : ℝ} (hr : 0 < r) (ht : 0 < t)
    (x : Vec d) {L : ℝ} (hL : 0 ≤ L) :
    (∫ ω, ((∫ y in clockBlockCube x L, ∫ z : Vec d,
      anisotropicGaussian ((2 : ℝ) • (1 : Mat d)) (r ^ 2) z * centeredClockField Q (y - z) ω) -
      ∫ y in clockBlockCube x L, ∫ z : Vec d,
        anisotropicGaussian ((2 : ℝ) • (1 : Mat d)) (t ^ 2) z * centeredClockField Q (y - z) ω) ^ 2
      ∂reducedLaw Q) ≤
      8 * clockVarianceConstant d Λ r₀ * (d : ℝ) ^ 2 * Real.sqrt 2 * L ^ (d - 1) * (r + t) := by
  let X := fun a : ℝ => fun ω => ∫ y in clockBlockCube x L, ∫ z : Vec d,
    anisotropicGaussian ((2 : ℝ) • (1 : Mat d)) (a ^ 2) z * centeredClockField Q (y - z) ω
  let Y := fun ω => ∫ y in clockBlockCube x L, centeredClockField Q y ω
  have hrmem := memLp_clockCube_gaussian Q _ S1.two_smul_one_posDef hr MeasurableSet.univ x hL
  have htmem := memLp_clockCube_gaussian Q _ S1.two_smul_one_posDef ht MeasurableSet.univ x hL
  simp only [Measure.restrict_univ] at hrmem htmem
  have hymem := memLp_clockCube_raw Q x hL
  change MemLp (X r) 2 (reducedLaw Q) at hrmem
  change MemLp (X t) 2 (reducedLaw Q) at htmem
  change MemLp Y 2 (reducedLaw Q) at hymem
  have hri := (hrmem.sub hymem).integrable_sq
  have hti := (htmem.sub hymem).integrable_sq
  change Integrable (fun ω => (X r ω - Y ω) ^ 2) (reducedLaw Q) at hri
  change Integrable (fun ω => (X t ω - Y ω) ^ 2) (reducedLaw Q) at hti
  have h : (∫ ω, (X r ω - X t ω) ^ 2 ∂reducedLaw Q) ≤
      2 * (∫ ω, (X r ω - Y ω) ^ 2 ∂reducedLaw Q) +
        2 * (∫ ω, (X t ω - Y ω) ^ 2 ∂reducedLaw Q) := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add
      (hri.const_mul 2) (hti.const_mul 2)]
    apply integral_mono (hrmem.sub htmem).integrable_sq
      ((hri.const_mul 2).add (hti.const_mul 2))
    intro ω
    dsimp only [Pi.add_apply, Pi.sub_apply]
    nlinarith [sq_nonneg (X r ω + X t ω - 2 * Y ω)]
  apply h.trans
  have hrbound := clockCube_isotropic_smoothing_variance_le Q hr x hL
  have htbound := clockCube_isotropic_smoothing_variance_le Q ht x hL
  change (∫ ω, (X r ω - Y ω) ^ 2 ∂reducedLaw Q) ≤ _ at hrbound
  change (∫ ω, (X t ω - Y ω) ^ 2 ∂reducedLaw Q) ≤ _ at htbound
  linarith only [hrbound, htbound]

/-- The actual Gaussian clock convolution is jointly measurable, including
its unrenormalized restriction to an arbitrary measurable spatial region. -/
theorem clockGaussian_joint_measurable {d : ℕ} {Λ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ r₀) (A : Mat d) (s : ℝ) (T : Set (Vec d)) :
    Measurable (fun p : Vec d × FieldPair d => ∫ z in T,
      anisotropicGaussian A s z * centeredClockField Q (p.1 - z) p.2) := by
  have hm : Measurable (fun p : (Vec d × FieldPair d) × Vec d =>
      anisotropicGaussian A s p.2 * centeredClockField Q (p.1.1 - p.2) p.1.2) :=
    ((contDiff_anisotropicGaussian A s).continuous.measurable.comp measurable_snd).mul
      ((continuous_centeredClockField Q).measurable.comp
        ((measurable_fst.fst.sub measurable_snd).prodMk measurable_fst.snd))
  exact hm.stronglyMeasurable.integral_prod_right' (ν := volume.restrict T) |>.measurable

/-- Restricting the probability Gaussian cannot enlarge a uniform clock bound. -/
theorem clockGaussian_average_abs_le {d : ℕ} {Λ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ r₀) (A : Mat d) (hA : A.PosDef)
    {s : ℝ} (hs : 0 < s) (T : Set (Vec d)) (x : Vec d) (ω : FieldPair d)
    {B : ℝ} (hB : 0 ≤ B) (hω : ∀ y, |centeredClockField Q y ω| ≤ B) :
    |∫ z in T, anisotropicGaussian A s z * centeredClockField Q (x - z) ω| ≤ B := by
  have hk := integrable_anisotropicGaussian A hA s hs
  have hk0 (z : Vec d) : 0 ≤ anisotropicGaussian A s z := by
    unfold anisotropicGaussian
    positivity
  calc
    _ ≤ ∫ z in T, anisotropicGaussian A s z * B := by
      change ‖∫ z in T, anisotropicGaussian A s z * centeredClockField Q (x - z) ω‖ ≤ _
      apply norm_integral_le_of_norm_le (hk.mul_const B).integrableOn
      exact ae_of_all _ fun z => by
        rw [norm_mul, Real.norm_of_nonneg (hk0 z), Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hω (x - z)) (hk0 z)
    _ ≤ ∫ z : Vec d, anisotropicGaussian A s z * B :=
      integral_mono_measure Measure.restrict_le_self
        (ae_of_all _ fun z => mul_nonneg (hk0 z) hB) (hk.mul_const B)
    _ = B := by rw [integral_mul_const, integral_anisotropicGaussian A hA s hs, one_mul]

/-- The spatial Gaussian clock pairing is integrable on the finite Euclidean
cube whenever the environment has the simultaneous structural clock bound. -/
theorem integrableOn_clockGaussian_average {d : ℕ} {Λ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ r₀) (A : Mat d) (hA : A.PosDef)
    {s : ℝ} (hs : 0 < s) (T : Set (Vec d)) (x : Vec d)
    {L : ℝ} (hL : 0 ≤ L) (ω : FieldPair d) {B : ℝ} (hB : 0 ≤ B)
    (hω : ∀ y, |centeredClockField Q y ω| ≤ B) :
    IntegrableOn (fun y => ∫ z in T,
      anisotropicGaussian A s z * centeredClockField Q (y - z) ω)
      (clockBlockCube x L) volume := by
  have hLf : volume (clockBlockCube x L) < ⊤ := by
    rw [volume_clockBlockCube x hL]
    finiteness
  apply IntegrableOn.of_bound hLf
    ((clockGaussian_joint_measurable Q A s T).comp
      (measurable_id.prodMk measurable_const)).aestronglyMeasurable.restrict B
  exact ae_of_all _ fun y => by
    simpa only [Real.norm_eq_abs] using! clockGaussian_average_abs_le Q A hA hs T y ω hB hω

/-- Physical truncation of the literal isotropic clock has every inverse-power
cube error bound, with the constant chosen before the law and both scales. -/
theorem clockCube_isotropic_truncation_L2 {d : ℕ}
    (D : StructuralData d) {δ : ℝ} (hδ : 0 < δ) (p : ℝ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ Q : EnvironmentLaw d D.ellipticity D.dependenceRange,
      ∀ r : ℝ, 2 * D.dependenceRange ≤ r → ∀ (x : Vec d) (L : ℝ), 0 ≤ L →
      let F := fun ω => (∫ y in clockBlockCube x L, ∫ z : Vec d,
          anisotropicGaussian ((2 : ℝ) • (1 : Mat d)) (r ^ 2) z * centeredClockField Q (y - z) ω) -
        ∫ y in clockBlockCube x L, ∫ z in ball (0 : Vec d) (covarianceLocalizationRadius D δ r),
          anisotropicGaussian ((2 : ℝ) • (1 : Mat d)) (r ^ 2) z * centeredClockField Q (y - z) ω
      MemLp F 2 (reducedLaw Q) ∧
        Real.sqrt (∫ ω, (F ω) ^ 2 ∂reducedLaw Q) ≤ C * L ^ d * r ^ (-p) := by
  obtain ⟨C, hC, htail⟩ := covarianceHeatKernel_physical_tail_inversePower_le D hδ p
  let B := 2 * sourceReducedBound D.ellipticity
  have hB : 0 < B := mul_pos (by norm_num) (Clock.sourceReducedBound_pos D.one_le_ellipticity)
  refine ⟨B * C, mul_pos hB hC, ?_⟩
  intro Q r hr x L hL
  have hrpos : 0 < r := lt_of_lt_of_le
    (mul_pos (by norm_num) (lt_of_lt_of_le zero_lt_one D.one_le_dependenceRange)) hr
  let A : Mat d := (2 : ℝ) • (1 : Mat d)
  let T := ball (0 : Vec d) (covarianceLocalizationRadius D δ r)
  let G := fun ω => (∫ y in clockBlockCube x L, ∫ z : Vec d,
      anisotropicGaussian A (r ^ 2) z * centeredClockField Q (y - z) ω) -
    ∫ y in clockBlockCube x L, ∫ z in T,
      anisotropicGaussian A (r ^ 2) z * centeredClockField Q (y - z) ω
  have hu := memLp_clockCube_gaussian Q A S1.two_smul_one_posDef hrpos MeasurableSet.univ x hL
  simp only [Measure.restrict_univ] at hu
  have ht := memLp_clockCube_gaussian Q A S1.two_smul_one_posDef hrpos (T := T)
    (covarianceSourceBall_measurable (0 : Vec d) (covarianceLocalizationRadius D δ r)) x hL
  have hg : MemLp G 2 (reducedLaw Q) := hu.sub ht
  change MemLp G 2 (reducedLaw Q) ∧ _
  refine ⟨hg, ?_⟩
  have hb : ∀ᵐ ω ∂reducedLaw Q, |G ω| ≤ (B * C) * L ^ d * r ^ (-p) := by
    filter_upwards [ae_forall_abs_centeredClockField_le Q,
      covarianceLocalizedClock_ae_truncation_error_le Q hrpos
        (covarianceLocalizationRadius D δ r)] with ω hω herr
    have hiu := integrableOn_clockGaussian_average Q A S1.two_smul_one_posDef
      (sq_pos_of_pos hrpos) Set.univ x hL ω hB.le hω
    simp only [Measure.restrict_univ] at hiu
    have hit := integrableOn_clockGaussian_average Q A S1.two_smul_one_posDef
      (sq_pos_of_pos hrpos) T x hL ω hB.le hω
    have he (y : Vec d) : |(∫ z : Vec d,
        anisotropicGaussian A (r ^ 2) z * centeredClockField Q (y - z) ω) -
        ∫ z in T, anisotropicGaussian A (r ^ 2) z * centeredClockField Q (y - z) ω| ≤
          B * C * r ^ (-p) := by
      have hy := herr y
      simp only [covarianceLocalizedClock, S1.heatKernel_eq_anisotropic r hrpos] at hy
      have htail' := htail r hr
      rw [S1.heatKernel_eq_anisotropic r hrpos] at htail'
      exact hy.trans (by
        simpa only [B, mul_assoc] using mul_le_mul_of_nonneg_left htail' hB.le)
    dsimp only [G]
    rw [← integral_sub hiu hit]
    calc
      _ ≤ ∫ y in clockBlockCube x L, B * C * r ^ (-p) := by
        change ‖∫ y in clockBlockCube x L,
          ((∫ z : Vec d, anisotropicGaussian A (r ^ 2) z * centeredClockField Q (y - z) ω) -
            ∫ z in T, anisotropicGaussian A (r ^ 2) z * centeredClockField Q (y - z) ω)‖ ≤ _
        apply norm_integral_le_of_norm_le
          (integrableOn_const (by rw [volume_clockBlockCube x hL]; finiteness))
        exact ae_of_all _ fun y => by simpa only [Real.norm_eq_abs] using he y
      _ = _ := by rw [setIntegral_const, smul_eq_mul, volumeReal_clockBlockCube x hL]; ring
  have hi : (∫ ω, (G ω) ^ 2 ∂reducedLaw Q) ≤ ((B * C) * L ^ d * r ^ (-p)) ^ 2 := by
    apply (integral_mono_ae hg.integrable_sq (integrable_const _) <|
      hb.mono fun ω hω => by
        simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hω 2).trans_eq
    simp only [integral_const, probReal_univ, one_smul]
  exact (Real.sqrt_le_sqrt hi).trans_eq (Real.sqrt_sq (by positivity))

/-- The Euclidean cube surface factor gives the asserted normalized gain. -/
theorem normalized_clock_surface_factor {d : ℕ} (hd : 1 ≤ d)
    {L : ℝ} (hL : 0 < L) (β : ℝ) :
    (L ^ (-(d : ℝ) / 2)) ^ 2 * L ^ (d - 1) * L ^ β =
      (L ^ (-(1 - β) / 2)) ^ 2 := by
  rw [← Real.rpow_natCast (L ^ (-(d : ℝ) / 2)) 2, ← Real.rpow_mul hL.le,
    ← Real.rpow_natCast L (d - 1), ← Real.rpow_add hL, ← Real.rpow_add hL,
    ← Real.rpow_natCast (L ^ (-(1 - β) / 2)) 2, ← Real.rpow_mul hL.le]
  congr 1
  rw [Nat.cast_sub hd]
  push_cast
  ring

/-- Normalized full isotropic clock smoothings have the surface-area decay,
uniformly for both smoothing scales below the prescribed upper power. -/
theorem normalized_clockCube_isotropic_scaleChange_L2 {d : ℕ} (hd : 1 ≤ d)
    {Λ r₀ : ℝ} (Q : EnvironmentLaw d Λ r₀) (β : ℝ)
    {L r t : ℝ} (hL : 0 < L) (hr : 0 < r) (ht : 0 < t)
    (hrhi : r ≤ L ^ β) (hthi : t ≤ L ^ β) (x : Vec d) :
    let F := fun ω => L ^ (-(d : ℝ) / 2) *
      ((∫ y in clockBlockCube x L, ∫ z : Vec d,
        anisotropicGaussian ((2 : ℝ) • (1 : Mat d)) (r ^ 2) z * centeredClockField Q (y - z) ω) -
       ∫ y in clockBlockCube x L, ∫ z : Vec d,
        anisotropicGaussian ((2 : ℝ) • (1 : Mat d)) (t ^ 2) z * centeredClockField Q (y - z) ω)
    MemLp F 2 (reducedLaw Q) ∧
      Real.sqrt (∫ ω, (F ω) ^ 2 ∂reducedLaw Q) ≤
        Real.sqrt (16 * clockVarianceConstant d Λ r₀ * (d : ℝ) ^ 2 * Real.sqrt 2) *
          L ^ (-(1 - β) / 2) := by
  let K := 16 * clockVarianceConstant d Λ r₀ * (d : ℝ) ^ 2 * Real.sqrt 2
  have hV : 0 ≤ clockVarianceConstant d Λ r₀ := by
    unfold clockVarianceConstant
    positivity [le_trans zero_le_one Q.range_parameter]
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hu := memLp_clockCube_gaussian Q _ S1.two_smul_one_posDef hr MeasurableSet.univ x hL.le
  have hv := memLp_clockCube_gaussian Q _ S1.two_smul_one_posDef ht MeasurableSet.univ x hL.le
  simp only [Measure.restrict_univ] at hu hv
  dsimp only
  refine ⟨(hu.sub hv).const_mul _, ?_⟩
  have hb := clockCube_isotropic_scaleChange_variance_le Q hr ht x hL.le
  have hupper : 8 * clockVarianceConstant d Λ r₀ * (d : ℝ) ^ 2 * Real.sqrt 2 *
      L ^ (d - 1) * (r + t) ≤ K * L ^ (d - 1) * L ^ β := by
    have hh := mul_le_mul_of_nonneg_left (add_le_add hrhi hthi)
      (show 0 ≤ 8 * clockVarianceConstant d Λ r₀ * (d : ℝ) ^ 2 * Real.sqrt 2 * L ^ (d - 1)
        by positivity)
    convert hh using 1 <;> dsimp [K] <;> ring
  have hi : (∫ ω, (L ^ (-(d : ℝ) / 2) *
      ((∫ y in clockBlockCube x L, ∫ z : Vec d,
        anisotropicGaussian ((2 : ℝ) • (1 : Mat d)) (r ^ 2) z * centeredClockField Q (y - z) ω) -
       ∫ y in clockBlockCube x L, ∫ z : Vec d,
        anisotropicGaussian ((2 : ℝ) • (1 : Mat d)) (t ^ 2) z * centeredClockField Q (y - z) ω)) ^ 2
      ∂reducedLaw Q) ≤ (Real.sqrt K * L ^ (-(1 - β) / 2)) ^ 2 := by
    simp_rw [mul_pow]
    rw [integral_const_mul]
    calc
      _ ≤ (L ^ (-(d : ℝ) / 2)) ^ 2 * (K * L ^ (d - 1) * L ^ β) :=
        mul_le_mul_of_nonneg_left (hb.trans hupper) (sq_nonneg _)
      _ = K * ((L ^ (-(d : ℝ) / 2)) ^ 2 * L ^ (d - 1) * L ^ β) := by ring
      _ = _ := by rw [normalized_clock_surface_factor hd hL, Real.sq_sqrt hK]
  exact (Real.sqrt_le_sqrt hi).trans_eq (Real.sqrt_sq (by positivity))

/-- A sufficiently high inverse-power tail survives cube normalization and
decays faster than the clock surface gain for all admissible smoothing scales. -/
theorem normalized_clock_tail_power {d : ℕ} {L r η β : ℝ}
    (hL : 1 ≤ L) (hη : 1 / 2 < η) (hβ : 0 < β) (hr : L ^ η ≤ r) :
    L ^ (-(d : ℝ) / 2) * L ^ d * r ^ (-((d : ℝ) + 2)) ≤
      L ^ (-(1 - β) / 2) := by
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hp : 0 ≤ (d : ℝ) + 2 := by positivity
  have hb := Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hLpos η) hr (neg_nonpos.mpr hp)
  calc
    _ ≤ L ^ (-(d : ℝ) / 2) * L ^ d * (L ^ η) ^ (-((d : ℝ) + 2)) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = L ^ ((d : ℝ) / 2 - η * ((d : ℝ) + 2)) := by
      rw [← Real.rpow_mul hLpos.le, ← Real.rpow_natCast L d,
        ← Real.rpow_add hLpos, ← Real.rpow_add hLpos]
      congr 1
      ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hL (by
      have hd : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
      nlinarith)

/-- The literal truncated physical clock has the same scale-change gain as
the full isotropic smoothing. Both truncation errors are internal estimates. -/
theorem physicalClockBlock_change_L2
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (s δ γ η β : ℝ) (h : covarianceWindow d D s δ γ η β) :
    ∃ C L₀ : ℝ, 0 < C ∧ 2 ≤ L₀ ∧
      ∀ Q : EnvironmentLaw d D.ellipticity D.dependenceRange,
      ∀ L : ℝ, L₀ ≤ L → ∀ r : ℝ, L ^ η ≤ r → r ≤ L ^ β → ∀ x : Vec d,
      let F := fun ω => covarianceBlock d hd D s δ γ η β h Q r L L x (fun _ => 1) ω (.inr ()) -
        covarianceBlock d hd D s δ γ η β h Q (L ^ η) L L x (fun _ => 1) ω (.inr ())
      MemLp F 2 (reducedLaw Q) ∧
        Real.sqrt (∫ ω, (F ω) ^ 2 ∂reducedLaw Q) ≤ C * L ^ (-(1 - β) / 2) := by
  have hwindow := h
  obtain ⟨_, _, _, hδ, _, _, _, _, hηhalf, hηβ, _⟩ := hwindow
  have hη : 0 < η := by linarith only [hηhalf]
  have hβpos : 0 < β := lt_trans (mul_pos hη (by linarith)) hηβ
  obtain ⟨T₀, hT₀, hscale⟩ := clt_source_scale_threshold D.one_le_dependenceRange hη
    (η' := 0) le_rfl hη
  obtain ⟨C, hC, htrunc⟩ := clockCube_isotropic_truncation_L2 D hδ ((d : ℝ) + 2)
  let K := Real.sqrt (16 * clockVarianceConstant d D.ellipticity D.dependenceRange *
    (d : ℝ) ^ 2 * Real.sqrt 2)
  refine ⟨K + 2 * C, T₀, add_pos_of_nonneg_of_pos (Real.sqrt_nonneg _) (by positivity), hT₀, ?_⟩
  intro Q L hL r hrlo hrhi x
  have hL2 : 2 ≤ L := hT₀.trans hL
  have hL1 : 1 ≤ L := by linarith
  have hLpos : 0 < L := by linarith
  have hr₀ : 0 < D.dependenceRange := lt_of_lt_of_le zero_lt_one D.one_le_dependenceRange
  have hbase : 2 * D.dependenceRange ≤ L ^ η :=
    (le_div_iff₀ hr₀).1 (hscale L hL).2.1
  have htpos : 0 < L ^ η := Real.rpow_pos_of_pos hLpos η
  have hrpos : 0 < r := htpos.trans_le hrlo
  let U := fun a ω => L ^ (-(d : ℝ) / 2) * ∫ y in clockBlockCube x L, ∫ z : Vec d,
    anisotropicGaussian ((2 : ℝ) • (1 : Mat d)) (a ^ 2) z * centeredClockField Q (y - z) ω
  let V := fun a ω => covarianceBlock d hd D s δ γ η β h Q a L L x (fun _ => 1) ω (.inr ())
  let E := fun a ω => U a ω - V a ω
  have he (a : ℝ) (ha : L ^ η ≤ a) : MemLp (E a) 2 (reducedLaw Q) ∧
      Real.sqrt (∫ ω, (E a ω) ^ 2 ∂reducedLaw Q) ≤ C * L ^ (-(1 - β) / 2) := by
    have hapos : 0 < a := htpos.trans_le ha
    obtain ⟨hp, hb⟩ := htrunc Q a (hbase.trans ha) x L hLpos.le
    have heq : E a = fun ω => L ^ (-(d : ℝ) / 2) *
        ((∫ y in clockBlockCube x L, ∫ z : Vec d,
          anisotropicGaussian ((2 : ℝ) • (1 : Mat d)) (a ^ 2) z * centeredClockField Q (y - z) ω) -
         ∫ y in clockBlockCube x L, ∫ z in ball (0 : Vec d) (covarianceLocalizationRadius D δ a),
          anisotropicGaussian ((2 : ℝ) • (1 : Mat d)) (a ^ 2) z * centeredClockField Q (y - z) ω) := by
      funext ω
      dsimp only [E, U, V]
      rw [S1.clock_block_eq d hd D s δ γ η β h Q hapos]
      simp only [one_mul]
      ring
    rw [heq]
    refine ⟨hp.const_mul _, ?_⟩
    rw [rootSecondMoment_const_mul, abs_of_pos (Real.rpow_pos_of_pos hLpos _)]
    calc
      _ ≤ L ^ (-(d : ℝ) / 2) * (C * L ^ d * a ^ (-((d : ℝ) + 2))) :=
        mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hLpos.le _)
      _ = C * (L ^ (-(d : ℝ) / 2) * L ^ d * a ^ (-((d : ℝ) + 2))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (normalized_clock_tail_power hL1 hηhalf hβpos ha) hC.le
  have hf := normalized_clockCube_isotropic_scaleChange_L2 (by omega : 1 ≤ d)
    Q β hLpos hrpos htpos hrhi (hrlo.trans hrhi) x
  have heq : (fun ω => U r ω - U (L ^ η) ω) =
      (fun ω => L ^ (-(d : ℝ) / 2) *
        ((∫ y in clockBlockCube x L, ∫ z : Vec d,
          anisotropicGaussian ((2 : ℝ) • (1 : Mat d)) (r ^ 2) z * centeredClockField Q (y - z) ω) -
         ∫ y in clockBlockCube x L, ∫ z : Vec d,
          anisotropicGaussian ((2 : ℝ) • (1 : Mat d)) ((L ^ η) ^ 2) z * centeredClockField Q (y - z) ω)) := by
    funext ω
    dsimp only [U]
    ring
  rw [← heq] at hf
  obtain ⟨her, hbr⟩ := he r hrlo
  obtain ⟨het, hbt⟩ := he (L ^ η) le_rfl
  have herr := her.sub het
  have hmain := hf.1.sub herr
  have hmainEq : (fun ω => (U r ω - U (L ^ η) ω) - (E r ω - E (L ^ η) ω)) =
      (fun ω => V r ω - V (L ^ η) ω) := by
    funext ω
    dsimp only [E]
    ring
  change MemLp (fun ω => (U r ω - U (L ^ η) ω) -
    (E r ω - E (L ^ η) ω)) 2 (reducedLaw Q) at hmain
  rw [hmainEq] at hmain
  refine ⟨hmain, ?_⟩
  change Real.sqrt (∫ ω, (V r ω - V (L ^ η) ω) ^ 2 ∂reducedLaw Q) ≤ _
  simp_rw [← congrFun hmainEq]
  have htri := rootSecondMoment_sub_le hf.1 herr
  simp only [Pi.sub_apply] at htri
  have htailtri := rootSecondMoment_sub_le her het
  have hfull := hf.2
  change Real.sqrt (∫ ω, (U r ω - U (L ^ η) ω) ^ 2 ∂reducedLaw Q) ≤
    K * L ^ (-(1 - β) / 2) at hfull
  nlinarith only [htri, htailtri, hfull, hbr, hbt]

/-- Full Euclidean matrix-clock scale comparison, with a single positive
structural gain and all constants fixed before the actual environment law. -/
theorem covarianceBlock_change_L2
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (s δ γ η β : ℝ) (h : covarianceWindow d D s δ γ η β) :
    ∃ C L₀ κ : ℝ, 0 < C ∧ 2 ≤ L₀ ∧ 0 < κ ∧ κ ≤ (1 - β) / 2 ∧
      ∀ Q : EnvironmentLaw d D.ellipticity D.dependenceRange,
      ∀ L : ℝ, L₀ ≤ L → ∀ (x : Vec d) (r : ℝ), L ^ η ≤ r → r ≤ L ^ β →
      let X := fun ω a => covarianceBlock d hd D s δ γ η β h Q r L L x (fun _ => 1) ω a -
        covarianceBlock d hd D s δ γ η β h Q (L ^ η) L L x (fun _ => 1) ω a
      MemLp (fun ω => covarianceVectorSize (X ω)) 2 (reducedLaw Q) ∧
        covarianceL2Size (reducedLaw Q) X ≤ C * L ^ (-κ) := by
  classical
  obtain ⟨ε, Cm, Lm, hε, hCm, hLm, hm⟩ := physicalMatrixBlock_change_L2 d hd D s δ γ η β h
  obtain ⟨Cc, Lc, hCc, hLc, hc⟩ := physicalClockBlock_change_L2 d hd D s δ γ η β h
  have hβ : β < 1 := h.2.2.2.2.2.2.2.2.2.2
  let κ := min ε ((1 - β) / 2)
  let M := Cm + Cc
  have hκ : 0 < κ := lt_min hε (by linarith)
  have hM : 0 < M := add_pos hCm hCc
  have hcard : 0 < (Fintype.card (JointObservationIndex d) : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨Sum.inr ()⟩
  refine ⟨Real.sqrt (Fintype.card (JointObservationIndex d) : ℝ) * M, max Lm Lc, κ,
    mul_pos (Real.sqrt_pos.mpr hcard) hM, hLm.trans (le_max_left _ _), hκ,
    min_le_right _ _, ?_⟩
  intro Q L hL x r hrlo hrhi
  have hLLm : Lm ≤ L := (le_max_left _ _).trans hL
  have hLLc : Lc ≤ L := (le_max_right _ _).trans hL
  have hL1 : 1 ≤ L := by linarith [hLm.trans hLLm]
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL1
  have hpm := Real.rpow_le_rpow_of_exponent_le hL1 (neg_le_neg (min_le_left ε ((1 - β) / 2)))
  have hpc : L ^ (-(1 - β) / 2) ≤ L ^ (-κ) := by
    simpa only [neg_div] using Real.rpow_le_rpow_of_exponent_le hL1
      (neg_le_neg (min_le_right ε ((1 - β) / 2)))
  have hpow : 0 ≤ L ^ (-κ) := Real.rpow_nonneg hLpos.le _
  let X := fun ω a => covarianceBlock d hd D s δ γ η β h Q r L L x (fun _ => 1) ω a -
    covarianceBlock d hd D s δ γ η β h Q (L ^ η) L L x (fun _ => 1) ω a
  have hcoord (i : JointObservationIndex d) : MemLp (fun ω => X ω i) 2 (reducedLaw Q) ∧
      Real.sqrt (∫ ω, (X ω i) ^ 2 ∂reducedLaw Q) ≤ M * L ^ (-κ) := by
    rcases i with ⟨j, k⟩ | u
    · obtain ⟨_, hp, hb⟩ := hm Q L hLLm r hrlo hrhi x j k
      refine ⟨hp, hb.trans ?_⟩
      calc
        _ ≤ Cm * L ^ (-κ) := mul_le_mul_of_nonneg_left hpm hCm.le
        _ ≤ _ := mul_le_mul_of_nonneg_right (by dsimp [M]; linarith) hpow
    · cases u
      obtain ⟨hp, hb⟩ := hc Q L hLLc r hrlo hrhi x
      refine ⟨hp, hb.trans ?_⟩
      calc
        _ ≤ Cc * L ^ (-κ) := mul_le_mul_of_nonneg_left hpc hCc.le
        _ ≤ _ := mul_le_mul_of_nonneg_right (by dsimp [M]; linarith) hpow
  have hv := covarianceVectorSize_L2_of_coordinates (reducedLaw Q) X
    (fun i => (hcoord i).1.aestronglyMeasurable) (fun i => (hcoord i).1)
    (mul_nonneg hM.le hpow) (fun i => (hcoord i).2)
  refine ⟨hv.1, ?_⟩
  simpa only [mul_assoc] using hv.2

end EinsteinFull.Calculus.C2BlockChange
