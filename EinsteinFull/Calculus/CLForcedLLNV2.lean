import EinsteinFull.Calculus.C11ForcedSignedVelocity
import EinsteinFull.Calculus.U2GMPFinalEnvironment
import EinsteinFull.Calculus.CLSpatialDilation
import EinsteinRelation.Sharpness.PhysicalLawSampleBounds
import EinsteinFull.Blueprint.Foundation.Draft.S2SmoothScopePathwise
import EinsteinFull.Blueprint.Foundation.Draft.S2SmoothScopeForcedLLN
import EinsteinFull.Blueprint.Foundation.node_eq_u2E_reduced_u2D_bounds

/-! Smooth-scope (D1) forced LLN, `paper/main.tex:227`. For forces in `(0,1]` the
GMP Section 7 kernel solves the literal martingale problem and has the GMP
velocity; smooth-scope pathwise uniqueness identifies every supplied law with it.
The reduced law is handled through the zero-potential reduced environment law.
Other forces are normalized by spatial scaling and reflection of the law. -/

open MeasureTheory Filter ProbabilityTheory
open scoped NNReal

namespace EinsteinFull
open EinsteinRelation EinsteinRelation.External.GantertSection7Support

/-- Supplied physical laws agree on a smooth environment law. -/
theorem clr_physical_mp_unique_smooth
    (hpath : Blueprint.node_eq_u2E_reduced_u2D_generator_u23_pathwiseStmtV2)
    {d : ℕ} (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
    (i : Fin d) (lam : ℝ) (PX PX' : QuenchedPathLaws d)
    (hX : ∀ᵐ ω ∂Q.measure, SolvesMartingaleProblem (physicalGenerator i ω lam) 0 (PX (0, ω)))
    (hX' : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (physicalGenerator i ω lam) 0 (PX' (0, ω))) :
    ∀ᵐ ω ∂Q.measure, PX (0, ω) = PX' (0, ω) := by
  obtain ⟨⟨-, PY, -, hY⟩, huniq⟩ := hpath d hd D Q hQ i lam
  filter_upwards [huniq PX PY hX hY, huniq PX' PY hX' hY, Q.regular] with ω h1 h2 hω
  rw [(h1 hω).1, (h2 hω).1]

/-- Supplied reduced laws agree on a smooth environment law. -/
theorem clr_reduced_mp_unique_smooth
    (hpath : Blueprint.node_eq_u2E_reduced_u2D_generator_u23_pathwiseStmtV2)
    {d : ℕ} (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
    (i : Fin d) (lam : ℝ) (PY PY' : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure, SolvesMartingaleProblem (reducedGenerator i ω lam) 0 (PY (0, ω)))
    (hY' : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator i ω lam) 0 (PY' (0, ω))) :
    ∀ᵐ ω ∂Q.measure, PY (0, ω) = PY' (0, ω) := by
  obtain ⟨⟨PX, -, hX, -⟩, huniq⟩ := hpath d hd D Q hQ i lam
  filter_upwards [huniq PX PY hX hY, huniq PX PY' hX hY', Q.regular] with ω h1 h2 hω
  exact pathLaw_eq_of_inverseClock_map_eq ω D.ellipticity hω _ _ ((h1 hω).1.symm.trans (h2 hω).1)

/-- Physical velocity for forces in `(0,1]` on a smooth environment law. -/
theorem clr_physical_velocity_unit
    (hpath : Blueprint.node_eq_u2E_reduced_u2D_generator_u23_pathwiseStmtV2)
    {d : ℕ} (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
    {lam : ℝ} (h0 : 0 < lam) (h1 : lam ≤ 1) (P : Kernel (FieldPair d) (Path d))
    (hP : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (physicalGenerator (firstCoordinateIndex hd) ω lam) 0 (P ω)) :
    ∃ v : Vec d, HasQuenchedVelocity Q.measure P v ∧ 0 < v (firstCoordinateIndex hd) := by
  have hsm : ∀ᵐ ω ∂Q.measure, IsSmoothFieldPair ω := hQ.mono fun ω h => h.1
  obtain ⟨K, -, hsrc, hKmp⟩ := u2_foundation_smooth_gmp_physical_origin_law_and_mp
    hd D.one_le_ellipticity Q lam h0.le h1 hsm
  have heq := clr_physical_mp_unique_smooth hpath hd D Q hQ (firstCoordinateIndex hd) lam
    (P.comap Prod.snd measurable_snd) (K.comap Prod.snd measurable_snd) hP hKmp
  have hsrcP : IsGMPPhysicalOriginLaw hd Q.ellipticity_parameter Q lam h0.le h1 P := by
    filter_upwards [hsrc, heq] with ω hω hωeq
    obtain ⟨hreg, r, hr⟩ := hω
    exact ⟨hreg, r, hωeq.trans hr⟩
  obtain ⟨v, hv, hpos, -⟩ := Regeneration.gmp_physical_origin_velocity hd Q h0 h1 P hsrcP
  exact ⟨v, hv, hpos⟩

/-- Structural data of the scaled law: the same ellipticity and derivative
bounds, with the range enlarged by `c⁻¹`. -/
noncomputable def clrScaledData {d : ℕ} (D : StructuralData d) {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) :
    StructuralData d where
  ellipticity := D.ellipticity
  dependenceRange := D.dependenceRange / c
  derivativeBound := D.derivativeBound
  one_le_ellipticity := D.one_le_ellipticity
  one_le_dependenceRange := by
    rw [le_div_iff₀ hc, one_mul]
    exact hc1.trans D.one_le_dependenceRange
  derivativeBound_pos := D.derivativeBound_pos

/-- A contracted environment law keeps the smooth bounds. -/
theorem clr_scaled_hasSmoothBounds {d : ℕ} (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
    {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) :
    HasSmoothBounds (clrScaledData D hc hc1) (scaledEnvironmentLaw Q hc hc1) := by
  show ∀ᵐ ω ∂(scaledEnvironmentLaw Q hc hc1).measure, IsSmoothWithBounds D.derivativeBound ω
  rw [scaledEnvironmentLaw_measure]
  apply (scaleEnvironmentHomeomorph d c hc.ne').measurableEmbedding.ae_map_iff.mpr
  filter_upwards [hQ] with ω h
  exact clr_isSmoothWithBounds_scale (by rw [abs_of_pos hc]; exact hc1) h

theorem clr_reflect_eq_scale {d : ℕ} (ω : FieldPair d) :
    reflectEnvironment ω = scaleEnvironment (-1) ω := by
  apply Prod.ext <;> ext x <;>
    simp only [reflectEnvironment_matrix, reflectEnvironment_potential,
      scaleEnvironment_matrix, scaleEnvironment_potential, neg_one_smul]

/-- A reflected environment law keeps the smooth bounds. -/
theorem clr_reflected_hasSmoothBounds {d : ℕ} (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q) :
    HasSmoothBounds D (reflectedEnvironmentLaw Q) := by
  show ∀ᵐ ω ∂(reflectedEnvironmentLaw Q).measure, IsSmoothWithBounds D.derivativeBound ω
  rw [reflectedEnvironmentLaw_measure]
  apply (reflectEnvironmentHomeomorph d).measurableEmbedding.ae_map_iff.mpr
  filter_upwards [hQ] with ω h
  change IsSmoothWithBounds D.derivativeBound (reflectEnvironment ω)
  rw [clr_reflect_eq_scale]
  exact clr_isSmoothWithBounds_scale (by norm_num) h

/-- Physical velocity for every positive force, by contracting the law. -/
theorem clr_physical_velocity_pos
    (hpath : Blueprint.node_eq_u2E_reduced_u2D_generator_u23_pathwiseStmtV2)
    {d : ℕ} (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
    {lam : ℝ} (hlam : 0 < lam) (P : Kernel (FieldPair d) (Path d))
    (hP : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (physicalGenerator (firstCoordinateIndex hd) ω lam) 0 (P ω)) :
    ∃ v : Vec d, HasQuenchedVelocity Q.measure P v ∧
      0 < lam * v (firstCoordinateIndex hd) := by
  let c : ℝ := min 1 lam⁻¹
  have hc : 0 < c := lt_min zero_lt_one (inv_pos.mpr hlam)
  have hc1 : c ≤ 1 := min_le_left _ _
  have hmu0 : 0 < c * lam := mul_pos hc hlam
  have hmu1 : c * lam ≤ 1 := by
    calc
      c * lam ≤ lam⁻¹ * lam := mul_le_mul_of_nonneg_right (min_le_right _ _) hlam.le
      _ = 1 := inv_mul_cancel₀ hlam.ne'
  let Qs := scaledEnvironmentLaw Q hc hc1
  let Ps := scaledEnvironmentKernel P c hc
  have hPs : ∀ᵐ ω ∂Qs.measure,
      SolvesMartingaleProblem (physicalGenerator (firstCoordinateIndex hd) ω (c * lam))
        0 (Ps ω) := solvesMartingaleProblem_scaledJointLaw _ lam c hc hP
  obtain ⟨v, hv, hpos⟩ := clr_physical_velocity_unit hpath hd (clrScaledData D hc hc1) Qs
    (clr_scaled_hasSmoothBounds D Q hQ hc hc1) hmu0 hmu1 Ps hPs
  have hback := quenchedVelocity_of_reindex
    (scaleEnvironmentHomeomorph d c hc.ne').toMeasurableEquiv
    (inv_ne_zero hc.ne')
    (sq_pos_of_pos (show (0 : ℝ≥0) < NNReal.mk c hc.le from hc)) hv
  have hscalar : (c⁻¹)⁻¹ * (((NNReal.mk c hc.le) ^ (2 : ℕ) : ℝ≥0) : ℝ)⁻¹ = c⁻¹ := by
    simp only [inv_inv, pow_two, NNReal.coe_mul, NNReal.coe_mk, mul_inv_rev]
    rw [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]
  rw [hscalar] at hback
  refine ⟨c⁻¹ • v, hback, ?_⟩
  exact mul_pos hlam (mul_pos (inv_pos.mpr hc) hpos)

/-- Physical velocity for every nonzero force, by reflecting the law. -/
theorem clr_physical_velocity_signed
    (hpath : Blueprint.node_eq_u2E_reduced_u2D_generator_u23_pathwiseStmtV2)
    {d : ℕ} (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
    {lam : ℝ} (hlam : lam ≠ 0) (P : Kernel (FieldPair d) (Path d))
    (hP : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (physicalGenerator (firstCoordinateIndex hd) ω lam) 0 (P ω)) :
    ∃ v : Vec d, HasQuenchedVelocity Q.measure P v ∧
      0 < lam * v (firstCoordinateIndex hd) := by
  rcases lt_or_gt_of_ne hlam with hneg | hpos
  · let e := (reflectEnvironmentHomeomorph d).toMeasurableEquiv
    let Qr := reflectedEnvironmentLaw Q
    let Pr := reindexVelocityKernel P e (-1) 1
    have hPr : ∀ᵐ ω ∂Qr.measure,
        SolvesMartingaleProblem (physicalGenerator (firstCoordinateIndex hd) ω (-lam))
          0 (Pr ω) := by
      apply e.measurableEmbedding.ae_map_iff.mpr
      filter_upwards [hP] with ω hω
      rw [reindexVelocityKernel_apply]
      change SolvesMartingaleProblem
        (physicalGenerator (firstCoordinateIndex hd) (reflectEnvironment ω) (-lam)) 0
        ((P ω).map (velocityPathTransform (-1) 1))
      simpa only [neg_zero] using
        solvesMartingaleProblem_reflectedPath (firstCoordinateIndex hd) ω lam 0 hω
    obtain ⟨v, hv, hsign⟩ := clr_physical_velocity_pos hpath hd D Qr
      (clr_reflected_hasSmoothBounds D Q hQ) (neg_pos.mpr hneg) Pr hPr
    have hback := quenchedVelocity_of_reindex e (a := -1) (by norm_num)
      (b := 1) (by norm_num) hv
    have hv' : HasQuenchedVelocity Q.measure P (-v) := by
      simpa only [inv_neg, inv_one, NNReal.coe_one, mul_one, neg_one_smul] using hback
    refine ⟨-v, hv', ?_⟩
    simpa only [Pi.neg_apply, neg_mul, mul_neg] using hsign
  · exact clr_physical_velocity_pos hpath hd D Q hQ hpos P hP


/-- The zero-potential reduced pair of a smooth pair is smooth. -/
theorem clr_isSmoothFieldPair_flat {d : ℕ} {ω : FieldPair d} (h : IsSmoothFieldPair ω) :
    IsSmoothFieldPair (flatReducedEnvironment ω) := by
  refine ⟨fun j k => ?_, ?_⟩
  · change ContDiff ℝ (⊤ : ℕ∞) (fun x => (clockDensity ω x • ω.1 x) j k)
    simp only [Matrix.smul_apply, smul_eq_mul, clockDensity]
    exact (Real.contDiff_exp.comp (contDiff_const.mul h.2)).mul (h.1 j k)
  · change ContDiff ℝ (⊤ : ℕ∞) (fun _ : Vec d => (0 : ℝ))
    exact contDiff_const

/-- Reduced velocity for forces in `(0,1]` on a smooth environment law, through the
zero-potential reduced environment law. -/
theorem clr_reduced_velocity_unit
    (hpath : Blueprint.node_eq_u2E_reduced_u2D_generator_u23_pathwiseStmtV2)
    {d : ℕ} (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
    {lam : ℝ} (h0 : 0 < lam) (h1 : lam ≤ 1) (P : Kernel (FieldPair d) (Path d))
    (hP : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator (firstCoordinateIndex hd) ω lam) 0 (P ω)) :
    ∃ v : Vec d, HasQuenchedVelocity Q.measure P v ∧
      0 < v (firstCoordinateIndex hd) := by
  let Qf := flatReducedEnvironmentLaw Q
  have hfm := measurable_flatReducedEnvironment (d := d)
  have hsmf : ∀ᵐ ω ∂Qf.measure, IsSmoothFieldPair ω := by
    rw [flatReducedEnvironmentLaw_measure]
    exact (ae_map_iff hfm.aemeasurable Sharpness.measurableSet_isSmoothFieldPair_fieldPair).mpr
      (hQ.mono fun ω h => clr_isSmoothFieldPair_flat h.1)
  obtain ⟨K, -, hsrc, hKmp⟩ := u2_foundation_smooth_gmp_physical_origin_law_and_mp hd
    (one_le_sourceReducedBound D.one_le_ellipticity) Qf lam h0.le h1 hsmf
  obtain ⟨v, hv, hpos, -⟩ := Regeneration.gmp_physical_origin_velocity hd Qf h0 h1 K hsrc
  let Z : QuenchedPathLaws d := K.comap (fun z => flatReducedEnvironment z.2)
    (hfm.comp measurable_snd)
  have hZ : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator (firstCoordinateIndex hd) ω lam) 0 (Z (0, ω)) := by
    have hpull : ∀ᵐ ω ∂Q.measure, SolvesMartingaleProblem
        (physicalGenerator (firstCoordinateIndex hd) (flatReducedEnvironment ω) lam) 0
        (K (flatReducedEnvironment ω)) := by
      have hKm : ∀ᵐ ω' ∂Q.measure.map flatReducedEnvironment, SolvesMartingaleProblem
          (physicalGenerator (firstCoordinateIndex hd) ω' lam) 0 (K ω') := hKmp
      exact ae_of_ae_map hfm.aemeasurable hKm
    filter_upwards [hpull] with ω hω
    rw [flatReducedEnvironment_eq_zeroPotentialReducedPair,
      Blueprint.physicalGenerator_zeroPotentialReducedPair] at hω
    exact hω
  have hvZ : HasQuenchedVelocity Q.measure (originLaw Z) v := by
    have hvm : ∀ᵐ ω' ∂Q.measure.map flatReducedEnvironment, ∀ᵐ γ ∂K ω', HasPathVelocity γ v := hv
    exact ae_of_ae_map hfm.aemeasurable hvm
  have heq := clr_reduced_mp_unique_smooth hpath hd D Q hQ _ lam
    (P.comap Prod.snd measurable_snd) Z hP hZ
  refine ⟨v, ?_, hpos⟩
  filter_upwards [heq, hvZ] with ω he hω
  change ∀ᵐ γ ∂P ω, HasPathVelocity γ v
  change P ω = Z (0, ω) at he
  rw [he]
  exact hω

theorem clr_flat_scale {d : ℕ} (c : ℝ) (ω : FieldPair d) :
    flatReducedEnvironment (scaleEnvironment c ω) = scaleEnvironment c (flatReducedEnvironment ω) := by
  apply Prod.ext <;> ext x <;> rfl

theorem clr_flat_reflect {d : ℕ} (ω : FieldPair d) :
    flatReducedEnvironment (reflectEnvironment ω) = reflectEnvironment (flatReducedEnvironment ω) := by
  apply Prod.ext <;> ext x <;> rfl

/-- The reduced martingale problem under contraction of the joint law. -/
theorem clr_reduced_mp_scaledJointLaw {d : ℕ} (i : Fin d) {Q : Measure (FieldPair d)}
    {P : Kernel (FieldPair d) (Path d)} (lam c : ℝ) (hc : 0 < c)
    (hP : ∀ᵐ ω ∂Q, SolvesMartingaleProblem (reducedGenerator i ω lam) 0 (P ω)) :
    ∀ᵐ ω ∂Q.map (scaleEnvironment c),
      SolvesMartingaleProblem (reducedGenerator i ω (c * lam)) 0
        (scaledEnvironmentKernel P c hc ω) := by
  apply (scaleEnvironmentHomeomorph d c hc.ne').measurableEmbedding.ae_map_iff.mpr
  filter_upwards [hP] with ω hω
  change SolvesMartingaleProblem
    (reducedGenerator i (scaleEnvironment c ω) (c * lam)) 0
    (scaledEnvironmentKernel P c hc (scaleEnvironment c ω))
  rw [scaledEnvironmentKernel_apply, ← Blueprint.physicalGenerator_zeroPotentialReducedPair,
    ← flatReducedEnvironment_eq_zeroPotentialReducedPair, clr_flat_scale]
  rw [← Blueprint.physicalGenerator_zeroPotentialReducedPair,
    ← flatReducedEnvironment_eq_zeroPotentialReducedPair] at hω
  simpa only [smul_zero] using
    solvesMartingaleProblem_scaledPath i (flatReducedEnvironment ω) lam c hc 0 hω


/-- The reduced martingale problem under reflection of the joint law. -/
theorem clr_reduced_mp_reflectedJointLaw {d : ℕ} (i : Fin d) {Q : Measure (FieldPair d)}
    {P : Kernel (FieldPair d) (Path d)} (lam : ℝ)
    (hP : ∀ᵐ ω ∂Q, SolvesMartingaleProblem (reducedGenerator i ω lam) 0 (P ω)) :
    ∀ᵐ ω ∂Q.map reflectEnvironment,
      SolvesMartingaleProblem (reducedGenerator i ω (-lam)) 0
        (reindexVelocityKernel P (reflectEnvironmentHomeomorph d).toMeasurableEquiv (-1) 1 ω) := by
  apply (reflectEnvironmentHomeomorph d).toMeasurableEquiv.measurableEmbedding.ae_map_iff.mpr
  filter_upwards [hP] with ω hω
  rw [reindexVelocityKernel_apply]
  change SolvesMartingaleProblem
    (reducedGenerator i (reflectEnvironment ω) (-lam)) 0
    ((P ω).map (velocityPathTransform (-1) 1))
  rw [← Blueprint.physicalGenerator_zeroPotentialReducedPair,
    ← flatReducedEnvironment_eq_zeroPotentialReducedPair, clr_flat_reflect]
  rw [← Blueprint.physicalGenerator_zeroPotentialReducedPair,
    ← flatReducedEnvironment_eq_zeroPotentialReducedPair] at hω
  simpa only [neg_zero] using
    solvesMartingaleProblem_reflectedPath i (flatReducedEnvironment ω) lam 0 hω

/-- Reduced velocity for every positive force, by contracting the law. -/
theorem clr_reduced_velocity_pos
    (hpath : Blueprint.node_eq_u2E_reduced_u2D_generator_u23_pathwiseStmtV2)
    {d : ℕ} (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
    {lam : ℝ} (hlam : 0 < lam) (P : Kernel (FieldPair d) (Path d))
    (hP : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator (firstCoordinateIndex hd) ω lam) 0 (P ω)) :
    ∃ v : Vec d, HasQuenchedVelocity Q.measure P v ∧
      0 < lam * v (firstCoordinateIndex hd) := by
  let c : ℝ := min 1 lam⁻¹
  have hc : 0 < c := lt_min zero_lt_one (inv_pos.mpr hlam)
  have hc1 : c ≤ 1 := min_le_left _ _
  have hmu0 : 0 < c * lam := mul_pos hc hlam
  have hmu1 : c * lam ≤ 1 := by
    calc
      c * lam ≤ lam⁻¹ * lam := mul_le_mul_of_nonneg_right (min_le_right _ _) hlam.le
      _ = 1 := inv_mul_cancel₀ hlam.ne'
  let Qs := scaledEnvironmentLaw Q hc hc1
  let Ps := scaledEnvironmentKernel P c hc
  have hPs : ∀ᵐ ω ∂Qs.measure,
      SolvesMartingaleProblem (reducedGenerator (firstCoordinateIndex hd) ω (c * lam))
        0 (Ps ω) := clr_reduced_mp_scaledJointLaw _ lam c hc hP
  obtain ⟨v, hv, hpos⟩ := clr_reduced_velocity_unit hpath hd (clrScaledData D hc hc1) Qs
    (clr_scaled_hasSmoothBounds D Q hQ hc hc1) hmu0 hmu1 Ps hPs
  have hback := quenchedVelocity_of_reindex
    (scaleEnvironmentHomeomorph d c hc.ne').toMeasurableEquiv
    (inv_ne_zero hc.ne')
    (sq_pos_of_pos (show (0 : ℝ≥0) < NNReal.mk c hc.le from hc)) hv
  have hscalar : (c⁻¹)⁻¹ * (((NNReal.mk c hc.le) ^ (2 : ℕ) : ℝ≥0) : ℝ)⁻¹ = c⁻¹ := by
    simp only [inv_inv, pow_two, NNReal.coe_mul, NNReal.coe_mk, mul_inv_rev]
    rw [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]
  rw [hscalar] at hback
  refine ⟨c⁻¹ • v, hback, ?_⟩
  exact mul_pos hlam (mul_pos (inv_pos.mpr hc) hpos)

/-- Reduced velocity for every nonzero force, by reflecting the law. -/
theorem clr_reduced_velocity_signed
    (hpath : Blueprint.node_eq_u2E_reduced_u2D_generator_u23_pathwiseStmtV2)
    {d : ℕ} (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
    {lam : ℝ} (hlam : lam ≠ 0) (P : Kernel (FieldPair d) (Path d))
    (hP : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator (firstCoordinateIndex hd) ω lam) 0 (P ω)) :
    ∃ v : Vec d, HasQuenchedVelocity Q.measure P v ∧
      0 < lam * v (firstCoordinateIndex hd) := by
  rcases lt_or_gt_of_ne hlam with hneg | hpos
  · let e := (reflectEnvironmentHomeomorph d).toMeasurableEquiv
    let Qr := reflectedEnvironmentLaw Q
    let Pr := reindexVelocityKernel P e (-1) 1
    have hPr : ∀ᵐ ω ∂Qr.measure,
        SolvesMartingaleProblem (reducedGenerator (firstCoordinateIndex hd) ω (-lam))
          0 (Pr ω) := clr_reduced_mp_reflectedJointLaw _ lam hP
    obtain ⟨v, hv, hsign⟩ := clr_reduced_velocity_pos hpath hd D Qr
      (clr_reflected_hasSmoothBounds D Q hQ) (neg_pos.mpr hneg) Pr hPr
    have hback := quenchedVelocity_of_reindex e (a := -1) (by norm_num)
      (b := 1) (by norm_num) hv
    have hv' : HasQuenchedVelocity Q.measure P (-v) := by
      simpa only [inv_neg, inv_one, NNReal.coe_one, mul_one, neg_one_smul] using hback
    refine ⟨-v, hv', ?_⟩
    simpa only [Pi.neg_apply, neg_mul, mul_neg] using hsign
  · exact clr_reduced_velocity_pos hpath hd D Q hQ hpos P hP

end EinsteinFull

namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- `eq.time-change-identities#forced-lln`, smooth-scope version: both supplied laws have
strictly signed deterministic velocities for every nonzero force. The reduced-bounds
premise is retained in its graph position. -/
@[nolint unusedArguments]
theorem node_eq_u2E_time_u2D_change_u2D_identities_u23_forced_u2D_lln_of_deps
    (hpath : node_eq_u2E_reduced_u2D_generator_u23_pathwiseStmtV2)
    (_hbounds : node_eq_u2E_reduced_u2D_boundsStmt) :
    node_eq_u2E_time_u2D_change_u2D_identities_u23_forced_u2D_llnStmtV2 := by
  intro d hd Λ₀ r₀ b Q hΛ hr hb hsm lam hlam X Y hX hY
  let D : StructuralData d := ⟨Λ₀, r₀, b, hΛ, hr, hb⟩
  have hQ : HasSmoothBounds D Q := hsm
  have hi : External.GantertSection7Support.firstCoordinateIndex hd = (⟨0, by omega⟩ : Fin d) :=
    Fin.ext rfl
  obtain ⟨vX, hvX, hsX⟩ := clr_physical_velocity_signed hpath hd D Q hQ hlam (originLaw X)
    (by rw [hi]; exact hX)
  obtain ⟨vY, hvY, hsY⟩ := clr_reduced_velocity_signed hpath hd D Q hQ hlam (originLaw Y)
    (by rw [hi]; exact hY)
  rw [hi] at hsX hsY
  exact ⟨vX, vY, hvX, hvY, hsX, hsY⟩

end EinsteinFull.Blueprint
