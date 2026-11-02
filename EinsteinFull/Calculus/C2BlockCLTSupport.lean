import EinsteinFull.Calculus.C2BlockBoundarySupport
import EinsteinFull.External.AKMBlockClt

/-! Source CLT transport to the literal physical matrix-clock block. -/
open MeasureTheory ProbabilityTheory
noncomputable section
namespace EinsteinFull.Calculus.C2BlockCLT
open EinsteinRelation EinsteinRelation.External.AKM
open EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinFull.Blueprint EinsteinFull.External.Source.AKM
open EinsteinFull.Calculus.C2BlockBoundary

/-- A smaller structural source exponent absorbs the physical range dilation. -/
theorem clt_source_scale_threshold
    {r₀ η η' : ℝ} (hr₀ : 1 ≤ r₀) (hη : 0 < η) (hη' : 0 ≤ η') (hgap : η' < η) :
    ∃ L₀ : ℝ, 2 ≤ L₀ ∧ ∀ L : ℝ, L₀ ≤ L →
      1 ≤ L / r₀ ∧ 2 ≤ L ^ η / r₀ ∧ (L / r₀) ^ η' ≤ L ^ η / r₀ := by
  have hr₀0 : 0 < r₀ := lt_of_lt_of_le zero_lt_one hr₀
  obtain ⟨A, hA⟩ := Filter.eventually_atTop.1
    ((tendsto_rpow_atTop hη).eventually_ge_atTop (2 * r₀))
  obtain ⟨B, hB⟩ := Filter.eventually_atTop.1
    ((tendsto_rpow_atTop (sub_pos.mpr hgap)).eventually_ge_atTop r₀)
  refine ⟨max 2 (max r₀ (max A B)), le_max_left _ _, ?_⟩
  intro L hL
  have hL2 := (le_max_left 2 _).trans hL
  have hL0 : 0 < L := by linarith
  have hrest := (le_max_right 2 _).trans hL
  have hrL := (le_max_left r₀ _).trans hrest
  have hAB := (le_max_right r₀ _).trans hrest
  have hLA := (le_max_left A B).trans hAB
  have hLB := (le_max_right A B).trans hAB
  refine ⟨(one_le_div hr₀0).2 hrL, (le_div_iff₀ hr₀0).2 (hA L hLA), ?_⟩
  apply (Real.rpow_le_rpow (div_nonneg hL0.le hr₀0.le)
    (div_le_self hL0.le hr₀) hη').trans
  apply (le_div_iff₀ hr₀0).2
  calc L ^ η' * r₀ ≤ L ^ η' * L ^ (η - η') :=
        mul_le_mul_of_nonneg_left (hB L hLB) (Real.rpow_nonneg hL0.le _)
    _ = L ^ η := by rw [← Real.rpow_add hL0]; congr 1; ring

/-- The source exponent is strictly inside the admissible window. -/
theorem clt_intermediate_exponent
    {d : ℕ} (hd : 2 ≤ d) {D : StructuralData d} {s δ γ η β : ℝ}
    (h : covarianceWindow d D s δ γ η β) :
    ∃ η' : ℝ, 0 < η' ∧ η' < η ∧ blockParameterWindow d s δ γ η' := by
  have hw := covarianceWindow_blockParameterWindow hd h
  have hγ : 0 < γ := by
    have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
    have hδ := h.2.2.2.1
    exact lt_trans (by positivity : (0 : ℝ) < (d : ℝ) / 2 * (1 + δ)) h.2.2.2.2.1
  have he : max (1 / 2 : ℝ) ((d : ℝ) / (2 * γ)) < η :=
    max_lt hw.2.2.2.2.2.1 h.2.2.2.2.2.2.1
  obtain ⟨η', hlo, hhi⟩ := exists_between he
  have hhalf := (le_max_left (1 / 2 : ℝ) _).trans_lt hlo
  have hdiv := (le_max_right (1 / 2 : ℝ) _).trans_lt hlo
  have hprod := (div_lt_iff₀ (by positivity : 0 < 2 * γ)).mp hdiv
  refine ⟨η', by linarith, hhi, hw.1, hw.2.1, hw.2.2.1, hw.2.2.2.1,
    hw.2.2.2.2.1, hhalf, ?_, hhi.trans hw.2.2.2.2.2.2.2⟩
  nlinarith only [hprod]

/-- The approved scalar source CLT uses the exact selected family. -/
theorem centeredSourceBlock_clt_osBound
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (s δ γ η β : ℝ) (h : covarianceWindow d D s δ γ η β)
    (η' : ℝ) (hw : blockParameterWindow d s δ γ η') :
    ∃ C : ℝ, 0 < C ∧
      ∀ Q : EnvironmentLaw d D.ellipticity D.dependenceRange,
      ∀ (R r : ℝ), 1 ≤ R → 2 ≤ r → R ^ η' ≤ r → r ≤ R →
      ∀ (z p q : Vec d), euclideanNorm p < 1 → euclideanNorm q < 1 →
      ∀ f : Vec d → ℝ, Measurable f → (∀ y, |f y| ≤ 1) →
      OsBound (actualCoefficientLaw Q) (fun a => |sourceCenteredBlock (actualCoefficientLaw Q)
        (covarianceSourceLocalizedEnergy d hd D s δ γ η β h Q) a z R r f p q|)
        s (C * R ^ (-(d : ℝ) / 2)) := by
  obtain ⟨C, hC, hb⟩ := EinsteinFull.External.akm_block_clt d hd
    (AKMUpperEllipticity D.ellipticity) s δ γ η' h.1 hw
  refine ⟨C, hC, ?_⟩
  intro Q R r hR hr hlo hhi z p q hp hq f hf hfb
  simpa only [covarianceSourceLocalizedEnergy_eq_sourceSelectedLocalizedEnergy]
    using hb (actualCoefficientLaw Q) (lawHypotheses_actualCoefficientLaw Q)
      R r hR hr hlo hhi z p q hp hq f hf hfb

theorem centeredSourceBlock_clt_L2
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (s δ γ η β : ℝ) (h : covarianceWindow d D s δ γ η β)
    (η' : ℝ) (hw : blockParameterWindow d s δ γ η') :
    ∃ C : ℝ, 0 < C ∧
      ∀ Q : EnvironmentLaw d D.ellipticity D.dependenceRange,
      ∀ (R r : ℝ), 1 ≤ R → 2 ≤ r → R ^ η' ≤ r → r ≤ R →
      ∀ (z p q : Vec d), euclideanNorm p < 1 → euclideanNorm q < 1 →
      ∀ f : Vec d → ℝ, Measurable f → (∀ y, |f y| ≤ 1) →
      let X := fun a => sourceCenteredBlock (actualCoefficientLaw Q)
        (covarianceSourceLocalizedEnergy d hd D s δ γ η β h Q) a z R r f p q
      MemLp X 2 (actualCoefficientLaw Q) ∧
        Real.sqrt (∫ a, (X a) ^ 2 ∂actualCoefficientLaw Q) ≤
          C * R ^ (-(d : ℝ) / 2) := by
  obtain ⟨C, hC, hbound⟩ := centeredSourceBlock_clt_osBound d hd D s δ γ η β h η' hw
  let M := Real.sqrt (2 * (2 / s) ^ (2 / s))
  have hM : 0 < M := Real.sqrt_pos.2
    (mul_pos (by norm_num) (Real.rpow_pos_of_pos (div_pos (by norm_num) (lt_trans zero_lt_one h.2.1)) _))
  refine ⟨M * C, mul_pos hM hC, ?_⟩
  intro Q R r hR hr hlo hhi z p q hp hq f hf hfb
  have hos := hbound Q R r hR hr hlo hhi z p q hp hq f hf hfb
  refine ⟨EinsteinFull.AKM.memLp_two_of_osBound hos
    (centeredSourceBlock_measurable d hd D s δ γ η β h Q z R r p q hf).aestronglyMeasurable, ?_⟩
  simpa only [M, mul_assoc, sq_abs] using EinsteinFull.AKM.sqrt_integral_sq_le_of_osBound hos

/-- Unit-load source estimates extend to the actual arbitrary polarization
loads by their proved common quadratic scaling, with the dependence exposed. -/
theorem centeredSourceBlock_clt_real_loads_L2
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (s δ γ η β : ℝ) (h : covarianceWindow d D s δ γ η β)
    (η' : ℝ) (hw : blockParameterWindow d s δ γ η') :
    ∃ C : ℝ, 0 < C ∧
      ∀ Q : EnvironmentLaw d D.ellipticity D.dependenceRange,
      ∀ (R r : ℝ), 1 ≤ R → 2 ≤ r → R ^ η' ≤ r → r ≤ R →
      ∀ (z p q : Vec d) (f : Vec d → ℝ), Measurable f → (∀ y, |f y| ≤ 1) →
      let X := fun a => sourceCenteredBlock (actualCoefficientLaw Q)
        (covarianceSourceLocalizedEnergy d hd D s δ γ η β h Q) a z R r f p q
      MemLp X 2 (actualCoefficientLaw Q) ∧
        Real.sqrt (∫ a, (X a) ^ 2 ∂actualCoefficientLaw Q) ≤
          (1 + euclideanNorm p + euclideanNorm q) ^ 2 * C *
            R ^ (-(d : ℝ) / 2) := by
  obtain ⟨C, hC, hbound⟩ := centeredSourceBlock_clt_L2 d hd D s δ γ η β h η' hw
  refine ⟨C, hC, ?_⟩
  intro Q R r hR hr hlo hhi z p q f hf hfb
  let t := 1 + euclideanNorm p + euclideanNorm q
  have ht : 0 < t := by dsimp [t, euclideanNorm]; positivity
  have hp : euclideanNorm (t⁻¹ • p) < 1 := by
    rw [TimeChange.euclideanNorm_smul, abs_of_pos (inv_pos.mpr ht), inv_mul_eq_div]
    apply (div_lt_one ht).2
    dsimp [t]
    have hq0 : 0 ≤ euclideanNorm q := Real.sqrt_nonneg _
    linarith
  have hq : euclideanNorm (t⁻¹ • q) < 1 := by
    rw [TimeChange.euclideanNorm_smul, abs_of_pos (inv_pos.mpr ht), inv_mul_eq_div]
    apply (div_lt_one ht).2
    dsimp [t]
    have hp0 : 0 ≤ euclideanNorm p := Real.sqrt_nonneg _
    linarith
  let Y := fun a => sourceCenteredBlock (actualCoefficientLaw Q)
    (covarianceSourceLocalizedEnergy d hd D s δ γ η β h Q) a z R r f (t⁻¹ • p) (t⁻¹ • q)
  have heq (a : Coefficient d (AKMUpperEllipticity D.ellipticity)) :
      sourceCenteredBlock (actualCoefficientLaw Q)
        (covarianceSourceLocalizedEnergy d hd D s δ γ η β h Q) a z R r f p q = t ^ 2 * Y a := by
    simpa only [smul_smul, mul_inv_cancel₀ ht.ne', one_smul, Y] using
      centeredSourceBlock_smul d hd D s δ γ η β h Q (actualCoefficientLaw Q)
        a z R r t (t⁻¹ • p) (t⁻¹ • q) f
  obtain ⟨hYm, hYb⟩ := hbound Q R r hR hr hlo hhi z (t⁻¹ • p) (t⁻¹ • q) hp hq f hf hfb
  dsimp only
  simp_rw [heq]
  refine ⟨hYm.const_mul (t ^ 2), ?_⟩
  simp_rw [mul_pow]
  rw [integral_const_mul, Real.sqrt_mul (sq_nonneg (t ^ 2)), Real.sqrt_sq (sq_nonneg t)]
  exact (mul_le_mul_of_nonneg_left hYb (sq_nonneg t)).trans_eq (by dsimp [t]; ring)


/-- The cube Jacobian and CLT normalization leave only the physical range factor. -/
theorem physical_source_clt_factor (d : ℕ) {L r₀ : ℝ} (hL : 0 < L) (hr₀ : 0 < r₀) :
    (L ^ (-(d : ℝ) / 2) * r₀ ^ d * (L / r₀) ^ d) *
      (L / r₀) ^ (-(d : ℝ) / 2) = r₀ ^ ((d : ℝ) / 2) := by
  simpa only [sub_self, zero_div, sub_zero, add_zero, neg_zero, Real.rpow_zero, mul_one]
    using physical_source_boundary_factor d 1 hL hr₀

theorem physicalSourceBlock_clt_L2
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (s δ γ η β : ℝ) (h : covarianceWindow d D s δ γ η β) :
    ∃ C L₀ : ℝ, 0 < C ∧ 2 ≤ L₀ ∧
      ∀ Q : EnvironmentLaw d D.ellipticity D.dependenceRange,
      ∀ L : ℝ, L₀ ≤ L → ∀ r : ℝ, L ^ η ≤ r → r ≤ L → ∀ (z p q : Vec d) (f : Vec d → ℝ),
      Measurable f → (∀ y, |f y| ≤ 1) →
      let F := fun a => L ^ (-(d : ℝ) / 2) * ∫ y in sourceBlockCube z L,
        f y * centeredLocalizedEnergy (actualCoefficientLaw Q)
          (covarianceSourceLocalizedEnergy d hd D s δ γ η β h Q) a
          (D.dependenceRange⁻¹ • y) (r / D.dependenceRange) p q
      Measurable F ∧ MemLp F 2 (actualCoefficientLaw Q) ∧
        Real.sqrt (∫ a, (F a) ^ 2 ∂actualCoefficientLaw Q) ≤
          (1 + euclideanNorm p + euclideanNorm q) ^ 2 * C := by
  obtain ⟨η', hη', hη'η, hw⟩ := clt_intermediate_exponent hd h
  obtain ⟨C, hC, hbound⟩ := centeredSourceBlock_clt_real_loads_L2 d hd D s δ γ η β h η' hw
  have hr₀ : 0 < D.dependenceRange := lt_of_lt_of_le zero_lt_one D.one_le_dependenceRange
  have hη : 0 < η := lt_trans (by norm_num) h.2.2.2.2.2.2.2.2.1
  obtain ⟨L₀, hL₀, hscale⟩ := clt_source_scale_threshold D.one_le_dependenceRange
    hη hη'.le hη'η
  refine ⟨C * D.dependenceRange ^ ((d : ℝ) / 2), L₀,
    mul_pos hC (Real.rpow_pos_of_pos hr₀ _), hL₀, ?_⟩
  intro Q L hLL r hrlo hrhi z p q f hf hfb
  have hL : 0 < L := by linarith
  obtain ⟨hR, hr, hlo⟩ := hscale L hLL
  have hrlo' : L ^ η / D.dependenceRange ≤ r / D.dependenceRange :=
    div_le_div_of_nonneg_right hrlo hr₀.le
  have hhi : r / D.dependenceRange ≤ L / D.dependenceRange :=
    div_le_div_of_nonneg_right hrhi hr₀.le
  let g : Vec d → ℝ := fun u => f (D.dependenceRange • u)
  have hg : Measurable g := hf.comp (measurable_id.const_smul D.dependenceRange)
  let Y := fun a => sourceCenteredBlock (actualCoefficientLaw Q)
    (covarianceSourceLocalizedEnergy d hd D s δ γ η β h Q) a
    (D.dependenceRange⁻¹ • z) (L / D.dependenceRange) (r / D.dependenceRange) g p q
  have hYm : Measurable Y := centeredSourceBlock_measurable d hd D s δ γ η β h Q
    _ _ _ p q hg
  obtain ⟨hY, hYb⟩ := hbound Q _ _ hR (hr.trans hrlo') (hlo.trans hrlo') hhi _ p q g hg (fun u => hfb _)
  let A := L ^ (-(d : ℝ) / 2) * D.dependenceRange ^ d * (L / D.dependenceRange) ^ d
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have heq (a : Coefficient d (AKMUpperEllipticity D.ellipticity)) :
      L ^ (-(d : ℝ) / 2) * (∫ y in sourceBlockCube z L,
        f y * centeredLocalizedEnergy (actualCoefficientLaw Q)
          (covarianceSourceLocalizedEnergy d hd D s δ γ η β h Q) a
          (D.dependenceRange⁻¹ • y) (r / D.dependenceRange) p q) = A * Y a :=
    normalized_centeredSourceLoad_rescale _ _ a z hL _ f p q hr₀
  dsimp only
  simp_rw [heq]
  refine ⟨hYm.const_mul A, hY.const_mul A, ?_⟩
  simp_rw [mul_pow]
  rw [integral_const_mul, Real.sqrt_mul (sq_nonneg A), Real.sqrt_sq hA]
  calc
    _ ≤ A * ((1 + euclideanNorm p + euclideanNorm q) ^ 2 * C *
        (L / D.dependenceRange) ^ (-(d : ℝ) / 2)) :=
      mul_le_mul_of_nonneg_left hYb hA
    _ = (1 + euclideanNorm p + euclideanNorm q) ^ 2 * C *
        (A * (L / D.dependenceRange) ^ (-(d : ℝ) / 2)) := by ring
    _ = _ := by rw [physical_source_clt_factor d hL hr₀]; ring

theorem physicalMatrixBlock_clt_L2
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (s δ γ η β : ℝ) (h : covarianceWindow d D s δ γ η β) :
    ∃ C L₀ : ℝ, 0 < C ∧ 2 ≤ L₀ ∧
      ∀ Q : EnvironmentLaw d D.ellipticity D.dependenceRange,
      ∀ L : ℝ, L₀ ≤ L → ∀ r : ℝ, L ^ η ≤ r → r ≤ L → ∀ (z : Vec d) (j k : Fin d) (f : Vec d → ℝ),
      Measurable f → (∀ y, |f y| ≤ 1) →
      let F := fun ω => covarianceBlock d hd D s δ γ η β h Q r L L z f ω (.inl (j, k))
      Measurable F ∧ MemLp F 2 (reducedLaw Q) ∧
        Real.sqrt (∫ ω, (F ω) ^ 2 ∂reducedLaw Q) ≤ C := by
  obtain ⟨C, L₀, hC, hL₀, hb⟩ := physicalSourceBlock_clt_L2 d hd D s δ γ η β h
  let t := (ellipticityScale D.ellipticity)⁻¹ / 2
  let W := 3 + ellipticityScale D.ellipticity * sourceReducedBound D.ellipticity
  have ht : 0 < t := by dsimp [t]; exact div_pos (inv_pos.mpr (ellipticityScale_pos D.one_le_ellipticity)) (by norm_num)
  have hW : 0 < W := by
    dsimp [W]
    have := Clock.sourceReducedBound_pos D.one_le_ellipticity
    have := ellipticityScale_pos D.one_le_ellipticity
    positivity
  refine ⟨t * (2 * W ^ 2 * C), L₀, by positivity, hL₀, ?_⟩
  intro Q L hL r hrlo hrhi z j k f hf hfb
  have hLpos : 0 < L := by linarith
  let q := (ellipticityScale D.ellipticity • homogenizedCoefficient Q).mulVec (unitVector j)
  let B := fun p a => L ^ (-(d : ℝ) / 2) * ∫ y in sourceBlockCube z L,
    f y * centeredLocalizedEnergy (actualCoefficientLaw Q)
      (covarianceSourceLocalizedEnergy d hd D s δ γ η β h Q) a
      (D.dependenceRange⁻¹ • y) (r / D.dependenceRange) p q
  obtain ⟨hpm, hp, hpb⟩ := hb Q L hL r hrlo hrhi z (unitVector j + unitVector k) q f hf hfb
  obtain ⟨hmm, hm, hmb⟩ := hb Q L hL r hrlo hrhi z (unitVector j - unitVector k) q f hf hfb
  have he : (fun ω => covarianceBlock d hd D s δ γ η β h Q r L L z f ω (.inl (j,k))) =
      covariancePhysicalLift Q (fun a => t * (B (unitVector j + unitVector k) a - B (unitVector j - unitVector k) a)) := by
    rw [physicalMatrixBlock_eq_lift d hd D s δ γ η β h Q r L L (by linarith) z j k hf zero_le_one (fun y _ => hfb y)]
    congr 1
    funext a
    dsimp [B, t]
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
  calc
    _ ≤ t * (Real.sqrt (∫ a, (B (unitVector j + unitVector k) a) ^ 2 ∂actualCoefficientLaw Q) +
        Real.sqrt (∫ a, (B (unitVector j - unitVector k) a) ^ 2 ∂actualCoefficientLaw Q)) :=
      mul_le_mul_of_nonneg_left (rootSecondMoment_sub_le hp hm) ht.le
    _ ≤ t * (((1 + euclideanNorm (unitVector j + unitVector k) + euclideanNorm q) ^ 2 +
        (1 + euclideanNorm (unitVector j - unitVector k) + euclideanNorm q) ^ 2) * C) := by
      apply mul_le_mul_of_nonneg_left _ ht.le
      nlinarith only [hpb, hmb]
    _ ≤ t * ((2 * W ^ 2) * C) := by
      gcongr
      dsimp [q, W] at *
      linarith
    _ = _ := by ring

/-- The literal isotropic clock coordinate has a uniform root-second moment. -/
theorem clockBlock_clt_L2
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (s δ γ η β : ℝ) (h : covarianceWindow d D s δ γ η β)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    {r : ℝ} (hr : 0 < r) {L : ℝ} (hL : 0 < L) (z : Vec d)
    {f : Vec d → ℝ} (hf : Measurable f) (hfb : ∀ y, |f y| ≤ 1) :
    MemLp (fun ω => covarianceBlock d hd D s δ γ η β h Q r L L z f ω (.inr ()))
      2 (reducedLaw Q) ∧
    Real.sqrt (∫ ω, (covarianceBlock d hd D s δ γ η β h Q r L L z f ω (.inr ())) ^ 2
      ∂reducedLaw Q) ≤ Real.sqrt (clockVarianceConstant d D.ellipticity D.dependenceRange) := by
  refine ⟨clockBlock_memLp d hd D s δ γ η β h Q hr L z hL.le hf zero_le_one
    (fun y _ => hfb y), ?_⟩
  apply Real.sqrt_le_sqrt
  simpa only [one_pow, mul_one] using S1.clock_block_sq_le d hd D s δ γ η β h Q hr z hL hf
    zero_le_one (fun y _ => hfb y)

theorem covarianceBlock_clt_unit_L2
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (s δ γ η β : ℝ) (h : covarianceWindow d D s δ γ η β) :
    ∃ C L₀ : ℝ, 0 < C ∧ 2 ≤ L₀ ∧
      ∀ Q : EnvironmentLaw d D.ellipticity D.dependenceRange,
      ∀ L : ℝ, L₀ ≤ L → ∀ r : ℝ, L ^ η ≤ r → r ≤ L → ∀ (z : Vec d) (f : Vec d → ℝ),
      Measurable f → (∀ y, |f y| ≤ 1) →
      let X := covarianceBlock d hd D s δ γ η β h Q r L L z f
      MemLp (fun ω => covarianceVectorSize (X ω)) 2 (reducedLaw Q) ∧
        covarianceL2Size (reducedLaw Q) X ≤ C := by
  classical
  obtain ⟨C, L₀, hC, hL₀, hm⟩ := physicalMatrixBlock_clt_L2 d hd D s δ γ η β h
  let K := Real.sqrt (clockVarianceConstant d D.ellipticity D.dependenceRange)
  let M := C + K
  have hK : 0 ≤ K := Real.sqrt_nonneg _
  have hM : 0 < M := add_pos_of_pos_of_nonneg hC hK
  have hcard : 0 < (Fintype.card (JointObservationIndex d) : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨Sum.inr ()⟩
  refine ⟨Real.sqrt (Fintype.card (JointObservationIndex d) : ℝ) * M,
    L₀, mul_pos (Real.sqrt_pos.mpr hcard) hM, hL₀, ?_⟩
  intro Q L hL r hrlo hrhi z f hf hfb
  have hLpos : 0 < L := by linarith
  have hrpos : 0 < r := (Real.rpow_pos_of_pos hLpos η).trans_le hrlo
  have hc := clockBlock_clt_L2 d hd D s δ γ η β h Q hrpos hLpos z hf hfb
  let X := covarianceBlock d hd D s δ γ η β h Q r L L z f
  have hcoord (i : JointObservationIndex d) : MemLp (fun ω => X ω i) 2 (reducedLaw Q) ∧
      Real.sqrt (∫ ω, (X ω i) ^ 2 ∂reducedLaw Q) ≤ M := by
    rcases i with ⟨j, k⟩ | u
    · obtain ⟨_, hp, hb⟩ := hm Q L hL r hrlo hrhi z j k f hf hfb
      refine ⟨hp, hb.trans ?_⟩
      exact (by dsimp [M]; linarith)
    · cases u
      refine ⟨hc.1, ?_⟩
      have hb : Real.sqrt (∫ ω, (X ω (.inr ())) ^ 2 ∂reducedLaw Q) ≤ K := by
        simpa only [mul_one] using hc.2
      exact hb.trans ((by dsimp [M]; linarith))
  have hv := covarianceVectorSize_L2_of_coordinates (reducedLaw Q) X
    (fun i => (hcoord i).1.aestronglyMeasurable) (fun i => (hcoord i).1)
    hM.le (fun i => (hcoord i).2)
  refine ⟨hv.1, ?_⟩
  simpa only [mul_assoc] using hv.2

theorem covarianceBlock_clt_L2
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (s δ γ η β : ℝ) (h : covarianceWindow d D s δ γ η β) :
    ∃ C L₀ : ℝ, 0 < C ∧ 2 ≤ L₀ ∧
      ∀ Q : EnvironmentLaw d D.ellipticity D.dependenceRange,
      ∀ L : ℝ, L₀ ≤ L → ∀ (z : Vec d) (f : Vec d → ℝ) (b : ℝ),
      Measurable f → 0 ≤ b → (∀ y ∈ clockBlockCube z L, |f y| ≤ b) →
      ∀ r : ℝ, L ^ η ≤ r → r ≤ L →
      let X := covarianceBlock d hd D s δ γ η β h Q r L L z f
      MemLp (fun ω => covarianceVectorSize (X ω)) 2 (reducedLaw Q) ∧
        covarianceL2Size (reducedLaw Q) X ≤ C * b := by
  obtain ⟨C, L₀, hC, hL₀, hbound⟩ := covarianceBlock_clt_unit_L2 d hd D s δ γ η β h
  refine ⟨C, L₀, hC, hL₀, ?_⟩
  intro Q L hL z f b hf hb hfb r hrlo hrhi
  by_cases hb0 : b = 0
  · have hfz : ∀ y ∈ clockBlockCube z L, f y = 0 * (0 : Vec d → ℝ) y := by
      intro y hy
      simpa only [zero_mul] using abs_nonpos_iff.mp (by simpa only [hb0] using hfb y hy)
    have he (ω : FieldPair d) (i : JointObservationIndex d) :
        covarianceBlock d hd D s δ γ η β h Q r L L z f ω i = 0 := by
      simpa only [zero_mul] using covarianceBlock_test_mul d hd D s δ γ η β h Q
        r L L z f 0 0 hfz ω i
    dsimp only
    simp_rw [covarianceL2Size, covarianceVectorSize, he]
    simp [hb0]
  · have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
    let g := (clockBlockCube z L).indicator (fun y => b⁻¹ * f y)
    have hg : Measurable g := (measurable_const.mul hf).indicator (measurableSet_clockBlockCube z L)
    have hgb : ∀ y, |g y| ≤ 1 := by
      intro y
      by_cases hy : y ∈ clockBlockCube z L
      · dsimp [g]
        rw [Set.indicator_of_mem hy, abs_mul, abs_of_pos (inv_pos.mpr hbpos)]
        exact (inv_mul_le_iff₀ hbpos).2 (by simpa only [mul_one] using hfb y hy)
      · simp only [g, Set.indicator_of_notMem hy, abs_zero, zero_le_one]
    obtain ⟨hLp, hsize⟩ := hbound Q L hL r hrlo hrhi z g hg hgb
    have he (ω : FieldPair d) (i : JointObservationIndex d) :
        covarianceBlock d hd D s δ γ η β h Q r L L z f ω i =
          b * covarianceBlock d hd D s δ γ η β h Q r L L z g ω i := by
      apply covarianceBlock_test_mul
      intro y hy
      dsimp [g]
      rw [Set.indicator_of_mem hy, ← mul_assoc, mul_inv_cancel₀ hb0, one_mul]
    have hn (ω : FieldPair d) :
        covarianceVectorSize (covarianceBlock d hd D s δ γ η β h Q r L L z f ω) =
        b * covarianceVectorSize (covarianceBlock d hd D s δ γ η β h Q r L L z g ω) := by
      simp_rw [show covarianceBlock d hd D s δ γ η β h Q r L L z f ω =
        (fun i => b * covarianceBlock d hd D s δ γ η β h Q r L L z g ω i) from funext (he ω)]
      rw [covarianceVectorSize_mul, abs_of_pos hbpos]
    dsimp only
    constructor
    · simpa only [hn] using hLp.const_mul b
    · unfold covarianceL2Size
      simp_rw [hn]
      rw [rootSecondMoment_const_mul, abs_of_pos hbpos]
      exact (mul_le_mul_of_nonneg_left hsize hb).trans_eq (by ring)


end EinsteinFull.Calculus.C2BlockCLT
