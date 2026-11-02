import EinsteinFull.Calculus.U2GMPEnvironmentRealization
import EinsteinFull.Calculus.PhysicalGaugeDomainSupport
import EinsteinFull.Calculus.C27RealForceRealization
import EinsteinRelation.Diffusion.PhysicalH1Representatives
import EinsteinFull.Work.W1.PhysicalFullSpaceZeroBoundarySupport

open EinsteinRelation MeasureTheory Filter
open EinsteinRelation.External.GantertSection7Support EinsteinRelation.SpatialDirichlet
open scoped ENNReal Topology

noncomputable section
namespace EinsteinFull

/-- The exponential gauge acting continuously on real force-weighted L². -/
def u2RealGaugeL2 {d : ℕ} (i : Fin d) (lam : ℝ) :
    Lp ℝ 2 (physicalForceMeasure i lam) →L[ℝ] Lp ℝ 2 (volume : Measure (Vec d)) :=
  (Complex.reCLM.compLpL 2 volume).comp
    (((physicalGaugeUnitary i lam).toLinearIsometry.toContinuousLinearMap.restrictScalars ℝ).comp
      (Complex.ofRealCLM.compLpL 2 (physicalForceMeasure i lam)))

/-- The real L² gauge has the literal exponential multiplier as representative. -/
theorem u2RealGaugeL2_coe {d : ℕ} (i : Fin d) (lam : ℝ)
    (f : Lp ℝ 2 (physicalForceMeasure i lam)) :
    (u2RealGaugeL2 i lam f : Vec d → ℝ) =ᵐ[volume]
      fun x => Real.exp (lam * x i) * f x := by
  let F := Complex.ofRealCLM.compLp f
  filter_upwards [Complex.reCLM.coeFn_compLp (physicalGaugeUnitary i lam F),
    physicalGaugeUnitary_coe i lam F,
    (volume_absolutelyContinuous_physicalForceMeasure i lam).ae_eq
      (Complex.ofRealCLM.coeFn_compLp f)] with x hr hg hf
  change (Complex.reCLM.compLp (physicalGaugeUnitary i lam F)) x = _
  rw [hr, hg]
  change F x = (f x : ℂ) at hf
  simp only [physicalGaugeMultiplier, Complex.reCLM_apply, hf,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

/-- Real force-graph embedding, following `u1_force_graph_complex`. -/
private theorem u2ForceGraphComplex {d : ℕ} (m : Measure (Vec d))
    (hm : m = volume ∨ ∃ (i : Fin d) (lam : ℝ), m = physicalForceMeasure i lam)
    (u : WeightedSobolevGraph m) :
    ∃ (f : Lp ℂ 2 m)
      (G : Fin d → Lp ℂ 2 m),
      IsPhysicalH1Graph m
        hm f G ∧
      (f : EinsteinRelation.Vec d → ℂ) =ᵐ[m]
        (fun x => (u.value x : ℂ)) ∧
      ∀ j, (G j : EinsteinRelation.Vec d → ℂ) =ᵐ[m]
        (fun x => (u.weakGradient x j : ℂ)) := by
  have hf : MemLp (fun x => (u.value x : ℂ)) 2
      m :=
    Complex.ofRealCLM.comp_memLp' u.value_memLp
  have hG (j : Fin d) : MemLp (fun x => (u.weakGradient x j : ℂ)) 2
      m :=
    Complex.ofRealCLM.comp_memLp' (Blueprint.gmpEuclideanMemLp_coordinate u.gradient_memLp j)
  let f := hf.toLp _
  let G (j : Fin d) := (hG j).toLp _
  refine ⟨f, G, ?_, hf.coeFn_toLp, fun j => (hG j).coeFn_toLp⟩
  rw [isPhysicalH1Graph_iff_representatives _ hm
    f G _ _ hf.coeFn_toLp (fun j => (hG j).coeFn_toLp)]
  constructor
  · intro j
    simpa only [Complex.ofReal_re] using u.distributionalGradient j
  · intro j
    simp only [Complex.ofReal_im]
    have hz : coordinateDerivative j (fun _ : EinsteinRelation.Vec d => (0 : ℝ)) = (fun _ => 0) := by
      funext x
      simp [EinsteinRelation.coordinateDerivative]
    simpa only [hz] using
      hasWeakPartialDerivative_of_contDiff j (fun _ : EinsteinRelation.Vec d => (0 : ℝ)) contDiff_const

/-- Real parts of a complex graph retain its full distributional gradient. -/
private def u2RealGraphOfComplex {d : ℕ} (m : Measure (Vec d))
    (hm : m = volume ∨ ∃ (i : Fin d) (lam : ℝ), m = physicalForceMeasure i lam)
    (F : Lp ℂ 2 m) (G : Fin d → Lp ℂ 2 m)
    (hG : IsPhysicalH1Graph m hm F G) : WeightedSobolevGraph m where
  value := fun x => (F x).re
  weakGradient := fun x => WithLp.toLp 2 (fun j => (G j x).re)
  value_memLp := by
    simpa only [Function.comp_def, Complex.reCLM_apply] using Complex.reCLM.comp_memLp' (Lp.memLp F)
  gradient_memLp := by
    apply memLp_piLp_iff.mpr
    intro j
    simpa only [PiLp.toLp_apply, Function.comp_def, Complex.reCLM_apply] using
      Complex.reCLM.comp_memLp' (Lp.memLp (G j))
  distributionalGradient := by
    intro j
    simpa only [WithLp.ofLp_toLp] using hG.1 j

/-- The full physical H¹ domain is transported by the signed exponential gauge. -/
theorem u2_regular_physical_H1_gauge_iff {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam : ℝ)
    (f : Vec d → ℝ) :
    physicalH1Member ω hd lam f ↔
      physicalH1Member ω hd 0
        (fun x => Real.exp (lam * x (firstCoordinateIndex hd)) * f x) := by
  let i := firstCoordinateIndex hd
  have hv (l : ℝ) : (volume : Measure (Vec d)) ≪ physicalReversibleMeasure ω hd l := by
    apply Measure.ae_le_iff_absolutelyContinuous.mp
    intro P hP
    exact (Blueprint.gmpPhysical_ae_iff_volume hd ω l P).mp hP
  have hp (l : ℝ) : physicalReversibleMeasure ω hd l ≪ (volume : Measure (Vec d)) :=
    withDensity_absolutelyContinuous _ _
  constructor
  · intro hf
    obtain ⟨u, hu⟩ := (physicalH1Member_iff_exists_graph ω hd lam f).mp hf
    obtain ⟨F, G, hG, hF, _⟩ := u2ForceGraphComplex (physicalForceMeasure i lam) (Or.inr ⟨i, lam, rfl⟩) u
    obtain ⟨H, hH, _⟩ := physicalH1Graph_gauge_forward i lam F G hG
    let w := u2RealGraphOfComplex volume (Or.inl rfl) (physicalGaugeUnitary i lam F) H hH
    apply (physicalH1Member_iff_exists_graph ω hd 0 _).mpr
    have hzero : EinsteinRelation.External.GantertSection7Support.physicalForceMeasure hd 0 = (volume : Measure (Vec d)) := physicalForceMeasure_zero i
    rw [hzero]
    refine ⟨w, (hp 0).ae_eq ?_⟩
    filter_upwards [physicalGaugeUnitary_coe i lam F,
      (volume_absolutelyContinuous_physicalForceMeasure i lam).ae_eq hF,
      (hv lam).ae_eq hu] with x hx hFx hux
    change ((physicalGaugeUnitary i lam F) x).re = _
    rw [hx]
    simp only [physicalGaugeMultiplier, hFx, hux, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero]
    rfl
  · intro hf
    obtain ⟨u, hu⟩ := (physicalH1Member_iff_exists_graph ω hd 0 _).mp hf
    let u0 : WeightedSobolevGraph (volume : Measure (Vec d)) :=
      ⟨u.value, u.weakGradient,
        by simpa only [show EinsteinRelation.External.GantertSection7Support.physicalForceMeasure hd 0 =
          (volume : Measure (Vec d)) from physicalForceMeasure_zero i] using u.value_memLp,
        by simpa only [show EinsteinRelation.External.GantertSection7Support.physicalForceMeasure hd 0 =
          (volume : Measure (Vec d)) from physicalForceMeasure_zero i] using u.gradient_memLp,
        u.distributionalGradient⟩
    obtain ⟨F, G, hG, hF, _⟩ := u2ForceGraphComplex volume (Or.inl rfl) u0
    change (F : Vec d → ℂ) =ᵐ[volume] (fun x => (u.value x : ℂ)) at hF
    obtain ⟨H, hH, _⟩ := physicalH1Graph_gauge_backward i lam F G hG
    let w := u2RealGraphOfComplex (physicalForceMeasure i lam) (Or.inr ⟨i, lam, rfl⟩)
      ((physicalGaugeUnitary i lam).symm F) H hH
    apply (physicalH1Member_iff_exists_graph ω hd lam f).mpr
    refine ⟨w, (hp lam).ae_eq ?_⟩
    filter_upwards [(volume_absolutelyContinuous_physicalForceMeasure i lam).ae_eq
        (physicalGaugeUnitary_symm_coe i lam F), hF, (hv 0).ae_eq hu] with x hx hFx hux
    change (((physicalGaugeUnitary i lam).symm F) x).re = _
    rw [hx]
    simp only [physicalGaugeMultiplier, hFx, hux, Complex.ofReal_mul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero]
    rw [← mul_assoc, ← Real.exp_add]
    simp [i]

theorem u2_integral_physical_reversible_gauge {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam : ℝ) (F : Vec d → ℝ) :
    (∫ x, F x ∂physicalReversibleMeasure ω hd lam) =
      ∫ x, Real.exp (lam * x (firstCoordinateIndex hd)) ^ 2 * F x
        ∂physicalReversibleMeasure ω hd 0 := by
  unfold physicalReversibleMeasure
  rw [integral_withDensity_eq_integral_toReal_smul
    (EinsteinRelation.physicalReversibleDensity_continuous ω hd lam).measurable.ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top),
    integral_withDensity_eq_integral_toReal_smul
    (EinsteinRelation.physicalReversibleDensity_continuous ω hd 0).measurable.ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [smul_eq_mul]
  apply integral_congr_ae
  filter_upwards with x
  rw [ENNReal.toReal_ofReal (EinsteinRelation.physicalReversibleDensity_pos ω hd lam x).le,
    ENNReal.toReal_ofReal (EinsteinRelation.physicalReversibleDensity_pos ω hd 0 x).le]
  simp only [physicalReversibleDensity, physicalForceWeight, mul_zero, zero_mul, Real.exp_zero, one_mul]
  have he : Real.exp (2 * lam * x (firstCoordinateIndex hd)) =
      Real.exp (lam * x (firstCoordinateIndex hd)) ^ 2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [he]
  ring

theorem u2_regular_compact_mul_generator_integrable {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (testForce : ℝ) (f g : Vec d → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f)
    (hg : Continuous g) (hgc : HasCompactSupport g) :
    Integrable (fun x => g x * physicalGenerator (firstCoordinateIndex hd) ω testForce f x)
      (physicalReversibleMeasure ω hd lam) := by
  let μ := physicalReversibleMeasure ω hd lam
  let : IsLocallyFiniteMeasure μ :=
    EinsteinFull.Work.W5.gantert_physicalMeasure_locallyFinite hd ω lam
  have hgint : Integrable g μ := hg.integrable_of_hasCompactSupport hgc
  obtain ⟨B, _, hB⟩ := sbxS4_physicalGenerator_bounded hd (firstCoordinateIndex hd)
    (by linarith : 0 < Λ) hω testForce hf hfc
  apply (hgint.norm.mul_const B).mono'
    ((hg.measurable.mul (measurable_physicalGenerator _ _ _ _)).aestronglyMeasurable)
  filter_upwards with x
  simpa only [Pi.mul_apply, Real.norm_eq_abs, abs_mul] using
    mul_le_mul_of_nonneg_left (hB x) (abs_nonneg (g x))

theorem u2_physical_generator_gauge_ae {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hω : IsRegular Λ ω) (f : Vec d → ℝ) (hf : ContDiff ℝ 2 f) :
    let i := firstCoordinateIndex hd
    let h : Vec d → ℝ := fun x => Real.exp (lam * x i)
    ∀ᵐ x ∂(volume : Measure (Vec d)),
      physicalGenerator i ω 0 (fun y => h y * f y) x -
        f x * physicalGenerator i ω 0 h x = h x * physicalGenerator i ω lam f x := by
  filter_upwards [c27_reduced_generator_exponential_conjugation_ae
    (by linarith : 0 < Λ) hω (firstCoordinateIndex hd) lam f hf] with x hx
  have h1 := clockDensity_mul_physicalGenerator (firstCoordinateIndex hd) ω 0
    (fun y => Real.exp (lam * y (firstCoordinateIndex hd)) * f y) x
  have h2 := clockDensity_mul_physicalGenerator (firstCoordinateIndex hd) ω 0
    (fun y => Real.exp (lam * y (firstCoordinateIndex hd))) x
  have h3 := clockDensity_mul_physicalGenerator (firstCoordinateIndex hd) ω lam f x
  have hc : 0 < clockDensity ω x := by simp [clockDensity, Real.exp_pos]
  rw [← h1, ← h2, ← h3] at hx
  apply (mul_left_cancel₀ (ne_of_gt hc))
  nlinarith [hx]

theorem u2_physical_generator_gauge_potential_ae {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hω : IsRegular Λ ω) :
    let i := firstCoordinateIndex hd
    let h : Vec d → ℝ := fun x => Real.exp (lam * x i)
    ∀ᵐ x ∂(volume : Measure (Vec d)),
      physicalGenerator i ω 0 h x = h x *
        (lam * physicalDrift ω i 0 x i + (lam ^ 2 / 2) * ω.1 x i i) := by
  filter_upwards [c27_reduced_generator_exponential_potential_ae
    (by linarith : 0 < Λ) hω (firstCoordinateIndex hd) lam] with x hx
  rw [physicalGenerator_eq_inv_mul, hx]
  simp only [physicalDrift, reducedCoefficient, Matrix.smul_apply, smul_eq_mul]
  have hc : clockDensity ω x ≠ 0 := (clockDensity_pos ω x).ne'
  field_simp
  <;> ring

theorem u2_regular_gauge_compact_generator_pairing {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (f g : Vec d → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g) :
    let i := firstCoordinateIndex hd
    let h := fun x : Vec d => Real.exp (lam * x i)
    let V := fun x : Vec d => lam * physicalDrift ω i 0 x i + (lam ^ 2 / 2) * ω.1 x i i
    (∫ x, g x * physicalGenerator i ω lam f x ∂physicalReversibleMeasure ω hd lam) =
      (∫ x, (h x * g x) * physicalGenerator i ω 0 (fun y => h y * f y) x
        ∂physicalReversibleMeasure ω hd 0) -
      ∫ x, V x * (h x * g x) * (h x * f x) ∂physicalReversibleMeasure ω hd 0 := by
  let i := firstCoordinateIndex hd
  let h : Vec d → ℝ := fun x => Real.exp (lam * x i)
  let V : Vec d → ℝ := fun x => lam * physicalDrift ω i 0 x i + (lam ^ 2 / 2) * ω.1 x i i
  let μ := physicalReversibleMeasure ω hd 0
  have hh : ContDiff ℝ (⊤ : ℕ∞) h := (contDiff_const.mul (contDiff_apply ℝ ℝ i)).exp
  have hfh : ContDiff ℝ (⊤ : ℕ∞) (fun x => h x * f x) := hh.mul hf
  have hfhc : HasCompactSupport (fun x => h x * f x) := hfc.mul_left
  have ha : Integrable (fun x => (h x ^ 2 * g x) * physicalGenerator i ω lam f x) μ :=
    u2_regular_compact_mul_generator_integrable hd ω 0 Λ hΛ hω lam f
      (fun x => h x ^ 2 * g x) hf hfc ((hh.continuous.pow 2).mul hg.continuous) hgc.mul_left
  have hb : Integrable (fun x => (h x * g x) * physicalGenerator i ω 0 (fun y => h y * f y) x) μ :=
    u2_regular_compact_mul_generator_integrable hd ω 0 Λ hΛ hω 0 (fun x => h x * f x)
      (fun x => h x * g x) hfh hfhc (hh.continuous.mul hg.continuous) hgc.mul_left
  have hpoint : ∀ᵐ x ∂μ,
      (h x ^ 2 * g x) * physicalGenerator i ω lam f x =
        (h x * g x) * physicalGenerator i ω 0 (fun y => h y * f y) x -
          V x * (h x * g x) * (h x * f x) := by
    have hac : μ ≪ (volume : Measure (Vec d)) := withDensity_absolutelyContinuous _ _
    filter_upwards [hac.ae_le (u2_physical_generator_gauge_ae hd ω lam Λ hΛ hω f (hf.of_le (by simp))),
      hac.ae_le (u2_physical_generator_gauge_potential_ae hd ω lam Λ hΛ hω)] with x hx hy
    change physicalGenerator i ω 0 (fun y => h y * f y) x -
      f x * physicalGenerator i ω 0 h x = h x * physicalGenerator i ω lam f x at hx
    change physicalGenerator i ω 0 h x = h x * V x at hy
    rw [hy] at hx
    have hmul := congrArg (fun z : ℝ => (h x * g x) * z) hx
    nlinarith [hmul]
  have hc : Integrable (fun x => V x * (h x * g x) * (h x * f x)) μ := by
    apply (hb.sub ha).congr
    filter_upwards [hpoint] with x hx
    dsimp only [Pi.sub_apply]
    linarith
  change (∫ x, g x * physicalGenerator i ω lam f x ∂physicalReversibleMeasure ω hd lam) =
    (∫ x, (h x * g x) * physicalGenerator i ω 0 (fun y => h y * f y) x ∂μ) -
      ∫ x, V x * (h x * g x) * (h x * f x) ∂μ
  rw [u2_integral_physical_reversible_gauge]
  calc
    (∫ x, h x ^ 2 * (g x * physicalGenerator i ω lam f x) ∂μ) =
        ∫ x, (h x ^ 2 * g x) * physicalGenerator i ω lam f x ∂μ := by
          apply integral_congr_ae
          filter_upwards with x
          ring
    _ = ∫ x, ((h x * g x) * physicalGenerator i ω 0 (fun y => h y * f y) x -
          V x * (h x * g x) * (h x * f x)) ∂μ := integral_congr_ae hpoint
    _ = _ := integral_sub hb hc

/-- The physical gauge potential is measurable and uniformly bounded. -/
theorem u2_regular_physical_gauge_potential_bounded {d : ℕ}
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hω : IsRegular Λ ω) (i : Fin d) :
    Measurable (fun x : Vec d =>
      lam * physicalDrift ω i 0 x i + (lam ^ 2 / 2) * ω.1 x i i) ∧
    ∃ C : ℝ, 0 < C ∧ ∀ x : Vec d,
      |lam * physicalDrift ω i 0 x i + (lam ^ 2 / 2) * ω.1 x i i| ≤ C := by
  obtain ⟨hm, M, hM, hb⟩ := c25_reduced_force_potential_bounded
    (by linarith : 0 < Λ) hω i lam
  have hc : Continuous (fun x : Vec d => (clockDensity ω x)⁻¹) := by
    have he : (fun x : Vec d => (clockDensity ω x)⁻¹) =
        (fun x => Real.exp (2 * ω.2 x)) := by
      funext x
      rw [clockDensity, ← Real.exp_neg]
      congr 1
      ring
    rw [he]
    exact Real.continuous_exp.comp (continuous_const.mul ω.2.continuous)
  have heq (x : Vec d) :
      lam * physicalDrift ω i 0 x i + (lam ^ 2 / 2) * ω.1 x i i =
        (clockDensity ω x)⁻¹ *
          (lam * forcedDrift (reducedCoefficient ω) i 0 x i +
            (lam ^ 2 / 2) * reducedCoefficient ω x i i) := by
    simp only [physicalDrift, reducedCoefficient, Matrix.smul_apply, smul_eq_mul]
    have hclock : clockDensity ω x ≠ 0 := (clockDensity_pos ω x).ne'
    field_simp
    <;> ring
  constructor
  · have hfun : (fun x : Vec d =>
        lam * physicalDrift ω i 0 x i + (lam ^ 2 / 2) * ω.1 x i i) =
        (fun x => (clockDensity ω x)⁻¹ *
          (lam * forcedDrift (reducedCoefficient ω) i 0 x i +
            (lam ^ 2 / 2) * reducedCoefficient ω x i i)) := funext heq
    rw [hfun]
    exact hc.measurable.mul hm
  · refine ⟨Real.exp (2 * Λ) * M + 1, by positivity, ?_⟩
    intro x
    rw [heq, abs_mul]
    calc
      |(clockDensity ω x)⁻¹| *
          |lam * forcedDrift (reducedCoefficient ω) i 0 x i +
            (lam ^ 2 / 2) * reducedCoefficient ω x i i|
          ≤ Real.exp (2 * Λ) * M := mul_le_mul
            (abs_clockDensity_inv_le hω x) (hb x) (abs_nonneg _) (Real.exp_pos _).le
      _ ≤ Real.exp (2 * Λ) * M + 1 := by linarith

/-- The physical gauge potential is an essentially bounded multiplier. -/
theorem u2_regular_physical_gauge_potential_memLp_top {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) :
    MemLp (fun x : Vec d => lam * physicalDrift ω (firstCoordinateIndex hd) 0 x
      (firstCoordinateIndex hd) + (lam ^ 2 / 2) * ω.1 x (firstCoordinateIndex hd)
      (firstCoordinateIndex hd)) ∞ (physicalReversibleMeasure ω hd 0) := by
  obtain ⟨hm, C, _, hC⟩ :=
    u2_regular_physical_gauge_potential_bounded ω lam Λ hΛ hω (firstCoordinateIndex hd)
  apply memLp_top_of_bound hm.aestronglyMeasurable C
  exact ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hC x

/-- Multiplication by the gauge potential is bounded on the actual physical L² space. -/
def u2PhysicalGaugePotentialMul {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) :
    Lp ℝ 2 (physicalReversibleMeasure ω hd 0) →L[ℝ]
      Lp ℝ 2 (physicalReversibleMeasure ω hd 0) :=
  (ContinuousLinearMap.mul ℝ ℝ).holderL (physicalReversibleMeasure ω hd 0) ∞ 2 2
    ((u2_regular_physical_gauge_potential_memLp_top hd ω lam Λ hΛ hω).toLp _)

/-- The bounded multiplier retains the original physical potential pointwise a.e. -/
theorem u2PhysicalGaugePotentialMul_coe {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd 0)) :
    (u2PhysicalGaugePotentialMul hd ω lam Λ hΛ hω f : Vec d → ℝ) =ᵐ[
      physicalReversibleMeasure ω hd 0] fun x =>
        (lam * physicalDrift ω (firstCoordinateIndex hd) 0 x (firstCoordinateIndex hd) +
          (lam ^ 2 / 2) * ω.1 x (firstCoordinateIndex hd) (firstCoordinateIndex hd)) * f x := by
  have hm := u2_regular_physical_gauge_potential_memLp_top hd ω lam Λ hΛ hω
  have hmul := (ContinuousLinearMap.mul ℝ ℝ).coeFn_holder (r := 2) (hm.toLp _) f
  filter_upwards [hm.coeFn_toLp, hmul] with x hx hy
  simpa only [u2PhysicalGaugePotentialMul, ContinuousLinearMap.holderL_apply_apply,
    ContinuousLinearMap.mul_apply', hx] using hy

/-- Gauge transport of the actual physical form on compact smooth tests. -/
theorem u2_regular_gauge_compact_form {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (f g : Vec d → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g) :
    let i := firstCoordinateIndex hd
    let h := fun x : Vec d => Real.exp (lam * x i)
    let V := fun x : Vec d => lam * physicalDrift ω i 0 x i + (lam ^ 2 / 2) * ω.1 x i i
    (∫ x, (1 / 2 : ℝ) * dot (gradient g x) ((ω.1 x).mulVec (gradient f x))
      ∂physicalReversibleMeasure ω hd lam) =
      (∫ x, (1 / 2 : ℝ) * dot (gradient (fun y => h y * g y) x)
        ((ω.1 x).mulVec (gradient (fun y => h y * f y) x))
        ∂physicalReversibleMeasure ω hd 0) +
      ∫ x, V x * (h x * g x) * (h x * f x) ∂physicalReversibleMeasure ω hd 0 := by
  let i := firstCoordinateIndex hd
  let h : Vec d → ℝ := fun x => Real.exp (lam * x i)
  have hh : ContDiff ℝ (⊤ : ℕ∞) h := (contDiff_const.mul (contDiff_apply ℝ ℝ i)).exp
  have hfh : ContDiff ℝ (⊤ : ℕ∞) (fun x => h x * f x) := hh.mul hf
  have hgh : ContDiff ℝ (⊤ : ℕ∞) (fun x => h x * g x) := hh.mul hg
  have hfhc : HasCompactSupport (fun x => h x * f x) := hfc.mul_left
  have hghc : HasCompactSupport (fun x => h x * g x) := hgc.mul_left
  have h1 := sbxS4_fullForm_compactTest hd (by linarith : 0 < Λ) hω lam hf hfc
    (C8GMP.compactTestGraph hd lam g hg hgc)
  have h2 := sbxS4_fullForm_compactTest hd (by linarith : 0 < Λ) hω 0 hfh hfhc
    (C8GMP.compactTestGraph hd 0 (fun x => h x * g x) hgh hghc)
  simp only [C8GMP.compactTestGraph_value, C8GMP.compactTestGraph_gradient] at h1 h2
  have hp := u2_regular_gauge_compact_generator_pairing hd ω lam Λ hΛ hω f g hf hfc hg hgc
  dsimp only at hp ⊢
  linarith

private def u2H1ValueMap {d : ℕ} (hd : 2 ≤ d) (lam : ℝ) :
    PhysicalH1Space hd lam →L[ℝ] Lp ℝ 2
      (EinsteinRelation.External.GantertSection7Support.physicalForceMeasure hd lam) :=
  (ContinuousLinearMap.fst ℝ _ _).comp
    ((WithLp.prodContinuousLinearEquiv 2 ℝ _ _).toContinuousLinearMap.comp
      (densityWeightedH1Submodule (physicalForceWeight hd lam)
        (physicalForceWeight_continuous hd lam) (physicalForceWeight_pos hd lam)).subtypeL)

private theorem u2H1ValueMap_injective {d : ℕ} (hd : 2 ≤ d) (lam : ℝ)
    (u v : PhysicalH1Space hd lam) (hv : u2H1ValueMap hd lam u = u2H1ValueMap hd lam v) :
    u = v := by
  have hv' : densityWeightedH1SpaceValue u = densityWeightedH1SpaceValue v := hv
  have hg : densityWeightedH1SpaceGradient u = densityWeightedH1SpaceGradient v := by
    apply Lp.ext
    exact densityWeightedGraph_gradient_ae_of_value_ae (physicalForceWeight hd lam)
      (physicalForceWeight_continuous hd lam) (physicalForceWeight_pos hd lam)
      (physicalH1SpaceRepresentative hd lam u) (physicalH1SpaceRepresentative hd lam v)
      (by rw [show (physicalH1SpaceRepresentative hd lam u).value =
        densityWeightedH1SpaceValue u from rfl,
        show (physicalH1SpaceRepresentative hd lam v).value =
        densityWeightedH1SpaceValue v from rfl, hv'])
  apply Subtype.ext
  apply (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).injective
  exact Prod.ext hv' hg

private def u2H1ZeroValueMap {d : ℕ} (hd : 2 ≤ d) :
    PhysicalH1Space hd 0 →L[ℝ] Lp ℝ 2 (volume : Measure (Vec d)) :=
  (u2RealGaugeL2 (firstCoordinateIndex hd) 0).comp (u2H1ValueMap hd 0)

private theorem u2H1ZeroValueMap_injective {d : ℕ} (hd : 2 ≤ d) :
    Function.Injective (u2H1ZeroValueMap hd) := by
  intro u v h
  apply u2H1ValueMap_injective hd 0
  apply Lp.ext
  have hu := u2RealGaugeL2_coe (firstCoordinateIndex hd) 0 (u2H1ValueMap hd 0 u)
  have hv := u2RealGaugeL2_coe (firstCoordinateIndex hd) 0 (u2H1ValueMap hd 0 v)
  have he : (u2H1ZeroValueMap hd u : Vec d → ℝ) =ᵐ[volume]
      (u2H1ZeroValueMap hd v : Vec d → ℝ) := by rw [h]
  have hm : physicalForceMeasure (firstCoordinateIndex hd) 0 ≪
      (volume : Measure (Vec d)) := withDensity_absolutelyContinuous _ _
  apply hm.ae_eq
  filter_upwards [hu, hv, he] with x hux hvx hx
  simp only [zero_mul, Real.exp_zero, one_mul] at hux hvx
  exact hux.symm.trans (hx.trans hvx)

private theorem u2H1Gauge_lift {d : ℕ} (hd : 2 ≤ d) (lam : ℝ)
    (u : PhysicalH1Space hd lam) :
    ∃ v : PhysicalH1Space hd 0, u2H1ZeroValueMap hd v =
      u2RealGaugeL2 (firstCoordinateIndex hd) lam (u2H1ValueMap hd lam u) := by
  let i := firstCoordinateIndex hd
  let w := physicalH1SpaceRepresentative hd lam u
  obtain ⟨F, G, hG, hF, _⟩ := u2ForceGraphComplex (physicalForceMeasure i lam)
    (Or.inr ⟨i, lam, rfl⟩) w
  obtain ⟨H, hH, _⟩ := physicalH1Graph_gauge_forward i lam F G hG
  let z := u2RealGraphOfComplex volume (Or.inl rfl) (physicalGaugeUnitary i lam F) H hH
  have hzero : EinsteinRelation.External.GantertSection7Support.physicalForceMeasure hd 0 =
      (volume : Measure (Vec d)) := physicalForceMeasure_zero i
  let z' : WeightedSobolevGraph
      (EinsteinRelation.External.GantertSection7Support.physicalForceMeasure hd 0) :=
    ⟨z.value, z.weakGradient, by rw [hzero]; exact z.value_memLp,
      by rw [hzero]; exact z.gradient_memLp, z.distributionalGradient⟩
  refine ⟨Blueprint.gmpH1FromGraph (physicalForceWeight hd 0) (physicalForceWeight_continuous hd 0)
    (physicalForceWeight_pos hd 0) z', ?_⟩
  apply Lp.ext
  have hz := Blueprint.gmpH1FromGraph_value_ae (physicalForceWeight hd 0)
    (physicalForceWeight_continuous hd 0) (physicalForceWeight_pos hd 0) z'
  have hz' : (u2H1ZeroValueMap hd (Blueprint.gmpH1FromGraph (physicalForceWeight hd 0)
      (physicalForceWeight_continuous hd 0) (physicalForceWeight_pos hd 0) z') : Vec d → ℝ)
      =ᵐ[volume] z.value := by
    have hzv := (volume_absolutelyContinuous_physicalForceMeasure i 0).ae_eq hz
    have hg := u2RealGaugeL2_coe i 0 (u2H1ValueMap hd 0
      (Blueprint.gmpH1FromGraph (physicalForceWeight hd 0)
        (physicalForceWeight_continuous hd 0) (physicalForceWeight_pos hd 0) z'))
    filter_upwards [hg, hzv] with x hx hy
    simp only [zero_mul, Real.exp_zero, one_mul] at hx
    change (u2RealGaugeL2 i 0 (u2H1ValueMap hd 0
      (Blueprint.gmpH1FromGraph (physicalForceWeight hd 0)
        (physicalForceWeight_continuous hd 0) (physicalForceWeight_pos hd 0) z'))) x = z'.value x
    exact hx.trans hy
  filter_upwards [hz', u2RealGaugeL2_coe i lam (u2H1ValueMap hd lam u),
    physicalGaugeUnitary_coe i lam F,
    (volume_absolutelyContinuous_physicalForceMeasure i lam).ae_eq hF] with x hx hy hF' hF''
  rw [hx, hy]
  change ((physicalGaugeUnitary i lam F) x).re = _
  rw [hF']
  simp only [physicalGaugeMultiplier, hF'', Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]
  rfl

private def u2H1GaugeLinear {d : ℕ} (hd : 2 ≤ d) (lam : ℝ) :
    PhysicalH1Space hd lam →ₗ[ℝ] PhysicalH1Space hd 0 where
  toFun u := Classical.choose (u2H1Gauge_lift hd lam u)
  map_add' u v := by
    apply u2H1ZeroValueMap_injective hd
    change u2H1ZeroValueMap hd (Classical.choose (u2H1Gauge_lift hd lam (u + v))) = _
    calc
      _ = u2RealGaugeL2 (firstCoordinateIndex hd) lam (u2H1ValueMap hd lam (u + v)) :=
        Classical.choose_spec (u2H1Gauge_lift hd lam (u + v))
      _ = u2RealGaugeL2 (firstCoordinateIndex hd) lam (u2H1ValueMap hd lam u) +
          u2RealGaugeL2 (firstCoordinateIndex hd) lam (u2H1ValueMap hd lam v) := by
        rw [map_add (u2H1ValueMap hd lam)]
        exact map_add (u2RealGaugeL2 (firstCoordinateIndex hd) lam) _ _
      _ = u2H1ZeroValueMap hd (Classical.choose (u2H1Gauge_lift hd lam u)) +
          u2H1ZeroValueMap hd (Classical.choose (u2H1Gauge_lift hd lam v)) :=
        congrArg₂ (· + ·) (Classical.choose_spec (u2H1Gauge_lift hd lam u)).symm
        (Classical.choose_spec (u2H1Gauge_lift hd lam v)).symm
      _ = _ := (map_add (u2H1ZeroValueMap hd) _ _).symm
  map_smul' c u := by
    apply u2H1ZeroValueMap_injective hd
    change u2H1ZeroValueMap hd (Classical.choose (u2H1Gauge_lift hd lam (c • u))) = _
    calc
      _ = u2RealGaugeL2 (firstCoordinateIndex hd) lam (u2H1ValueMap hd lam (c • u)) :=
        Classical.choose_spec (u2H1Gauge_lift hd lam (c • u))
      _ = c • u2RealGaugeL2 (firstCoordinateIndex hd) lam (u2H1ValueMap hd lam u) := by
        rw [map_smul (u2H1ValueMap hd lam)]
        exact map_smul (u2RealGaugeL2 (firstCoordinateIndex hd) lam) c _
      _ = c • u2H1ZeroValueMap hd (Classical.choose (u2H1Gauge_lift hd lam u)) :=
        congrArg (c • ·) (Classical.choose_spec (u2H1Gauge_lift hd lam u)).symm
      _ = _ := (map_smul (u2H1ZeroValueMap hd) c _).symm

private theorem u2H1GaugeLinear_value {d : ℕ} (hd : 2 ≤ d) (lam : ℝ)
    (u : PhysicalH1Space hd lam) :
    u2H1ZeroValueMap hd (u2H1GaugeLinear hd lam u) =
      u2RealGaugeL2 (firstCoordinateIndex hd) lam (u2H1ValueMap hd lam u) :=
  Classical.choose_spec (u2H1Gauge_lift hd lam u)

/-- The exponential gauge is continuous between the full physical H¹ graphs. -/
def u2PhysicalH1Gauge {d : ℕ} (hd : 2 ≤ d) (lam : ℝ) :
    PhysicalH1Space hd lam →L[ℝ] PhysicalH1Space hd 0 :=
  ⟨u2H1GaugeLinear hd lam, (u2H1GaugeLinear hd lam).continuous_of_seq_closed_graph (by
    intro u x y hu hv
    apply u2H1ZeroValueMap_injective hd
    have hleft := (u2H1ZeroValueMap hd).continuous.tendsto y |>.comp hv
    have hright := ((u2RealGaugeL2 (firstCoordinateIndex hd) lam).continuous.tendsto
      (u2H1ValueMap hd lam x)).comp ((u2H1ValueMap hd lam).continuous.tendsto x |>.comp hu)
    rw [u2H1GaugeLinear_value]
    apply tendsto_nhds_unique hleft
    convert hright using 1
    funext n
    exact u2H1GaugeLinear_value hd lam (u n))⟩

/-- The H¹ gauge represents multiplication by the literal exponential. -/
theorem u2PhysicalH1Gauge_value {d : ℕ} (hd : 2 ≤ d) (lam : ℝ)
    (u : PhysicalH1Space hd lam) :
    (u2H1ZeroValueMap hd (u2PhysicalH1Gauge hd lam u) : Vec d → ℝ) =ᵐ[volume]
      fun x => Real.exp (lam * x (firstCoordinateIndex hd)) * u2H1ValueMap hd lam u x := by
  change (u2H1ZeroValueMap hd (u2H1GaugeLinear hd lam u) : Vec d → ℝ) =ᵐ[volume] _
  rw [u2H1GaugeLinear_value]
  exact u2RealGaugeL2_coe (firstCoordinateIndex hd) lam (u2H1ValueMap hd lam u)

/-- The full graph gauge has the expected literal representative. -/
theorem u2PhysicalH1Gauge_value_ae {d : ℕ} (hd : 2 ≤ d) (lam : ℝ)
    (u : PhysicalH1Space hd lam) :
    (densityWeightedH1SpaceValue (u2PhysicalH1Gauge hd lam u) : Vec d → ℝ) =ᵐ[volume]
      fun x => Real.exp (lam * x (firstCoordinateIndex hd)) * densityWeightedH1SpaceValue u x := by
  have h0 := u2RealGaugeL2_coe (firstCoordinateIndex hd) 0
    (u2H1ValueMap hd 0 (u2PhysicalH1Gauge hd lam u))
  have h1 := u2PhysicalH1Gauge_value hd lam u
  filter_upwards [h0, h1] with x hx hy
  simp only [zero_mul, Real.exp_zero, one_mul] at hx
  exact hx.symm.trans hy

/-- The full H¹ gauge maps each smooth compact test to its literal gauged test. -/
theorem u2PhysicalH1Gauge_smoothTest {d : ℕ} (hd : 2 ≤ d) (lam : ℝ)
    (φ : Vec d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) :
    u2PhysicalH1Gauge hd lam (physicalH1SmoothTest hd lam φ hφ hc) =
      physicalH1SmoothTest hd 0
        (fun x => Real.exp (lam * x (firstCoordinateIndex hd)) * φ x)
        (((contDiff_const.mul (contDiff_apply ℝ ℝ (firstCoordinateIndex hd))).exp).mul hφ)
        (hc.mul_left) := by
  apply u2H1ValueMap_injective
  apply Lp.ext
  apply (physicalForceMeasure_absolutelyContinuous (firstCoordinateIndex hd) 0).ae_eq
  have htest := (volume_absolutelyContinuous_physicalForceMeasure
    (firstCoordinateIndex hd) lam).ae_eq (physicalH1SmoothTest_value hd lam φ hφ hc)
  have hout := (volume_absolutelyContinuous_physicalForceMeasure
    (firstCoordinateIndex hd) 0).ae_eq (physicalH1SmoothTest_value hd 0
      (fun x => Real.exp (lam * x (firstCoordinateIndex hd)) * φ x)
      (((contDiff_const.mul (contDiff_apply ℝ ℝ (firstCoordinateIndex hd))).exp).mul hφ)
      (hc.mul_left))
  filter_upwards [u2PhysicalH1Gauge_value_ae hd lam
    (physicalH1SmoothTest hd lam φ hφ hc), htest, hout] with x hg hi ho
  exact hg.trans ((congrArg (Real.exp (lam * x (firstCoordinateIndex hd)) * ·) hi).trans ho.symm)

/-- The physical gauge-potential pairing on the complete signed-force H¹ space. -/
def u2PhysicalGaugePotentialForm {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (u v : PhysicalH1Space hd lam) : ℝ :=
  inner ℝ
    (u2PhysicalGaugePotentialMul hd ω lam Λ hΛ hω
      (Blueprint.gmpPhysicalH1ValueContinuousLinear hd ω 0 Λ hω (u2PhysicalH1Gauge hd lam u)))
    (Blueprint.gmpPhysicalH1ValueContinuousLinear hd ω 0 Λ hω (u2PhysicalH1Gauge hd lam v))

/-- The potential term is jointly continuous in the full H¹ graph norm. -/
theorem u2PhysicalGaugePotentialForm_continuous {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) :
    Continuous (fun p : PhysicalH1Space hd lam × PhysicalH1Space hd lam =>
      u2PhysicalGaugePotentialForm hd ω lam Λ hΛ hω p.1 p.2) := by
  unfold u2PhysicalGaugePotentialForm
  fun_prop

/-- The continuous potential pairing is the integral of the original potential. -/
theorem u2PhysicalGaugePotentialForm_integral {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (u v : PhysicalH1Space hd lam) :
    u2PhysicalGaugePotentialForm hd ω lam Λ hΛ hω u v =
      ∫ x, (lam * physicalDrift ω (firstCoordinateIndex hd) 0 x (firstCoordinateIndex hd) +
          (lam ^ 2 / 2) * ω.1 x (firstCoordinateIndex hd) (firstCoordinateIndex hd)) *
        (Blueprint.gmpPhysicalH1ValueContinuousLinear hd ω 0 Λ hω (u2PhysicalH1Gauge hd lam u)) x *
        (Blueprint.gmpPhysicalH1ValueContinuousLinear hd ω 0 Λ hω (u2PhysicalH1Gauge hd lam v)) x
        ∂physicalReversibleMeasure ω hd 0 := by
  unfold u2PhysicalGaugePotentialForm
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [u2PhysicalGaugePotentialMul_coe hd ω lam Λ hΛ hω
    (Blueprint.gmpPhysicalH1ValueContinuousLinear hd ω 0 Λ hω (u2PhysicalH1Gauge hd lam u))]
    with x hx
  simp only [RCLike.inner_apply', conj_trivial, hx]

/-- A graph-norm bound for the actual anisotropic physical energy. -/
theorem u2PhysicalH1Energy_bound {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (u v : Blueprint.GMPForceH1 hd lam) :
    |Blueprint.gmpPhysicalH1Energy hd ω lam Λ hω u v| ≤
      (Real.exp (2 * Λ) * (1 + Λ / 2) + Real.exp Λ * Real.exp Λ) * ‖u‖ * ‖v‖ := by
  let U := Blueprint.gmpPhysicalH1Value hd ω lam Λ hω u
  let V := Blueprint.gmpPhysicalH1Value hd ω lam Λ hω v
  let E := Blueprint.gmpPhysicalH1Energy hd ω lam Λ hω u v
  have hf : |inner ℝ U V + E| ≤ Real.exp (2 * Λ) * (1 + Λ / 2) * ‖u‖ * ‖v‖ := by
    have h := sourcePhysicalResolventForm_bounded hd ω lam Λ 1 hΛ hω zero_lt_one u v
    dsimp only [U, V, E]
    rw [Blueprint.gmpPhysicalH1Energy_eq_source]
    simp only [one_mul] at h
    convert h using 1 <;> rfl
  have hm : |inner ℝ U V| ≤ (Real.exp Λ * Real.exp Λ) * ‖u‖ * ‖v‖ := by
    calc
      _ ≤ ‖U‖ * ‖V‖ := abs_real_inner_le_norm _ _
      _ ≤ (Real.exp Λ * ‖u‖) * (Real.exp Λ * ‖v‖) :=
        mul_le_mul (Blueprint.gmpPhysicalH1Value_norm_le hd ω lam Λ hω u)
          (Blueprint.gmpPhysicalH1Value_norm_le hd ω lam Λ hω v)
          (norm_nonneg _) (mul_nonneg (Real.exp_nonneg _) (norm_nonneg _))
      _ = _ := by ring
  have ht := abs_sub (inner ℝ U V + E) (inner ℝ U V)
  have he : (inner ℝ U V + E) - inner ℝ U V = E := by ring
  rw [he] at ht
  dsimp only [E] at ht
  calc
    _ ≤ |inner ℝ U V + E| + |inner ℝ U V| := ht
    _ ≤ _ := by nlinarith [hf, hm]

/-- The full physical energy is a continuous bilinear form on the H¹ graph. -/
def u2PhysicalH1EnergyBilinear {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) :
    Blueprint.GMPForceH1 hd lam →L[ℝ] Blueprint.GMPForceH1 hd lam →L[ℝ] ℝ := by
  let E := Blueprint.gmpPhysicalH1Energy hd ω lam Λ hω
  let B : Blueprint.GMPForceH1 hd lam →ₗ[ℝ] Blueprint.GMPForceH1 hd lam →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ E
      (Blueprint.gmpPhysicalH1Energy_add_left hd ω lam Λ hΛ hω)
      (by intro c u v; dsimp only [E]; simpa only [smul_eq_mul] using
        Blueprint.gmpPhysicalH1Energy_smul_left hd ω lam Λ hω c u v)
      (by
        intro u v w
        dsimp only [E]
        rw [Blueprint.gmpPhysicalH1Energy_symm hd ω lam Λ hω u (v + w),
          Blueprint.gmpPhysicalH1Energy_add_left hd ω lam Λ hΛ hω,
          Blueprint.gmpPhysicalH1Energy_symm hd ω lam Λ hω v u,
          Blueprint.gmpPhysicalH1Energy_symm hd ω lam Λ hω w u])
      (by
        intro c u v
        dsimp only [E]
        rw [Blueprint.gmpPhysicalH1Energy_symm hd ω lam Λ hω u (c • v),
          Blueprint.gmpPhysicalH1Energy_smul_left hd ω lam Λ hω,
          Blueprint.gmpPhysicalH1Energy_symm hd ω lam Λ hω v u]
        rfl)
  exact B.mkContinuous₂
    (Real.exp (2 * Λ) * (1 + Λ / 2) + Real.exp Λ * Real.exp Λ)
    (fun u v => by simpa only [B, LinearMap.mk₂_apply, E, Real.norm_eq_abs] using
      u2PhysicalH1Energy_bound hd ω lam Λ hΛ hω u v)

/-- The actual physical energy depends continuously on both H¹ arguments. -/
theorem u2PhysicalH1Energy_continuous {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) :
    Continuous (fun p : Blueprint.GMPForceH1 hd lam × Blueprint.GMPForceH1 hd lam =>
      Blueprint.gmpPhysicalH1Energy hd ω lam Λ hω p.1 p.2) := by
  change Continuous (fun p : Blueprint.GMPForceH1 hd lam × Blueprint.GMPForceH1 hd lam =>
    u2PhysicalH1EnergyBilinear hd ω lam Λ hΛ hω p.1 p.2)
  fun_prop

/-- The two canonical embeddings of a compact test give the same full H¹ graph. -/
theorem u2PhysicalH1SmoothTest_eq_compactTestDomain {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hω : IsRegular Λ ω)
    (φ : Vec d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) :
    physicalH1SmoothTest hd lam φ hφ hc = C8GMP.compactTestDomain hd lam φ hφ hc := by
  apply Blueprint.gmpPhysicalH1Value_injective hd ω lam Λ hω
  apply Lp.ext
  exact ((Blueprint.gmpPhysicalH1Value_ae_eq hd ω lam Λ hω
    (physicalH1SmoothTest hd lam φ hφ hc)).trans
      ((Measure.absolutelyContinuous_of_le_smul
        (sourcePhysicalMeasure_le_reduced ω hd lam Λ hω)).ae_eq
          (physicalH1SmoothTest_value hd lam φ hφ hc))).trans
    (Blueprint.gmpPhysicalCompactTest_value_ae hd ω lam Λ hω φ hφ hc).symm

/-- The full energy of two literal smooth tests is their classical gradient integral. -/
theorem u2PhysicalH1Energy_smoothTest {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hω : IsRegular Λ ω)
    (φ ψ : Vec d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hcφ : HasCompactSupport φ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hcψ : HasCompactSupport ψ) :
    Blueprint.gmpPhysicalH1Energy hd ω lam Λ hω
      (physicalH1SmoothTest hd lam φ hφ hcφ) (physicalH1SmoothTest hd lam ψ hψ hcψ) =
      ∫ x, (1 / 2 : ℝ) * dot (gradient φ x) ((ω.1 x).mulVec (gradient ψ x))
        ∂physicalReversibleMeasure ω hd lam := by
  have hgrad (f : Vec d → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) :
      (Blueprint.gmpPhysicalH1GradientContinuousLinear hd ω lam Λ hω
        (physicalH1SmoothTest hd lam f hf hc) : Vec d → EuclideanSpace ℝ (Fin d)) =ᵐ[
          physicalReversibleMeasure ω hd lam]
        fun x => (EuclideanSpace.equiv (Fin d) ℝ).symm (gradient f x) := by
    exact (Lp.coeFn_LpToLpOfMeasureLeSMul ENNReal.ofReal_ne_top
      (sourcePhysicalMeasure_le_reduced ω hd lam Λ hω)
      (densityWeightedH1SpaceGradient (physicalH1SmoothTest hd lam f hf hc))).trans
        ((Measure.absolutelyContinuous_of_le_smul
          (sourcePhysicalMeasure_le_reduced ω hd lam Λ hω)).ae_eq
          (physicalH1SmoothTest_gradient hd lam f hf hc))
  unfold Blueprint.gmpPhysicalH1Energy
  apply integral_congr_ae
  filter_upwards [hgrad φ hφ hcφ, hgrad ψ hψ hcψ] with x h1 h2
  rw [h1, h2]
  rfl

/-- On compact tests the potential pairing is the classical gauge-potential integral. -/
theorem u2PhysicalGaugePotentialForm_smoothTest {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (φ ψ : Vec d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hcφ : HasCompactSupport φ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hcψ : HasCompactSupport ψ) :
    u2PhysicalGaugePotentialForm hd ω lam Λ hΛ hω
      (physicalH1SmoothTest hd lam φ hφ hcφ) (physicalH1SmoothTest hd lam ψ hψ hcψ) =
      ∫ x, (lam * physicalDrift ω (firstCoordinateIndex hd) 0 x (firstCoordinateIndex hd) +
          (lam ^ 2 / 2) * ω.1 x (firstCoordinateIndex hd) (firstCoordinateIndex hd)) *
        (Real.exp (lam * x (firstCoordinateIndex hd)) * φ x) *
        (Real.exp (lam * x (firstCoordinateIndex hd)) * ψ x)
        ∂physicalReversibleMeasure ω hd 0 := by
  rw [u2PhysicalGaugePotentialForm_integral]
  have hval (f : Vec d → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) :
      (Blueprint.gmpPhysicalH1ValueContinuousLinear hd ω 0 Λ hω
        (u2PhysicalH1Gauge hd lam (physicalH1SmoothTest hd lam f hf hc)) : Vec d → ℝ) =ᵐ[
          physicalReversibleMeasure ω hd 0]
        fun x => Real.exp (lam * x (firstCoordinateIndex hd)) * f x := by
    have h0 := Blueprint.gmpPhysicalH1Value_ae_eq hd ω 0 Λ hω
      (u2PhysicalH1Gauge hd lam (physicalH1SmoothTest hd lam f hf hc))
    have hg := (Blueprint.gmpPhysical_ae_iff_volume hd ω 0 _).mpr
      (u2PhysicalH1Gauge_value_ae hd lam (physicalH1SmoothTest hd lam f hf hc))
    have ht := (Blueprint.gmpPhysical_ae_iff_volume hd ω 0 _).mpr
      ((volume_absolutelyContinuous_physicalForceMeasure (firstCoordinateIndex hd) lam).ae_eq
        (physicalH1SmoothTest_value hd lam f hf hc))
    filter_upwards [h0, hg, ht] with x h0x hgx htx
    exact h0x.trans (hgx.trans (congrArg (Real.exp (lam * x (firstCoordinateIndex hd)) * ·) htx))
  apply integral_congr_ae
  filter_upwards [hval φ hφ hcφ, hval ψ hψ hcψ] with x h1 h2
  rw [h1, h2]

/-- The exact gauge form identity on the full-domain compact test embeddings. -/
theorem u2PhysicalH1Gauge_form_smoothTest {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (φ ψ : Vec d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hcφ : HasCompactSupport φ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hcψ : HasCompactSupport ψ) :
    Blueprint.gmpPhysicalH1Energy hd ω lam Λ hω
      (physicalH1SmoothTest hd lam φ hφ hcφ) (physicalH1SmoothTest hd lam ψ hψ hcψ) =
    Blueprint.gmpPhysicalH1Energy hd ω 0 Λ hω
      (u2PhysicalH1Gauge hd lam (physicalH1SmoothTest hd lam φ hφ hcφ))
      (u2PhysicalH1Gauge hd lam (physicalH1SmoothTest hd lam ψ hψ hcψ)) +
    u2PhysicalGaugePotentialForm hd ω lam Λ hΛ hω
      (physicalH1SmoothTest hd lam φ hφ hcφ) (physicalH1SmoothTest hd lam ψ hψ hcψ) := by
  rw [u2PhysicalH1Gauge_smoothTest, u2PhysicalH1Gauge_smoothTest,
    u2PhysicalH1Energy_smoothTest, u2PhysicalH1Energy_smoothTest,
    u2PhysicalGaugePotentialForm_smoothTest]
  exact u2_regular_gauge_compact_form hd ω lam Λ hΛ hω ψ φ hψ hcψ hφ hcφ

private def u2H1LiteralTestSubmodule {d : ℕ} (hd : 2 ≤ d) (lam : ℝ) :
    Submodule ℝ (PhysicalH1Space hd lam) where
  carrier := {u | ∃ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧
    u2H1ValueMap hd lam u =ᵐ[EinsteinRelation.External.GantertSection7Support.physicalForceMeasure hd lam] φ}
  zero_mem' := by
    refine ⟨0, contDiff_const, HasCompactSupport.zero, ?_⟩
    simpa only [map_zero] using Lp.coeFn_zero ℝ 2
      (EinsteinRelation.External.GantertSection7Support.physicalForceMeasure hd lam)
  add_mem' := by
    rintro u v ⟨φ, hφ, hφc, hu⟩ ⟨ψ, hψ, hψc, hv⟩
    refine ⟨φ + ψ, hφ.add hψ, hφc.add hψc, ?_⟩
    rw [map_add]
    filter_upwards [Lp.coeFn_add (u2H1ValueMap hd lam u) (u2H1ValueMap hd lam v), hu, hv]
      with x hx hy hz
    exact hx.trans (congrArg₂ (· + ·) hy hz)
  smul_mem' := by
    rintro c u ⟨φ, hφ, hφc, hu⟩
    have hs : tsupport (c • φ) ⊆ tsupport φ :=
      tsupport_smul_subset_right (fun _ : Vec d => c) φ
    refine ⟨c • φ, hφ.const_smul c,
      hφc.of_isClosed_subset (isClosed_tsupport _) hs, ?_⟩
    rw [map_smul]
    filter_upwards [Lp.coeFn_smul c (u2H1ValueMap hd lam u), hu] with x hx hy
    exact hx.trans (congrArg (c • ·) hy)

/-- Smooth compact graphs are dense in the actual full signed-force H¹ graph. -/
theorem u2_physicalH1_smooth_core_approximation {d : ℕ} (hd : 2 ≤ d) (lam : ℝ)
    (u : PhysicalH1Space hd lam) :
    ∃ v : ℕ → PhysicalH1Space hd lam,
      (∀ n, v n ∈ physicalH1SmoothCore Set.univ hd lam) ∧
        Tendsto v atTop (𝓝 u) := by
  apply mem_closure_iff_seq_limit.mp
  exact physicalH1Space_mem_zeroBoundary_univ hd lam u

/-- The approximating graph values are literal smooth compactly supported functions. -/
theorem u2_physicalH1_smooth_test_approximation {d : ℕ} (hd : 2 ≤ d) (lam : ℝ)
    (u : PhysicalH1Space hd lam) :
    ∃ (φ : ℕ → Vec d → ℝ) (hφ : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (φ n))
      (hφc : ∀ n, HasCompactSupport (φ n)),
      Tendsto (fun n => physicalH1SmoothTest hd lam (φ n) (hφ n) (hφc n)) atTop (𝓝 u) := by
  have hcore : physicalH1SmoothCore Set.univ hd lam ≤ u2H1LiteralTestSubmodule hd lam := by
    apply Submodule.span_le.mpr
    rintro v ⟨φ, hφ, rfl⟩
    exact ⟨φ, hφ.1, hφ.2.1, physicalH1SmoothTest_value hd lam φ hφ.1 hφ.2.1⟩
  obtain ⟨v, hv, ht⟩ := u2_physicalH1_smooth_core_approximation hd lam u
  have htest (n) := hcore (hv n)
  choose φ hφ hφc hval using htest
  refine ⟨φ, hφ, hφc, ?_⟩
  have heq (n) : physicalH1SmoothTest hd lam (φ n) (hφ n) (hφc n) = v n := by
    apply u2H1ValueMap_injective
    apply Lp.ext
    exact (physicalH1SmoothTest_value hd lam (φ n) (hφ n) (hφc n)).trans (hval n).symm
  simpa only [heq] using ht

/-- The exact physical gauge form identity on the entire signed-force H¹ domain. -/
theorem u2_regular_gauge_full_form {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (u v : PhysicalH1Space hd lam) :
    Blueprint.gmpPhysicalH1Energy hd ω lam Λ hω u v =
      Blueprint.gmpPhysicalH1Energy hd ω 0 Λ hω (u2PhysicalH1Gauge hd lam u)
        (u2PhysicalH1Gauge hd lam v) + u2PhysicalGaugePotentialForm hd ω lam Λ hΛ hω u v := by
  obtain ⟨φ, hφ, hcφ, hu⟩ := u2_physicalH1_smooth_test_approximation hd lam u
  obtain ⟨ψ, hψ, hcψ, hv⟩ := u2_physicalH1_smooth_test_approximation hd lam v
  have hu0 := ((u2PhysicalH1Gauge hd lam).continuous.tendsto u).comp hu
  have hv0 := ((u2PhysicalH1Gauge hd lam).continuous.tendsto v).comp hv
  have hl := ((u2PhysicalH1Energy_continuous hd ω lam Λ hΛ hω).tendsto (u, v)).comp
    (hu.prodMk_nhds hv)
  have hr := (((u2PhysicalH1Energy_continuous hd ω 0 Λ hΛ hω).tendsto
    (u2PhysicalH1Gauge hd lam u, u2PhysicalH1Gauge hd lam v)).comp (hu0.prodMk_nhds hv0)).add
      (((u2PhysicalGaugePotentialForm_continuous hd ω lam Λ hΛ hω).tendsto (u, v)).comp
        (hu.prodMk_nhds hv))
  apply tendsto_nhds_unique hl
  convert hr using 1
  funext n
  exact (u2PhysicalH1Gauge_form_smoothTest hd ω lam Λ hΛ hω
    (φ n) (ψ n) (hφ n) (hcφ n) (hψ n) (hcψ n))

/-- The full-domain identity with the physical potential displayed as an integral. -/
theorem u2_regular_gauge_full_form_integral {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (u v : PhysicalH1Space hd lam) :
    Blueprint.gmpPhysicalH1Energy hd ω lam Λ hω u v =
      Blueprint.gmpPhysicalH1Energy hd ω 0 Λ hω (u2PhysicalH1Gauge hd lam u)
        (u2PhysicalH1Gauge hd lam v) +
      ∫ x, (lam * physicalDrift ω (firstCoordinateIndex hd) 0 x (firstCoordinateIndex hd) +
          (lam ^ 2 / 2) * ω.1 x (firstCoordinateIndex hd) (firstCoordinateIndex hd)) *
        (Blueprint.gmpPhysicalH1ValueContinuousLinear hd ω 0 Λ hω (u2PhysicalH1Gauge hd lam u)) x *
        (Blueprint.gmpPhysicalH1ValueContinuousLinear hd ω 0 Λ hω (u2PhysicalH1Gauge hd lam v)) x
        ∂physicalReversibleMeasure ω hd 0 := by
  have h := u2_regular_gauge_full_form hd ω lam Λ hΛ hω u v
  rw [u2PhysicalGaugePotentialForm_integral] at h
  exact h

/-- The gauge identity on literal weighted Sobolev graphs. -/
theorem u2_regular_physical_full_H1_gauge_energy
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (u : SpatialDirichlet.WeightedSobolevGraph
      (EinsteinRelation.External.GantertSection7Support.physicalForceMeasure hd lam)) :
    ∃ v : SpatialDirichlet.WeightedSobolevGraph
        (EinsteinRelation.External.GantertSection7Support.physicalForceMeasure hd 0),
      (v.value =ᵐ[physicalReversibleMeasure ω hd 0]
        fun x => Real.exp (lam * x (firstCoordinateIndex hd)) * u.value x) ∧
      physicalH1FormEnergy ω hd lam u = physicalH1FormEnergy ω hd 0 v +
        ∫ x, (lam * physicalDrift ω (firstCoordinateIndex hd) 0 x
          (firstCoordinateIndex hd) + (lam ^ 2 / 2) *
          ω.1 x (firstCoordinateIndex hd) (firstCoordinateIndex hd)) *
          (v.value x) ^ 2 ∂physicalReversibleMeasure ω hd 0 := by
  let q : DensityWeightedH1 (sourceReducedDensity hd lam) := Quotient.mk _ u
  let w : PhysicalH1Space hd lam := densityWeightedH1GraphEquiv _ _ _ q
  let z := u2PhysicalH1Gauge hd lam w
  let v := densityWeightedH1SpaceRepresentative (sourceReducedDensity hd 0)
    (continuousSourceReducedDensity hd 0) (positiveSourceReducedDensity hd 0) z
  have hw : (densityWeightedH1SpaceValue w : Vec d → ℝ) =ᵐ[volume] u.value := by
    apply (ae_withDensity_iff_volume_of_continuous_pos (sourceReducedDensity hd lam)
      (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam) _).mp
    change (densityWeightedH1SpaceValue (densityWeightedH1GraphEquiv _ _ _ q) : Vec d → ℝ) =ᵐ[_] u.value
    rw [Blueprint.gmpForceH1_graphEquiv_value hd lam q]
    exact u.value_memLp.coeFn_toLp
  have hz : v.value =ᵐ[volume] (densityWeightedH1SpaceValue z : Vec d → ℝ) := by
    apply (ae_withDensity_iff_volume_of_continuous_pos (sourceReducedDensity hd 0)
      (continuousSourceReducedDensity hd 0) (positiveSourceReducedDensity hd 0) _).mp
    exact Blueprint.gmpH1Representative_value_ae _ _ _ z
  have hvalue : v.value =ᵐ[physicalReversibleMeasure ω hd 0]
      fun x => Real.exp (lam * x (firstCoordinateIndex hd)) * u.value x := by
    apply (withDensity_absolutelyContinuous _ _).ae_eq
    filter_upwards [hz, u2PhysicalH1Gauge_value_ae hd lam w, hw] with x ha hb hc
    rw [ha, hb, hc]
  have henergy : Blueprint.gmpPhysicalH1Energy hd ω lam Λ hω w w =
      physicalH1FormEnergy ω hd lam u := by
    rw [Blueprint.gmpPhysicalH1Energy_eq_source hd ω lam Λ hω w w,
      sourcePhysicalDirichletForm_self_eq_physicalH1FormEnergy ω hd lam Λ hω w]
    let g := densityWeightedH1SpaceRepresentative (sourceReducedDensity hd lam)
      (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam) w
    have hg : g.value =ᵐ[volume] u.value := by
      have h := Blueprint.gmpH1Representative_value_ae _ _ _ w
      have h' : g.value =ᵐ[volume] (densityWeightedH1SpaceValue w : Vec d → ℝ) :=
        (ae_withDensity_iff_volume_of_continuous_pos (sourceReducedDensity hd lam)
        (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam) _).mp h
      exact h'.trans hw
    have hgrad := weakGradients_ae_eq_of_value_ae_eq hg g.distributionalGradient u.distributionalGradient
    unfold physicalH1FormEnergy
    apply integral_congr_ae
    filter_upwards [(withDensity_absolutelyContinuous _ _).ae_eq hgrad] with x hx
    change (1 / 2 : ℝ) * dot (g.weakGradient x).ofLp _ = _
    rw [hx]
    rfl
  have hzval : (Blueprint.gmpPhysicalH1ValueContinuousLinear hd ω 0 Λ hω z : Vec d → ℝ) =ᵐ[
      physicalReversibleMeasure ω hd 0] v.value := by
    exact (Blueprint.gmpPhysicalH1Value_ae_eq hd ω 0 Λ hω z).trans
      ((withDensity_absolutelyContinuous _ _).ae_eq hz.symm)
  have h := u2_regular_gauge_full_form_integral hd ω lam Λ hΛ hω w w
  change Blueprint.gmpPhysicalH1Energy hd ω lam Λ hω w w =
    Blueprint.gmpPhysicalH1Energy hd ω 0 Λ hω z z + _ at h
  rw [henergy, Blueprint.gmpPhysicalH1Energy_eq_source hd ω 0 Λ hω z z,
    sourcePhysicalDirichletForm_self_eq_physicalH1FormEnergy ω hd 0 Λ hω z] at h
  refine ⟨v, hvalue, ?_⟩
  convert h using 1
  congr 1
  apply integral_congr_ae
  filter_upwards [hzval] with x hx
  rw [hx]
  ring



end EinsteinFull
