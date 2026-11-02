import EinsteinFull.Calculus.C3JointLocalizationSupport
import EinsteinFull.Calculus.S1ClockBlockBounds
import EinsteinFull.External.AKMBlockBoundary
import EinsteinFull.Calculus.AKMStretchedExponentialMoments
import EinsteinFull.Calculus.S1CovarianceL2Support
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Source-load and physical block interfaces for the boundary-strip estimate. -/

open MeasureTheory ProbabilityTheory
open scoped Pointwise
noncomputable section

namespace EinsteinFull.Calculus.C2BlockBoundary
open EinsteinRelation EinsteinRelation.External.AKM
open EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinFull.Blueprint EinsteinFull.External.Source.AKM

/-- The covariance window supplies the literal source block window. -/
theorem covarianceWindow_blockParameterWindow
    {d : ℕ} (hd : 2 ≤ d) {D : StructuralData d} {s δ γ η β : ℝ}
    (h : covarianceWindow d D s δ γ η β) : blockParameterWindow d s δ γ η := by
  obtain ⟨_, hs, hs', hδ, hγ, hγ', hηγ, hη, hη2, _, _⟩ := h
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hγ0 : 0 < γ := lt_trans (by positivity) hγ
  have hmul := (div_lt_iff₀ (by positivity : 0 < 2 * γ)).mp hηγ
  exact ⟨hs, hs', hδ, hγ, hγ', hη2, by nlinarith only [hmul], hη⟩

/-- The actual covariance family and the reviewed source family make exactly
the same structural choices, before choosing the environment law. -/
theorem covarianceSourceLocalizedEnergy_eq_sourceSelectedLocalizedEnergy
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (s δ γ η β : ℝ) (h : covarianceWindow d D s δ γ η β)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) :
    covarianceSourceLocalizedEnergy d hd D s δ γ η β h Q =
      sourceSelectedLocalizedEnergy d hd (AKMUpperEllipticity D.ellipticity) s δ γ
        h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1
        (actualCoefficientLaw Q) (lawHypotheses_actualCoefficientLaw Q) := by
  rfl

/-- The physical radius at the prescribed scale eventually lies in the
literal source boundary interval. The threshold precedes the law. -/
theorem boundary_source_scale_threshold
    {r₀ δ η β : ℝ} (hr₀ : 1 ≤ r₀) (hδ : 0 < δ) (hη : 0 < η)
    (hηβ : η * (1 + δ) < β) (hβ : β < 1) :
    ∃ L₀ : ℝ, 2 ≤ L₀ ∧ ∀ L : ℝ, L₀ ≤ L →
      1 ≤ L / r₀ ∧ 2 ≤ L ^ η / r₀ ∧
      (L / r₀) ^ (β * η) ≤ L ^ η / r₀ ∧
      L ^ η / r₀ ≤ (L / r₀) ^ (β / (1 + δ)) := by
  have hr₀0 : 0 < r₀ := lt_of_lt_of_le zero_lt_one hr₀
  have hgap : 0 < η - β * η := by nlinarith
  obtain ⟨A, hA⟩ := Filter.eventually_atTop.1
    ((tendsto_rpow_atTop hη).eventually_ge_atTop (2 * r₀))
  obtain ⟨B, hB⟩ := Filter.eventually_atTop.1
    ((tendsto_rpow_atTop hgap).eventually_ge_atTop r₀)
  refine ⟨max 2 (max r₀ (max A B)), le_max_left _ _, ?_⟩
  intro L hL
  have hL2 := (le_max_left 2 _).trans hL
  have hL1 : 1 ≤ L := by linarith
  have hL0 : 0 < L := by linarith
  have hrest := (le_max_right 2 _).trans hL
  have hrL := (le_max_left r₀ _).trans hrest
  have hAB := (le_max_right r₀ _).trans hrest
  have hLA := (le_max_left A B).trans hAB
  have hLB := (le_max_right A B).trans hAB
  refine ⟨(one_le_div hr₀0).2 hrL, (le_div_iff₀ hr₀0).2 (hA L hLA), ?_, ?_⟩
  · have hβ0 : 0 ≤ β := by nlinarith
    have hratio : L / r₀ ≤ L := div_le_self hL0.le hr₀
    have hpow : (L / r₀) ^ (β * η) ≤ L ^ (β * η) :=
      Real.rpow_le_rpow (div_nonneg hL0.le hr₀0.le) hratio (mul_nonneg hβ0 hη.le)
    apply hpow.trans
    apply (le_div_iff₀ hr₀0).2
    calc L ^ (β * η) * r₀ ≤ L ^ (β * η) * L ^ (η - β * η) :=
          mul_le_mul_of_nonneg_left (hB L hLB) (Real.rpow_nonneg hL0.le _)
      _ = L ^ η := by rw [← Real.rpow_add hL0]; congr 1; ring
  · have hk : η ≤ β / (1 + δ) :=
      ((le_div_iff₀ (by linarith : 0 < 1 + δ)).2 hηβ.le)
    have hk1 : β / (1 + δ) ≤ 1 := by
      apply (div_le_one (by linarith : 0 < 1 + δ)).2
      linarith
    rw [Real.div_rpow hL0.le hr₀0.le]
    exact div_le_div₀ (Real.rpow_nonneg hL0.le _) (Real.rpow_le_rpow_of_exponent_le hL1 hk)
      (Real.rpow_pos_of_pos hr₀0 _) (Real.rpow_le_self_of_one_le hr₀ hk1)

/-- Every bounded measurable spatial test on a finite-measure set can be
integrated against each actual centered source load. The measurable spatial
map includes the physical dependence-range rescaling used by polarization. -/
theorem centeredSourceLoad_integrableOn
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (s δ γ η β : ℝ) (h : covarianceWindow d D s δ γ η β)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (P : Measure (Coefficient d (AKMUpperEllipticity D.ellipticity)))
    [IsProbabilityMeasure P]
    (a : Coefficient d (AKMUpperEllipticity D.ellipticity))
    (g : Vec d → Vec d) (hg : Measurable g) (r : ℝ) (p q : Vec d)
    {S : Set (Vec d)} (hSm : MeasurableSet S) (hS : volume S < ⊤)
    {f : Vec d → ℝ} (hf : Measurable f) {b : ℝ} (hb : 0 ≤ b)
    (hfb : ∀ y ∈ S, |f y| ≤ b) :
    IntegrableOn (fun y => f y * centeredLocalizedEnergy P
      (covarianceSourceLocalizedEnergy d hd D s δ γ η β h Q) a (g y) r p q) S := by
  have : IsFiniteMeasure (volume.restrict S) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hS⟩
  let B := (AKMUpperEllipticity D.ellipticity * euclideanNorm p + euclideanNorm q) ^ 2 / 2
  have hmap : Measurable (fun y : Vec d => (g y, a)) := hg.prodMk measurable_const
  have hm := (covarianceCenteredLocalizedEnergy_joint_measurable
    d hd D s δ γ η β h Q P r p q).comp hmap
  apply (integrable_const (b * B)).mono' (hf.mul hm).aestronglyMeasurable
  filter_upwards [ae_restrict_mem hSm] with y hy
  change ‖f y * centeredLocalizedEnergy P
    (covarianceSourceLocalizedEnergy d hd D s δ γ η β h Q) a (g y) r p q‖ ≤ b * B
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul (hfb y hy)
    (covarianceCenteredLocalizedEnergy_abs_le d hd D s δ γ η β h Q P a (g y) r p q)
    (abs_nonneg _) hb

/-- Polarized physical block integrals split only after each of their literal
source loads has been shown spatially integrable. The identity retains all
physical units and the original block normalization. -/
theorem physicalMatrixBlock_eq_lift
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (s δ γ η β : ℝ) (h : covarianceWindow d D s δ γ η β)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (r L side : ℝ) (hside : 0 ≤ side) (x : Vec d) (j k : Fin d)
    {f : Vec d → ℝ} (hf : Measurable f) {b : ℝ} (hb : 0 ≤ b)
    (hfb : ∀ y ∈ clockBlockCube x side, |f y| ≤ b) :
    let J := covarianceSourceLocalizedEnergy d hd D s δ γ η β h Q
    let A := ellipticityScale D.ellipticity • homogenizedCoefficient Q
    (fun ω => covarianceBlock d hd D s δ γ η β h Q r L side x f ω (.inl (j, k))) =
      covariancePhysicalLift Q (fun a =>
        L ^ (-(d : ℝ) / 2) * ((ellipticityScale D.ellipticity)⁻¹ / 2) *
          ((∫ y in clockBlockCube x side, f y * centeredLocalizedEnergy
            (actualCoefficientLaw Q) J a (D.dependenceRange⁻¹ • y)
              (r / D.dependenceRange) (unitVector j + unitVector k) (A.mulVec (unitVector j))) -
           (∫ y in clockBlockCube x side, f y * centeredLocalizedEnergy
            (actualCoefficientLaw Q) J a (D.dependenceRange⁻¹ • y)
              (r / D.dependenceRange) (unitVector j - unitVector k) (A.mulVec (unitVector j))))) := by
  classical
  have := actualCoefficientLaw_probability Q
  dsimp only
  funext ω
  by_cases hω : ω ∈ ReductionImageV3.physicalReducedRange D.ellipticity
  · let a := project (r₀ := D.dependenceRange) Q.ellipticity_parameter
      (ReductionImageV3.inverseReducePhysical ⟨ω, hω⟩)
    let A := ellipticityScale D.ellipticity • homogenizedCoefficient Q
    have hg : Measurable (fun y : Vec d => D.dependenceRange⁻¹ • y) :=
      (continuous_const_smul (D.dependenceRange⁻¹ : ℝ)).measurable
    have hS : volume (clockBlockCube x side) < ⊤ := by
      rw [volume_clockBlockCube x hside]
      exact ENNReal.ofReal_lt_top
    have hip := centeredSourceLoad_integrableOn d hd D s δ γ η β h Q
      (actualCoefficientLaw Q) a _ hg (r / D.dependenceRange)
      (unitVector j + unitVector k) (A.mulVec (unitVector j))
      (measurableSet_clockBlockCube x side) hS hf hb hfb
    have him := centeredSourceLoad_integrableOn d hd D s δ γ η β h Q
      (actualCoefficientLaw Q) a _ hg (r / D.dependenceRange)
      (unitVector j - unitVector k) (A.mulVec (unitVector j))
      (measurableSet_clockBlockCube x side) hS hf hb hfb
    simp only [covarianceBlock, covarianceLocalizedField, covarianceLocalizedEntry,
      covariancePhysicalLift, dite_eq_left hω]
    rw [show (fun y : Vec d => f y * ((ellipticityScale D.ellipticity)⁻¹ *
        (centeredLocalizedEnergy (actualCoefficientLaw Q)
          (covarianceSourceLocalizedEnergy d hd D s δ γ η β h Q) a
          (D.dependenceRange⁻¹ • y) (r / D.dependenceRange)
          (unitVector j + unitVector k) (A.mulVec (unitVector j)) -
        centeredLocalizedEnergy (actualCoefficientLaw Q)
          (covarianceSourceLocalizedEnergy d hd D s δ γ η β h Q) a
          (D.dependenceRange⁻¹ • y) (r / D.dependenceRange)
          (unitVector j - unitVector k) (A.mulVec (unitVector j))) / 2)) =
        (fun y => ((ellipticityScale D.ellipticity)⁻¹ / 2) *
          (f y * centeredLocalizedEnergy (actualCoefficientLaw Q)
            (covarianceSourceLocalizedEnergy d hd D s δ γ η β h Q) a
            (D.dependenceRange⁻¹ • y) (r / D.dependenceRange)
            (unitVector j + unitVector k) (A.mulVec (unitVector j)) -
          f y * centeredLocalizedEnergy (actualCoefficientLaw Q)
            (covarianceSourceLocalizedEnergy d hd D s δ γ η β h Q) a
            (D.dependenceRange⁻¹ • y) (r / D.dependenceRange)
            (unitVector j - unitVector k) (A.mulVec (unitVector j)))) by
      funext y; ring]
    rw [integral_const_mul, integral_sub hip him]
    ring
  · simp only [covarianceBlock, covarianceLocalizedField, covarianceLocalizedEntry,
      covariancePhysicalLift, dite_eq_right hω, mul_zero, integral_zero]

/-- Centering preserves the actual source energy's quadratic load scaling. -/
theorem centeredSourceLoad_smul
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (s δ γ η β : ℝ) (h : covarianceWindow d D s δ γ η β)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (P : Measure (Coefficient d (AKMUpperEllipticity D.ellipticity)))
    (a : Coefficient d (AKMUpperEllipticity D.ellipticity))
    (z : Vec d) (r t : ℝ) (p q : Vec d) :
    centeredLocalizedEnergy P (covarianceSourceLocalizedEnergy d hd D s δ γ η β h Q)
      a z r (t • p) (t • q) =
      t ^ 2 * centeredLocalizedEnergy P
        (covarianceSourceLocalizedEnergy d hd D s δ γ η β h Q) a z r p q := by
  simp only [centeredLocalizedEnergy,
    covarianceSourceLocalizedEnergy_smul d hd D s δ γ η β h Q, integral_const_mul]
  ring

/-- Quadratic load scaling commutes with the literal source block integral. -/
theorem centeredSourceBlock_smul
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (s δ γ η β : ℝ) (h : covarianceWindow d D s δ γ η β)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (P : Measure (Coefficient d (AKMUpperEllipticity D.ellipticity)))
    (a : Coefficient d (AKMUpperEllipticity D.ellipticity))
    (z : Vec d) (R r t : ℝ) (p q : Vec d) (f : Vec d → ℝ) :
    sourceCenteredBlock P (covarianceSourceLocalizedEnergy d hd D s δ γ η β h Q)
      a z R r f (t • p) (t • q) =
      t ^ 2 * sourceCenteredBlock P
        (covarianceSourceLocalizedEnergy d hd D s δ γ η β h Q) a z R r f p q := by
  simp only [sourceCenteredBlock, centeredSourceLoad_smul d hd D s δ γ η β h Q]
  simp_rw [show ∀ y : Vec d, f y * (t ^ 2 * centeredLocalizedEnergy P
      (covarianceSourceLocalizedEnergy d hd D s δ γ η β h Q) a y r p q) =
      t ^ 2 * (f y * centeredLocalizedEnergy P
        (covarianceSourceLocalizedEnergy d hd D s δ γ η β h Q) a y r p q) by
    intro y; ring]
  rw [integral_const_mul]
  ring

/-- A cube test is converted to the literal globally bounded supported test
required by AKM, retaining the original outer-cube normalization. -/
theorem cubeTest_indicator_normalize
    {d : ℕ} (x : Vec d) (L w : ℝ) {f : Vec d → ℝ} (hf : Measurable f)
    {b : ℝ} (hb : 0 < b) (hfb : ∀ y ∈ clockBlockCube x L, |f y| ≤ b)
    (hf0 : ∀ y ∈ clockBlockCube x (L - w), f y = 0) :
    let g := (clockBlockCube x L).indicator (fun y => b⁻¹ * f y)
    Measurable g ∧ (∀ y, |g y| ≤ 1) ∧
      Function.support g ⊆ clockBlockCube x L \ clockBlockCube x (L - w) := by
  dsimp only
  refine ⟨(measurable_const.mul hf).indicator (measurableSet_clockBlockCube x L), ?_, ?_⟩
  · intro y
    by_cases hy : y ∈ clockBlockCube x L
    · rw [Set.indicator_of_mem hy, abs_mul, abs_of_pos (inv_pos.mpr hb)]
      calc b⁻¹ * |f y| ≤ b⁻¹ * b := mul_le_mul_of_nonneg_left (hfb y hy) (inv_nonneg.mpr hb.le)
           _ = 1 := inv_mul_cancel₀ hb.ne'
    · rw [Set.indicator_of_notMem hy, abs_zero]
      exact zero_le_one
  · intro y hy
    have hout : y ∈ clockBlockCube x L := by
      by_contra hn
      exact hy (Set.indicator_of_notMem hn _)
    refine ⟨hout, ?_⟩
    intro hin
    apply hy
    rw [Set.indicator_of_mem hout, hf0 y hin, mul_zero]

/-- The two existing open-cube conventions agree exactly. -/
theorem sourceBlockCube_eq_clockBlockCube {d : ℕ} (x : Vec d) (L : ℝ) :
    sourceBlockCube x L = clockBlockCube x L := by
  ext y
  simp only [sourceBlockCube, clockBlockCube, Set.mem_ofPred_eq, Set.mem_pi,
    Set.mem_univ, forall_true_left, Set.mem_Ioo, abs_lt]
  constructor <;> intro hy i <;> obtain ⟨hlo, hhi⟩ := hy i <;> constructor <;> linarith

/-- Signed source blocks are measurable before using any stochastic estimate. -/
theorem centeredSourceBlock_measurable
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (s δ γ η β : ℝ) (h : covarianceWindow d D s δ γ η β)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (z : Vec d) (R r : ℝ) (p q : Vec d) {f : Vec d → ℝ} (hf : Measurable f) :
    Measurable (fun a => sourceCenteredBlock (actualCoefficientLaw Q)
      (covarianceSourceLocalizedEnergy d hd D s δ γ η β h Q) a z R r f p q) := by
  have := actualCoefficientLaw_probability Q
  have hm := (hf.comp measurable_fst).mul
    (covarianceCenteredLocalizedEnergy_joint_measurable d hd D s δ γ η β h Q
      (actualCoefficientLaw Q) r p q)
  exact hm.stronglyMeasurable.integral_prod_left'.measurable.const_mul _

/-- AKM's boundary input applies to the actual selected covariance energy.
The constant is chosen before the physical law, source scales and loads. -/
theorem centeredSourceBlock_boundary_osBound
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (s δ γ η β : ℝ) (h : covarianceWindow d D s δ γ η β) :
    ∃ C : ℝ, 0 < C ∧
      ∀ Q : EnvironmentLaw d D.ellipticity D.dependenceRange,
      ∀ (R r : ℝ), 1 ≤ R → 2 ≤ r → R ^ (β * η) ≤ r →
        r ≤ R ^ (β / (1 + δ)) →
      ∀ (z p q : Vec d), euclideanNorm p < 1 → euclideanNorm q < 1 →
      ∀ f : Vec d → ℝ, Measurable f → (∀ y, |f y| ≤ 1) →
        Function.support f ⊆ sourceBlockCube z R \ sourceBlockCube z (R - R ^ β) →
      OsBound (actualCoefficientLaw Q) (fun a => |sourceCenteredBlock (actualCoefficientLaw Q)
        (covarianceSourceLocalizedEnergy d hd D s δ γ η β h Q) a z R r f p q|)
        s (C * R ^ (-(d : ℝ) / 2 - (1 - β) / 2)) := by
  have hw := covarianceWindow_blockParameterWindow hd h
  have hβ0 : 0 ≤ β := by
    have hδ := h.2.2.2.1
    have hη := h.2.2.2.2.2.2.2.2.1
    have hβ := h.2.2.2.2.2.2.2.2.2.1
    nlinarith
  obtain ⟨C, hC, hbound⟩ := EinsteinFull.External.akm_block_boundary d hd
    (AKMUpperEllipticity D.ellipticity) s δ γ η h.1 hw β hβ0
    h.2.2.2.2.2.2.2.2.2.2.le
  refine ⟨C, hC, ?_⟩
  intro Q R r hR hr hlo hhi z p q hp hq f hf hfb hfs
  simpa only [covarianceSourceLocalizedEnergy_eq_sourceSelectedLocalizedEnergy]
    using hbound (actualCoefficientLaw Q) (lawHypotheses_actualCoefficientLaw Q)
      R r hR hr hlo hhi z p q hp hq f hf hfb hfs

/-- The actual signed boundary block has genuine square integrability as well
as its root-second-moment decay. Both conclusions use the literal source block. -/
theorem centeredSourceBlock_boundary_L2
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (s δ γ η β : ℝ) (h : covarianceWindow d D s δ γ η β) :
    ∃ C : ℝ, 0 < C ∧
      ∀ Q : EnvironmentLaw d D.ellipticity D.dependenceRange,
      ∀ (R r : ℝ), 1 ≤ R → 2 ≤ r → R ^ (β * η) ≤ r →
        r ≤ R ^ (β / (1 + δ)) →
      ∀ (z p q : Vec d), euclideanNorm p < 1 → euclideanNorm q < 1 →
      ∀ f : Vec d → ℝ, Measurable f → (∀ y, |f y| ≤ 1) →
        Function.support f ⊆ sourceBlockCube z R \ sourceBlockCube z (R - R ^ β) →
      let X := fun a => sourceCenteredBlock (actualCoefficientLaw Q)
        (covarianceSourceLocalizedEnergy d hd D s δ γ η β h Q) a z R r f p q
      MemLp X 2 (actualCoefficientLaw Q) ∧
        Real.sqrt (∫ a, (X a) ^ 2 ∂actualCoefficientLaw Q) ≤
          C * R ^ (-(d : ℝ) / 2 - (1 - β) / 2) := by
  obtain ⟨C, hC, hbound⟩ := centeredSourceBlock_boundary_osBound d hd D s δ γ η β h
  let M := Real.sqrt (2 * (2 / s) ^ (2 / s))
  have hM : 0 < M := Real.sqrt_pos.2
    (mul_pos (by norm_num) (Real.rpow_pos_of_pos (div_pos (by norm_num) (lt_trans zero_lt_one h.2.1)) _))
  refine ⟨M * C, mul_pos hM hC, ?_⟩
  intro Q R r hR hr hlo hhi z p q hp hq f hf hfb hfs
  have hos := hbound Q R r hR hr hlo hhi z p q hp hq f hf hfb hfs
  refine ⟨EinsteinFull.AKM.memLp_two_of_osBound hos
    (centeredSourceBlock_measurable d hd D s δ γ η β h Q z R r p q hf).aestronglyMeasurable, ?_⟩
  simpa only [M, mul_assoc, sq_abs] using EinsteinFull.AKM.sqrt_integral_sq_le_of_osBound hos

/-- Unit-load source estimates extend to the actual arbitrary polarization
loads by their proved common quadratic scaling, with the dependence exposed. -/
theorem centeredSourceBlock_boundary_real_loads_L2
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (s δ γ η β : ℝ) (h : covarianceWindow d D s δ γ η β) :
    ∃ C : ℝ, 0 < C ∧
      ∀ Q : EnvironmentLaw d D.ellipticity D.dependenceRange,
      ∀ (R r : ℝ), 1 ≤ R → 2 ≤ r → R ^ (β * η) ≤ r →
        r ≤ R ^ (β / (1 + δ)) →
      ∀ (z p q : Vec d) (f : Vec d → ℝ), Measurable f → (∀ y, |f y| ≤ 1) →
        Function.support f ⊆ sourceBlockCube z R \ sourceBlockCube z (R - R ^ β) →
      let X := fun a => sourceCenteredBlock (actualCoefficientLaw Q)
        (covarianceSourceLocalizedEnergy d hd D s δ γ η β h Q) a z R r f p q
      MemLp X 2 (actualCoefficientLaw Q) ∧
        Real.sqrt (∫ a, (X a) ^ 2 ∂actualCoefficientLaw Q) ≤
          (1 + euclideanNorm p + euclideanNorm q) ^ 2 * C *
            R ^ (-(d : ℝ) / 2 - (1 - β) / 2) := by
  obtain ⟨C, hC, hbound⟩ := centeredSourceBlock_boundary_L2 d hd D s δ γ η β h
  refine ⟨C, hC, ?_⟩
  intro Q R r hR hr hlo hhi z p q f hf hfb hfs
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
  obtain ⟨hYm, hYb⟩ := hbound Q R r hR hr hlo hhi z (t⁻¹ • p) (t⁻¹ • q) hp hq f hf hfb hfs
  dsimp only
  simp_rw [heq]
  refine ⟨hYm.const_mul (t ^ 2), ?_⟩
  simp_rw [mul_pow]
  rw [integral_const_mul, Real.sqrt_mul (sq_nonneg (t ^ 2)), Real.sqrt_sq (sq_nonneg t)]
  exact (mul_le_mul_of_nonneg_left hYb (sq_nonneg t)).trans_eq (by dsimp [t]; ring)

/-- Positive spatial dilation preserves the literal open-cube convention. -/
theorem smul_sourceBlockCube {d : ℕ} (z : Vec d) (R : ℝ)
    {c : ℝ} (hc : 0 < c) :
    c • sourceBlockCube z R = sourceBlockCube (c • z) (c * R) := by
  ext u
  constructor
  · rintro ⟨v, hv, rfl⟩ i
    change |c * v i - c * z i| < c * R / 2
    rw [← mul_sub, abs_mul, abs_of_pos hc]
    exact (mul_lt_mul_of_pos_left (hv i) hc).trans_eq (by ring)
  · intro hu
    refine ⟨c⁻¹ • u, ?_, smul_inv_smul₀ hc.ne' u⟩
    intro i
    change |c⁻¹ * u i - z i| < R / 2
    apply (mul_lt_mul_iff_right₀ hc).mp
    have he : c * |c⁻¹ * u i - z i| = |u i - c * z i| := by
      calc
        _ = |c * (c⁻¹ * u i - z i)| := by rw [abs_mul, abs_of_pos hc]
        _ = _ := by congr 1; field_simp
    rw [he]
    exact (hu i).trans_eq (by ring)

/-- Exact change of variables for a physical centered scalar block. The
Jacobian remains explicit, before applying either block normalization. -/
theorem integral_centeredSourceLoad_rescale {d : ℕ} {K : ℝ}
    (P : Measure (Coefficient d K))
    (J : Coefficient d K → Vec d → ℝ → Vec d → Vec d → ℝ)
    (a : Coefficient d K) (z : Vec d) (L r : ℝ) (f : Vec d → ℝ)
    (p q : Vec d) {r₀ : ℝ} (hr₀ : 0 < r₀) :
    (∫ y in sourceBlockCube z L,
      f y * centeredLocalizedEnergy P J a (r₀⁻¹ • y) r p q) =
    r₀ ^ d * ∫ u in sourceBlockCube (r₀⁻¹ • z) (L / r₀),
      f (r₀ • u) * centeredLocalizedEnergy P J a u r p q := by
  have he := Measure.setIntegral_comp_smul_of_pos (volume : Measure (Vec d))
    (fun u => f (r₀ • u) * centeredLocalizedEnergy P J a u r p q)
    (sourceBlockCube z L) (inv_pos.mpr hr₀)
  simp only [Module.finrank_pi, Fintype.card_fin, inv_pow, inv_inv,
    smul_smul, mul_inv_cancel₀ hr₀.ne', one_smul, smul_eq_mul] at he
  rw [smul_sourceBlockCube z L (inv_pos.mpr hr₀)] at he
  simpa only [div_eq_inv_mul] using he

/-- The physical boundary strip becomes a subset of the source strip; its
thickness is never silently substituted for the original cube side. -/
theorem rescaled_boundary_test_support {d : ℕ} (z : Vec d)
    {L r₀ β : ℝ} (hL : 0 < L) (hr₀ : 1 ≤ r₀) (hβ : β ≤ 1)
    {f : Vec d → ℝ}
    (hf : Function.support f ⊆ sourceBlockCube z L \
      sourceBlockCube z (L - L ^ β)) :
    Function.support (fun u => f (r₀ • u)) ⊆
      sourceBlockCube (r₀⁻¹ • z) (L / r₀) \
      sourceBlockCube (r₀⁻¹ • z) (L / r₀ - (L / r₀) ^ β) := by
  have hr : 0 < r₀ := lt_of_lt_of_le zero_lt_one hr₀
  have hw : L ^ β / r₀ ≤ (L / r₀) ^ β := by
    rw [Real.div_rpow hL.le hr.le]
    exact div_le_div_of_nonneg_left (Real.rpow_nonneg hL.le _)
      (Real.rpow_pos_of_pos hr _) (Real.rpow_le_self_of_one_le hr₀ hβ)
  intro u hu
  obtain ⟨hout, hin⟩ := hf hu
  constructor
  · have hm := Set.smul_mem_smul_set (a := r₀⁻¹) hout
    rw [smul_sourceBlockCube z L (inv_pos.mpr hr)] at hm
    simpa only [inv_smul_smul₀ hr.ne', div_eq_inv_mul] using hm
  · intro hus
    apply hin
    intro i
    have hi := hus i
    have he : |r₀ * u i - z i| = r₀ * |u i - r₀⁻¹ * z i| := by
      calc
        _ = |r₀ * (u i - r₀⁻¹ * z i)| := by congr 1; field_simp
        _ = _ := by rw [abs_mul, abs_of_pos hr]
    change |r₀ * u i - z i| < (L - L ^ β) / 2
    rw [he]
    change |u i - r₀⁻¹ * z i| < (L / r₀ - (L / r₀) ^ β) / 2 at hi
    have hh := (div_le_iff₀ hr).mp hw
    have hi' := mul_lt_mul_of_pos_left hi hr
    have hcancel : r₀ * (L / r₀) = L := by field_simp
    nlinarith

/-- The literal isotropic clock block is a genuine L² random variable,
independently of the subsequent strip second-moment estimate. -/
theorem clockBlock_memLp
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (s δ γ η β : ℝ) (h : covarianceWindow d D s δ γ η β)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    {r : ℝ} (hr : 0 < r) (L : ℝ) (x : Vec d)
    {side : ℝ} (hside : 0 ≤ side)
    {f : Vec d → ℝ} (hf : Measurable f) {b : ℝ} (hb : 0 ≤ b)
    (hfb : ∀ y ∈ clockBlockCube x side, |f y| ≤ b) :
    MemLp (fun ω => covarianceBlock d hd D s δ γ η β h Q r L side x f ω (.inr ()))
      2 (reducedLaw Q) := by
  have := reducedLaw_probability Q
  have : IsFiniteMeasure (volume.restrict (clockBlockCube x side)) :=
    ⟨by rw [Measure.restrict_apply_univ, volume_clockBlockCube x hside]
        exact ENNReal.ofReal_lt_top⟩
  let B := 2 * sourceReducedBound D.ellipticity
  have hm := (hf.comp measurable_fst).mul
    (covarianceLocalizedClock_joint_measurable Q r (covarianceLocalizationRadius D δ r))
  have hbm : Measurable (fun ω => covarianceBlock d hd D s δ γ η β h Q r L side x f ω (.inr ())) :=
    hm.stronglyMeasurable.integral_prod_left'.measurable.const_mul _
  apply MemLp.of_bound hbm.aestronglyMeasurable
    (|L ^ (-(d : ℝ) / 2)| * ((volume (clockBlockCube x side)).toReal * (b * B)))
  filter_upwards [covarianceLocalizedClock_ae_forall_abs_le Q hr
    (covarianceLocalizationRadius D δ r)] with ω hω
  change ‖L ^ (-(d : ℝ) / 2) * ∫ y in clockBlockCube x side,
    f y * covarianceLocalizedClock Q r (covarianceLocalizationRadius D δ r) y ω‖ ≤ _
  rw [norm_mul, Real.norm_eq_abs]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  calc
    _ ≤ ∫ _y in clockBlockCube x side, b * B := by
      apply norm_integral_le_of_norm_le (integrable_const (b * B))
      filter_upwards [ae_restrict_mem (measurableSet_clockBlockCube x side)] with y hy
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hfb y hy) (hω y) (abs_nonneg _) hb
    _ = _ := by rw [setIntegral_const, smul_eq_mul]; rfl

/-- The physical CLT block is exactly a scalar multiple of the source's
volume-normalized block. Both outer-cube factors are retained. -/
theorem normalized_centeredSourceLoad_rescale {d : ℕ} {K : ℝ}
    (P : Measure (Coefficient d K))
    (J : Coefficient d K → Vec d → ℝ → Vec d → Vec d → ℝ)
    (a : Coefficient d K) (z : Vec d) {L : ℝ} (hL : 0 < L)
    (r : ℝ) (f : Vec d → ℝ) (p q : Vec d)
    {r₀ : ℝ} (hr₀ : 0 < r₀) :
    L ^ (-(d : ℝ) / 2) * (∫ y in sourceBlockCube z L,
      f y * centeredLocalizedEnergy P J a (r₀⁻¹ • y) r p q) =
    (L ^ (-(d : ℝ) / 2) * r₀ ^ d * (L / r₀) ^ d) *
      sourceCenteredBlock P J a (r₀⁻¹ • z) (L / r₀) r
        (fun u => f (r₀ • u)) p q := by
  have hR : 0 < L / r₀ := div_pos hL hr₀
  have hc : (L / r₀) ^ d * (L / r₀) ^ (-(d : ℝ)) = 1 := by
    rw [← Real.rpow_natCast (L / r₀) d, ← Real.rpow_add hR,
      add_neg_cancel, Real.rpow_zero]
  rw [integral_centeredSourceLoad_rescale P J a z L r f p q hr₀, sourceCenteredBlock]
  calc
    _ = (L ^ (-(d : ℝ) / 2) * r₀ ^ d) *
        (((L / r₀) ^ d * (L / r₀) ^ (-(d : ℝ))) *
          ∫ u in sourceBlockCube (r₀⁻¹ • z) (L / r₀),
            f (r₀ • u) * centeredLocalizedEnergy P J a u r p q) := by rw [hc]; ring
    _ = _ := by ring

/-- The literal isotropic clock has the boundary gain with the prescribed
signed exponent and the original test amplitude. -/
theorem clockBlock_boundary_L2
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (s δ γ η β : ℝ) (h : covarianceWindow d D s δ γ η β)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    {r : ℝ} (hr : 0 < r) {L : ℝ} (hL : 1 ≤ L) (x : Vec d)
    {f : Vec d → ℝ} (hf : Measurable f) {b : ℝ} (hb : 0 ≤ b)
    (hfb : ∀ y ∈ clockBlockCube x L, |f y| ≤ b)
    (hf0 : ∀ y ∈ clockBlockCube x (L - L ^ β), f y = 0) :
    let X := fun ω => covarianceBlock d hd D s δ γ η β h Q r L L x f ω (.inr ())
    MemLp X 2 (reducedLaw Q) ∧
      Real.sqrt (∫ ω, (X ω) ^ 2 ∂reducedLaw Q) ≤
        Real.sqrt (clockVarianceConstant d D.ellipticity D.dependenceRange * d) *
          L ^ (-(1 - β) / 2) * b := by
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hβ : β < 1 := h.2.2.2.2.2.2.2.2.2.2
  have hK : 0 ≤ clockVarianceConstant d D.ellipticity D.dependenceRange := by
    unfold clockVarianceConstant
    positivity [le_trans zero_le_one Q.range_parameter]
  have he : L ^ β / L = (L ^ (-(1 - β) / 2)) ^ 2 := by
    rw [← Real.rpow_sub_one hLp.ne', ← Real.rpow_natCast _ 2,
      ← Real.rpow_mul hLp.le]
    congr 1
    push_cast
    ring
  refine ⟨clockBlock_memLp d hd D s δ γ η β h Q hr L x hLp.le hf hb hfb, ?_⟩
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  calc
    _ ≤ clockVarianceConstant d D.ellipticity D.dependenceRange * b ^ 2 *
        (d * L ^ β / L) :=
      S1.clock_strip_sq_le d hd D s δ γ η β h Q hr x hLp
        (Real.rpow_nonneg hLp.le β) (Real.rpow_le_self_of_one_le hL hβ.le) hf hb hfb hf0
    _ = _ := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (mul_nonneg hK (Nat.cast_nonneg d)), ← he]
      ring

/-- The source decay, Jacobian and original physical CLT normalization
leave exactly the surface-order physical decay. -/
theorem physical_source_boundary_factor (d : ℕ) (β : ℝ)
    {L r₀ : ℝ} (hL : 0 < L) (hr₀ : 0 < r₀) :
    (L ^ (-(d : ℝ) / 2) * r₀ ^ d * (L / r₀) ^ d) *
        (L / r₀) ^ (-(d : ℝ) / 2 - (1 - β) / 2) =
      r₀ ^ ((d : ℝ) / 2 + (1 - β) / 2) * L ^ (-(1 - β) / 2) := by
  let a : ℝ := -(d : ℝ) / 2 - (1 - β) / 2
  have hR : 0 < L / r₀ := div_pos hL hr₀
  have h₁ : (d : ℝ) - ((d : ℝ) + a) = (d : ℝ) / 2 + (1 - β) / 2 := by
    dsimp [a]; ring
  have h₂ : -(d : ℝ) / 2 + ((d : ℝ) + a) = -(1 - β) / 2 := by
    dsimp [a]; ring
  change (L ^ (-(d : ℝ) / 2) * r₀ ^ d * (L / r₀) ^ d) * (L / r₀) ^ a = _
  rw [← Real.rpow_natCast r₀ d, ← Real.rpow_natCast (L / r₀) d]
  calc
    _ = L ^ (-(d : ℝ) / 2) * r₀ ^ (d : ℝ) * (L / r₀) ^ ((d : ℝ) + a) := by
      rw [Real.rpow_add hR]; ring
    _ = L ^ (-(d : ℝ) / 2) * r₀ ^ (d : ℝ) *
        (L ^ ((d : ℝ) + a) / r₀ ^ ((d : ℝ) + a)) := by rw [Real.div_rpow hL.le hr₀.le]
    _ = r₀ ^ ((d : ℝ) - ((d : ℝ) + a)) *
        L ^ (-(d : ℝ) / 2 + ((d : ℝ) + a)) := by
      rw [Real.rpow_sub hr₀,
        Real.rpow_add hL (-(d : ℝ) / 2) ((d : ℝ) + a)]
      ring
    _ = _ := by rw [h₁, h₂]

/-- The genuine source boundary estimate in physical coordinates, uniformly
over laws and arbitrary real polarization loads. -/
theorem physicalSourceBlock_boundary_L2
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (s δ γ η β : ℝ) (h : covarianceWindow d D s δ γ η β) :
    ∃ C L₀ : ℝ, 0 < C ∧ 2 ≤ L₀ ∧
      ∀ Q : EnvironmentLaw d D.ellipticity D.dependenceRange,
      ∀ L : ℝ, L₀ ≤ L → ∀ (z p q : Vec d) (f : Vec d → ℝ),
      Measurable f → (∀ y, |f y| ≤ 1) →
      Function.support f ⊆ sourceBlockCube z L \ sourceBlockCube z (L - L ^ β) →
      let F := fun a => L ^ (-(d : ℝ) / 2) * ∫ y in sourceBlockCube z L,
        f y * centeredLocalizedEnergy (actualCoefficientLaw Q)
          (covarianceSourceLocalizedEnergy d hd D s δ γ η β h Q) a
          (D.dependenceRange⁻¹ • y) (L ^ η / D.dependenceRange) p q
      Measurable F ∧ MemLp F 2 (actualCoefficientLaw Q) ∧
        Real.sqrt (∫ a, (F a) ^ 2 ∂actualCoefficientLaw Q) ≤
          (1 + euclideanNorm p + euclideanNorm q) ^ 2 * C * L ^ (-(1 - β) / 2) := by
  obtain ⟨C, hC, hbound⟩ := centeredSourceBlock_boundary_real_loads_L2 d hd D s δ γ η β h
  have hr₀ : 0 < D.dependenceRange := lt_of_lt_of_le zero_lt_one D.one_le_dependenceRange
  have hη : 0 < η := lt_trans (by norm_num) h.2.2.2.2.2.2.2.2.1
  obtain ⟨L₀, hL₀, hscale⟩ := boundary_source_scale_threshold D.one_le_dependenceRange
    h.2.2.2.1 hη h.2.2.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2.2.2
  refine ⟨C * D.dependenceRange ^ ((d : ℝ) / 2 + (1 - β) / 2), L₀,
    mul_pos hC (Real.rpow_pos_of_pos hr₀ _), hL₀, ?_⟩
  intro Q L hLL z p q f hf hfb hfs
  have hL : 0 < L := by linarith
  obtain ⟨hR, hr, hlo, hhi⟩ := hscale L hLL
  let g : Vec d → ℝ := fun u => f (D.dependenceRange • u)
  have hg : Measurable g := hf.comp (measurable_id.const_smul D.dependenceRange)
  have hgs := rescaled_boundary_test_support z hL D.one_le_dependenceRange
    h.2.2.2.2.2.2.2.2.2.2.le hfs
  let Y := fun a => sourceCenteredBlock (actualCoefficientLaw Q)
    (covarianceSourceLocalizedEnergy d hd D s δ γ η β h Q) a
    (D.dependenceRange⁻¹ • z) (L / D.dependenceRange) (L ^ η / D.dependenceRange) g p q
  have hYm : Measurable Y := centeredSourceBlock_measurable d hd D s δ γ η β h Q
    _ _ _ p q hg
  obtain ⟨hY, hYb⟩ := hbound Q _ _ hR hr hlo hhi _ p q g hg (fun u => hfb _) hgs
  let A := L ^ (-(d : ℝ) / 2) * D.dependenceRange ^ d * (L / D.dependenceRange) ^ d
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have heq (a : Coefficient d (AKMUpperEllipticity D.ellipticity)) :
      L ^ (-(d : ℝ) / 2) * (∫ y in sourceBlockCube z L,
        f y * centeredLocalizedEnergy (actualCoefficientLaw Q)
          (covarianceSourceLocalizedEnergy d hd D s δ γ η β h Q) a
          (D.dependenceRange⁻¹ • y) (L ^ η / D.dependenceRange) p q) = A * Y a :=
    normalized_centeredSourceLoad_rescale _ _ a z hL _ f p q hr₀
  dsimp only
  simp_rw [heq]
  refine ⟨hYm.const_mul A, hY.const_mul A, ?_⟩
  simp_rw [mul_pow]
  rw [integral_const_mul, Real.sqrt_mul (sq_nonneg A), Real.sqrt_sq hA]
  calc
    _ ≤ A * ((1 + euclideanNorm p + euclideanNorm q) ^ 2 * C *
        (L / D.dependenceRange) ^ (-(d : ℝ) / 2 - (1 - β) / 2)) :=
      mul_le_mul_of_nonneg_left hYb hA
    _ = (1 + euclideanNorm p + euclideanNorm q) ^ 2 * C *
        (A * (L / D.dependenceRange) ^ (-(d : ℝ) / 2 - (1 - β) / 2)) := by ring
    _ = _ := by rw [physical_source_boundary_factor d β hL hr₀]; ring

/-- Scalar root-second moments retain their literal real-square convention. -/
theorem rootSecondMoment_const_mul {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (F : Ω → ℝ) (c : ℝ) :
    Real.sqrt (∫ ω, (c * F ω) ^ 2 ∂μ) = |c| * Real.sqrt (∫ ω, (F ω) ^ 2 ∂μ) := by
  simp_rw [mul_pow]
  rw [integral_const_mul, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

theorem rootSecondMoment_sub_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {F G : Ω → ℝ} (hF : MemLp F 2 μ) (hG : MemLp G 2 μ) :
    Real.sqrt (∫ ω, (F ω - G ω) ^ 2 ∂μ) ≤
      Real.sqrt (∫ ω, (F ω) ^ 2 ∂μ) + Real.sqrt (∫ ω, (G ω) ^ 2 ∂μ) := by
  simpa only [S1.l2Size, Real.norm_eq_abs, sq_abs, Pi.sub_apply] using S1.l2Size_sub_le hF hG

/-- Squaring commutes with the exact zero-extended physical lift, hence its
root-second moment is exactly that of the actual coefficient law. -/
theorem covariancePhysicalLift_rootSecondMoment {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (F : Coefficient d (AKMUpperEllipticity L) → ℝ)
    (hF : Measurable F) :
    Real.sqrt (∫ ω, (covariancePhysicalLift Q F ω) ^ 2 ∂reducedLaw Q) =
      Real.sqrt (∫ a, (F a) ^ 2 ∂actualCoefficientLaw Q) := by
  have he : (fun ω => (covariancePhysicalLift Q F ω) ^ 2) =
      covariancePhysicalLift Q (fun a => (F a) ^ 2) := by
    funext ω
    unfold covariancePhysicalLift
    split <;> simp
  rw [he, covariancePhysicalLift_integral Q _ (hF.pow_const 2)]

/-- The loads used in physical polarization have a structural bound. -/
theorem polarization_load_bound
    {d : ℕ} (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (j k : Fin d) :
    let q := (ellipticityScale D.ellipticity • homogenizedCoefficient Q).mulVec (unitVector j)
    let W := 3 + ellipticityScale D.ellipticity * sourceReducedBound D.ellipticity
    (1 + euclideanNorm (unitVector j + unitVector k) + euclideanNorm q) ^ 2 ≤ W ^ 2 ∧
    (1 + euclideanNorm (unitVector j - unitVector k) + euclideanNorm q) ^ 2 ≤ W ^ 2 := by
  have hu (i : Fin d) : euclideanNorm (unitVector i) = 1 := by
    change Real.sqrt (dotProduct (Pi.single i 1) (Pi.single i 1)) = 1
    simp
  have hp : euclideanNorm (unitVector j + unitVector k) ≤ 2 := by
    simpa only [hu, one_add_one_eq_two] using TimeChange.euclideanNorm_add_le (unitVector j) (unitVector k)
  have hm : euclideanNorm (unitVector j - unitVector k) ≤ 2 := by
    have hn : euclideanNorm (-unitVector k) = 1 := by
      rw [show -unitVector k = (-1 : ℝ) • unitVector k by ext i; simp,
        TimeChange.euclideanNorm_smul, hu]
      norm_num
    simpa only [sub_eq_add_neg, hu, hn, one_add_one_eq_two] using
      TimeChange.euclideanNorm_add_le (unitVector j) (-unitVector k)
  have hscale := ellipticityScale_pos D.one_le_ellipticity
  have hq : euclideanNorm ((ellipticityScale D.ellipticity • homogenizedCoefficient Q).mulVec
      (unitVector j)) ≤ ellipticityScale D.ellipticity * sourceReducedBound D.ellipticity := by
    rw [Matrix.smul_mulVec, TimeChange.euclideanNorm_smul, abs_of_pos hscale]
    exact mul_le_mul_of_nonneg_left (homogenizedMatrix_euclideanNorm_mulVec_unitVector_le Q j) hscale.le
  have hn (v : Vec d) : 0 ≤ euclideanNorm v := Real.sqrt_nonneg _
  have hq0 := hn ((ellipticityScale D.ellipticity • homogenizedCoefficient Q).mulVec (unitVector j))
  have hbound (v : Vec d) (hv : euclideanNorm v ≤ 2) :
      (1 + euclideanNorm v + euclideanNorm
        ((ellipticityScale D.ellipticity • homogenizedCoefficient Q).mulVec (unitVector j))) ^ 2 ≤
      (3 + ellipticityScale D.ellipticity * sourceReducedBound D.ellipticity) ^ 2 := by
    apply (sq_le_sq₀ (by linarith [hn v]) (by linarith)).2
    linarith
  exact ⟨hbound _ hp, hbound _ hm⟩

/-- Physical matrix coordinates inherit the boundary rate through the literal
polarization and coefficient-law transport. -/
theorem physicalMatrixBlock_boundary_L2
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (s δ γ η β : ℝ) (h : covarianceWindow d D s δ γ η β) :
    ∃ C L₀ : ℝ, 0 < C ∧ 2 ≤ L₀ ∧
      ∀ Q : EnvironmentLaw d D.ellipticity D.dependenceRange,
      ∀ L : ℝ, L₀ ≤ L → ∀ (z : Vec d) (j k : Fin d) (f : Vec d → ℝ),
      Measurable f → (∀ y, |f y| ≤ 1) →
      Function.support f ⊆ clockBlockCube z L \ clockBlockCube z (L - L ^ β) →
      let F := fun ω => covarianceBlock d hd D s δ γ η β h Q (L ^ η) L L z f ω (.inl (j, k))
      Measurable F ∧ MemLp F 2 (reducedLaw Q) ∧
        Real.sqrt (∫ ω, (F ω) ^ 2 ∂reducedLaw Q) ≤ C * L ^ (-(1 - β) / 2) := by
  obtain ⟨C, L₀, hC, hL₀, hb⟩ := physicalSourceBlock_boundary_L2 d hd D s δ γ η β h
  let t := (ellipticityScale D.ellipticity)⁻¹ / 2
  let W := 3 + ellipticityScale D.ellipticity * sourceReducedBound D.ellipticity
  have ht : 0 < t := by dsimp [t]; exact div_pos (inv_pos.mpr (ellipticityScale_pos D.one_le_ellipticity)) (by norm_num)
  have hW : 0 < W := by
    dsimp [W]
    have := Clock.sourceReducedBound_pos D.one_le_ellipticity
    have := ellipticityScale_pos D.one_le_ellipticity
    positivity
  refine ⟨t * (2 * W ^ 2 * C), L₀, by positivity, hL₀, ?_⟩
  intro Q L hL z j k f hf hfb hfs
  have hLpos : 0 < L := by linarith
  let q := (ellipticityScale D.ellipticity • homogenizedCoefficient Q).mulVec (unitVector j)
  let B := fun p a => L ^ (-(d : ℝ) / 2) * ∫ y in sourceBlockCube z L,
    f y * centeredLocalizedEnergy (actualCoefficientLaw Q)
      (covarianceSourceLocalizedEnergy d hd D s δ γ η β h Q) a
      (D.dependenceRange⁻¹ • y) (L ^ η / D.dependenceRange) p q
  have hsupport : Function.support f ⊆ sourceBlockCube z L \ sourceBlockCube z (L - L ^ β) := by
    simpa only [sourceBlockCube_eq_clockBlockCube] using hfs
  obtain ⟨hpm, hp, hpb⟩ := hb Q L hL z (unitVector j + unitVector k) q f hf hfb hsupport
  obtain ⟨hmm, hm, hmb⟩ := hb Q L hL z (unitVector j - unitVector k) q f hf hfb hsupport
  have he : (fun ω => covarianceBlock d hd D s δ γ η β h Q (L ^ η) L L z f ω (.inl (j,k))) =
      covariancePhysicalLift Q (fun a => t * (B (unitVector j + unitVector k) a - B (unitVector j - unitVector k) a)) := by
    rw [physicalMatrixBlock_eq_lift d hd D s δ γ η β h Q (L ^ η) L L (by linarith) z j k hf zero_le_one (fun y _ => hfb y)]
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
        (1 + euclideanNorm (unitVector j - unitVector k) + euclideanNorm q) ^ 2) * C * L ^ (-(1 - β) / 2)) := by
      apply mul_le_mul_of_nonneg_left _ ht.le
      nlinarith only [hpb, hmb]
    _ ≤ t * ((2 * W ^ 2) * C * L ^ (-(1 - β) / 2)) := by
      gcongr
      dsimp [q, W] at *
      linarith
    _ = _ := by ring

/-- Coordinate square integrability and bounds assemble in the literal
Euclidean matrix-clock norm, including every coordinate. -/
theorem covarianceVectorSize_L2_of_coordinates
    {d : ℕ} (μ : Measure (FieldPair d)) (X : FieldPair d → JointObservationIndex d → ℝ)
    (hm : ∀ i, AEStronglyMeasurable (fun ω => X ω i) μ)
    (hLp : ∀ i, MemLp (fun ω => X ω i) 2 μ)
    {a : ℝ} (ha : 0 ≤ a)
    (hb : ∀ i, Real.sqrt (∫ ω, (X ω i) ^ 2 ∂μ) ≤ a) :
    MemLp (fun ω => covarianceVectorSize (X ω)) 2 μ ∧
      covarianceL2Size μ X ≤ Real.sqrt (Fintype.card (JointObservationIndex d) : ℝ) * a := by
  classical
  have he (ω) : covarianceVectorSize (X ω) ^ 2 = ∑ i, (X ω i) ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)
  have hi : Integrable (fun ω => ∑ i, (X ω i) ^ 2) μ :=
    integrable_finsetSum _ fun i _ => (hLp i).integrable_sq
  have hmeas : AEStronglyMeasurable (fun ω => covarianceVectorSize (X ω)) μ := by
    unfold covarianceVectorSize
    exact Real.continuous_sqrt.comp_aestronglyMeasurable
      (Finset.aestronglyMeasurable_fun_sum _ fun i _ =>
        (continuous_pow 2).comp_aestronglyMeasurable (hm i))
  refine ⟨(memLp_two_iff_integrable_sq hmeas).2 ?_, ?_⟩
  · simpa only [he] using hi
  · unfold covarianceL2Size
    simp_rw [he]
    rw [integral_finsetSum _ (fun i _ => (hLp i).integrable_sq)]
    calc
      _ ≤ Real.sqrt (∑ _i : JointObservationIndex d, a ^ 2) := by
        apply Real.sqrt_le_sqrt
        apply Finset.sum_le_sum
        intro i _
        exact (Real.sqrt_le_iff).mp (hb i) |>.2
      _ = Real.sqrt (Fintype.card (JointObservationIndex d) : ℝ) * a := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq ha]

/-- Uniform normalized boundary tests for the full physical matrix-clock
block, in the specified finite Euclidean norm. -/
theorem covarianceBlock_boundary_unit_L2
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (s δ γ η β : ℝ) (h : covarianceWindow d D s δ γ η β) :
    ∃ C L₀ : ℝ, 0 < C ∧ 2 ≤ L₀ ∧
      ∀ Q : EnvironmentLaw d D.ellipticity D.dependenceRange,
      ∀ L : ℝ, L₀ ≤ L → ∀ (z : Vec d) (f : Vec d → ℝ),
      Measurable f → (∀ y, |f y| ≤ 1) →
      Function.support f ⊆ clockBlockCube z L \ clockBlockCube z (L - L ^ β) →
      let X := covarianceBlock d hd D s δ γ η β h Q (L ^ η) L L z f
      MemLp (fun ω => covarianceVectorSize (X ω)) 2 (reducedLaw Q) ∧
        covarianceL2Size (reducedLaw Q) X ≤ C * L ^ (-(1 - β) / 2) := by
  classical
  obtain ⟨C, L₀, hC, hL₀, hm⟩ := physicalMatrixBlock_boundary_L2 d hd D s δ γ η β h
  let K := Real.sqrt (clockVarianceConstant d D.ellipticity D.dependenceRange * d)
  let M := C + K
  have hK : 0 ≤ K := Real.sqrt_nonneg _
  have hM : 0 < M := add_pos_of_pos_of_nonneg hC hK
  have hcard : 0 < (Fintype.card (JointObservationIndex d) : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨Sum.inr ()⟩
  refine ⟨Real.sqrt (Fintype.card (JointObservationIndex d) : ℝ) * M,
    L₀, mul_pos (Real.sqrt_pos.mpr hcard) hM, hL₀, ?_⟩
  intro Q L hL z f hf hfb hfs
  have hLpos : 0 < L := by linarith
  have hf0 : ∀ y ∈ clockBlockCube z (L - L ^ β), f y = 0 := by
    intro y hy
    by_contra hne
    exact (hfs (show y ∈ Function.support f from hne)).2 hy
  have hc := clockBlock_boundary_L2 d hd D s δ γ η β h Q
    (Real.rpow_pos_of_pos hLpos η) (by linarith : 1 ≤ L) z hf zero_le_one
    (fun y _ => hfb y) hf0
  let X := covarianceBlock d hd D s δ γ η β h Q (L ^ η) L L z f
  have hcoord (i : JointObservationIndex d) : MemLp (fun ω => X ω i) 2 (reducedLaw Q) ∧
      Real.sqrt (∫ ω, (X ω i) ^ 2 ∂reducedLaw Q) ≤ M * L ^ (-(1 - β) / 2) := by
    rcases i with ⟨j, k⟩ | u
    · obtain ⟨_, hp, hb⟩ := hm Q L hL z j k f hf hfb hfs
      refine ⟨hp, hb.trans ?_⟩
      exact mul_le_mul_of_nonneg_right (by dsimp [M]; linarith) (Real.rpow_nonneg hLpos.le _)
    · cases u
      refine ⟨hc.1, ?_⟩
      have hb : Real.sqrt (∫ ω, (X ω (.inr ())) ^ 2 ∂reducedLaw Q) ≤ K * L ^ (-(1 - β) / 2) := by
        simpa only [mul_one] using hc.2
      exact hb.trans (mul_le_mul_of_nonneg_right (by dsimp [M]; linarith) (Real.rpow_nonneg hLpos.le _))
  have hv := covarianceVectorSize_L2_of_coordinates (reducedLaw Q) X
    (fun i => (hcoord i).1.aestronglyMeasurable) (fun i => (hcoord i).1)
    (mul_nonneg hM.le (Real.rpow_nonneg hLpos.le _)) (fun i => (hcoord i).2)
  refine ⟨hv.1, ?_⟩
  simpa only [mul_assoc] using hv.2

/-- Pointwise scalar test identities on the integration cube pass through
every physical coordinate without any spatial splitting. -/
theorem covarianceBlock_test_mul
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (s δ γ η β : ℝ) (h : covarianceWindow d D s δ γ η β)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (r L side : ℝ) (z : Vec d) (f g : Vec d → ℝ) (c : ℝ)
    (hfg : ∀ y ∈ clockBlockCube z side, f y = c * g y)
    (ω : FieldPair d) (i : JointObservationIndex d) :
    covarianceBlock d hd D s δ γ η β h Q r L side z f ω i =
      c * covarianceBlock d hd D s δ γ η β h Q r L side z g ω i := by
  unfold covarianceBlock
  calc
    _ = L ^ (-(d : ℝ) / 2) * ∫ y in clockBlockCube z side,
        c * (g y * covarianceLocalizedField d hd D s δ γ η β h Q r y ω i) := by
      congr 1
      apply setIntegral_congr_fun (measurableSet_clockBlockCube z side)
      intro y hy
      dsimp only
      rw [hfg y hy]
      ring
    _ = _ := by rw [integral_const_mul]; ring

theorem covarianceVectorSize_mul {d : ℕ} (c : ℝ) (v : JointObservationIndex d → ℝ) :
    covarianceVectorSize (fun i => c * v i) = |c| * covarianceVectorSize v := by
  unfold covarianceVectorSize
  simp_rw [mul_pow]
  rw [← Finset.mul_sum, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

/-- Boundary tests with their original amplitude, physical normalization,
and complete Euclidean matrix-clock observation vector. -/
theorem covarianceBlock_boundary_L2
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (s δ γ η β : ℝ) (h : covarianceWindow d D s δ γ η β) :
    ∃ C L₀ : ℝ, 0 < C ∧ 2 ≤ L₀ ∧
      ∀ Q : EnvironmentLaw d D.ellipticity D.dependenceRange,
      ∀ L : ℝ, L₀ ≤ L → ∀ (z : Vec d) (f : Vec d → ℝ) (b : ℝ),
      Measurable f → 0 ≤ b → (∀ y ∈ clockBlockCube z L, |f y| ≤ b) →
      (∀ y ∈ clockBlockCube z (L - L ^ β), f y = 0) →
      let X := covarianceBlock d hd D s δ γ η β h Q (L ^ η) L L z f
      MemLp (fun ω => covarianceVectorSize (X ω)) 2 (reducedLaw Q) ∧
        covarianceL2Size (reducedLaw Q) X ≤ C * L ^ (-(1 - β) / 2) * b := by
  obtain ⟨C, L₀, hC, hL₀, hbound⟩ := covarianceBlock_boundary_unit_L2 d hd D s δ γ η β h
  refine ⟨C, L₀, hC, hL₀, ?_⟩
  intro Q L hL z f b hf hb hfb hf0
  by_cases hb0 : b = 0
  · have hfz : ∀ y ∈ clockBlockCube z L, f y = 0 * (0 : Vec d → ℝ) y := by
      intro y hy
      simpa only [zero_mul] using abs_nonpos_iff.mp (by simpa only [hb0] using hfb y hy)
    have he (ω : FieldPair d) (i : JointObservationIndex d) :
        covarianceBlock d hd D s δ γ η β h Q (L ^ η) L L z f ω i = 0 := by
      simpa only [zero_mul] using covarianceBlock_test_mul d hd D s δ γ η β h Q
        (L ^ η) L L z f 0 0 hfz ω i
    dsimp only
    simp_rw [covarianceL2Size, covarianceVectorSize, he]
    simp [hb0]
  · have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
    let g := (clockBlockCube z L).indicator (fun y => b⁻¹ * f y)
    obtain ⟨hg, hgb, hgs⟩ := cubeTest_indicator_normalize z L (L ^ β) hf hbpos hfb hf0
    obtain ⟨hLp, hsize⟩ := hbound Q L hL z g hg hgb hgs
    have he (ω : FieldPair d) (i : JointObservationIndex d) :
        covarianceBlock d hd D s δ γ η β h Q (L ^ η) L L z f ω i =
          b * covarianceBlock d hd D s δ γ η β h Q (L ^ η) L L z g ω i := by
      apply covarianceBlock_test_mul
      intro y hy
      dsimp [g]
      rw [Set.indicator_of_mem hy, ← mul_assoc, mul_inv_cancel₀ hb0, one_mul]
    have hn (ω : FieldPair d) :
        covarianceVectorSize (covarianceBlock d hd D s δ γ η β h Q (L ^ η) L L z f ω) =
        b * covarianceVectorSize (covarianceBlock d hd D s δ γ η β h Q (L ^ η) L L z g ω) := by
      simp_rw [show covarianceBlock d hd D s δ γ η β h Q (L ^ η) L L z f ω =
        (fun i => b * covarianceBlock d hd D s δ γ η β h Q (L ^ η) L L z g ω i) from funext (he ω)]
      rw [covarianceVectorSize_mul, abs_of_pos hbpos]
    dsimp only
    constructor
    · simpa only [hn] using hLp.const_mul b
    · unfold covarianceL2Size
      simp_rw [hn]
      rw [rootSecondMoment_const_mul, abs_of_pos hbpos]
      exact (mul_le_mul_of_nonneg_left hsize hb).trans_eq (by ring)

end EinsteinFull.Calculus.C2BlockBoundary
