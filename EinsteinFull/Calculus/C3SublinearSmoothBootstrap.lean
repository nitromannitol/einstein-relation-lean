import EinsteinFull.Calculus.C3SublinearC1Scalar
import EinsteinRelation.Correctors.PairedCorrectorEquation
import EinsteinRelation.Calculus.WeakGradientTranslation
import PDEFoundation.PDE.DGNM.Caccioppoli
import PDEFoundation.Sobolev.Cutoff.Ball
import EinsteinRelation.Correctors.ReducedOperatorLipschitz
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Calculus.Deriv.Slope
import PDEFoundation.Sobolev.H1.HilbertGraph
import PDEFoundation.Sobolev.H1.GraphPairing
import PDEFoundation.Sobolev.H1.GraphRepresentative
import PDEFoundation.Sobolev.H1.ZeroBoundaryCutoff
import PDEFoundation.Sobolev.H1.ZeroExtension
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import PDEFoundation.Sobolev.WeakDerivative.Congruence
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators Pointwise
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinRelation.External.AKM
open EinsteinRelation.Environment.AKMTestIntegralSupport EinsteinRelation.ReductionImageV3
namespace C3SublinearSmooth

/-- A cutoff of a continuous H1 representative with continuous local weak
gradient is genuinely C1. Zero extension is performed only after the cutoff
has supplied zero boundary data. -/
theorem contDiff_cutoff_of_continuous_weakGradient
    {d : ℕ} {U : Set (Vec d)} (hU : PDE.IsOpenBoundedConvexDomain U)
    (w : PDE.H1Function U) {u : Vec d → ℝ} {G : Vec d → Vec d}
    (hu : Continuous u) (hw : w.toFun =ᵐ[PDE.volumeOn U] u)
    (hG : ContinuousOn G U) (hwG : G =ᵐ[PDE.volumeOn U] w.grad)
    {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηc : HasCompactSupport η) (hηU : tsupport η ⊆ U) :
    ContDiff ℝ (1 : ℕ∞) (fun x => η x * u x) := by
  let w₀ := w.mulContDiffHasCompactSupportToH10 hU hη hηc hηU
  let W := w₀.zeroExtendToH1 isOpen_univ hU.isOpen (Set.subset_univ U)
  let H : Vec d → Vec d := fun x => η x • G x + u x • PDE.classicalGradient η x
  have hηG : Continuous (fun x => η x • G x) :=
    (hη.continuous.continuousOn.smul hG).continuous_of_tsupport_subset hU.isOpen
      ((tsupport_smul_subset_left η G).trans hηU)
  have hH : Continuous H := hηG.add
    (hu.smul (PDE.ContDiff.continuous_classicalGradient (hη.of_le (by simp))))
  have hηzero {x : Vec d} (hx : x ∉ U) : η x = 0 := by
    by_contra h
    exact hx (hηU (subset_closure h))
  have hηgradzero {x : Vec d} (hx : x ∉ U) : PDE.classicalGradient η x = 0 := by
    have ht : x ∉ tsupport η := fun ht => hx (hηU ht)
    funext j
    change fderiv ℝ η x (PDE.basisVec j) = 0
    rw [fderiv_of_notMem_tsupport ℝ ht]
    rfl
  have hw' : ∀ᵐ x ∂(volume : Measure (Vec d)), x ∈ U → w x = u x :=
    (ae_restrict_iff' hU.measurableSet).mp hw
  have hwG' : ∀ᵐ x ∂(volume : Measure (Vec d)), x ∈ U → G x = w.grad x :=
    (ae_restrict_iff' hU.measurableSet).mp hwG
  have hW : W.toFun =ᵐ[(volume : Measure (Vec d))] (fun x => η x * u x) := by
    filter_upwards [hw'] with x hx
    simp only [W, PDE.H10Function.zeroExtendToH1_toFun,
      w₀, PDE.H1Function.mulContDiffHasCompactSupportToH10_toFun]
    by_cases hxU : x ∈ U
    · rw [Set.indicator_of_mem hxU, hx hxU]
    · rw [Set.indicator_of_notMem hxU, hηzero hxU, zero_mul]
  have hWH : H =ᵐ[(volume : Measure (Vec d))] W.grad := by
    filter_upwards [hw', hwG'] with x hx hxG
    simp only [W, PDE.H10Function.zeroExtendToH1_grad,
      w₀, PDE.H1Function.mulContDiffHasCompactSupportToH10_grad]
    by_cases hxU : x ∈ U
    · rw [Set.indicator_of_mem hxU]
      simp only [H, hxG hxU, hx hxU]
    · rw [Set.indicator_of_notMem hxU]
      simp only [H, hηzero hxU, hηgradzero hxU, zero_smul, smul_zero, add_zero]
  have hweak : PDE.HasWeakGradientOn Set.univ (fun x => η x * u x) H := by
    intro j ψ hψ hψc hψs
    have h := W.hasWeakGradient j ψ hψ hψc hψs
    simp only [Measure.restrict_univ] at h ⊢
    calc
      (∫ x, (η x * u x) * fderiv ℝ ψ x (PDE.basisVec j)) =
          ∫ x, W x * fderiv ℝ ψ x (PDE.basisVec j) := by
        apply integral_congr_ae
        filter_upwards [hW] with x hx
        rw [hx]
      _ = -(∫ x, W.grad x j * ψ x) := h
      _ = -(∫ x, H x j * ψ x) := by
        congr 1
        apply integral_congr_ae
        filter_upwards [hWH] with x hx
        rw [hx]
  obtain ⟨v, hvc, hv, _⟩ :=
    C3SublinearC1.exists_c1_representative_of_continuous_weakGradient
      (hη.continuous.mul hu).locallyIntegrable hH hweak
  have heq : v = fun x => η x * u x := MeasureTheory.Measure.eq_of_ae_eq hv
    hvc.continuous (hη.continuous.mul hu)
  rwa [heq] at hvc

/-- Continuous local weak gradients give classical C1 regularity on the domain.
The compact cutoff is removed locally by division where it is nonzero. -/
theorem contDiffOn_of_continuous_weakGradient
    {d : ℕ} {U : Set (Vec d)} (hU : PDE.IsOpenBoundedConvexDomain U)
    (w : PDE.H1Function U) {u : Vec d → ℝ} {G : Vec d → Vec d}
    (hu : Continuous u) (hw : w.toFun =ᵐ[PDE.volumeOn U] u)
    (hG : ContinuousOn G U) (hwG : G =ᵐ[PDE.volumeOn U] w.grad) :
    ContDiffOn ℝ (1 : ℕ∞) u U := by
  rw [hU.isOpen.contDiffOn_iff]
  intro x hx
  obtain ⟨η, hηU, hηc, hη, _, hηx⟩ :=
    exists_contDiff_tsupport_subset (n := (⊤ : ℕ∞)) (hU.isOpen.mem_nhds hx)
  have hηne : η x ≠ 0 := by rw [hηx]; norm_num
  have hcut := contDiff_cutoff_of_continuous_weakGradient hU w hu hw hG hwG
    hη hηc hηU
  have hquot := hcut.contDiffAt.div (hη.of_le (by simp)).contDiffAt hηne
  apply hquot.congr_of_eventuallyEq
  filter_upwards [hη.continuous.continuousAt.eventually_ne hηne] with y hy
  exact (mul_div_cancel_left₀ (u y) hy).symm

/-- The inhomogeneous Schauder estimate retains a Hölder representative of
the weak gradient. Only the coefficients are assumed smooth: the differentiated
corrector's forcing must enter through its actual Hölder bound. -/
theorem exists_holder_gradient_halfBall
    {d : ℕ} (hd : 0 < d) {Λ : ℝ}
    (a : PDE.CoeffField d) (F : Vec d → Vec d)
    (ha : ∀ j k, ContDiff ℝ (⊤ : ℕ∞) (fun x => a x j k))
    (hF : ∃ B : ℝ, 0 ≤ B ∧ PDE.EuclideanFieldHolderSeminormLE
      (PDE.euclideanBall (0 : Vec d) 1) F (1 / 2) B)
    (hell : ∀ x ∈ PDE.euclideanBall (0 : Vec d) 1,
      PDE.IsEllipticMatrix 1 Λ (a x))
    (u : PDE.H1Function (PDE.euclideanBall (0 : Vec d) 1))
    (hu : PDE.IsWeakDivergenceFormSolutionOn a
      (PDE.euclideanBall (0 : Vec d) 1) u 0 F) :
    ∃ (G : Vec d → Vec d) (K : ℝ), 0 ≤ K ∧
      PDE.EuclideanFieldHolderSeminormLE
        (PDE.euclideanBall (0 : Vec d) (1 / 2)) G (1 / 2) K ∧
      G =ᵐ[PDE.volumeOn (PDE.euclideanBall (0 : Vec d) (1 / 2))] u.grad := by
  obtain ⟨C, hC, hs⟩ := PDE.SchauderC1Proof.result hd (Λ := Λ)
  obtain ⟨M, hM, ham⟩ :=
    PDE.exists_euclideanMatrixHolderSeminormLE_half_of_contDiff ha
  obtain ⟨ε, hε, hεfour, hsmall⟩ :=
    EinsteinFull.exists_schauder_half_scale C M hC hM
  let ha' : ∃ K : ℝ, 0 ≤ K ∧ PDE.EuclideanMatrixHolderSeminormLE
      (PDE.euclideanBall (0 : Vec d) 1) a (1 / 2) K := ⟨M, hM, ham⟩
  have hsmall' : ε ^ (1 / 2 : ℝ) * PDE.euclideanMatrixHolderSeminormOn
      (PDE.euclideanBall (0 : Vec d) 1) a (1 / 2) ha' ≤
      C⁻¹ * (1 / 2) * (1 - 1 / 2) :=
    (mul_le_mul_of_nonneg_left (PDE.euclideanMatrixHolderSeminormOn_le ha' hM ham)
      (Real.rpow_nonneg hε.le _)).trans hsmall
  obtain ⟨G, ⟨K, hK, hGK⟩, _, heq, _⟩ := hs
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
    hε hεfour a F hell ha' hF hsmall' u hu
  exact ⟨G, K, hK, hGK, heq⟩

/-- The nonzero forcing pairing scales with the same factor as the
elliptic flux. The transformed source is `R • F (R • y + x₀)`. -/
theorem blowUp_forcing_pairing
    {d : ℕ} {U : Set (Vec d)} (hU : IsOpen U)
    (F : Vec d → Vec d) (x₀ : Vec d) {R : ℝ} (hR : 0 < R)
    (hball : PDE.euclideanBall x₀ R ⊆ U)
    (ψ : PDE.WeakTestFunction (PDE.euclideanBall (0 : Vec d) 1))
    (hint : IntegrableOn (fun x => PDE.vecDot (F x)
      ((PDE.DGNM.extendTest hball (PDE.DGNM.pullTest x₀ hR ψ)).grad x)) U) :
    IntegrableOn (fun y => PDE.vecDot (R • F (R • y + x₀)) (ψ.grad y))
        (PDE.euclideanBall (0 : Vec d) 1) ∧
      (∫ y in PDE.euclideanBall (0 : Vec d) 1,
        PDE.vecDot (R • F (R • y + x₀)) (ψ.grad y)) =
      R ^ 2 * (R ^ d)⁻¹ * ∫ x in U, PDE.vecDot (F x)
        ((PDE.DGNM.extendTest hball (PDE.DGNM.pullTest x₀ hR ψ)).grad x) := by
  let H : Vec d → ℝ := fun x => PDE.vecDot (F x)
    ((PDE.DGNM.pullTest x₀ hR ψ).grad x)
  have hset : PDE.translateSet x₀ (R • PDE.euclideanBall (0 : Vec d) 1) =
      PDE.euclideanBall x₀ R := by
    rw [PDE.DGNM.translateSet_smul_euclideanBall x₀ hR 1, mul_one]
  have hpoint (y : Vec d) : PDE.vecDot (R • F (R • y + x₀)) (ψ.grad y) =
      R ^ 2 * H (R • y + x₀) := by
    have hy : R⁻¹ • (R • y + x₀ - x₀) = y := by
      rw [add_sub_cancel_right, smul_smul, inv_mul_cancel₀ hR.ne', one_smul]
    simp only [H, PDE.DGNM.pullTest_grad, hy,
      PDE.DGNM.vecDot_smul_left, PDE.DGNM.vecDot_smul_right]
    field_simp
  rw [PDE.DGNM.extendTest_grad] at hint ⊢
  have hHint : IntegrableOn H (PDE.euclideanBall x₀ R) := hint.mono_set hball
  rw [← hset] at hHint
  have hcomp := PDE.DGNM.integrableOn_comp_affineScale x₀ hR hHint
  refine ⟨?_, ?_⟩
  · simp_rw [hpoint]
    exact hcomp.const_mul _
  · simp_rw [hpoint]
    rw [integral_const_mul, PDE.DGNM.setIntegral_comp_affineScale x₀ hR, hset,
      PDE.DGNM.setIntegral_vecDot_extendTest hU.measurableSet hball]
    ring

/-- Dilation of an inhomogeneous weak solution retains its full forcing,
including the required amplitude factor. -/
theorem forced_solutionOn_blowUp
    {d : ℕ} {U : Set (Vec d)} {a : PDE.CoeffField d}
    {u : PDE.H1Function U} {F : Vec d → Vec d} (hU : IsOpen U)
    (hu : PDE.IsWeakDivergenceFormSolutionOn a U u 0 F)
    (x₀ : Vec d) {R : ℝ} (hR : 0 < R)
    (hball : PDE.euclideanBall x₀ R ⊆ U) :
    PDE.IsWeakDivergenceFormSolutionOn (PDE.DGNM.blowUpCoeff a x₀ R)
      (PDE.euclideanBall (0 : Vec d) 1) (PDE.DGNM.blowUp u x₀ hR hball)
      0 (fun y => R • F (R • y + x₀)) := by
  intro ψ
  obtain ⟨ht, he⟩ := hu (PDE.DGNM.extendTest hball (PDE.DGNM.pullTest x₀ hR ψ))
  obtain ⟨hflux, hfluxeq⟩ := PDE.DGNM.blowUp_flux hU u x₀ hR hball ψ ht.flux_integrable
  obtain ⟨hforce, hforceeq⟩ := blowUp_forcing_pairing hU F x₀ hR hball ψ
    ht.forcing_integrable
  refine ⟨⟨hflux, by simp, hforce⟩, ?_⟩
  simp only [Pi.zero_apply, zero_mul, integral_zero, zero_sub] at he ⊢
  rw [hfluxeq, hforceeq, he, mul_neg]

/-- Physical-ball inhomogeneous Schauder regularity. Both the forcing
amplitude and the gradient amplitude are transported explicitly. -/
theorem exists_holder_forced_gradient_ball
    {d : ℕ} (hd : 0 < d) {Λ R : ℝ} (hR : 0 < R)
    (a : PDE.CoeffField d) (F : Vec d → Vec d)
    (ha : ∀ j k, ContDiff ℝ (⊤ : ℕ∞) (fun x => a x j k))
    (hF : ∃ B : ℝ, 0 ≤ B ∧ PDE.EuclideanFieldHolderSeminormLE
      (PDE.euclideanBall (0 : Vec d) R) F (1 / 2) B)
    (hell : ∀ x ∈ PDE.euclideanBall (0 : Vec d) R,
      PDE.IsEllipticMatrix 1 Λ (a x))
    (u : PDE.H1Function (PDE.euclideanBall (0 : Vec d) R))
    (hu : PDE.IsWeakDivergenceFormSolutionOn a
      (PDE.euclideanBall (0 : Vec d) R) u 0 F) :
    ∃ (G : Vec d → Vec d) (K : ℝ), 0 ≤ K ∧
      PDE.EuclideanFieldHolderSeminormLE
        (PDE.euclideanBall (0 : Vec d) (R * (1 / 2))) G (1 / 2) K ∧
      G =ᵐ[PDE.volumeOn (PDE.euclideanBall (0 : Vec d) (R * (1 / 2)))] u.grad := by
  obtain ⟨B, hB, hFH⟩ := hF
  have hscaled : ∃ K : ℝ, 0 ≤ K ∧ PDE.EuclideanFieldHolderSeminormLE
      (PDE.euclideanBall (0 : Vec d) 1)
      (fun y => R • F (R • y + 0)) (1 / 2) K := by
    refine ⟨R * B * R ^ (1 / 2 : ℝ), by positivity, ?_⟩
    intro x hx y hy
    have hxR : R • x ∈ PDE.euclideanBall (0 : Vec d) R := by
      simpa only [mul_one, add_zero] using
        (PDE.DGNM.affineScale_mem_euclideanBall_iff 0 hR 1 x).mpr hx
    have hyR : R • y ∈ PDE.euclideanBall (0 : Vec d) R := by
      simpa only [mul_one, add_zero] using
        (PDE.DGNM.affineScale_mem_euclideanBall_iff 0 hR 1 y).mpr hy
    have h := mul_le_mul_of_nonneg_left (hFH _ hxR _ hyR) hR.le
    simp only [add_zero]
    rw [← smul_sub, PDE.vecEuclideanNorm_smul, abs_of_pos hR]
    rw [← smul_sub, PDE.vecEuclideanNorm_smul, abs_of_pos hR,
      Real.mul_rpow hR.le (PDE.vecEuclideanNorm_nonneg _)] at h
    exact h.trans_eq (by ring)
  obtain ⟨G₀, K, hK, hGH, heq⟩ := exists_holder_gradient_halfBall hd
    (PDE.DGNM.blowUpCoeff a 0 R) (fun y => R • F (R • y + 0))
    (fun j k => (ha j k).comp (contDiff_id.const_smul R |>.add contDiff_const))
    hscaled (PDE.DGNM.blowUpCoeff_elliptic hell 0 hR (Set.Subset.refl _))
    (PDE.DGNM.blowUp u 0 hR (Set.Subset.refl _))
    (forced_solutionOn_blowUp (PDE.isOpen_euclideanBall 0 R) hu 0 hR (Set.Subset.refl _))
  have hmem {x : Vec d} (hx : x ∈ PDE.euclideanBall (0 : Vec d) (R * (1 / 2))) :
      R⁻¹ • x ∈ PDE.euclideanBall (0 : Vec d) (1 / 2) := by
    apply (PDE.DGNM.affineScale_mem_euclideanBall_iff 0 hR (1 / 2) (R⁻¹ • x)).mp
    simpa only [smul_smul, mul_inv_cancel₀ hR.ne', one_smul, add_zero] using hx
  refine ⟨fun x => R⁻¹ • G₀ (R⁻¹ • x), R⁻¹ * K * (R⁻¹) ^ (1 / 2 : ℝ),
    by positivity, ?_, ?_⟩
  · intro x hx y hy
    have h := mul_le_mul_of_nonneg_left
      (hGH _ (hmem hx) _ (hmem hy)) (inv_nonneg.mpr hR.le)
    rw [← smul_sub, PDE.vecEuclideanNorm_smul, abs_of_pos (inv_pos.mpr hR)]
    rw [← smul_sub, PDE.vecEuclideanNorm_smul, abs_of_pos (inv_pos.mpr hR),
      Real.mul_rpow (inv_nonneg.mpr hR.le) (PDE.vecEuclideanNorm_nonneg _)] at h
    exact h.trans_eq (by ring)
  · apply (PDE.DGNM.ae_comp_affineScale_ball_iff 0 hR (1 / 2)).mp
    filter_upwards [heq] with y hy
    simpa only [add_zero, smul_smul, inv_mul_cancel₀ hR.ne', one_smul,
      PDE.DGNM.blowUp_grad] using congrArg (fun ξ : Vec d => R⁻¹ • ξ) hy

/-- On a physical ball, smooth-coefficient harmonic gradients have an actual
Euclidean Hölder representative. The dilation factor stays in the constant. -/
theorem exists_holder_harmonic_gradient_ball
    {d : ℕ} (hd : 0 < d) {Λ R : ℝ} (hR : 0 < R)
    (a : PDE.CoeffField d)
    (ha : ∀ j k, ContDiff ℝ (⊤ : ℕ∞) (fun x => a x j k))
    (hell : ∀ x ∈ PDE.euclideanBall (0 : Vec d) R,
      PDE.IsEllipticMatrix 1 Λ (a x))
    (u : PDE.H1Function (PDE.euclideanBall (0 : Vec d) R))
    (hu : PDE.IsWeakDivergenceFormSolutionOn a
      (PDE.euclideanBall (0 : Vec d) R) u 0 0) :
    ∃ (G : Vec d → Vec d) (K : ℝ), 0 ≤ K ∧
      PDE.EuclideanFieldHolderSeminormLE
        (PDE.euclideanBall (0 : Vec d) (R * (1 / 2))) G (1 / 2) K ∧
      G =ᵐ[PDE.volumeOn (PDE.euclideanBall (0 : Vec d) (R * (1 / 2)))] u.grad := by
  let v := R⁻¹ • PDE.DGNM.blowUp u 0 hR (Set.Subset.refl _)
  have hv (y : Vec d) : v.grad y = u.grad (R • y) := by
    simp only [v, PDE.H1Function.smul_grad, PDE.DGNM.blowUp_grad,
      add_zero, smul_smul, inv_mul_cancel₀ hR.ne', one_smul]
  have hvs := PDE.DGNM.solutionOn_smul
    (PDE.DGNM.solutionOn_blowUp (PDE.isOpen_euclideanBall 0 R)
      hu 0 hR (Set.Subset.refl _)) R⁻¹
  have has (j k : Fin d) : ContDiff ℝ (⊤ : ℕ∞)
      (fun y => PDE.DGNM.blowUpCoeff a 0 R y j k) :=
    (ha j k).comp (contDiff_id.const_smul R |>.add contDiff_const)
  have hzero : ∃ B : ℝ, 0 ≤ B ∧ PDE.EuclideanFieldHolderSeminormLE
      (PDE.euclideanBall (0 : Vec d) 1) (0 : Vec d → Vec d) (1 / 2) B := by
    refine ⟨0, le_rfl, fun x _ y _ => ?_⟩
    change PDE.vecEuclideanNorm ((0 : Vec d) - 0) ≤ 0 * _
    rw [sub_self, PDE.vecEuclideanNorm_eq_zero_iff.mpr rfl, zero_mul]
  obtain ⟨G₀, K, hK, hG₀, heq⟩ := exists_holder_gradient_halfBall hd
    (PDE.DGNM.blowUpCoeff a 0 R) 0 has hzero
    (PDE.DGNM.blowUpCoeff_elliptic hell 0 hR (Set.Subset.refl _)) v hvs
  have hmem {x : Vec d} (hx : x ∈ PDE.euclideanBall (0 : Vec d) (R * (1 / 2))) :
      R⁻¹ • x ∈ PDE.euclideanBall (0 : Vec d) (1 / 2) := by
    apply (PDE.DGNM.affineScale_mem_euclideanBall_iff 0 hR (1 / 2)
      (R⁻¹ • x)).mp
    simpa only [smul_smul, mul_inv_cancel₀ hR.ne', one_smul, add_zero] using hx
  refine ⟨fun x => G₀ (R⁻¹ • x), K * (R⁻¹) ^ (1 / 2 : ℝ),
    mul_nonneg hK (Real.rpow_nonneg (inv_nonneg.mpr hR.le) _), ?_, ?_⟩
  · intro x hx y hy
    have h := hG₀ (R⁻¹ • x) (hmem hx) (R⁻¹ • y) (hmem hy)
    rw [← smul_sub, PDE.vecEuclideanNorm_smul, abs_of_pos (inv_pos.mpr hR),
      Real.mul_rpow (inv_nonneg.mpr hR.le) (PDE.vecEuclideanNorm_nonneg _)] at h
    exact h.trans_eq (mul_assoc _ _ _).symm
  · apply (PDE.DGNM.ae_comp_affineScale_ball_iff 0 hR (1 / 2)).mp
    filter_upwards [heq] with y hy
    simpa only [hv, add_zero, smul_smul, inv_mul_cancel₀ hR.ne', one_smul] using hy

/-- Subtracting the fixed affine gradient from the harmonic representative
preserves its Hölder bound and the literal source gradient's AE class. -/
theorem exists_holder_source_gradient_ball
    {d : ℕ} (hd : 0 < d) {Λ R : ℝ} (hR : 0 < R)
    (a : PDE.CoeffField d) (i : Fin d)
    (ha : ∀ j k, ContDiff ℝ (⊤ : ℕ∞) (fun x => a x j k))
    (hell : ∀ x ∈ PDE.euclideanBall (0 : Vec d) R,
      PDE.IsEllipticMatrix 1 Λ (a x))
    {u : Vec d → ℝ} {g : Vec d → Vec d}
    (hu : MemLp u 2 (volume.restrict (ball 0 R)))
    (hg : MemLp g 2 (volume.restrict (ball 0 R)))
    (hw : HasWeakGradient Set.univ u g)
    (he : HasWeakDivergence Set.univ
      (fun x => (a x).mulVec (unitVector i + g x)) (fun _ => 0)) :
    ∃ (G : Vec d → Vec d) (K : ℝ), 0 ≤ K ∧
      PDE.EuclideanFieldHolderSeminormLE
        (PDE.euclideanBall (0 : Vec d) (R * (1 / 2))) G (1 / 2) K ∧
      G =ᵐ[PDE.volumeOn (PDE.euclideanBall (0 : Vec d) (R * (1 / 2)))] g := by
  have hball : PDE.euclideanBall (0 : Vec d) R = ball 0 R := by
    ext x
    exact PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hR
  have hw' := Correctors.hasWeakGradient_mono (Set.subset_univ (ball 0 R)) hw
  have he' := Correctors.hasWeakDivergence_mono (Set.subset_univ (ball 0 R)) he
  have hsol := Correctors.affine_weakSolution_on_ball_of_weakPotential
    (0 : Vec d) R hR i a u g 0 (by simpa using hu) hg (by simpa using hw') he'
  rw [← hball] at hsol
  obtain ⟨G, K, hK, hG, heq⟩ := exists_holder_harmonic_gradient_ball hd hR a ha hell
    (EinsteinFull.pdeH1OfSpatialWeakSolution hsol)
    (EinsteinFull.pdeH1OfSpatialWeakSolution_isSolution hsol)
  refine ⟨fun x => G x - unitVector i, K, hK, ?_, ?_⟩
  · intro x hx y hy
    have hsub : (G x - unitVector i) - (G y - unitVector i) = G x - G y := by abel
    simpa only [hsub] using hG x hx y hy
  · filter_upwards [heq] with x hx
    change G x = unitVector i + g x at hx
    rw [hx]
    abel

/-- Multiplication of a Hölder gradient by a Hölder matrix retains both
terms in the differentiated forcing estimate, in the explicit Euclidean norm. -/
theorem holder_matrix_affine_gradient
    {d : ℕ} {U : Set (Vec d)} {A : PDE.CoeffField d} {g : Vec d → Vec d}
    {α KA Kg M B : ℝ} (e : Vec d)
    (hA : PDE.EuclideanMatrixHolderSeminormLE U A α KA)
    (hg : PDE.EuclideanFieldHolderSeminormLE U g α Kg)
    (hKA : 0 ≤ KA) (hM : 0 ≤ M)
    (hAb : ∀ x ∈ U, ∀ ξ : Vec d,
      PDE.vecEuclideanNorm (PDE.matVecMul (A x) ξ) ≤ M * PDE.vecEuclideanNorm ξ)
    (hgb : ∀ x ∈ U, PDE.vecEuclideanNorm (e + g x) ≤ B) :
    PDE.EuclideanFieldHolderSeminormLE U
      (fun x => PDE.matVecMul (A x) (e + g x)) α (M * Kg + KA * B) := by
  intro x hx y hy
  have hsplit : PDE.matVecMul (A x) (e + g x) -
      PDE.matVecMul (A y) (e + g y) =
      PDE.matVecMul (A x) (g x - g y) +
        PDE.matVecMul (A x - A y) (e + g y) := by
    change (A x).mulVec (e + g x) - (A y).mulVec (e + g y) =
      (A x).mulVec (g x - g y) + (A x - A y).mulVec (e + g y)
    simp only [Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.sub_mulVec]
    abel
  rw [hsplit]
  calc
    PDE.vecEuclideanNorm (PDE.matVecMul (A x) (g x - g y) +
        PDE.matVecMul (A x - A y) (e + g y)) ≤
        PDE.vecEuclideanNorm (PDE.matVecMul (A x) (g x - g y)) +
          PDE.vecEuclideanNorm (PDE.matVecMul (A x - A y) (e + g y)) :=
      PDE.vecEuclideanNorm_add_le _ _
    _ ≤ M * PDE.vecEuclideanNorm (g x - g y) +
        (KA * PDE.vecEuclideanNorm (x - y) ^ α) *
          PDE.vecEuclideanNorm (e + g y) :=
      add_le_add (hAb x hx _) (hA x hx y hy _)
    _ ≤ M * (Kg * PDE.vecEuclideanNorm (x - y) ^ α) +
        (KA * PDE.vecEuclideanNorm (x - y) ^ α) * B :=
      add_le_add (mul_le_mul_of_nonneg_left (hg x hx y hy) hM)
        (mul_le_mul_of_nonneg_left (hgb y hy)
          (mul_nonneg hKA (Real.rpow_nonneg (PDE.vecEuclideanNorm_nonneg _) _)))
    _ = (M * Kg + KA * B) * PDE.vecEuclideanNorm (x - y) ^ α := by ring

/-- A smooth matrix field has a Euclidean operator Hölder bound on every
positive physical ball, with the dilation absorbed in the constant. -/
theorem exists_holder_matrix_ball
    {d : ℕ} {A : PDE.CoeffField d} (hA : ∀ j k,
      ContDiff ℝ (⊤ : ℕ∞) (fun x => A x j k)) {R : ℝ} (hR : 0 < R) :
    ∃ K : ℝ, 0 ≤ K ∧ PDE.EuclideanMatrixHolderSeminormLE
      (PDE.euclideanBall (0 : Vec d) R) A (1 / 2) K := by
  obtain ⟨K, hK, hAK⟩ :=
    PDE.exists_euclideanMatrixHolderSeminormLE_half_of_contDiff
      (fun j k => (hA j k).comp (contDiff_id.const_smul R))
  have hmem {x : Vec d} (hx : x ∈ PDE.euclideanBall (0 : Vec d) R) :
      R⁻¹ • x ∈ PDE.euclideanBall (0 : Vec d) 1 := by
    apply (PDE.DGNM.affineScale_mem_euclideanBall_iff 0 hR 1 (R⁻¹ • x)).mp
    simpa only [mul_one, smul_smul, mul_inv_cancel₀ hR.ne', one_smul, add_zero] using hx
  refine ⟨K * (R⁻¹) ^ (1 / 2 : ℝ),
    mul_nonneg hK (Real.rpow_nonneg (inv_nonneg.mpr hR.le) _), ?_⟩
  intro x hx y hy ξ
  have h := hAK (R⁻¹ • x) (hmem hx) (R⁻¹ • y) (hmem hy) ξ
  simp only [Function.comp_apply, id_eq, smul_smul, mul_inv_cancel₀ hR.ne', one_smul] at h
  rw [← smul_sub, PDE.vecEuclideanNorm_smul, abs_of_pos (inv_pos.mpr hR),
    Real.mul_rpow (inv_nonneg.mpr hR.le) (PDE.vecEuclideanNorm_nonneg _)] at h
  exact h.trans_eq (by ring)

/-- An entrywise absolute sum bounds the Euclidean action of any matrix;
no ellipticity of a differentiated coefficient matrix is assumed. -/
theorem matrix_action_le_sum_abs {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (ξ : Vec d) :
    PDE.vecEuclideanNorm (PDE.matVecMul A ξ) ≤
      (∑ i : Fin d, ∑ j : Fin d, |A i j|) * PDE.vecEuclideanNorm ξ := by
  calc
    PDE.vecEuclideanNorm (PDE.matVecMul A ξ) ≤
        ∑ i : Fin d, |PDE.matVecMul A ξ i| := PDE.vecEuclideanNorm_le_sum_abs _
    _ ≤ ∑ i : Fin d, ∑ j : Fin d, |A i j| * PDE.vecEuclideanNorm ξ := by
      apply Finset.sum_le_sum
      intro i _
      calc
        |PDE.matVecMul A ξ i| ≤ ∑ j : Fin d, |A i j| * |ξ j| := by
          unfold PDE.matVecMul
          exact (Finset.abs_sum_le_sum_abs _ _).trans_eq
            (Finset.sum_congr rfl fun j _ => abs_mul _ _)
        _ ≤ ∑ j : Fin d, |A i j| * PDE.vecEuclideanNorm ξ :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left
            (PDE.abs_apply_le_vecEuclideanNorm ξ j) (abs_nonneg _)
    _ = (∑ i : Fin d, ∑ j : Fin d, |A i j|) * PDE.vecEuclideanNorm ξ := by
      simp only [Finset.sum_mul]

/-- The differentiated source is Hölder whenever its smooth matrix factor
multiplies the actual continuous, locally Hölder gradient. -/
theorem exists_holder_smooth_matrix_affine_gradient_ball
    {d : ℕ} {A : PDE.CoeffField d} {g : Vec d → Vec d}
    (hA : ∀ j k, ContDiff ℝ (⊤ : ℕ∞) (fun x => A x j k))
    (hg : Continuous g) (e : Vec d) {R : ℝ} (hR : 0 < R)
    (hgH : ∃ K : ℝ, 0 ≤ K ∧ PDE.EuclideanFieldHolderSeminormLE
      (PDE.euclideanBall (0 : Vec d) R) g (1 / 2) K) :
    ∃ K : ℝ, 0 ≤ K ∧ PDE.EuclideanFieldHolderSeminormLE
      (PDE.euclideanBall (0 : Vec d) R)
      (fun x => PDE.matVecMul (A x) (e + g x)) (1 / 2) K := by
  obtain ⟨KA, hKA, hAH⟩ := exists_holder_matrix_ball hA hR
  obtain ⟨Kg, hKg, hgH⟩ := hgH
  have hsum : Continuous (fun x => ∑ i : Fin d, ∑ j : Fin d, |A x i j|) := by
    fun_prop
  obtain ⟨M, hM⟩ :=
    (PDE.isCompact_euclideanClosedBall (0 : Vec d) hR.le).exists_bound_of_continuousOn
      hsum.continuousOn
  obtain ⟨B, hB⟩ :=
    (PDE.isCompact_euclideanClosedBall (0 : Vec d) hR.le).exists_bound_of_continuousOn
      (PDE.continuous_vecEuclideanNorm.comp
        ((continuous_const : Continuous (fun _ : Vec d => e)).add hg)).continuousOn
  refine ⟨max M 0 * Kg + KA * max B 0, by positivity, ?_⟩
  apply holder_matrix_affine_gradient e hAH hgH hKA (le_max_right _ _)
  · intro x hx ξ
    apply (matrix_action_le_sum_abs (A x) ξ).trans
    apply mul_le_mul_of_nonneg_right _ (PDE.vecEuclideanNorm_nonneg _)
    have h := hM x (PDE.euclideanBall_subset_euclideanClosedBall _ _ hx)
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => abs_nonneg _)] at h
    exact h.trans (le_max_left _ _)
  · intro x hx
    have h := hB x (PDE.euclideanBall_subset_euclideanClosedBall _ _ hx)
    change ‖PDE.vecEuclideanNorm (e + g x)‖ ≤ B at h
    rw [Real.norm_eq_abs, abs_of_nonneg (PDE.vecEuclideanNorm_nonneg _)] at h
    exact h.trans (le_max_left _ _)

/-- Difference quotients retain their actual weak gradient. The scalar can
be zero; no sign restriction on the translation parameter is used. -/
theorem weakGradient_differenceQuotient {d : ℕ}
    {u : Vec d → ℝ} {g : Vec d → Vec d}
    (hw : HasWeakGradient Set.univ u g) (z : Vec d) (t : ℝ) :
    HasWeakGradient Set.univ (fun x => t⁻¹ * (u (z + x) - u x))
      (fun x => t⁻¹ • (g (z + x) - g x)) := by
  have h := Correctors.hasWeakGradient_sub (hw.translated z) hw
  intro j
  refine ⟨fun x hx => ((h j).1 x hx).smul t⁻¹,
    fun x hx => ((h j).2.1 x hx).smul t⁻¹, ?_⟩
  intro ψ hψ
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]
  rw [(h j).2.2 ψ hψ, mul_neg]

private theorem weakDivergence_const_smul {d : ℕ}
    {F : Vec d → Vec d} (hw : HasWeakDivergence Set.univ F (fun _ => 0))
    (c : ℝ) : HasWeakDivergence Set.univ (fun x => c • F x) (fun _ => 0) := by
  refine ⟨fun j x hx => ((hw.1 j) x hx).smul c,
    locallyIntegrableOn_zero, ?_⟩
  intro ψ hψ
  have hdot (x : Vec d) : dot (c • F x) (gradient ψ x) =
      c * dot (F x) (gradient ψ x) := by
    simp only [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
  simp only [hdot, integral_const_mul]
  have he := hw.2.2 ψ hψ
  simpa only [zero_mul, integral_zero, neg_zero, mul_zero] using congrArg (c * ·) he

private theorem weakDivergence_translate {d : ℕ}
    {F : Vec d → Vec d} (hw : HasWeakDivergence Set.univ F (fun _ => 0))
    (z : Vec d) : HasWeakDivergence Set.univ (fun x => F (z + x)) (fun _ => 0) := by
  refine ⟨?_, locallyIntegrableOn_zero, ?_⟩
  · intro j
    rw [locallyIntegrableOn_univ]
    have hj := hw.1 j
    rw [locallyIntegrableOn_univ] at hj
    have hm : (volume : Measure (Vec d)).map (Homeomorph.addLeft z) = volume :=
      (measurePreserving_add_left volume z).map_eq
    have hh := (locallyIntegrable_map_homeomorph (Homeomorph.addLeft z)
      (f := fun x => F x j) (μ := (volume : Measure (Vec d)))).mp
    exact hh (by rwa [hm])
  · intro ψ hψ
    let η : Vec d → ℝ := fun x => ψ (-z + x)
    have hη : IsSpatialTest Set.univ η :=
      ⟨hψ.1.comp (contDiff_const.add contDiff_id),
        hψ.2.1.comp_homeomorph (Homeomorph.addLeft (-z)), Set.subset_univ _⟩
    have he := hw.2.2 η hη
    simp only [Measure.restrict_univ, zero_mul, integral_zero, neg_zero] at he ⊢
    have ht (f : Vec d → ℝ) : (∫ x, f (z + x)) = ∫ x, f x :=
      (measurePreserving_add_left (volume : Measure (Vec d)) z).integral_comp
        (Homeomorph.addLeft z).measurableEmbedding f
    have hg (x : Vec d) : gradient η (z + x) = gradient ψ x := by
      ext j
      simp only [gradient, coordinateDerivative, η, fderiv_comp_add_left,
        neg_add_cancel_left]
    rw [← ht (fun x => dot (F x) (gradient η x))] at he
    simpa only [hg] using he

/-- The translated affine corrector equation gives the inhomogeneous
finite-difference equation. Its coefficient commutator is retained explicitly. -/
theorem weakDivergence_differenceQuotient {d : ℕ}
    {a : Vec d → Mat d} {g : Vec d → Vec d} (e : Vec d)
    (hw : HasWeakDivergence Set.univ
      (fun x => (a x).mulVec (e + g x)) (fun _ => 0))
    (z : Vec d) (t : ℝ) :
    HasWeakDivergence Set.univ
      (fun x => (a x).mulVec (t⁻¹ • (g (z + x) - g x)) +
        t⁻¹ • ((a (z + x) - a x).mulVec (e + g (z + x)))) (fun _ => 0) := by
  have ht' := weakDivergence_translate hw z
  have hs := Correctors.hasWeakDivergence_sub ht' hw
  simp only [sub_self] at hs
  apply Correctors.hasWeakDivergence_congr_ae isOpen_univ
    (weakDivergence_const_smul hs t⁻¹) _ Filter.EventuallyEq.rfl
  apply Filter.Eventually.of_forall
  intro x
  change t⁻¹ • ((a (z + x)).mulVec (e + g (z + x)) - (a x).mulVec (e + g x)) = _
  dsimp only
  rw [Matrix.mulVec_smul, Matrix.sub_mulVec, Matrix.mulVec_sub]
  simp only [Matrix.mulVec_add]
  module

/-- Differencing a forced affine equation retains both the coefficient
commutator and the difference quotient of its original forcing. -/
theorem weakDivergence_forced_differenceQuotient {d : ℕ}
    {a : Vec d → Mat d} {g F : Vec d → Vec d} (e : Vec d)
    (hw : HasWeakDivergence Set.univ
      (fun x => (a x).mulVec (e + g x) + F x) (fun _ => 0))
    (z : Vec d) (t : ℝ) :
    HasWeakDivergence Set.univ
      (fun x => (a x).mulVec (t⁻¹ • (g (z + x) - g x)) +
        (t⁻¹ • ((a (z + x) - a x).mulVec (e + g (z + x))) +
          t⁻¹ • (F (z + x) - F x))) (fun _ => 0) := by
  have ht' := weakDivergence_translate hw z
  have hs := Correctors.hasWeakDivergence_sub ht' hw
  simp only [sub_self] at hs
  apply Correctors.hasWeakDivergence_congr_ae isOpen_univ
    (weakDivergence_const_smul hs t⁻¹) _ Filter.EventuallyEq.rfl
  apply Filter.Eventually.of_forall
  intro x
  change t⁻¹ • (((a (z + x)).mulVec (e + g (z + x)) + F (z + x)) -
    ((a x).mulVec (e + g x) + F x)) = _
  dsimp only
  rw [Matrix.mulVec_smul, Matrix.sub_mulVec, Matrix.mulVec_sub]
  simp only [Matrix.mulVec_add]
  module

section Energy
open PDE PDE.DGNM

/-- The square cutoff test for an equation with a genuine divergence forcing.
The forcing contributes both its gradient and cutoff pairings. -/
theorem forced_square_test {d : ℕ} {U : Set (PDE.Vec d)} {a : PDE.CoeffField d}
    (hU : PDE.IsOpenBoundedConvexDomain U) {u : PDE.H1Function U}
    {F : PDE.Vec d → PDE.Vec d}
    (hsol : PDE.IsWeakDivergenceFormL2SolutionOn a U u (fun _ => 0) F)
    {η : PDE.Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηc : HasCompactSupport η) (hηU : tsupport η ⊆ U) :
    IntegrableOn (fun x => η x ^ 2 *
      PDE.vecDot (PDE.matVecMul (a x) (u.grad x)) (u.grad x)) U ∧
    IntegrableOn (fun x => 2 * η x * u x *
      PDE.vecDot (PDE.matVecMul (a x) (u.grad x)) (PDE.classicalGradient η x)) U ∧
    IntegrableOn (fun x => η x ^ 2 * PDE.vecDot (F x) (u.grad x)) U ∧
    IntegrableOn (fun x => 2 * η x * u x *
      PDE.vecDot (F x) (PDE.classicalGradient η x)) U ∧
    (∫ x in U, η x ^ 2 * PDE.vecDot (PDE.matVecMul (a x) (u.grad x)) (u.grad x)) +
      (∫ x in U, 2 * η x * u x *
        PDE.vecDot (PDE.matVecMul (a x) (u.grad x)) (PDE.classicalGradient η x)) =
      -(∫ x in U, η x ^ 2 * PDE.vecDot (F x) (u.grad x)) -
        ∫ x in U, 2 * η x * u x * PDE.vecDot (F x) (PDE.classicalGradient η x) := by
  have hs := contDiff_sq hη
  have hc := hasCompactSupport_sq hηc
  have hUη := tsupport_sq_subset hηU
  obtain ⟨h1, h2, he⟩ := integral_vecDot_productTest hU hsol.flux_memL2 u hs hc hUη
  obtain ⟨h3, h4, hf⟩ := integral_vecDot_productTest hU hsol.forcing_memL2 u hs hc hUη
  have heq := (hsol.toH10SolutionOn
    (u.mulContDiffHasCompactSupportToH10 hU hs hc hUη)).2
  rw [he, hf] at heq
  have hcross (G : PDE.Vec d → PDE.Vec d) :
      (fun x => u x * PDE.vecDot (G x) (PDE.classicalGradient (fun y => η y ^ 2) x)) =
        (fun x => 2 * η x * u x * PDE.vecDot (G x) (PDE.classicalGradient η x)) := by
    funext x
    rw [classicalGradient_sq hη, vecDot_smul_right]
    ring
  simp only [hcross] at h2 h4 heq
  refine ⟨h1, h2, h3, h4, ?_⟩
  simp only [zero_mul, integral_zero] at heq
  linarith

/-- Inhomogeneous Caccioppoli estimate. In particular, the commutator in a
coefficient difference quotient is controlled rather than discarded. -/
theorem forced_caccioppoli {d : ℕ} {U : Set (PDE.Vec d)} {a : PDE.CoeffField d}
    {Λ : ℝ} (hU : PDE.IsOpenBoundedConvexDomain U)
    (hEll : ∀ x ∈ U, PDE.IsEllipticMatrix 1 Λ (a x))
    {u : PDE.H1Function U} {F : PDE.Vec d → PDE.Vec d}
    (hsol : PDE.IsWeakDivergenceFormL2SolutionOn a U u (fun _ => 0) F)
    {η : PDE.Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηc : HasCompactSupport η) (hηU : tsupport η ⊆ U) :
    (∫ x in U, η x ^ 2 * PDE.vecDot (u.grad x) (PDE.matVecMul (a x) (u.grad x))) ≤
      (8 * Λ + 4) * (∫ x in U, u x ^ 2 * PDE.vecNormSq (PDE.classicalGradient η x)) +
        8 * ∫ x in U, η x ^ 2 * PDE.vecNormSq (F x) := by
  obtain ⟨h1, h2, h3, h4, heq⟩ := forced_square_test hU hsol hη hηc hηU
  simp only [PDE.vecDot_comm (PDE.matVecMul _ _) (u.grad _)] at h1 heq
  have hG : PDE.MemVectorL2On U (fun x => u x • PDE.classicalGradient η x) := by
    intro j
    simpa only [Pi.smul_apply, smul_eq_mul, mul_comm] using
      u.memL2.fun_mul (memLpOn_top_classicalGradient hη hηc j)
  have hH : PDE.MemVectorL2On U (fun x => η x • F x) := by
    intro j
    simpa only [Pi.smul_apply, smul_eq_mul, mul_comm] using
      (hsol.forcing_memL2 j).fun_mul (memLpOn_top_of_contDiff hη hηc)
  have hV : IntegrableOn
      (fun x => u x ^ 2 * PDE.vecNormSq (PDE.classicalGradient η x)) U := by
    simpa only [PDE.vecNormSq_smul] using PDE.integrableOn_vecNormSq_of_memVectorL2On hG
  have hF : IntegrableOn (fun x => η x ^ 2 * PDE.vecNormSq (F x)) U := by
    simpa only [PDE.vecNormSq_smul] using PDE.integrableOn_vecNormSq_of_memVectorL2On hH
  have hmem : ∀ᵐ x ∂PDE.volumeOn U, x ∈ U :=
    (ae_restrict_iff' hU.measurableSet).2 (Eventually.of_forall fun _ hx => hx)
  have hp : ∀ᵐ x ∂PDE.volumeOn U,
      -(2 * η x * u x * PDE.vecDot (PDE.matVecMul (a x) (u.grad x))
          (PDE.classicalGradient η x) + η x ^ 2 * PDE.vecDot (F x) (u.grad x) +
          2 * η x * u x * PDE.vecDot (F x) (PDE.classicalGradient η x)) ≤
        3 / 4 * (η x ^ 2 * PDE.vecDot (u.grad x) (PDE.matVecMul (a x) (u.grad x))) +
          (2 * Λ + 1) * (u x ^ 2 * PDE.vecNormSq (PDE.classicalGradient η x)) +
          2 * (η x ^ 2 * PDE.vecNormSq (F x)) := by
    filter_upwards [hmem] with x hx
    have ha := abs_two_mul_mul_vecDot_le_caccioppoli
      (η := η x) (w := u x) (hEll x hx) (u.grad x) (PDE.classicalGradient η x)
    have hb := PDE.abs_mul_mul_vecDot_le_add_halves_mul_sq_vecNormSq
      (2 * η x) (η x) (F x) (u.grad x)
    have hc := PDE.abs_mul_mul_vecDot_le_add_halves_mul_sq_vecNormSq
      (η x) (u x) (F x) (PDE.classicalGradient η x)
    have hg := mul_le_mul_of_nonneg_left
      (vecNormSq_le_vecDot_matVecMul (hEll x hx) (u.grad x)) (sq_nonneg (η x))
    have hbn : -(η x ^ 2 * PDE.vecDot (F x) (u.grad x)) ≤
        η x ^ 2 * PDE.vecNormSq (F x) +
          (η x ^ 2 * PDE.vecDot (u.grad x) (PDE.matVecMul (a x) (u.grad x))) / 4 := by
      have hab : |2 * η x * η x * PDE.vecDot (F x) (u.grad x)| =
          2 * |η x ^ 2 * PDE.vecDot (F x) (u.grad x)| := by
        rw [← abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num), ← abs_mul]
        congr 1
        ring
      rw [hab] at hb
      nlinarith [neg_abs_le (η x ^ 2 * PDE.vecDot (F x) (u.grad x))]
    have hcn : -(2 * η x * u x * PDE.vecDot (F x) (PDE.classicalGradient η x)) ≤
        η x ^ 2 * PDE.vecNormSq (F x) +
          u x ^ 2 * PDE.vecNormSq (PDE.classicalGradient η x) := by
      have hn := neg_abs_le (η x * u x * PDE.vecDot (F x) (PDE.classicalGradient η x))
      linarith
    have han := neg_abs_le (2 * η x * u x *
      PDE.vecDot (PDE.matVecMul (a x) (u.grad x)) (PDE.classicalGradient η x))
    linarith
  have hleft := ((h2.add h3).add h4).neg
  have hright := ((h1.const_mul (3 / 4)).add (hV.const_mul (2 * Λ + 1))).add
    (hF.const_mul 2)
  have hi := integral_mono_ae hleft hright hp
  simp only [Pi.neg_apply, Pi.add_apply] at hi
  have hl := integral_add (h2.add h3) h4
  have hl' := integral_add h2 h3
  have hr := integral_add ((h1.const_mul (3 / 4)).add (hV.const_mul (2 * Λ + 1)))
    (hF.const_mul 2)
  have hr' := integral_add (h1.const_mul (3 / 4)) (hV.const_mul (2 * Λ + 1))
  simp only [Pi.add_apply] at hl hl' hr hr'
  rw [integral_neg, hl, hl', hr, hr', integral_const_mul, integral_const_mul,
    integral_const_mul] at hi
  linarith

end Energy

/-- Convert the literal spatial equation with an explicit forcing into the
`L²` PDE interface, so square-cutoff testing needs no extra test premise. -/
theorem sourceH1_forced_isL2Solution {d : ℕ} {U : Set (Vec d)}
    {a : Vec d → Mat d} {Λ : ℝ}
    (hell : PDE.IsEllipticFieldOn 1 Λ U a)
    {u : Vec d → ℝ} {g F : Vec d → Vec d}
    (hu : MemLp u 2 (volume.restrict U)) (hg : MemLp g 2 (volume.restrict U))
    (hF : PDE.MemVectorL2On U F) (hw : HasWeakGradient Set.univ u g)
    (he : HasWeakDivergence Set.univ (fun x => (a x).mulVec (g x) + F x) (fun _ => 0)) :
    PDE.IsWeakDivergenceFormL2SolutionOn a U (C3SublinearC1.sourceH1 hu hg hw)
      (fun _ => 0) F := by
  have hdata : PDE.DivergenceFormL2DataOn a U (C3SublinearC1.sourceH1 hu hg hw)
      (fun _ => 0) F :=
    PDE.DivergenceFormL2DataOn.of_isEllipticFieldOn hell MemLp.zero hF
  refine ⟨hdata, ?_⟩
  intro ψ
  have ht := hdata.testable ψ
  have he' := Correctors.hasWeakDivergence_mono (Set.subset_univ U) he
  have heq := he'.2.2 ψ.toFun ⟨ψ.contDiff, ψ.hasCompactSupport, ψ.tsupport_subset⟩
  have hpoint (x : Vec d) :
      dot ((a x).mulVec (g x) + F x) (gradient ψ.toFun x) =
        PDE.vecDot (PDE.matVecMul (a x) ((C3SublinearC1.sourceH1 hu hg hw).grad x))
          (ψ.grad x) + PDE.vecDot (F x) (ψ.grad x) := by
    simp only [dot, gradient, coordinateDerivative,
      PDE.vecDot, PDE.matVecMul, PDE.WeakTestFunction.grad,
      PDE.WeakTestFunction.partialDeriv, PDE.basisVec, unitVector,
      C3SublinearC1.sourceH1, Matrix.mulVec, dotProduct, Pi.add_apply,
      Finset.sum_add_distrib, add_mul]
  simp only [zero_mul, integral_zero, neg_zero] at heq
  simp_rw [hpoint] at heq
  rw [integral_add ht.flux_integrable ht.forcing_integrable] at heq
  simp only [zero_mul, integral_zero, zero_sub]
  linarith

private theorem continuous_memLp_bounded {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [SecondCountableTopology E]
    {U : Set (Vec d)} (hU : PDE.IsOpenBoundedConvexDomain U) {f : Vec d → E}
    (hf : Continuous f) : MemLp f 2 (volume.restrict U) := by
  have : IsFiniteMeasure (PDE.volumeOn U) :=
    hU.isSobolevRegularDomain.isFiniteMeasure_volumeOn
  obtain ⟨C, hC⟩ := hU.isBoundedDomain.isBounded.isCompact_closure.exists_bound_of_continuousOn
    hf.continuousOn
  refine MemLp.of_bound hf.aestronglyMeasurable C ?_
  rw [ae_restrict_iff' hU.measurableSet]
  exact Eventually.of_forall fun x hx => hC x (subset_closure hx)

/-- Apply the forced energy estimate to the literal affine-equation difference
quotient. Local `L²` data follow from the already available continuity. -/
theorem differenceQuotient_energy {d : ℕ} {U : Set (Vec d)} {Λ : ℝ}
    (hU : PDE.IsOpenBoundedConvexDomain U) {a : Vec d → Mat d}
    (hell : PDE.IsEllipticFieldOn 1 Λ U a)
    (ha : ∀ j k, Continuous (fun x => a x j k))
    {u : Vec d → ℝ} {g : Vec d → Vec d} (hu : Continuous u) (hg : Continuous g)
    (hw : HasWeakGradient Set.univ u g) (e : Vec d)
    (he : HasWeakDivergence Set.univ (fun x => (a x).mulVec (e + g x)) (fun _ => 0))
    (z : Vec d) (t : ℝ) {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηc : HasCompactSupport η) (hηU : tsupport η ⊆ U) :
    let q := fun x => t⁻¹ * (u (z + x) - u x)
    let G := fun x => t⁻¹ • (g (z + x) - g x)
    let F := fun x => t⁻¹ • ((a (z + x) - a x).mulVec (e + g (z + x)))
    (∫ x in U, η x ^ 2 * PDE.vecDot (G x) (PDE.matVecMul (a x) (G x))) ≤
      (8 * Λ + 4) * (∫ x in U, q x ^ 2 * PDE.vecNormSq (PDE.classicalGradient η x)) +
        8 * ∫ x in U, η x ^ 2 * PDE.vecNormSq (F x) := by
  let q := fun x => t⁻¹ * (u (z + x) - u x)
  let G := fun x => t⁻¹ • (g (z + x) - g x)
  let F := fun x => t⁻¹ • ((a (z + x) - a x).mulVec (e + g (z + x)))
  have hq : Continuous q := continuous_const.mul
    ((hu.comp (continuous_const.add continuous_id)).sub hu)
  have hG : Continuous G := (continuous_const : Continuous (fun _ : Vec d => t⁻¹)).smul
    ((hg.comp (continuous_const.add continuous_id)).sub hg)
  have hF : Continuous F := by
    apply continuous_pi
    intro j
    change Continuous (fun x => t⁻¹ * ∑ k, (a (z + x) j k - a x j k) *
      (e k + g (z + x) k))
    apply continuous_const.mul
    apply continuous_finsetSum
    intro k _
    exact ((ha j k).comp (continuous_const.add continuous_id) |>.sub (ha j k)).mul
      (continuous_const.add (((continuous_apply k).comp hg).comp
        (continuous_const.add continuous_id)))
  have hqL := continuous_memLp_bounded hU hq
  have hGL := continuous_memLp_bounded hU hG
  have hFL : PDE.MemVectorL2On U F := by
    intro j
    exact (continuous_memLp_bounded hU hF).continuousLinearMap_comp
      (ContinuousLinearMap.proj j : Vec d →L[ℝ] ℝ)
  have hqw := weakGradient_differenceQuotient hw z t
  have hqe := weakDivergence_differenceQuotient e he z t
  have hsol := sourceH1_forced_isL2Solution hell hqL hGL hFL hqw hqe
  exact forced_caccioppoli hU hell.2 hsol hη hηc hηU

/-- The quotient energy estimate for a nonzero original forcing keeps its
source quotient in the full forcing term. -/
theorem forced_differenceQuotient_energy {d : ℕ} {U : Set (Vec d)} {Λ : ℝ}
    (hU : PDE.IsOpenBoundedConvexDomain U) {a : Vec d → Mat d}
    (hell : PDE.IsEllipticFieldOn 1 Λ U a)
    (ha : ∀ j k, Continuous (fun x => a x j k))
    {u : Vec d → ℝ} {g B : Vec d → Vec d}
    (hu : Continuous u) (hg : Continuous g) (hB : Continuous B)
    (hw : HasWeakGradient Set.univ u g) (e : Vec d)
    (he : HasWeakDivergence Set.univ (fun x => (a x).mulVec (e + g x) + B x) (fun _ => 0))
    (z : Vec d) (t : ℝ) {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηc : HasCompactSupport η) (hηU : tsupport η ⊆ U) :
    let q := fun x => t⁻¹ * (u (z + x) - u x)
    let G := fun x => t⁻¹ • (g (z + x) - g x)
    let F := fun x => t⁻¹ • ((a (z + x) - a x).mulVec (e + g (z + x))) +
      t⁻¹ • (B (z + x) - B x)
    (∫ x in U, η x ^ 2 * PDE.vecDot (G x) (PDE.matVecMul (a x) (G x))) ≤
      (8 * Λ + 4) * (∫ x in U, q x ^ 2 * PDE.vecNormSq (PDE.classicalGradient η x)) +
        8 * ∫ x in U, η x ^ 2 * PDE.vecNormSq (F x) := by
  let q := fun x => t⁻¹ * (u (z + x) - u x)
  let G := fun x => t⁻¹ • (g (z + x) - g x)
  let F := fun x => t⁻¹ • ((a (z + x) - a x).mulVec (e + g (z + x))) +
      t⁻¹ • (B (z + x) - B x)
  have hq : Continuous q := continuous_const.mul
    ((hu.comp (continuous_const.add continuous_id)).sub hu)
  have hG : Continuous G := (continuous_const : Continuous (fun _ : Vec d => t⁻¹)).smul
    ((hg.comp (continuous_const.add continuous_id)).sub hg)
  have hF : Continuous F := by
    apply Continuous.add ?_
      ((continuous_const : Continuous (fun _ : Vec d => t⁻¹)).smul
        ((hB.comp (continuous_const.add continuous_id)).sub hB))
    apply continuous_pi
    intro j
    change Continuous (fun x => t⁻¹ * ∑ k, (a (z + x) j k - a x j k) *
      (e k + g (z + x) k))
    apply continuous_const.mul
    apply continuous_finsetSum
    intro k _
    exact ((ha j k).comp (continuous_const.add continuous_id) |>.sub (ha j k)).mul
      (continuous_const.add (((continuous_apply k).comp hg).comp
        (continuous_const.add continuous_id)))
  have hqL := continuous_memLp_bounded hU hq
  have hGL := continuous_memLp_bounded hU hG
  have hFL : PDE.MemVectorL2On U F := by
    intro j
    exact (continuous_memLp_bounded hU hF).continuousLinearMap_comp
      (ContinuousLinearMap.proj j : Vec d →L[ℝ] ℝ)
  have hqw := weakGradient_differenceQuotient hw z t
  have hqe := weakDivergence_forced_differenceQuotient e he z t
  have hsol := sourceH1_forced_isL2Solution hell hqL hGL hFL hqw hqe
  exact forced_caccioppoli hU hell.2 hsol hη hηc hηU

/-- A signed directional quotient of a Lipschitz coefficient has a bound
independent of the nonzero step size. -/
theorem coefficient_commutator_bound {d : ℕ} {a : Vec d → Mat d} {L : ℝ}
    (ha : IsOperatorLipschitz L a) (x z ξ : Vec d) {t : ℝ} (ht : t ≠ 0) :
    euclideanNorm (t⁻¹ • ((a (t • z + x) - a x).mulVec ξ)) ≤
      L * euclideanNorm z * euclideanNorm ξ := by
  have hn (c : ℝ) (v : Vec d) : euclideanNorm (c • v) = |c| * euclideanNorm v :=
    PDE.vecEuclideanNorm_smul c v
  calc
    euclideanNorm (t⁻¹ • ((a (t • z + x) - a x).mulVec ξ)) =
        |t⁻¹| * euclideanNorm ((a (t • z + x) - a x).mulVec ξ) := hn _ _
    _ ≤ |t⁻¹| * (L * euclideanNorm (t • z + x - x) * euclideanNorm ξ) :=
      mul_le_mul_of_nonneg_left (ha _ _ _) (abs_nonneg _)
    _ = L * euclideanNorm z * euclideanNorm ξ := by
      rw [add_sub_cancel_right, hn, abs_inv]
      field_simp

/-- Squared Euclidean form of the commutator bound, as needed by the
inhomogeneous energy estimate. -/
theorem coefficient_commutator_sq_bound {d : ℕ} {a : Vec d → Mat d} {L : ℝ}
    (ha : IsOperatorLipschitz L a) (x z ξ : Vec d) {t : ℝ} (ht : t ≠ 0) :
    PDE.vecNormSq (t⁻¹ • ((a (t • z + x) - a x).mulVec ξ)) ≤
      L ^ 2 * PDE.vecNormSq z * PDE.vecNormSq ξ := by
  have h := coefficient_commutator_bound ha x z ξ ht
  change PDE.vecEuclideanNorm _ ≤ L * PDE.vecEuclideanNorm z * PDE.vecEuclideanNorm ξ at h
  have hs := mul_self_le_mul_self (PDE.vecEuclideanNorm_nonneg _) h
  simp only [← pow_two, mul_pow, PDE.vecEuclideanNorm_sq] at hs
  exact hs

/-- On a bounded domain, a `C¹` potential and continuous gradient supply
uniform bounds for the scalar quotient and shifted affine gradient. -/
theorem exists_uniform_quotient_data_bound {d : ℕ} {U : Set (Vec d)}
    (hU : Bornology.IsBounded U) {u : Vec d → ℝ} {g : Vec d → Vec d}
    (hu : ContDiff ℝ (1 : ℕ∞) u) (hg : Continuous g) (e z : Vec d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t : ℝ), t ≠ 0 → |t| ≤ 1 → ∀ x ∈ U,
      |t⁻¹ * (u (t • z + x) - u x)| ≤ C ∧
        PDE.vecNormSq (e + g (t • z + x)) ≤ C := by
  obtain ⟨R, hUR⟩ := hU.exists_norm_le
  let K := Metric.closedBall (0 : Vec d) (R + ‖z‖)
  have hK : IsCompact K := isCompact_closedBall _ _
  obtain ⟨A, hA⟩ := hu.contDiffOn.exists_lipschitzOnWith (by simp)
    (convex_closedBall (0 : Vec d) (R + ‖z‖)) hK
  have hgc : Continuous (fun x => PDE.vecNormSq (e + g x)) := by
    unfold PDE.vecNormSq
    apply continuous_finsetSum
    intro j _
    have hj : Continuous (fun x => e j + g x j) :=
      continuous_const.add ((continuous_apply j).comp hg)
    exact hj.mul hj
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hgc.continuousOn
  refine ⟨(A : ℝ) * ‖z‖ + |B| + 1, by positivity, ?_⟩
  intro t ht hts x hx
  have hxK : x ∈ K := by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (hUR x hx).trans (le_add_of_nonneg_right (norm_nonneg z))
  have hyK : t • z + x ∈ K := by
    rw [Metric.mem_closedBall, dist_zero_right]
    have htz : ‖t • z‖ ≤ ‖z‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      nlinarith [norm_nonneg z]
    exact (norm_add_le _ _).trans (by linarith [hUR x hx])
  have hq : |t⁻¹ * (u (t • z + x) - u x)| ≤ (A : ℝ) * ‖z‖ := by
    rw [abs_mul, abs_inv]
    calc
      |t|⁻¹ * |u (t • z + x) - u x| ≤
          |t|⁻¹ * ((A : ℝ) * ‖t • z + x - x‖) :=
        mul_le_mul_of_nonneg_left
          (by simpa only [Real.norm_eq_abs] using (hA.norm_sub_le hyK hxK))
          (inv_nonneg.mpr (abs_nonneg t))
      _ = (A : ℝ) * ‖z‖ := by
        rw [add_sub_cancel_right, norm_smul, Real.norm_eq_abs]
        field_simp
  have hb : PDE.vecNormSq (e + g (t • z + x)) ≤ |B| :=
    (le_abs_self _).trans ((hB _ hyK).trans (le_abs_self B))
  have hAz : 0 ≤ (A : ℝ) * ‖z‖ := by positivity
  exact ⟨by linarith [abs_nonneg B], by linarith⟩

/-- A componentwise C1 vector source has uniformly bounded signed
quotients on bounded domains, in the explicit Euclidean square norm. -/
theorem exists_uniform_source_quotient_bound {d : ℕ} {U : Set (Vec d)}
    (hU : Bornology.IsBounded U) {F : Vec d → Vec d}
    (hF : ∀ j, ContDiff ℝ (1 : ℕ∞) (fun x => F x j)) (z : Vec d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, t ≠ 0 → |t| ≤ 1 → ∀ x ∈ U,
      PDE.vecNormSq (t⁻¹ • (F (t • z + x) - F x)) ≤ C := by
  have hscalar (j : Fin d) : ∃ C : ℝ, 0 ≤ C ∧
      ∀ t : ℝ, t ≠ 0 → |t| ≤ 1 → ∀ x ∈ U,
        |t⁻¹ * (F (t • z + x) j - F x j)| ≤ C := by
    obtain ⟨C, hC, hbound⟩ := exists_uniform_quotient_data_bound hU (hF j)
      (g := fun _ => (0 : Vec d)) continuous_const 0 z
    exact ⟨C, hC, fun t ht hts x hx => (hbound t ht hts x hx).1⟩
  choose C hC hbound using hscalar
  refine ⟨∑ j, C j ^ 2, Finset.sum_nonneg (fun j _ => sq_nonneg _), ?_⟩
  intro t ht hts x hx
  simp only [PDE.vecNormSq, PDE.vecDot, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  apply Finset.sum_le_sum
  intro j _
  have hs := mul_self_le_mul_self (abs_nonneg _) (hbound j t ht hts x hx)
  simpa only [← pow_two, sq_abs] using hs

/-- The affine weak equation gives a uniform, explicitly Euclidean local
`L²` bound for signed directional quotients of its continuous gradient. -/
theorem exists_uniform_differenceQuotient_energy {d : ℕ} {U : Set (Vec d)} {Λ : ℝ}
    (hU : PDE.IsOpenBoundedConvexDomain U) {a : Vec d → Mat d} {L : ℝ}
    (hell : PDE.IsEllipticFieldOn 1 Λ U a)
    (ha : ∀ j k, Continuous (fun x => a x j k)) (haL : IsOperatorLipschitz L a)
    {u : Vec d → ℝ} {g : Vec d → Vec d}
    (hu : ContDiff ℝ (1 : ℕ∞) u) (hg : Continuous g)
    (hw : HasWeakGradient Set.univ u g) (e : Vec d)
    (he : HasWeakDivergence Set.univ (fun x => (a x).mulVec (e + g x)) (fun _ => 0))
    (z : Vec d) {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηc : HasCompactSupport η) (hηU : tsupport η ⊆ U) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ t : ℝ, t ≠ 0 → |t| ≤ 1 →
      (∫ x in U, η x ^ 2 * PDE.vecNormSq (t⁻¹ • (g (t • z + x) - g x))) ≤ E := by
  obtain ⟨C, hC, hdata⟩ := exists_uniform_quotient_data_bound hU.isBoundedDomain.isBounded hu hg e z
  haveI := hU.isSobolevRegularDomain.isFiniteMeasure_volumeOn
  let D := ∫ x in U, PDE.vecNormSq (PDE.classicalGradient η x)
  let H := ∫ x in U, η x ^ 2
  let B := L ^ 2 * PDE.vecNormSq z * C
  have hD : 0 ≤ D := integral_nonneg (fun _ => PDE.vecNormSq_nonneg _)
  have hH : 0 ≤ H := integral_nonneg (fun _ => sq_nonneg _)
  have hB : 0 ≤ B := mul_nonneg (mul_nonneg (sq_nonneg L) (PDE.vecNormSq_nonneg z)) hC
  have hDi : IntegrableOn (fun x => PDE.vecNormSq (PDE.classicalGradient η x)) U :=
    (continuous_memLp_bounded hU (PDE.continuous_vecNormSq.comp
      (PDE.ContDiff.continuous_classicalGradient (hη.of_le (by simp))))).integrable (by norm_num)
  have hHi : IntegrableOn (fun x => η x ^ 2) U :=
    (continuous_memLp_bounded hU hη.continuous).integrable_sq
  refine ⟨|8 * Λ + 4| * (C ^ 2 * D) + 8 * (B * H), by positivity, ?_⟩
  intro t ht hts
  let q := fun x => t⁻¹ * (u (t • z + x) - u x)
  let G := fun x => t⁻¹ • (g (t • z + x) - g x)
  let F := fun x => t⁻¹ • ((a (t • z + x) - a x).mulVec (e + g (t • z + x)))
  have hmem : ∀ᵐ x ∂(volume.restrict U), x ∈ U :=
    (ae_restrict_iff' hU.measurableSet).2 (Eventually.of_forall fun _ hx => hx)
  have hq : (∫ x in U, q x ^ 2 * PDE.vecNormSq (PDE.classicalGradient η x)) ≤ C ^ 2 * D := by
    rw [← integral_const_mul]
    apply integral_mono_of_nonneg
      (Eventually.of_forall fun _ => mul_nonneg (sq_nonneg _) (PDE.vecNormSq_nonneg _))
      (hDi.const_mul _)
    filter_upwards [hmem] with x hx
    have hs := mul_self_le_mul_self (abs_nonneg (q x)) (hdata t ht hts x hx).1
    have hs' : q x ^ 2 ≤ C ^ 2 := by simpa only [← pow_two, sq_abs] using hs
    exact mul_le_mul_of_nonneg_right hs' (PDE.vecNormSq_nonneg _)
  have hF : (∫ x in U, η x ^ 2 * PDE.vecNormSq (F x)) ≤ B * H := by
    rw [← integral_const_mul]
    apply integral_mono_of_nonneg
      (Eventually.of_forall fun _ => mul_nonneg (sq_nonneg _) (PDE.vecNormSq_nonneg _))
      (hHi.const_mul _)
    filter_upwards [hmem] with x hx
    have hb : PDE.vecNormSq (F x) ≤ B :=
      (coefficient_commutator_sq_bound haL x z (e + g (t • z + x)) ht).trans
        (mul_le_mul_of_nonneg_left (hdata t ht hts x hx).2
          (mul_nonneg (sq_nonneg L) (PDE.vecNormSq_nonneg z)))
    simpa only [mul_comm B] using mul_le_mul_of_nonneg_left hb (sq_nonneg (η x))
  have henergy := differenceQuotient_energy hU hell ha hu.continuous hg hw e he
    (t • z) t hη hηc hηU
  have hGc : Continuous G := (continuous_const : Continuous (fun _ : Vec d => t⁻¹)).smul
    ((hg.comp (continuous_const.add continuous_id)).sub hg)
  have hac : Continuous a := continuous_pi fun j => continuous_pi fun k => ha j k
  have hfluxc := hac.matrix_mulVec hGc
  have hdotc : Continuous (fun x => PDE.vecDot (G x) (PDE.matVecMul (a x) (G x))) :=
    hGc.dotProduct hfluxc
  have hEi : IntegrableOn
      (fun x => η x ^ 2 * PDE.vecDot (G x) (PDE.matVecMul (a x) (G x))) U :=
    (continuous_memLp_bounded hU ((hη.continuous.pow 2).mul hdotc)).integrable (by norm_num)
  have hcoerc : (∫ x in U, η x ^ 2 * PDE.vecNormSq (G x)) ≤
      ∫ x in U, η x ^ 2 * PDE.vecDot (G x) (PDE.matVecMul (a x) (G x)) := by
    apply integral_mono_of_nonneg
      (Eventually.of_forall fun _ => mul_nonneg (sq_nonneg _) (PDE.vecNormSq_nonneg _)) hEi
    filter_upwards [hmem] with x hx
    exact mul_le_mul_of_nonneg_left
      (PDE.DGNM.vecNormSq_le_vecDot_matVecMul (hell.2 x hx) (G x)) (sq_nonneg _)
  have hqnonneg : 0 ≤ ∫ x in U, q x ^ 2 * PDE.vecNormSq (PDE.classicalGradient η x) :=
    integral_nonneg (fun _ => mul_nonneg (sq_nonneg _) (PDE.vecNormSq_nonneg _))
  have hcoeff := mul_le_mul_of_nonneg_right (le_abs_self (8 * Λ + 4)) hqnonneg
  have hq' := mul_le_mul_of_nonneg_left hq (abs_nonneg (8 * Λ + 4))
  change (∫ x in U, η x ^ 2 * PDE.vecNormSq (G x)) ≤ _
  linarith

/-- A componentwise C1 original forcing contributes its own bounded
quotient to the uniform local gradient energy estimate. -/
theorem exists_uniform_forced_differenceQuotient_energy {d : ℕ} {U : Set (Vec d)} {Λ : ℝ}
    (hU : PDE.IsOpenBoundedConvexDomain U) {a : Vec d → Mat d} {L : ℝ}
    (hell : PDE.IsEllipticFieldOn 1 Λ U a)
    (ha : ∀ j k, Continuous (fun x => a x j k)) (haL : IsOperatorLipschitz L a)
    {u : Vec d → ℝ} {g S : Vec d → Vec d}
    (hu : ContDiff ℝ (1 : ℕ∞) u) (hg : Continuous g)
    (hS : ∀ j, ContDiff ℝ (1 : ℕ∞) (fun x => S x j))
    (hw : HasWeakGradient Set.univ u g) (e : Vec d)
    (he : HasWeakDivergence Set.univ (fun x => (a x).mulVec (e + g x) + S x) (fun _ => 0))
    (z : Vec d) {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηc : HasCompactSupport η) (hηU : tsupport η ⊆ U) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ t : ℝ, t ≠ 0 → |t| ≤ 1 →
      (∫ x in U, η x ^ 2 * PDE.vecNormSq (t⁻¹ • (g (t • z + x) - g x))) ≤ E := by
  obtain ⟨C, hC, hdata⟩ := exists_uniform_quotient_data_bound hU.isBoundedDomain.isBounded hu hg e z
  obtain ⟨CS, hCS, hsource⟩ :=
    exists_uniform_source_quotient_bound hU.isBoundedDomain.isBounded hS z
  have hSc : Continuous S := continuous_pi fun j => (hS j).continuous
  letI := hU.isSobolevRegularDomain.isFiniteMeasure_volumeOn
  let D := ∫ x in U, PDE.vecNormSq (PDE.classicalGradient η x)
  let H := ∫ x in U, η x ^ 2
  let B := 2 * (L ^ 2 * PDE.vecNormSq z * C + CS)
  have hD : 0 ≤ D := integral_nonneg (fun _ => PDE.vecNormSq_nonneg _)
  have hH : 0 ≤ H := integral_nonneg (fun _ => sq_nonneg _)
  have hB : 0 ≤ B := mul_nonneg (by norm_num)
    (add_nonneg (mul_nonneg (mul_nonneg (sq_nonneg L) (PDE.vecNormSq_nonneg z)) hC) hCS)
  have hDi : IntegrableOn (fun x => PDE.vecNormSq (PDE.classicalGradient η x)) U :=
    (continuous_memLp_bounded hU (PDE.continuous_vecNormSq.comp
      (PDE.ContDiff.continuous_classicalGradient (hη.of_le (by simp))))).integrable (by norm_num)
  have hHi : IntegrableOn (fun x => η x ^ 2) U :=
    (continuous_memLp_bounded hU hη.continuous).integrable_sq
  refine ⟨|8 * Λ + 4| * (C ^ 2 * D) + 8 * (B * H), by positivity, ?_⟩
  intro t ht hts
  let q := fun x => t⁻¹ * (u (t • z + x) - u x)
  let G := fun x => t⁻¹ • (g (t • z + x) - g x)
  let F := fun x => t⁻¹ • ((a (t • z + x) - a x).mulVec (e + g (t • z + x))) +
    t⁻¹ • (S (t • z + x) - S x)
  have hmem : ∀ᵐ x ∂(volume.restrict U), x ∈ U :=
    (ae_restrict_iff' hU.measurableSet).2 (Eventually.of_forall fun _ hx => hx)
  have hq : (∫ x in U, q x ^ 2 * PDE.vecNormSq (PDE.classicalGradient η x)) ≤ C ^ 2 * D := by
    rw [← integral_const_mul]
    apply integral_mono_of_nonneg
      (Eventually.of_forall fun _ => mul_nonneg (sq_nonneg _) (PDE.vecNormSq_nonneg _))
      (hDi.const_mul _)
    filter_upwards [hmem] with x hx
    have hs := mul_self_le_mul_self (abs_nonneg (q x)) (hdata t ht hts x hx).1
    have hs' : q x ^ 2 ≤ C ^ 2 := by simpa only [← pow_two, sq_abs] using hs
    exact mul_le_mul_of_nonneg_right hs' (PDE.vecNormSq_nonneg _)
  have hF : (∫ x in U, η x ^ 2 * PDE.vecNormSq (F x)) ≤ B * H := by
    rw [← integral_const_mul]
    apply integral_mono_of_nonneg
      (Eventually.of_forall fun _ => mul_nonneg (sq_nonneg _) (PDE.vecNormSq_nonneg _))
      (hHi.const_mul _)
    filter_upwards [hmem] with x hx
    have haBound :=
      (coefficient_commutator_sq_bound haL x z (e + g (t • z + x)) ht).trans
        (mul_le_mul_of_nonneg_left (hdata t ht hts x hx).2
          (mul_nonneg (sq_nonneg L) (PDE.vecNormSq_nonneg z)))
    have hsBound := hsource t ht hts x hx
    have htri := PDE.vecNormSq_add_le
      (t⁻¹ • ((a (t • z + x) - a x).mulVec (e + g (t • z + x))))
      (t⁻¹ • (S (t • z + x) - S x))
    have hb : PDE.vecNormSq (F x) ≤ B :=
      htri.trans (mul_le_mul_of_nonneg_left (add_le_add haBound hsBound) (by norm_num))
    simpa only [mul_comm B] using mul_le_mul_of_nonneg_left hb (sq_nonneg (η x))
  have henergy := forced_differenceQuotient_energy hU hell ha hu.continuous hg hSc hw e he
    (t • z) t hη hηc hηU
  have hGc : Continuous G := (continuous_const : Continuous (fun _ : Vec d => t⁻¹)).smul
    ((hg.comp (continuous_const.add continuous_id)).sub hg)
  have hac : Continuous a := continuous_pi fun j => continuous_pi fun k => ha j k
  have hfluxc := hac.matrix_mulVec hGc
  have hdotc : Continuous (fun x => PDE.vecDot (G x) (PDE.matVecMul (a x) (G x))) :=
    hGc.dotProduct hfluxc
  have hEi : IntegrableOn
      (fun x => η x ^ 2 * PDE.vecDot (G x) (PDE.matVecMul (a x) (G x))) U :=
    (continuous_memLp_bounded hU ((hη.continuous.pow 2).mul hdotc)).integrable (by norm_num)
  have hcoerc : (∫ x in U, η x ^ 2 * PDE.vecNormSq (G x)) ≤
      ∫ x in U, η x ^ 2 * PDE.vecDot (G x) (PDE.matVecMul (a x) (G x)) := by
    apply integral_mono_of_nonneg
      (Eventually.of_forall fun _ => mul_nonneg (sq_nonneg _) (PDE.vecNormSq_nonneg _)) hEi
    filter_upwards [hmem] with x hx
    exact mul_le_mul_of_nonneg_left
      (PDE.DGNM.vecNormSq_le_vecDot_matVecMul (hell.2 x hx) (G x)) (sq_nonneg _)
  have hqnonneg : 0 ≤ ∫ x in U, q x ^ 2 * PDE.vecNormSq (PDE.classicalGradient η x) :=
    integral_nonneg (fun _ => mul_nonneg (sq_nonneg _) (PDE.vecNormSq_nonneg _))
  have hcoeff := mul_le_mul_of_nonneg_right (le_abs_self (8 * Λ + 4)) hqnonneg
  have hq' := mul_le_mul_of_nonneg_left hq (abs_nonneg (8 * Λ + 4))
  change (∫ x in U, η x ^ 2 * PDE.vecNormSq (G x)) ≤ _
  linarith

/-- A norm-bounded Hilbert sequence has a weak limit along a nontrivial
filter refining `atTop`. No separability or choice of subsequence is needed. -/
theorem exists_weak_limit_of_norm_bound {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (v : ℕ → E) {R : ℝ}
    (hv : ∀ n, ‖v n‖ ≤ R) :
    ∃ w : E, ‖w‖ ≤ R ∧ ∃ l : Filter ℕ, l.NeBot ∧ l ≤ atTop ∧
      ∀ y : E, Tendsto (fun n => inner ℝ (v n) y) l (𝓝 (inner ℝ w y)) := by
  let V : ℕ → WeakDual ℝ E := fun n =>
    StrongDual.toWeakDual (InnerProductSpace.toDual ℝ E (v n))
  have hmem : ∀ n, V n ∈ WeakDual.toStrongDual ⁻¹'
      Metric.closedBall (0 : StrongDual ℝ E) R := by
    intro n
    simpa only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right,
      V, StrongDual.toStrongDual_toWeakDual, LinearIsometryEquiv.norm_map] using hv n
  obtain ⟨F, hF, hc⟩ := (WeakDual.isCompact_closedBall (0 : StrongDual ℝ E) R).exists_mapClusterPt (f := (atTop : Filter ℕ)) (u := V)
    (Filter.le_principal_iff.mpr (Filter.eventually_map.mpr
      (Eventually.of_forall hmem)))
  let w := (InnerProductSpace.toDual ℝ E).symm F.toStrongDual
  let l := Filter.comap V (𝓝 F) ⊓ atTop
  have hl : l.NeBot := Filter.neBot_inf_comap_iff_map'.mpr hc
  have hV : Tendsto V l (𝓝 F) := tendsto_comap.mono_left inf_le_left
  refine ⟨w, ?_, l, hl, inf_le_right, ?_⟩
  · simpa only [w, LinearIsometryEquiv.norm_map, Set.mem_preimage,
      Metric.mem_closedBall, dist_zero_right] using hF
  · intro y
    have ht := (WeakDual.eval_continuous y).continuousAt.tendsto.comp hV
    change Tendsto (fun n => inner ℝ (v n) y) l (𝓝 (F y)) at ht
    simpa only [w, InnerProductSpace.toDual_symm_apply,
      WeakDual.toStrongDual_apply] using ht

/-- Weak Hilbert convergence is preserved by a continuous linear map,
including the value and gradient projections of the complete Sobolev graph. -/
theorem tendsto_inner_clm_of_tendsto_inner
    {ι E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {l : Filter ι} {v : ι → E} {w : E}
    (hw : ∀ y : E, Tendsto (fun n => inner ℝ (v n) y) l (𝓝 (inner ℝ w y)))
    (A : E →L[ℝ] F) (y : F) :
    Tendsto (fun n => inner ℝ (A (v n)) y) l (𝓝 (inner ℝ (A w) y)) := by
  let φ : StrongDual ℝ E := (InnerProductSpace.toDualMap ℝ F y).comp A
  let z : E := (InnerProductSpace.toDual ℝ E).symm φ
  have hz (x : E) : inner ℝ x z = inner ℝ (A x) y := by
    rw [real_inner_comm, InnerProductSpace.toDual_symm_apply]
    change inner ℝ y (A x) = inner ℝ (A x) y
    exact real_inner_comm (A x) y
  simpa only [hz] using hw z

/-- A bounded Hilbert sequence whose image converges strongly has a weak
limit with exactly that image. -/
theorem exists_preimage_of_norm_bound_of_tendsto
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (A : E →L[ℝ] F) (v : ℕ → E) {R : ℝ} (hv : ∀ n, ‖v n‖ ≤ R)
    {f : F} (hf : Tendsto (fun n => A (v n)) atTop (𝓝 f)) :
    ∃ w : E, ‖w‖ ≤ R ∧ A w = f := by
  obtain ⟨w, hw, l, hl, hltop, hweak⟩ := exists_weak_limit_of_norm_bound v hv
  have := hl
  refine ⟨w, hw, ext_inner_right ℝ (fun y => ?_)⟩
  let φ : StrongDual ℝ E := (InnerProductSpace.toDualMap ℝ F y).comp A
  let z : E := (InnerProductSpace.toDual ℝ E).symm φ
  have hz (x : E) : inner ℝ x z = inner ℝ (A x) y := by
    rw [real_inner_comm, InnerProductSpace.toDual_symm_apply]
    change inner ℝ y (A x) = inner ℝ (A x) y
    exact real_inner_comm (A x) y
  have hwl : Tendsto (fun n => inner ℝ (A (v n)) y) l (𝓝 (inner ℝ (A w) y)) := by
    simpa only [hz] using hweak z
  have hfl : Tendsto (fun n => inner ℝ (A (v n)) y) l (𝓝 (inner ℝ f y)) :=
    ((hf.mono_left hltop).inner tendsto_const_nhds)
  exact tendsto_nhds_unique hwl hfl

/-- Strong `L²` limits of sequences bounded in the genuine Hilbert `H¹`
graph have an `H¹` weak gradient, with the same graph-norm bound. -/
theorem exists_h1Graph_of_value_tendsto {d : ℕ} {U : Set (Vec d)}
    (v : ℕ → PDE.H1HilbertGraph U) {R : ℝ} (hv : ∀ n, ‖v n‖ ≤ R)
    {f : PDE.ScalarLp U (2 : ℝ≥0∞)}
    (hf : Tendsto (fun n => (v n).value) atTop (𝓝 f)) :
    ∃ w : PDE.H1HilbertGraph U, ‖w‖ ≤ R ∧ w.value = f :=
  exists_preimage_of_norm_bound_of_tendsto PDE.H1HilbertGraph.valueCLM v hv hf

/-- The Hilbert graph norm is exactly the scalar and Euclidean gradient
energy of a concrete Sobolev function. -/
theorem h1HilbertGraph_norm_sq {d : ℕ} {U : Set (Vec d)} (u : PDE.H1Function U) :
    ‖PDE.H1HilbertGraph.ofH1Graph u.toW1pFunction.toW1pGraph‖ ^ 2 =
      (∫ x in U, u.toFun x ^ 2) + (∫ x in U, PDE.vecNormSq (u.grad x)) := by
  rw [PDE.H1Function.setIntegral_sq_toFun_eq_norm_sq,
    PDE.H1Function.setIntegral_vecNormSq_grad_eq_norm_sq]
  change ‖(PDE.h1HilbertAmbientEquiv U).symm u.toW1pFunction.toW1pGraph.1‖ ^ 2 = _
  rw [WithLp.prod_norm_sq_eq_of_L2]
  rfl

/-- A strong scalar `L²` limit of genuine Sobolev functions with uniformly
bounded scalar and Euclidean gradient energies has a weak gradient. -/
theorem exists_h1Function_of_energy_bound_of_value_tendsto
    {d : ℕ} {U : Set (Vec d)} (v : ℕ → PDE.H1Function U) {M : ℝ}
    (hM : ∀ n, (∫ x in U, (v n).toFun x ^ 2) +
      (∫ x in U, PDE.vecNormSq ((v n).grad x)) ≤ M)
    {f : PDE.ScalarLp U (2 : ℝ≥0∞)}
    (hf : Tendsto (fun n => (v n).toW1pFunction.toW1pGraph.1.1) atTop (𝓝 f)) :
    ∃ w : PDE.H1Function U, w.toFun =ᵐ[PDE.volumeOn U] ⇑f := by
  let V : ℕ → PDE.H1HilbertGraph U := fun n =>
    PDE.H1HilbertGraph.ofH1Graph (v n).toW1pFunction.toW1pGraph
  have hV (n : ℕ) : ‖V n‖ ≤ |M| + 1 := by
    have hn : ‖V n‖ ^ 2 ≤ M := by
      simpa only [V, h1HilbertGraph_norm_sq] using hM n
    have := le_abs_self M
    nlinarith [norm_nonneg (V n), abs_nonneg M]
  have hf' : Tendsto (fun n => (V n).value) atTop (𝓝 f) := hf
  obtain ⟨w, _, hw⟩ := exists_h1Graph_of_value_tendsto V hV hf'
  refine ⟨w.toH1Graph.toH1Function, ?_⟩
  change (⇑w.value) =ᵐ[PDE.volumeOn U] ⇑f
  rw [hw]

/-- Compactness retains weak convergence of every native Euclidean gradient
pairing, in addition to identifying the scalar limit. These pairings allow the
variable-coefficient weak equation to pass to the derivative limit. -/
theorem exists_h1Function_of_energy_bound_of_value_tendsto_with_pairings
    {d : ℕ} {U : Set (Vec d)} (v : ℕ → PDE.H1Function U) {M : ℝ}
    (hM : ∀ n, (∫ x in U, (v n).toFun x ^ 2) +
      (∫ x in U, PDE.vecNormSq ((v n).grad x)) ≤ M)
    {f : PDE.ScalarLp U (2 : ℝ≥0∞)}
    (hf : Tendsto (fun n => (v n).toW1pFunction.toW1pGraph.1.1) atTop (𝓝 f)) :
    ∃ w : PDE.H1Function U, w.toFun =ᵐ[PDE.volumeOn U] ⇑f ∧
      ∃ l : Filter ℕ, l.NeBot ∧ l ≤ atTop ∧
        ∀ (F : Vec d → Vec d), PDE.MemVectorL2On U F →
          Tendsto (fun n => ∫ x in U, PDE.vecDot ((v n).grad x) (F x)) l
            (𝓝 (∫ x in U, PDE.vecDot (w.grad x) (F x))) := by
  let V : ℕ → PDE.H1HilbertGraph U := fun n =>
    PDE.H1HilbertGraph.ofH1Graph (v n).toW1pFunction.toW1pGraph
  have hV (n : ℕ) : ‖V n‖ ≤ |M| + 1 := by
    have hn : ‖V n‖ ^ 2 ≤ M := by
      simpa only [V, h1HilbertGraph_norm_sq] using hM n
    nlinarith [norm_nonneg (V n), abs_nonneg M, le_abs_self M]
  obtain ⟨W, _, l, hl, hltop, hweak⟩ := exists_weak_limit_of_norm_bound V hV
  have := hl
  have hvalue : W.value = f := by
    apply ext_inner_right ℝ
    intro y
    exact tendsto_nhds_unique
      (tendsto_inner_clm_of_tendsto_inner hweak PDE.H1HilbertGraph.valueCLM y)
      ((hf.mono_left hltop).inner tendsto_const_nhds)
  let w := W.toH1Graph.toH1Function
  refine ⟨w, ?_, l, hl, hltop, ?_⟩
  · change (⇑W.value) =ᵐ[PDE.volumeOn U] ⇑f
    rw [hvalue]
  · intro F hF
    let H := (PDE.gradMemLpOn_iff_memLp_toHilbertVecField.mp hF).toLp
      (PDE.toHilbertVecField F)
    have hH : ⇑H =ᵐ[PDE.volumeOn U] PDE.toHilbertVecField F :=
      MemLp.coeFn_toLp _
    have hn (n : ℕ) : (∫ x in U, PDE.vecDot ((v n).grad x) (F x)) =
        inner ℝ (PDE.H1HilbertGraph.gradientCLM (V n)) H := by
      exact PDE.setIntegral_vecDot_eq_inner_of_ae_eq _ _ _ _
        (v n).toW1pFunction.coeFn_toW1pGraph_snd hH
    have hw : (∫ x in U, PDE.vecDot (w.grad x) (F x)) =
        inner ℝ (PDE.H1HilbertGraph.gradientCLM W) H := by
      apply PDE.setIntegral_vecDot_eq_inner_of_ae_eq _ _ _ _ ?_ hH
      exact Eventually.of_forall fun x => by
        simp only [w, PDE.H1Graph.toH1Function_grad, PDE.toHilbertVecField,
          PDE.Vec.toHilbertVec_toVec]
        rfl
    simpa only [hn, hw] using
      tendsto_inner_clm_of_tendsto_inner hweak PDE.H1HilbertGraph.gradientCLM H

/-- Weak convergence of Euclidean gradient pairings passes through a
continuous variable coefficient in each smooth flux test. -/
theorem tendsto_flux_test_of_gradient_pairings
    {ι : Type*} {d : ℕ} {U : Set (Vec d)} {l : Filter ι}
    (hU : PDE.IsOpenBoundedConvexDomain U)
    {a : Vec d → Mat d} (ha : ∀ j k, Continuous (fun x => a x j k))
    {g : ι → Vec d → Vec d} {g₀ : Vec d → Vec d}
    (hg : ∀ (F : Vec d → Vec d), PDE.MemVectorL2On U F →
      Tendsto (fun n => ∫ x in U, PDE.vecDot (g n x) (F x)) l
        (𝓝 (∫ x in U, PDE.vecDot (g₀ x) (F x))))
    {ψ : Vec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    Tendsto (fun n => ∫ x in U, dot ((a x).mulVec (g n x)) (gradient ψ x)) l
      (𝓝 (∫ x in U, dot ((a x).mulVec (g₀ x)) (gradient ψ x))) := by
  let F : Vec d → Vec d := fun x k => ∑ j, a x j k * gradient ψ x j
  have hψg (j : Fin d) : Continuous (fun x => gradient ψ x j) :=
    (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hF : PDE.MemVectorL2On U F := by
    intro k
    apply continuous_memLp_bounded hU
    exact continuous_finset_sum _ (fun j _ => (ha j k).mul (hψg j))
  have heq (x : Vec d) (v : Vec d) :
      dot ((a x).mulVec v) (gradient ψ x) = PDE.vecDot v (F x) := by
    simp only [dot, Matrix.mulVec, dotProduct, PDE.vecDot, F,
      Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simpa only [heq] using hg F hF

/-- Signed directional difference quotients converge to the actual
Fréchet derivative, before any Sobolev limiting argument. -/
theorem tendsto_differenceQuotient {d : ℕ} {u : Vec d → ℝ} {x : Vec d}
    (hu : DifferentiableAt ℝ u x) (z : Vec d) :
    Tendsto (fun t : ℝ => t⁻¹ * (u (t • z + x) - u x))
      (𝓝[≠] 0) (𝓝 (fderiv ℝ u x z)) := by
  have hline : HasDerivAt (fun t : ℝ => t • z + x) z 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const z).add_const x
  have hu' : HasFDerivAt u (fderiv ℝ u x) ((fun t : ℝ => t • z + x) 0) := by
    simpa using hu.hasFDerivAt
  have h := (hu'.comp_hasDerivAt 0 hline).tendsto_slope_zero
  simpa [Function.comp_def] using h

/-- The signed coefficient commutator converges to the full differentiated
forcing. The affine vector and translated gradient are retained in the limit. -/
theorem tendsto_coefficient_commutator
    {d : ℕ} {a : Vec d → Mat d} {g : Vec d → Vec d} {x : Vec d}
    (ha : ∀ j k, DifferentiableAt ℝ (fun y => a y j k) x)
    (hg : ContinuousAt g x) (e z : Vec d) :
    Tendsto (fun t : ℝ => t⁻¹ •
      ((a (t • z + x) - a x).mulVec (e + g (t • z + x))))
      (𝓝[≠] 0)
      (𝓝 (Matrix.mulVec (fun j k => fderiv ℝ (fun y => a y j k) x z) (e + g x))) := by
  have ht : Tendsto (fun t : ℝ => t) (𝓝[≠] 0) (𝓝 0) := nhdsWithin_le_nhds
  have hshift : Tendsto (fun t : ℝ => t • z + x) (𝓝[≠] 0) (𝓝 x) := by
    simpa using (ht.smul (tendsto_const_nhds (x := z))).add
      (tendsto_const_nhds (x := x))
  have hg' := hg.tendsto.comp hshift
  apply tendsto_pi_nhds.mpr
  intro j
  have hsum := tendsto_finsetSum Finset.univ (fun k _ =>
    (tendsto_differenceQuotient (ha j k) z).mul
      ((tendsto_const_nhds (x := e k)).add
        ((continuous_apply k).tendsto (g x) |>.comp hg')))
  simpa only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct,
    Pi.add_apply, Matrix.sub_apply, Finset.mul_sum, mul_assoc, Function.comp_apply] using hsum

/-- Uniform operator-Lipschitz control makes the actual coefficient
commutators converge in every continuous bounded-domain flux pairing. -/
theorem tendsto_coefficient_commutator_test
    {d : ℕ} {U : Set (Vec d)} (hU : PDE.IsOpenBoundedConvexDomain U)
    {a : Vec d → Mat d} (ha : ∀ j k, ContDiff ℝ (1 : ℕ∞) (fun x => a x j k))
    {L : ℝ} (haL : IsOperatorLipschitz L a)
    {g F : Vec d → Vec d} (hg : Continuous g) (hF : Continuous F) (e z : Vec d) :
    Tendsto (fun n => ∫ x in U, PDE.vecDot
      ((C3SublinearC1.mollifierScale n)⁻¹ •
        ((a (C3SublinearC1.mollifierScale n • z + x) - a x).mulVec
          (e + g (C3SublinearC1.mollifierScale n • z + x)))) (F x)) atTop
      (𝓝 (∫ x in U, PDE.vecDot
        (Matrix.mulVec (fun j k => fderiv ℝ (fun y => a y j k) x z) (e + g x))
        (F x))) := by
  have := hU.isSobolevRegularDomain.isFiniteMeasure_volumeOn
  let s := C3SublinearC1.mollifierScale
  let B := fun n x => (s n)⁻¹ •
    ((a (s n • z + x) - a x).mulVec (e + g (s n • z + x)))
  let B₀ := fun x => Matrix.mulVec
    (fun j k => fderiv ℝ (fun y => a y j k) x z) (e + g x)
  have hspos (n : ℕ) : 0 < s n := C3SublinearC1.mollifierScale_pos n
  have hsle (n : ℕ) : |s n| ≤ 1 := by
    rw [abs_of_pos (hspos n)]
    change 1 / (n + 1 : ℝ) ≤ 1
    exact (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])
  obtain ⟨C, _, hC⟩ := exists_uniform_quotient_data_bound
    hU.isBoundedDomain.isBounded (u := fun _ => 0) contDiff_const hg e z
  let K := L ^ 2 * PDE.vecNormSq z * C
  have hB (n : ℕ) (x : Vec d) (hx : x ∈ U) :
      PDE.vecEuclideanNorm (B n x) ≤ |K| + 1 := by
    have hb := coefficient_commutator_sq_bound haL x z
      (e + g (s n • z + x)) (ne_of_gt (hspos n))
    have hc := (hC _ (ne_of_gt (hspos n)) (hsle n) x hx).2
    have hsq : PDE.vecNormSq (B n x) ≤ K :=
      hb.trans (mul_le_mul_of_nonneg_left hc
        (mul_nonneg (sq_nonneg _) (PDE.vecNormSq_nonneg _)))
    rw [← PDE.vecEuclideanNorm_sq] at hsq
    nlinarith [PDE.vecEuclideanNorm_nonneg (B n x), abs_nonneg K, le_abs_self K]
  obtain ⟨D, hD⟩ := hU.isBoundedDomain.isBounded.isCompact_closure.exists_bound_of_continuousOn
    (PDE.continuous_vecEuclideanNorm.comp hF).continuousOn
  have hBc (n : ℕ) (j : Fin d) : Continuous (fun x => B n x j) := by
    apply continuous_const.mul
    change Continuous (fun x => ∑ k,
      (a (s n • z + x) j k - a x j k) * (e k + g (s n • z + x) k))
    apply continuous_finset_sum
    intro k _
    exact (((ha j k).continuous.comp (continuous_const.add continuous_id)).sub
      (ha j k).continuous).mul
      (continuous_const.add ((continuous_apply k).comp
        (hg.comp (continuous_const.add continuous_id))))
  have hlim (x : Vec d) : Tendsto (fun n => B n x) atTop (𝓝 (B₀ x)) :=
    (tendsto_coefficient_commutator
      (fun j k => (ha j k).differentiable (by simp) x) hg.continuousAt e z).comp
      (C3SublinearC1.mollifierScale_tendsto.mono_right (nhdsGT_le_nhdsNE 0))
  apply tendsto_integral_of_dominated_convergence (μ := PDE.volumeOn U)
    (fun _ => (|K| + 1) * |D|)
  · intro n
    exact (continuous_finset_sum _ (fun j _ => (hBc n j).mul
      ((continuous_apply j).comp hF))).aestronglyMeasurable
  · exact integrable_const _
  · intro n
    filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
    rw [Real.norm_eq_abs]
    apply (PDE.abs_vecDot_le_vecEuclideanNorm_mul _ _).trans
    apply mul_le_mul (hB n x hx) ?_ (PDE.vecEuclideanNorm_nonneg _) (by positivity)
    have hd := hD x (subset_closure hx)
    exact (le_abs_self _).trans (hd.trans (le_abs_self D))
  · exact Eventually.of_forall fun x => by
      exact tendsto_finsetSum _ (fun j _ =>
        (((continuous_apply j).tendsto (B₀ x)).comp (hlim x)).mul_const (F x j))

/-- The original source quotient converges in each continuous test
pairing to the directional derivative of that source. -/
theorem tendsto_source_quotient_test
    {d : ℕ} {U : Set (Vec d)} (hU : PDE.IsOpenBoundedConvexDomain U)
    {S F : Vec d → Vec d}
    (hS : ∀ j, ContDiff ℝ (1 : ℕ∞) (fun x => S x j))
    (hF : Continuous F) (z : Vec d) :
    Tendsto (fun n => ∫ x in U, PDE.vecDot
      ((C3SublinearC1.mollifierScale n)⁻¹ •
        (S (C3SublinearC1.mollifierScale n • z + x) - S x)) (F x)) atTop
      (𝓝 (∫ x in U, PDE.vecDot
        (fun j => fderiv ℝ (fun y => S y j) x z) (F x))) := by
  have := hU.isSobolevRegularDomain.isFiniteMeasure_volumeOn
  let s := C3SublinearC1.mollifierScale
  let B := fun n x => (s n)⁻¹ • (S (s n • z + x) - S x)
  let B₀ := fun x j => fderiv ℝ (fun y => S y j) x z
  have hspos (n : ℕ) : 0 < s n := C3SublinearC1.mollifierScale_pos n
  have hsle (n : ℕ) : |s n| ≤ 1 := by
    rw [abs_of_pos (hspos n)]
    change 1 / (n + 1 : ℝ) ≤ 1
    exact (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])
  obtain ⟨C, _, hC⟩ := exists_uniform_source_quotient_bound
    hU.isBoundedDomain.isBounded hS z
  have hB (n : ℕ) (x : Vec d) (hx : x ∈ U) :
      PDE.vecEuclideanNorm (B n x) ≤ |C| + 1 := by
    have hsq := hC (s n) (ne_of_gt (hspos n)) (hsle n) x hx
    change PDE.vecNormSq (B n x) ≤ C at hsq
    rw [← PDE.vecEuclideanNorm_sq] at hsq
    nlinarith [PDE.vecEuclideanNorm_nonneg (B n x), abs_nonneg C, le_abs_self C]
  obtain ⟨D, hD⟩ := hU.isBoundedDomain.isBounded.isCompact_closure.exists_bound_of_continuousOn
    (PDE.continuous_vecEuclideanNorm.comp hF).continuousOn
  have hBc (n : ℕ) (j : Fin d) : Continuous (fun x => B n x j) :=
    continuous_const.mul (((hS j).continuous.comp
      (continuous_const.add continuous_id)).sub (hS j).continuous)
  have hlim (x : Vec d) : Tendsto (fun n => B n x) atTop (𝓝 (B₀ x)) := by
    apply tendsto_pi_nhds.2
    intro j
    exact (tendsto_differenceQuotient ((hS j).differentiable (by simp) x) z).comp
      (C3SublinearC1.mollifierScale_tendsto.mono_right (nhdsGT_le_nhdsNE 0))
  apply tendsto_integral_of_dominated_convergence (μ := PDE.volumeOn U)
    (fun _ => (|C| + 1) * |D|)
  · intro n
    exact (continuous_finsetSum _ (fun j _ => (hBc n j).mul
      ((continuous_apply j).comp hF))).aestronglyMeasurable
  · exact integrable_const _
  · intro n
    filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
    rw [Real.norm_eq_abs]
    apply (PDE.abs_vecDot_le_vecEuclideanNorm_mul _ _).trans
    apply mul_le_mul (hB n x hx) ?_ (PDE.vecEuclideanNorm_nonneg _) (by positivity)
    have hd := hD x (subset_closure hx)
    exact (le_abs_self _).trans (hd.trans (le_abs_self D))
  · exact Eventually.of_forall fun x => by
      exact tendsto_finsetSum _ (fun j _ =>
        (((continuous_apply j).tendsto (B₀ x)).comp (hlim x)).mul_const (F x j))

/-- A continuously differentiable, divergence-free flux retains zero weak
 divergence after any fixed directional differentiation. The equation is global;
 compact support of each test supplies the bounded domain for the quotient limit. -/
theorem weakDivergence_fderiv {d : ℕ} {F : Vec d → Vec d}
    (hF : ∀ j, ContDiff ℝ (1 : ℕ∞) (fun x => F x j))
    (hdiv : HasWeakDivergence Set.univ F (fun _ => 0)) (z : Vec d) :
    HasWeakDivergence Set.univ
      (fun x j => fderiv ℝ (fun y => F y j) x z) (fun _ => 0) := by
  refine ⟨fun j => (((hF j).continuous_fderiv (by simp)).clm_apply
    continuous_const).locallyIntegrable.locallyIntegrableOn _,
    locallyIntegrableOn_zero, ?_⟩
  intro ψ hψ
  simp only [Measure.restrict_univ, zero_mul, integral_zero, neg_zero]
  obtain ⟨M, hM⟩ := hψ.2.1.isCompact.exists_bound_of_continuousOn
    PDE.continuous_vecEuclideanNorm.continuousOn
  let R : ℝ := |M| + 1
  have hR : 0 < R := by dsimp [R]; positivity
  have hsupp : tsupport ψ ⊆ PDE.euclideanBall (0 : Vec d) R := by
    intro x hx
    rw [PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hR]
    simp only [sub_zero]
    have hb := hM x hx
    have hn := PDE.vecEuclideanNorm_nonneg x
    rw [Real.norm_eq_abs, abs_of_nonneg hn] at hb
    dsimp [R]
    linarith [le_abs_self M]
  have hgrad (x : Vec d) (hx : x ∉ PDE.euclideanBall (0 : Vec d) R) :
      gradient ψ x = 0 := by
    have hnot : x ∉ tsupport ψ := fun h => hx (hsupp h)
    ext j
    change fderiv ℝ ψ x (unitVector j) = 0
    rw [fderiv_of_notMem_tsupport ℝ hnot]
    rfl
  have hreduce (A : Vec d → Vec d) :
      (∫ x in PDE.euclideanBall (0 : Vec d) R, PDE.vecDot (A x) (gradient ψ x)) =
        ∫ x, dot (A x) (gradient ψ x) := by
    change (∫ x in PDE.euclideanBall (0 : Vec d) R, dot (A x) (gradient ψ x)) = _
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    simp only [hgrad x hx, dot, Pi.zero_apply, mul_zero, Finset.sum_const_zero]
  have hψg : Continuous (gradient ψ) := by
    apply continuous_pi
    intro j
    exact (hψ.1.continuous_fderiv (by simp)).clm_apply continuous_const
  have hlim := tendsto_source_quotient_test
    (PDE.isOpenBoundedConvexDomain_euclideanBall (0 : Vec d) hR) hF hψg z
  have hzero (n : ℕ) :
      (∫ x in PDE.euclideanBall (0 : Vec d) R, PDE.vecDot
        ((C3SublinearC1.mollifierScale n)⁻¹ •
          (F (C3SublinearC1.mollifierScale n • z + x) - F x)) (gradient ψ x)) = 0 := by
    rw [hreduce]
    have hdiff := Correctors.hasWeakDivergence_sub
      (weakDivergence_translate hdiv (C3SublinearC1.mollifierScale n • z)) hdiv
    simp only [sub_self] at hdiff
    have hq := weakDivergence_const_smul hdiff (C3SublinearC1.mollifierScale n)⁻¹
    simpa only [Measure.restrict_univ, zero_mul, integral_zero, neg_zero] using hq.2.2 ψ hψ
  have heq : (∫ x in PDE.euclideanBall (0 : Vec d) R, PDE.vecDot
      (fun j => fderiv ℝ (fun y => F y j) x z) (gradient ψ x)) = 0 := by
    have ht : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝
        (∫ x in PDE.euclideanBall (0 : Vec d) R, PDE.vecDot
          (fun j => fderiv ℝ (fun y => F y j) x z) (gradient ψ x))) := by
      simpa only [hzero] using hlim
    exact tendsto_nhds_unique ht tendsto_const_nhds
  rwa [hreduce] at heq

/-- For a C1 affine gradient and C1 source, the classical differentiated
flux obeys the global weak equation with both differentiated forcing terms. -/
theorem weakDivergence_forced_fderiv {d : ℕ}
    {a : Vec d → Mat d} {g S : Vec d → Vec d}
    (ha : ∀ j k, ContDiff ℝ (1 : ℕ∞) (fun x => a x j k))
    (hg : ∀ j, ContDiff ℝ (1 : ℕ∞) (fun x => g x j))
    (hS : ∀ j, ContDiff ℝ (1 : ℕ∞) (fun x => S x j))
    (e : Vec d)
    (he : HasWeakDivergence Set.univ
      (fun x => (a x).mulVec (e + g x) + S x) (fun _ => 0)) (z : Vec d) :
    HasWeakDivergence Set.univ
      (fun x => (a x).mulVec (fun k => fderiv ℝ (fun y => g y k) x z) +
        (Matrix.mulVec (fun j k => fderiv ℝ (fun y => a y j k) x z) (e + g x) +
          (fun j => fderiv ℝ (fun y => S y j) x z))) (fun _ => 0) := by
  have hflux (j : Fin d) : ContDiff ℝ (1 : ℕ∞)
      (fun x => ((a x).mulVec (e + g x) + S x) j) := by
    change ContDiff ℝ (1 : ℕ∞)
      (fun x => (∑ k, a x j k * (e k + g x k)) + S x j)
    apply ContDiff.add
    · apply ContDiff.sum
      intro k _
      exact (ha j k).mul (contDiff_const.add (hg k))
    · exact hS j
  have hder := weakDivergence_fderiv hflux he z
  have hid (x : Vec d) :
      (fun j => fderiv ℝ (fun y => ((a y).mulVec (e + g y) + S y) j) x z) =
        (a x).mulVec (fun k => fderiv ℝ (fun y => g y k) x z) +
          (Matrix.mulVec (fun j k => fderiv ℝ (fun y => a y j k) x z) (e + g x) +
            (fun j => fderiv ℝ (fun y => S y j) x z)) := by
    ext j
    have hap (k : Fin d) := (ha j k).differentiable (by simp) x
    have hgp (k : Fin d) := (hg k).differentiable (by simp) x
    have hsp := (hS j).differentiable (by simp) x
    have hprod (k : Fin d) : DifferentiableAt ℝ
        (fun y => a y j k * (e k + g y k)) x :=
      (hap k).mul ((hgp k).const_add (e k))
    change fderiv ℝ (fun y => (∑ k, a y j k * (e k + g y k)) + S y j) x z = _
    rw [fderiv_fun_add (DifferentiableAt.fun_sum (fun k _ => hprod k)) hsp,
      fderiv_fun_sum (fun k _ => hprod k)]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sum_apply]
    have hterm (k : Fin d) :
        fderiv ℝ (fun y => a y j k * (e k + g y k)) x z =
          a x j k * fderiv ℝ (fun y => g y k) x z +
            fderiv ℝ (fun y => a y j k) x z * (e k + g x k) := by
      rw [fderiv_fun_mul (hap k) ((hgp k).const_add (e k)),
        fderiv_const_add]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
      ring
    simp only [hterm, Finset.sum_add_distrib, Pi.add_apply, Matrix.mulVec, dotProduct]
    ring
  apply Correctors.hasWeakDivergence_congr_ae isOpen_univ hder
    (Filter.Eventually.of_forall hid) Filter.EventuallyEq.rfl

/-- On a finite-volume domain, pointwise convergence with a uniform
bound on the scalar errors gives strong `L²` convergence. -/
theorem tendsto_scalarLp_of_bounded_pointwise
    {d : ℕ} {U : Set (Vec d)} [IsFiniteMeasure (PDE.volumeOn U)]
    (v : ℕ → PDE.ScalarLp U (2 : ℝ≥0∞)) (f : PDE.ScalarLp U (2 : ℝ≥0∞))
    {C : ℝ} (hC : ∀ n, ∀ᵐ x ∂PDE.volumeOn U, |v n x - f x| ≤ C)
    (hlim : ∀ᵐ x ∂PDE.volumeOn U, Tendsto (fun n => v n x) atTop (𝓝 (f x))) :
    Tendsto v atTop (𝓝 f) := by
  have hsq : Tendsto (fun n => ∫ x, (v n x - f x) ^ 2 ∂PDE.volumeOn U)
      atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence (μ := PDE.volumeOn U)
      (F := fun n x => (v n x - f x) ^ 2) (f := fun _ => (0 : ℝ))
      (fun _ => C ^ 2) (fun n => ((Lp.aestronglyMeasurable (v n)).sub
        (Lp.aestronglyMeasurable f)).pow 2) (integrable_const _) ?_ ?_
    · simpa using h
    · intro n
      filter_upwards [hC n] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hx 2
    · filter_upwards [hlim] with x hx
      simpa using (hx.sub_const (f x)).pow 2
  have heq (n : ℕ) : (∫ x, (v n x - f x) ^ 2 ∂PDE.volumeOn U) =
      ‖v n - f‖ ^ 2 := by
    apply PDE.integral_sq_eq_sq_norm_of_ae_eq
    exact Lp.coeFn_sub (v n) f
  have hnorm : Tendsto (fun n => ‖v n - f‖) atTop (𝓝 0) := by
    have h := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
    change Tendsto (fun n => Real.sqrt (∫ x, (v n x - f x) ^ 2 ∂PDE.volumeOn U))
      atTop (𝓝 (Real.sqrt 0)) at h
    simpa only [heq, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using h
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hnorm

/-- Uniform energy and bounded pointwise convergence of concrete Sobolev
representatives give a genuine weak gradient for the limiting function. -/
theorem exists_h1Function_of_energy_bound_of_pointwise
    {d : ℕ} {U : Set (Vec d)} [IsFiniteMeasure (PDE.volumeOn U)]
    (v : ℕ → PDE.H1Function U) {M : ℝ}
    (hM : ∀ n, (∫ x in U, (v n).toFun x ^ 2) +
      (∫ x in U, PDE.vecNormSq ((v n).grad x)) ≤ M)
    {f : Vec d → ℝ} (hf : MemLp f 2 (PDE.volumeOn U)) {C : ℝ}
    (hC : ∀ n, ∀ᵐ x ∂PDE.volumeOn U, |(v n).toFun x - f x| ≤ C)
    (hlim : ∀ᵐ x ∂PDE.volumeOn U,
      Tendsto (fun n => (v n).toFun x) atTop (𝓝 (f x))) :
    ∃ w : PDE.H1Function U, w.toFun =ᵐ[PDE.volumeOn U] f := by
  let V := fun n => (v n).toW1pFunction.toW1pGraph.1.1
  let F := hf.toLp f
  have hF : ⇑F =ᵐ[PDE.volumeOn U] f := hf.coeFn_toLp
  have hV : ∀ᵐ x ∂PDE.volumeOn U, ∀ n, V n x = (v n).toFun x :=
    ae_all_iff.mpr (fun n => (v n).toW1pFunction.coeFn_toW1pGraph_fst)
  have hbound (n : ℕ) : ∀ᵐ x ∂PDE.volumeOn U, |V n x - F x| ≤ C := by
    filter_upwards [hV, hF, hC n] with x hx hfx hcx
    simpa only [hx n, hfx] using hcx
  have hconv : ∀ᵐ x ∂PDE.volumeOn U, Tendsto (fun n => V n x) atTop (𝓝 (F x)) := by
    filter_upwards [hV, hF, hlim] with x hx hfx htx
    simpa only [hx, hfx] using htx
  have hstrong := tendsto_scalarLp_of_bounded_pointwise V F hbound hconv
  obtain ⟨w, hw⟩ := exists_h1Function_of_energy_bound_of_value_tendsto v hM hstrong
  exact ⟨w, hw.trans hF⟩

/-- Uniform energy and bounded pointwise convergence of concrete Sobolev
representatives retain all weak Euclidean gradient pairings at the limit. -/
theorem exists_h1Function_of_energy_bound_of_pointwise_with_pairings
    {d : ℕ} {U : Set (Vec d)} [IsFiniteMeasure (PDE.volumeOn U)]
    (v : ℕ → PDE.H1Function U) {M : ℝ}
    (hM : ∀ n, (∫ x in U, (v n).toFun x ^ 2) +
      (∫ x in U, PDE.vecNormSq ((v n).grad x)) ≤ M)
    {f : Vec d → ℝ} (hf : MemLp f 2 (PDE.volumeOn U)) {C : ℝ}
    (hC : ∀ n, ∀ᵐ x ∂PDE.volumeOn U, |(v n).toFun x - f x| ≤ C)
    (hlim : ∀ᵐ x ∂PDE.volumeOn U,
      Tendsto (fun n => (v n).toFun x) atTop (𝓝 (f x))) :
    ∃ w : PDE.H1Function U, w.toFun =ᵐ[PDE.volumeOn U] f ∧
      ∃ l : Filter ℕ, l.NeBot ∧ l ≤ atTop ∧
        ∀ (F : Vec d → Vec d), PDE.MemVectorL2On U F →
          Tendsto (fun n => ∫ x in U, PDE.vecDot ((v n).grad x) (F x)) l
            (𝓝 (∫ x in U, PDE.vecDot (w.grad x) (F x))) := by
  let V := fun n => (v n).toW1pFunction.toW1pGraph.1.1
  let F := hf.toLp f
  have hF : ⇑F =ᵐ[PDE.volumeOn U] f := hf.coeFn_toLp
  have hV : ∀ᵐ x ∂PDE.volumeOn U, ∀ n, V n x = (v n).toFun x :=
    ae_all_iff.mpr (fun n => (v n).toW1pFunction.coeFn_toW1pGraph_fst)
  have hbound (n : ℕ) : ∀ᵐ x ∂PDE.volumeOn U, |V n x - F x| ≤ C := by
    filter_upwards [hV, hF, hC n] with x hx hfx hcx
    simpa only [hx n, hfx] using hcx
  have hconv : ∀ᵐ x ∂PDE.volumeOn U, Tendsto (fun n => V n x) atTop (𝓝 (F x)) := by
    filter_upwards [hV, hF, hlim] with x hx hfx htx
    simpa only [hx, hfx] using htx
  have hstrong := tendsto_scalarLp_of_bounded_pointwise V F hbound hconv
  obtain ⟨w, hw, hpair⟩ :=
    exists_h1Function_of_energy_bound_of_value_tendsto_with_pairings v hM hstrong
  exact ⟨w, hw.trans hF, hpair⟩

/-- A directional derivative of an actual `C¹` affine weak solution has
an `H¹` representative on every inner cutoff domain. The second weak derivative
is obtained from the forced quotient energy, rather than assumed. -/
theorem exists_h1Function_fderiv_of_affine_weak_equation_with_pairings
    {d : ℕ} {U V : Set (Vec d)} {Λ : ℝ}
    (hU : PDE.IsOpenBoundedConvexDomain U) (hV : PDE.IsOpenBoundedConvexDomain V)
    (hVU : V ⊆ U) {a : Vec d → Mat d} {L : ℝ}
    (hell : PDE.IsEllipticFieldOn 1 Λ U a)
    (ha : ∀ j k, Continuous (fun x => a x j k)) (haL : IsOperatorLipschitz L a)
    {u : Vec d → ℝ} {g : Vec d → Vec d}
    (hu : ContDiff ℝ (1 : ℕ∞) u) (hg : Continuous g)
    (hw : HasWeakGradient Set.univ u g) (e : Vec d)
    (he : HasWeakDivergence Set.univ (fun x => (a x).mulVec (e + g x)) (fun _ => 0))
    (z : Vec d) {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηc : HasCompactSupport η) (hηU : tsupport η ⊆ U)
    (hηV : ∀ x ∈ V, η x = 1) :
    ∃ w : PDE.H1Function V,
      w.toFun =ᵐ[PDE.volumeOn V] (fun x => fderiv ℝ u x z) ∧
      ∃ l : Filter ℕ, l.NeBot ∧ l ≤ atTop ∧
        ∀ (F : Vec d → Vec d), PDE.MemVectorL2On V F →
          Tendsto (fun n => ∫ x in V, PDE.vecDot
            ((C3SublinearC1.mollifierScale n)⁻¹ •
              (g (C3SublinearC1.mollifierScale n • z + x) - g x)) (F x)) l
            (𝓝 (∫ x in V, PDE.vecDot (w.grad x) (F x))) := by
  have := hV.isSobolevRegularDomain.isFiniteMeasure_volumeOn
  have := hU.isSobolevRegularDomain.isFiniteMeasure_volumeOn
  obtain ⟨E, _, hE⟩ := exists_uniform_differenceQuotient_energy
    hU hell ha haL hu hg hw e he z hη hηc hηU
  obtain ⟨C, _, hdata⟩ := exists_uniform_quotient_data_bound
    hV.isBoundedDomain.isBounded hu hg e z
  let s := C3SublinearC1.mollifierScale
  have hspos (n : ℕ) : 0 < s n := C3SublinearC1.mollifierScale_pos n
  have hsle (n : ℕ) : |s n| ≤ 1 := by
    rw [abs_of_pos (hspos n)]
    change 1 / (n + 1 : ℝ) ≤ 1
    exact (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])
  let q := fun n x => (s n)⁻¹ * (u (s n • z + x) - u x)
  let G := fun n x => (s n)⁻¹ • (g (s n • z + x) - g x)
  have hqc (n : ℕ) : Continuous (q n) := continuous_const.mul
    ((hu.continuous.comp (continuous_const.add continuous_id)).sub hu.continuous)
  have hGc (n : ℕ) : Continuous (G n) :=
    (continuous_const : Continuous (fun _ : Vec d => (s n)⁻¹)).smul
      ((hg.comp (continuous_const.add continuous_id)).sub hg)
  let v : ℕ → PDE.H1Function V := fun n => C3SublinearC1.sourceH1
    (continuous_memLp_bounded hV (hqc n)) (continuous_memLp_bounded hV (hGc n))
    (weakGradient_differenceQuotient hw (s n • z) (s n))
  have hmem : ∀ᵐ x ∂PDE.volumeOn V, x ∈ V :=
    (ae_restrict_iff' hV.measurableSet).mpr (Eventually.of_forall fun _ hx => hx)
  have hscalar (n : ℕ) : (∫ x in V, q n x ^ 2) ≤ C ^ 2 * (volume V).toReal := by
    calc
      (∫ x in V, q n x ^ 2) ≤ ∫ _x in V, C ^ 2 := by
        apply integral_mono_of_nonneg (Eventually.of_forall fun _ => sq_nonneg _)
          (integrable_const _)
        filter_upwards [hmem] with x hx
        simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _)
          (hdata _ (ne_of_gt (hspos n)) (hsle n) x hx).1 2
      _ = C ^ 2 * (volume V).toReal := by simp [Measure.real, mul_comm]
  have hgradient (n : ℕ) : (∫ x in V, PDE.vecNormSq (G n x)) ≤ E := by
    have hInt : IntegrableOn (fun x => η x ^ 2 * PDE.vecNormSq (G n x)) U :=
      (continuous_memLp_bounded hU ((hη.continuous.pow 2).mul
        (PDE.continuous_vecNormSq.comp (hGc n)))).integrable (by norm_num)
    calc
      (∫ x in V, PDE.vecNormSq (G n x)) =
          ∫ x in V, η x ^ 2 * PDE.vecNormSq (G n x) := by
        apply integral_congr_ae
        filter_upwards [hmem] with x hx
        rw [hηV x hx, one_pow, one_mul]
      _ ≤ ∫ x in U, η x ^ 2 * PDE.vecNormSq (G n x) :=
        setIntegral_mono_set hInt
          (Eventually.of_forall fun _ => mul_nonneg (sq_nonneg _) (PDE.vecNormSq_nonneg _))
          (Eventually.of_forall hVU)
      _ ≤ E := hE _ (ne_of_gt (hspos n)) (hsle n)
  let f := fun x => fderiv ℝ u x z
  have hfc : Continuous f := (hu.continuous_fderiv (by simp)).clm_apply continuous_const
  obtain ⟨B, hB⟩ := hV.isBoundedDomain.isBounded.isCompact_closure.exists_bound_of_continuousOn
    hfc.continuousOn
  have hlim (x : Vec d) : Tendsto (fun n => q n x) atTop (𝓝 (f x)) :=
    (tendsto_differenceQuotient (hu.differentiable (by simp) x) z).comp
      (C3SublinearC1.mollifierScale_tendsto.mono_right (nhdsGT_le_nhdsNE 0))
  apply exists_h1Function_of_energy_bound_of_pointwise_with_pairings v
    (M := C ^ 2 * (volume V).toReal + E) ?_
    (continuous_memLp_bounded hV hfc) (C := C + B) ?_ ?_
  · intro n
    exact add_le_add (hscalar n) (hgradient n)
  · intro n
    filter_upwards [hmem] with x hx
    calc
      |(v n).toFun x - f x| ≤ |q n x| + |f x| := abs_sub _ _
      _ ≤ C + B := add_le_add (hdata _ (ne_of_gt (hspos n)) (hsle n) x hx).1
        (by simpa only [Real.norm_eq_abs] using hB x (subset_closure hx))
  · exact Eventually.of_forall hlim

/-- Uniform forced quotient energy produces a local weak directional
derivative with all L2 gradient pairings retained. -/
theorem exists_h1Function_fderiv_of_forced_weak_equation_with_pairings
    {d : ℕ} {U V : Set (Vec d)} {Λ : ℝ}
    (hU : PDE.IsOpenBoundedConvexDomain U) (hV : PDE.IsOpenBoundedConvexDomain V)
    (hVU : V ⊆ U) {a : Vec d → Mat d} {L : ℝ}
    (hell : PDE.IsEllipticFieldOn 1 Λ U a)
    (ha : ∀ j k, Continuous (fun x => a x j k)) (haL : IsOperatorLipschitz L a)
    {u : Vec d → ℝ} {g S : Vec d → Vec d}
    (hu : ContDiff ℝ (1 : ℕ∞) u) (hg : Continuous g)
    (hS : ∀ j, ContDiff ℝ (1 : ℕ∞) (fun x => S x j))
    (hw : HasWeakGradient Set.univ u g) (e : Vec d)
    (he : HasWeakDivergence Set.univ (fun x => (a x).mulVec (e + g x) + S x) (fun _ => 0))
    (z : Vec d) {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηc : HasCompactSupport η) (hηU : tsupport η ⊆ U)
    (hηV : ∀ x ∈ V, η x = 1) :
    ∃ w : PDE.H1Function V,
      w.toFun =ᵐ[PDE.volumeOn V] (fun x => fderiv ℝ u x z) ∧
      ∃ l : Filter ℕ, l.NeBot ∧ l ≤ atTop ∧
        ∀ (F : Vec d → Vec d), PDE.MemVectorL2On V F →
          Tendsto (fun n => ∫ x in V, PDE.vecDot
            ((C3SublinearC1.mollifierScale n)⁻¹ •
              (g (C3SublinearC1.mollifierScale n • z + x) - g x)) (F x)) l
            (𝓝 (∫ x in V, PDE.vecDot (w.grad x) (F x))) := by
  have := hV.isSobolevRegularDomain.isFiniteMeasure_volumeOn
  have := hU.isSobolevRegularDomain.isFiniteMeasure_volumeOn
  obtain ⟨E, _, hE⟩ := exists_uniform_forced_differenceQuotient_energy
    hU hell ha haL hu hg hS hw e he z hη hηc hηU
  obtain ⟨C, _, hdata⟩ := exists_uniform_quotient_data_bound
    hV.isBoundedDomain.isBounded hu hg e z
  let s := C3SublinearC1.mollifierScale
  have hspos (n : ℕ) : 0 < s n := C3SublinearC1.mollifierScale_pos n
  have hsle (n : ℕ) : |s n| ≤ 1 := by
    rw [abs_of_pos (hspos n)]
    change 1 / (n + 1 : ℝ) ≤ 1
    exact (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])
  let q := fun n x => (s n)⁻¹ * (u (s n • z + x) - u x)
  let G := fun n x => (s n)⁻¹ • (g (s n • z + x) - g x)
  have hqc (n : ℕ) : Continuous (q n) := continuous_const.mul
    ((hu.continuous.comp (continuous_const.add continuous_id)).sub hu.continuous)
  have hGc (n : ℕ) : Continuous (G n) :=
    (continuous_const : Continuous (fun _ : Vec d => (s n)⁻¹)).smul
      ((hg.comp (continuous_const.add continuous_id)).sub hg)
  let v : ℕ → PDE.H1Function V := fun n => C3SublinearC1.sourceH1
    (continuous_memLp_bounded hV (hqc n)) (continuous_memLp_bounded hV (hGc n))
    (weakGradient_differenceQuotient hw (s n • z) (s n))
  have hmem : ∀ᵐ x ∂PDE.volumeOn V, x ∈ V :=
    (ae_restrict_iff' hV.measurableSet).mpr (Eventually.of_forall fun _ hx => hx)
  have hscalar (n : ℕ) : (∫ x in V, q n x ^ 2) ≤ C ^ 2 * (volume V).toReal := by
    calc
      (∫ x in V, q n x ^ 2) ≤ ∫ _x in V, C ^ 2 := by
        apply integral_mono_of_nonneg (Eventually.of_forall fun _ => sq_nonneg _)
          (integrable_const _)
        filter_upwards [hmem] with x hx
        simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _)
          (hdata _ (ne_of_gt (hspos n)) (hsle n) x hx).1 2
      _ = C ^ 2 * (volume V).toReal := by simp [Measure.real, mul_comm]
  have hgradient (n : ℕ) : (∫ x in V, PDE.vecNormSq (G n x)) ≤ E := by
    have hInt : IntegrableOn (fun x => η x ^ 2 * PDE.vecNormSq (G n x)) U :=
      (continuous_memLp_bounded hU ((hη.continuous.pow 2).mul
        (PDE.continuous_vecNormSq.comp (hGc n)))).integrable (by norm_num)
    calc
      (∫ x in V, PDE.vecNormSq (G n x)) =
          ∫ x in V, η x ^ 2 * PDE.vecNormSq (G n x) := by
        apply integral_congr_ae
        filter_upwards [hmem] with x hx
        rw [hηV x hx, one_pow, one_mul]
      _ ≤ ∫ x in U, η x ^ 2 * PDE.vecNormSq (G n x) :=
        setIntegral_mono_set hInt
          (Eventually.of_forall fun _ => mul_nonneg (sq_nonneg _) (PDE.vecNormSq_nonneg _))
          (Eventually.of_forall hVU)
      _ ≤ E := hE _ (ne_of_gt (hspos n)) (hsle n)
  let f := fun x => fderiv ℝ u x z
  have hfc : Continuous f := (hu.continuous_fderiv (by simp)).clm_apply continuous_const
  obtain ⟨B, hB⟩ := hV.isBoundedDomain.isBounded.isCompact_closure.exists_bound_of_continuousOn
    hfc.continuousOn
  have hlim (x : Vec d) : Tendsto (fun n => q n x) atTop (𝓝 (f x)) :=
    (tendsto_differenceQuotient (hu.differentiable (by simp) x) z).comp
      (C3SublinearC1.mollifierScale_tendsto.mono_right (nhdsGT_le_nhdsNE 0))
  apply exists_h1Function_of_energy_bound_of_pointwise_with_pairings v
    (M := C ^ 2 * (volume V).toReal + E) ?_
    (continuous_memLp_bounded hV hfc) (C := C + B) ?_ ?_
  · intro n
    exact add_le_add (hscalar n) (hgradient n)
  · intro n
    filter_upwards [hmem] with x hx
    calc
      |(v n).toFun x - f x| ≤ |q n x| + |f x| := abs_sub _ _
      _ ≤ C + B := add_le_add (hdata _ (ne_of_gt (hspos n)) (hsle n) x hx).1
        (by simpa only [Real.norm_eq_abs] using hB x (subset_closure hx))
  · exact Eventually.of_forall hlim

/-- The local weak directional derivative solves the differentiated
inhomogeneous equation. Its coefficient derivative forcing is derived from
the original affine equation, with no derivative equation premise. -/
theorem exists_h1Function_fderiv_isForcedSolution
    {d : ℕ} {U V : Set (Vec d)} {Λ : ℝ}
    (hU : PDE.IsOpenBoundedConvexDomain U) (hV : PDE.IsOpenBoundedConvexDomain V)
    (hVU : V ⊆ U) {a : Vec d → Mat d} {L : ℝ}
    (hell : PDE.IsEllipticFieldOn 1 Λ U a)
    (ha : ∀ j k, ContDiff ℝ (1 : ℕ∞) (fun x => a x j k))
    (haL : IsOperatorLipschitz L a)
    {u : Vec d → ℝ} {g : Vec d → Vec d}
    (hu : ContDiff ℝ (1 : ℕ∞) u) (hg : Continuous g)
    (hw : HasWeakGradient Set.univ u g) (e : Vec d)
    (he : HasWeakDivergence Set.univ (fun x => (a x).mulVec (e + g x)) (fun _ => 0))
    (z : Vec d) {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηc : HasCompactSupport η) (hηU : tsupport η ⊆ U)
    (hηV : ∀ x ∈ V, η x = 1) :
    ∃ w : PDE.H1Function V,
      w.toFun =ᵐ[PDE.volumeOn V] (fun x => fderiv ℝ u x z) ∧
      PDE.IsWeakDivergenceFormL2SolutionOn a V w (fun _ => 0)
        (fun x => Matrix.mulVec
          (fun j k => fderiv ℝ (fun y => a y j k) x z) (e + g x)) := by
  obtain ⟨w, hwval, l, hl, hltop, hpair⟩ :=
    exists_h1Function_fderiv_of_affine_weak_equation_with_pairings
      hU hV hVU hell (fun j k => (ha j k).continuous) haL hu hg hw e he z hη hηc hηU hηV
  have := hl
  let s := C3SublinearC1.mollifierScale
  let q := fun n x => (s n)⁻¹ * (u (s n • z + x) - u x)
  let G := fun n x => (s n)⁻¹ • (g (s n • z + x) - g x)
  let F := fun n x => (s n)⁻¹ •
    ((a (s n • z + x) - a x).mulVec (e + g (s n • z + x)))
  let F₀ := fun x => Matrix.mulVec
    (fun j k => fderiv ℝ (fun y => a y j k) x z) (e + g x)
  have hqc (n : ℕ) : Continuous (q n) := continuous_const.mul
    ((hu.continuous.comp (continuous_const.add continuous_id)).sub hu.continuous)
  have hGc (n : ℕ) : Continuous (G n) :=
    (continuous_const : Continuous (fun _ : Vec d => (s n)⁻¹)).smul
      ((hg.comp (continuous_const.add continuous_id)).sub hg)
  have hFc (n : ℕ) (j : Fin d) : Continuous (fun x => F n x j) := by
    apply continuous_const.mul
    change Continuous (fun x => ∑ k,
      (a (s n • z + x) j k - a x j k) * (e k + g (s n • z + x) k))
    exact continuous_finset_sum _ (fun k _ =>
      (((ha j k).continuous.comp (continuous_const.add continuous_id)).sub
        (ha j k).continuous).mul
        (continuous_const.add ((continuous_apply k).comp
          (hg.comp (continuous_const.add continuous_id)))))
  have hF₀ : PDE.MemVectorL2On V F₀ := by
    intro j
    apply continuous_memLp_bounded hV
    change Continuous (fun x => ∑ k,
      fderiv ℝ (fun y => a y j k) x z * (e k + g x k))
    exact continuous_finset_sum _ (fun k _ =>
      ((ha j k).continuous_fderiv (by simp)).clm_apply continuous_const |>.mul
        (continuous_const.add ((continuous_apply k).comp hg)))
  have hellV := hell.mono hV.measurableSet hVU
  have hdata : PDE.DivergenceFormL2DataOn a V w (fun _ => 0) F₀ :=
    PDE.DivergenceFormL2DataOn.of_isEllipticFieldOn hellV MemLp.zero hF₀
  refine ⟨w, hwval, hdata, ?_⟩
  intro ψ
  have hψg : Continuous ψ.grad := by
    apply continuous_pi
    intro j
    exact (ψ.contDiff.continuous_fderiv (by simp)).clm_apply continuous_const
  have hflux := tendsto_flux_test_of_gradient_pairings hV
    (fun j k => (ha j k).continuous) hpair ψ.contDiff
  have hflux' : Tendsto
      (fun n => ∫ x in V, PDE.vecDot (PDE.matVecMul (a x) (G n x)) (ψ.grad x)) l
      (𝓝 (∫ x in V, PDE.vecDot (PDE.matVecMul (a x) (w.grad x)) (ψ.grad x))) := by
    simpa only [dot, gradient, coordinateDerivative, PDE.vecDot, PDE.matVecMul,
      PDE.WeakTestFunction.grad, PDE.WeakTestFunction.partialDeriv,
      PDE.basisVec, unitVector, Matrix.mulVec, dotProduct] using hflux
  have hforce : Tendsto (fun n => ∫ x in V, PDE.vecDot (F n x) (ψ.grad x)) l
      (𝓝 (∫ x in V, PDE.vecDot (F₀ x) (ψ.grad x))) :=
    (tendsto_coefficient_commutator_test hV ha haL hg hψg e z).mono_left hltop
  have hident (n : ℕ) :
      (∫ x in V, PDE.vecDot (PDE.matVecMul (a x) (G n x)) (ψ.grad x)) =
        -(∫ x in V, PDE.vecDot (F n x) (ψ.grad x)) := by
    have hFn : PDE.MemVectorL2On V (F n) :=
      fun j => continuous_memLp_bounded hV (hFc n j)
    have hn := sourceH1_forced_isL2Solution hellV
      (continuous_memLp_bounded hV (hqc n)) (continuous_memLp_bounded hV (hGc n))
      hFn (weakGradient_differenceQuotient hw (s n • z) (s n))
      (weakDivergence_differenceQuotient e he (s n • z) (s n))
    simpa only [C3SublinearC1.sourceH1, zero_mul, integral_zero, zero_sub] using hn.identity ψ
  have heq := tendsto_nhds_unique hflux'
    (by simpa only [hident] using hforce.neg)
  simpa only [zero_mul, integral_zero, zero_sub] using heq

/-- Differentiating a forced affine equation retains both the coefficient
commutator and the directional derivative of its original source. -/
theorem exists_h1Function_fderiv_of_forced_isForcedSolution
    {d : ℕ} {U V : Set (Vec d)} {Λ : ℝ}
    (hU : PDE.IsOpenBoundedConvexDomain U) (hV : PDE.IsOpenBoundedConvexDomain V)
    (hVU : V ⊆ U) {a : Vec d → Mat d} {L : ℝ}
    (hell : PDE.IsEllipticFieldOn 1 Λ U a)
    (ha : ∀ j k, ContDiff ℝ (1 : ℕ∞) (fun x => a x j k))
    (haL : IsOperatorLipschitz L a)
    {u : Vec d → ℝ} {g S : Vec d → Vec d}
    (hu : ContDiff ℝ (1 : ℕ∞) u) (hg : Continuous g)
    (hS : ∀ j, ContDiff ℝ (1 : ℕ∞) (fun x => S x j))
    (hw : HasWeakGradient Set.univ u g) (e : Vec d)
    (he : HasWeakDivergence Set.univ (fun x => (a x).mulVec (e + g x) + S x) (fun _ => 0))
    (z : Vec d) {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηc : HasCompactSupport η) (hηU : tsupport η ⊆ U)
    (hηV : ∀ x ∈ V, η x = 1) :
    ∃ w : PDE.H1Function V,
      w.toFun =ᵐ[PDE.volumeOn V] (fun x => fderiv ℝ u x z) ∧
      PDE.IsWeakDivergenceFormL2SolutionOn a V w (fun _ => 0)
        (fun x => Matrix.mulVec
          (fun j k => fderiv ℝ (fun y => a y j k) x z) (e + g x) +
          (fun j => fderiv ℝ (fun y => S y j) x z)) := by
  obtain ⟨w, hwval, l, hl, hltop, hpair⟩ :=
    exists_h1Function_fderiv_of_forced_weak_equation_with_pairings
      hU hV hVU hell (fun j k => (ha j k).continuous) haL hu hg hS hw e he z hη hηc hηU hηV
  have := hl
  let s := C3SublinearC1.mollifierScale
  let q := fun n x => (s n)⁻¹ * (u (s n • z + x) - u x)
  let G := fun n x => (s n)⁻¹ • (g (s n • z + x) - g x)
  let A := fun n x => (s n)⁻¹ •
    ((a (s n • z + x) - a x).mulVec (e + g (s n • z + x)))
  let B := fun n x => (s n)⁻¹ • (S (s n • z + x) - S x)
  let F := fun n x => A n x + B n x
  let A₀ := fun x => Matrix.mulVec
    (fun j k => fderiv ℝ (fun y => a y j k) x z) (e + g x)
  let B₀ := fun x j => fderiv ℝ (fun y => S y j) x z
  let F₀ := fun x => A₀ x + B₀ x
  have := hV.isSobolevRegularDomain.isFiniteMeasure_volumeOn
  have hqc (n : ℕ) : Continuous (q n) := continuous_const.mul
    ((hu.continuous.comp (continuous_const.add continuous_id)).sub hu.continuous)
  have hGc (n : ℕ) : Continuous (G n) :=
    (continuous_const : Continuous (fun _ : Vec d => (s n)⁻¹)).smul
      ((hg.comp (continuous_const.add continuous_id)).sub hg)
  have hAc (n : ℕ) (j : Fin d) : Continuous (fun x => A n x j) := by
    apply continuous_const.mul
    change Continuous (fun x => ∑ k,
      (a (s n • z + x) j k - a x j k) * (e k + g (s n • z + x) k))
    exact continuous_finset_sum _ (fun k _ =>
      (((ha j k).continuous.comp (continuous_const.add continuous_id)).sub
        (ha j k).continuous).mul
        (continuous_const.add ((continuous_apply k).comp
          (hg.comp (continuous_const.add continuous_id)))))
  have hBc (n : ℕ) (j : Fin d) : Continuous (fun x => B n x j) :=
    continuous_const.mul (((hS j).continuous.comp
      (continuous_const.add continuous_id)).sub (hS j).continuous)
  have hFc (n : ℕ) (j : Fin d) : Continuous (fun x => F n x j) :=
    (hAc n j).add (hBc n j)
  have hA₀c (j : Fin d) : Continuous (fun x => A₀ x j) := by
    change Continuous (fun x => ∑ k,
      fderiv ℝ (fun y => a y j k) x z * (e k + g x k))
    exact continuous_finset_sum _ (fun k _ =>
      ((ha j k).continuous_fderiv (by simp)).clm_apply continuous_const |>.mul
        (continuous_const.add ((continuous_apply k).comp hg)))
  have hB₀c (j : Fin d) : Continuous (fun x => B₀ x j) :=
    ((hS j).continuous_fderiv (by simp)).clm_apply continuous_const
  have hF₀ : PDE.MemVectorL2On V F₀ := fun j =>
    continuous_memLp_bounded hV ((hA₀c j).add (hB₀c j))
  have hellV := hell.mono hV.measurableSet hVU
  have hdata : PDE.DivergenceFormL2DataOn a V w (fun _ => 0) F₀ :=
    PDE.DivergenceFormL2DataOn.of_isEllipticFieldOn hellV MemLp.zero hF₀
  refine ⟨w, hwval, hdata, ?_⟩
  intro ψ
  have hψg : Continuous ψ.grad := by
    apply continuous_pi
    intro j
    exact (ψ.contDiff.continuous_fderiv (by simp)).clm_apply continuous_const
  have hflux := tendsto_flux_test_of_gradient_pairings hV
    (fun j k => (ha j k).continuous) hpair ψ.contDiff
  have hflux' : Tendsto
      (fun n => ∫ x in V, PDE.vecDot (PDE.matVecMul (a x) (G n x)) (ψ.grad x)) l
      (𝓝 (∫ x in V, PDE.vecDot (PDE.matVecMul (a x) (w.grad x)) (ψ.grad x))) := by
    simpa only [dot, gradient, coordinateDerivative, PDE.vecDot, PDE.matVecMul,
      PDE.WeakTestFunction.grad, PDE.WeakTestFunction.partialDeriv,
      PDE.basisVec, unitVector, Matrix.mulVec, dotProduct] using hflux
  have hsplit (A B : Vec d → Vec d)
      (hA : ∀ j, Continuous (fun x => A x j))
      (hB : ∀ j, Continuous (fun x => B x j)) :
      (∫ x in V, PDE.vecDot (A x + B x) (ψ.grad x)) =
        (∫ x in V, PDE.vecDot (A x) (ψ.grad x)) +
        (∫ x in V, PDE.vecDot (B x) (ψ.grad x)) := by
    simp_rw [PDE.DGNM.vecDot_add_left]
    apply integral_add
    · exact (continuous_memLp_bounded hV (continuous_finsetSum _ (fun j _ =>
        (hA j).mul ((continuous_apply j).comp hψg)))).integrable (by norm_num)
    · exact (continuous_memLp_bounded hV (continuous_finsetSum _ (fun j _ =>
        (hB j).mul ((continuous_apply j).comp hψg)))).integrable (by norm_num)
  have hforce : Tendsto (fun n => ∫ x in V, PDE.vecDot (F n x) (ψ.grad x)) l
      (𝓝 (∫ x in V, PDE.vecDot (F₀ x) (ψ.grad x))) := by
    have hA := (tendsto_coefficient_commutator_test hV ha haL hg hψg e z).mono_left hltop
    have hB := (tendsto_source_quotient_test hV hS hψg z).mono_left hltop
    change Tendsto (fun n => ∫ x in V, PDE.vecDot (A n x + B n x) (ψ.grad x)) l
      (𝓝 (∫ x in V, PDE.vecDot (A₀ x + B₀ x) (ψ.grad x)))
    simp_rw [hsplit _ _ (hAc _) (hBc _), hsplit _ _ hA₀c hB₀c]
    exact hA.add hB
  have hident (n : ℕ) :
      (∫ x in V, PDE.vecDot (PDE.matVecMul (a x) (G n x)) (ψ.grad x)) =
        -(∫ x in V, PDE.vecDot (F n x) (ψ.grad x)) := by
    have hFn : PDE.MemVectorL2On V (F n) :=
      fun j => continuous_memLp_bounded hV (hFc n j)
    have hn := sourceH1_forced_isL2Solution hellV
      (continuous_memLp_bounded hV (hqc n)) (continuous_memLp_bounded hV (hGc n))
      hFn (weakGradient_differenceQuotient hw (s n • z) (s n))
      (weakDivergence_forced_differenceQuotient e he (s n • z) (s n))
    simpa only [C3SublinearC1.sourceH1, zero_mul, integral_zero, zero_sub] using hn.identity ψ
  have heq := tendsto_nhds_unique hflux'
    (by simpa only [hident] using hforce.neg)
  simpa only [zero_mul, integral_zero, zero_sub] using heq

/-- Forgetting the retained weak pairings gives the local second-derivative
representative without any additional convergence premise. -/
theorem exists_h1Function_fderiv_of_affine_weak_equation
    {d : ℕ} {U V : Set (Vec d)} {Λ : ℝ}
    (hU : PDE.IsOpenBoundedConvexDomain U) (hV : PDE.IsOpenBoundedConvexDomain V)
    (hVU : V ⊆ U) {a : Vec d → Mat d} {L : ℝ}
    (hell : PDE.IsEllipticFieldOn 1 Λ U a)
    (ha : ∀ j k, Continuous (fun x => a x j k)) (haL : IsOperatorLipschitz L a)
    {u : Vec d → ℝ} {g : Vec d → Vec d}
    (hu : ContDiff ℝ (1 : ℕ∞) u) (hg : Continuous g)
    (hw : HasWeakGradient Set.univ u g) (e : Vec d)
    (he : HasWeakDivergence Set.univ (fun x => (a x).mulVec (e + g x)) (fun _ => 0))
    (z : Vec d) {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηc : HasCompactSupport η) (hηU : tsupport η ⊆ U)
    (hηV : ∀ x ∈ V, η x = 1) :
    ∃ w : PDE.H1Function V,
      w.toFun =ᵐ[PDE.volumeOn V] (fun x => fderiv ℝ u x z) := by
  obtain ⟨w, hw, _⟩ := exists_h1Function_fderiv_of_affine_weak_equation_with_pairings
    hU hV hVU hell ha haL hu hg hw e he z hη hηc hηU hηV
  exact ⟨w, hw⟩

/-- The canonical round cutoff removes the auxiliary cutoff premise in
the local second-weak-derivative conclusion. -/
theorem exists_h1Function_fderiv_ball
    {d : ℕ} {a : Vec d → Mat d} {Λ L : ℝ}
    (ha : ∀ j k, Continuous (fun x => a x j k)) (haL : IsOperatorLipschitz L a)
    (hell : ∀ x, PDE.IsEllipticMatrix 1 Λ (a x))
    {u : Vec d → ℝ} {g : Vec d → Vec d}
    (hu : ContDiff ℝ (1 : ℕ∞) u) (hg : Continuous g)
    (hw : HasWeakGradient Set.univ u g) (e : Vec d)
    (he : HasWeakDivergence Set.univ (fun x => (a x).mulVec (e + g x)) (fun _ => 0))
    (x₀ z : Vec d) {r : ℝ} (hr : 0 < r) :
    ∃ w : PDE.H1Function (PDE.euclideanBall x₀ r),
      w.toFun =ᵐ[PDE.volumeOn (PDE.euclideanBall x₀ r)] (fun x => fderiv ℝ u x z) := by
  let η := PDE.quantitativeBallCutoff x₀ hr.le (show r < 2 * r by linarith)
  have hell' : PDE.IsEllipticFieldOn 1 Λ (PDE.euclideanBall x₀ (2 * r)) a := by
    refine ⟨?_, fun x _ => hell x⟩
    apply Measurable.of_eval
    intro j
    apply Measurable.of_eval
    intro k
    exact Measurable.ite (PDE.isOpen_euclideanBall x₀ (2 * r)).measurableSet
      (ha j k).measurable measurable_const
  exact exists_h1Function_fderiv_of_affine_weak_equation
    (PDE.isOpenBoundedConvexDomain_euclideanBall x₀ (by positivity))
    (PDE.isOpenBoundedConvexDomain_euclideanBall x₀ hr)
    (PDE.euclideanBall_mono hr.le (by linarith)) hell' ha haL hu hg hw e he z
    η.smooth η.hasCompactSupport η.tsupport_subset η.eq_one_on_inner

/-- On every round ball, the actual weak derivative satisfies the
inhomogeneous differentiated equation with its coefficient forcing. -/
theorem exists_h1Function_fderiv_ball_isForcedSolution
    {d : ℕ} {a : Vec d → Mat d} {Λ L : ℝ}
    (ha : ∀ j k, ContDiff ℝ (1 : ℕ∞) (fun x => a x j k)) (haL : IsOperatorLipschitz L a)
    (hell : ∀ x, PDE.IsEllipticMatrix 1 Λ (a x))
    {u : Vec d → ℝ} {g : Vec d → Vec d}
    (hu : ContDiff ℝ (1 : ℕ∞) u) (hg : Continuous g)
    (hw : HasWeakGradient Set.univ u g) (e : Vec d)
    (he : HasWeakDivergence Set.univ (fun x => (a x).mulVec (e + g x)) (fun _ => 0))
    (x₀ z : Vec d) {r : ℝ} (hr : 0 < r) :
    ∃ w : PDE.H1Function (PDE.euclideanBall x₀ r),
      w.toFun =ᵐ[PDE.volumeOn (PDE.euclideanBall x₀ r)] (fun x => fderiv ℝ u x z) ∧
      PDE.IsWeakDivergenceFormL2SolutionOn a (PDE.euclideanBall x₀ r) w (fun _ => 0)
        (fun x => Matrix.mulVec
          (fun j k => fderiv ℝ (fun y => a y j k) x z) (e + g x)) := by
  let η := PDE.quantitativeBallCutoff x₀ hr.le (show r < 2 * r by linarith)
  have hell' : PDE.IsEllipticFieldOn 1 Λ (PDE.euclideanBall x₀ (2 * r)) a := by
    refine ⟨?_, fun x _ => hell x⟩
    apply Measurable.of_eval
    intro j
    apply Measurable.of_eval
    intro k
    exact Measurable.ite (PDE.isOpen_euclideanBall x₀ (2 * r)).measurableSet
      (ha j k).continuous.measurable measurable_const
  exact exists_h1Function_fderiv_isForcedSolution
    (PDE.isOpenBoundedConvexDomain_euclideanBall x₀ (by positivity))
    (PDE.isOpenBoundedConvexDomain_euclideanBall x₀ hr)
    (PDE.euclideanBall_mono hr.le (by linarith)) hell' ha haL hu hg hw e he z
    η.smooth η.hasCompactSupport η.tsupport_subset η.eq_one_on_inner

/-- The actual reduced and rescaled coefficient retains the explicit
Euclidean operator Lipschitz bound from the physical regularity assumption. -/
theorem project_operatorLipschitz {d : ℕ} {L r₀ : ℝ} (hL : 1 ≤ L) (hr₀ : 0 ≤ r₀)
    (ω : PhysicalField d L) :
    IsOperatorLipschitz
      (ellipticityScale L * (Real.exp (2 * L) * (L + 2 * L ^ 2)) * r₀)
      (project (r₀ := r₀) hL ω) := by
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hB : 0 ≤ ellipticityScale L := by unfold ellipticityScale; positivity
  intro x y ξ
  have hA := Correctors.reducedCoefficient_operatorLipschitz hL ω.2 (r₀ • x) (r₀ • y) ξ
  rw [← smul_sub, euclideanNorm_smul r₀ hr₀] at hA
  change euclideanNorm
    ((ellipticityScale L • reducedCoefficient ω.1 (r₀ • x) -
      ellipticityScale L • reducedCoefficient ω.1 (r₀ • y)).mulVec ξ) ≤ _
  rw [← smul_sub, Matrix.smul_mulVec, euclideanNorm_smul _ hB]
  exact (mul_le_mul_of_nonneg_left hA hB).trans_eq (by ring)

/-- The actual C¹ representative retains the original affine weak equation,
so it can be used in difference quotients without a representative premise. -/
theorem source_corrector_c1_weak_equation
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q) (i : Fin d)
    (φ : Corrector (actualCoefficientLaw Q) (Correctors.correctorUnitVector i).ofLp) :
    ∀ᵐ ω ∂physicalReferenceLaw Q, ∃ v : Vec d → ℝ,
      ContDiff ℝ (1 : ℕ∞) v ∧
      v =ᵐ[(volume : Measure (Vec d))]
        (fun x => φ.potential (project (r₀ := D.dependenceRange)
          Q.ellipticity_parameter ω) x) ∧
      gradient v =ᵐ[(volume : Measure (Vec d))]
        φ.grad (project (r₀ := D.dependenceRange) Q.ellipticity_parameter ω) ∧
      HasWeakGradient Set.univ v (gradient v) ∧
      HasWeakDivergence Set.univ
        (fun x => (project (r₀ := D.dependenceRange) Q.ellipticity_parameter ω x).mulVec
          ((Correctors.correctorUnitVector i).ofLp + gradient v x)) (fun _ => 0) := by
  have hw := ae_of_ae_map
    (measurable_project (r₀ := D.dependenceRange) Q.ellipticity_parameter).aemeasurable
    φ.weak_gradient
  have he := ae_of_ae_map
    (measurable_project (r₀ := D.dependenceRange) Q.ellipticity_parameter).aemeasurable
    φ.harmonic
  filter_upwards [sublinear_source_corrector_c1_representative d hd D Q hQ i φ,
    hw, he] with ω hv hwω heω
  obtain ⟨v, hvc, hvp, hvg⟩ := hv
  have hvg' : gradient v =ᵐ[(volume : Measure (Vec d))]
      φ.grad (project (r₀ := D.dependenceRange) Q.ellipticity_parameter ω) := by
    filter_upwards [hvg] with x hx
    exact funext hx
  refine ⟨v, hvc, hvp, hvg', ?_, ?_⟩
  · apply Correctors.hasWeakGradient_congr_ae isOpen_univ hwω
    · simpa only [Measure.restrict_univ] using hvp.symm
    · simpa only [Measure.restrict_univ] using hvg'.symm
  · apply Correctors.hasWeakDivergence_congr_ae isOpen_univ heω _
      Filter.EventuallyEq.rfl
    simp only [Measure.restrict_univ]
    filter_upwards [hvg'] with x hx
    rw [hx]

/-- On one full-law event the actual `C¹` representative has local
second weak derivatives in every direction, on every round ball. -/
theorem source_corrector_local_h2
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q) (i : Fin d)
    (φ : Corrector (actualCoefficientLaw Q) (Correctors.correctorUnitVector i).ofLp) :
    ∀ᵐ ω ∂physicalReferenceLaw Q, ∃ v : Vec d → ℝ,
      ContDiff ℝ (1 : ℕ∞) v ∧
      v =ᵐ[(volume : Measure (Vec d))]
        (fun x => φ.potential (project (r₀ := D.dependenceRange)
          Q.ellipticity_parameter ω) x) ∧
      gradient v =ᵐ[(volume : Measure (Vec d))]
        φ.grad (project (r₀ := D.dependenceRange) Q.ellipticity_parameter ω) ∧
      ∀ (x₀ z : Vec d) (r : ℝ), 0 < r →
        ∃ w : PDE.H1Function (PDE.euclideanBall x₀ r),
          w.toFun =ᵐ[PDE.volumeOn (PDE.euclideanBall x₀ r)]
            (fun x => fderiv ℝ v x z) := by
  have hs : ∀ᵐ ω ∂physicalReferenceLaw Q, IsSmoothFieldPair ω.1 := by
    have h := hQ.mono fun _ hω => hω.1
    rw [← physicalReferenceLaw_forget Q] at h
    exact ae_of_ae_map measurable_subtype_coe.aemeasurable h
  filter_upwards [source_corrector_c1_weak_equation d hd D Q hQ i φ, hs] with ω hv hsω
  obtain ⟨v, hvc, hvp, hvg, hw, he⟩ := hv
  refine ⟨v, hvc, hvp, hvg, fun x₀ z r hr => ?_⟩
  have hg : Continuous (gradient v) := by
    apply continuous_pi
    intro j
    exact (hvc.continuous_fderiv (by simp)).clm_apply continuous_const
  exact exists_h1Function_fderiv_ball
    (fun j k => (C3SublinearC1.project_smooth Q.ellipticity_parameter ω hsω j k).continuous)
    (project_operatorLipschitz Q.ellipticity_parameter
      (zero_le_one.trans Q.range_parameter) ω)
    (C3SublinearC1.coefficient_isEllipticMatrix _) hvc hg hw
    (Correctors.correctorUnitVector i).ofLp he x₀ z hr

/-- The actual source corrector has local H1 directional derivatives
solving the full differentiated forced equation on one full-measure event. -/
theorem source_corrector_local_differentiated_equation
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q) (i : Fin d)
    (φ : Corrector (actualCoefficientLaw Q) (Correctors.correctorUnitVector i).ofLp) :
    ∀ᵐ ω ∂physicalReferenceLaw Q, ∃ v : Vec d → ℝ,
      ContDiff ℝ (1 : ℕ∞) v ∧
      v =ᵐ[(volume : Measure (Vec d))]
        (fun x => φ.potential (project (r₀ := D.dependenceRange)
          Q.ellipticity_parameter ω) x) ∧
      gradient v =ᵐ[(volume : Measure (Vec d))]
        φ.grad (project (r₀ := D.dependenceRange) Q.ellipticity_parameter ω) ∧
      ∀ (x₀ z : Vec d) (r : ℝ), 0 < r →
        ∃ w : PDE.H1Function (PDE.euclideanBall x₀ r),
          w.toFun =ᵐ[PDE.volumeOn (PDE.euclideanBall x₀ r)]
            (fun x => fderiv ℝ v x z) ∧
          PDE.IsWeakDivergenceFormL2SolutionOn
            (project (r₀ := D.dependenceRange) Q.ellipticity_parameter ω)
            (PDE.euclideanBall x₀ r) w (fun _ => 0)
            (fun x => Matrix.mulVec
              (fun j k => fderiv ℝ (fun y =>
                project (r₀ := D.dependenceRange) Q.ellipticity_parameter ω y j k) x z)
              ((Correctors.correctorUnitVector i).ofLp + gradient v x)) := by
  have hs : ∀ᵐ ω ∂physicalReferenceLaw Q, IsSmoothFieldPair ω.1 := by
    have h := hQ.mono fun _ hω => hω.1
    rw [← physicalReferenceLaw_forget Q] at h
    exact ae_of_ae_map measurable_subtype_coe.aemeasurable h
  filter_upwards [source_corrector_c1_weak_equation d hd D Q hQ i φ, hs] with ω hv hsω
  obtain ⟨v, hvc, hvp, hvg, hw, he⟩ := hv
  refine ⟨v, hvc, hvp, hvg, fun x₀ z r hr => ?_⟩
  have hg : Continuous (gradient v) := by
    apply continuous_pi
    intro j
    exact (hvc.continuous_fderiv (by simp)).clm_apply continuous_const
  exact exists_h1Function_fderiv_ball_isForcedSolution
    (fun j k => (C3SublinearC1.project_smooth Q.ellipticity_parameter ω hsω j k).of_le
      (by exact_mod_cast (show (1 : ℕ∞) ≤ ⊤ from le_top)))
    (project_operatorLipschitz Q.ellipticity_parameter
      (zero_le_one.trans Q.range_parameter) ω)
    (C3SublinearC1.coefficient_isEllipticMatrix _) hvc hg hw
    (Correctors.correctorUnitVector i).ofLp he x₀ z hr

/-- Every signed difference quotient of the literal source corrector satisfies
the weak equation with the coefficient commutator, on one full-measure event. -/
theorem source_corrector_differenceQuotients
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q) (i : Fin d)
    (φ : Corrector (actualCoefficientLaw Q) (Correctors.correctorUnitVector i).ofLp) :
    ∀ᵐ ω ∂physicalReferenceLaw Q, ∃ v : Vec d → ℝ,
      ContDiff ℝ (1 : ℕ∞) v ∧
      v =ᵐ[(volume : Measure (Vec d))]
        (fun x => φ.potential (project (r₀ := D.dependenceRange)
          Q.ellipticity_parameter ω) x) ∧
      gradient v =ᵐ[(volume : Measure (Vec d))]
        φ.grad (project (r₀ := D.dependenceRange) Q.ellipticity_parameter ω) ∧
      ∀ (z : Vec d) (t : ℝ),
        HasWeakGradient Set.univ (fun x => t⁻¹ * (v (z + x) - v x))
          (fun x => t⁻¹ • (gradient v (z + x) - gradient v x)) ∧
        HasWeakDivergence Set.univ
          (fun x => (project (r₀ := D.dependenceRange) Q.ellipticity_parameter ω x).mulVec
              (t⁻¹ • (gradient v (z + x) - gradient v x)) +
            t⁻¹ • ((project (r₀ := D.dependenceRange) Q.ellipticity_parameter ω (z + x) -
              project (r₀ := D.dependenceRange) Q.ellipticity_parameter ω x).mulVec
                ((Correctors.correctorUnitVector i).ofLp + gradient v (z + x))))
          (fun _ => 0) := by
  filter_upwards [source_corrector_c1_weak_equation d hd D Q hQ i φ] with ω hv
  obtain ⟨v, hvc, hvp, hvg, hw, he⟩ := hv
  refine ⟨v, hvc, hvp, hvg, fun z t => ?_⟩
  exact ⟨weakGradient_differenceQuotient hw z t,
    weakDivergence_differenceQuotient _ he z t⟩

/-- The same actual C¹ representative has a locally one-half-Hölder gradient
on every centered ball. Continuity identifies each Schauder representative
pointwise, so no choices of incompatible derivatives enter the bootstrap. -/
theorem source_corrector_local_holder_gradient
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q) (i : Fin d)
    (φ : Corrector (actualCoefficientLaw Q) (Correctors.correctorUnitVector i).ofLp) :
    ∀ᵐ ω ∂physicalReferenceLaw Q, ∃ v : Vec d → ℝ,
      ContDiff ℝ (1 : ℕ∞) v ∧
      v =ᵐ[(volume : Measure (Vec d))]
        (fun x => φ.potential (project (r₀ := D.dependenceRange)
          Q.ellipticity_parameter ω) x) ∧
      gradient v =ᵐ[(volume : Measure (Vec d))]
        φ.grad (project (r₀ := D.dependenceRange) Q.ellipticity_parameter ω) ∧
      ∀ R : ℝ, 0 < R → ∃ K : ℝ, 0 ≤ K ∧
        PDE.EuclideanFieldHolderSeminormLE
          (PDE.euclideanBall (0 : Vec d) R) (gradient v) (1 / 2) K := by
  have hs : ∀ᵐ ω ∂physicalReferenceLaw Q, IsSmoothFieldPair ω.1 := by
    have h := hQ.mono fun _ hω => hω.1
    rw [← physicalReferenceLaw_forget Q] at h
    exact ae_of_ae_map measurable_subtype_coe.aemeasurable h
  filter_upwards [source_corrector_c1_weak_equation d hd D Q hQ i φ, hs] with ω hv hsω
  obtain ⟨v, hvc, hvp, hvg, hw, he⟩ := hv
  have hg : Continuous (gradient v) := by
    apply continuous_pi
    intro j
    exact (hvc.continuous_fderiv (by simp)).clm_apply continuous_const
  refine ⟨v, hvc, hvp, hvg, fun R hR => ?_⟩
  have h2R : 0 < 2 * R := mul_pos (by norm_num) hR
  have hball : PDE.euclideanBall (0 : Vec d) (2 * R) = ball 0 (2 * R) := by
    ext x
    exact PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt h2R
  have huL := continuous_memLp_bounded
    (PDE.isOpenBoundedConvexDomain_euclideanBall (0 : Vec d) h2R) hvc.continuous
  have hgL := continuous_memLp_bounded
    (PDE.isOpenBoundedConvexDomain_euclideanBall (0 : Vec d) h2R) hg
  rw [hball] at huL hgL
  obtain ⟨G, K, hK, hGK, heq⟩ := exists_holder_source_gradient_ball (by omega) h2R
    (project (r₀ := D.dependenceRange) Q.ellipticity_parameter ω) i
    (C3SublinearC1.project_smooth Q.ellipticity_parameter ω hsω)
    (fun x _ => C3SublinearC1.coefficient_isEllipticMatrix _ x) huL hgL hw he
  have hrad : (2 * R) * (1 / 2 : ℝ) = R := by ring
  rw [hrad] at hGK heq
  have hpoint := MeasureTheory.Measure.eqOn_open_of_ae_eq heq
    (PDE.isOpen_euclideanBall (0 : Vec d) R)
    (hGK.continuousOn (by norm_num) hK) hg.continuousOn
  refine ⟨K, hK, fun x hx y hy => ?_⟩
  rw [← hpoint hx, ← hpoint hy]
  exact hGK x hx y hy


/-- On one full-measure event, every directional differentiated source has
its genuine local Hölder bound on the same source-corrector representative. -/
theorem source_corrector_local_holder_forcing
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q) (i : Fin d)
    (φ : Corrector (actualCoefficientLaw Q) (Correctors.correctorUnitVector i).ofLp) :
    ∀ᵐ ω ∂physicalReferenceLaw Q, ∃ v : Vec d → ℝ,
      ContDiff ℝ (1 : ℕ∞) v ∧
      v =ᵐ[(volume : Measure (Vec d))]
        (fun x => φ.potential (project (r₀ := D.dependenceRange)
          Q.ellipticity_parameter ω) x) ∧
      gradient v =ᵐ[(volume : Measure (Vec d))]
        φ.grad (project (r₀ := D.dependenceRange) Q.ellipticity_parameter ω) ∧
      ∀ (z : Vec d) (R : ℝ), 0 < R → ∃ K : ℝ, 0 ≤ K ∧
        PDE.EuclideanFieldHolderSeminormLE
          (PDE.euclideanBall (0 : Vec d) R)
          (fun x => Matrix.mulVec
            (fun j k => fderiv ℝ (fun y =>
              project (r₀ := D.dependenceRange) Q.ellipticity_parameter ω y j k) x z)
            ((Correctors.correctorUnitVector i).ofLp + gradient v x)) (1 / 2) K := by
  have hs : ∀ᵐ ω ∂physicalReferenceLaw Q, IsSmoothFieldPair ω.1 := by
    have h := hQ.mono fun _ hω => hω.1
    rw [← physicalReferenceLaw_forget Q] at h
    exact ae_of_ae_map measurable_subtype_coe.aemeasurable h
  filter_upwards [source_corrector_local_holder_gradient d hd D Q hQ i φ, hs]
    with ω hv hsω
  obtain ⟨v, hvc, hvp, hvg, hvH⟩ := hv
  have hg : Continuous (gradient v) := by
    apply continuous_pi
    intro j
    exact (hvc.continuous_fderiv (by simp)).clm_apply continuous_const
  refine ⟨v, hvc, hvp, hvg, fun z R hR => ?_⟩
  exact exists_holder_smooth_matrix_affine_gradient_ball
    (fun j k => ((contDiff_infty_iff_fderiv.mp
      (C3SublinearC1.project_smooth Q.ellipticity_parameter ω hsω j k)).2.clm_apply
        contDiff_const)) hg (Correctors.correctorUnitVector i).ofLp hR (hvH R hR)


/-- Every actual directional derivative has a locally Hölder weak gradient.
The local H1 representative and the nonzero differentiated equation are
obtained internally from the same C1 source-corrector representative. -/
theorem source_corrector_local_holder_derivative_gradient
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q) (i : Fin d)
    (φ : Corrector (actualCoefficientLaw Q) (Correctors.correctorUnitVector i).ofLp) :
    ∀ᵐ ω ∂physicalReferenceLaw Q, ∃ v : Vec d → ℝ,
      ContDiff ℝ (1 : ℕ∞) v ∧
      v =ᵐ[(volume : Measure (Vec d))]
        (fun x => φ.potential (project (r₀ := D.dependenceRange)
          Q.ellipticity_parameter ω) x) ∧
      gradient v =ᵐ[(volume : Measure (Vec d))]
        φ.grad (project (r₀ := D.dependenceRange) Q.ellipticity_parameter ω) ∧
      ∀ (z : Vec d) (R : ℝ), 0 < R →
        ∃ (w : PDE.H1Function (PDE.euclideanBall (0 : Vec d) (2 * R)))
          (G : Vec d → Vec d) (K : ℝ),
          w.toFun =ᵐ[PDE.volumeOn (PDE.euclideanBall (0 : Vec d) (2 * R))]
            (fun x => fderiv ℝ v x z) ∧
          0 ≤ K ∧ PDE.EuclideanFieldHolderSeminormLE
            (PDE.euclideanBall (0 : Vec d) R) G (1 / 2) K ∧
          G =ᵐ[PDE.volumeOn (PDE.euclideanBall (0 : Vec d) R)] w.grad := by
  have hs : ∀ᵐ ω ∂physicalReferenceLaw Q, IsSmoothFieldPair ω.1 := by
    have h := hQ.mono fun _ hω => hω.1
    rw [← physicalReferenceLaw_forget Q] at h
    exact ae_of_ae_map measurable_subtype_coe.aemeasurable h
  filter_upwards [source_corrector_local_differentiated_equation d hd D Q hQ i φ,
    source_corrector_local_holder_forcing d hd D Q hQ i φ, hs] with ω hv hv' hsω
  obtain ⟨v, hvc, hvp, hvg, hvw⟩ := hv
  obtain ⟨v', hv'c, hv'p, _, hv'F⟩ := hv'
  have heq : v = v' := MeasureTheory.Measure.eq_of_ae_eq (hvp.trans hv'p.symm)
    hvc.continuous hv'c.continuous
  subst v'
  refine ⟨v, hvc, hvp, hvg, fun z R hR => ?_⟩
  have h2R : 0 < 2 * R := mul_pos (by norm_num) hR
  obtain ⟨w, hweq, hw⟩ := hvw 0 z (2 * R) h2R
  obtain ⟨G, K, hK, hGH, hG⟩ := exists_holder_forced_gradient_ball (by omega) h2R
    (project (r₀ := D.dependenceRange) Q.ellipticity_parameter ω) _
    (C3SublinearC1.project_smooth Q.ellipticity_parameter ω hsω)
    (hv'F z (2 * R) h2R)
    (fun x _ => C3SublinearC1.coefficient_isEllipticMatrix _ x) w
    hw.toIsWeakDivergenceFormSolutionOn
  have hrad : (2 * R) * (1 / 2 : ℝ) = R := by ring
  rw [hrad] at hGH hG
  exact ⟨w, G, K, hweq, hK, hGH, hG⟩

/-- The actual source corrector has a C2 representative in its original AE
class, with the canonical gradient unchanged. -/
theorem source_corrector_c2_representative
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q) (i : Fin d)
    (φ : Corrector (actualCoefficientLaw Q) (Correctors.correctorUnitVector i).ofLp) :
    ∀ᵐ ω ∂physicalReferenceLaw Q, ∃ v : Vec d → ℝ,
      ContDiff ℝ (2 : ℕ∞) v ∧
      v =ᵐ[(volume : Measure (Vec d))]
        (fun x => φ.potential (project (r₀ := D.dependenceRange)
          Q.ellipticity_parameter ω) x) ∧
      gradient v =ᵐ[(volume : Measure (Vec d))]
        φ.grad (project (r₀ := D.dependenceRange) Q.ellipticity_parameter ω) := by
  filter_upwards [source_corrector_local_holder_derivative_gradient d hd D Q hQ i φ]
    with ω hv
  obtain ⟨v, hvc, hvp, hvg, hvw⟩ := hv
  refine ⟨v, ?_, hvp, hvg⟩
  change ContDiff ℝ ((1 : WithTop ℕ∞) + 1) v
  rw [contDiff_succ_iff_fderiv_apply]
  refine ⟨hvc.differentiable (by simp), by simp, fun z => ?_⟩
  rw [contDiff_iff_contDiffAt]
  intro x
  let R : ℝ := PDE.vecEuclideanNorm x + 1
  have hR : 0 < R := by
    dsimp [R]
    have := PDE.vecEuclideanNorm_nonneg x
    linarith
  have hx : x ∈ PDE.euclideanBall (0 : Vec d) R := by
    rw [PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hR]
    simpa [R] using (lt_add_one (PDE.vecEuclideanNorm x))
  have hsub : PDE.euclideanBall (0 : Vec d) R ⊆
      PDE.euclideanBall (0 : Vec d) (2 * R) :=
    PDE.euclideanBall_mono hR.le (by linarith)
  obtain ⟨w, G, K, hweq, hK, hGH, hG⟩ := hvw z R hR
  have hweq' : w.toFun =ᵐ[PDE.volumeOn (PDE.euclideanBall (0 : Vec d) R)]
      (fun y => fderiv ℝ v y z) :=
    ae_restrict_of_ae_restrict_of_subset hsub hweq
  have hc := contDiffOn_of_continuous_weakGradient
    (PDE.isOpenBoundedConvexDomain_euclideanBall (0 : Vec d) hR)
    (w.restrict (PDE.isOpen_euclideanBall (0 : Vec d) R) hsub)
    ((hvc.continuous_fderiv (by simp)).clm_apply continuous_const)
    hweq' (hGH.continuousOn (by norm_num) hK) hG
  exact hc.contDiffAt ((PDE.isOpen_euclideanBall (0 : Vec d) R).mem_nhds hx)

/-- C2 Hessian symmetry identifies the classical gradient of every fixed
 directional derivative with the directional derivative of the gradient. -/
theorem gradient_fderiv_eq {d : ℕ} {u : Vec d → ℝ}
    (hu : ContDiff ℝ (2 : ℕ∞) u) (z x : Vec d) :
    gradient (fun y => fderiv ℝ u y z) x =
      (fun j => fderiv ℝ (fun y => gradient u y j) x z) := by
  have hdu : DifferentiableAt ℝ (fderiv ℝ u) x :=
    ((hu.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) x
  have happ (v w : Vec d) :
      fderiv ℝ (fun y => fderiv ℝ u y v) x w =
        fderiv ℝ (fderiv ℝ u) x w v := by
    rw [fderiv_clm_apply hdu (differentiableAt_const _)]
    simp only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add,
      ContinuousLinearMap.flip_apply]
  ext j
  change fderiv ℝ (fun y => fderiv ℝ u y z) x (unitVector j) =
    fderiv ℝ (fun y => fderiv ℝ u y (unitVector j)) x z
  rw [happ, happ]
  exact (hu.contDiffAt.isSymmSndFDerivAt (by norm_num)).eq (unitVector j) z

/-- A classical C1 function has its canonical gradient as a global weak
 gradient, with local integrability supplied by continuity. -/
theorem hasWeakGradient_of_contDiff {d : ℕ} {u : Vec d → ℝ}
    (hu : ContDiff ℝ (1 : ℕ∞) u) :
    HasWeakGradient Set.univ u (gradient u) := by
  intro j
  refine ⟨hu.continuous.locallyIntegrable.locallyIntegrableOn _,
    ((hu.continuous_fderiv (by simp)).clm_apply
      continuous_const).locallyIntegrable.locallyIntegrableOn _, ?_⟩
  intro ψ hψ
  exact PDE.HasWeakGradientOn.of_contDiff hu j ψ hψ.1 hψ.2.1 hψ.2.2

/-- The differentiated forced equation uses the gradient of the actual
 classical directional derivative. Both source terms remain in the flux. -/
theorem weakDivergence_forced_gradient_fderiv {d : ℕ}
    {a : Vec d → Mat d} {u : Vec d → ℝ} {S : Vec d → Vec d}
    (ha : ∀ j k, ContDiff ℝ (1 : ℕ∞) (fun x => a x j k))
    (hu : ContDiff ℝ (2 : ℕ∞) u)
    (hS : ∀ j, ContDiff ℝ (1 : ℕ∞) (fun x => S x j))
    (e : Vec d)
    (he : HasWeakDivergence Set.univ
      (fun x => (a x).mulVec (e + gradient u x) + S x) (fun _ => 0)) (z : Vec d) :
    HasWeakDivergence Set.univ
      (fun x => (a x).mulVec (gradient (fun y => fderiv ℝ u y z) x) +
        (Matrix.mulVec (fun j k => fderiv ℝ (fun y => a y j k) x z)
          (e + gradient u x) +
          (fun j => fderiv ℝ (fun y => S y j) x z))) (fun _ => 0) := by
  have hg (j : Fin d) : ContDiff ℝ (1 : ℕ∞) (fun x => gradient u x j) :=
    (hu.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  simpa only [gradient_fderiv_eq hu] using weakDivergence_forced_fderiv ha hg hS e he z

/-- The same actual C2 source-corrector representative satisfies the global
 differentiated equation in every direction, with its coefficient forcing. -/
theorem source_corrector_c2_differentiated_equation
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q) (i : Fin d)
    (φ : Corrector (actualCoefficientLaw Q) (Correctors.correctorUnitVector i).ofLp) :
    ∀ᵐ ω ∂physicalReferenceLaw Q, ∃ v : Vec d → ℝ,
      ContDiff ℝ (2 : ℕ∞) v ∧
      v =ᵐ[(volume : Measure (Vec d))]
        (fun x => φ.potential (project (r₀ := D.dependenceRange)
          Q.ellipticity_parameter ω) x) ∧
      gradient v =ᵐ[(volume : Measure (Vec d))]
        φ.grad (project (r₀ := D.dependenceRange) Q.ellipticity_parameter ω) ∧
      ∀ z : Vec d,
        HasWeakGradient Set.univ (fun x => fderiv ℝ v x z)
          (gradient (fun x => fderiv ℝ v x z)) ∧
        HasWeakDivergence Set.univ
          (fun x => (project (r₀ := D.dependenceRange)
              Q.ellipticity_parameter ω x).mulVec
              (gradient (fun y => fderiv ℝ v y z) x) +
            Matrix.mulVec
              (fun j k => fderiv ℝ (fun y =>
                project (r₀ := D.dependenceRange) Q.ellipticity_parameter ω y j k) x z)
              ((Correctors.correctorUnitVector i).ofLp + gradient v x)) (fun _ => 0) := by
  have hs : ∀ᵐ ω ∂physicalReferenceLaw Q, IsSmoothFieldPair ω.1 := by
    have h := hQ.mono fun _ hω => hω.1
    rw [← physicalReferenceLaw_forget Q] at h
    exact ae_of_ae_map measurable_subtype_coe.aemeasurable h
  filter_upwards [source_corrector_c2_representative d hd D Q hQ i φ,
    source_corrector_c1_weak_equation d hd D Q hQ i φ, hs] with ω hv hv' hsω
  obtain ⟨v, hvc, hvp, hvg⟩ := hv
  obtain ⟨v', hv'c, hv'p, _, _, hve⟩ := hv'
  have heq : v' = v := MeasureTheory.Measure.eq_of_ae_eq (hv'p.trans hvp.symm)
    hv'c.continuous hvc.continuous
  subst v'
  refine ⟨v, hvc, hvp, hvg, fun z => ⟨?_, ?_⟩⟩
  · exact hasWeakGradient_of_contDiff
      ((hvc.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const)
  · have hve' : HasWeakDivergence Set.univ
        (fun x => (project (r₀ := D.dependenceRange) Q.ellipticity_parameter ω x).mulVec
          ((Correctors.correctorUnitVector i).ofLp + gradient v x) +
          (fun _ : Fin d => (0 : ℝ))) (fun _ => 0) := by
      simpa only [show (fun _ : Fin d => (0 : ℝ)) = 0 from rfl, add_zero] using hve
    have h := weakDivergence_forced_gradient_fderiv
      (fun j k => (C3SublinearC1.project_smooth
        Q.ellipticity_parameter ω hsω j k).of_le (by simp))
      hvc (fun _ => contDiff_const) (Correctors.correctorUnitVector i).ofLp hve' z
    simpa only [fderiv_const_apply, zero_apply,
      show (fun _ : Fin d => (0 : ℝ)) = 0 from rfl, add_zero] using h

/-- A continuous weak-gradient representative agrees pointwise on the open
 domain with the gradient of its C1 value representative. -/
theorem gradient_eqOn_of_contDiff_ae_eq {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpen U) (w : PDE.H1Function U) {u : Vec d → ℝ} {G : Vec d → Vec d}
    (hu : ContDiff ℝ (1 : ℕ∞) u)
    (hw : w.toFun =ᵐ[PDE.volumeOn U] u)
    (hG : ContinuousOn G U) (hwG : G =ᵐ[PDE.volumeOn U] w.grad) :
    EqOn (gradient u) G U := by
  have hgrad : Continuous (gradient u) := by
    apply continuous_pi
    intro j
    exact (hu.continuous_fderiv (by simp)).clm_apply continuous_const
  have hcoords (j : Fin d) :
      (fun x => gradient u x j) =ᵐ[PDE.volumeOn U] (fun x => w.grad x j) := by
    exact PDE.HasWeakPartialDerivOn.ae_eq_of_ae_eq_value hU
      (hu.continuous.locallyIntegrable.locallyIntegrableOn _)
      (locallyIntegrableOn_of_locallyIntegrable_restrict
        (w.memL2.locallyIntegrable (by norm_num)))
      (((continuous_apply j).comp hgrad).locallyIntegrable.locallyIntegrableOn _)
      (locallyIntegrableOn_of_locallyIntegrable_restrict
        ((w.gradMemL2 j).locallyIntegrable (by norm_num)))
      hw.symm (PDE.HasWeakGradientOn.of_contDiff hu j) (w.hasWeakGradient j)
  have hgradw : gradient u =ᵐ[PDE.volumeOn U] w.grad := by
    filter_upwards [ae_all_iff.mpr hcoords] with x hx
    exact funext hx
  exact MeasureTheory.Measure.eqOn_open_of_ae_eq (hgradw.trans hwG.symm)
    hU hgrad.continuousOn hG

/-- The actual C2 corrector has locally Hölder classical second derivatives.
The Hölder field from Schauder is identified with the gradient of the same
 directional derivative, rather than retained as an unrelated AE witness. -/
theorem source_corrector_c2_holder_hessian
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q) (i : Fin d)
    (φ : Corrector (actualCoefficientLaw Q) (Correctors.correctorUnitVector i).ofLp) :
    ∀ᵐ ω ∂physicalReferenceLaw Q, ∃ v : Vec d → ℝ,
      ContDiff ℝ (2 : ℕ∞) v ∧
      v =ᵐ[(volume : Measure (Vec d))]
        (fun x => φ.potential (project (r₀ := D.dependenceRange)
          Q.ellipticity_parameter ω) x) ∧
      gradient v =ᵐ[(volume : Measure (Vec d))]
        φ.grad (project (r₀ := D.dependenceRange) Q.ellipticity_parameter ω) ∧
      ∀ (z : Vec d) (R : ℝ), 0 < R → ∃ K : ℝ, 0 ≤ K ∧
        PDE.EuclideanFieldHolderSeminormLE (PDE.euclideanBall (0 : Vec d) R)
          (gradient (fun x => fderiv ℝ v x z)) (1 / 2) K := by
  filter_upwards [source_corrector_c2_representative d hd D Q hQ i φ,
    source_corrector_local_holder_derivative_gradient d hd D Q hQ i φ] with ω hv hv'
  obtain ⟨v, hvc, hvp, hvg⟩ := hv
  obtain ⟨v', hv'c, hv'p, _, hv'G⟩ := hv'
  have heq : v' = v := MeasureTheory.Measure.eq_of_ae_eq (hv'p.trans hvp.symm)
    hv'c.continuous hvc.continuous
  subst v'
  refine ⟨v, hvc, hvp, hvg, fun z R hR => ?_⟩
  obtain ⟨w, G, K, hw, hK, hGH, hwG⟩ := hv'G z R hR
  have hsub : PDE.euclideanBall (0 : Vec d) R ⊆
      PDE.euclideanBall (0 : Vec d) (2 * R) :=
    PDE.euclideanBall_mono hR.le (by linarith)
  have heqG := gradient_eqOn_of_contDiff_ae_eq
    (PDE.isOpen_euclideanBall (0 : Vec d) R)
    (w.restrict (PDE.isOpen_euclideanBall (0 : Vec d) R) hsub)
    ((hvc.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const)
    (ae_restrict_of_ae_restrict_of_subset hsub hw)
    (hGH.continuousOn (by norm_num) hK) hwG
  refine ⟨K, hK, fun x hx y hy => ?_⟩
  rw [heqG hx, heqG hy]
  exact hGH x hx y hy


/-- Hölder vector fields can be added without changing the Euclidean norm
or the common exponent. -/
theorem holder_field_add {d : ℕ} {U : Set (Vec d)} {F G : Vec d → Vec d}
    {α K B : ℝ} (hF : PDE.EuclideanFieldHolderSeminormLE U F α K)
    (hG : PDE.EuclideanFieldHolderSeminormLE U G α B) :
    PDE.EuclideanFieldHolderSeminormLE U (fun x => F x + G x) α (K + B) := by
  intro x hx y hy
  have heq : F x + G x - (F y + G y) = (F x - F y) + (G x - G y) := by abel
  rw [heq]
  exact (PDE.vecEuclideanNorm_add_le _ _).trans
    ((add_le_add (hF x hx y hy) (hG x hx y hy)).trans_eq (by ring))

/-- Local H1 differentiation for a forced equation on a ball. The source
contains both the coefficient commutator and the differentiated old source. -/
theorem exists_h1Function_fderiv_ball_of_forced_isForcedSolution
    {d : ℕ} {a : Vec d → Mat d} {Λ L : ℝ}
    (ha : ∀ j k, ContDiff ℝ (1 : ℕ∞) (fun x => a x j k))
    (haL : IsOperatorLipschitz L a)
    (hell : ∀ x, PDE.IsEllipticMatrix 1 Λ (a x))
    {u : Vec d → ℝ} {g S : Vec d → Vec d}
    (hu : ContDiff ℝ (1 : ℕ∞) u) (hg : Continuous g)
    (hS : ∀ j, ContDiff ℝ (1 : ℕ∞) (fun x => S x j))
    (hw : HasWeakGradient Set.univ u g) (e : Vec d)
    (he : HasWeakDivergence Set.univ (fun x => (a x).mulVec (e + g x) + S x) (fun _ => 0))
    (x₀ z : Vec d) {r : ℝ} (hr : 0 < r) :
    ∃ w : PDE.H1Function (PDE.euclideanBall x₀ r),
      w.toFun =ᵐ[PDE.volumeOn (PDE.euclideanBall x₀ r)] (fun x => fderiv ℝ u x z) ∧
      PDE.IsWeakDivergenceFormL2SolutionOn a (PDE.euclideanBall x₀ r) w (fun _ => 0)
        (fun x => Matrix.mulVec
          (fun j k => fderiv ℝ (fun y => a y j k) x z) (e + g x) +
          (fun j => fderiv ℝ (fun y => S y j) x z)) := by
  let η := PDE.quantitativeBallCutoff x₀ hr.le (show r < 2 * r by linarith)
  have hell' : PDE.IsEllipticFieldOn 1 Λ (PDE.euclideanBall x₀ (2 * r)) a := by
    refine ⟨?_, fun x _ => hell x⟩
    apply Measurable.of_eval
    intro j
    apply Measurable.of_eval
    intro k
    exact Measurable.ite (PDE.isOpen_euclideanBall x₀ (2 * r)).measurableSet
      (ha j k).continuous.measurable measurable_const
  exact exists_h1Function_fderiv_of_forced_isForcedSolution
    (PDE.isOpenBoundedConvexDomain_euclideanBall x₀ (by positivity))
    (PDE.isOpenBoundedConvexDomain_euclideanBall x₀ hr)
    (PDE.euclideanBall_mono hr.le (by linarith)) hell' ha haL hu hg hS hw e he z
    η.smooth η.hasCompactSupport η.tsupport_subset η.eq_one_on_inner

/-- A C1 solution with locally Hölder gradient becomes C2 when the derivative
of its source is locally Hölder. Schauder also gives locally Hölder classical
second derivatives, on the same value representative. -/
theorem contDiff_two_and_holder_gradient_fderiv_of_forced_equation
    {d : ℕ} (hd : 0 < d) {a : Vec d → Mat d} {Λ L : ℝ}
    (ha : ∀ j k, ContDiff ℝ (⊤ : ℕ∞) (fun x => a x j k))
    (haL : IsOperatorLipschitz L a)
    (hell : ∀ x, PDE.IsEllipticMatrix 1 Λ (a x))
    {u : Vec d → ℝ} {S : Vec d → Vec d}
    (hu : ContDiff ℝ (1 : ℕ∞) u)
    (hS : ∀ j, ContDiff ℝ (1 : ℕ∞) (fun x => S x j))
    (hgH : ∀ R : ℝ, 0 < R → ∃ K : ℝ, 0 ≤ K ∧
      PDE.EuclideanFieldHolderSeminormLE (PDE.euclideanBall (0 : Vec d) R)
        (gradient u) (1 / 2) K)
    (hSH : ∀ (z : Vec d) (R : ℝ), 0 < R → ∃ K : ℝ, 0 ≤ K ∧
      PDE.EuclideanFieldHolderSeminormLE (PDE.euclideanBall (0 : Vec d) R)
        (fun x j => fderiv ℝ (fun y => S y j) x z) (1 / 2) K)
    (e : Vec d)
    (he : HasWeakDivergence Set.univ
      (fun x => (a x).mulVec (e + gradient u x) + S x) (fun _ => 0)) :
    ContDiff ℝ (2 : ℕ∞) u ∧
      ∀ (z : Vec d) (R : ℝ), 0 < R → ∃ K : ℝ, 0 ≤ K ∧
        PDE.EuclideanFieldHolderSeminormLE (PDE.euclideanBall (0 : Vec d) R)
          (gradient (fun x => fderiv ℝ u x z)) (1 / 2) K := by
  have hgc : Continuous (gradient u) := by
    apply continuous_pi
    intro j
    exact (hu.continuous_fderiv (by simp)).clm_apply continuous_const
  have hlocal (z : Vec d) (R : ℝ) (hR : 0 < R) :
      ∃ (w : PDE.H1Function (PDE.euclideanBall (0 : Vec d) (2 * R)))
        (G : Vec d → Vec d) (K : ℝ),
        w.toFun =ᵐ[PDE.volumeOn (PDE.euclideanBall (0 : Vec d) (2 * R))]
          (fun x => fderiv ℝ u x z) ∧ 0 ≤ K ∧
        PDE.EuclideanFieldHolderSeminormLE (PDE.euclideanBall (0 : Vec d) R)
          G (1 / 2) K ∧
        G =ᵐ[PDE.volumeOn (PDE.euclideanBall (0 : Vec d) R)] w.grad := by
    have h2R : 0 < 2 * R := mul_pos (by norm_num) hR
    obtain ⟨w, hw, hwe⟩ := exists_h1Function_fderiv_ball_of_forced_isForcedSolution
      (fun j k => (ha j k).of_le (by simp)) haL hell hu hgc hS
      (hasWeakGradient_of_contDiff hu) e he 0 z h2R
    have hDa : ∀ j k, ContDiff ℝ (⊤ : ℕ∞)
        (fun x => fderiv ℝ (fun y => a y j k) x z) := by
      intro j k
      exact (contDiff_infty_iff_fderiv.mp (ha j k)).2.clm_apply contDiff_const
    obtain ⟨K₁, hK₁, hF₁⟩ := exists_holder_smooth_matrix_affine_gradient_ball
      hDa hgc e h2R (hgH (2 * R) h2R)
    obtain ⟨K₂, hK₂, hF₂⟩ := hSH z (2 * R) h2R
    obtain ⟨G, K, hK, hGH, hG⟩ := exists_holder_forced_gradient_ball hd h2R a _ ha
      ⟨K₁ + K₂, add_nonneg hK₁ hK₂, holder_field_add hF₁ hF₂⟩
      (fun x _ => hell x) w hwe.toIsWeakDivergenceFormSolutionOn
    have hrad : (2 * R) * (1 / 2 : ℝ) = R := by ring
    rw [hrad] at hGH hG
    exact ⟨w, G, K, hw, hK, hGH, hG⟩
  have hu₂ : ContDiff ℝ (2 : ℕ∞) u := by
    change ContDiff ℝ ((1 : WithTop ℕ∞) + 1) u
    rw [contDiff_succ_iff_fderiv_apply]
    refine ⟨hu.differentiable (by simp), by simp, fun z => ?_⟩
    rw [contDiff_iff_contDiffAt]
    intro x
    let R : ℝ := PDE.vecEuclideanNorm x + 1
    have hR : 0 < R := by
      dsimp [R]
      have := PDE.vecEuclideanNorm_nonneg x
      linarith
    have hx : x ∈ PDE.euclideanBall (0 : Vec d) R := by
      rw [PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hR]
      simpa [R] using (lt_add_one (PDE.vecEuclideanNorm x))
    have hsub : PDE.euclideanBall (0 : Vec d) R ⊆
        PDE.euclideanBall (0 : Vec d) (2 * R) :=
      PDE.euclideanBall_mono hR.le (by linarith)
    obtain ⟨w, G, K, hw, hK, hGH, hG⟩ := hlocal z R hR
    have hc := contDiffOn_of_continuous_weakGradient
      (PDE.isOpenBoundedConvexDomain_euclideanBall (0 : Vec d) hR)
      (w.restrict (PDE.isOpen_euclideanBall (0 : Vec d) R) hsub)
      ((hu.continuous_fderiv (by simp)).clm_apply continuous_const)
      (ae_restrict_of_ae_restrict_of_subset hsub hw)
      (hGH.continuousOn (by norm_num) hK) hG
    exact hc.contDiffAt ((PDE.isOpen_euclideanBall (0 : Vec d) R).mem_nhds hx)
  refine ⟨hu₂, fun z R hR => ?_⟩
  obtain ⟨w, G, K, hw, hK, hGH, hG⟩ := hlocal z R hR
  have hsub : PDE.euclideanBall (0 : Vec d) R ⊆
      PDE.euclideanBall (0 : Vec d) (2 * R) :=
    PDE.euclideanBall_mono hR.le (by linarith)
  have heqG := gradient_eqOn_of_contDiff_ae_eq
    (PDE.isOpen_euclideanBall (0 : Vec d) R)
    (w.restrict (PDE.isOpen_euclideanBall (0 : Vec d) R) hsub)
    ((hu₂.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const)
    (ae_restrict_of_ae_restrict_of_subset hsub hw)
    (hGH.continuousOn (by norm_num) hK) hG
  refine ⟨K, hK, fun x hx y hy => ?_⟩
  rw [heqG hx, heqG hy]
  exact hGH x hx y hy


/-- The derivative of a smooth matrix times an affine classical gradient
contains both product-rule terms. Hessian symmetry fixes the gradient order. -/
theorem fderiv_matrix_affine_gradient_eq {d : ℕ}
    {A : Vec d → Mat d} {u : Vec d → ℝ}
    (hA : ∀ j k, ContDiff ℝ (1 : ℕ∞) (fun x => A x j k))
    (hu : ContDiff ℝ (2 : ℕ∞) u) (e z x : Vec d) :
    (fun j => fderiv ℝ (fun y => ((A y).mulVec (e + gradient u y)) j) x z) =
      Matrix.mulVec (fun j k => fderiv ℝ (fun y => A y j k) x z)
        (e + gradient u x) +
      (A x).mulVec (gradient (fun y => fderiv ℝ u y z) x) := by
  rw [gradient_fderiv_eq hu]
  ext j
  have hap (k : Fin d) := (hA j k).differentiable (by simp) x
  have hgp (k : Fin d) : DifferentiableAt ℝ (fun y => gradient u y k) x :=
    ((hu.fderiv_right (m := 1) (by norm_num)).clm_apply
      (contDiff_const (c := unitVector k))).differentiable (by simp) x
  have hprod (k : Fin d) : DifferentiableAt ℝ
      (fun y => A y j k * (e k + gradient u y k)) x :=
    (hap k).mul ((hgp k).const_add (e k))
  change fderiv ℝ (fun y => ∑ k, A y j k * (e k + gradient u y k)) x z = _
  rw [fderiv_fun_sum (fun k _ => hprod k)]
  simp only [ContinuousLinearMap.sum_apply]
  have hterm (k : Fin d) :
      fderiv ℝ (fun y => A y j k * (e k + gradient u y k)) x z =
        fderiv ℝ (fun y => A y j k) x z * (e k + gradient u x k) +
          A x j k * fderiv ℝ (fun y => gradient u y k) x z := by
    rw [fderiv_fun_mul (hap k) ((hgp k).const_add (e k)), fderiv_const_add]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  simp only [hterm, Finset.sum_add_distrib, Pi.add_apply, Matrix.mulVec, dotProduct]

/-- The derivative of a smooth matrix times an affine C2 gradient is locally
Hölder when the actual gradient and the actual Hessian are locally Hölder. -/
theorem exists_holder_fderiv_smooth_matrix_affine_gradient_ball
    {d : ℕ} {A : Vec d → Mat d} {u : Vec d → ℝ}
    (hA : ∀ j k, ContDiff ℝ (⊤ : ℕ∞) (fun x => A x j k))
    (hu : ContDiff ℝ (2 : ℕ∞) u)
    (hgH : ∀ R : ℝ, 0 < R → ∃ K : ℝ, 0 ≤ K ∧
      PDE.EuclideanFieldHolderSeminormLE (PDE.euclideanBall (0 : Vec d) R)
        (gradient u) (1 / 2) K)
    (hHH : ∀ (z : Vec d) (R : ℝ), 0 < R → ∃ K : ℝ, 0 ≤ K ∧
      PDE.EuclideanFieldHolderSeminormLE (PDE.euclideanBall (0 : Vec d) R)
        (gradient (fun x => fderiv ℝ u x z)) (1 / 2) K)
    (e z : Vec d) {R : ℝ} (hR : 0 < R) :
    ∃ K : ℝ, 0 ≤ K ∧ PDE.EuclideanFieldHolderSeminormLE
      (PDE.euclideanBall (0 : Vec d) R)
      (fun x j => fderiv ℝ (fun y => ((A y).mulVec (e + gradient u y)) j) x z)
      (1 / 2) K := by
  have hgc : Continuous (gradient u) := by
    apply continuous_pi
    intro j
    exact ((hu.of_le (by norm_num) : ContDiff ℝ (1 : ℕ∞) u).continuous_fderiv
      (by simp)).clm_apply continuous_const
  have hdu : ContDiff ℝ (1 : ℕ∞) (fun x => fderiv ℝ u x z) :=
    (hu.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hHc : Continuous (gradient (fun x => fderiv ℝ u x z)) := by
    apply continuous_pi
    intro j
    exact (hdu.continuous_fderiv (by simp)).clm_apply continuous_const
  have hDa : ∀ j k, ContDiff ℝ (⊤ : ℕ∞)
      (fun x => fderiv ℝ (fun y => A y j k) x z) := by
    intro j k
    exact (contDiff_infty_iff_fderiv.mp (hA j k)).2.clm_apply contDiff_const
  obtain ⟨K₁, hK₁, hF₁⟩ := exists_holder_smooth_matrix_affine_gradient_ball
    (A := fun x j k => fderiv ℝ (fun y => A y j k) x z)
    hDa hgc e hR (hgH R hR)
  obtain ⟨K₂, hK₂, hF₂⟩ := exists_holder_smooth_matrix_affine_gradient_ball
    hA hHc 0 hR (hHH z R hR)
  refine ⟨K₁ + K₂, add_nonneg hK₁ hK₂, ?_⟩
  have hsum := holder_field_add hF₁ hF₂
  have hid : (fun x j => fderiv ℝ
      (fun y => ((A y).mulVec (e + gradient u y)) j) x z) =
      (fun x => Matrix.mulVec (fun j k => fderiv ℝ (fun y => A y j k) x z)
        (e + gradient u x) + (A x).mulVec (gradient (fun y => fderiv ℝ u y z) x)) := by
    funext x
    exact fderiv_matrix_affine_gradient_eq (fun j k => (hA j k).of_le (by simp)) hu e z x
  rw [hid]
  have hsum' : PDE.EuclideanFieldHolderSeminormLE
      (PDE.euclideanBall (0 : Vec d) R)
      (fun x => Matrix.mulVec (fun j k => fderiv ℝ (fun y => A y j k) x z)
        (e + gradient u x) + (A x).mulVec
          (0 + gradient (fun y => fderiv ℝ u y z) x)) (1 / 2) (K₁ + K₂) := hsum
  simpa only [zero_add] using hsum'


/-- The actual corrector is C3 in its original AE class. Its classical third
 derivatives satisfy local Hölder bounds, obtained from the differentiated
inhomogeneous source rather than a homogeneous equation. -/
theorem source_corrector_c3_holder_third_derivatives
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q) (i : Fin d)
    (φ : Corrector (actualCoefficientLaw Q) (Correctors.correctorUnitVector i).ofLp) :
    ∀ᵐ ω ∂physicalReferenceLaw Q, ∃ v : Vec d → ℝ,
      ContDiff ℝ (3 : ℕ∞) v ∧
      v =ᵐ[(volume : Measure (Vec d))]
        (fun x => φ.potential (project (r₀ := D.dependenceRange)
          Q.ellipticity_parameter ω) x) ∧
      gradient v =ᵐ[(volume : Measure (Vec d))]
        φ.grad (project (r₀ := D.dependenceRange) Q.ellipticity_parameter ω) ∧
      ∀ (z w : Vec d) (R : ℝ), 0 < R → ∃ K : ℝ, 0 ≤ K ∧
        PDE.EuclideanFieldHolderSeminormLE (PDE.euclideanBall (0 : Vec d) R)
          (gradient (fun x => fderiv ℝ (fun y => fderiv ℝ v y z) x w)) (1 / 2) K := by
  have hs : ∀ᵐ ω ∂physicalReferenceLaw Q, IsSmoothFieldPair ω.1 := by
    have h := hQ.mono fun _ hω => hω.1
    rw [← physicalReferenceLaw_forget Q] at h
    exact ae_of_ae_map measurable_subtype_coe.aemeasurable h
  filter_upwards [source_corrector_c2_differentiated_equation d hd D Q hQ i φ,
    source_corrector_c2_holder_hessian d hd D Q hQ i φ,
    source_corrector_local_holder_gradient d hd D Q hQ i φ, hs]
    with ω hv hvH hvG hsω
  obtain ⟨v, hvc, hvp, hvg, hve⟩ := hv
  obtain ⟨vH, hvHc, hvHp, _, hvHH⟩ := hvH
  have heqH : vH = v := MeasureTheory.Measure.eq_of_ae_eq (hvHp.trans hvp.symm)
    hvHc.continuous hvc.continuous
  subst vH
  obtain ⟨vG, hvGc, hvGp, _, hvGH⟩ := hvG
  have heqG : vG = v := MeasureTheory.Measure.eq_of_ae_eq (hvGp.trans hvp.symm)
    hvGc.continuous hvc.continuous
  subst vG
  let a := project (r₀ := D.dependenceRange) Q.ellipticity_parameter ω
  let e := (Correctors.correctorUnitVector i).ofLp
  have ha : ∀ j k, ContDiff ℝ (⊤ : ℕ∞) (fun x => a x j k) :=
    C3SublinearC1.project_smooth Q.ellipticity_parameter ω hsω
  have hup (z : Vec d) :
      ContDiff ℝ (2 : ℕ∞) (fun x => fderiv ℝ v x z) ∧
      ∀ (w : Vec d) (R : ℝ), 0 < R → ∃ K : ℝ, 0 ≤ K ∧
        PDE.EuclideanFieldHolderSeminormLE (PDE.euclideanBall (0 : Vec d) R)
          (gradient (fun x => fderiv ℝ (fun y => fderiv ℝ v y z) x w)) (1 / 2) K := by
    let A : Vec d → Mat d := fun x j k => fderiv ℝ (fun y => a y j k) x z
    have hA : ∀ j k, ContDiff ℝ (⊤ : ℕ∞) (fun x => A x j k) := by
      intro j k
      exact (contDiff_infty_iff_fderiv.mp (ha j k)).2.clm_apply contDiff_const
    let S : Vec d → Vec d := fun x => (A x).mulVec (e + gradient v x)
    have hS : ∀ j, ContDiff ℝ (1 : ℕ∞) (fun x => S x j) := by
      intro j
      change ContDiff ℝ (1 : ℕ∞) (fun x => ∑ k, A x j k * (e k + gradient v x k))
      apply ContDiff.sum
      intro k _
      exact ((hA j k).of_le (by simp)).mul
        (contDiff_const.add ((hvc.fderiv_right (m := 1) (by norm_num)).clm_apply
          (contDiff_const (c := unitVector k))))
    have hSH (w : Vec d) (R : ℝ) (hR : 0 < R) :
        ∃ K : ℝ, 0 ≤ K ∧ PDE.EuclideanFieldHolderSeminormLE
          (PDE.euclideanBall (0 : Vec d) R)
          (fun x j => fderiv ℝ (fun y => S y j) x w) (1 / 2) K :=
      exists_holder_fderiv_smooth_matrix_affine_gradient_ball hA hvc hvGH hvHH e w hR
    have hde : HasWeakDivergence Set.univ
        (fun x => (a x).mulVec (0 + gradient (fun y => fderiv ℝ v y z) x) + S x)
        (fun _ => 0) := by
      simpa only [zero_add] using (hve z).2
    exact contDiff_two_and_holder_gradient_fderiv_of_forced_equation (by omega)
      ha (project_operatorLipschitz Q.ellipticity_parameter
        (zero_le_one.trans Q.range_parameter) ω)
      (C3SublinearC1.coefficient_isEllipticMatrix _)
      ((hvc.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const)
      hS (hvHH z) hSH 0 hde
  refine ⟨v, ?_, hvp, hvg, fun z w R hR => (hup z).2 w R hR⟩
  change ContDiff ℝ ((2 : WithTop ℕ∞) + 1) v
  rw [contDiff_succ_iff_fderiv_apply]
  exact ⟨hvc.differentiable (by simp), by simp, fun z => (hup z).1⟩


/-- A list records successive classical directional derivatives; the head
is the last derivative applied. -/
def directionalJet {d : ℕ} (u : Vec d → ℝ) (zs : List (Vec d)) : Vec d → ℝ :=
  zs.rec u (fun z _ v x => fderiv ℝ v x z)

/-- Data for one coefficient commutator. No regularity or equation is
included in this representation of the source. -/
structure GradientJetSourceTerm (d : ℕ) where
  /-- A differentiated coefficient matrix. -/
  matrix : Vec d → Mat d
  /-- The constant affine part of this summand. -/
  offset : Vec d
  /-- The derivative word applied to the potential in this summand. -/
  directions : List (Vec d)

/-- Evaluate one matrix-gradient commutator on the original potential. -/
def GradientJetSourceTerm.field {d : ℕ} (t : GradientJetSourceTerm d)
    (u : Vec d → ℝ) : Vec d → Vec d :=
  fun x => (t.matrix x).mulVec (t.offset + gradient (directionalJet u t.directions) x)

/-- The two product-rule terms in a differentiated commutator. -/
def GradientJetSourceTerm.differentiate {d : ℕ} (t : GradientJetSourceTerm d)
    (z : Vec d) : List (GradientJetSourceTerm d) :=
  [⟨fun x j k => fderiv ℝ (fun y => t.matrix y j k) x z, t.offset, t.directions⟩,
    ⟨t.matrix, 0, z :: t.directions⟩]

/-- The source is the literal finite sum of its matrix-gradient terms. -/
def jetSourceField {d : ℕ} (u : Vec d → ℝ) (ts : List (GradientJetSourceTerm d)) :
    Vec d → Vec d :=
  (ts.map (fun t => t.field u)).sum

@[simp] theorem jetSourceField_nil {d : ℕ} (u : Vec d → ℝ) :
    jetSourceField u [] = 0 := rfl

@[simp] theorem jetSourceField_cons {d : ℕ} (u : Vec d → ℝ)
    (t : GradientJetSourceTerm d) (ts : List (GradientJetSourceTerm d)) :
    jetSourceField u (t :: ts) = t.field u + jetSourceField u ts := rfl

theorem jetSourceField_append {d : ℕ} (u : Vec d → ℝ)
    (ts ss : List (GradientJetSourceTerm d)) :
    jetSourceField u (ts ++ ss) = jetSourceField u ts + jetSourceField u ss := by
  simp only [jetSourceField, List.map_append, List.sum_append]

/-- Only the undifferentiated equation carries the original affine offset. -/
def jetOffset {d : ℕ} (e : Vec d) (zs : List (Vec d)) : Vec d :=
  if zs = [] then e else 0

@[simp] theorem jetOffset_nil {d : ℕ} (e : Vec d) : jetOffset e [] = e := rfl

@[simp] theorem jetOffset_cons {d : ℕ} (e z : Vec d) (zs : List (Vec d)) :
    jetOffset e (z :: zs) = 0 := by
  simp only [jetOffset, List.cons_ne_nil, if_false]

/-- Recursive source expansion for every directional derivative of an affine
solution. Differentiating an old source retains both product-rule terms. -/
def jetSourceTerms {d : ℕ} (a : Vec d → Mat d) (e : Vec d)
    (zs : List (Vec d)) : List (GradientJetSourceTerm d) :=
  zs.rec [] (fun z ws ts =>
    ⟨fun x j k => fderiv ℝ (fun y => a y j k) x z, jetOffset e ws, ws⟩ ::
      ts.flatMap (fun t => t.differentiate z))

@[simp] theorem jetSourceTerms_nil {d : ℕ} (a : Vec d → Mat d) (e : Vec d) :
    jetSourceTerms a e [] = [] := rfl

@[simp] theorem jetSourceTerms_cons {d : ℕ} (a : Vec d → Mat d) (e z : Vec d)
    (zs : List (Vec d)) :
    jetSourceTerms a e (z :: zs) =
      ⟨fun x j k => fderiv ℝ (fun y => a y j k) x z, jetOffset e zs, zs⟩ ::
        (jetSourceTerms a e zs).flatMap (fun t => t.differentiate z) := rfl

/-- Each commutator contains only derivatives of lower order than its own
 differentiated equation. -/
theorem jetSourceTerms_directions_length_lt {d : ℕ} (a : Vec d → Mat d)
    (e : Vec d) (zs : List (Vec d)) {t : GradientJetSourceTerm d}
    (ht : t ∈ jetSourceTerms a e zs) : t.directions.length < zs.length := by
  induction zs generalizing t with
  | nil => simp only [jetSourceTerms, List.not_mem_nil] at ht
  | cons z zs ih =>
    simp only [jetSourceTerms, List.mem_cons] at ht
    rcases ht with rfl | ht
    · simp only [List.length_cons, Nat.lt_add_one]
    · obtain ⟨s, hs, ht⟩ := List.mem_flatMap.mp ht
      simp only [GradientJetSourceTerm.differentiate, List.mem_cons,
        List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl
      · exact (ih (t := s) hs).trans (by simp)
      · simpa only [List.length_cons] using Nat.succ_lt_succ (ih (t := s) hs)

/-- Every coefficient in the complete commutator expansion remains smooth. -/
theorem jetSourceTerms_matrix_smooth {d : ℕ} {a : Vec d → Mat d}
    (ha : ∀ j k, ContDiff ℝ (⊤ : ℕ∞) (fun x => a x j k))
    (e : Vec d) (zs : List (Vec d)) {t : GradientJetSourceTerm d}
    (ht : t ∈ jetSourceTerms a e zs) :
    ∀ j k, ContDiff ℝ (⊤ : ℕ∞) (fun x => t.matrix x j k) := by
  induction zs generalizing t with
  | nil => simp only [jetSourceTerms, List.not_mem_nil] at ht
  | cons z zs ih =>
    simp only [jetSourceTerms, List.mem_cons] at ht
    rcases ht with rfl | ht
    · intro j k
      exact (contDiff_infty_iff_fderiv.mp (ha j k)).2.clm_apply contDiff_const
    · obtain ⟨s, hs, ht⟩ := List.mem_flatMap.mp ht
      simp only [GradientJetSourceTerm.differentiate, List.mem_cons,
        List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl
      · intro j k
        exact (contDiff_infty_iff_fderiv.mp (ih (t := s) hs j k)).2.clm_apply contDiff_const
      · exact ih (t := s) hs

/-- A matrix-gradient source term is C1 when its potential is C2. -/
theorem GradientJetSourceTerm.field_contDiff {d : ℕ} (t : GradientJetSourceTerm d)
    {u : Vec d → ℝ}
    (hA : ∀ j k, ContDiff ℝ (1 : ℕ∞) (fun x => t.matrix x j k))
    (hu : ContDiff ℝ (2 : ℕ∞) (directionalJet u t.directions)) :
    ∀ j, ContDiff ℝ (1 : ℕ∞) (fun x => t.field u x j) := by
  intro j
  change ContDiff ℝ (1 : ℕ∞) (fun x => ∑ k,
    t.matrix x j k * (t.offset k + gradient (directionalJet u t.directions) x k))
  apply ContDiff.sum
  intro k _
  exact (hA j k).mul (contDiff_const.add
    ((hu.fderiv_right (m := 1) (by norm_num)).clm_apply
      (contDiff_const (c := unitVector k))))

/-- The two-term commutator expansion equals the actual classical derivative. -/
theorem GradientJetSourceTerm.field_fderiv_eq {d : ℕ} (t : GradientJetSourceTerm d)
    {u : Vec d → ℝ}
    (hA : ∀ j k, ContDiff ℝ (1 : ℕ∞) (fun x => t.matrix x j k))
    (hu : ContDiff ℝ (2 : ℕ∞) (directionalJet u t.directions)) (z : Vec d) :
    (fun x j => fderiv ℝ (fun y => t.field u y j) x z) =
      jetSourceField u (t.differentiate z) := by
  funext x
  change (fun j => fderiv ℝ (fun y =>
      ((t.matrix y).mulVec (t.offset + gradient (directionalJet u t.directions) y)) j) x z) =
    Matrix.mulVec (fun j k => fderiv ℝ (fun y => t.matrix y j k) x z)
      (t.offset + gradient (directionalJet u t.directions) x) +
      ((t.matrix x).mulVec (0 + gradient
        (fun y => fderiv ℝ (directionalJet u t.directions) y z) x) + 0)
  rw [add_zero, zero_add]
  exact fderiv_matrix_affine_gradient_eq hA hu t.offset z x

/-- Finite matrix-gradient source sums inherit C1 regularity term by term. -/
theorem jetSourceField_contDiff {d : ℕ} {u : Vec d → ℝ}
    (ts : List (GradientJetSourceTerm d))
    (hA : ∀ t ∈ ts, ∀ j k, ContDiff ℝ (1 : ℕ∞) (fun x => t.matrix x j k))
    (hu : ∀ t ∈ ts, ContDiff ℝ (2 : ℕ∞) (directionalJet u t.directions)) :
    ∀ j, ContDiff ℝ (1 : ℕ∞) (fun x => jetSourceField u ts x j) := by
  induction ts with
  | nil => exact fun _ => contDiff_const
  | cons t ts ih =>
    intro j
    change ContDiff ℝ (1 : ℕ∞)
      (fun x => t.field u x j + jetSourceField u ts x j)
    exact (t.field_contDiff (hA t (by simp)) (hu t (by simp)) j).add
      (ih (fun s hs => hA s (by simp [hs])) (fun s hs => hu s (by simp [hs])) j)

/-- Differentiating a finite source sum is exactly the sum of both
product-rule terms for every original summand. -/
theorem jetSourceField_fderiv_eq {d : ℕ} {u : Vec d → ℝ}
    (ts : List (GradientJetSourceTerm d))
    (hA : ∀ t ∈ ts, ∀ j k, ContDiff ℝ (1 : ℕ∞) (fun x => t.matrix x j k))
    (hu : ∀ t ∈ ts, ContDiff ℝ (2 : ℕ∞) (directionalJet u t.directions)) (z : Vec d) :
    (fun x j => fderiv ℝ (fun y => jetSourceField u ts y j) x z) =
      jetSourceField u (ts.flatMap (fun t => t.differentiate z)) := by
  induction ts with
  | nil =>
    funext x j
    simp only [jetSourceField, List.map_nil, List.sum_nil, List.flatMap_nil,
      Pi.zero_apply, fderiv_const_apply, zero_apply]
  | cons t ts ih =>
    have htA := hA t (by simp)
    have htu := hu t (by simp)
    have hsA := fun s hs => hA s (List.mem_cons_of_mem t hs)
    have hsu := fun s hs => hu s (List.mem_cons_of_mem t hs)
    have htder := t.field_fderiv_eq htA htu z
    have hsder := ih hsA hsu
    rw [List.flatMap_cons, jetSourceField_append]
    funext x j
    change fderiv ℝ (fun y => t.field u y j + jetSourceField u ts y j) x z =
      jetSourceField u (t.differentiate z) x j +
        jetSourceField u (ts.flatMap (fun s => s.differentiate z)) x j
    rw [fderiv_fun_add ((t.field_contDiff htA htu j).differentiable (by simp) x)
      ((jetSourceField_contDiff ts hsA hsu j).differentiable (by simp) x)]
    exact congrArg₂ (fun a b : ℝ => a + b)
      (congrFun (congrFun htder x) j) (congrFun (congrFun hsder x) j)

/-- The recursive source for the next derivative is the coefficient
commutator plus the full derivative of the preceding source. -/
theorem jetSourceTerms_succ_field_eq {d : ℕ} {u : Vec d → ℝ}
    {a : Vec d → Mat d}
    (ha : ∀ j k, ContDiff ℝ (⊤ : ℕ∞) (fun x => a x j k))
    (e : Vec d) (zs : List (Vec d))
    (hu : ∀ t ∈ jetSourceTerms a e zs,
      ContDiff ℝ (2 : ℕ∞) (directionalJet u t.directions)) (z : Vec d) :
    jetSourceField u (jetSourceTerms a e (z :: zs)) =
      (fun x => Matrix.mulVec (fun j k => fderiv ℝ (fun y => a y j k) x z)
        (jetOffset e zs + gradient (directionalJet u zs) x) +
        (fun j => fderiv ℝ (fun y => jetSourceField u (jetSourceTerms a e zs) y j) x z)) := by
  rw [jetSourceTerms_cons, jetSourceField_cons,
    ← jetSourceField_fderiv_eq (jetSourceTerms a e zs)
      (fun t ht j k => (jetSourceTerms_matrix_smooth ha e zs ht j k).of_le (by simp)) hu z]
  rfl


/-- The derivative of the complete finite commutator source is locally
Hölder whenever the lower-order potentials have Hölder gradients and Hessians. -/
theorem jetSourceField_fderiv_holder {d : ℕ} {u : Vec d → ℝ}
    (ts : List (GradientJetSourceTerm d))
    (hA : ∀ t ∈ ts, ∀ j k, ContDiff ℝ (⊤ : ℕ∞) (fun x => t.matrix x j k))
    (hu : ∀ t ∈ ts, ContDiff ℝ (2 : ℕ∞) (directionalJet u t.directions))
    (hgH : ∀ t ∈ ts, ∀ R : ℝ, 0 < R → ∃ K : ℝ, 0 ≤ K ∧
      PDE.EuclideanFieldHolderSeminormLE (PDE.euclideanBall (0 : Vec d) R)
        (gradient (directionalJet u t.directions)) (1 / 2) K)
    (hHH : ∀ t ∈ ts, ∀ (z : Vec d) (R : ℝ), 0 < R → ∃ K : ℝ, 0 ≤ K ∧
      PDE.EuclideanFieldHolderSeminormLE (PDE.euclideanBall (0 : Vec d) R)
        (gradient (fun x => fderiv ℝ (directionalJet u t.directions) x z)) (1 / 2) K)
    (z : Vec d) {R : ℝ} (hR : 0 < R) :
    ∃ K : ℝ, 0 ≤ K ∧ PDE.EuclideanFieldHolderSeminormLE
      (PDE.euclideanBall (0 : Vec d) R)
      (fun x j => fderiv ℝ (fun y => jetSourceField u ts y j) x z) (1 / 2) K := by
  induction ts with
  | nil =>
    refine ⟨0, le_refl 0, ?_⟩
    intro x hx y hy
    simp only [jetSourceField_nil, Pi.zero_apply, fderiv_const_apply, zero_apply,
      sub_self, zero_mul]
    exact le_of_eq (PDE.vecEuclideanNorm_eq_zero_iff.mpr rfl)
  | cons t ts ih =>
    have htA := hA t (by simp)
    have htu := hu t (by simp)
    have hsA := fun s hs => hA s (List.mem_cons_of_mem t hs)
    have hsu := fun s hs => hu s (List.mem_cons_of_mem t hs)
    obtain ⟨K₁, hK₁, hF₁⟩ := exists_holder_fderiv_smooth_matrix_affine_gradient_ball
      htA htu (hgH t (by simp)) (hHH t (by simp)) t.offset z hR
    obtain ⟨K₂, hK₂, hF₂⟩ := ih hsA hsu
      (fun s hs => hgH s (List.mem_cons_of_mem t hs))
      (fun s hs => hHH s (List.mem_cons_of_mem t hs))
    refine ⟨K₁ + K₂, add_nonneg hK₁ hK₂, ?_⟩
    have heq : (fun x j => fderiv ℝ
        (fun y => jetSourceField u (t :: ts) y j) x z) =
        (fun x => (fun j => fderiv ℝ (fun y => t.field u y j) x z) +
          (fun j => fderiv ℝ (fun y => jetSourceField u ts y j) x z)) := by
      funext x j
      change fderiv ℝ (fun y => t.field u y j + jetSourceField u ts y j) x z = _
      rw [fderiv_fun_add
        ((t.field_contDiff (fun j k => (htA j k).of_le (by simp)) htu j).differentiable
          (by simp) x)
        ((jetSourceField_contDiff ts (fun s hs j k => (hsA s hs j k).of_le (by simp))
          hsu j).differentiable (by simp) x)]
      rfl
    rw [heq]
    exact holder_field_add hF₁ hF₂


/-- The next directional jet satisfies the recursively expanded forced
 equation. Its flux retains every differentiated coefficient and old source. -/
theorem directionalJet_forced_equation_succ {d : ℕ} {u : Vec d → ℝ}
    {a : Vec d → Mat d}
    (ha : ∀ j k, ContDiff ℝ (⊤ : ℕ∞) (fun x => a x j k))
    (e : Vec d) (zs : List (Vec d))
    (hu : ContDiff ℝ (2 : ℕ∞) (directionalJet u zs))
    (hsource : ∀ t ∈ jetSourceTerms a e zs,
      ContDiff ℝ (2 : ℕ∞) (directionalJet u t.directions))
    (he : HasWeakDivergence Set.univ
      (fun x => (a x).mulVec (jetOffset e zs + gradient (directionalJet u zs) x) +
        jetSourceField u (jetSourceTerms a e zs) x) (fun _ => 0)) (z : Vec d) :
    HasWeakDivergence Set.univ
      (fun x => (a x).mulVec
        (jetOffset e (z :: zs) + gradient (directionalJet u (z :: zs)) x) +
        jetSourceField u (jetSourceTerms a e (z :: zs)) x) (fun _ => 0) := by
  have hS := jetSourceField_contDiff (jetSourceTerms a e zs)
    (fun t ht j k => (jetSourceTerms_matrix_smooth ha e zs ht j k).of_le (by simp))
    hsource
  rw [jetSourceTerms_succ_field_eq ha e zs hsource z]
  simpa only [jetOffset_cons, zero_add, directionalJet] using
    weakDivergence_forced_gradient_fderiv (fun j k => (ha j k).of_le (by simp))
      hu hS (jetOffset e zs) he z


/-- All directional jets of an affine solution are C2, with locally Hölder
 gradients and Hessians and the complete recursively differentiated equation.
The induction uses only strictly lower-order potentials in each source. -/
theorem directionalJet_regular_of_affine_equation
    {d : ℕ} (hd : 0 < d) {a : Vec d → Mat d} {Λ L : ℝ}
    (ha : ∀ j k, ContDiff ℝ (⊤ : ℕ∞) (fun x => a x j k))
    (haL : IsOperatorLipschitz L a)
    (hell : ∀ x, PDE.IsEllipticMatrix 1 Λ (a x))
    {u : Vec d → ℝ} (hu : ContDiff ℝ (2 : ℕ∞) u)
    (hgH : ∀ R : ℝ, 0 < R → ∃ K : ℝ, 0 ≤ K ∧
      PDE.EuclideanFieldHolderSeminormLE (PDE.euclideanBall (0 : Vec d) R)
        (gradient u) (1 / 2) K)
    (hHH : ∀ (z : Vec d) (R : ℝ), 0 < R → ∃ K : ℝ, 0 ≤ K ∧
      PDE.EuclideanFieldHolderSeminormLE (PDE.euclideanBall (0 : Vec d) R)
        (gradient (fun x => fderiv ℝ u x z)) (1 / 2) K)
    (e : Vec d)
    (he : HasWeakDivergence Set.univ
      (fun x => (a x).mulVec (e + gradient u x)) (fun _ => 0)) :
    ∀ zs : List (Vec d),
      ContDiff ℝ (2 : ℕ∞) (directionalJet u zs) ∧
      (∀ R : ℝ, 0 < R → ∃ K : ℝ, 0 ≤ K ∧
        PDE.EuclideanFieldHolderSeminormLE (PDE.euclideanBall (0 : Vec d) R)
          (gradient (directionalJet u zs)) (1 / 2) K) ∧
      (∀ (z : Vec d) (R : ℝ), 0 < R → ∃ K : ℝ, 0 ≤ K ∧
        PDE.EuclideanFieldHolderSeminormLE (PDE.euclideanBall (0 : Vec d) R)
          (gradient (fun x => fderiv ℝ (directionalJet u zs) x z)) (1 / 2) K) ∧
      HasWeakDivergence Set.univ
        (fun x => (a x).mulVec (jetOffset e zs + gradient (directionalJet u zs) x) +
          jetSourceField u (jetSourceTerms a e zs) x) (fun _ => 0) := by
  intro zs
  generalize hn : zs.length = n
  induction n using Nat.strong_induction_on generalizing zs with
  | h n ih =>
    cases zs with
    | nil =>
      refine ⟨hu, hgH, hHH, ?_⟩
      simpa only [jetOffset_nil, directionalJet, jetSourceTerms_nil,
        jetSourceField_nil, Pi.zero_apply, add_zero] using he
    | cons z ws =>
      have hws : ws.length < n := by
        rw [← hn, List.length_cons]
        exact Nat.lt_succ_self _
      have hp := ih ws.length hws ws rfl
      have hsource : ∀ t ∈ jetSourceTerms a e ws,
          ContDiff ℝ (2 : ℕ∞) (directionalJet u t.directions) := by
        intro t ht
        exact (ih t.directions.length
          ((jetSourceTerms_directions_length_lt a e ws ht).trans hws)
          t.directions rfl).1
      have hnext := directionalJet_forced_equation_succ ha e ws hp.1 hsource hp.2.2.2 z
      have htlen (t : GradientJetSourceTerm d) (ht : t ∈ jetSourceTerms a e (z :: ws)) :
          t.directions.length < n := by
        rw [← hn]
        exact jetSourceTerms_directions_length_lt a e (z :: ws) ht
      have hA := fun (t : GradientJetSourceTerm d)
        (ht : t ∈ jetSourceTerms a e (z :: ws)) =>
        jetSourceTerms_matrix_smooth ha e (z :: ws) (t := t) ht
      have hC2 := fun (t : GradientJetSourceTerm d)
        (ht : t ∈ jetSourceTerms a e (z :: ws)) => (ih t.directions.length (htlen t ht) t.directions rfl).1
      have hG := fun (t : GradientJetSourceTerm d)
        (ht : t ∈ jetSourceTerms a e (z :: ws)) => (ih t.directions.length (htlen t ht) t.directions rfl).2.1
      have hH := fun (t : GradientJetSourceTerm d)
        (ht : t ∈ jetSourceTerms a e (z :: ws)) => (ih t.directions.length (htlen t ht) t.directions rfl).2.2.1
      have hS := jetSourceField_contDiff (jetSourceTerms a e (z :: ws))
        (fun t ht j k => (hA t ht j k).of_le (by simp)) hC2
      have hSH := fun (w : Vec d) (R : ℝ) (hR : 0 < R) => jetSourceField_fderiv_holder
        (jetSourceTerms a e (z :: ws)) hA hC2 hG hH w (R := R) hR
      have hu1 : ContDiff ℝ (1 : ℕ∞) (directionalJet u (z :: ws)) :=
        (hp.1.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
      have hup := contDiff_two_and_holder_gradient_fderiv_of_forced_equation
        hd ha haL hell hu1 hS (hp.2.2.1 z) hSH (jetOffset e (z :: ws)) hnext
      exact ⟨hup.1, hp.2.2.1 z, hup.2, hnext⟩


/-- C2 regularity of every directional word implies smoothness of the
original scalar function in finite dimension. -/
theorem contDiff_infty_of_directionalJet_contDiff_two {d : ℕ} {u : Vec d → ℝ}
    (hjet : ∀ zs : List (Vec d), ContDiff ℝ (2 : ℕ∞) (directionalJet u zs)) :
    ContDiff ℝ (⊤ : ℕ∞) u := by
  have hfinite (n : ℕ) : ∀ zs : List (Vec d),
      ContDiff ℝ (n : ℕ∞) (directionalJet u zs) := by
    induction n with
    | zero => exact fun zs => (hjet zs).of_le (by norm_num)
    | succ n ih =>
      intro zs
      change ContDiff ℝ ((n : WithTop ℕ∞) + 1) (directionalJet u zs)
      apply contDiff_succ_iff_fderiv_apply.mpr
      refine ⟨(hjet zs).differentiable (by norm_num), by simp, ?_⟩
      intro z
      exact ih (z :: zs)
  exact contDiff_infty.mpr (fun n => hfinite n [])

end C3SublinearSmooth

/-- The actual source corrector has a smooth representative in its original
AE potential class, with the canonical gradient in every coordinate. -/
theorem sublinear_source_corrector_smooth_representative
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q) (i : Fin d)
    (φ : Corrector (actualCoefficientLaw Q) (Correctors.correctorUnitVector i).ofLp) :
    ∀ᵐ ω ∂physicalReferenceLaw Q, ∃ v : Vec d → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) v ∧
      v =ᵐ[(volume : Measure (Vec d))]
        (fun x => φ.potential (project (r₀ := D.dependenceRange)
          Q.ellipticity_parameter ω) x) ∧
      ∀ᵐ x ∂(volume : Measure (Vec d)), ∀ j : Fin d,
        fderiv ℝ v x (unitVector j) =
          φ.grad (project (r₀ := D.dependenceRange) Q.ellipticity_parameter ω) x j := by
  have hs : ∀ᵐ ω ∂physicalReferenceLaw Q, IsSmoothFieldPair ω.1 := by
    have h := hQ.mono fun _ hω => hω.1
    rw [← physicalReferenceLaw_forget Q] at h
    exact ae_of_ae_map measurable_subtype_coe.aemeasurable h
  filter_upwards [C3SublinearSmooth.source_corrector_c2_holder_hessian d hd D Q hQ i φ,
    C3SublinearSmooth.source_corrector_local_holder_gradient d hd D Q hQ i φ,
    C3SublinearSmooth.source_corrector_c1_weak_equation d hd D Q hQ i φ, hs]
    with ω hv hvG hvE hsω
  obtain ⟨v, hvc, hvp, hvg, hvHH⟩ := hv
  obtain ⟨vG, hvGc, hvGp, _, hvGH⟩ := hvG
  have heqG : vG = v := MeasureTheory.Measure.eq_of_ae_eq (hvGp.trans hvp.symm)
    hvGc.continuous hvc.continuous
  subst vG
  obtain ⟨vE, hvEc, hvEp, _, _, hve⟩ := hvE
  have heqE : vE = v := MeasureTheory.Measure.eq_of_ae_eq (hvEp.trans hvp.symm)
    hvEc.continuous hvc.continuous
  subst vE
  have ha : ∀ j k, ContDiff ℝ (⊤ : ℕ∞) (fun x =>
      project (r₀ := D.dependenceRange) Q.ellipticity_parameter ω x j k) :=
    C3SublinearC1.project_smooth Q.ellipticity_parameter ω hsω
  have hjet := C3SublinearSmooth.directionalJet_regular_of_affine_equation (by omega)
    ha (C3SublinearSmooth.project_operatorLipschitz Q.ellipticity_parameter
      (zero_le_one.trans Q.range_parameter) ω)
    (C3SublinearC1.coefficient_isEllipticMatrix _) hvc hvGH hvHH
    (Correctors.correctorUnitVector i).ofLp hve
  refine ⟨v, C3SublinearSmooth.contDiff_infty_of_directionalJet_contDiff_two
    (fun zs => (hjet zs).1), hvp, ?_⟩
  filter_upwards [hvg] with x hx
  intro j
  exact congrFun hx j

end EinsteinFull.Blueprint
