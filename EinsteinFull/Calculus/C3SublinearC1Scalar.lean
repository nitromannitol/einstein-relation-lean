import EinsteinRelation.Correctors.AffineWeakSolutionOnBalls
import EinsteinFull.Calculus.C3SublinearPairSupport
import EinsteinFull.Blueprint.G3.node_e_u3A_sublinear_u2D_pair
import EinsteinFull.Calculus.C2CorrectorSchauderSupport
import EllipticRegularity.Schauder.C1alphaProof
import PDEFoundation.Regularity.SmoothFieldHolder
import PDEFoundation.Sobolev.H1.Smooth
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import PDEFoundation.PDE.HarmonicWeylConvergence
import PDEFoundation.Sobolev.Inequalities.SobolevWholeSpaceCutoff
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators
open scoped Convolution
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinRelation.External.AKM
open EinsteinRelation.Environment.AKMTestIntegralSupport EinsteinRelation.ReductionImageV3

namespace C3SublinearC1

/-- The derivative functional associated with a coordinate gradient, on the
existing coordinate carrier. -/
def gradientMap {d : ℕ} : Vec d →L[ℝ] (Vec d →L[ℝ] ℝ) :=
  ∑ j, (ContinuousLinearMap.smulRightL ℝ (Vec d) ℝ
    (ContinuousLinearMap.proj j)).comp (ContinuousLinearMap.proj j)

theorem gradientMap_apply_basis {d : ℕ} (g : Vec d) (j : Fin d) :
    gradientMap g (PDE.basisVec j) = g j := by
  simp [gradientMap, PDE.basisVec_apply]

theorem continuous_gradientMap {d : ℕ} : Continuous (gradientMap (d := d)) :=
  gradientMap.continuous

/-- A positive sequence of radii for the whole-space approximate identity. -/
def mollifierScale (n : ℕ) : ℝ := 1 / (n + 1 : ℝ)

theorem mollifierScale_pos (n : ℕ) : 0 < mollifierScale n := by
  unfold mollifierScale
  positivity

theorem mollifierScale_tendsto : Tendsto mollifierScale atTop (𝓝[>] (0 : ℝ)) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall mollifierScale_pos⟩
  exact tendsto_one_div_add_atTop_nhds_zero_nat

/-- The round smooth approximate identity converges locally uniformly on every
continuous field, including fields of derivative functionals. -/
theorem mollifier_tendstoLocallyUniformly
    {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {G : Vec d → E} (hG : Continuous G) :
    TendstoLocallyUniformly
      (fun n => PDE.harmonicKernelScaled (mollifierScale n)
        ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] G) G atTop := by
  have hs : Tendsto
      (fun n => Function.support (PDE.harmonicKernelScaled (d := d) (mollifierScale n)))
      atTop (𝓝 (0 : Vec d)).smallSets := by
    rw [tendsto_smallSets_iff]
    intro S hS
    obtain ⟨ε, hε, hεS⟩ := Metric.mem_nhds_iff.mp hS
    filter_upwards [(mollifierScale_tendsto.mono_right nhdsWithin_le_nhds).eventually
      (gt_mem_nhds hε)] with n hn
    intro y hy
    apply hεS
    have hy' := PDE.euclideanBall_subset_supBall (mollifierScale_pos n)
      (PDE.harmonicKernelScaled_tsupport_subset (mollifierScale_pos n)
        (subset_tsupport _ hy))
    exact Metric.ball_subset_ball hn.le hy'
  rw [tendstoLocallyUniformly_iff_forall_tendsto]
  intro x
  have hc : Tendsto
      (fun p : ℕ × Vec d =>
        (PDE.harmonicKernelScaled (mollifierScale p.1)
          ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] G) p.2)
      (atTop ×ˢ 𝓝 x) (𝓝 (G x)) :=
    convolution_tendsto_right
      (Eventually.of_forall fun p => PDE.harmonicKernelScaled_nonneg (mollifierScale_pos p.1))
      (Eventually.of_forall fun p => PDE.harmonicKernelScaled_integral_eq_one (mollifierScale_pos p.1))
      (hs.comp tendsto_fst)
      (Eventually.of_forall fun _ => hG.aestronglyMeasurable)
      ((hG.tendsto x).comp tendsto_snd) tendsto_snd
  exact (((hG.tendsto x).comp tendsto_snd).prodMk_nhds hc).mono_right
    (nhds_le_uniformity (G x))

/-- Derivative convergence controls the additive constants through the original
potential's almost-everywhere limit, so the resulting C¹ representative stays
in that potential's actual almost-everywhere class. -/
theorem exists_c1_representative_of_ae_limit
    {d : ℕ} (f : ℕ → Vec d → ℝ) (df : ℕ → Vec d → Vec d →L[ℝ] ℝ)
    (A : Vec d → Vec d →L[ℝ] ℝ) (u : Vec d → ℝ)
    (hA : Continuous A) (hf : ∀ n x, HasFDerivAt (f n) (df n x) x)
    (hdf : ∀ x r, TendstoUniformlyOn df A atTop (Metric.ball x r))
    (hu : ∀ᵐ x ∂(volume : Measure (Vec d)),
      Tendsto (fun n => f n x) atTop (𝓝 (u x))) :
    ∃ v : Vec d → ℝ, ContDiff ℝ (1 : ℕ∞) v ∧
      v =ᵐ[(volume : Measure (Vec d))] u ∧
      ∀ x, HasFDerivAt v (A x) x := by
  obtain ⟨x₀, hx₀⟩ := hu.exists
  have hconv (x : Vec d) : ∃ y : ℝ, Tendsto (fun n => f n x) atTop (𝓝 y) := by
    let r := dist x x₀ + 1
    have hC := uniformCauchySeqOn_ball_of_fderiv
      (hdf x₀ r).uniformCauchySeqOn (fun n y _ => hf n y) hx₀.cauchy_map
    apply cauchy_map_iff_exists_tendsto.mp
    exact hC.cauchy_map (by simp only [Metric.mem_ball, r]; linarith)
  choose v hv using hconv
  have hder (x : Vec d) : HasFDerivAt v (A x) x := by
    exact hasFDerivAt_of_tendstoUniformlyOn Metric.isOpen_ball (hdf x 1)
      (fun n y _ => hf n y) (fun y _ => hv y) (Metric.mem_ball_self zero_lt_one)
  refine ⟨v, contDiff_one_iff_hasFDerivAt.mpr ⟨A, hA, hder⟩, ?_, hder⟩
  filter_upwards [hu] with x hx
  exact tendsto_nhds_unique (hv x) hx

/-- A continuous weak gradient gives a classical C¹ representative of the
literal locally integrable potential. This is proved by the approximate
identity, rather than assumed as a regularity input. -/
theorem exists_c1_representative_of_continuous_weakGradient
    {d : ℕ} {u : Vec d → ℝ} {G : Vec d → Vec d}
    (hu : LocallyIntegrable u volume) (hG : Continuous G)
    (hw : PDE.HasWeakGradientOn Set.univ u G) :
    ∃ v : Vec d → ℝ, ContDiff ℝ (1 : ℕ∞) v ∧
      v =ᵐ[(volume : Measure (Vec d))] u ∧
      ∀ x j, fderiv ℝ v x (PDE.basisVec j) = G x j := by
  let K : ℕ → Vec d → ℝ := fun n => PDE.harmonicKernelScaled (mollifierScale n)
  let f : ℕ → Vec d → ℝ := fun n => K n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u
  let A : Vec d → Vec d →L[ℝ] ℝ := fun x => gradientMap (G x)
  let df : ℕ → Vec d → Vec d →L[ℝ] ℝ := fun n =>
    K n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] A
  have hA : Continuous A := continuous_gradientMap.comp hG
  have hKc (n : ℕ) : HasCompactSupport (K n) :=
    PDE.harmonicKernelScaled_hasCompactSupport (mollifierScale_pos n)
  have hKs (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (K n) :=
    PDE.harmonicKernelScaled_smooth _
  have hfs (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (f n) :=
    (hKc n).contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) (hKs n) hu
  have hdf (n : ℕ) (x : Vec d) : HasFDerivAt (f n) (df n x) x := by
    have hb (j : Fin d) : fderiv ℝ (f n) x (PDE.basisVec j) =
        df n x (PDE.basisVec j) := by
      have hd := congrFun (PDE.euclideanCoordDeriv_convolution_eq_of_hasWeakPartialDerivOn
        (hKc n) (hKs n) hu (hw j)) x
      have hi := (hKc n).convolutionExists_left_of_continuous_right
        (L := ContinuousLinearMap.lsmul ℝ ℝ) (μ := volume) (hKs n).continuous.locallyIntegrable hA x
      change Integrable (fun y => K n y • A (x - y)) volume at hi
      change fderiv ℝ (f n) x (PDE.basisVec j) = _ at hd
      rw [hd]
      change _ = (∫ y, K n y • A (x - y) ∂volume) (PDE.basisVec j)
      rw [ContinuousLinearMap.integral_apply hi]
      simp only [convolution_def, ContinuousLinearMap.lsmul_apply,
        smul_apply, A, gradientMap_apply_basis]
    have heq : fderiv ℝ (f n) x = df n x := by
      ext y
      rw [← PDE.sum_smul_basisVec y]
      simp only [map_sum, map_smul, hb]
    rw [← heq]
    exact ((hfs n).differentiable (by simp) x).hasFDerivAt
  have hdfu (x : Vec d) (r : ℝ) :
      TendstoUniformlyOn df A atTop (Metric.ball x r) := by
    have hl := mollifier_tendstoLocallyUniformly hA
    exact ((tendstoLocallyUniformly_iff_forall_isCompact.mp hl)
      (Metric.closedBall x r) (isCompact_closedBall x r)).mono Metric.ball_subset_closedBall
  have hfu : ∀ᵐ x ∂(volume : Measure (Vec d)),
      Tendsto (fun n => f n x) atTop (𝓝 (u x)) := by
    filter_upwards [PDE.ae_tendsto_harmonicKernelScaled_convolution_of_locallyIntegrable hu]
      with x hx
    exact hx.comp mollifierScale_tendsto
  obtain ⟨v, hv, hvu, hvd⟩ := exists_c1_representative_of_ae_limit f df A u hA hdf hdfu hfu
  refine ⟨v, hv, hvu, fun x j => ?_⟩
  rw [(hvd x).fderiv]
  exact gradientMap_apply_basis (G x) j

/-- Continuous representatives of the same measurable class agree on open
overlaps, hence glue along a countable open cover. -/
theorem exists_continuous_representative_of_open_cover
    {d : ℕ} (g : Vec d → Vec d) (U : ℕ → Set (Vec d))
    (hU : ∀ n, IsOpen (U n)) (hcover : ∀ x, ∃ n, x ∈ U n)
    (hlocal : ∀ n, ∃ G : Vec d → Vec d, ContinuousOn G (U n) ∧
      G =ᵐ[volume.restrict (U n)] g) :
    ∃ G : Vec d → Vec d, Continuous G ∧ G =ᵐ[volume] g := by
  classical
  choose G hGc hGe using hlocal
  choose k hk using hcover
  have hover (n m : ℕ) : Set.EqOn (G n) (G m) (U n ∩ U m) := by
    have hn : G n =ᵐ[volume.restrict (U n ∩ U m)] g :=
      ae_restrict_of_ae_restrict_of_subset inter_subset_left (hGe n)
    have hm : G m =ᵐ[volume.restrict (U n ∩ U m)] g :=
      ae_restrict_of_ae_restrict_of_subset inter_subset_right (hGe m)
    exact MeasureTheory.Measure.eqOn_open_of_ae_eq (hn.trans hm.symm)
      ((hU n).inter (hU m))
      ((hGc n).mono inter_subset_left) ((hGc m).mono inter_subset_right)
  let H : Vec d → Vec d := fun x => G (k x) x
  have heq (n : ℕ) : Set.EqOn H (G n) (U n) := by
    intro x hx
    exact hover (k x) n ⟨hk x, hx⟩
  have hc (n : ℕ) : ContinuousOn H (U n) := (hGc n).congr (heq n)
  refine ⟨H, continuous_iff_continuousAt.mpr (fun x =>
    (hc (k x)).continuousAt ((hU (k x)).mem_nhds (hk x))), ?_⟩
  have hall : ∀ᵐ x ∂(volume : Measure (Vec d)), ∀ n, x ∈ U n → G n x = g x :=
    ae_all_iff.mpr fun n => (ae_restrict_iff' (hU n).measurableSet).mp (hGe n)
  filter_upwards [hall] with x hx
  exact hx (k x) (hk x)

/-- Changing a weak gradient on a null set preserves the literal potential
and yields a classical representative once that gradient is continuous. -/
theorem exists_c1_representative_of_source_continuous_gradient
    {d : ℕ} (hd : 0 < d) {u : Vec d → ℝ} {g G : Vec d → Vec d}
    (hw : HasWeakGradient Set.univ u g) (hG : Continuous G)
    (heq : G =ᵐ[(volume : Measure (Vec d))] g) :
    ∃ v : Vec d → ℝ, ContDiff ℝ (1 : ℕ∞) v ∧
      v =ᵐ[(volume : Measure (Vec d))] u ∧
      ∀ᵐ x ∂(volume : Measure (Vec d)), ∀ j : Fin d,
        fderiv ℝ v x (unitVector j) = g x j := by
  have hu : LocallyIntegrable u volume :=
    locallyIntegrableOn_univ.mp (hw ⟨0, hd⟩).1
  have hwG : PDE.HasWeakGradientOn Set.univ u G := by
    intro j ψ hψ hc hs
    have h := (hw j).2.2 ψ ⟨hψ, hc, hs⟩
    simp only [Measure.restrict_univ] at h ⊢
    change (∫ x, u x * fderiv ℝ ψ x (PDE.basisVec j)) =
      -(∫ x, G x j * ψ x)
    change (∫ x, u x * fderiv ℝ ψ x (PDE.basisVec j)) =
      -(∫ x, g x j * ψ x) at h
    rw [h]
    congr 1
    apply integral_congr_ae
    filter_upwards [heq] with x hx
    rw [hx]
  obtain ⟨v, hv, hvu, hvd⟩ :=
    exists_c1_representative_of_continuous_weakGradient hu hG hwG
  refine ⟨v, hv, hvu, ?_⟩
  filter_upwards [heq] with x hx j
  exact (hvd x j).trans (congrFun hx j)

/-- AKM's symmetric quadratic bounds imply the library's inverse-coercivity
convention for the same matrix, without replacing its anisotropy. -/
theorem coefficient_isEllipticMatrix {d : ℕ} {K : ℝ}
    (a : Coefficient d K) (x : Vec d) :
    PDE.IsEllipticMatrix 1 (max 1 K) (a x) := by
  let Λ := max 1 K
  have hΛ : 1 ≤ Λ := le_max_left _ _
  have hΛ0 : 0 < Λ := zero_lt_one.trans_le hΛ
  have hlo (ξ : Vec d) : PDE.vecNormSq ξ ≤ PDE.vecDot ξ (PDE.matVecMul (a x) ξ) :=
    (a.elliptic x ξ).1
  have hup (ξ : Vec d) :
      PDE.vecDot ξ (PDE.matVecMul (a x) ξ) ≤ Λ * PDE.vecNormSq ξ :=
    ((a.elliptic x ξ).2).trans
      (mul_le_mul_of_nonneg_right (le_max_right 1 K) (PDE.vecNormSq_nonneg ξ))
  have hs : EinsteinFull.S5Elliptic (a x) Λ := by
    refine ⟨hΛ, ?_, ?_, ?_⟩
    · intro j k
      exact (congrFun (congrFun (a.symmetric x) j) k).symm
    · intro ξ
      rw [EinsteinFull.ParabolicBridge.s5Bil_eq_vecDot, ← PDE.vecNormSq_eq_sum_sq]
      exact (mul_le_mul_of_nonneg_right (inv_le_one_of_one_le₀ hΛ)
        (PDE.vecNormSq_nonneg ξ)).trans (by simpa only [one_mul] using hlo ξ)
    · intro ξ
      rw [EinsteinFull.ParabolicBridge.s5Bil_eq_vecDot, ← PDE.vecNormSq_eq_sum_sq]
      exact hup ξ
  have hinj : Function.Injective (a x).mulVec := by
    intro ξ η heq
    have hz : (a x).mulVec (ξ - η) = 0 := by rw [Matrix.mulVec_sub, heq, sub_self]
    have h := hlo (ξ - η)
    change PDE.vecNormSq (ξ - η) ≤ PDE.vecDot (ξ - η) ((a x).mulVec (ξ - η)) at h
    rw [hz] at h
    have hzero : PDE.vecNormSq (ξ - η) = 0 :=
      le_antisymm (by simpa only [PDE.vecDot, Pi.zero_apply, mul_zero,
        Finset.sum_const_zero] using h) (PDE.vecNormSq_nonneg _)
    exact sub_eq_zero.mp (PDE.vecNormSq_eq_zero hzero)
  have hdet : IsUnit (a x).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (Matrix.mulVec_injective_iff_isUnit.mp hinj)
  refine ⟨one_pos, hΛ, ?_, ?_⟩
  · intro ξ
    simpa only [one_mul] using hlo ξ
  · intro ξ
    let η := (a x)⁻¹.mulVec ξ
    have hAη : (a x).mulVec η = ξ := by
      dsimp only [η]
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
    have hcross : EinsteinFull.s5Bil (a x) ξ η = PDE.vecNormSq ξ := by
      rw [EinsteinFull.ParabolicBridge.s5Bil_eq_vecDot]
      change PDE.vecDot ξ ((a x).mulVec η) = _
      rw [hAη]
      rfl
    have hη : EinsteinFull.s5Bil (a x) η η =
        PDE.vecDot ξ (PDE.matVecMul (a x)⁻¹ ξ) := by
      rw [EinsteinFull.ParabolicBridge.s5Bil_eq_vecDot]
      change PDE.vecDot η ((a x).mulVec η) = PDE.vecDot ξ η
      rw [hAη, PDE.vecDot_comm]
    have hcs := EinsteinFull.s5Bil_sq_le hs ξ η
    have hupper : EinsteinFull.s5Bil (a x) ξ ξ ≤ Λ * PDE.vecNormSq ξ := by
      rw [EinsteinFull.ParabolicBridge.s5Bil_eq_vecDot]
      exact hup ξ
    have hηnonneg := EinsteinFull.s5Bil_self_nonneg hs η
    rw [hcross] at hcs
    have hbound := hcs.trans (mul_le_mul_of_nonneg_right hupper hηnonneg)
    rw [← hη]
    by_cases hz : PDE.vecNormSq ξ = 0
    · simpa only [hz, mul_zero] using hηnonneg
    · have hp : 0 < PDE.vecNormSq ξ :=
        lt_of_le_of_ne (PDE.vecNormSq_nonneg ξ) (Ne.symm hz)
      rw [inv_mul_le_iff₀ hΛ0]
      nlinarith only [hbound, hp]

/-- Smooth variable coefficients and smooth affine forcing produce a continuous
representative of the chosen weak gradient on the interior half ball. The
Schauder scale is chosen internally from the actual coefficient seminorm. -/
theorem exists_continuous_gradient_halfBall
    {d : ℕ} (hd : 0 < d) {Λ : ℝ}
    (a : PDE.CoeffField d) (F : Vec d → Vec d)
    (ha : ∀ j k, ContDiff ℝ (⊤ : ℕ∞) (fun x => a x j k))
    (hF : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (fun x => F x j))
    (hell : ∀ x ∈ PDE.euclideanBall (0 : Vec d) 1,
      PDE.IsEllipticMatrix 1 Λ (a x))
    (u : PDE.H1Function (PDE.euclideanBall (0 : Vec d) 1))
    (hu : PDE.IsWeakDivergenceFormSolutionOn a
      (PDE.euclideanBall (0 : Vec d) 1) u 0 F) :
    ∃ G : Vec d → Vec d,
      ContinuousOn G (PDE.euclideanBall (0 : Vec d) (1 / 2)) ∧
      G =ᵐ[PDE.volumeOn (PDE.euclideanBall (0 : Vec d) (1 / 2))] u.grad := by
  obtain ⟨C, hC, hs⟩ := PDE.SchauderC1Proof.result hd (Λ := Λ)
  obtain ⟨M, hM, ham⟩ :=
    PDE.exists_euclideanMatrixHolderSeminormLE_half_of_contDiff ha
  obtain ⟨B, hB, hfb⟩ :=
    PDE.exists_euclideanFieldHolderSeminormLE_half_of_contDiff hF
  obtain ⟨ε, hε, hεfour, hsmall⟩ :=
    EinsteinFull.exists_schauder_half_scale C M hC hM
  let ha' : ∃ K : ℝ, 0 ≤ K ∧ PDE.EuclideanMatrixHolderSeminormLE
      (PDE.euclideanBall (0 : Vec d) 1) a (1 / 2) K := ⟨M, hM, ham⟩
  let hF' : ∃ K : ℝ, 0 ≤ K ∧ PDE.EuclideanFieldHolderSeminormLE
      (PDE.euclideanBall (0 : Vec d) 1) F (1 / 2) K := ⟨B, hB, hfb⟩
  have hsmall' : ε ^ (1 / 2 : ℝ) * PDE.euclideanMatrixHolderSeminormOn
      (PDE.euclideanBall (0 : Vec d) 1) a (1 / 2) ha' ≤
      C⁻¹ * (1 / 2) * (1 - 1 / 2) :=
    (mul_le_mul_of_nonneg_left (PDE.euclideanMatrixHolderSeminormOn_le ha' hM ham)
      (Real.rpow_nonneg hε.le _)).trans hsmall
  obtain ⟨G, hG, _, heq, _⟩ := hs
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
    hε hεfour a F hell ha' hF' hsmall' u hu
  obtain ⟨K, hK, hgk⟩ := hG
  exact ⟨G, hgk.continuousOn (by norm_num) hK, heq⟩

/-- Rescale a smooth variable-coefficient harmonic equation on any centered
ball to the checked half-unit-ball gradient estimate. -/
theorem exists_continuous_harmonic_gradient_ball
    {d : ℕ} (hd : 0 < d) {Λ R : ℝ} (hR : 0 < R)
    (a : PDE.CoeffField d)
    (ha : ∀ j k, ContDiff ℝ (⊤ : ℕ∞) (fun x => a x j k))
    (hell : ∀ x ∈ PDE.euclideanBall (0 : Vec d) R,
      PDE.IsEllipticMatrix 1 Λ (a x))
    (u : PDE.H1Function (PDE.euclideanBall (0 : Vec d) R))
    (hu : PDE.IsWeakDivergenceFormSolutionOn a
      (PDE.euclideanBall (0 : Vec d) R) u 0 0) :
    ∃ G : Vec d → Vec d,
      ContinuousOn G (PDE.euclideanBall (0 : Vec d) (R * (1 / 2))) ∧
      G =ᵐ[PDE.volumeOn (PDE.euclideanBall (0 : Vec d) (R * (1 / 2)))] u.grad := by
  let v := R⁻¹ • PDE.DGNM.blowUp u 0 hR (Set.Subset.refl _)
  have hv (y : Vec d) : v.grad y = u.grad (R • y) := by
    simp only [v, PDE.H1Function.smul_grad, PDE.DGNM.blowUp_grad,
      add_zero, smul_smul, inv_mul_cancel₀ hR.ne', one_smul]
  have hvs := PDE.DGNM.solutionOn_smul
    (PDE.DGNM.solutionOn_blowUp (PDE.isOpen_euclideanBall 0 R)
      hu 0 hR (Set.Subset.refl _)) R⁻¹
  have has (j k : Fin d) : ContDiff ℝ (⊤ : ℕ∞)
      (fun y => PDE.DGNM.blowUpCoeff a 0 R y j k) := by
    exact (ha j k).comp (contDiff_id.const_smul R |>.add contDiff_const)
  obtain ⟨G₀, hG₀, heq⟩ := exists_continuous_gradient_halfBall hd
    (PDE.DGNM.blowUpCoeff a 0 R) 0 has (fun _ => contDiff_const)
    (PDE.DGNM.blowUpCoeff_elliptic hell 0 hR (Set.Subset.refl _)) v hvs
  refine ⟨fun x => G₀ (R⁻¹ • x), ?_, ?_⟩
  · apply hG₀.comp ((continuous_id.const_smul R⁻¹).continuousOn)
    intro x hx
    apply (PDE.DGNM.affineScale_mem_euclideanBall_iff 0 hR (1 / 2)
      (R⁻¹ • x)).mp
    simpa only [smul_smul, mul_inv_cancel₀ hR.ne', one_smul, add_zero] using hx
  · apply (PDE.DGNM.ae_comp_affineScale_ball_iff 0 hR (1 / 2)).mp
    filter_upwards [heq] with y hy
    simpa only [hv, add_zero, smul_smul, inv_mul_cancel₀ hR.ne', one_smul] using hy

/-- Restrict a literal spatial potential and its literal weak gradient to a
bounded ball without selecting another representative. -/
def sourceH1 {d : ℕ} {U : Set (Vec d)}
    {u : Vec d → ℝ} {g : Vec d → Vec d}
    (hu : MemLp u 2 (volume.restrict U))
    (hg : MemLp g 2 (volume.restrict U))
    (hw : HasWeakGradient Set.univ u g) : PDE.H1Function U where
  toFun := u
  grad := g
  memL2 := hu
  gradMemL2 := fun j => hg.continuousLinearMap_comp
    (ContinuousLinearMap.proj j : Vec d →L[ℝ] ℝ)
  hasWeakGradient := by
    have h := Correctors.hasWeakGradient_mono (Set.subset_univ U) hw
    intro j ψ hψ hc hs
    exact (h j).2.2 ψ ⟨hψ, hc, hs⟩

/-- The corrector equation retains the affine flux as the literal smooth
divergence forcing, with both flux integrals certified before splitting. -/
theorem sourceH1_isSolution
    {d : ℕ} {Λ : ℝ} (a : Vec d → Mat d) (e : Vec d)
    (ha : ∀ j k, ContDiff ℝ (⊤ : ℕ∞) (fun x => a x j k))
    (hell : ∀ x ∈ PDE.euclideanBall (0 : Vec d) 1,
      PDE.IsEllipticMatrix 1 Λ (a x))
    {u : Vec d → ℝ} {g : Vec d → Vec d}
    (hu : MemLp u 2 (volume.restrict (PDE.euclideanBall (0 : Vec d) 1)))
    (hg : MemLp g 2 (volume.restrict (PDE.euclideanBall (0 : Vec d) 1)))
    (hw : HasWeakGradient Set.univ u g)
    (he : HasWeakDivergence Set.univ
      (fun x => (a x).mulVec (e + g x)) (fun _ => 0)) :
    PDE.IsWeakDivergenceFormSolutionOn a
      (PDE.euclideanBall (0 : Vec d) 1) (sourceH1 hu hg hw) 0
      (fun x => (a x).mulVec e) := by
  classical
  have hf (j : Fin d) : ContDiff ℝ (⊤ : ℕ∞)
      (fun x => (a x).mulVec e j) := by
    change ContDiff ℝ (⊤ : ℕ∞) (fun x => ∑ k, a x j k * e k)
    exact ContDiff.sum fun k _ => (ha j k).mul contDiff_const
  have hfl : PDE.MemVectorL2On (PDE.euclideanBall (0 : Vec d) 1)
      (fun x => (a x).mulVec e) := by
    intro j
    exact (PDE.H1Function.ofContDiffOnIsOpenBoundedConvexDomain
      (PDE.isOpenBoundedConvexDomain_euclideanBall (0 : Vec d) (by norm_num))
      ((hf j).of_le (by simp))).memL2
  have hell' : PDE.IsEllipticFieldOn 1 Λ (PDE.euclideanBall (0 : Vec d) 1) a := by
    refine ⟨?_, hell⟩
    apply Measurable.of_eval
    intro j
    apply Measurable.of_eval
    intro k
    exact Measurable.ite (PDE.isOpen_euclideanBall (0 : Vec d) 1).measurableSet
      (ha j k).continuous.measurable measurable_const
  have hdata : PDE.DivergenceFormL2DataOn a
      (PDE.euclideanBall (0 : Vec d) 1) (sourceH1 hu hg hw) 0
      (fun x => (a x).mulVec e) :=
    PDE.DivergenceFormL2DataOn.of_isEllipticFieldOn hell' MemLp.zero hfl
  intro ψ
  have ht := hdata.testable ψ
  refine ⟨ht, ?_⟩
  have he' := Correctors.hasWeakDivergence_mono
    (Set.subset_univ (PDE.euclideanBall (0 : Vec d) 1)) he
  have heq := he'.2.2 ψ.toFun ⟨ψ.contDiff, ψ.hasCompactSupport, ψ.tsupport_subset⟩
  have hpoint (x : Vec d) :
      dot ((a x).mulVec (e + g x)) (gradient ψ.toFun x) =
        PDE.vecDot (PDE.matVecMul (a x) ((sourceH1 hu hg hw).grad x)) (ψ.grad x) +
        PDE.vecDot ((a x).mulVec e) (ψ.grad x) := by
    simp only [dot, gradient, coordinateDerivative,
      PDE.vecDot, PDE.matVecMul, PDE.WeakTestFunction.grad,
      PDE.WeakTestFunction.partialDeriv, PDE.basisVec, unitVector,
      sourceH1, Matrix.mulVec, dotProduct, Pi.add_apply, mul_add,
      Finset.sum_add_distrib, add_mul]
    ring
  simp only [zero_mul, integral_zero, neg_zero] at heq
  simp_rw [hpoint] at heq
  rw [integral_add ht.flux_integrable ht.forcing_integrable] at heq
  simp only [Pi.zero_apply, zero_mul, integral_zero, zero_sub]
  linarith only [heq]

/-- Local continuous representative of the literal corrector gradient. The
potential is used through its actual Sobolev class and harmonic flux equation. -/
theorem exists_continuous_source_gradient_halfBall
    {d : ℕ} (hd : 0 < d) {Λ : ℝ} (a : Vec d → Mat d) (e : Vec d)
    (ha : ∀ j k, ContDiff ℝ (⊤ : ℕ∞) (fun x => a x j k))
    (hell : ∀ x ∈ PDE.euclideanBall (0 : Vec d) 1,
      PDE.IsEllipticMatrix 1 Λ (a x))
    {u : Vec d → ℝ} {g : Vec d → Vec d}
    (hu : MemLp u 2 (volume.restrict (PDE.euclideanBall (0 : Vec d) 1)))
    (hg : MemLp g 2 (volume.restrict (PDE.euclideanBall (0 : Vec d) 1)))
    (hw : HasWeakGradient Set.univ u g)
    (he : HasWeakDivergence Set.univ
      (fun x => (a x).mulVec (e + g x)) (fun _ => 0)) :
    ∃ G : Vec d → Vec d,
      ContinuousOn G (PDE.euclideanBall (0 : Vec d) (1 / 2)) ∧
      G =ᵐ[PDE.volumeOn (PDE.euclideanBall (0 : Vec d) (1 / 2))] g := by
  apply exists_continuous_gradient_halfBall hd a (fun x => (a x).mulVec e) ha
    (fun j => ?_) hell (sourceH1 hu hg hw) (sourceH1_isSolution a e ha hell hu hg hw he)
  change ContDiff ℝ (⊤ : ℕ∞) (fun x => ∑ k, a x j k * e k)
  exact ContDiff.sum fun k _ => (ha j k).mul contDiff_const

/-- The affine corrector is harmonic on every centered ball. Subtracting its
constant affine gradient retains the original potential's weak-gradient class. -/
theorem exists_continuous_source_gradient_ball
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
    ∃ G : Vec d → Vec d,
      ContinuousOn G (PDE.euclideanBall (0 : Vec d) (R * (1 / 2))) ∧
      G =ᵐ[PDE.volumeOn (PDE.euclideanBall (0 : Vec d) (R * (1 / 2)))] g := by
  have hball : PDE.euclideanBall (0 : Vec d) R = ball 0 R := by
    ext x
    exact PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hR
  have hw' := Correctors.hasWeakGradient_mono (Set.subset_univ (ball 0 R)) hw
  have he' := Correctors.hasWeakDivergence_mono (Set.subset_univ (ball 0 R)) he
  have hsol := Correctors.affine_weakSolution_on_ball_of_weakPotential
    (0 : Vec d) R hR i a u g 0 (by simpa using hu) hg (by simpa using hw') he'
  rw [← hball] at hsol
  obtain ⟨G, hG, heq⟩ := exists_continuous_harmonic_gradient_ball hd hR a ha hell
    (EinsteinFull.pdeH1OfSpatialWeakSolution hsol)
    (EinsteinFull.pdeH1OfSpatialWeakSolution_isSolution hsol)
  refine ⟨fun x => G x - unitVector i, hG.sub continuousOn_const, ?_⟩
  filter_upwards [heq] with x hx
  change G x = unitVector i + g x at hx
  rw [hx]
  abel

/-- Physical dilation and scalar normalization preserve smoothness of each
entry of the actual projected coefficient. -/
theorem project_smooth
    {d : ℕ} {L r₀ : ℝ} (hL : 1 ≤ L)
    (ω : PhysicalField d L) (hω : IsSmoothFieldPair ω.1) (j k : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => project (r₀ := r₀) hL ω x j k) := by
  change ContDiff ℝ (⊤ : ℕ∞) (fun x =>
    ellipticityScale L * (Real.exp (-2 * ω.1.2 (r₀ • x)) * ω.1.1 (r₀ • x) j k))
  have hr : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec d => r₀ • x) :=
    contDiff_id.const_smul r₀
  exact contDiff_const.mul
    ((contDiff_const.mul (hω.2.comp hr)).exp.mul ((hω.1 j k).comp hr))

/-- The actual source corrector has a continuous weak-gradient representative
locally. No extra regularity of its potential or gradient is assumed. -/
theorem source_corrector_continuous_gradient_halfBall
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q) (i : Fin d)
    (φ : Corrector (actualCoefficientLaw Q) (Correctors.correctorUnitVector i).ofLp) :
    ∀ᵐ ω ∂physicalReferenceLaw Q, ∃ G : Vec d → Vec d,
      ContinuousOn G (PDE.euclideanBall (0 : Vec d) (1 / 2)) ∧
      G =ᵐ[PDE.volumeOn (PDE.euclideanBall (0 : Vec d) (1 / 2))]
        φ.grad (project (r₀ := D.dependenceRange) Q.ellipticity_parameter ω) := by
  have hw := ae_of_ae_map
    (measurable_project (r₀ := D.dependenceRange) Q.ellipticity_parameter).aemeasurable
    φ.weak_gradient
  have he := ae_of_ae_map
    (measurable_project (r₀ := D.dependenceRange) Q.ellipticity_parameter).aemeasurable
    φ.harmonic
  have hl := ae_of_ae_map
    (measurable_project (r₀ := D.dependenceRange) Q.ellipticity_parameter).aemeasurable
    φ.locally_square_integrable
  have hs : ∀ᵐ ω ∂physicalReferenceLaw Q, IsSmoothFieldPair ω.1 := by
    have h := hQ.mono fun _ hω => hω.1
    rw [← physicalReferenceLaw_forget Q] at h
    exact ae_of_ae_map measurable_subtype_coe.aemeasurable h
  filter_upwards [hw, he, hl, hs] with ω hwω heω hlω hsω
  have hball : PDE.euclideanBall (0 : Vec d) 1 = ball 0 1 := by
    ext x
    exact PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)
  obtain ⟨hu, hg⟩ := hlω 1 (by norm_num)
  rw [← hball] at hu hg
  exact exists_continuous_source_gradient_halfBall (by omega)
    (project (r₀ := D.dependenceRange) Q.ellipticity_parameter ω)
    (Correctors.correctorUnitVector i).ofLp
    (project_smooth Q.ellipticity_parameter ω hsω)
    (fun x _ => coefficient_isEllipticMatrix _ x) hu hg hwω heω

/-- Exhausting physical space by centered balls produces a continuous
representative of the actual source corrector gradient. -/
theorem source_corrector_continuous_gradient
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q) (i : Fin d)
    (φ : Corrector (actualCoefficientLaw Q) (Correctors.correctorUnitVector i).ofLp) :
    ∀ᵐ ω ∂physicalReferenceLaw Q, ∃ G : Vec d → Vec d,
      Continuous G ∧ G =ᵐ[(volume : Measure (Vec d))]
        φ.grad (project (r₀ := D.dependenceRange) Q.ellipticity_parameter ω) := by
  have hw := ae_of_ae_map
    (measurable_project (r₀ := D.dependenceRange) Q.ellipticity_parameter).aemeasurable
    φ.weak_gradient
  have he := ae_of_ae_map
    (measurable_project (r₀ := D.dependenceRange) Q.ellipticity_parameter).aemeasurable
    φ.harmonic
  have hl := ae_of_ae_map
    (measurable_project (r₀ := D.dependenceRange) Q.ellipticity_parameter).aemeasurable
    φ.locally_square_integrable
  have hs : ∀ᵐ ω ∂physicalReferenceLaw Q, IsSmoothFieldPair ω.1 := by
    have h := hQ.mono fun _ hω => hω.1
    rw [← physicalReferenceLaw_forget Q] at h
    exact ae_of_ae_map measurable_subtype_coe.aemeasurable h
  filter_upwards [hw, he, hl, hs] with ω hwω heω hlω hsω
  apply exists_continuous_representative_of_open_cover
    (φ.grad (project (r₀ := D.dependenceRange) Q.ellipticity_parameter ω))
    (fun n => PDE.euclideanBall (0 : Vec d) (n + 1 : ℝ))
    (fun n => PDE.isOpen_euclideanBall _ _)
  · intro x
    obtain ⟨n, hn⟩ := exists_nat_gt (PDE.vecEuclideanNorm x)
    refine ⟨n, ?_⟩
    apply (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)).mpr
    simpa only [sub_zero] using hn.trans (by norm_num : (n : ℝ) < n + 1)
  · intro n
    have hR : (0 : ℝ) < 2 * (n + 1 : ℝ) := by positivity
    obtain ⟨hu, hg⟩ := hlω _ hR
    obtain ⟨G, hG, heq⟩ := exists_continuous_source_gradient_ball (by omega) hR
      (project (r₀ := D.dependenceRange) Q.ellipticity_parameter ω) i
      (project_smooth Q.ellipticity_parameter ω hsω)
      (fun x _ => coefficient_isEllipticMatrix _ x) hu hg hwω heω
    have hr : 2 * (n + 1 : ℝ) * (1 / 2) = n + 1 := by ring
    rw [hr] at hG heq
    exact ⟨G, hG, heq⟩

end C3SublinearC1

/-- A C¹ representative of the literal source potential, with its actual
corrector gradient, under the physical environment law. -/
theorem sublinear_source_corrector_c1_representative
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q) (i : Fin d)
    (φ : Corrector (actualCoefficientLaw Q) (Correctors.correctorUnitVector i).ofLp) :
    ∀ᵐ ω ∂physicalReferenceLaw Q, ∃ v : Vec d → ℝ,
      ContDiff ℝ (1 : ℕ∞) v ∧
      v =ᵐ[(volume : Measure (Vec d))]
        (fun x => φ.potential (project (r₀ := D.dependenceRange)
          Q.ellipticity_parameter ω) x) ∧
      ∀ᵐ x ∂(volume : Measure (Vec d)), ∀ j : Fin d,
        fderiv ℝ v x (unitVector j) =
          φ.grad (project (r₀ := D.dependenceRange) Q.ellipticity_parameter ω) x j := by
  have hw := ae_of_ae_map
    (measurable_project (r₀ := D.dependenceRange) Q.ellipticity_parameter).aemeasurable
    φ.weak_gradient
  filter_upwards [hw, C3SublinearC1.source_corrector_continuous_gradient d hd D Q hQ i φ]
    with ω hwω hG
  obtain ⟨G, hGc, hGe⟩ := hG
  exact C3SublinearC1.exists_c1_representative_of_source_continuous_gradient
    (by omega) hwω hGc hGe

-- Exact-type check against the supervisor task statement.
example
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q) (i : Fin d)
    (φ : Corrector (actualCoefficientLaw Q) (Correctors.correctorUnitVector i).ofLp) :
    ∀ᵐ ω ∂physicalReferenceLaw Q, ∃ v : Vec d → ℝ,
      ContDiff ℝ (1 : ℕ∞) v ∧
      v =ᵐ[(volume : Measure (Vec d))]
        (fun x => φ.potential (project (r₀ := D.dependenceRange)
          Q.ellipticity_parameter ω) x) ∧
      ∀ᵐ x ∂(volume : Measure (Vec d)), ∀ j : Fin d,
        fderiv ℝ v x (unitVector j) =
          φ.grad (project (r₀ := D.dependenceRange) Q.ellipticity_parameter ω) x j :=
  sublinear_source_corrector_c1_representative d hd D Q hQ i φ

#print axioms sublinear_source_corrector_c1_representative
#print axioms C3SublinearC1.exists_continuous_gradient_halfBall
#print axioms C3SublinearC1.sourceH1
#print axioms C3SublinearC1.sourceH1_isSolution
#print axioms C3SublinearC1.exists_continuous_source_gradient_halfBall
#print axioms C3SublinearC1.coefficient_isEllipticMatrix
#print axioms C3SublinearC1.project_smooth
#print axioms C3SublinearC1.source_corrector_continuous_gradient_halfBall
#lint

run_cmd do
  let env ← Lean.getEnv
  let mut checked : Nat := 0
  for (n, _) in env.constants.toList do
    if (env.getModuleIdxFor? n).isNone then
      let axs ← Lean.collectAxioms n
      unless axs.all (fun a => #[`propext, `Classical.choice, `Quot.sound].contains a) do
        throwError m!"nonstandard axioms for {n}: {axs}"
      checked := checked + 1
  Lean.logInfo m!"C3 all-owned-and-generated transitive axiom audit passed: {checked} declarations"
end EinsteinFull.Blueprint
