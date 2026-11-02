import EinsteinFull.Blueprint.G2.node_e_u3A_holder_u2D_average
import EinsteinFull.Blueprint.Foundation.node_e_u3A_local_u2D_time
import EinsteinFull.Blueprint.Foundation.node_e_u3A_lp_u2D_growth
import EinsteinFull.Blueprint.Foundation.node_l_u3A_forced_u2D_local_u23_centered_u2D_source
import EinsteinFull.Blueprint.G2.node_e_u3A_holder_u2D_average_u23_unforced_u2D_interior
import EinsteinFull.Blueprint.G2.Proofs.C1HolderAverage
import EinsteinFull.Calculus.C1HolderComparisonSupport
import EinsteinFull.Calculus.C3HolderAverageSupport
import EinsteinFull.Blueprint.G2.Proofs.C3HolderAverage
import EinsteinFull.Calculus.C3AnalyticClockSupport
import EinsteinFull.Calculus.C4PhysicalLocalEnergy
import EinsteinFull.Calculus.ParabolicBridgeCoeff
import EinsteinRelation.Correctors.ScalarSetAverageMoments
import PDEFoundation.Measure.BallVolume
import EinsteinFull.Calculus.C5HolderTranspose
import Mathlib.Algebra.Order.Field.GeomSum
import PDEFoundation.Geometry.EuclideanBall.Interior
import EinsteinFull.Calculus.C1LocalTimeGradientMoment
import EinsteinFull.Calculus.C6HolderLocalGaussianIncrement
import EinsteinFull.Calculus.C6HolderGaussianIncrement
import EinsteinFull.Calculus.C6EndpointPhysicalCylinderApproximation
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinFull
open PDE PDE.Parabolic PDE.Parabolic.Lions

private theorem real_oscillation_comparison_contraction
    {X : Type*} [MeasurableSpace X] {μ ν : Measure X}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {u v : X → ℝ}
    (huμ : MemLp u 2 μ) (hvμ : MemLp v 2 μ)
    (huν : MemLp u 2 ν) (hvν : MemLp v 2 ν) {K : ℝ} (hK : 0 ≤ K)
    (hv : Real.sqrt (⨍ x, |v x - (⨍ y, v y ∂μ)| ^ 2 ∂μ) ≤
      K * Real.sqrt (⨍ x, |v x - (⨍ y, v y ∂ν)| ^ 2 ∂ν)) :
    Real.sqrt (⨍ x, |u x - (⨍ y, u y ∂μ)| ^ 2 ∂μ) ≤
      Real.sqrt (⨍ x, |u x - v x| ^ 2 ∂μ) +
        K * Real.sqrt (⨍ x, |u x - v x| ^ 2 ∂ν) +
        K * Real.sqrt (⨍ x, |u x - (⨍ y, u y ∂ν)| ^ 2 ∂ν) := by
  have hcomp {σ : Measure X} [IsFiniteMeasure σ] {f g : X → ℝ}
      (hf : MemLp f 2 σ) (hg : MemLp g 2 σ) :
      Real.sqrt (⨍ x, |f x - (⨍ y, f y ∂σ)| ^ 2 ∂σ) ≤
        Real.sqrt (⨍ x, |f x - g x| ^ 2 ∂σ) +
          Real.sqrt (⨍ x, |g x - (⨍ y, g y ∂σ)| ^ 2 ∂σ) := by
    have hmean := mul_le_mul_of_nonneg_left
      (ParabolicBridge.integral_sq_sub_average_le σ hf (⨍ y, g y ∂σ))
      (inv_nonneg.mpr (measureReal_nonneg (μ := σ) (s := univ)))
    have htriangle := ParabolicBridge.sqrt_integral_sq_add_le σ
      (hf.sub hg) (hg.sub (memLp_const (⨍ y, g y ∂σ)))
    simp only [Pi.sub_apply, sub_add_sub_cancel] at htriangle
    have hscaled := mul_le_mul_of_nonneg_left htriangle
      (Real.sqrt_nonneg ((σ.real univ)⁻¹))
    calc
      _ ≤ Real.sqrt (⨍ x, |f x - (⨍ y, g y ∂σ)| ^ 2 ∂σ) := by
        apply Real.sqrt_le_sqrt
        simpa only [average_eq, smul_eq_mul, sq_abs] using hmean
      _ ≤ _ := by
        simpa only [average_eq, smul_eq_mul, sq_abs,
          Real.sqrt_mul (inv_nonneg.mpr (measureReal_nonneg)), mul_add] using hscaled
  have hsmall := hcomp huμ hvμ
  have hlarge := hcomp hvν huν
  have hdist (x : X) : |v x - u x| = |u x - v x| := abs_sub_comm _ _
  simp only [hdist] at hlarge
  have htransfer := hv.trans (mul_le_mul_of_nonneg_left hlarge hK)
  linarith only [hsmall, htransfer]

/-- A local forced real field has the interior oscillation estimate supplied by
its genuine caloric replacement. The source error is retained on both scales;
no regularity or boundary trace of the forced field is assumed. -/
theorem holder_forward_real_comparison
    (hinterior : node_e_u3A_holder_u2D_average_u23_unforced_u2D_interiorStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ α C : ℝ, 0 < α ∧ α < 1 ∧ 1 ≤ C ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange),
      HasSmoothBounds D Q → ∀ᵐ ω ∂reducedLaw Q,
    ∀ (τ : ℝ) (x₀ : EinsteinRelation.Vec d) (r lam Lam : ℝ), 0 < r →
      let a : ParCoeffField d := fun z => ω.1 z.1
      let cyl := fun ρ : ℝ =>
        Ioo (τ - ρ ^ 2) τ ×ˢ euclideanBall x₀ ρ
      IsParabolicCoeff lam Lam a univ (Icc (τ - r ^ 2) τ) →
      ∀ (u f : EinsteinRelation.Vec d × ℝ → ℝ) (g : EinsteinRelation.Vec d × ℝ → EinsteinRelation.Vec d),
      MemLp u 2 (volume.restrict (euclideanBall x₀ r ×ˢ Ioo (τ - r ^ 2) τ)) →
      (∀ j, MemLp (fun z => g z j) 2
        (volume.restrict (euclideanBall x₀ r ×ˢ Ioo (τ - r ^ 2) τ))) →
      MemLp f 2 (volume.restrict (euclideanBall x₀ r ×ˢ Ioo (τ - r ^ 2) τ)) →
      (∀ φ : holderComparisonTestSpace d (euclideanBall x₀ r) (τ - r ^ 2) τ,
        ∀ j : Fin d,
        (∫ z in euclideanBall x₀ r ×ˢ Ioo (τ - r ^ 2) τ,
          u z * parSpaceGrad (φ.val : EinsteinRelation.Vec d × ℝ → ℝ) z j) =
          -(∫ z in euclideanBall x₀ r ×ˢ Ioo (τ - r ^ 2) τ,
            g z j * (φ.val : EinsteinRelation.Vec d × ℝ → ℝ) z)) →
      (∀ φ : holderComparisonTestSpace d (euclideanBall x₀ r) (τ - r ^ 2) τ,
        (∫ z in euclideanBall x₀ r ×ˢ Ioo (τ - r ^ 2) τ,
          u z * parTimeDeriv (φ.val : EinsteinRelation.Vec d × ℝ → ℝ) z) =
          (1 / 2 : ℝ) * (∫ z in euclideanBall x₀ r ×ˢ Ioo (τ - r ^ 2) τ,
            vecDot (g z) (matVecMul (matTranspose (a z))
              (parSpaceGrad (φ.val : EinsteinRelation.Vec d × ℝ → ℝ) z))) -
          (∫ z in euclideanBall x₀ r ×ˢ Ioo (τ - r ^ 2) τ,
            f z * (φ.val : EinsteinRelation.Vec d × ℝ → ℝ) z)) →
      ∀ θ : ℝ, 0 < θ → θ ≤ 1 / 2 →
      let B := r ^ 4 * (∫ z in euclideanBall x₀ r ×ˢ Ioo (τ - r ^ 2) τ,
        f z ^ 2) / (lam / 10) ^ 2
      Real.sqrt (⨍ z in cyl (θ * r),
        |u z.swap - (⨍ w in cyl (θ * r), u w.swap)| ^ 2) ≤
        (Real.sqrt ((volume.real (cyl (θ * r)))⁻¹) +
          C * θ ^ α * Real.sqrt ((volume.real (cyl r))⁻¹)) * Real.sqrt B +
          C * θ ^ α * Real.sqrt (⨍ z in cyl r,
            |u z.swap - (⨍ w in cyl r, u w.swap)| ^ 2) := by
  obtain ⟨α, C, hα, hα1, hC, hinterior⟩ := hinterior d hd D
  refine ⟨α, C, hα, hα1, hC, ?_⟩
  intro Q hQ
  filter_upwards [hinterior Q hQ] with ω hω
  intro τ x₀ r lam Lam hr
  dsimp only
  intro ha u f g hu hg hf hgrad hheat θ hθ hθhalf
  let cyl := fun ρ : ℝ => Ioo (τ - ρ ^ 2) τ ×ˢ euclideanBall x₀ ρ
  let B := r ^ 4 * (∫ z in euclideanBall x₀ r ×ˢ Ioo (τ - r ^ 2) τ,
    f z ^ 2) / (lam / 10) ^ 2
  have hsT : τ - r ^ 2 < τ := sub_lt_self _ (sq_pos_of_pos hr)
  obtain ⟨v, hvgrad, hvheat, herror⟩ := holderComparison_local_caloric_replacement
    hsT ha hr (⟨0, by omega⟩ : Fin d) hu hg hf hgrad hheat
  have hv := holderComparison_cylinder_memLp (U := euclideanBall x₀ r) (cauchyJointValue_memLp v)
  have hvG j := holderComparison_cylinder_memLp (U := euclideanBall x₀ r) (cauchyJointGradient_memLp v j)
  have hball (ρ : ℝ) (hρ : 0 < ρ) :
      {y : EinsteinRelation.Vec d | euclideanNorm (y - x₀) < ρ} = euclideanBall x₀ ρ := by
    ext y
    change Real.sqrt (euclideanSq (y - x₀)) < ρ ↔ vecNormSq (y - x₀) < ρ ^ 2
    rw [Real.sqrt_lt' hρ]
    rfl
  have hωr := hω τ x₀ r hr
  dsimp only at hωr
  rw [hball r hr] at hωr
  have hvdecay := hωr (fun z => cauchyJointValue v z.swap)
    (fun j z => cauchyJointGradient v z.swap j) hv hvG
    (fun φ hφ hc hs j => holderComparison_cylinder_weakGradient v hvgrad
      φ (hφ.of_le (by norm_num)) hc hs j)
    (fun φ hφ hc hs => holderComparison_cylinder_heat _ v hvheat
      φ (hφ.of_le (by norm_num)) hc hs) θ hθ hθhalf
  rw [hball (θ * r) (mul_pos hθ hr)] at hvdecay
  have hsub : cyl (θ * r) ⊆ cyl r := by
    have hθr : θ * r ≤ r := mul_le_of_le_one_left hr.le (by linarith)
    have hsq : (θ * r) ^ 2 ≤ r ^ 2 := sq_le_sq₀ (by positivity) hr.le |>.mpr hθr
    intro z hz
    exact ⟨⟨by linarith [hz.1.1], hz.1.2⟩, (euclideanBall_mono (by positivity) hθr) hz.2⟩
  have hu' : MemLp (fun z : ℝ × EinsteinRelation.Vec d => u z.swap) 2 (volume.restrict (cyl r)) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at hu ⊢
    exact hu.comp_measurePreserving Measure.measurePreserving_swap
  have hfinit (ρ : ℝ) (hρ : 0 ≤ ρ) : IsFiniteMeasure (volume.restrict (cyl ρ)) := by
    apply isFiniteMeasure_restrict.mpr
    have hs : cyl ρ ⊆ Icc (τ - ρ ^ 2) τ ×ˢ euclideanClosedBall x₀ ρ :=
      Set.prod_mono Ioo_subset_Icc_self (euclideanBall_subset_euclideanClosedBall x₀ ρ)
    exact ((measure_mono hs).trans_lt
      ((isCompact_Icc.prod (isCompact_euclideanClosedBall x₀ hρ)).measure_lt_top)).ne
  let := hfinit r hr.le
  let := hfinit (θ * r) (by positivity)
  have hμ : volume.restrict (cyl (θ * r)) ≤ volume.restrict (cyl r) :=
    Measure.restrict_mono hsub le_rfl
  have heint : Integrable (fun z : ℝ × EinsteinRelation.Vec d =>
      |u z.swap - cauchyJointValue v z.swap| ^ 2) (volume.restrict (cyl r)) := by
    simpa only [sq_abs, Pi.sub_apply] using (hu'.sub hv).integrable_sq
  have herrsmall : (∫ z in cyl (θ * r),
      |u z.swap - cauchyJointValue v z.swap| ^ 2) ≤ B :=
    (integral_mono_measure hμ (ae_of_all _ fun _ => sq_nonneg _) heint).trans herror
  have hnormerr (ρ : ℝ) (he : (∫ z in cyl ρ,
      |u z.swap - cauchyJointValue v z.swap| ^ 2) ≤ B) :
      Real.sqrt (⨍ z in cyl ρ, |u z.swap - cauchyJointValue v z.swap| ^ 2) ≤
        Real.sqrt ((volume.real (cyl ρ))⁻¹) * Real.sqrt B := by
    rw [average_eq, smul_eq_mul, measureReal_restrict_apply_univ,
      Real.sqrt_mul (inv_nonneg.mpr (measureReal_nonneg))]
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt he) (Real.sqrt_nonneg _)
  have hcomparison := real_oscillation_comparison_contraction
    (hu'.mono_measure hμ) (hv.mono_measure hμ) hu' hv
    (show 0 ≤ C * θ ^ α by positivity) hvdecay
  have hsmall := hnormerr (θ * r) herrsmall
  have hlarge := mul_le_mul_of_nonneg_left (hnormerr r herror)
    (show 0 ≤ C * θ ^ α by positivity)
  change _ ≤ _ at hcomparison
  nlinarith only [hcomparison, hsmall, hlarge]

/-- Real linear projections of the actual complex diffusion pairing retain
its coefficient matrix and the factor one half. Compact tests supply all
absolute integrability needed to pass the projection through the integral. -/
theorem holder_forward_project_diffusion
    {d : ℕ} {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    {μ : Measure X} {a : X → Matrix (Fin d) (Fin d) ℝ}
    (ha : ∀ j k, Continuous (fun z => a z j k))
    {G : Fin d → X → ℂ} (hG : ∀ k, Integrable (G k) μ)
    {q : Fin d → X → ℝ} (hq : ∀ j, Continuous (q j))
    (hc : ∀ j, HasCompactSupport (q j)) (R : ℂ →L[ℝ] ℝ) :
    (∑ j, R (∫ z, ((1 / 2 : ℂ) * ∑ k, (a z j k : ℂ) * G k z) *
      (q j z : ℂ) ∂μ)) =
      (1 / 2 : ℝ) * (∫ z, ∑ j, (∑ k, a z j k * R (G k z)) * q j z ∂μ) := by
  let F := fun j z => ((1 / 2 : ℂ) * ∑ k, (a z j k : ℂ) * G k z) *
    (q j z : ℂ)
  have he (j : Fin d) (z : X) :
      F j z = (1 / 2 : ℝ) • ∑ k, (a z j k * q j z) • G k z := by
    simp only [F, Complex.real_smul, Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_ofNat, Complex.ofReal_mul, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hij (j k : Fin d) : Integrable
      (fun z => (a z j k * q j z) • G k z) μ := by
    simpa only [Complex.real_smul, mul_comm] using
      holderComparison_integrable_mul_compact_real (hG k)
        (q := fun z => a z j k * q j z)
        ((ha j k).mul (hq j)) (by exact (hc j).mul_left)
  have hi (j : Fin d) : Integrable (F j) μ := by
    change Integrable (fun z => F j z) μ
    simp_rw [he]
    exact (integrable_finsetSum _ fun k _ => hij j k).smul (1 / 2 : ℝ)
  have hp (j : Fin d) (z : X) :
      R (F j z) = (1 / 2 : ℝ) * (∑ k, a z j k * R (G k z)) * q j z := by
    rw [he, map_smul, map_sum]
    simp only [map_smul, smul_eq_mul]
    calc
      _ = (1 / 2 : ℝ) * (∑ k, (a z j k * R (G k z)) * q j z) := by
        congr 1
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ = _ := by rw [← Finset.sum_mul]; ring
  calc
    _ = ∑ j, ∫ z, R (F j z) ∂μ := by
      apply Finset.sum_congr rfl
      intro j _
      exact (R.integral_comp_comm (hi j)).symm
    _ = ∫ z, ∑ j, R (F j z) ∂μ :=
      (integral_finsetSum _ fun j _ => R.integrable_comp (hi j)).symm
    _ = _ := by
      simp_rw [hp]
      simp only [mul_assoc, ← Finset.mul_sum, integral_const_mul]

/-- A real projection of the actual complex spatial weak-gradient equation
has precisely the same spatial derivative and the projected gradient. -/
theorem holder_forward_project_local_gradient
    {d : ℕ} {μ : Measure (EinsteinRelation.Vec d × ℝ)}
    {u g : EinsteinRelation.Vec d × ℝ → ℂ}
    (hu : Integrable u μ) (hg : Integrable g μ)
    {φ : EinsteinRelation.Vec d × ℝ → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hc : HasCompactSupport φ) (j : Fin d)
    (hgrad : (∫ z, u z * (parSpaceGrad φ z j : ℂ) ∂μ) =
      -(∫ z, g z * (φ z : ℂ) ∂μ)) (R : ℂ →L[ℝ] ℝ) :
    (∫ z, R (u z) * parSpaceGrad φ z j ∂μ) =
      -(∫ z, R (g z) * φ z ∂μ) := by
  have hd : Continuous (fun z => parSpaceGrad φ z j) :=
    (hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hdc : HasCompactSupport (fun z => parSpaceGrad φ z j) :=
    (hc.fderiv ℝ).comp_left
      (g := fun L : (EinsteinRelation.Vec d × ℝ) →L[ℝ] ℝ => L (basisVec j, 0))
      (by simp)
  rw [holderComparison_project_pairing hu R hd hdc, hgrad, map_neg,
    ← holderComparison_project_pairing hg R hφ.continuous hc]

/-- Project the complex corrected equation to a real forced equation. The
source is projected as well; no unforced equation is substituted for it. -/
theorem holder_forward_project_local_heat
    {d : ℕ} {μ : Measure (EinsteinRelation.Vec d × ℝ)}
    {a : ParCoeffField d} (ha : ∀ j k, Continuous (fun z => a z j k))
    {u S : EinsteinRelation.Vec d × ℝ → ℂ}
    {G : Fin d → EinsteinRelation.Vec d × ℝ → ℂ}
    (hu : Integrable u μ) (hS : Integrable S μ) (hG : ∀ j, Integrable (G j) μ)
    {φ : EinsteinRelation.Vec d × ℝ → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hc : HasCompactSupport φ)
    (hheat : (∫ z, u z * (parTimeDeriv φ z : ℂ) ∂μ) =
      (∑ j, ∫ z, ((1 / 2 : ℂ) * ∑ k, (a z j k : ℂ) * G k z) *
        (parSpaceGrad φ z j : ℂ) ∂μ) + ∫ z, S z * (φ z : ℂ) ∂μ)
    (R : ℂ →L[ℝ] ℝ) :
    (∫ z, R (u z) * parTimeDeriv φ z ∂μ) =
      (1 / 2 : ℝ) * (∫ z, vecDot (fun j => R (G j z))
        (matVecMul (matTranspose (a z)) (parSpaceGrad φ z)) ∂μ) +
      ∫ z, R (S z) * φ z ∂μ := by
  have hd (v : EinsteinRelation.Vec d × ℝ) :
      Continuous (fun z => fderiv ℝ φ z v) :=
    (hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hdc (v : EinsteinRelation.Vec d × ℝ) :
      HasCompactSupport (fun z => fderiv ℝ φ z v) :=
    (hc.fderiv ℝ).comp_left (g := fun L : (EinsteinRelation.Vec d × ℝ) →L[ℝ] ℝ => L v) (by simp)
  unfold parTimeDeriv at hheat ⊢
  rw [holderComparison_project_pairing hu R (hd (0, 1)) (hdc (0, 1)),
    hheat, map_add, map_sum,
    holder_forward_project_diffusion (q := fun j z => parSpaceGrad φ z j) ha hG
      (fun j => hd (basisVec j, 0)) (fun j => hdc (basisVec j, 0)),
    ← holderComparison_project_pairing hS R hφ.continuous hc]
  simp_rw [holderComparison_flux_sum]

private theorem complex_oscillation_of_component_bounds
    {X : Type*} [MeasurableSpace X] {μ ν : Measure X}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {u : X → ℂ}
    (hμ : MemLp u 2 μ) (hν : MemLp u 2 ν) {A B K : ℝ}
    (hK : 0 ≤ K)
    (hre : Real.sqrt (⨍ x, |(u x).re - (⨍ y, (u y).re ∂μ)| ^ 2 ∂μ) ≤
      A * Real.sqrt B + K * Real.sqrt
        (⨍ x, |(u x).re - (⨍ y, (u y).re ∂ν)| ^ 2 ∂ν))
    (him : Real.sqrt (⨍ x, |(u x).im - (⨍ y, (u y).im ∂μ)| ^ 2 ∂μ) ≤
      A * Real.sqrt B + K * Real.sqrt
        (⨍ x, |(u x).im - (⨍ y, (u y).im ∂ν)| ^ 2 ∂ν)) :
    Real.sqrt (⨍ x, ‖u x - (⨍ y, u y ∂μ)‖ ^ 2 ∂μ) ≤
      2 * A * Real.sqrt B + 2 * K *
        Real.sqrt (⨍ x, ‖u x - (⨍ y, u y ∂ν)‖ ^ 2 ∂ν) := by
  have hsum (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
      Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb,
      Real.sq_sqrt (add_nonneg ha hb), Real.sqrt_nonneg a, Real.sqrt_nonneg b]
  have hs : Real.sqrt ((⨍ x, |(u x).re - (⨍ y, (u y).re ∂μ)| ^ 2 ∂μ) +
      (⨍ x, |(u x).im - (⨍ y, (u y).im ∂μ)| ^ 2 ∂μ)) ≤
      Real.sqrt (⨍ x, |(u x).re - (⨍ y, (u y).re ∂μ)| ^ 2 ∂μ) +
      Real.sqrt (⨍ x, |(u x).im - (⨍ y, (u y).im ∂μ)| ^ 2 ∂μ) :=
    hsum _ _ (integral_nonneg fun _ => sq_nonneg _) (integral_nonneg fun _ => sq_nonneg _)
  rw [← holder_complex_oscillation_sq hμ] at hs
  have hr : Real.sqrt (⨍ x, |(u x).re - (⨍ y, (u y).re ∂ν)| ^ 2 ∂ν) ≤
      Real.sqrt (⨍ x, ‖u x - (⨍ y, u y ∂ν)‖ ^ 2 ∂ν) := by
    apply Real.sqrt_le_sqrt
    rw [holder_complex_oscillation_sq hν]
    exact le_add_of_nonneg_right (integral_nonneg fun _ => sq_nonneg _)
  have hi : Real.sqrt (⨍ x, |(u x).im - (⨍ y, (u y).im ∂ν)| ^ 2 ∂ν) ≤
      Real.sqrt (⨍ x, ‖u x - (⨍ y, u y ∂ν)‖ ^ 2 ∂ν) := by
    apply Real.sqrt_le_sqrt
    rw [holder_complex_oscillation_sq hν]
    exact le_add_of_nonneg_left (integral_nonneg fun _ => sq_nonneg _)
  have hr' := mul_le_mul_of_nonneg_left hr hK
  have hi' := mul_le_mul_of_nonneg_left hi hK
  linarith

/-- Actual complex forced weak solutions inherit a sourced oscillation
comparison from the real interior dependency. The source keeps its full
complex L² energy, and the structural exponent is chosen before any Lᵖ index. -/
theorem holder_forward_complex_comparison
    (hinterior : node_e_u3A_holder_u2D_average_u23_unforced_u2D_interiorStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ α C : ℝ, 0 < α ∧ α < 1 ∧ 1 ≤ C ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange),
      HasSmoothBounds D Q → ∀ᵐ ω ∂reducedLaw Q,
    ∀ (τ : ℝ) (x₀ : EinsteinRelation.Vec d) (r lam Lam : ℝ), 0 < r →
      let a : ParCoeffField d := fun z => ω.1 z.1
      let Ω := euclideanBall x₀ r ×ˢ Ioo (τ - r ^ 2) τ
      let cyl := fun ρ : ℝ => Ioo (τ - ρ ^ 2) τ ×ˢ euclideanBall x₀ ρ
      IsParabolicCoeff lam Lam a univ (Icc (τ - r ^ 2) τ) →
      (∀ j k, Continuous (fun z => a z j k)) →
      ∀ (u S : EinsteinRelation.Vec d × ℝ → ℂ)
        (G : Fin d → EinsteinRelation.Vec d × ℝ → ℂ),
      MemLp u 2 (volume.restrict Ω) → (∀ j, MemLp (G j) 2 (volume.restrict Ω)) →
      MemLp S 2 (volume.restrict Ω) →
      (∀ φ : holderComparisonTestSpace d (euclideanBall x₀ r) (τ - r ^ 2) τ,
        ∀ j, (∫ z in Ω, u z * (parSpaceGrad (φ.val : EinsteinRelation.Vec d × ℝ → ℝ) z j : ℂ)) =
          -(∫ z in Ω, G j z * (φ.val : EinsteinRelation.Vec d × ℝ → ℝ) z)) →
      (∀ φ : holderComparisonTestSpace d (euclideanBall x₀ r) (τ - r ^ 2) τ,
        (∫ z in Ω, u z * (parTimeDeriv (φ.val : EinsteinRelation.Vec d × ℝ → ℝ) z : ℂ)) =
          (∑ j, ∫ z in Ω, ((1 / 2 : ℂ) * ∑ k, (a z j k : ℂ) * G k z) *
            (parSpaceGrad (φ.val : EinsteinRelation.Vec d × ℝ → ℝ) z j : ℂ)) +
          ∫ z in Ω, S z * (φ.val : EinsteinRelation.Vec d × ℝ → ℝ) z) →
      ∀ θ : ℝ, 0 < θ → θ ≤ 1 / 2 →
      let B := r ^ 4 * (∫ z in Ω, ‖S z‖ ^ 2) / (lam / 10) ^ 2
      Real.sqrt (⨍ z in cyl (θ * r),
        ‖u z.swap - (⨍ w in cyl (θ * r), u w.swap)‖ ^ 2) ≤
        2 * (Real.sqrt ((volume.real (cyl (θ * r)))⁻¹) +
          C * θ ^ α * Real.sqrt ((volume.real (cyl r))⁻¹)) * Real.sqrt B +
          2 * C * θ ^ α * Real.sqrt (⨍ z in cyl r,
            ‖u z.swap - (⨍ w in cyl r, u w.swap)‖ ^ 2) := by
  obtain ⟨α, C, hα, hα1, hC, hall⟩ := holder_forward_real_comparison hinterior d hd D
  refine ⟨α, C, hα, hα1, hC, ?_⟩
  intro Q hQ
  filter_upwards [hall Q hQ] with ω hω
  intro τ x₀ r lam Lam hr
  dsimp only
  intro ha hac u S G hu hG hS hgrad hheat θ hθ hθhalf
  let Ω := euclideanBall x₀ r ×ˢ Ioo (τ - r ^ 2) τ
  let cyl := fun ρ : ℝ => Ioo (τ - ρ ^ 2) τ ×ˢ euclideanBall x₀ ρ
  have hfinΩ : IsFiniteMeasure (volume.restrict Ω) := by
    apply isFiniteMeasure_restrict.mpr
    exact ((measure_mono (Set.prod_mono
      (euclideanBall_subset_euclideanClosedBall x₀ r) Ioo_subset_Icc_self)).trans_lt
      (((isCompact_euclideanClosedBall x₀ hr.le).prod isCompact_Icc).measure_lt_top)).ne
  let := hfinΩ
  have hu1 := hu.integrable (by norm_num)
  have hS1 := hS.integrable (by norm_num)
  have hG1 j := (hG j).integrable (by norm_num)
  have hgradR (R : ℂ →L[ℝ] ℝ)
      (φ : holderComparisonTestSpace d (euclideanBall x₀ r) (τ - r ^ 2) τ) j := holder_forward_project_local_gradient
    hu1 (hG1 j) φ.val.property.1 φ.val.property.2.1 j (hgrad φ j) R
  have hheatR (R : ℂ →L[ℝ] ℝ)
      (φ : holderComparisonTestSpace d (euclideanBall x₀ r) (τ - r ^ 2) τ) := holder_forward_project_local_heat
    hac hu1 hS1 hG1 φ.val.property.1 φ.val.property.2.1 (hheat φ) R
  have hrealheat (φ : holderComparisonTestSpace d (euclideanBall x₀ r) (τ - r ^ 2) τ) :
      (∫ z in Ω, (u z).re * parTimeDeriv (φ.val : EinsteinRelation.Vec d × ℝ → ℝ) z) =
        (1 / 2 : ℝ) * (∫ z in Ω, vecDot (fun j => (G j z).re)
          (matVecMul (matTranspose (ω.1 z.1))
            (parSpaceGrad (φ.val : EinsteinRelation.Vec d × ℝ → ℝ) z))) -
          ∫ z in Ω, -(S z).re * (φ.val : EinsteinRelation.Vec d × ℝ → ℝ) z := by
    simpa only [Complex.reCLM_apply, neg_mul, integral_neg, sub_neg_eq_add] using
      hheatR Complex.reCLM φ
  have himagheat (φ : holderComparisonTestSpace d (euclideanBall x₀ r) (τ - r ^ 2) τ) :
      (∫ z in Ω, (u z).im * parTimeDeriv (φ.val : EinsteinRelation.Vec d × ℝ → ℝ) z) =
        (1 / 2 : ℝ) * (∫ z in Ω, vecDot (fun j => (G j z).im)
          (matVecMul (matTranspose (ω.1 z.1))
            (parSpaceGrad (φ.val : EinsteinRelation.Vec d × ℝ → ℝ) z))) -
          ∫ z in Ω, -(S z).im * (φ.val : EinsteinRelation.Vec d × ℝ → ℝ) z := by
    simpa only [Complex.imCLM_apply, neg_mul, integral_neg, sub_neg_eq_add] using
      hheatR Complex.imCLM φ
  have hre := hω τ x₀ r lam Lam hr ha (fun z => (u z).re) (fun z => -(S z).re)
    (fun z j => (G j z).re) hu.re (fun j => (hG j).re) hS.re.neg
    (hgradR Complex.reCLM) hrealheat θ hθ hθhalf
  have him := hω τ x₀ r lam Lam hr ha (fun z => (u z).im) (fun z => -(S z).im)
    (fun z j => (G j z).im) hu.im (fun j => (hG j).im) hS.im.neg
    (hgradR Complex.imCLM) himagheat θ hθ hθhalf
  dsimp only at hre him
  have hsource (R : ℂ → ℝ) (hR : ∀ z, |R z| ≤ ‖z‖)
      (hRI : Integrable (fun z => R (S z) ^ 2) (volume.restrict Ω)) :
      Real.sqrt (r ^ 4 * (∫ z in Ω, (-R (S z)) ^ 2) / (lam / 10) ^ 2) ≤
        Real.sqrt (r ^ 4 * (∫ z in Ω, ‖S z‖ ^ 2) / (lam / 10) ^ 2) := by
    apply Real.sqrt_le_sqrt
    apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    simp only [neg_sq]
    apply integral_mono hRI ((memLp_two_iff_integrable_sq_norm hS.aestronglyMeasurable).mp hS)
    intro z
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mpr (hR (S z))
  have hrS := hsource Complex.re Complex.abs_re_le_norm hS.re.integrable_sq
  have hiS := hsource Complex.im Complex.abs_im_le_norm hS.im.integrable_sq
  have hA : 0 ≤ Real.sqrt ((volume.real (cyl (θ * r)))⁻¹) +
      C * θ ^ α * Real.sqrt ((volume.real (cyl r))⁻¹) := by positivity
  have hre' := hre.trans (add_le_add (mul_le_mul_of_nonneg_left hrS hA) le_rfl)
  have him' := him.trans (add_le_add (mul_le_mul_of_nonneg_left hiS hA) le_rfl)
  have hθr : θ * r ≤ r := mul_le_of_le_one_left hr.le (by linarith)
  have hsub : cyl (θ * r) ⊆ cyl r := by
    have hs := (sq_le_sq₀ (mul_pos hθ hr).le hr.le).mpr hθr
    exact Set.prod_mono (fun s hs' => ⟨by linarith [hs'.1], hs'.2⟩)
      (euclideanBall_mono (mul_pos hθ hr).le hθr)
  have hu' : MemLp (fun z : ℝ × EinsteinRelation.Vec d => u z.swap) 2 (volume.restrict (cyl r)) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at hu ⊢
    exact hu.comp_measurePreserving Measure.measurePreserving_swap
  have hfinit (ρ : ℝ) (hρ : 0 ≤ ρ) : IsFiniteMeasure (volume.restrict (cyl ρ)) := by
    apply isFiniteMeasure_restrict.mpr
    exact ((measure_mono (Set.prod_mono Ioo_subset_Icc_self
      (euclideanBall_subset_euclideanClosedBall x₀ ρ))).trans_lt
      ((isCompact_Icc.prod (isCompact_euclideanClosedBall x₀ hρ)).measure_lt_top)).ne
  let := hfinit r hr.le
  let := hfinit (θ * r) (by positivity)
  have hμ := hu'.mono_measure (Measure.restrict_mono hsub le_rfl)
  simpa only [mul_assoc] using complex_oscillation_of_component_bounds hμ hu'
    (show 0 ≤ C * θ ^ α by positivity) hre' him'

/-- The actual symmetric coefficient satisfies the parabolic library's
inverse-coercivity convention without spatial rescaling. -/
private theorem holder_forward_parabolic_coeff {d : ℕ} {L : ℝ}
    (hL : 1 ≤ L) {ω : FieldPair d}
    (hω : IsElliptic L (fun x => ω.1 x)) (b c : ℝ) :
    IsParabolicCoeff L⁻¹ L (fun z => ω.1 z.1) univ (Icc b c) := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  refine ⟨fun j k => ?_, ae_of_all _ fun z => ?_⟩
  · exact (((continuous_apply k).comp ((continuous_apply j).comp
      ω.1.continuous)).comp continuous_fst).measurable.aemeasurable
  · have hs := ParabolicBridge.isEllipticMatrix_smul_of_symm_bounds hL
      (hω z.1).1 (fun ξ => ((hω z.1).2 ξ).1) (fun ξ => ((hω z.1).2 ξ).2)
    have hu := PDE.isEllipticMatrix_smul (inv_pos.mpr hLp) hs
    simpa only [smul_smul, inv_mul_cancel₀ hLp.ne', one_smul, mul_one,
      pow_two, ← mul_assoc, one_mul] using hu

/-- The sourced comparison applied to the actual corrected forward orbit.
Its source is the literal coefficient-gradient drift; the right hand side
retains the actual local gradient energy that must be absorbed by Caccioppoli. -/
theorem holder_forward_corrected_orbit_comparison
    (hinterior : node_e_u3A_holder_u2D_average_u23_unforced_u2D_interiorStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ α C : ℝ, 0 < α ∧ α < 1 ∧ 1 ≤ C ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange),
      HasSmoothBounds D Q → ∀ (i : Fin d) (ζ : ℂ)
      (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
      ∀ (hP : IsComplexEnvironmentSemigroup Q i ζ P),
      ∀ (f : Lp ℂ 2 (reducedLaw Q)) (t : ℝ) (x₀ : EinsteinRelation.Vec d) (r : ℝ),
      0 < t → 0 < r → 0 < t - r ^ 2 →
      ∃ (W : ℝ × FieldPair d → ℂ) (V : Fin d → ℝ × FieldPair d → ℂ),
      Measurable W ∧ (∀ j, Measurable (V j)) ∧
      (∀ s, (fun ω => W (s, ω)) =ᵐ[reducedLaw Q]
        (fun ω => centeredComplexLp Q (P s.toNNReal f) ω +
          ∫ v in (t / 4)..s, hP.centeringSource f v)) ∧
      (∀ j s, (fun ω => V j (s, ω)) =ᵐ[reducedLaw Q]
        (hP.gradientOrbit f s) j) ∧
      ∀ᵐ ω ∂reducedLaw Q,
      let L := Real.exp (2 * D.ellipticity) * D.ellipticity
      let Ω := euclideanBall x₀ r ×ˢ Ioo (t - r ^ 2) t
      let u : EinsteinRelation.Vec d × ℝ → ℂ := fun z => W (z.2, translate z.1 ω)
      let G : Fin d → EinsteinRelation.Vec d × ℝ → ℂ := fun j z => V j (z.2, translate z.1 ω)
      let cyl := fun ρ : ℝ => Ioo (t - ρ ^ 2) t ×ˢ euclideanBall x₀ ρ
      ∀ θ : ℝ, 0 < θ → θ ≤ 1 / 2 →
      Real.sqrt (⨍ z in cyl (θ * r),
        ‖u z.swap - (⨍ w in cyl (θ * r), u w.swap)‖ ^ 2) ≤
        2 * (Real.sqrt ((volume.real (cyl (θ * r)))⁻¹) +
          C * θ ^ α * Real.sqrt ((volume.real (cyl r))⁻¹)) *
          Real.sqrt (r ^ 4 * ((2 * L * ‖ζ‖) ^ 2 *
            (∫ z in Ω, ∑ j, ‖G j z‖ ^ 2)) / (L⁻¹ / 10) ^ 2) +
        2 * C * θ ^ α * Real.sqrt (⨍ z in cyl r,
          ‖u z.swap - (⨍ w in cyl r, u w.swap)‖ ^ 2) := by
  obtain ⟨α, C, hα, hα1, hC, hcomp⟩ :=
    holder_forward_complex_comparison hinterior d hd D
  refine ⟨α, C, hα, hα1, hC, ?_⟩
  intro Q hQ i ζ P hP f t x₀ r ht hr hb
  letI : Fact (2 ≤ d) := ⟨hd⟩
  obtain ⟨W, V, hW, hV, heW, heV, hlocal⟩ :=
    holder_average_corrected_local_comparison_equations hP f ht hb hr
  refine ⟨W, V, hW, hV, heW, heV, ?_⟩
  let L := Real.exp (2 * D.ellipticity) * D.ellipticity
  have hL : 1 ≤ L := one_le_mul_of_one_le_of_one_le
    (Real.one_le_exp (by linarith [D.one_le_ellipticity])) D.one_le_ellipticity
  filter_upwards [hlocal, hcomp Q hQ, c4_ae_reduced_physical_elliptic Q] with ω hloc hc hell
  dsimp only at hloc ⊢
  obtain ⟨hu, hG, hgrad, hheat⟩ := hloc
  have hac (j k : Fin d) : Continuous (fun z : EinsteinRelation.Vec d × ℝ => ω.1 z.1 j k) :=
    ((continuous_apply k).comp ((continuous_apply j).comp ω.1.continuous)).comp continuous_fst
  have hsource := holderComparison_drift_memLp_integral
    (ae_of_all (volume.restrict (euclideanBall x₀ r ×ˢ Ioo (t - r ^ 2) t))
      fun z => s5Elliptic_of_isElliptic hL hell z.1)
    (fun j k => (hac j k).aestronglyMeasurable) i (-ζ) hG
  intro θ hθ hθhalf
  have he := hc t x₀ r L⁻¹ L hr
    (holder_forward_parabolic_coeff hL hell (t - r ^ 2) t) hac
    _ _ _ hu hG hsource.1 hgrad hheat θ hθ hθhalf
  dsimp only at he
  apply he.trans
  apply add_le_add _ le_rfl
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.sqrt_le_sqrt
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  simpa only [norm_neg] using hsource.2

/-- Restarting the actual centered semigroup at the eighth-time slice gives
an Lp bound uniform over the terminal time window. -/
theorem holder_forward_centered_window_bound
    (hgrowth : node_e_u3A_lp_u2D_growthStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) (p : ℝ) (hp : 2 ≤ p) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (ζ : ℂ)
      (P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
      IsComplexTransposeSemigroup Q P T →
    ∀ (f : Lp ℂ 2 (reducedLaw Q)) (t : ℝ), 0 < t →
      let u := fun s : ℝ => centeredComplexLp Q (P s.toNNReal (centeredComplexLp Q f))
      MemLp (u (t / 8)) (ENNReal.ofReal p) (reducedLaw Q) →
      ∀ s ∈ Icc (t / 4) t,
        MemLp (u s) (ENNReal.ofReal p) (reducedLaw Q) ∧
        eLpNorm (u s) (ENNReal.ofReal p) (reducedLaw Q) ≤
          ENNReal.ofReal (2 * Real.exp (C * ‖ζ‖ ^ 2 * t)) *
            eLpNorm (u (t / 8)) (ENNReal.ofReal p) (reducedLaw Q) := by
  obtain ⟨C, hC, h⟩ := hgrowth d D.ellipticity D.dependenceRange p hd hp
  refine ⟨C, hC, ?_⟩
  intro Q ζ P T hP hT f t ht u hu s hs
  obtain ⟨hbound, _, _, hadd⟩ := h Q ⟨0, by omega⟩ ζ P T hP hT
  have he : (s - t / 8).toNNReal + (t / 8).toNNReal = s.toNNReal := by
    apply NNReal.eq
    simp only [NNReal.coe_add, Real.coe_toNNReal _ (by linarith [hs.1] : 0 ≤ s - t / 8),
      Real.coe_toNNReal _ (by positivity : 0 ≤ t / 8),
      Real.coe_toNNReal _ (by linarith [hs.1] : 0 ≤ s)]
    ring
  have hb := hbound (s - t / 8).toNNReal (u (t / 8)) hu
  have hrestart : centeredComplexLp Q
      (P (s - t / 8).toNNReal (centeredComplexLp Q (u (t / 8)))) = u s := by
    exact (hadd (s - t / 8).toNNReal (t / 8).toNNReal f).symm.trans
      (congrArg (fun r => centeredComplexLp Q (P r (centeredComplexLp Q f))) he)
  have hm := hb.2.2.1
  have hn := hb.2.2.2.2.2
  change MemLp (centeredComplexLp Q
    (P (s - t / 8).toNNReal (centeredComplexLp Q (u (t / 8))))) _ _ at hm
  change eLpNorm (centeredComplexLp Q
    (P (s - t / 8).toNNReal (centeredComplexLp Q (u (t / 8))))) _ _ ≤ _ at hn
  rw [hrestart] at hm hn
  refine ⟨hm, hn.trans ?_⟩
  refine mul_le_mul_left ?_ _
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.exp_le_exp.mpr
  rw [Real.coe_toNNReal _ (by linarith [hs.1] : 0 ≤ s - t / 8)]
  exact mul_le_mul_of_nonneg_left (by linarith [hs.2] : s - t / 8 ≤ t) (by positivity)

/-- The corrected forward orbit has a common jointly measurable
representative with an Lp bound at every time in the terminal window. The
source constant is chosen before p, as in the centered-source dependency. -/
theorem holder_forward_corrected_window_bound
    (hgrowth : node_e_u3A_lp_u2D_growthStmt)
    (hsource : node_l_u3A_forced_u2D_local_u23_centered_u2D_sourceStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ Cs : ℝ, 0 < Cs ∧ ∀ p : ℝ, 2 ≤ p → ∃ Cg : ℝ, 0 < Cg ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange),
      HasSmoothBounds D Q → ∀ (ζ : ℂ)
      (P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
      ∀ (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P),
      IsComplexTransposeSemigroup Q P T →
    ∀ f : Lp ℂ 2 (reducedLaw Q), MemLp f (ENNReal.ofReal p) (reducedLaw Q) →
      letI := reducedLaw_probability Q
      let u := fun s : ℝ => centeredComplexLp Q (P s.toNNReal (centeredComplexLp Q f))
      ∃ G : ℝ → PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)),
        (∀ s : ℝ, 0 < s →
          HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
            (u s) (G s)) ∧
        (let c := fun s : ℝ => ζ * (∫ ω,
            ∑ j : Fin d, (ω.1 0 j ⟨0, by omega⟩ : ℂ) * G s j ω ∂reducedLaw Q)
         (∀ s : ℝ, 0 < s → c s = hP.centeringSource (centeredComplexLp Q f) s) ∧
         ∀ t : ℝ, 0 < t →
           let w := fun s : ℝ => u s +
             Lp.const 2 (reducedLaw Q) (∫ v in (t / 4)..s, c v)
           (∀ s : ℝ, 0 < s → ∃ V : Lp ℂ 2 (reducedLaw Q),
             HasDerivAt w V s ∧ IsComplexGeneratorPair Q ⟨0, by omega⟩ ζ (w s) V) ∧
           ∃ U : ℝ × FieldPair d → ℂ,
             StronglyMeasurable U ∧
             (∀ s : ℝ, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] w s) ∧
             ∀ s ∈ Icc (t / 4) t,
               MemLp (fun ω => U (s, ω)) (ENNReal.ofReal p) (reducedLaw Q) ∧
               eLpNorm (fun ω => U (s, ω)) (ENNReal.ofReal p) (reducedLaw Q) ≤
                 ENNReal.ofReal (2 * Real.exp (Cg * ‖ζ‖ ^ 2 * t) +
                   Cs * ‖ζ‖ * Real.sqrt t * Real.exp (Cs * ‖ζ‖ ^ 2 * t)) *
                   eLpNorm (u (t / 8)) (ENNReal.ofReal p) (reducedLaw Q)) := by
  obtain ⟨Cs, hCs, hsrc⟩ := hsource d hd D
  refine ⟨Cs, hCs, ?_⟩
  intro p hp
  obtain ⟨Cg, hCg, hg⟩ := holder_forward_centered_window_bound hgrowth d hd D p hp
  obtain ⟨Cp, _, hsrcp⟩ := hsrc p hp
  refine ⟨Cg, hCg, ?_⟩
  intro Q hQ ζ P T hP hT f hf
  letI := reducedLaw_probability Q
  intro u
  obtain ⟨G, hG, hc⟩ := hsrcp Q hQ ζ P hP f hf
  refine ⟨G, fun s hs => (hG s hs).1, ?_⟩
  intro c
  refine ⟨?_, ?_⟩
  · intro s hs
    have he : hP.gradientOrbit (centeredComplexLp Q f) s = G s :=
      WithLp.ofLp_injective 2
        ((hP.centered_gradientOrbit_spec (centeredComplexLp Q f) hs).unique ((hG s hs).1))
    change _ = ζ * (∫ ω, ∑ j, (ω.1 0 j ⟨0, by omega⟩ : ℂ) *
      (hP.gradientOrbit (centeredComplexLp Q f) s) j ω ∂reducedLaw Q)
    rw [he]
  intro t ht w
  obtain ⟨hu8, _, hcb, hregular, U, hU, heU, _⟩ := hc t ht
  refine ⟨hregular, U, hU, heU, ?_⟩
  have hp0 : 0 < p := by linarith
  have hpe : (1 : ENNReal) ≤ ENNReal.ofReal p := by
    exact_mod_cast (ENNReal.ofReal_le_ofReal (by linarith : (1 : ℝ) ≤ p))
  have hp2 : (2 : ENNReal) ≤ ENNReal.ofReal p := by
    exact_mod_cast (ENNReal.ofReal_le_ofReal hp)
  have hn8 : ‖u (t / 8)‖ ≤
      (eLpNorm (u (t / 8)) (ENNReal.ofReal p) (reducedLaw Q)).toReal := by
    exact ENNReal.toReal_mono hu8.eLpNorm_ne_top
      (eLpNorm_le_eLpNorm_of_exponent_le hp2)
  intro s hs
  obtain ⟨hus, hns⟩ := hg Q ζ P T hP hT f t ht hu8 s hs
  let a := ∫ v in (t / 4)..s, c v
  have hca : ‖a‖ ≤ Cs * ‖ζ‖ * Real.sqrt t * Real.exp (Cs * ‖ζ‖ ^ 2 * t) *
      (eLpNorm (u (t / 8)) (ENNReal.ofReal p) (reducedLaw Q)).toReal := by
    have hcpoint (v : ℝ) (hv : v ∈ Set.uIoc (t / 4) s) :
        ‖c v‖ ≤ Cs * ‖ζ‖ / Real.sqrt t * Real.exp (Cs * ‖ζ‖ ^ 2 * t) *
          (eLpNorm (u (t / 8)) (ENNReal.ofReal p) (reducedLaw Q)).toReal := by
      rw [Set.uIoc_of_le hs.1] at hv
      exact (hcb v ⟨hv.1.le, hv.2.trans hs.2⟩).trans
        (mul_le_mul_of_nonneg_left hn8 (by positivity))
    have ha := intervalIntegral.norm_integral_le_of_norm_le_const hcpoint
    have hlen : |s - t / 4| ≤ t := by rw [abs_of_nonneg (by linarith [hs.1])]; linarith [hs.2]
    have hsqrt : t / Real.sqrt t = Real.sqrt t := by
      apply (div_eq_iff (Real.sqrt_pos.mpr ht).ne').mpr
      nlinarith [Real.sq_sqrt ht.le]
    calc
      ‖a‖ ≤ _ := ha
      _ ≤ (Cs * ‖ζ‖ / Real.sqrt t * Real.exp (Cs * ‖ζ‖ ^ 2 * t) *
          (eLpNorm (u (t / 8)) (ENNReal.ofReal p) (reducedLaw Q)).toReal) * t :=
        mul_le_mul_of_nonneg_left hlen (by positivity)
      _ = (Cs * ‖ζ‖ * Real.exp (Cs * ‖ζ‖ ^ 2 * t) *
          (eLpNorm (u (t / 8)) (ENNReal.ofReal p) (reducedLaw Q)).toReal) *
            (t / Real.sqrt t) := by ring
      _ = _ := by rw [hsqrt]; ring
  have hew : (w s : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
      (fun ω => u s ω + a) := by
    filter_upwards [Lp.coeFn_add (u s) (Lp.const 2 (reducedLaw Q) a),
      Lp.coeFn_const 2 (reducedLaw Q) a] with ω hadd hconst
    exact hadd.trans (congrArg (u s ω + ·) hconst)
  have hUa := (heU s).trans hew
  refine ⟨(memLp_congr_ae hUa).mpr (hus.add (memLp_const a)), ?_⟩
  rw [eLpNorm_congr_ae hUa]
  have hna : eLpNorm (fun _ : FieldPair d => a) (ENNReal.ofReal p) (reducedLaw Q) ≤
      ENNReal.ofReal (Cs * ‖ζ‖ * Real.sqrt t * Real.exp (Cs * ‖ζ‖ ^ 2 * t)) *
        eLpNorm (u (t / 8)) (ENNReal.ofReal p) (reducedLaw Q) := by
    rw [eLpNorm_const' a (ENNReal.ofReal_pos.mpr hp0).ne' ENNReal.ofReal_ne_top,
      measure_univ, ENNReal.one_rpow, mul_one, ← ofReal_norm]
    calc
      _ ≤ ENNReal.ofReal (Cs * ‖ζ‖ * Real.sqrt t * Real.exp (Cs * ‖ζ‖ ^ 2 * t) *
          (eLpNorm (u (t / 8)) (ENNReal.ofReal p) (reducedLaw Q)).toReal) := by
        exact ENNReal.ofReal_le_ofReal hca
      _ = _ := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hu8.eLpNorm_ne_top]
  calc
    _ ≤ eLpNorm (u s) (ENNReal.ofReal p) (reducedLaw Q) +
        eLpNorm (fun _ : FieldPair d => a) (ENNReal.ofReal p) (reducedLaw Q) :=
      eLpNorm_add_le hpe
    _ ≤ _ := add_le_add hns hna
    _ = _ := by rw [← add_mul, ENNReal.ofReal_add (by positivity) (by positivity)]

/-- Normalized physical spacetime L2 averages preserve a uniform window
Lp bound. In particular, shrinking the cylinder introduces no inverse-volume
loss in the environment norm. -/
theorem holder_forward_window_rms_bound
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    {p M a b : ℝ} (hp : 2 ≤ p) (hM : 0 ≤ M)
    (U : ℝ × FieldPair d → ℂ) (hU : Measurable U)
    (hwindow : ∀ s ∈ Icc a b,
      MemLp (fun ω => U (s, ω)) (ENNReal.ofReal p) (reducedLaw Q) ∧
      eLpNorm (fun ω => U (s, ω)) (ENNReal.ofReal p) (reducedLaw Q) ≤
        ENNReal.ofReal M)
    (S : Set (ℝ × EinsteinRelation.Vec d)) (hS : MeasurableSet S)
    (hS0 : volume S ≠ 0) (hSfin : volume S ≠ ⊤)
    (hSt : ∀ z ∈ S, z.1 ∈ Icc a b) :
    MemLp (fun ω => Real.sqrt (⨍ z in S, ‖U (z.1, translate z.2 ω)‖ ^ 2))
      (ENNReal.ofReal p) (reducedLaw Q) ∧
    eLpNorm (fun ω => Real.sqrt (⨍ z in S, ‖U (z.1, translate z.2 ω)‖ ^ 2))
      (ENNReal.ofReal p) (reducedLaw Q) ≤ ENNReal.ofReal M := by
  letI := reducedLaw_probability Q
  let F : FieldPair d × (ℝ × EinsteinRelation.Vec d) → ℝ :=
    fun z => ‖U (z.2.1, translate z.2.2 z.1)‖
  have hF : Measurable F :=
    (hU.comp (measurable_snd.fst.prodMk
      (Probability.continuous_translate.measurable.comp
        (measurable_snd.snd.prodMk measurable_fst)))).norm
  apply Correctors.scalarL2_setAverage_moment_le
    (reducedLaw Q) volume hS hS0 hSfin hp hM F hF
  intro z hz
  obtain ⟨hu, hb⟩ := hwindow z.1 (hSt z hz)
  have htr := measurePreserving_translate
    (reducedLaw Q) (reducedLaw_stationary Q) z.2
  refine ⟨hu.norm.comp_measurePreserving htr, ?_⟩
  have hn := eLpNorm_comp_measurePreserving (p := ENNReal.ofReal p)
    hu.norm.aestronglyMeasurable htr
  rw [eLpNorm_norm _ hu.aestronglyMeasurable] at hn
  exact hn.trans_le hb

/-- Jointly measurable representatives of the same environment orbit agree
on almost every physical spacetime section, for any s-finite time measure.
This permits local energy estimates to be transferred to one common orbit. -/
theorem holder_forward_physical_representative_eq
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (ν : Measure ℝ) [SFinite ν]
    (U V : ℝ × FieldPair d → ℂ) (hU : Measurable U) (hV : Measurable V)
    (hUV : ∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] fun ω => V (s, ω)) :
    ∀ᵐ ω ∂reducedLaw Q,
      (fun z : EinsteinRelation.Vec d × ℝ => U (z.2, translate z.1 ω))
        =ᵐ[(volume : Measure (EinsteinRelation.Vec d)).prod ν]
      (fun z => V (z.2, translate z.1 ω)) := by
  let Φ : (EinsteinRelation.Vec d × ℝ) × FieldPair d → ℝ × FieldPair d :=
    fun z => (z.1.2, translate z.1.1 z.2)
  have hΦ : Measurable Φ := measurable_fst.snd.prodMk
    (Probability.continuous_translate.measurable.comp
      (measurable_fst.fst.prodMk measurable_snd))
  have he : MeasurableSet {z : (EinsteinRelation.Vec d × ℝ) × FieldPair d |
      U (z.1.2, translate z.1.1 z.2) = V (z.1.2, translate z.1.1 z.2)} :=
    measurableSet_eq_fun (hU.comp hΦ) (hV.comp hΦ)
  apply (Measure.ae_ae_comm he).mp
  refine ae_of_all _ fun z => ?_
  have htr := measurePreserving_translate
    (reducedLaw Q) (reducedLaw_stationary Q) z.1
  exact htr.quasiMeasurePreserving.ae (hUV z.2)

/-- A geometric comparison with a linearly decaying source still gives a
structural decay rate. The source size affects only the prefactor. -/
theorem holder_forward_inhomogeneous_iteration
    (E : ℕ → ℝ) {a q κ B : ℝ}
    (ha : 0 ≤ a) (hq : 0 ≤ q) (hqκ : q ≤ κ) (haκ : a < κ)
    (hB : 0 ≤ B) (hE : 0 ≤ E 0)
    (hstep : ∀ n : ℕ, E (n + 1) ≤ a * E n + B * q ^ n) :
    ∀ n : ℕ, E n ≤ κ ^ n * (E 0 + B / (κ - a)) := by
  have hden : 0 < κ - a := sub_pos.mpr haκ
  have hκ : 0 ≤ κ := hq.trans hqκ
  have hK : 0 ≤ B / (κ - a) := div_nonneg hB hden.le
  have hcancel : (κ - a) * (B / (κ - a)) = B :=
    mul_div_cancel₀ B hden.ne'
  intro n
  induction n with
  | zero => simpa only [pow_zero, one_mul] using le_add_of_nonneg_right hK
  | succ n ih =>
    have hp : q ^ n ≤ κ ^ n := by gcongr
    calc
      E (n + 1) ≤ a * E n + B * q ^ n := hstep n
      _ ≤ a * (κ ^ n * (E 0 + B / (κ - a))) + B * κ ^ n :=
        add_le_add (mul_le_mul_of_nonneg_left ih ha)
          (mul_le_mul_of_nonneg_left hp hB)
      _ = κ ^ n * (a * (E 0 + B / (κ - a)) + B) := by ring
      _ ≤ κ ^ n * (κ * (E 0 + B / (κ - a))) := by
        apply mul_le_mul_of_nonneg_left _ (pow_nonneg hκ _)
        nlinarith
      _ = κ ^ (n + 1) * (E 0 + B / (κ - a)) := by rw [pow_succ]; ring

/-- One dimension-dependent spatial cutoff constant controls the actual
corrected-orbit Caccioppoli inequality for every law, force and initial datum.
The gradient and primitive remain those of the actual semigroup. -/
theorem holder_forward_uniform_caccioppoli
    (d : ℕ) (hd : 2 ≤ d) :
    ∃ B : ℝ, 0 < B ∧ ∀ {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (f : Lp ℂ 2 (reducedLaw Q)) {t a : ℝ} (ht : 0 < t) (ha : 0 < a),
    let L := Real.exp (2 * Λ₀) * Λ₀
    let w := fun r : ℝ => centeredComplexLp Q (P r.toNNReal (centeredComplexLp Q f)) +
      Lp.const 2 (reducedLaw Q) (∫ v in (t / 4)..r, hP.centeringSource f v)
    ∃ g : Lp ℂ 2 (reducedLaw Q),
      ∃ W V : ℝ × FieldPair d → ℂ, ∃ D : Fin d → ℝ × FieldPair d → ℂ,
      Measurable W ∧ Measurable V ∧ (∀ j, Measurable (D j)) ∧
      (∀ s, (fun ω => W (s, ω)) =ᵐ[reducedLaw Q] w s) ∧
      (∀ s, (fun ω => V (s, ω)) =ᵐ[reducedLaw Q] P (s - a).toNNReal g) ∧
      (∀ j s, (fun ω => D j (s, ω)) =ᵐ[reducedLaw Q]
        (hP.gradientOrbit (centeredComplexLp Q f) s) j) ∧
      (∀ r, a < r → HasDerivAt w (P (r - a).toNNReal g) r ∧
        IsComplexGeneratorPair Q i ζ (w r) (P (r - a).toNNReal g)) ∧
      ∀ b c : ℝ, a < b → b < c → ∀ z : EinsteinRelation.Vec d, ∀ r κ : ℝ,
        0 < r → 0 ≤ κ → r ≤ κ * Real.sqrt t / (1 + ‖ζ‖ * Real.sqrt t) →
        ∀ᵐ ω ∂reducedLaw Q,
          (∫ s in Icc ((b + c) / 2) c,
            ∫ x in {x | euclideanNorm (x - z) ≤ r},
              ∑ j, ‖D j (s, translate x ω)‖ ^ 2) ≤
          16 * L * ((c - b)⁻¹ +
            (2 * (d : ℝ) * ((d : ℝ) + 1) * L ^ 3) *
              ((κ ^ 2 + (d : ℝ) * B ^ 2) / r ^ 2)) *
            (∫ s in Icc b c, ∫ x in {x | euclideanNorm (x - z) ≤ 2 * r},
              ‖W (s, translate x ω)‖ ^ 2) := by
  letI : Fact (2 ≤ d) := ⟨hd⟩
  obtain ⟨B, hB, hcutoff⟩ := exists_physical_euclidean_cutoff d
  refine ⟨B, hB, ?_⟩
  intro Λ₀ r₀ Q i ζ P hP f t a ht ha L w
  let := reducedLaw_probability Q
  obtain ⟨g, W, V, D, hW, hV, hD, heW, heV, heD, hregular, henergy⟩ :=
    complexForced_correctedOrbit_ae_physical_boundaryCutoffEnergy hP f ht ha
  refine ⟨g, W, V, D, hW, hV, hD, heW, heV, heD, hregular, ?_⟩
  have hu : Continuous (fun r : ℝ =>
      centeredComplexLp Q (P r.toNNReal (centeredComplexLp Q f))) := by
    simpa only [Function.comp_def, centeredComplexLpCLM_apply] using
      (centeredComplexLpCLM Q).continuous.comp
        ((hP.2.2.1 (centeredComplexLp Q f)).comp continuous_real_toNNReal)
  have hw : Continuous w := hu.add ((Lp.constL 2 (reducedLaw Q) ℂ).continuous.comp
    (Blueprint.continuous_centered_source_primitive hP f (t / 4)))
  have hL : 0 < L := mul_pos (Real.exp_pos _)
    (lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter)
  have hC : 0 ≤ 2 * (d : ℝ) * ((d : ℝ) + 1) * L ^ 3 := by positivity
  intro b c hb hbc z r κ hr hκ hrad
  obtain ⟨φ, hφ, hφrange, hone, hzero, hφD⟩ := hcutoff z r hr
  obtain ⟨η, hη, hηd, hηb, hηc, hηbounds⟩ := exists_physical_temporal_cutoff hbc
  have hηcont : ContinuousOn η (Icc b c) := by
    simpa only [uIcc_of_le hbc.le] using hη.continuousOn
  have hηrange s (hs : s ∈ Icc b c) : 0 ≤ η s ∧ η s ≤ 1 ∧
      0 ≤ deriv η s ∧ deriv η s ≤ 2 / (c - b) :=
    ⟨(hηbounds s hs).1, (hηbounds s hs).2.1,
      (hηbounds s hs).2.2.1, (hηbounds s hs).2.2.2.1⟩
  have hηlower s (hs : s ∈ Icc ((b + c) / 2) c) : 1 / 4 ≤ η s :=
    (hηbounds s ⟨by linarith [hs.1], hs.2⟩).2.2.2.2 hs.1
  have hwI : IntegrableOn (fun s => ‖w s‖ ^ 2) (Icc b c) volume :=
    (hw.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  have hlocalW := ae_locally_memLp_joint_spatial_translate
    (reducedLaw Q) (reducedLaw_stationary Q) hW
    (integrable_sq_joint_l2_representative hwI hW heW)
  have hlocalD (j : Fin d) : ∀ᵐ ω ∂reducedLaw Q,
      ∀ K : Set (EinsteinRelation.Vec d), IsCompact K →
        MemLp (fun p : EinsteinRelation.Vec d × ℝ => D j (p.2, translate p.1 ω)) 2
          ((volume.restrict K).prod (volume.restrict (Icc b c))) := by
    have hc : ContinuousOn (fun s : ℝ => (hP.gradientOrbit (centeredComplexLp Q f) s) j)
        (Ioi 0) :=
      (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)) j).continuous.comp_continuousOn
        (hP.continuousOn_gradientOrbit (centeredComplexLp Q f))
    have hi : IntegrableOn (fun s : ℝ => ‖(hP.gradientOrbit (centeredComplexLp Q f) s) j‖ ^ 2)
        (Icc b c) volume :=
      ((hc.norm.pow 2).mono (fun _ hs => lt_of_lt_of_le (ha.trans hb) hs.1)).integrableOn_compact
        isCompact_Icc
    exact ae_locally_memLp_joint_spatial_translate (reducedLaw Q) (reducedLaw_stationary Q)
      (hD j) (integrable_sq_joint_l2_representative hi (hD j) (heD j))
  filter_upwards [henergy b c hb hbc.le φ hφ η hη hηd
    (fun s hs => (hηbounds s hs).1), hlocalW, ae_all_iff.mpr hlocalD]
    with ω hω hlW hlD
  have hK := isCompact_physical_euclidean_closedBall z (2 * r)
  apply physical_cylinder_caccioppoli_of_cutoff_energy (U := fun x => (w c) (translate x ω))
    hbc hr hκ hL hC hrad
    (hlW _ hK) (fun j => hlD j _ hK) hφ hφrange hone hzero hφD hηcont hηd
    hηrange hηlower
  rw [hηb, hηc, zero_mul, one_mul, zero_sub] at hω
  linarith only [hω]

/-- The physical representative transfer only needs agreement at almost
every time for the time measure used in the local estimate. -/
theorem holder_forward_physical_representative_eq_ae
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (ν : Measure ℝ) [SFinite ν]
    (U V : ℝ × FieldPair d → ℂ) (hU : Measurable U) (hV : Measurable V)
    (hUV : ∀ᵐ s ∂ν, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] fun ω => V (s, ω)) :
    ∀ᵐ ω ∂reducedLaw Q,
      (fun z : EinsteinRelation.Vec d × ℝ => U (z.2, translate z.1 ω))
        =ᵐ[(volume : Measure (EinsteinRelation.Vec d)).prod ν]
      (fun z => V (z.2, translate z.1 ω)) := by
  let Φ : (EinsteinRelation.Vec d × ℝ) × FieldPair d → ℝ × FieldPair d :=
    fun z => (z.1.2, translate z.1.1 z.2)
  have hΦ : Measurable Φ := measurable_fst.snd.prodMk
    (Probability.continuous_translate.measurable.comp
      (measurable_fst.fst.prodMk measurable_snd))
  have he : MeasurableSet {z : (EinsteinRelation.Vec d × ℝ) × FieldPair d |
      U (z.1.2, translate z.1.1 z.2) = V (z.1.2, translate z.1.1 z.2)} :=
    measurableSet_eq_fun (hU.comp hΦ) (hV.comp hΦ)
  apply (Measure.ae_ae_comm he).mp
  filter_upwards [Measure.quasiMeasurePreserving_snd.ae hUV] with z hz
  have htr := measurePreserving_translate
    (reducedLaw Q) (reducedLaw_stationary Q) z.1
  exact htr.quasiMeasurePreserving.ae hz

/-- Local physical energies do not depend on the jointly measurable
representative chosen for the orbit on the time window. -/
theorem holder_forward_window_energy_congr
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (I : Set ℝ) (hI : MeasurableSet I) (K : Set (EinsteinRelation.Vec d))
    (U V : ℝ × FieldPair d → ℂ) (hU : Measurable U) (hV : Measurable V)
    (hUV : ∀ s ∈ I, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] fun ω => V (s, ω)) :
    ∀ᵐ ω ∂reducedLaw Q,
      (∫ s in I, ∫ x in K, ‖U (s, translate x ω)‖ ^ 2) =
      (∫ s in I, ∫ x in K, ‖V (s, translate x ω)‖ ^ 2) := by
  have hp := holder_forward_physical_representative_eq_ae Q (volume.restrict I)
    U V hU hV (ae_restrict_of_forall_mem hI hUV)
  filter_upwards [hp] with ω hω
  have hs := Measure.ae_ae_of_ae_prod
    (Measure.measurePreserving_swap.quasiMeasurePreserving.ae hω)
  apply integral_congr_ae
  filter_upwards [hs] with s hs
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae hs] with x hx
  change U (s, translate x ω) = V (s, translate x ω) at hx
  rw [hx]

/-- All normalized spacetime oscillations agree for two measurable
representatives of the same orbit, on one environment event for every domain. -/
theorem holder_forward_oscillation_congr
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (U V : ℝ × FieldPair d → ℂ) (hU : Measurable U) (hV : Measurable V)
    (hUV : ∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] fun ω => V (s, ω)) :
    ∀ᵐ ω ∂reducedLaw Q, ∀ S : Set (ℝ × EinsteinRelation.Vec d),
      Real.sqrt (⨍ z in S, ‖U (z.1, translate z.2 ω) -
        (⨍ y in S, U (y.1, translate y.2 ω))‖ ^ 2) =
      Real.sqrt (⨍ z in S, ‖V (z.1, translate z.2 ω) -
        (⨍ y in S, V (y.1, translate y.2 ω))‖ ^ 2) := by
  have hp := holder_forward_physical_representative_eq Q volume U V hU hV hUV
  filter_upwards [hp] with ω hω
  have he : (fun z : ℝ × EinsteinRelation.Vec d => U (z.1, translate z.2 ω))
      =ᵐ[volume] fun z => V (z.1, translate z.2 ω) := by
    rw [Measure.volume_eq_prod]
    filter_upwards [Measure.measurePreserving_swap.quasiMeasurePreserving.ae hω]
      with z hz
    exact hz
  intro S
  have heS := ae_restrict_of_ae (s := S) he
  have hm := average_congr heS
  apply congrArg Real.sqrt
  apply average_congr
  filter_upwards [heS] with z hz
  rw [hz, hm]

/-- Actual joint gradient representatives have identical local physical
energies, on one environment event for every time window and spatial domain. -/
theorem holder_forward_gradient_energy_congr
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (G H : Fin d → ℝ × FieldPair d → ℂ)
    (hG : ∀ j, Measurable (G j)) (hH : ∀ j, Measurable (H j))
    (hGH : ∀ j s, (fun ω => G j (s, ω)) =ᵐ[reducedLaw Q] fun ω => H j (s, ω)) :
    ∀ᵐ ω ∂reducedLaw Q, ∀ (I : Set ℝ) (K : Set (EinsteinRelation.Vec d)),
      (∫ s in I, ∫ x in K, ∑ j, ‖G j (s, translate x ω)‖ ^ 2) =
      (∫ s in I, ∫ x in K, ∑ j, ‖H j (s, translate x ω)‖ ^ 2) := by
  have hp j := holder_forward_physical_representative_eq Q volume
    (G j) (H j) (hG j) (hH j) (hGH j)
  filter_upwards [ae_all_iff.mpr hp] with ω hω
  have he : (fun z : EinsteinRelation.Vec d × ℝ =>
      ∑ j, ‖G j (z.2, translate z.1 ω)‖ ^ 2) =ᵐ[volume.prod volume]
      (fun z => ∑ j, ‖H j (z.2, translate z.1 ω)‖ ^ 2) := by
    filter_upwards [ae_all_iff.mpr hω] with z hz
    exact Finset.sum_congr rfl fun j _ => congrArg (fun v : ℂ => ‖v‖ ^ 2) (hz j)
  have hs := Measure.ae_ae_of_ae_prod
    (Measure.measurePreserving_swap.quasiMeasurePreserving.ae he)
  intro I K
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae hs] with s hs
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae hs] with x hx
  exact hx

/-- The window estimate applies to every representative of the actual
corrected orbit used in the physical energy comparison. The source primitive
is identified on the positive terminal window, without an extra assumption. -/
theorem holder_forward_actual_window_bound
    (hgrowth : node_e_u3A_lp_u2D_growthStmt)
    (hsource : node_l_u3A_forced_u2D_local_u23_centered_u2D_sourceStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ Cs : ℝ, 0 < Cs ∧ ∀ p : ℝ, 2 ≤ p → ∃ Cg : ℝ, 0 < Cg ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange),
      HasSmoothBounds D Q → ∀ (ζ : ℂ)
      (P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
      ∀ (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P),
      IsComplexTransposeSemigroup Q P T →
    ∀ f : Lp ℂ 2 (reducedLaw Q), MemLp f (ENNReal.ofReal p) (reducedLaw Q) →
    ∀ t : ℝ, 0 < t →
      let u := fun s : ℝ => centeredComplexLp Q (P s.toNNReal (centeredComplexLp Q f))
      MemLp (u (t / 8)) (ENNReal.ofReal p) (reducedLaw Q) ∧
      ∀ W : ℝ × FieldPair d → ℂ,
      (∀ s, (fun ω => W (s, ω)) =ᵐ[reducedLaw Q]
        (fun ω => u s ω + ∫ v in (t / 4)..s,
          hP.centeringSource (centeredComplexLp Q f) v)) →
      ∀ s ∈ Icc (t / 4) t,
        MemLp (fun ω => W (s, ω)) (ENNReal.ofReal p) (reducedLaw Q) ∧
        eLpNorm (fun ω => W (s, ω)) (ENNReal.ofReal p) (reducedLaw Q) ≤
          ENNReal.ofReal (2 * Real.exp (Cg * ‖ζ‖ ^ 2 * t) +
            Cs * ‖ζ‖ * Real.sqrt t * Real.exp (Cs * ‖ζ‖ ^ 2 * t)) *
            eLpNorm (u (t / 8)) (ENNReal.ofReal p) (reducedLaw Q) := by
  obtain ⟨Cs, hCs, hbound⟩ := holder_forward_corrected_window_bound hgrowth hsource d hd D
  refine ⟨Cs, hCs, ?_⟩
  intro p hp
  obtain ⟨Cg, hCg, hbound⟩ := hbound p hp
  obtain ⟨_, _, hg⟩ := hgrowth d D.ellipticity D.dependenceRange p hd hp
  refine ⟨Cg, hCg, ?_⟩
  intro Q hQ ζ P T hP hT f hf t ht u
  letI := reducedLaw_probability Q
  have hu8 := ((hg Q ⟨0, by omega⟩ ζ P T hP hT).1 (t / 8).toNNReal f hf).2.2.1
  refine ⟨hu8, ?_⟩
  intro W heW s hs
  obtain ⟨G, _, hc, hcorrected⟩ := hbound Q hQ ζ P T hP hT f hf
  obtain ⟨_, U, _, heU, hUb⟩ := hcorrected t ht
  let c := fun v : ℝ => ζ * (∫ ω,
    ∑ j : Fin d, (ω.1 0 j ⟨0, by omega⟩ : ℂ) * G v j ω ∂reducedLaw Q)
  have hint : (∫ v in (t / 4)..s, c v) =
      ∫ v in (t / 4)..s, hP.centeringSource (centeredComplexLp Q f) v := by
    apply intervalIntegral.integral_congr
    intro v hv
    rw [uIcc_of_le hs.1] at hv
    exact hc v (by linarith [hv.1])
  have heUs : (fun ω => U (s, ω)) =ᵐ[reducedLaw Q]
      fun ω => u s ω + ∫ v in (t / 4)..s, c v := by
    filter_upwards [heU s,
      Lp.coeFn_add (u s) (Lp.const 2 (reducedLaw Q) (∫ v in (t / 4)..s, c v)),
      Lp.coeFn_const 2 (reducedLaw Q) (∫ v in (t / 4)..s, c v)]
      with ω hω hadd hconst
    exact hω.trans (hadd.trans (congrArg (u s ω + ·) hconst))
  rw [hint] at heUs
  have hWU := (heW s).trans heUs.symm
  refine ⟨(memLp_congr_ae hWU).mpr (hUb s hs).1, ?_⟩
  rw [eLpNorm_congr_ae hWU]
  exact (hUb s hs).2

/-- A backward Euclidean parabolic cylinder has exactly the expected
radius power, with no dependence on its center or terminal time. -/
theorem holder_forward_cylinder_volume
    {d : ℕ} (x : EinsteinRelation.Vec d) (t : ℝ) {r : ℝ} (hr : 0 < r) :
    volume.real (Ioo (t - r ^ 2) t ×ˢ euclideanBall x r) =
      r ^ (d + 2) * volume.real (euclideanBall (0 : EinsteinRelation.Vec d) 1) := by
  rw [Measure.volume_eq_prod, measureReal_prod_prod,
    Real.volume_real_Ioo_of_le (by nlinarith [sq_nonneg r])]
  change (t - (t - r ^ 2)) * (volume (euclideanBall x r)).toReal = _
  rw [volume_euclideanBall_toReal_eq_unit_mul_of_pos x hr]
  simp only [pow_add, pow_two, measureReal_def]
  ring

/-- Ratios of cylinder volumes depend only on the radius ratio. This is the
normalization used when taking environment norms in the comparison estimate. -/
theorem holder_forward_cylinder_volume_ratio
    {d : ℕ} (x y : EinsteinRelation.Vec d) (t s : ℝ) {r R : ℝ}
    (hr : 0 < r) (hR : 0 < R) :
    volume.real (Ioo (t - R ^ 2) t ×ˢ euclideanBall x R) /
        volume.real (Ioo (s - r ^ 2) s ×ˢ euclideanBall y r) =
      (R / r) ^ (d + 2) := by
  rw [holder_forward_cylinder_volume x t hR, holder_forward_cylinder_volume y s hr,
    div_pow]
  have hu : volume.real (euclideanBall (0 : EinsteinRelation.Vec d) 1) ≠ 0 :=
    (volume_euclideanBall_toReal_pos (0 : EinsteinRelation.Vec d) (by norm_num)).ne'
  field_simp

/-- The doubled closed energy cylinder has positive finite volume and a
structural volume ratio to the open comparison cylinder. A radius-three open
ball avoids any boundary-measure convention in this normalization. -/
theorem holder_forward_outer_cylinder_volume
    {d : ℕ} (x : EinsteinRelation.Vec d) (t : ℝ) {r : ℝ} (hr : 0 < r) :
    let S := Icc (t - 2 * r ^ 2) t ×ˢ
      {y : EinsteinRelation.Vec d | euclideanNorm (y - x) ≤ 2 * r}
    0 < volume.real S ∧ volume S ≠ ⊤ ∧
      volume.real S ≤ (2 * (3 : ℝ) ^ d) *
        volume.real (Ioo (t - r ^ 2) t ×ˢ euclideanBall x r) := by
  intro S
  let K := {y : EinsteinRelation.Vec d | euclideanNorm (y - x) ≤ 2 * r}
  have hK : IsCompact K := isCompact_physical_euclidean_closedBall x (2 * r)
  have hsmall : euclideanBall x r ⊆ K := by
    intro y hy
    have hy' := (mem_euclideanBall_iff_vecEuclideanNorm_lt hr).mp hy
    change euclideanNorm (y - x) < r at hy'
    change euclideanNorm (y - x) ≤ 2 * r
    linarith
  have hlarge : K ⊆ euclideanBall x (3 * r) := by
    intro y hy
    change euclideanNorm (y - x) ≤ 2 * r at hy
    apply (mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)).mpr
    change euclideanNorm (y - x) < 3 * r
    linarith
  have hKpos : 0 < volume.real K :=
    (volume_euclideanBall_toReal_pos x hr).trans_le
      (measureReal_mono hsmall (hK.measure_ne_top (μ := volume)))
  have hKbound := measureReal_mono hlarge
    (volume_euclideanBall_ne_top x (by positivity : 0 ≤ 3 * r))
  have hv : volume.real S = 2 * r ^ 2 * volume.real K := by
    change volume.real (Icc (t - 2 * r ^ 2) t ×ˢ K) = _
    rw [Measure.volume_eq_prod, measureReal_prod_prod,
      Real.volume_real_Icc_of_le (by nlinarith [sq_nonneg r])]
    ring
  refine ⟨by rw [hv]; positivity,
    (isCompact_Icc.prod hK).measure_ne_top (μ := volume), ?_⟩
  rw [hv, holder_forward_cylinder_volume x t hr]
  calc
    _ ≤ 2 * r ^ 2 * volume.real (euclideanBall x (3 * r)) :=
      mul_le_mul_of_nonneg_left hKbound (by positivity)
    _ = _ := by
      simp only [measureReal_def,
        volume_euclideanBall_toReal_eq_unit_mul_of_pos x (by positivity : 0 < 3 * r),
        mul_pow, pow_add]
      ring

/-- Caloric comparison and Caccioppoli hold for one actual corrected orbit.
The gradient energy has been eliminated in favor of the outer solution energy;
all three constants are chosen before the environment law and the force. -/
theorem holder_forward_energy_comparison
    (hinterior : node_e_u3A_holder_u2D_average_u23_unforced_u2D_interiorStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ α C B : ℝ, 0 < α ∧ α < 1 ∧ 1 ≤ C ∧ 0 < B ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange),
      HasSmoothBounds D Q → ∀ (i : Fin d) (ζ : ℂ)
      (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
      ∀ (hP : IsComplexEnvironmentSemigroup Q i ζ P)
      (f : Lp ℂ 2 (reducedLaw Q)) (t : ℝ), 0 < t →
      ∃ W : ℝ × FieldPair d → ℂ, Measurable W ∧
      (∀ s, (fun ω => W (s, ω)) =ᵐ[reducedLaw Q]
        (fun ω => centeredComplexLp Q (P s.toNNReal (centeredComplexLp Q f)) ω +
          ∫ v in (t / 4)..s, hP.centeringSource (centeredComplexLp Q f) v)) ∧
      ∀ (x₀ : EinsteinRelation.Vec d) (r : ℝ), 0 < r → t / 8 < t - 2 * r ^ 2 →
        r ≤ Real.sqrt t / (1 + ‖ζ‖ * Real.sqrt t) →
      ∀ᵐ ω ∂reducedLaw Q,
      let L := Real.exp (2 * D.ellipticity) * D.ellipticity
      let A := 2 * (d : ℝ) * ((d : ℝ) + 1) * L ^ 3
      let K := 16 * L * ((1 / 2 + A * (1 + (d : ℝ) * B ^ 2)) / r ^ 2)
      let u := fun z : ℝ × EinsteinRelation.Vec d => W (z.1, translate z.2 ω)
      let cyl := fun ρ : ℝ => Ioo (t - ρ ^ 2) t ×ˢ euclideanBall x₀ ρ
      ∀ θ : ℝ, 0 < θ → θ ≤ 1 / 2 →
      Real.sqrt (⨍ z in cyl (θ * r), ‖u z - (⨍ w in cyl (θ * r), u w)‖ ^ 2) ≤
        2 * (Real.sqrt ((volume.real (cyl (θ * r)))⁻¹) +
          C * θ ^ α * Real.sqrt ((volume.real (cyl r))⁻¹)) *
          Real.sqrt (r ^ 4 * ((2 * L * ‖ζ‖) ^ 2 *
            (K * (∫ s in Icc (t - 2 * r ^ 2) t,
              ∫ x in {x | euclideanNorm (x - x₀) ≤ 2 * r}, ‖u (s, x)‖ ^ 2))) /
              (L⁻¹ / 10) ^ 2) +
        2 * C * θ ^ α * Real.sqrt (⨍ z in cyl r, ‖u z - (⨍ w in cyl r, u w)‖ ^ 2) := by
  obtain ⟨α, C, hα, hα1, hC, hcomp⟩ :=
    holder_forward_corrected_orbit_comparison hinterior d hd D
  obtain ⟨B, hB, henergy⟩ := holder_forward_uniform_caccioppoli d hd
  refine ⟨α, C, B, hα, hα1, hC, hB, ?_⟩
  intro Q hQ i ζ P hP f t ht
  letI : Fact (2 ≤ d) := ⟨hd⟩
  letI := reducedLaw_probability Q
  let f₀ := centeredComplexLp Q f
  obtain ⟨g, W, V, G, hW, hV, hG, heW, heV, heG, hreg, hcacc⟩ :=
    henergy hP f₀ ht (show 0 < t / 8 by positivity)
  have heW' (s : ℝ) : (fun ω => W (s, ω)) =ᵐ[reducedLaw Q]
      (fun ω => centeredComplexLp Q (P s.toNNReal f₀) ω +
        ∫ v in (t / 4)..s, hP.centeringSource f₀ v) := by
    have hs := heW s
    simp only [f₀, centeredComplexLp_idempotent] at hs
    filter_upwards [hs,
      Lp.coeFn_add (centeredComplexLp Q (P s.toNNReal f₀))
        (Lp.const 2 (reducedLaw Q) (∫ v in (t / 4)..s, hP.centeringSource f₀ v)),
      Lp.coeFn_const 2 (reducedLaw Q) (∫ v in (t / 4)..s, hP.centeringSource f₀ v)]
      with ω hs hadd hconst
    exact hs.trans (hadd.trans (congrArg (centeredComplexLp Q (P s.toNNReal f₀) ω + ·) hconst))
  have heG' (j : Fin d) (s : ℝ) :
      (fun ω => G j (s, ω)) =ᵐ[reducedLaw Q] (hP.gradientOrbit f₀ s) j := by
    simpa only [f₀, centeredComplexLp_idempotent] using heG j s
  refine ⟨W, hW, heW', ?_⟩
  intro x₀ r hr htime hrad
  have hb : 0 < t - 2 * r ^ 2 := lt_trans (by positivity) htime
  have hb' : 0 < t - r ^ 2 := by nlinarith [sq_nonneg r]
  have hbc : t - 2 * r ^ 2 < t := by nlinarith [sq_pos_of_pos hr]
  obtain ⟨U, H, hU, hH, heU, heH, hcomparison⟩ :=
    hcomp Q hQ i ζ P hP f₀ t x₀ r ht hr hb'
  have hUW s := (heU s).trans (heW' s).symm
  have hHG j s := (heH j s).trans (heG' j s).symm
  have heOsc := holder_forward_oscillation_congr Q U W hU hW hUW
  have heGrad j := holder_forward_physical_representative_eq Q volume
    (H j) (G j) (hH j) (hG j) (hHG j)
  have hlocal := holder_average_corrected_representatives_memLp hP f₀ t (c := t) hb hW hG heW' heG'
  filter_upwards [hcomparison, heOsc, ae_all_iff.mpr heGrad, hlocal,
    hcacc (t - 2 * r ^ 2) t htime hbc x₀ r 1 hr (by norm_num)
      (by simpa only [one_mul] using hrad)] with ω hcompω hosc hgrad hloc henergyω
  let L := Real.exp (2 * D.ellipticity) * D.ellipticity
  let K := 16 * L * ((1 / 2 +
    (2 * (d : ℝ) * ((d : ℝ) + 1) * L ^ 3) * (1 + (d : ℝ) * B ^ 2)) / r ^ 2)
  let closed := {x : EinsteinRelation.Vec d | euclideanNorm (x - x₀) ≤ r}
  let outer := {x : EinsteinRelation.Vec d | euclideanNorm (x - x₀) ≤ 2 * r}
  let E : EinsteinRelation.Vec d × ℝ → ℝ :=
    fun z => ∑ j, ‖G j (z.2, translate z.1 ω)‖ ^ 2
  have hlocG := (hloc outer (isCompact_physical_euclidean_closedBall x₀ (2 * r))).2
  have hEi : Integrable E ((volume.restrict outer).prod
      (volume.restrict (Icc (t - 2 * r ^ 2) t))) :=
    integrable_finsetSum _ fun j _ =>
      (memLp_two_iff_integrable_sq_norm (hlocG j).aestronglyMeasurable).mp (hlocG j)
  have hclosed : closed ⊆ outer := fun x hx => by
    change euclideanNorm (x - x₀) ≤ r at hx
    change euclideanNorm (x - x₀) ≤ 2 * r
    linarith
  have htimeSub : Icc (t - r ^ 2) t ⊆ Icc (t - 2 * r ^ 2) t := by
    intro s hs
    exact ⟨by nlinarith [hs.1, sq_nonneg r], hs.2⟩
  have hEi' : IntegrableOn E (closed ×ˢ Icc (t - r ^ 2) t) (volume.prod volume) := by
    unfold IntegrableOn
    rw [← Measure.prod_restrict]
    exact hEi.mono_measure (Measure.prod_mono
      (Measure.restrict_mono hclosed le_rfl) (Measure.restrict_mono htimeSub le_rfl))
  have hΩ : euclideanBall x₀ r ×ˢ Ioo (t - r ^ 2) t ⊆
      closed ×ˢ Icc (t - r ^ 2) t := by
    intro z hz
    have hx := (mem_euclideanBall_iff_vecEuclideanNorm_lt hr).mp hz.1
    refine ⟨?_, ⟨hz.2.1.le, hz.2.2.le⟩⟩
    exact hx.le
  have hEbound : (∫ z in euclideanBall x₀ r ×ˢ Ioo (t - r ^ 2) t, E z) ≤
      K * (∫ s in Icc (t - 2 * r ^ 2) t,
        ∫ x in outer, ‖W (s, translate x ω)‖ ^ 2) := by
    have hhalf : ((t - 2 * r ^ 2) + t) / 2 = t - r ^ 2 := by ring
    have hΔ : t - (t - 2 * r ^ 2) = 2 * r ^ 2 := by ring
    rw [hhalf, hΔ] at henergyω
    have he : (2 * r ^ 2)⁻¹ +
        (2 * (d : ℝ) * ((d : ℝ) + 1) * L ^ 3) *
          ((1 ^ 2 + (d : ℝ) * B ^ 2) / r ^ 2) =
        (1 / 2 + (2 * (d : ℝ) * ((d : ℝ) + 1) * L ^ 3) *
          (1 + (d : ℝ) * B ^ 2)) / r ^ 2 := by field_simp
    change (∫ s in Icc (t - r ^ 2) t, ∫ x in closed, E (x, s)) ≤ _ at henergyω
    rw [he] at henergyω
    calc
      _ ≤ ∫ z in closed ×ˢ Icc (t - r ^ 2) t, E z := by
        apply setIntegral_mono_set
          (by simpa only [Measure.volume_eq_prod] using hEi')
          (ae_of_all _ fun z => Finset.sum_nonneg fun j _ => sq_nonneg _)
          (ae_of_all _ fun _ hz => hΩ hz)
      _ = ∫ s in Icc (t - r ^ 2) t, ∫ x in closed, E (x, s) := by
        rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
        exact integral_prod_symm E (by simpa only [IntegrableOn, ← Measure.prod_restrict] using hEi')
      _ ≤ _ := henergyω
  have hgradEq : (fun z : EinsteinRelation.Vec d × ℝ =>
      ∑ j, ‖H j (z.2, translate z.1 ω)‖ ^ 2) =ᵐ[volume] E := by
    rw [Measure.volume_eq_prod]
    filter_upwards [ae_all_iff.mpr hgrad] with z hz
    exact Finset.sum_congr rfl fun j _ => congrArg (fun v : ℂ => ‖v‖ ^ 2) (hz j)
  dsimp only
  intro θ hθ hθhalf
  have he := hcompω θ hθ hθhalf
  dsimp only [Prod.swap] at he ⊢
  rw [hosc _, hosc _] at he
  rw [integral_congr_ae (ae_restrict_of_ae hgradEq)] at he
  apply he.trans
  apply add_le_add _ le_rfl
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.sqrt_le_sqrt
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact mul_le_mul_of_nonneg_left hEbound (sq_nonneg _)

private theorem holder_forward_forcing_factorization
    {L H r z E : ℝ} (hL : 0 < L) (hH : 0 ≤ H) (hr : 0 < r)
    (hz : 0 ≤ z) (hE : 0 ≤ E) :
    Real.sqrt (r ^ 4 * ((2 * L * z) ^ 2 * (H / r ^ 2 * E)) /
      (L⁻¹ / 10) ^ 2) =
      20 * L ^ 2 * r * z * Real.sqrt H * Real.sqrt E := by
  apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).mpr
  simp only [mul_pow, Real.sq_sqrt hH, Real.sq_sqrt hE]
  field_simp
  ring

/-- Normalizing the comparison forcing costs only a structural cylinder
volume ratio. The energy on the right is a normalized outer-cylinder RMS. -/
theorem holder_forward_normalized_forcing
    {d : ℕ} (x : EinsteinRelation.Vec d) (t : ℝ)
    {r θ L H z C q : ℝ} (hr : 0 < r) (hθ : 0 < θ)
    (hL : 0 < L) (hH : 0 ≤ H) (hz : 0 ≤ z) (hC : 0 ≤ C) (hq : 0 ≤ q)
    (u : ℝ × EinsteinRelation.Vec d → ℂ)
    (hu : IntegrableOn (fun w => ‖u w‖ ^ 2)
      (Icc (t - 2 * r ^ 2) t ×ˢ
        {y : EinsteinRelation.Vec d | euclideanNorm (y - x) ≤ 2 * r})) :
    let cyl := fun ρ : ℝ => Ioo (t - ρ ^ 2) t ×ˢ euclideanBall x ρ
    let outer := Icc (t - 2 * r ^ 2) t ×ˢ
      {y : EinsteinRelation.Vec d | euclideanNorm (y - x) ≤ 2 * r}
    2 * (Real.sqrt ((volume.real (cyl (θ * r)))⁻¹) +
      C * q * Real.sqrt ((volume.real (cyl r))⁻¹)) *
      Real.sqrt (r ^ 4 * ((2 * L * z) ^ 2 *
        (H / r ^ 2 * (∫ s in Icc (t - 2 * r ^ 2) t,
          ∫ y in {y : EinsteinRelation.Vec d | euclideanNorm (y - x) ≤ 2 * r},
            ‖u (s, y)‖ ^ 2))) / (L⁻¹ / 10) ^ 2) ≤
    (40 * L ^ 2 * Real.sqrt H * Real.sqrt (2 * (3 : ℝ) ^ d)) * z * r *
      (Real.sqrt ((θ ^ (d + 2))⁻¹) + C * q) *
        Real.sqrt (⨍ w in outer, ‖u w‖ ^ 2) := by
  intro cyl outer
  let E := ∫ w in outer, ‖u w‖ ^ 2
  have hE : 0 ≤ E := integral_nonneg fun _ => sq_nonneg _
  have hiter : (∫ s in Icc (t - 2 * r ^ 2) t,
      ∫ y in {y : EinsteinRelation.Vec d | euclideanNorm (y - x) ≤ 2 * r},
        ‖u (s, y)‖ ^ 2) = E := by
    change _ = ∫ w in outer, ‖u w‖ ^ 2
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
    exact (integral_prod _ (by simpa only [IntegrableOn,
      Measure.volume_eq_prod, ← Measure.prod_restrict] using hu)).symm
  rw [hiter, holder_forward_forcing_factorization hL hH hr hz hE]
  obtain ⟨hv, hvfin, hvbound⟩ := holder_forward_outer_cylinder_volume x t hr
  change 0 < volume.real outer at hv
  change volume.real outer ≤ _ at hvbound
  have hvr : 0 < volume.real (cyl r) := by
    rw [holder_forward_cylinder_volume x t hr]
    exact mul_pos (pow_pos hr _) (volume_euclideanBall_toReal_pos _ (by norm_num))
  have hvθ : volume.real (cyl (θ * r)) = θ ^ (d + 2) * volume.real (cyl r) := by
    dsimp only [cyl]
    rw [holder_forward_cylinder_volume x t (mul_pos hθ hr),
      holder_forward_cylinder_volume x t hr, mul_pow]
    ring
  have hinv : Real.sqrt ((volume.real (cyl (θ * r)))⁻¹) =
      Real.sqrt ((θ ^ (d + 2))⁻¹) * Real.sqrt ((volume.real (cyl r))⁻¹) := by
    rw [hvθ, mul_inv, Real.sqrt_mul (by positivity)]
  have hscale : Real.sqrt ((volume.real (cyl r))⁻¹) * Real.sqrt E ≤
      Real.sqrt (2 * (3 : ℝ) ^ d) * Real.sqrt (⨍ w in outer, ‖u w‖ ^ 2) := by
    have he : E = volume.real outer * (⨍ w in outer, ‖u w‖ ^ 2) := by
      rw [average_eq, measureReal_restrict_apply_univ, smul_eq_mul]
      dsimp only [E]
      field_simp
    rw [he, Real.sqrt_mul hv.le]
    have hvquot : (volume.real (cyl r))⁻¹ * volume.real outer ≤ 2 * (3 : ℝ) ^ d := by
      apply (inv_mul_le_iff₀ hvr).mpr
      simpa only [mul_comm] using hvbound
    have hs := Real.sqrt_le_sqrt hvquot
    rw [Real.sqrt_mul (by positivity)] at hs
    nlinarith [Real.sqrt_nonneg (⨍ w in outer, ‖u w‖ ^ 2)]
  rw [hinv]
  calc
    _ = (40 * L ^ 2 * Real.sqrt H * z * r *
        (Real.sqrt ((θ ^ (d + 2))⁻¹) + C * q)) *
          (Real.sqrt ((volume.real (cyl r))⁻¹) * Real.sqrt E) := by ring
    _ ≤ (40 * L ^ 2 * Real.sqrt H * z * r *
        (Real.sqrt ((θ ^ (d + 2))⁻¹) + C * q)) *
          (Real.sqrt (2 * (3 : ℝ) ^ d) * Real.sqrt (⨍ w in outer, ‖u w‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left hscale (by positivity)
    _ = _ := by ring

/-- Physical spacetime oscillations of a jointly measurable orbit are
measurable environment random variables, including when an integral vanishes
by the Bochner convention. No regularity of a chosen representative is needed. -/
theorem holder_forward_measurable_oscillation
    {d : ℕ} (U : ℝ × FieldPair d → ℂ) (hU : Measurable U)
    (S : Set (ℝ × EinsteinRelation.Vec d)) :
    Measurable (fun ω => Real.sqrt (⨍ z in S,
      ‖U (z.1, translate z.2 ω) -
        (⨍ w in S, U (w.1, translate w.2 ω))‖ ^ 2)) := by
  let F : FieldPair d × (ℝ × EinsteinRelation.Vec d) → ℂ :=
    fun z => U (z.2.1, translate z.2.2 z.1)
  have hF : Measurable F :=
    hU.comp (measurable_snd.fst.prodMk
      (Probability.continuous_translate.measurable.comp
        (measurable_snd.snd.prodMk measurable_fst)))
  have hm : Measurable (fun ω => ⨍ z in S, F (ω, z)) := by
    simp only [average_eq]
    exact (hF.stronglyMeasurable.integral_prod_right').measurable.const_smul _
  have hG : Measurable (fun z : FieldPair d × (ℝ × EinsteinRelation.Vec d) =>
      ‖F z - (⨍ w in S, F (z.1, w))‖ ^ 2) :=
    (hF.sub (hm.comp measurable_fst)).norm.pow_const 2
  have hi := hG.stronglyMeasurable.integral_prod_right' (ν := volume.restrict S)
  simpa only [average_eq, F, Function.comp_def, Pi.smul_apply] using
    Real.continuous_sqrt.measurable.comp (hi.measurable.const_smul
      ((volume.restrict S).real univ)⁻¹)

/-- A normalized oscillation has the same uniform environment Lp bound as
the orbit's RMS. Local L2 integrability is explicit, so the minimizing property
of the complex mean is applied to the actual physical section. -/
theorem holder_forward_window_oscillation_bound
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    {p M a b : ℝ} (hp : 2 ≤ p) (hM : 0 ≤ M)
    (U : ℝ × FieldPair d → ℂ) (hU : Measurable U)
    (hwindow : ∀ s ∈ Icc a b,
      MemLp (fun ω => U (s, ω)) (ENNReal.ofReal p) (reducedLaw Q) ∧
      eLpNorm (fun ω => U (s, ω)) (ENNReal.ofReal p) (reducedLaw Q) ≤
        ENNReal.ofReal M)
    (S : Set (ℝ × EinsteinRelation.Vec d)) (hS : MeasurableSet S)
    (hS0 : volume S ≠ 0) (hSfin : volume S ≠ ⊤)
    (hSt : ∀ z ∈ S, z.1 ∈ Icc a b)
    (hlocal : ∀ᵐ ω ∂reducedLaw Q,
      MemLp (fun z => U (z.1, translate z.2 ω)) 2 (volume.restrict S)) :
    MemLp (fun ω => Real.sqrt (⨍ z in S,
      ‖U (z.1, translate z.2 ω) -
        (⨍ w in S, U (w.1, translate w.2 ω))‖ ^ 2))
      (ENNReal.ofReal p) (reducedLaw Q) ∧
    eLpNorm (fun ω => Real.sqrt (⨍ z in S,
      ‖U (z.1, translate z.2 ω) -
        (⨍ w in S, U (w.1, translate w.2 ω))‖ ^ 2))
      (ENNReal.ofReal p) (reducedLaw Q) ≤ ENNReal.ofReal M := by
  haveI : IsFiniteMeasure (volume.restrict S) := ⟨by simpa using hSfin.lt_top⟩
  obtain ⟨hrms, hnrms⟩ := holder_forward_window_rms_bound Q hp hM U hU
    hwindow S hS hS0 hSfin hSt
  have hosc := holder_forward_measurable_oscillation U hU S
  have hle : ∀ᵐ ω ∂reducedLaw Q,
      ‖Real.sqrt (⨍ z in S, ‖U (z.1, translate z.2 ω) -
        (⨍ w in S, U (w.1, translate w.2 ω))‖ ^ 2)‖ ≤
      ‖Real.sqrt (⨍ z in S, ‖U (z.1, translate z.2 ω)‖ ^ 2)‖ := by
    filter_upwards [hlocal] with ω hω
    simp only [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    apply Real.sqrt_le_sqrt
    simpa only [sub_zero] using holder_complex_mean_minimizes hω 0
  exact ⟨hrms.of_le hosc.aestronglyMeasurable hle,
    (eLpNorm_mono_ae hosc.aestronglyMeasurable hle).trans hnrms⟩

/-- Every measurable representative of the actual corrected orbit is
locally L2 on physical spacetime sections. This version needs no separately
chosen gradient representative. -/
theorem holder_forward_corrected_locally_memLp
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) (f : Lp ℂ 2 (reducedLaw Q))
    (t a b : ℝ) (W : ℝ × FieldPair d → ℂ) (hW : Measurable W)
    (heW : ∀ s, (fun ω => W (s, ω)) =ᵐ[reducedLaw Q]
      (fun ω => centeredComplexLp Q (P s.toNNReal f) ω +
        ∫ v in (t / 4)..s, hP.centeringSource f v)) :
    ∀ᵐ ω ∂reducedLaw Q, ∀ K : Set (EinsteinRelation.Vec d), IsCompact K →
      MemLp (fun z : EinsteinRelation.Vec d × ℝ => W (z.2, translate z.1 ω)) 2
        ((volume.restrict K).prod (volume.restrict (Icc a b))) := by
  letI := reducedLaw_probability Q
  let w : ℝ → Lp ℂ 2 (reducedLaw Q) := fun s =>
    centeredComplexLp Q (P s.toNNReal f) +
      Lp.const 2 (reducedLaw Q) (∫ v in (t / 4)..s, hP.centeringSource f v)
  have hw : Continuous w := by
    have hu : Continuous (fun s : ℝ => centeredComplexLp Q (P s.toNNReal f)) :=
      by simpa only [Function.comp_def, centeredComplexLpCLM_apply] using
        (centeredComplexLpCLM Q).continuous.comp ((hP.2.2.1 f).comp continuous_real_toNNReal)
    exact hu.add ((Lp.constL 2 (reducedLaw Q) ℂ).continuous.comp
      (continuous_centered_source_primitive hP f (t / 4)))
  have he (s : ℝ) : (fun ω => W (s, ω)) =ᵐ[reducedLaw Q] w s := by
    filter_upwards [heW s, Lp.coeFn_add (centeredComplexLp Q (P s.toNNReal f))
      (Lp.const 2 (reducedLaw Q) (∫ v in (t / 4)..s, hP.centeringSource f v)),
      Lp.coeFn_const 2 (reducedLaw Q) (∫ v in (t / 4)..s, hP.centeringSource f v)]
      with ω hω hadd hconst
    exact hω.trans (by simp only [w, hadd, Pi.add_apply, hconst, Function.const_apply])
  exact holderComparison_ae_locally_memLp_joint_spatial_translate (reducedLaw Q)
    (reducedLaw_stationary Q) hW
    (holderComparison_integrable_sq_joint_l2_representative
      ((hw.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc) hW he)

/-- The actual forward comparison after geometric normalization. Its forcing
is linear in radius and multiplies a normalized RMS, with structural constants
chosen before the environment, force and orbit. -/
theorem holder_forward_normalized_comparison
    (hinterior : node_e_u3A_holder_u2D_average_u23_unforced_u2D_interiorStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ α C N : ℝ, 0 < α ∧ α < 1 ∧ 1 ≤ C ∧ 0 < N ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange),
      HasSmoothBounds D Q → ∀ (i : Fin d) (ζ : ℂ)
      (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
      ∀ (hP : IsComplexEnvironmentSemigroup Q i ζ P)
      (f : Lp ℂ 2 (reducedLaw Q)) (t : ℝ), 0 < t →
      ∃ W : ℝ × FieldPair d → ℂ, Measurable W ∧
      (∀ s, (fun ω => W (s, ω)) =ᵐ[reducedLaw Q]
        (fun ω => centeredComplexLp Q (P s.toNNReal (centeredComplexLp Q f)) ω +
          ∫ v in (t / 4)..s, hP.centeringSource (centeredComplexLp Q f) v)) ∧
      ∀ (x : EinsteinRelation.Vec d) (r : ℝ), 0 < r → t / 8 < t - 2 * r ^ 2 →
        r ≤ Real.sqrt t / (1 + ‖ζ‖ * Real.sqrt t) →
      ∀ᵐ ω ∂reducedLaw Q,
      let u := fun z : ℝ × EinsteinRelation.Vec d => W (z.1, translate z.2 ω)
      let cyl := fun ρ : ℝ => Ioo (t - ρ ^ 2) t ×ˢ euclideanBall x ρ
      let outer := Icc (t - 2 * r ^ 2) t ×ˢ
        {y : EinsteinRelation.Vec d | euclideanNorm (y - x) ≤ 2 * r}
      ∀ θ : ℝ, 0 < θ → θ ≤ 1 / 2 →
      Real.sqrt (⨍ z in cyl (θ * r), ‖u z - (⨍ w in cyl (θ * r), u w)‖ ^ 2) ≤
        N * ‖ζ‖ * r * (Real.sqrt ((θ ^ (d + 2))⁻¹) + C * θ ^ α) *
          Real.sqrt (⨍ z in outer, ‖u z‖ ^ 2) +
        2 * C * θ ^ α * Real.sqrt (⨍ z in cyl r, ‖u z - (⨍ w in cyl r, u w)‖ ^ 2) := by
  obtain ⟨α, C, B, hα, hα1, hC, hB, hcomp⟩ :=
    holder_forward_energy_comparison hinterior d hd D
  let L := Real.exp (2 * D.ellipticity) * D.ellipticity
  let H := 16 * L * (1 / 2 +
    (2 * (d : ℝ) * ((d : ℝ) + 1) * L ^ 3) * (1 + (d : ℝ) * B ^ 2))
  have hL : 0 < L := mul_pos (Real.exp_pos _) (zero_lt_one.trans_le D.one_le_ellipticity)
  have hH : 0 < H := by dsimp only [H]; positivity
  let N := 40 * L ^ 2 * Real.sqrt H * Real.sqrt (2 * (3 : ℝ) ^ d)
  refine ⟨α, C, N, hα, hα1, hC, by dsimp only [N]; positivity, ?_⟩
  intro Q hQ i ζ P hP f t ht
  obtain ⟨W, hW, heW, hc⟩ := hcomp Q hQ i ζ P hP f t ht
  refine ⟨W, hW, heW, ?_⟩
  intro x r hr htime hrad
  have hloc := holder_forward_corrected_locally_memLp hP (centeredComplexLp Q f)
    t (t - 2 * r ^ 2) t W hW heW
  filter_upwards [hc x r hr htime hrad, hloc] with ω hcω hω
  dsimp only
  intro θ hθ hθhalf
  have hu := (hω _ (isCompact_physical_euclidean_closedBall x (2 * r))).comp_measurePreserving
    (Measure.measurePreserving_swap (μ := volume.restrict (Icc (t - 2 * r ^ 2) t))
      (ν := volume.restrict {y : EinsteinRelation.Vec d | euclideanNorm (y - x) ≤ 2 * r}))
  have hui : IntegrableOn (fun z : ℝ × EinsteinRelation.Vec d =>
      ‖W (z.1, translate z.2 ω)‖ ^ 2)
      (Icc (t - 2 * r ^ 2) t ×ˢ
        {y : EinsteinRelation.Vec d | euclideanNorm (y - x) ≤ 2 * r}) := by
    unfold IntegrableOn
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
    exact (memLp_two_iff_integrable_sq_norm hu.aestronglyMeasurable).mp hu
  have hnorm := holder_forward_normalized_forcing x t hr hθ hL hH.le
    (norm_nonneg ζ) (zero_le_one.trans hC) (Real.rpow_nonneg hθ.le α)
    (fun z => W (z.1, translate z.2 ω)) hui
  have hcoeff : 16 * L * ((1 / 2 +
      (2 * (d : ℝ) * ((d : ℝ) + 1) * L ^ 3) * (1 + (d : ℝ) * B ^ 2)) / r ^ 2) =
      H / r ^ 2 := by dsimp only [H]; ring
  have hcθ := hcω θ hθ hθhalf
  dsimp only at hcθ hnorm
  change _ ≤ _ at hcθ
  change _ ≤ N * ‖ζ‖ * r * (Real.sqrt ((θ ^ (d + 2))⁻¹) + C * θ ^ α) * _ at hnorm
  simp only [← hcoeff] at hnorm
  exact hcθ.trans (add_le_add hnorm le_rfl)

/-- Taking environment norms in the actual normalized comparison gives an
inhomogeneous oscillation recurrence. The exponent and contraction constants
are chosen before p; the window bound can be supplied by
`holder_forward_actual_window_bound`. -/
theorem holder_forward_lp_recurrence
    (hinterior : node_e_u3A_holder_u2D_average_u23_unforced_u2D_interiorStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ α C N : ℝ, 0 < α ∧ α < 1 ∧ 1 ≤ C ∧ 0 < N ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange),
      HasSmoothBounds D Q → ∀ (i : Fin d) (ζ : ℂ)
      (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
      ∀ (hP : IsComplexEnvironmentSemigroup Q i ζ P)
      (f : Lp ℂ 2 (reducedLaw Q)) (t : ℝ), 0 < t →
      ∃ W : ℝ × FieldPair d → ℂ, Measurable W ∧
      (∀ s, (fun ω => W (s, ω)) =ᵐ[reducedLaw Q]
        (fun ω => centeredComplexLp Q (P s.toNNReal (centeredComplexLp Q f)) ω +
          ∫ v in (t / 4)..s, hP.centeringSource (centeredComplexLp Q f) v)) ∧
      ∀ p M : ℝ, 2 ≤ p → 0 ≤ M →
      (∀ s ∈ Icc (t / 4) t,
        MemLp (fun ω => W (s, ω)) (ENNReal.ofReal p) (reducedLaw Q) ∧
        eLpNorm (fun ω => W (s, ω)) (ENNReal.ofReal p) (reducedLaw Q) ≤ ENNReal.ofReal M) →
      ∀ (x : EinsteinRelation.Vec d) (r : ℝ), 0 < r → t / 4 ≤ t - 2 * r ^ 2 →
        r ≤ Real.sqrt t / (1 + ‖ζ‖ * Real.sqrt t) →
      ∀ θ : ℝ, 0 < θ → θ ≤ 1 / 2 →
      let osc := fun ρ ω => Real.sqrt (⨍ z in Ioo (t - ρ ^ 2) t ×ˢ euclideanBall x ρ,
        ‖W (z.1, translate z.2 ω) -
          (⨍ w in Ioo (t - ρ ^ 2) t ×ˢ euclideanBall x ρ,
            W (w.1, translate w.2 ω))‖ ^ 2)
      MemLp (osc (θ * r)) (ENNReal.ofReal p) (reducedLaw Q) ∧
      MemLp (osc r) (ENNReal.ofReal p) (reducedLaw Q) ∧
      (eLpNorm (osc (θ * r)) (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
        2 * C * θ ^ α * (eLpNorm (osc r) (ENNReal.ofReal p) (reducedLaw Q)).toReal +
          N * ‖ζ‖ * r * (Real.sqrt ((θ ^ (d + 2))⁻¹) + C * θ ^ α) * M := by
  obtain ⟨α, C, N, hα, hα1, hC, hN, hcomp⟩ :=
    holder_forward_normalized_comparison hinterior d hd D
  refine ⟨α, C, N, hα, hα1, hC, hN, ?_⟩
  intro Q hQ i ζ P hP f t ht
  obtain ⟨W, hW, heW, hc⟩ := hcomp Q hQ i ζ P hP f t ht
  refine ⟨W, hW, heW, ?_⟩
  intro p M hp hM hwindow x r hr htime hrad θ hθ hθhalf osc
  letI := reducedLaw_probability Q
  let outer := Icc (t - 2 * r ^ 2) t ×ˢ
    {y : EinsteinRelation.Vec d | euclideanNorm (y - x) ≤ 2 * r}
  let cyl := fun ρ : ℝ => Ioo (t - ρ ^ 2) t ×ˢ euclideanBall x ρ
  let rms := fun ω => Real.sqrt (⨍ z in outer, ‖W (z.1, translate z.2 ω)‖ ^ 2)
  have houter : MeasurableSet outer :=
    measurableSet_Icc.prod (isCompact_physical_euclidean_closedBall x (2 * r)).measurableSet
  obtain ⟨hvpos, hvfin, _⟩ := holder_forward_outer_cylinder_volume x t hr
  have hv0 : volume outer ≠ 0 := by
    intro hz
    change 0 < (volume outer).toReal at hvpos
    simpa only [hz, ENNReal.toReal_zero, lt_self_iff_false] using hvpos
  have houtertime : ∀ z ∈ outer, z.1 ∈ Icc (t / 4) t :=
    fun z hz => ⟨htime.trans hz.1.1, hz.1.2⟩
  obtain ⟨hrms, hnrms⟩ := holder_forward_window_rms_bound Q hp hM W hW hwindow
    outer houter hv0 hvfin houtertime
  have hloc := holder_forward_corrected_locally_memLp hP (centeredComplexLp Q f)
    t (t - 2 * r ^ 2) t W hW heW
  have hosc (ρ : ℝ) (hρ : 0 < ρ) (hρr : ρ ≤ r) :
      MemLp (osc ρ) (ENNReal.ofReal p) (reducedLaw Q) ∧
      eLpNorm (osc ρ) (ENNReal.ofReal p) (reducedLaw Q) ≤ ENNReal.ofReal M := by
    have hsub : cyl ρ ⊆ outer := by
      intro z hz
      have htρ : t - 2 * r ^ 2 ≤ t - ρ ^ 2 := by nlinarith [sq_nonneg (r - ρ)]
      refine ⟨⟨htρ.trans hz.1.1.le, hz.1.2.le⟩, ?_⟩
      have hy := (mem_euclideanBall_iff_vecEuclideanNorm_lt hρ).mp hz.2
      change euclideanNorm (z.2 - x) ≤ 2 * r
      change euclideanNorm (z.2 - x) < ρ at hy
      linarith
    have hfin : volume (cyl ρ) ≠ ⊤ := ne_top_of_le_ne_top hvfin (measure_mono hsub)
    have hpos : 0 < volume.real (cyl ρ) := by
      rw [holder_forward_cylinder_volume x t hρ]
      exact mul_pos (pow_pos hρ _) (volume_euclideanBall_toReal_pos _ (by norm_num))
    have hzero : volume (cyl ρ) ≠ 0 := by
      intro hz
      change 0 < (volume (cyl ρ)).toReal at hpos
      simpa only [hz, ENNReal.toReal_zero, lt_self_iff_false] using hpos
    have hlocal : ∀ᵐ ω ∂reducedLaw Q,
        MemLp (fun z : ℝ × EinsteinRelation.Vec d => W (z.1, translate z.2 ω)) 2
          (volume.restrict (cyl ρ)) := by
      filter_upwards [hloc] with ω hω
      have hu := (hω _ (isCompact_physical_euclidean_closedBall x (2 * r))).comp_measurePreserving
        (Measure.measurePreserving_swap (μ := volume.restrict (Icc (t - 2 * r ^ 2) t))
          (ν := volume.restrict {y : EinsteinRelation.Vec d | euclideanNorm (y - x) ≤ 2 * r}))
      have hu' : MemLp (fun z : ℝ × EinsteinRelation.Vec d => W (z.1, translate z.2 ω)) 2
          (volume.restrict outer) := by
        dsimp only [outer]
        rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
        exact hu
      exact hu'.mono_measure (Measure.restrict_mono hsub le_rfl)
    exact holder_forward_window_oscillation_bound Q hp hM W hW hwindow
      (cyl ρ) (measurableSet_Ioo.prod (isOpen_euclideanBall x ρ).measurableSet)
      hzero hfin (fun z hz => houtertime z (hsub hz)) hlocal
  have hθr : θ * r ≤ r := by nlinarith
  obtain ⟨hsmall, _⟩ := hosc (θ * r) (mul_pos hθ hr) hθr
  obtain ⟨hlarge, _⟩ := hosc r hr le_rfl
  refine ⟨hsmall, hlarge, ?_⟩
  let a := 2 * C * θ ^ α
  let b := N * ‖ζ‖ * r * (Real.sqrt ((θ ^ (d + 2))⁻¹) + C * θ ^ α)
  have ha : 0 ≤ a := by dsimp only [a]; positivity
  have hb : 0 ≤ b := by dsimp only [b]; positivity
  have hpoint : ∀ᵐ ω ∂reducedLaw Q, ‖osc (θ * r) ω‖ ≤
      ‖(a • osc r + b • rms) ω‖ := by
    filter_upwards [hc x r hr (by linarith) hrad] with ω hω
    have he := hω θ hθ hθhalf
    have hnlarge : 0 ≤ osc r ω := Real.sqrt_nonneg _
    have hnrms' : 0 ≤ rms ω := Real.sqrt_nonneg _
    change ‖osc (θ * r) ω‖ ≤ ‖a * osc r ω + b * rms ω‖
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _),
      abs_of_nonneg (by positivity : 0 ≤ a * osc r ω + b * rms ω)]
    change osc (θ * r) ω ≤ b * rms ω + a * osc r ω at he
    exact he.trans_eq (add_comm _ _)
  have hnorm : eLpNorm (osc (θ * r)) (ENNReal.ofReal p) (reducedLaw Q) ≤
      ENNReal.ofReal a * eLpNorm (osc r) (ENNReal.ofReal p) (reducedLaw Q) +
        ENNReal.ofReal b * ENNReal.ofReal M := by
    calc
      _ ≤ eLpNorm (a • osc r + b • rms) (ENNReal.ofReal p) (reducedLaw Q) :=
        eLpNorm_mono_ae hsmall.aestronglyMeasurable hpoint
      _ ≤ eLpNorm (a • osc r) (ENNReal.ofReal p) (reducedLaw Q) +
          eLpNorm (b • rms) (ENNReal.ofReal p) (reducedLaw Q) :=
        eLpNorm_add_le (ENNReal.one_le_ofReal.mpr (by linarith))
      _ = ENNReal.ofReal a * eLpNorm (osc r) (ENNReal.ofReal p) (reducedLaw Q) +
          ENNReal.ofReal b * eLpNorm rms (ENNReal.ofReal p) (reducedLaw Q) := by
        simp only [eLpNorm_const_smul, Real.enorm_of_nonneg ha, Real.enorm_of_nonneg hb]
      _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left hnrms (by positivity))
  have hbound : eLpNorm (osc (θ * r)) (ENNReal.ofReal p) (reducedLaw Q) ≤
      ENNReal.ofReal (a * (eLpNorm (osc r) (ENNReal.ofReal p) (reducedLaw Q)).toReal + b * M) := by
    rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul ha,
      ENNReal.ofReal_mul hb, ENNReal.ofReal_toReal hlarge.eLpNorm_ne_top]
    exact hnorm
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound).trans_eq
    (ENNReal.toReal_ofReal (by positivity))

/-- The unforced exponent selects a structural scale at which both the
oscillation coefficient and the radius shrink faster than the desired decay. -/
theorem holder_forward_structural_scales (C α : ℝ)
    (hC : 1 ≤ C) (hα : 0 < α) (hα1 : α < 1) :
    ∃ θ : ℝ, 0 < θ ∧ θ ≤ 1 / 2 ∧
      θ < θ ^ (α / 2) ∧ 2 * C * θ ^ α < θ ^ (α / 2) ∧ θ ^ (α / 2) < 1 := by
  obtain ⟨θ, c, hθ, hθhalf, hc, hbound⟩ :=
    holder_comparison_scales 0 (2 * C) α (by linarith only [hC]) hα
  have ha := hbound 0 1 (by linarith only [hc])
  simp only [zero_mul, mul_zero, add_zero] at ha
  have hhalf : 0 < α / 2 := by linarith only [hα]
  have hθ1 : θ < 1 := by linarith only [hθhalf]
  refine ⟨θ, hθ, hθhalf,
    Real.self_lt_rpow_of_lt_one hθ hθ1 (by linarith only [hα1]), ?_, ?_⟩
  · exact ha.trans_lt (Real.rpow_lt_rpow (by positivity) (by linarith only [hθ]) hhalf)
  · exact Real.rpow_lt_one hθ.le hθ1 hhalf


/-- The actual forward corrected orbit has geometric oscillation decay in
all finite environment moments. Structural witnesses precede the moment order. -/
theorem holder_forward_lp_geometric_decay
    (hinterior : node_e_u3A_holder_u2D_average_u23_unforced_u2D_interiorStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ α θ K : ℝ, 0 < α ∧ α < 1 ∧ 0 < θ ∧ θ ≤ 1 / 2 ∧ 1 ≤ K ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange),
      HasSmoothBounds D Q → ∀ (i : Fin d) (ζ : ℂ)
      (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
      ∀ (hP : IsComplexEnvironmentSemigroup Q i ζ P)
      (f : Lp ℂ 2 (reducedLaw Q)) (t : ℝ), 0 < t →
      ∃ W : ℝ × FieldPair d → ℂ, Measurable W ∧
      (∀ s, (fun ω => W (s, ω)) =ᵐ[reducedLaw Q]
        (fun ω => centeredComplexLp Q (P s.toNNReal (centeredComplexLp Q f)) ω +
          ∫ v in (t / 4)..s, hP.centeringSource (centeredComplexLp Q f) v)) ∧
      ∀ p M : ℝ, 2 ≤ p → 0 ≤ M →
      (∀ s ∈ Icc (t / 4) t,
        MemLp (fun ω => W (s, ω)) (ENNReal.ofReal p) (reducedLaw Q) ∧
        eLpNorm (fun ω => W (s, ω)) (ENNReal.ofReal p) (reducedLaw Q) ≤ ENNReal.ofReal M) →
      ∀ (x : EinsteinRelation.Vec d) (R : ℝ), 0 < R → t / 4 ≤ t - 2 * R ^ 2 →
        R ≤ Real.sqrt t / (1 + ‖ζ‖ * Real.sqrt t) →
      ∀ n : ℕ,
      let r := θ ^ n * R
      let osc := fun ω => Real.sqrt
        (⨍ z in Ioo (t - r ^ 2) t ×ˢ euclideanBall x r,
          ‖W (z.1, translate z.2 ω) -
            (⨍ w in Ioo (t - r ^ 2) t ×ˢ euclideanBall x r,
              W (w.1, translate w.2 ω))‖ ^ 2)
      MemLp osc (ENNReal.ofReal p) (reducedLaw Q) ∧
      (eLpNorm osc (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
        K * (θ ^ α) ^ n * (1 + ‖ζ‖ * R) * M := by
  obtain ⟨β, C, N, hβ, hβ1, hC, hN, hrec⟩ :=
    holder_forward_lp_recurrence hinterior d hd D
  obtain ⟨θ, hθ, hθhalf, hθκ, haκ, hκ1⟩ :=
    holder_forward_structural_scales C β hC hβ hβ1
  let κ := θ ^ (β / 2)
  let A := 2 * C * θ ^ β
  let S := Real.sqrt ((θ ^ (d + 2))⁻¹) + C * θ ^ β
  let K := 1 + N * S / (κ - A)
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hS : 0 ≤ S := by dsimp only [S]; positivity
  have hden : 0 < κ - A := sub_pos.mpr haκ
  have hK : 1 ≤ K := by
    dsimp only [K]
    exact le_add_of_nonneg_right (div_nonneg (mul_nonneg hN.le hS) hden.le)
  refine ⟨β / 2, θ, K, by linarith, by linarith, hθ, hθhalf, hK, ?_⟩
  intro Q hQ i ζ P hP f t ht
  obtain ⟨W, hW, heW, hrec⟩ := hrec Q hQ i ζ P hP f t ht
  refine ⟨W, hW, heW, ?_⟩
  intro p M hp hM hwindow x R hR htime hforce
  let cyl := fun r : ℝ => Ioo (t - r ^ 2) t ×ˢ euclideanBall x r
  let osc := fun r ω => Real.sqrt (⨍ z in cyl r,
    ‖W (z.1, translate z.2 ω) - (⨍ w in cyl r, W (w.1, translate w.2 ω))‖ ^ 2)
  let E := fun n : ℕ => (eLpNorm (osc (θ ^ n * R))
    (ENNReal.ofReal p) (reducedLaw Q)).toReal
  have hrpos (n : ℕ) : 0 < θ ^ n * R := mul_pos (pow_pos hθ _) hR
  have hrle (n : ℕ) : θ ^ n * R ≤ R :=
    mul_le_of_le_one_left hR.le (pow_le_one₀ hθ.le (by linarith))
  have hrad (n : ℕ) : (θ ^ n * R) ^ 2 ≤ R ^ 2 :=
    (sq_le_sq₀ (hrpos n).le hR.le).mpr (hrle n)
  have hrecn (n : ℕ) := hrec p M hp hM hwindow x (θ ^ n * R) (hrpos n)
    (by linarith [hrad n]) ((hrle n).trans hforce) θ hθ hθhalf
  have hmem (n : ℕ) : MemLp (osc (θ ^ n * R))
      (ENNReal.ofReal p) (reducedLaw Q) := (hrecn n).2.1
  have hbase : E 0 ≤ M := by
    let box := Icc (t / 4) t ×ˢ {y : EinsteinRelation.Vec d | euclideanNorm (y - x) ≤ R}
    have hsub : cyl R ⊆ box := by
      intro z hz
      refine ⟨⟨by dsimp only [cyl] at hz; nlinarith [hz.1.1], hz.1.2.le⟩, ?_⟩
      exact ((mem_euclideanBall_iff_vecEuclideanNorm_lt hR).mp hz.2).le
    have hfin : volume (cyl R) ≠ ⊤ :=
      ((measure_mono hsub).trans_lt
        ((isCompact_Icc.prod (isCompact_physical_euclidean_closedBall x R)).measure_lt_top)).ne
    have hzero : volume (cyl R) ≠ 0 := by
      have hpos : 0 < volume.real (cyl R) := by
        rw [holder_forward_cylinder_volume x t hR]
        exact mul_pos (pow_pos hR _) (volume_euclideanBall_toReal_pos _ (by norm_num))
      intro hz
      simpa only [measureReal_def, hz, ENNReal.toReal_zero, lt_self_iff_false] using hpos
    have hlocal : ∀ᵐ ω ∂reducedLaw Q,
        MemLp (fun z : ℝ × EinsteinRelation.Vec d => W (z.1, translate z.2 ω)) 2
          (volume.restrict (cyl R)) := by
      filter_upwards [holder_forward_corrected_locally_memLp hP (centeredComplexLp Q f)
        t (t / 4) t W hW heW] with ω hω
      have hu := (hω _ (isCompact_physical_euclidean_closedBall x R)).comp_measurePreserving
        (Measure.measurePreserving_swap (μ := volume.restrict (Icc (t / 4) t))
          (ν := volume.restrict {y : EinsteinRelation.Vec d | euclideanNorm (y - x) ≤ R}))
      have hu' : MemLp (fun z : ℝ × EinsteinRelation.Vec d => W (z.1, translate z.2 ω)) 2
          (volume.restrict box) := by
        dsimp only [box]
        rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
        exact hu
      exact hu'.mono_measure (Measure.restrict_mono hsub le_rfl)
    have hbound := (holder_forward_window_oscillation_bound Q hp hM W hW hwindow
      (cyl R) (measurableSet_Ioo.prod (isOpen_euclideanBall x R).measurableSet)
      hzero hfin (fun z hz => (hsub hz).1) hlocal).2
    have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
    simpa only [E, pow_zero, one_mul, ENNReal.toReal_ofReal hM] using hreal
  let B := N * ‖ζ‖ * R * S * M
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hstep (n : ℕ) : E (n + 1) ≤ A * E n + B * θ ^ n := by
    have he := (hrecn n).2.2
    have hradius : θ * (θ ^ n * R) = θ ^ (n + 1) * R := by rw [pow_succ]; ring
    change (eLpNorm (osc (θ * (θ ^ n * R))) _ _).toReal ≤ _ at he
    rw [hradius] at he
    convert he using 1 <;> dsimp only [E, A, B, S] <;> ring
  have hdecay := holder_forward_inhomogeneous_iteration E hA hθ.le
    hθκ.le haκ hB ENNReal.toReal_nonneg hstep
  intro n
  refine ⟨hmem n, (hdecay n).trans ?_⟩
  have hcoeff : E 0 + B / (κ - A) ≤ K * (1 + ‖ζ‖ * R) * M := by
    have heq : B / (κ - A) = (N * S / (κ - A)) * (‖ζ‖ * R) * M := by
      dsimp only [B]; ring
    rw [heq]
    dsimp only [K]
    have hnonneg : 0 ≤ (N * S / (κ - A)) * M := by positivity
    nlinarith only [hbase, hnonneg, mul_nonneg (norm_nonneg ζ) hR.le,
      mul_nonneg (mul_nonneg (norm_nonneg ζ) hR.le) hM]
  calc
    κ ^ n * (E 0 + B / (κ - A)) ≤ κ ^ n * (K * (1 + ‖ζ‖ * R) * M) :=
      mul_le_mul_of_nonneg_left hcoeff (pow_nonneg (hθ.le.trans hθκ.le) n)
    _ = K * (θ ^ (β / 2)) ^ n * (1 + ‖ζ‖ * R) * M := by ring


/-- The structural geometric decay applies to the actual corrected orbit with
the time-window moment supplied solely by growth and the centered-source input. -/
theorem holder_forward_actual_geometric_decay
    (hgrowth : node_e_u3A_lp_u2D_growthStmt)
    (hsource : node_l_u3A_forced_u2D_local_u23_centered_u2D_sourceStmt)
    (hinterior : node_e_u3A_holder_u2D_average_u23_unforced_u2D_interiorStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ α θ K Cs : ℝ, 0 < α ∧ α < 1 ∧ 0 < θ ∧ θ ≤ 1 / 2 ∧ 1 ≤ K ∧ 0 < Cs ∧
    ∀ p : ℝ, 2 ≤ p → ∃ Cg : ℝ, 0 < Cg ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange),
      HasSmoothBounds D Q → ∀ (ζ : ℂ)
      (P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
      ∀ (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P),
      IsComplexTransposeSemigroup Q P T →
      ∀ f : Lp ℂ 2 (reducedLaw Q), MemLp f (ENNReal.ofReal p) (reducedLaw Q) →
      ∀ t : ℝ, 0 < t →
      let u := fun s : ℝ => centeredComplexLp Q (P s.toNNReal (centeredComplexLp Q f))
      MemLp (u (t / 8)) (ENNReal.ofReal p) (reducedLaw Q) ∧
      ∃ W : ℝ × FieldPair d → ℂ, Measurable W ∧
      (∀ s, (fun ω => W (s, ω)) =ᵐ[reducedLaw Q]
        (fun ω => u s ω + ∫ v in (t / 4)..s,
          hP.centeringSource (centeredComplexLp Q f) v)) ∧
      ∀ (x : EinsteinRelation.Vec d) (R : ℝ), 0 < R → t / 4 ≤ t - 2 * R ^ 2 →
        R ≤ Real.sqrt t / (1 + ‖ζ‖ * Real.sqrt t) →
      ∀ n : ℕ,
      let r := θ ^ n * R
      let osc := fun ω => Real.sqrt
        (⨍ z in Ioo (t - r ^ 2) t ×ˢ euclideanBall x r,
          ‖W (z.1, translate z.2 ω) -
            (⨍ w in Ioo (t - r ^ 2) t ×ˢ euclideanBall x r,
              W (w.1, translate w.2 ω))‖ ^ 2)
      MemLp osc (ENNReal.ofReal p) (reducedLaw Q) ∧
      (eLpNorm osc (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
        K * (θ ^ α) ^ n * (1 + ‖ζ‖ * R) *
          ((2 * Real.exp (Cg * ‖ζ‖ ^ 2 * t) +
              Cs * ‖ζ‖ * Real.sqrt t * Real.exp (Cs * ‖ζ‖ ^ 2 * t)) *
            (eLpNorm (u (t / 8)) (ENNReal.ofReal p) (reducedLaw Q)).toReal) := by
  obtain ⟨α, θ, K, hα, hα1, hθ, hθhalf, hK, hdecay⟩ :=
    holder_forward_lp_geometric_decay hinterior d hd D
  obtain ⟨Cs, hCs, hwindow⟩ := holder_forward_actual_window_bound hgrowth hsource d hd D
  refine ⟨α, θ, K, Cs, hα, hα1, hθ, hθhalf, hK, hCs, ?_⟩
  intro p hp
  obtain ⟨Cg, hCg, hwindow⟩ := hwindow p hp
  refine ⟨Cg, hCg, ?_⟩
  intro Q hQ ζ P T hP hT f hf t ht u
  obtain ⟨W, hW, heW, hdecay⟩ := hdecay Q hQ ⟨0, by omega⟩ ζ P hP f t ht
  obtain ⟨hu8, hwindow⟩ := hwindow Q hQ ζ P T hP hT f hf t ht
  refine ⟨hu8, W, hW, heW, ?_⟩
  let F := 2 * Real.exp (Cg * ‖ζ‖ ^ 2 * t) +
    Cs * ‖ζ‖ * Real.sqrt t * Real.exp (Cs * ‖ζ‖ ^ 2 * t)
  let M := F * (eLpNorm (u (t / 8)) (ENNReal.ofReal p) (reducedLaw Q)).toReal
  have hF : 0 ≤ F := by dsimp only [F]; positivity
  have hM : 0 ≤ M := mul_nonneg hF ENNReal.toReal_nonneg
  have hnorm : ∀ s ∈ Icc (t / 4) t,
      MemLp (fun ω => W (s, ω)) (ENNReal.ofReal p) (reducedLaw Q) ∧
      eLpNorm (fun ω => W (s, ω)) (ENNReal.ofReal p) (reducedLaw Q) ≤ ENNReal.ofReal M := by
    intro s hs
    obtain ⟨hm, hb⟩ := hwindow W heW s hs
    refine ⟨hm, ?_⟩
    dsimp only [M]
    rw [ENNReal.ofReal_mul hF, ENNReal.ofReal_toReal hu8.eLpNorm_ne_top]
    exact hb
  exact hdecay p M hp hM hnorm

/-- Geometric bounds for successive environment-Lp means give a uniform
quantitative tail estimate, before any limit is identified. -/
theorem holder_forward_mean_telescope
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {p A κ : ℝ} (hp : 2 ≤ p) (hA : 0 ≤ A) (hκ : 0 ≤ κ) (hκ1 : κ < 1)
    (m : ℕ → Ω → ℂ)
    (hmem : ∀ n, MemLp (m (n + 1) - m n) (ENNReal.ofReal p) μ)
    (hstep : ∀ n, (eLpNorm (m (n + 1) - m n) (ENNReal.ofReal p) μ).toReal ≤ A * κ ^ n) :
    ∀ n l : ℕ, MemLp (m (n + l) - m n) (ENNReal.ofReal p) μ ∧
      (eLpNorm (m (n + l) - m n) (ENNReal.ofReal p) μ).toReal ≤
        A * κ ^ n / (1 - κ) := by
  have hp1 : 1 ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.mpr (by linarith)
  have hfinite (n l : ℕ) : MemLp (m (n + l) - m n) (ENNReal.ofReal p) μ ∧
      (eLpNorm (m (n + l) - m n) (ENNReal.ofReal p) μ).toReal ≤
        A * κ ^ n * ∑ j ∈ Finset.range l, κ ^ j := by
    induction l with
    | zero => simp
    | succ l ih =>
      have heq : m (n + (l + 1)) - m n =
          (m (n + l + 1) - m (n + l)) + (m (n + l) - m n) := by
        funext ω
        simp only [Pi.add_apply, Pi.sub_apply, Nat.add_assoc]
        ring
      rw [heq]
      refine ⟨(hmem (n + l)).add ih.1, ?_⟩
      have htri := ENNReal.toReal_mono
        (ENNReal.add_ne_top.mpr ⟨(hmem (n + l)).eLpNorm_ne_top, ih.1.eLpNorm_ne_top⟩)
        (eLpNorm_add_le (f := m (n + l + 1) - m (n + l))
          (g := m (n + l) - m n) hp1)
      rw [ENNReal.toReal_add (hmem (n + l)).eLpNorm_ne_top ih.1.eLpNorm_ne_top] at htri
      refine htri.trans ((add_le_add (hstep (n + l)) ih.2).trans_eq ?_)
      rw [Finset.sum_range_succ, pow_add]
      ring
  intro n l
  obtain ⟨hm, hb⟩ := hfinite n l
  refine ⟨hm, hb.trans ?_⟩
  have hsum : (∑ j ∈ Finset.range l, κ ^ j) ≤ 1 / (1 - κ) := by
    simpa only [Nat.Ico_zero_eq_range, pow_zero] using
      (geom_sum_Ico_le_of_lt_one hκ hκ1 (m := 0) (n := l))
  simpa only [div_eq_mul_inv, one_mul] using
    mul_le_mul_of_nonneg_left hsum (mul_nonneg hA (pow_nonneg hκ n))

/-- The same actual corrected representative used for geometric decay has
quantitatively summable differences of consecutive cylinder means. -/
theorem holder_forward_actual_mean_steps
    (hgrowth : node_e_u3A_lp_u2D_growthStmt)
    (hsource : node_l_u3A_forced_u2D_local_u23_centered_u2D_sourceStmt)
    (hinterior : node_e_u3A_holder_u2D_average_u23_unforced_u2D_interiorStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ α θ K Cs : ℝ, 0 < α ∧ α < 1 ∧ 0 < θ ∧ θ ≤ 1 / 2 ∧ 1 ≤ K ∧ 0 < Cs ∧
    ∀ p : ℝ, 2 ≤ p → ∃ Cg : ℝ, 0 < Cg ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange),
      HasSmoothBounds D Q → ∀ (ζ : ℂ)
      (P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
      ∀ (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P),
      IsComplexTransposeSemigroup Q P T →
      ∀ f : Lp ℂ 2 (reducedLaw Q), MemLp f (ENNReal.ofReal p) (reducedLaw Q) →
      ∀ t : ℝ, 0 < t →
      let u := fun s : ℝ => centeredComplexLp Q (P s.toNNReal (centeredComplexLp Q f))
      MemLp (u (t / 8)) (ENNReal.ofReal p) (reducedLaw Q) ∧
      ∃ W : ℝ × FieldPair d → ℂ, Measurable W ∧
      (∀ s, (fun ω => W (s, ω)) =ᵐ[reducedLaw Q]
        (fun ω => u s ω + ∫ v in (t / 4)..s,
          hP.centeringSource (centeredComplexLp Q f) v)) ∧
      ∀ (x : EinsteinRelation.Vec d) (R : ℝ), 0 < R → t / 4 ≤ t - 2 * R ^ 2 →
        R ≤ Real.sqrt t / (1 + ‖ζ‖ * Real.sqrt t) →
      let mean := fun n ω =>
        ⨍ z in Ioo (t - (θ ^ n * R) ^ 2) t ×ˢ euclideanBall x (θ ^ n * R),
          W (z.1, translate z.2 ω)
      let M := (2 * Real.exp (Cg * ‖ζ‖ ^ 2 * t) +
        Cs * ‖ζ‖ * Real.sqrt t * Real.exp (Cs * ‖ζ‖ ^ 2 * t)) *
          (eLpNorm (u (t / 8)) (ENNReal.ofReal p) (reducedLaw Q)).toReal
      ∀ n : ℕ, MemLp (mean (n + 1) - mean n) (ENNReal.ofReal p) (reducedLaw Q) ∧
        (eLpNorm (mean (n + 1) - mean n) (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
          Real.sqrt ((θ ^ (d + 2))⁻¹) * K * (θ ^ α) ^ n * (1 + ‖ζ‖ * R) * M := by
  obtain ⟨α, θ, K, Cs, hα, hα1, hθ, hθhalf, hK, hCs, hdecay⟩ :=
    holder_forward_actual_geometric_decay hgrowth hsource hinterior d hd D
  refine ⟨α, θ, K, Cs, hα, hα1, hθ, hθhalf, hK, hCs, ?_⟩
  intro p hp
  obtain ⟨Cg, hCg, hdecay⟩ := hdecay p hp
  refine ⟨Cg, hCg, ?_⟩
  intro Q hQ ζ P T hP hT f hf t ht u
  obtain ⟨hu8, W, hW, heW, hdecay⟩ := hdecay Q hQ ζ P T hP hT f hf t ht
  refine ⟨hu8, W, hW, heW, ?_⟩
  intro x R hR htime hforce mean M n
  let r := θ ^ n * R
  have hr : 0 < r := mul_pos (pow_pos hθ n) hR
  obtain ⟨hosc, hbound⟩ := hdecay x R hR htime hforce n
  have hlocal : ∀ᵐ ω ∂reducedLaw Q,
      MemLp (fun z : ℝ × EinsteinRelation.Vec d => W (z.1, translate z.2 ω)) 2
        (volume.restrict (Ioo (t - r ^ 2) t ×ˢ euclideanBall x r)) := by
    filter_upwards [holder_forward_corrected_locally_memLp hP (centeredComplexLp Q f)
      t (t - r ^ 2) t W hW heW] with ω hω
    let box := Icc (t - r ^ 2) t ×ˢ {y : EinsteinRelation.Vec d | euclideanNorm (y - x) ≤ r}
    have hu := (hω _ (isCompact_physical_euclidean_closedBall x r)).comp_measurePreserving
      (Measure.measurePreserving_swap (μ := volume.restrict (Icc (t - r ^ 2) t))
        (ν := volume.restrict {y : EinsteinRelation.Vec d | euclideanNorm (y - x) ≤ r}))
    have hu' : MemLp (fun z : ℝ × EinsteinRelation.Vec d => W (z.1, translate z.2 ω)) 2
        (volume.restrict box) := by
      dsimp only [box]
      rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
      exact hu
    apply hu'.mono_measure
    apply Measure.restrict_mono _ le_rfl
    exact Set.prod_mono Ioo_subset_Icc_self
      (fun y hy => ((mem_euclideanBall_iff_vecEuclideanNorm_lt hr).mp hy).le)
  have hstep := holder_transpose_cylinder_mean_step Q W hW x hr hθ
    (by linarith) hlocal hosc
  have heq : θ * r = θ ^ (n + 1) * R := by dsimp only [r]; rw [pow_succ]; ring
  dsimp only at hstep
  rw [heq] at hstep
  refine ⟨hstep.1, hstep.2.trans ?_⟩
  convert mul_le_mul_of_nonneg_left hbound (Real.sqrt_nonneg ((θ ^ (d + 2))⁻¹)) using 1 <;> ring

/-- Every finite tail of actual backward-cylinder means has the structural
geometric bound, uniformly in its length. -/
theorem holder_forward_actual_mean_telescope
    (hgrowth : node_e_u3A_lp_u2D_growthStmt)
    (hsource : node_l_u3A_forced_u2D_local_u23_centered_u2D_sourceStmt)
    (hinterior : node_e_u3A_holder_u2D_average_u23_unforced_u2D_interiorStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ α θ K Cs : ℝ, 0 < α ∧ α < 1 ∧ 0 < θ ∧ θ ≤ 1 / 2 ∧ 1 ≤ K ∧ 0 < Cs ∧
    ∀ p : ℝ, 2 ≤ p → ∃ Cg : ℝ, 0 < Cg ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange),
      HasSmoothBounds D Q → ∀ (ζ : ℂ)
      (P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
      ∀ (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P),
      IsComplexTransposeSemigroup Q P T →
      ∀ f : Lp ℂ 2 (reducedLaw Q), MemLp f (ENNReal.ofReal p) (reducedLaw Q) →
      ∀ t : ℝ, 0 < t →
      let u := fun s : ℝ => centeredComplexLp Q (P s.toNNReal (centeredComplexLp Q f))
      MemLp (u (t / 8)) (ENNReal.ofReal p) (reducedLaw Q) ∧
      ∃ W : ℝ × FieldPair d → ℂ, Measurable W ∧
      (∀ s, (fun ω => W (s, ω)) =ᵐ[reducedLaw Q]
        (fun ω => u s ω + ∫ v in (t / 4)..s,
          hP.centeringSource (centeredComplexLp Q f) v)) ∧
      ∀ (x : EinsteinRelation.Vec d) (R : ℝ), 0 < R → t / 4 ≤ t - 2 * R ^ 2 →
        R ≤ Real.sqrt t / (1 + ‖ζ‖ * Real.sqrt t) →
      let mean := fun n ω =>
        ⨍ z in Ioo (t - (θ ^ n * R) ^ 2) t ×ˢ euclideanBall x (θ ^ n * R),
          W (z.1, translate z.2 ω)
      let M := (2 * Real.exp (Cg * ‖ζ‖ ^ 2 * t) +
        Cs * ‖ζ‖ * Real.sqrt t * Real.exp (Cs * ‖ζ‖ ^ 2 * t)) *
          (eLpNorm (u (t / 8)) (ENNReal.ofReal p) (reducedLaw Q)).toReal
      ∀ n l : ℕ, MemLp (mean (n + l) - mean n) (ENNReal.ofReal p) (reducedLaw Q) ∧
        (eLpNorm (mean (n + l) - mean n) (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
          Real.sqrt ((θ ^ (d + 2))⁻¹) * K * (θ ^ α) ^ n * (1 + ‖ζ‖ * R) * M /
            (1 - θ ^ α) := by
  obtain ⟨α, θ, K, Cs, hα, hα1, hθ, hθhalf, hK, hCs, hsteps⟩ :=
    holder_forward_actual_mean_steps hgrowth hsource hinterior d hd D
  refine ⟨α, θ, K, Cs, hα, hα1, hθ, hθhalf, hK, hCs, ?_⟩
  intro p hp
  obtain ⟨Cg, hCg, hsteps⟩ := hsteps p hp
  refine ⟨Cg, hCg, ?_⟩
  intro Q hQ ζ P T hP hT f hf t ht u
  obtain ⟨hu8, W, hW, heW, hsteps⟩ := hsteps Q hQ ζ P T hP hT f hf t ht
  refine ⟨hu8, W, hW, heW, ?_⟩
  intro x R hR htime hforce mean M
  have hs := hsteps x R hR htime hforce
  let A := Real.sqrt ((θ ^ (d + 2))⁻¹) * K * (1 + ‖ζ‖ * R) * M
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hκ : 0 ≤ θ ^ α := Real.rpow_nonneg hθ.le _
  have hκ1 : θ ^ α < 1 := Real.rpow_lt_one hθ.le (by linarith) hα
  have hb (n : ℕ) :
      (eLpNorm (mean (n + 1) - mean n) (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
        A * (θ ^ α) ^ n := by
    convert (hs n).2 using 1 <;> dsimp only [A] <;> ring
  have htail := holder_forward_mean_telescope (reducedLaw Q) hp hA hκ hκ1 mean
    (fun n => (hs n).1) hb
  intro n l
  refine ⟨(htail n l).1, (htail n l).2.trans_eq ?_⟩
  dsimp only [A]
  ring

/-- One actual corrected representative has both summable mean steps and
nearby-center mean bounds with the same structural constants. -/
theorem holder_forward_actual_mean_control
    (hgrowth : node_e_u3A_lp_u2D_growthStmt)
    (hsource : node_l_u3A_forced_u2D_local_u23_centered_u2D_sourceStmt)
    (hinterior : node_e_u3A_holder_u2D_average_u23_unforced_u2D_interiorStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ α θ K Cs : ℝ, 0 < α ∧ α < 1 ∧ 0 < θ ∧ θ ≤ 1 / 2 ∧ 1 ≤ K ∧ 0 < Cs ∧
    ∀ p : ℝ, 2 ≤ p → ∃ Cg : ℝ, 0 < Cg ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange),
      HasSmoothBounds D Q → ∀ (ζ : ℂ)
      (P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
      ∀ (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P),
      IsComplexTransposeSemigroup Q P T →
      ∀ f : Lp ℂ 2 (reducedLaw Q), MemLp f (ENNReal.ofReal p) (reducedLaw Q) →
      ∀ t : ℝ, 0 < t →
      let u := fun s : ℝ => centeredComplexLp Q (P s.toNNReal (centeredComplexLp Q f))
      MemLp (u (t / 8)) (ENNReal.ofReal p) (reducedLaw Q) ∧
      ∃ W : ℝ × FieldPair d → ℂ, Measurable W ∧
      (∀ s, (fun ω => W (s, ω)) =ᵐ[reducedLaw Q]
        (fun ω => u s ω + ∫ v in (t / 4)..s,
          hP.centeringSource (centeredComplexLp Q f) v)) ∧
      ∀ (x : EinsteinRelation.Vec d) (R : ℝ), 0 < R → t / 4 ≤ t - 2 * R ^ 2 →
        R ≤ Real.sqrt t / (1 + ‖ζ‖ * Real.sqrt t) →
      let mean := fun c n ω =>
        ⨍ z in Ioo (t - (θ ^ n * R) ^ 2) t ×ˢ euclideanBall c (θ ^ n * R),
          W (z.1, translate z.2 ω)
      let M := (2 * Real.exp (Cg * ‖ζ‖ ^ 2 * t) +
        Cs * ‖ζ‖ * Real.sqrt t * Real.exp (Cs * ‖ζ‖ ^ 2 * t)) *
          (eLpNorm (u (t / 8)) (ENNReal.ofReal p) (reducedLaw Q)).toReal
      ∀ n : ℕ,
        MemLp (mean x (n + 1) - mean x n) (ENNReal.ofReal p) (reducedLaw Q) ∧
        (eLpNorm (mean x (n + 1) - mean x n) (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
          Real.sqrt ((θ ^ (d + 2))⁻¹) * K * (θ ^ α) ^ n * (1 + ‖ζ‖ * R) * M ∧
      ∀ y : EinsteinRelation.Vec d,
        vecEuclideanNorm (y - x) + θ * (θ ^ n * R) ≤ θ ^ n * R →
        MemLp (mean y (n + 1) - mean x (n + 1)) (ENNReal.ofReal p) (reducedLaw Q) ∧
        (eLpNorm (mean y (n + 1) - mean x (n + 1)) (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
          2 * Real.sqrt ((θ ^ (d + 2))⁻¹) * K * (θ ^ α) ^ n * (1 + ‖ζ‖ * R) * M := by
  obtain ⟨α, θ, K, Cs, hα, hα1, hθ, hθhalf, hK, hCs, hdecay⟩ :=
    holder_forward_actual_geometric_decay hgrowth hsource hinterior d hd D
  refine ⟨α, θ, K, Cs, hα, hα1, hθ, hθhalf, hK, hCs, ?_⟩
  intro p hp
  obtain ⟨Cg, hCg, hdecay⟩ := hdecay p hp
  refine ⟨Cg, hCg, ?_⟩
  intro Q hQ ζ P T hP hT f hf t ht u
  obtain ⟨hu8, W, hW, heW, hdecay⟩ := hdecay Q hQ ζ P T hP hT f hf t ht
  refine ⟨hu8, W, hW, heW, ?_⟩
  intro x R hR htime hforce mean M n
  let r := θ ^ n * R
  have hr : 0 < r := mul_pos (pow_pos hθ n) hR
  obtain ⟨hosc, hbound⟩ := hdecay x R hR htime hforce n
  have hlocal : ∀ᵐ ω ∂reducedLaw Q,
      MemLp (fun z : ℝ × EinsteinRelation.Vec d => W (z.1, translate z.2 ω)) 2
        (volume.restrict (Ioo (t - r ^ 2) t ×ˢ euclideanBall x r)) := by
    filter_upwards [holder_forward_corrected_locally_memLp hP (centeredComplexLp Q f)
      t (t - r ^ 2) t W hW heW] with ω hω
    let box := Icc (t - r ^ 2) t ×ˢ {y : EinsteinRelation.Vec d | euclideanNorm (y - x) ≤ r}
    have hu := (hω _ (isCompact_physical_euclidean_closedBall x r)).comp_measurePreserving
      (Measure.measurePreserving_swap (μ := volume.restrict (Icc (t - r ^ 2) t))
        (ν := volume.restrict {y : EinsteinRelation.Vec d | euclideanNorm (y - x) ≤ r}))
    have hu' : MemLp (fun z : ℝ × EinsteinRelation.Vec d => W (z.1, translate z.2 ω)) 2
        (volume.restrict box) := by
      dsimp only [box]
      rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
      exact hu
    apply hu'.mono_measure
    apply Measure.restrict_mono _ le_rfl
    exact Set.prod_mono Ioo_subset_Icc_self
      (fun y hy => ((mem_euclideanBall_iff_vecEuclideanNorm_lt hr).mp hy).le)
  have hsame := holder_transpose_cylinder_mean_step Q W hW x hr hθ
    (by linarith) hlocal hosc
  have heq : θ * r = θ ^ (n + 1) * R := by dsimp only [r]; rw [pow_succ]; ring
  dsimp only at hsame
  rw [heq] at hsame
  refine ⟨hsame.1, hsame.2.trans ?_, ?_⟩
  · convert mul_le_mul_of_nonneg_left hbound
      (Real.sqrt_nonneg ((θ ^ (d + 2))⁻¹)) using 1 <;> ring
  intro y hxy
  have hstep := holder_transpose_overlapping_cylinder_means Q (by linarith : 1 ≤ p) W hW x y hr hθ
    (by linarith) (PDE.euclideanBall_subset_of_center_norm_add_le (mul_pos hθ hr) hr hxy)
    hlocal hosc
  dsimp only at hstep
  rw [heq] at hstep
  refine ⟨hstep.1, hstep.2.trans ?_⟩
  convert mul_le_mul_of_nonneg_left hbound (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (Real.sqrt_nonneg ((θ ^ (d + 2))⁻¹))) using 1 <;> ring

/-- A uniform Lp bound passes to a limit identified in the same Lp seminorm. -/
theorem holder_forward_limit_norm_bound
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {p : ℝ≥0∞} (hp : 1 ≤ p) {B : ℝ} (f : ℕ → Ω → ℂ) (g : Ω → ℂ)
    (hlim : Tendsto (fun n => eLpNorm (f n - g) p μ) atTop (𝓝 0))
    (hbound : ∀ n, eLpNorm (f n) p μ ≤ ENNReal.ofReal B) :
    eLpNorm g p μ ≤ ENNReal.ofReal B := by
  have hb (n : ℕ) : eLpNorm g p μ ≤
      eLpNorm (f n - g) p μ + ENNReal.ofReal B := by
    have heq : g = (g - f n) + f n := by
      funext ω
      simp only [Pi.add_apply, Pi.sub_apply]
      ring
    calc
      eLpNorm g p μ ≤ eLpNorm (g - f n) p μ + eLpNorm (f n) p μ := by
        conv_lhs => rw [heq]
        exact eLpNorm_add_le hp
      _ ≤ eLpNorm (f n - g) p μ + ENNReal.ofReal B := by
        rw [eLpNorm_sub_comm]
        exact add_le_add le_rfl (hbound n)
  have ht : Tendsto (fun n => eLpNorm (f n - g) p μ + ENNReal.ofReal B)
      atTop (𝓝 (ENNReal.ofReal B)) := by
    simpa only [zero_add] using hlim.add tendsto_const_nhds
  exact ge_of_tendsto' ht hb

/-- The quantitative finite telescope retains its rate after its limit is identified. -/
theorem holder_forward_mean_limit_tail
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {p A κ : ℝ} (hp : 2 ≤ p) (hA : 0 ≤ A) (hκ : 0 ≤ κ) (hκ1 : κ < 1)
    (m : ℕ → Ω → ℂ) (v : Ω → ℂ)
    (hlim : Tendsto (fun n => eLpNorm (m n - v) (ENNReal.ofReal p) μ) atTop (𝓝 0))
    (hmem : ∀ n, MemLp (m (n + 1) - m n) (ENNReal.ofReal p) μ)
    (hstep : ∀ n, (eLpNorm (m (n + 1) - m n) (ENNReal.ofReal p) μ).toReal ≤ A * κ ^ n) :
    ∀ n, MemLp (v - m n) (ENNReal.ofReal p) μ ∧
      (eLpNorm (v - m n) (ENNReal.ofReal p) μ).toReal ≤ A * κ ^ n / (1 - κ) := by
  intro n
  have ht := holder_forward_mean_telescope μ hp hA hκ hκ1 m hmem hstep
  have heq (l : ℕ) : (m (n + l) - m n) - (v - m n) = m (n + l) - v := by
    funext ω
    simp only [Pi.sub_apply]
    ring
  have hl : Tendsto (fun l =>
      eLpNorm ((m (n + l) - m n) - (v - m n)) (ENNReal.ofReal p) μ) atTop (𝓝 0) := by
    simp only [heq]
    simpa only [Function.comp_def, Nat.add_comm] using hlim.comp (tendsto_add_atTop_nat n)
  have hb := holder_forward_limit_norm_bound μ (ENNReal.one_le_ofReal.mpr (by linarith))
    (fun l => m (n + l) - m n) (v - m n) hl (fun l =>
      (ENNReal.le_ofReal_iff_toReal_le (ht n l).1.eLpNorm_ne_top
        (by positivity : 0 ≤ A * κ ^ n / (1 - κ))).mpr (ht n l).2)
  have hfinite : eLpNorm (v - m n) (ENNReal.ofReal p) μ ≠ ⊤ :=
    (hb.trans_lt ENNReal.ofReal_lt_top).ne
  refine ⟨hfinite.lt_top, ?_⟩
  exact (ENNReal.le_ofReal_iff_toReal_le hfinite (by positivity)).mp hb

/-- Identified mean limits inherit the quantitative nearby-center increment
bound from their two geometric tails and one overlapping-mean comparison. -/
theorem holder_forward_mean_limit_increment
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {p A B κ : ℝ} (hp : 2 ≤ p) (hA : 0 ≤ A) (hκ : 0 ≤ κ) (hκ1 : κ < 1)
    (m₀ m₁ : ℕ → Ω → ℂ) (v₀ v₁ : Ω → ℂ)
    (hlim₀ : Tendsto (fun n => eLpNorm (m₀ n - v₀) (ENNReal.ofReal p) μ) atTop (𝓝 0))
    (hlim₁ : Tendsto (fun n => eLpNorm (m₁ n - v₁) (ENNReal.ofReal p) μ) atTop (𝓝 0))
    (hmem₀ : ∀ n, MemLp (m₀ (n + 1) - m₀ n) (ENNReal.ofReal p) μ)
    (hmem₁ : ∀ n, MemLp (m₁ (n + 1) - m₁ n) (ENNReal.ofReal p) μ)
    (hstep₀ : ∀ n, (eLpNorm (m₀ (n + 1) - m₀ n) (ENNReal.ofReal p) μ).toReal ≤ A * κ ^ n)
    (hstep₁ : ∀ n, (eLpNorm (m₁ (n + 1) - m₁ n) (ENNReal.ofReal p) μ).toReal ≤ A * κ ^ n)
    (n : ℕ) (hcross : MemLp (m₁ (n + 1) - m₀ (n + 1)) (ENNReal.ofReal p) μ)
    (hcrossbound : (eLpNorm (m₁ (n + 1) - m₀ (n + 1)) (ENNReal.ofReal p) μ).toReal ≤
      B * κ ^ n) :
    MemLp (v₁ - v₀) (ENNReal.ofReal p) μ ∧
    (eLpNorm (v₁ - v₀) (ENNReal.ofReal p) μ).toReal ≤
      (2 * A * κ / (1 - κ) + B) * κ ^ n := by
  obtain ⟨ht₀, hb₀⟩ := holder_forward_mean_limit_tail μ hp hA hκ hκ1 m₀ v₀
    hlim₀ hmem₀ hstep₀ (n + 1)
  obtain ⟨ht₁, hb₁⟩ := holder_forward_mean_limit_tail μ hp hA hκ hκ1 m₁ v₁
    hlim₁ hmem₁ hstep₁ (n + 1)
  let a := v₁ - m₁ (n + 1)
  let b := m₁ (n + 1) - m₀ (n + 1)
  let c := v₀ - m₀ (n + 1)
  have heq : v₁ - v₀ = (a + b) - c := by
    dsimp only [a, b, c]
    funext ω
    simp only [Pi.sub_apply, Pi.add_apply]
    ring
  rw [heq]
  have hab : MemLp (a + b) (ENNReal.ofReal p) μ := ht₁.add hcross
  refine ⟨hab.sub ht₀, ?_⟩
  have hp1 : 1 ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.mpr (by linarith)
  have hsub := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨hab.eLpNorm_ne_top, ht₀.eLpNorm_ne_top⟩)
    (eLpNorm_sub_le (f := a + b) (g := c) hp1)
  rw [ENNReal.toReal_add hab.eLpNorm_ne_top ht₀.eLpNorm_ne_top] at hsub
  have hadd := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨ht₁.eLpNorm_ne_top, hcross.eLpNorm_ne_top⟩)
    (eLpNorm_add_le (f := a) (g := b) hp1)
  rw [ENNReal.toReal_add ht₁.eLpNorm_ne_top hcross.eLpNorm_ne_top] at hadd
  have ht := hsub.trans (add_le_add (hadd.trans (add_le_add hb₁ hcrossbound)) hb₀)
  refine ht.trans_eq ?_
  rw [pow_succ]
  ring

/-- Geometric-scale bounds imply a power bound at every positive distance. -/
theorem holder_forward_discrete_scale_bound
    {θ α c R δ B N : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1)
    (hα : 0 ≤ α) (hc : 0 < c) (hR : 0 < R) (hδ : 0 < δ)
    (hδR : δ ≤ c * R) (hB : 0 ≤ B)
    (hbound : ∀ n : ℕ, δ ≤ c * (θ ^ n * R) → N ≤ B * (θ ^ α) ^ n) :
    N ≤ B * (δ / (θ * (c * R))) ^ α := by
  have hcR : 0 < c * R := mul_pos hc hR
  obtain ⟨n, hnlow, hnhi⟩ := exists_nat_pow_near_of_lt_one
    (div_pos hδ hcR) ((div_le_one hcR).mpr hδR) hθ hθ1
  have hdist : δ ≤ c * (θ ^ n * R) := by
    have hh := (div_le_iff₀ hcR).mp hnhi
    nlinarith only [hh]
  refine (hbound n hdist).trans (mul_le_mul_of_nonneg_left ?_ hB)
  have hpow : θ ^ n ≤ δ / (θ * (c * R)) := by
    apply (le_div_iff₀ (mul_pos hθ hcR)).mpr
    have hh := (lt_div_iff₀ hcR).mp hnlow
    rw [pow_succ] at hh
    nlinarith only [hh]
  have hrpow := Real.rpow_le_rpow (pow_nonneg hθ.le n) hpow hα
  have heq : (θ ^ α) ^ n = (θ ^ n) ^ α := by
    rw [← Real.rpow_mul_natCast hθ.le, ← Real.rpow_natCast_mul hθ.le, mul_comm]
  rwa [heq]

/-- Every forward or clock endpoint is the centered evolution of its actual
initial endpoint. This includes the signed complex clock factor at zero force. -/
theorem holder_forward_endpoint_restart
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
    (ζ : ℂ) (P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P)
    (ν : EndpointIndex d) (hν : ν ≠ .inr true) (s : ℝ≥0) :
    centeredComplexLp Q (P s (centeredComplexLp Q
      (indexedEndpoint hd Q ν ζ P T β a μ 0))) =
        indexedEndpoint hd Q ν ζ P T β a μ s := by
  rw [hP.centered_apply]
  cases ν with
  | inl k =>
    simp only [indexedEndpoint, velocityEndpoint, hP.1, ContinuousLinearMap.id_apply,
      hP.centered_apply]
  | inr b =>
    cases b with
    | true => exact False.elim (hν rfl)
    | false =>
      simp only [indexedEndpoint, clockEndpoint, hP.1, ContinuousLinearMap.id_apply]
      rw [map_smul, ← centeredComplexLpCLM_apply Q (ζ • P s (centeredComplexLp Q μ)),
        map_smul, centeredComplexLpCLM_apply, hP.centered_apply]

/-- The coupled mean estimates apply to the actual forward and clock endpoints,
with the same structural witnesses and one corrected measurable representative. -/
theorem holder_forward_endpoint_mean_control
    (hgrowth : node_e_u3A_lp_u2D_growthStmt)
    (hsource : node_l_u3A_forced_u2D_local_u23_centered_u2D_sourceStmt)
    (hinterior : node_e_u3A_holder_u2D_average_u23_unforced_u2D_interiorStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ α θ K Cs : ℝ, 0 < α ∧ α < 1 ∧ 0 < θ ∧ θ ≤ 1 / 2 ∧ 1 ≤ K ∧ 0 < Cs ∧
    ∀ p : ℝ, 2 ≤ p → ∃ Cg : ℝ, 0 < Cg ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q))
      (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ (ζ : ℂ)
      (P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
      ∀ (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P),
      IsComplexTransposeSemigroup Q P T →
      ∀ ν : EndpointIndex d, ν ≠ .inr true →
      ∀ t : ℝ≥0, 0 < (t : ℝ) →
      let f := indexedEndpoint hd Q ν ζ P T β a μ 0
      let u := fun s : ℝ => indexedEndpoint hd Q ν ζ P T β a μ s.toNNReal
      MemLp (u ((t : ℝ) / 8)) (ENNReal.ofReal p) (reducedLaw Q) ∧
      Continuous (fun s : ℝ => ∫ v in ((t : ℝ) / 4)..s,
        hP.centeringSource (centeredComplexLp Q f) v) ∧
      ∃ W : ℝ × FieldPair d → ℂ, Measurable W ∧
      (∀ s, (fun ω => W (s, ω)) =ᵐ[reducedLaw Q]
        (fun ω => u s ω + ∫ v in ((t : ℝ) / 4)..s,
          hP.centeringSource (centeredComplexLp Q f) v)) ∧
      ∀ (x : EinsteinRelation.Vec d) (R : ℝ), 0 < R → (t : ℝ) / 4 ≤ (t : ℝ) - 2 * R ^ 2 →
        R ≤ Real.sqrt (t : ℝ) / (1 + ‖ζ‖ * Real.sqrt (t : ℝ)) →
      let mean := fun c n ω =>
        ⨍ z in Ioo ((t : ℝ) - (θ ^ n * R) ^ 2) (t : ℝ) ×ˢ euclideanBall c (θ ^ n * R),
          W (z.1, translate z.2 ω)
      let M := (2 * Real.exp (Cg * ‖ζ‖ ^ 2 * (t : ℝ)) +
        Cs * ‖ζ‖ * Real.sqrt (t : ℝ) * Real.exp (Cs * ‖ζ‖ ^ 2 * (t : ℝ))) *
          (eLpNorm (u ((t : ℝ) / 8)) (ENNReal.ofReal p) (reducedLaw Q)).toReal
      ∀ n : ℕ,
        MemLp (mean x (n + 1) - mean x n) (ENNReal.ofReal p) (reducedLaw Q) ∧
        (eLpNorm (mean x (n + 1) - mean x n) (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
          Real.sqrt ((θ ^ (d + 2))⁻¹) * K * (θ ^ α) ^ n * (1 + ‖ζ‖ * R) * M ∧
      ∀ y : EinsteinRelation.Vec d,
        vecEuclideanNorm (y - x) + θ * (θ ^ n * R) ≤ θ ^ n * R →
        MemLp (mean y (n + 1) - mean x (n + 1)) (ENNReal.ofReal p) (reducedLaw Q) ∧
        (eLpNorm (mean y (n + 1) - mean x (n + 1)) (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
          2 * Real.sqrt ((θ ^ (d + 2))⁻¹) * K * (θ ^ α) ^ n * (1 + ‖ζ‖ * R) * M := by
  obtain ⟨α, θ, K, Cs, hα, hα1, hθ, hθhalf, hK, hCs, hmean⟩ :=
    holder_forward_actual_mean_control hgrowth hsource hinterior d hd D
  refine ⟨α, θ, K, Cs, hα, hα1, hθ, hθhalf, hK, hCs, ?_⟩
  intro p hp
  obtain ⟨Cg, hCg, hmean⟩ := hmean p hp
  refine ⟨Cg, hCg, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P T hP hT ν hν t ht f u
  have hf := local_time_gradient_endpoint_memLp hgrowth hd p hp Q hQ β a μ hβ ha hμ
    ζ P T hP hT ν 0
  have he (s : ℝ) : centeredComplexLp Q (P s.toNNReal (centeredComplexLp Q f)) = u s :=
    holder_forward_endpoint_restart hd Q β a μ ζ P T hP ν hν s.toNNReal
  have hm := hmean Q hQ ζ P T hP hT f hf (t : ℝ) ht
  simp only [he] at hm
  exact ⟨hm.1, continuous_centered_source_primitive hP (centeredComplexLp Q f) _, hm.2⟩

/-- The actual forward and clock endpoints inherit a spatial power modulus
from the corrected cylinder means. The scalar primitive cancels exactly. -/
theorem holder_forward_endpoint_spatial_increments
    (hgrowth : node_e_u3A_lp_u2D_growthStmt)
    (hsource : node_l_u3A_forced_u2D_local_u23_centered_u2D_sourceStmt)
    (hinterior : node_e_u3A_holder_u2D_average_u23_unforced_u2D_interiorStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ α θ K Cs : ℝ, 0 < α ∧ α < 1 ∧ 0 < θ ∧ θ ≤ 1 / 2 ∧ 1 ≤ K ∧ 0 < Cs ∧
    ∀ p : ℝ, 2 ≤ p → ∃ Cg : ℝ, 0 < Cg ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q))
      (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ (ζ : ℂ)
      (P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
      ∀ (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P),
      IsComplexTransposeSemigroup Q P T →
      ∀ ν : EndpointIndex d, ν ≠ .inr true →
      ∀ t : ℝ≥0, 0 < (t : ℝ) →
      let U := indexedEndpoint hd Q ν ζ P T β a μ t
      let U₈ := indexedEndpoint hd Q ν ζ P T β a μ (t / 8)
      MemLp (U₈ : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) ∧
      ∀ R : ℝ, 0 < R → (t : ℝ) / 4 ≤ (t : ℝ) - 2 * R ^ 2 →
        R ≤ Real.sqrt (t : ℝ) / (1 + ‖ζ‖ * Real.sqrt (t : ℝ)) →
      let M := (2 * Real.exp (Cg * ‖ζ‖ ^ 2 * (t : ℝ)) +
        Cs * ‖ζ‖ * Real.sqrt (t : ℝ) * Real.exp (Cs * ‖ζ‖ ^ 2 * (t : ℝ))) *
          (eLpNorm (U₈ : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal
      let A := Real.sqrt ((θ ^ (d + 2))⁻¹) * K * (1 + ‖ζ‖ * R) * M
      ∀ x y : EinsteinRelation.Vec d, vecEuclideanNorm (y - x) ≤ (1 - θ) * R →
        (eLpNorm (fun ω => U (translate y ω) - U (translate x ω))
          (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
          (2 * A * (θ ^ α) / (1 - θ ^ α) + 2 * A) *
            (vecEuclideanNorm (y - x) / (θ * ((1 - θ) * R))) ^ α := by
  obtain ⟨α, θ, K, Cs, hα, hα1, hθ, hθhalf, hK, hCs, hmean⟩ :=
    holder_forward_endpoint_mean_control hgrowth hsource hinterior d hd D
  refine ⟨α, θ, K, Cs, hα, hα1, hθ, hθhalf, hK, hCs, ?_⟩
  intro p hp
  obtain ⟨Cg, hCg, hmean⟩ := hmean p hp
  refine ⟨Cg, hCg, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P T hP hT ν hν t ht U U₈
  obtain ⟨hmem, hc, W, hW, heW, hmeans⟩ :=
    hmean Q hQ β a μ hβ ha hμ ζ P T hP hT ν hν t ht
  have ht8 : ((t : ℝ) / 8).toNNReal = t / 8 := by
    change (↑(t / 8) : ℝ).toNNReal = t / 8
    exact Real.toNNReal_coe
  simp only [ht8] at hmem hmeans
  refine ⟨hmem, ?_⟩
  intro R hR htime hforce M A x y hxy
  let c := fun s : ℝ => ∫ v in ((t : ℝ) / 4)..s,
    hP.centeringSource (centeredComplexLp Q (indexedEndpoint hd Q ν ζ P T β a μ 0)) v
  let mean := fun z n ω =>
    ⨍ w in Ioo ((t : ℝ) - (θ ^ n * R) ^ 2) (t : ℝ) ×ˢ euclideanBall z (θ ^ n * R),
      W (w.1, translate w.2 ω)
  let v := fun z ω => U (translate z ω) + c (t : ℝ)
  have hθ1 : θ < 1 := by linarith only [hθhalf]
  have hκ : 0 ≤ θ ^ α := Real.rpow_nonneg hθ.le _
  have hκ1 : θ ^ α < 1 := Real.rpow_lt_one hθ.le hθ1 hα
  have hA : 0 ≤ A := by dsimp only [A, M]; positivity
  have hB : 0 ≤ 2 * A * (θ ^ α) / (1 - θ ^ α) + 2 * A := by positivity
  have hradii : Tendsto (fun n : ℕ => θ ^ n * R) atTop (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, Filter.Eventually.of_forall (fun n => mul_pos (pow_pos hθ n) hR)⟩
    simpa only [zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hθ.le hθ1).mul_const R
  have hlim (z : EinsteinRelation.Vec d) : Tendsto (fun n =>
      eLpNorm (mean z n - v z) (ENNReal.ofReal p) (reducedLaw Q)) atTop (𝓝 0) := by
    have hh := (endpoint_corrected_physical_cylinder_average_tendsto hgrowth hd p hp Q hQ
      β a μ hβ ha hμ ζ P T hP hT ν t ht c hc W hW heW z).comp hradii
    apply hh.congr'
    apply Filter.Eventually.of_forall
    intro n
    apply eLpNorm_congr_ae
    filter_upwards [coeFn_complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) z U]
      with ω hω
    change mean z n ω - (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) z U) ω - c (t : ℝ) =
      mean z n ω - (U (translate z ω) + c (t : ℝ))
    rw [hω]
    ring
  have hstep (z : EinsteinRelation.Vec d) (n : ℕ) :
      MemLp (mean z (n + 1) - mean z n) (ENNReal.ofReal p) (reducedLaw Q) ∧
      (eLpNorm (mean z (n + 1) - mean z n) (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
        A * (θ ^ α) ^ n := by
    have hh := hmeans z R hR htime hforce n
    refine ⟨hh.1, hh.2.1.trans_eq ?_⟩
    dsimp only [A, M]
    ring
  have hscale (n : ℕ) (hn : vecEuclideanNorm (y - x) ≤ (1 - θ) * (θ ^ n * R)) :
      (eLpNorm (fun ω => U (translate y ω) - U (translate x ω))
        (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
        (2 * A * (θ ^ α) / (1 - θ ^ α) + 2 * A) * (θ ^ α) ^ n := by
    have hnear : vecEuclideanNorm (y - x) + θ * (θ ^ n * R) ≤ θ ^ n * R := by
      nlinarith only [hn]
    have hcross := (hmeans x R hR htime hforce n).2.2 y hnear
    have hcrossbound : (eLpNorm (mean y (n + 1) - mean x (n + 1))
        (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤ (2 * A) * (θ ^ α) ^ n := by
      refine hcross.2.trans_eq ?_
      dsimp only [A, M]
      ring
    have hh := holder_forward_mean_limit_increment (reducedLaw Q) hp hA hκ hκ1
      (mean x) (mean y) (v x) (v y) (hlim x) (hlim y)
      (fun n => (hstep x n).1) (fun n => (hstep y n).1)
      (fun n => (hstep x n).2) (fun n => (hstep y n).2) n hcross.1 hcrossbound
    have heq : v y - v x = fun ω => U (translate y ω) - U (translate x ω) := by
      funext ω
      dsimp only [v, Pi.sub_apply]
      ring
    rw [heq] at hh
    exact hh.2
  by_cases heq : y = x
  · subst y
    simp only [sub_self]
    rw [eLpNorm_fun_zero, ENNReal.toReal_zero]
    exact mul_nonneg hB (Real.rpow_nonneg (div_nonneg (vecEuclideanNorm_nonneg _) (by positivity)) _)
  have hδ : 0 < vecEuclideanNorm (y - x) := by
    apply lt_of_le_of_ne (vecEuclideanNorm_nonneg _)
    intro hz
    exact heq (sub_eq_zero.mp (vecEuclideanNorm_eq_zero_iff.mp hz.symm))
  exact holder_forward_discrete_scale_bound hθ hθ1 hα.le (by linarith : 0 < 1 - θ)
    hR hδ hxy hB hscale

/-- A force-dependent radius lies in the corrected terminal window and has
an explicit square, including at zero force. -/
theorem holder_forward_force_radius
    {t z : ℝ} (ht : 0 < t) (hz : 0 ≤ z) :
    let R := Real.sqrt t / (4 * (1 + z * Real.sqrt t))
    0 < R ∧ t / 4 ≤ t - 2 * R ^ 2 ∧
      R ≤ Real.sqrt t / (1 + z * Real.sqrt t) ∧
      R ^ 2 = t / (16 * (1 + z * Real.sqrt t) ^ 2) ∧
      1 + z * R ≤ 2 := by
  intro R
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hw : 1 ≤ 1 + z * Real.sqrt t := le_add_of_nonneg_right (mul_nonneg hz hs.le)
  have hwpos : 0 < 1 + z * Real.sqrt t := lt_of_lt_of_le zero_lt_one hw
  have hR : 0 < R := div_pos hs (mul_pos (by norm_num) hwpos)
  have hRsmall : R ≤ Real.sqrt t / 4 :=
    div_le_div_of_nonneg_left hs.le (by norm_num) (by linarith only [hw])
  have hRsq : R ^ 2 ≤ t / 16 := by
    calc
      R ^ 2 ≤ (Real.sqrt t / 4) ^ 2 :=
        (sq_le_sq₀ hR.le (div_nonneg hs.le (by norm_num))).mpr hRsmall
      _ = t / 16 := by rw [div_pow, Real.sq_sqrt ht.le]; norm_num
  refine ⟨hR, by linarith only [hRsq, ht], ?_, ?_, ?_⟩
  · exact div_le_div_of_nonneg_left hs.le hwpos (by linarith only [hwpos])
  · dsimp only [R]
    rw [div_pow, mul_pow, Real.sq_sqrt ht.le]
    norm_num
  · have he : z * R = (z * Real.sqrt t) / (4 * (1 + z * Real.sqrt t)) := by
      dsimp only [R]
      ring
    rw [he]
    have hh : (z * Real.sqrt t) / (4 * (1 + z * Real.sqrt t)) ≤ 1 :=
      (div_le_one (by positivity)).mpr (by nlinarith only [hw])
    linarith only [hh]

/-- On the local scale range, an exponential Gaussian tail is bounded by
any positive power of order at most one, with its rate constant retained. -/
theorem holder_forward_gaussian_tail_power
    {c x q : ℝ} (hc : 0 < c) (hx : 0 < x) (hx1 : x ≤ 1) (hq1 : q ≤ 1) :
    Real.exp (-c / x) ≤ (1 / c) * x ^ q := by
  have hexp : c / x ≤ Real.exp (c / x) :=
    (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1)).trans (Real.add_one_le_exp _)
  have hlin : Real.exp (-c / x) ≤ x / c := by
    calc
      Real.exp (-c / x) = 1 / Real.exp (c / x) := by
        rw [neg_div, Real.exp_neg, one_div]
      _ ≤ 1 / (c / x) := one_div_le_one_div_of_le (div_pos hc hx) hexp
      _ = x / c := by field_simp
  have hpow : x ≤ x ^ q := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge hx hx1 hq1
  calc
    Real.exp (-c / x) ≤ x / c := hlin
    _ ≤ x ^ q / c := div_le_div_of_nonneg_right hpow hc.le
    _ = (1 / c) * x ^ q := by ring

/-- The completed local Gaussian estimate gives a pure power bound; its
exponential tail is absorbed uniformly before choosing the law and endpoint. -/
theorem holder_forward_gaussian_power_of_local_increments
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) (p α : ℝ)
    (hp : 2 ≤ p) (hα : 0 < α) (hα1 : α ≤ 1) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (f : Lp ℂ 2 (reducedLaw Q)) (A M R : ℝ),
      0 ≤ A → 0 ≤ M → 0 < R →
      MemLp (f : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) →
      eLpNorm (f : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) ≤ ENNReal.ofReal M →
      (∀ x : EinsteinRelation.Vec d, euclideanNorm x ≤ R →
        eLpNorm (fun ω => f (translate x ω) - f ω)
          (ENNReal.ofReal p) (reducedLaw Q) ≤
          ENNReal.ofReal (A * (euclideanNorm x / R) ^ α)) →
      ∀ (s : ℝ) (hs : 0 < s), s ≤ R ^ 2 →
      MemLp ((f - gaussianAverage hd Q s hs f) : FieldPair d → ℂ)
        (ENNReal.ofReal p) (reducedLaw Q) ∧
      (eLpNorm ((f - gaussianAverage hd Q s hs f) : FieldPair d → ℂ)
        (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
          C * (A + M) * (s / R ^ 2) ^ (α / 2) := by
  obtain ⟨C, c, hC, hc, hlocal⟩ :=
    holder_gaussian_unsmoothing_of_local_increment_bound d hd D p α hp hα hα1
  refine ⟨C * (1 + 1 / c), by positivity, ?_⟩
  intro Q f A M R hA hM hR hf hfM hinc s hs hsR
  obtain ⟨hmem, hbound⟩ := hlocal Q f A M R hA hM hR hf hfM hinc s hs hsR
  refine ⟨hmem, ?_⟩
  have hx : 0 < s / R ^ 2 := div_pos hs (sq_pos_of_pos hR)
  have hx1 : s / R ^ 2 ≤ 1 := (div_le_one (sq_pos_of_pos hR)).mpr hsR
  have htail := holder_forward_gaussian_tail_power hc hx hx1 (by linarith : α / 2 ≤ 1)
  have he : -c * R ^ 2 / s = -c / (s / R ^ 2) := by field_simp
  rw [← he] at htail
  have hpow : 0 ≤ (s / R ^ 2) ^ (α / 2) := Real.rpow_nonneg hx.le _
  have hfactor : 1 ≤ 1 + 1 / c := le_add_of_nonneg_right (by positivity)
  have hfirst : (s / R ^ 2) ^ (α / 2) ≤
      (1 + 1 / c) * (s / R ^ 2) ^ (α / 2) := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hfactor hpow
  have hsecond : Real.exp (-c * R ^ 2 / s) ≤
      (1 + 1 / c) * (s / R ^ 2) ^ (α / 2) :=
    htail.trans (mul_le_mul_of_nonneg_right (by linarith : 1 / c ≤ 1 + 1 / c) hpow)
  have htotal := mul_le_mul_of_nonneg_left
    (add_le_add (mul_le_mul_of_nonneg_left hfirst hA)
      (mul_le_mul_of_nonneg_left hsecond hM)) hC.le
  have hfinite : C * (A * (s / R ^ 2) ^ (α / 2) +
      M * Real.exp (-c * R ^ 2 / s)) ≥ 0 := by positivity
  exact (ENNReal.toReal_le_of_le_ofReal hfinite hbound).trans (htotal.trans_eq (by ring))

/-- A local spatial modulus and the global moment bound give Gaussian
unsmoothing at every positive scale, by extending the modulus outside the ball. -/
theorem holder_forward_gaussian_all_scales_of_local_increments
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) (p α : ℝ)
    (hp : 2 ≤ p) (hα : 0 < α) (hα1 : α ≤ 1) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (f : Lp ℂ 2 (reducedLaw Q)) (A M R : ℝ),
      0 ≤ A → 0 ≤ M → 0 < R →
      MemLp (f : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) →
      eLpNorm (f : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) ≤ ENNReal.ofReal M →
      (∀ x : EinsteinRelation.Vec d, euclideanNorm x ≤ R →
        eLpNorm (fun ω => f (translate x ω) - f ω)
          (ENNReal.ofReal p) (reducedLaw Q) ≤
          ENNReal.ofReal (A * (euclideanNorm x / R) ^ α)) →
      ∀ (s : ℝ) (hs : 0 < s),
      MemLp ((f - gaussianAverage hd Q s hs f) : FieldPair d → ℂ)
        (ENNReal.ofReal p) (reducedLaw Q) ∧
      (eLpNorm ((f - gaussianAverage hd Q s hs f) : FieldPair d → ℂ)
        (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
          C * (A + 2 * M) * (s / R ^ 2) ^ (α / 2) := by
  obtain ⟨C, hC, hgauss⟩ :=
    holder_gaussian_unsmoothing_of_increment_bound d hd D p α hp hα hα1
  refine ⟨C, hC, ?_⟩
  intro Q f A M R hA hM hR hf hfM hinc s hs
  have hpowR : 0 < R ^ α := Real.rpow_pos_of_pos hR _
  have hp1 : 1 ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.mpr (by linarith only [hp])
  have hglobal (x : EinsteinRelation.Vec d) :
      eLpNorm (fun ω => f (translate x ω) - f ω) (ENNReal.ofReal p) (reducedLaw Q) ≤
        ENNReal.ofReal (((A + 2 * M) / R ^ α) * euclideanNorm x ^ α) := by
    have hx0 : 0 ≤ euclideanNorm x := Real.sqrt_nonneg _
    have hratio : (euclideanNorm x / R) ^ α = euclideanNorm x ^ α / R ^ α :=
      Real.div_rpow hx0 hR.le α
    have hmajor : A * (euclideanNorm x / R) ^ α ≤
        ((A + 2 * M) / R ^ α) * euclideanNorm x ^ α := by
      rw [hratio]
      have hh := mul_le_mul_of_nonneg_right (show A ≤ A + 2 * M by linarith only [hM])
        (div_nonneg (Real.rpow_nonneg hx0 α) hpowR.le)
      convert hh using 1 <;> ring
    by_cases hx : euclideanNorm x ≤ R
    · exact (hinc x hx).trans (ENNReal.ofReal_le_ofReal hmajor)
    have hnorm : eLpNorm (fun ω => f (translate x ω)) (ENNReal.ofReal p) (reducedLaw Q) =
        eLpNorm (f : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) :=
      eLpNorm_comp_measurePreserving hf.aestronglyMeasurable
        (measurePreserving_translate (reducedLaw Q) (reducedLaw_stationary Q) x)
    have hbound : eLpNorm (fun ω => f (translate x ω) - f ω)
        (ENNReal.ofReal p) (reducedLaw Q) ≤ ENNReal.ofReal (2 * M) := by
      calc
        _ ≤ eLpNorm (fun ω => f (translate x ω)) (ENNReal.ofReal p) (reducedLaw Q) +
            eLpNorm (f : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) := eLpNorm_sub_le hp1
        _ ≤ ENNReal.ofReal M + ENNReal.ofReal M := by rw [hnorm]; exact add_le_add hfM hfM
        _ = ENNReal.ofReal (2 * M) := by rw [← ENNReal.ofReal_add hM hM]; congr 1; ring
    have hone : 1 ≤ (euclideanNorm x / R) ^ α :=
      Real.one_le_rpow ((le_div_iff₀ hR).mpr (by linarith only [not_le.mp hx])) hα.le
    have hfar : 2 * M ≤ ((A + 2 * M) / R ^ α) * euclideanNorm x ^ α := by
      calc
        _ ≤ (A + 2 * M) * (euclideanNorm x / R) ^ α := by
          exact (show 2 * M ≤ A + 2 * M by linarith only [hA]).trans
            (le_mul_of_one_le_right (by positivity) hone)
        _ = _ := by rw [hratio]; ring
    exact hbound.trans (ENNReal.ofReal_le_ofReal hfar)
  have hb := hgauss Q f ((A + 2 * M) / R ^ α) (by positivity) hf hglobal s hs
  have hfinite := hb.trans_lt ENNReal.ofReal_lt_top
  refine ⟨hfinite, ?_⟩
  have hrpow : s ^ (α / 2) / R ^ α = (s / R ^ 2) ^ (α / 2) := by
    rw [Real.div_rpow hs.le (sq_nonneg R), ← Real.rpow_natCast_mul hR.le]
    congr 2
    ring
  have hh := ENNReal.toReal_le_of_le_ofReal (by positivity) hb
  refine hh.trans_eq ?_
  rw [← hrpow]
  ring

/-- The corrected-window amplitude is controlled by one force polynomial
and one exponential, using only constants already uniform in the law. -/
theorem holder_forward_corrected_amplitude_bound
    {Cs Cg z t N : ℝ} (hCs : 0 ≤ Cs) (hCg : 0 ≤ Cg)
    (hz : 0 ≤ z) (ht : 0 ≤ t) (hN : 0 ≤ N) :
    (2 * Real.exp (Cg * z ^ 2 * t) +
        Cs * z * Real.sqrt t * Real.exp (Cs * z ^ 2 * t)) * N ≤
      (2 + Cs) * (1 + z * Real.sqrt t) *
        Real.exp ((Cg + Cs) * z ^ 2 * t) * N := by
  have hCgexp : Real.exp (Cg * z ^ 2 * t) ≤
      Real.exp ((Cg + Cs) * z ^ 2 * t) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg hCs (mul_nonneg (sq_nonneg z) ht)]
  have hCsexp : Real.exp (Cs * z ^ 2 * t) ≤
      Real.exp ((Cg + Cs) * z ^ 2 * t) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg hCg (mul_nonneg (sq_nonneg z) ht)]
  apply mul_le_mul_of_nonneg_right _ hN
  have hsum := add_le_add (mul_le_mul_of_nonneg_left hCgexp (by norm_num : (0 : ℝ) ≤ 2))
    (mul_le_mul_of_nonneg_left hCsexp (by positivity : 0 ≤ Cs * z * Real.sqrt t))
  refine hsum.trans ?_
  have hcoeff : 2 + Cs * z * Real.sqrt t ≤ (2 + Cs) * (1 + z * Real.sqrt t) := by
    nlinarith [mul_nonneg hz (Real.sqrt_nonneg t)]
  convert mul_le_mul_of_nonneg_right hcoeff (Real.exp_nonneg _) using 1 <;> ring

/-- Uniform Gaussian unsmoothing for the actual forward and clock endpoints. -/
theorem holder_average_forward_clock_of_deps
  (h0 : EinsteinFull.Blueprint.node_e_u3A_local_u2D_timeStmt)
  (h1 : EinsteinFull.Blueprint.node_e_u3A_lp_u2D_growthStmt)
  (h2 : EinsteinFull.Blueprint.node_l_u3A_forced_u2D_local_u23_centered_u2D_sourceStmt)
  (h3 : EinsteinFull.Blueprint.node_e_u3A_holder_u2D_average_u23_unforced_u2D_interiorStmt) :
∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d),
    ∃ α : ℝ, 0 < α ∧
    ∀ p : ℝ, 2 ≤ p → ∃ C Cp : ℝ, 1 ≤ C ∧ 0 < Cp ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q))
      (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ ζ : ℂ,
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
      IsComplexTransposeSemigroup Q P Pdag → ∀ ν : EndpointIndex d, ν ≠ .inr true →
    ∀ (t : ℝ≥0), 0 < (t : ℝ) →
      let U := indexedEndpoint hd Q ν ζ P Pdag β a μ t
      let U₈ := indexedEndpoint hd Q ν ζ P Pdag β a μ (t / 8)
      MemLp (U₈ : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) ∧
      ∀ b : ℝ, 0 < b → b ≤ 1 / 16 → ∀ hbt : 0 < b * (t : ℝ),
        MemLp ((U - gaussianAverage hd Q (b * (t : ℝ)) hbt U) : FieldPair d → ℂ)
          (ENNReal.ofReal p) (reducedLaw Q) ∧
        (eLpNorm ((U - gaussianAverage hd Q (b * (t : ℝ)) hbt U) : FieldPair d → ℂ)
          (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
          C * b ^ (α / 2) * (1 + ‖ζ‖ * Real.sqrt (t : ℝ)) ^ C *
            Real.exp (Cp * ‖ζ‖ ^ 2 * (t : ℝ)) *
            (eLpNorm (U₈ : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal := by
  intro d hd D
  obtain ⟨α, θ, K, Cs, hα, hα1, hθ, hθhalf, hK, hCs, hincrements⟩ :=
    holder_forward_endpoint_spatial_increments h1 h2 h3 d hd D
  have hθ1 : θ < 1 := by linarith only [hθhalf]
  have hκ1 : θ ^ α < 1 := Real.rpow_lt_one hθ.le hθ1 hα
  let J := Real.sqrt ((θ ^ (d + 2))⁻¹) * K
  let L := 2 * J * (θ ^ α) / (1 - θ ^ α) + 2 * J
  have hJ : 0 ≤ J := mul_nonneg (Real.sqrt_nonneg _) (by linarith only [hK])
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  have hθα : 0 < θ ^ α := Real.rpow_pos_of_pos hθ _
  refine ⟨α, hα, ?_⟩
  intro p hp
  obtain ⟨Cg, hCg, hincrements⟩ := hincrements p hp
  obtain ⟨Cw, hCw, hwindow⟩ := holder_forward_centered_window_bound h1 d hd D p hp
  obtain ⟨H, hH, hgauss⟩ :=
    holder_forward_gaussian_all_scales_of_local_increments d hd D p α hp hα hα1.le
  let F := 2 * (L / θ ^ α) * (2 + Cs) + 4
  let V := (16 / (1 - θ) ^ 2) ^ (α / 2)
  let C := 2 + H * F * V
  let Cp := Cg + Cs + Cw
  have hF : 0 < F := by dsimp only [F]; positivity
  have hV : 0 < V := Real.rpow_pos_of_pos (div_pos (by norm_num) (sq_pos_of_pos (by linarith))) _
  have hC2 : 2 ≤ C := le_add_of_nonneg_right (by positivity)
  have hC : 1 ≤ C := by linarith only [hC2]
  have hCp : 0 < Cp := by dsimp only [Cp]; positivity
  refine ⟨C, Cp, hC, hCp, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P T hP hT ν hν t ht U U₈
  have hf := (holder_average_memLp_of_local_time h0 d hd D p hp Q hQ β a μ hβ ha hμ
    ζ P T hP hT ν t ht).1
  refine ⟨hf, ?_⟩
  have ht8 : ((t : ℝ) / 8).toNNReal = t / 8 := by
    change (↑(t / 8) : ℝ).toNNReal = t / 8
    exact Real.toNNReal_coe
  have he (s : ℝ≥0) : centeredComplexLp Q (P s (centeredComplexLp Q
      (indexedEndpoint hd Q ν ζ P T β a μ 0))) =
      indexedEndpoint hd Q ν ζ P T β a μ s :=
    holder_forward_endpoint_restart hd Q β a μ ζ P T hP ν hν s
  have hw := hwindow Q ζ P T hP hT (indexedEndpoint hd Q ν ζ P T β a μ 0) (t : ℝ) ht
  simp only [he, ht8] at hw
  have hu := hw hf (t : ℝ) ⟨by linarith only [ht], le_rfl⟩
  simp only [Real.toNNReal_coe] at hu
  let N := (eLpNorm (U₈ : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal
  let w := 1 + ‖ζ‖ * Real.sqrt (t : ℝ)
  let E := Real.exp (Cp * ‖ζ‖ ^ 2 * (t : ℝ))
  let R := Real.sqrt (t : ℝ) / (4 * w)
  let r := (1 - θ) * R
  let M := (2 * Real.exp (Cg * ‖ζ‖ ^ 2 * (t : ℝ)) +
    Cs * ‖ζ‖ * Real.sqrt (t : ℝ) * Real.exp (Cs * ‖ζ‖ ^ 2 * (t : ℝ))) * N
  let M₀ := 2 * Real.exp (Cw * ‖ζ‖ ^ 2 * (t : ℝ)) * N
  let A := (L / θ ^ α) * (1 + ‖ζ‖ * R) * M
  have hN : 0 ≤ N := ENNReal.toReal_nonneg
  have hw1 : 1 ≤ w := le_add_of_nonneg_right (mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))
  have hwpos : 0 < w := lt_of_lt_of_le zero_lt_one hw1
  obtain ⟨hR, htime, hforce, hRsq, hRz⟩ := holder_forward_force_radius ht (norm_nonneg ζ)
  change 0 < R at hR
  change (t : ℝ) / 4 ≤ (t : ℝ) - 2 * R ^ 2 at htime
  change R ≤ Real.sqrt (t : ℝ) / w at hforce
  change R ^ 2 = (t : ℝ) / (16 * w ^ 2) at hRsq
  change 1 + ‖ζ‖ * R ≤ 2 at hRz
  have hr : 0 < r := mul_pos (by linarith only [hθhalf]) hR
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  have hM₀ : 0 ≤ M₀ := by dsimp only [M₀]; positivity
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hUM : eLpNorm (U : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) ≤
      ENNReal.ofReal M₀ := by
    calc
      _ ≤ ENNReal.ofReal (2 * Real.exp (Cw * ‖ζ‖ ^ 2 * (t : ℝ))) *
          eLpNorm (U₈ : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) := hu.2
      _ = ENNReal.ofReal M₀ := by
        rw [← ENNReal.ofReal_toReal hf.eLpNorm_ne_top, ← ENNReal.ofReal_mul (by positivity)]
  have hinc : ∀ x : EinsteinRelation.Vec d, euclideanNorm x ≤ r →
      eLpNorm (fun ω => U (translate x ω) - U ω) (ENNReal.ofReal p) (reducedLaw Q) ≤
        ENNReal.ofReal (A * (euclideanNorm x / r) ^ α) := by
    intro x hx
    have hb := (hincrements Q hQ β a μ hβ ha hμ ζ P T hP hT ν hν t ht).2
      R hR htime hforce (0 : EinsteinRelation.Vec d) x
      (by simpa only [sub_zero, show vecEuclideanNorm x = euclideanNorm x from rfl] using hx)
    simp only [translate_zero, sub_zero] at hb
    have hm := (hu.1.comp_measurePreserving (measurePreserving_translate
      (reducedLaw Q) (reducedLaw_stationary Q) x)).sub hu.1
    apply (ENNReal.le_ofReal_iff_toReal_le hm.eLpNorm_ne_top (mul_nonneg hA (Real.rpow_nonneg (div_nonneg (Real.sqrt_nonneg _) hr.le) α))).mpr
    refine hb.trans_eq ?_
    have hbase : vecEuclideanNorm x / (θ * ((1 - θ) * R)) = (euclideanNorm x / r) / θ := by
      change euclideanNorm x / (θ * r) = (euclideanNorm x / r) / θ
      rw [div_div, mul_comm r θ]
    rw [hbase, Real.div_rpow (show 0 ≤ euclideanNorm x / r from
      div_nonneg (Real.sqrt_nonneg _) hr.le) hθ.le α]
    dsimp only [A, L, J, M, N, U₈, euclideanNorm]
    ring
  have hEg : Real.exp ((Cg + Cs) * ‖ζ‖ ^ 2 * (t : ℝ)) ≤ E := by
    apply Real.exp_le_exp.mpr
    dsimp only [Cp]
    nlinarith only [mul_nonneg hCw.le (mul_nonneg (sq_nonneg ‖ζ‖) t.coe_nonneg)]
  have hEw : Real.exp (Cw * ‖ζ‖ ^ 2 * (t : ℝ)) ≤ E := by
    apply Real.exp_le_exp.mpr
    dsimp only [Cp]
    nlinarith only [mul_nonneg (add_nonneg hCg.le hCs.le)
      (mul_nonneg (sq_nonneg ‖ζ‖) t.coe_nonneg)]
  have hMbound : M ≤ (2 + Cs) * w * E * N :=
    (holder_forward_corrected_amplitude_bound hCs.le hCg.le (norm_nonneg ζ) t.coe_nonneg hN).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hEg (by positivity)) hN)
  have hM₀bound : M₀ ≤ 2 * E * N :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hEw (by norm_num)) hN
  have hAM : A + 2 * M₀ ≤ F * w * E * N := by
    have hAbound : A ≤ (L / θ ^ α) * 2 * ((2 + Cs) * w * E * N) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left hRz (by positivity)) hMbound hM
        (by positivity)
    have hM₀w : M₀ ≤ 2 * w * E * N := by
      exact hM₀bound.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith only [hw1] : 2 ≤ 2 * w)
          (Real.exp_nonneg _)) hN)
    have hh := add_le_add hAbound (mul_le_mul_of_nonneg_left hM₀w (by norm_num : (0 : ℝ) ≤ 2))
    exact hh.trans_eq (by dsimp only [F]; ring)
  intro b hb _hbmax hbt
  obtain ⟨hmem, hbound⟩ := hgauss Q U A M₀ r hA hM₀ hr hu.1 hUM hinc
    (b * (t : ℝ)) hbt
  refine ⟨hmem, ?_⟩
  have hratio : b * (t : ℝ) / r ^ 2 = (16 / (1 - θ) ^ 2) * b * w ^ 2 := by
    dsimp only [r]
    rw [mul_pow, hRsq]
    field_simp
  have hscale : (b * (t : ℝ) / r ^ 2) ^ (α / 2) = V * b ^ (α / 2) * w ^ α := by
    rw [hratio, Real.mul_rpow (mul_nonneg (by positivity) hb.le) (sq_nonneg w),
      Real.mul_rpow (by positivity : 0 ≤ 16 / (1 - θ) ^ 2) hb.le,
      ← Real.rpow_natCast_mul hwpos.le]
    congr 2
    ring
  have hpoww : w ^ α ≤ w := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hw1 hα1.le
  have hpowC : w ^ 2 ≤ w ^ C := by
    simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_le hw1 hC2
  have hpref : H * F * V ≤ C := by dsimp only [C]; linarith
  calc
    _ ≤ H * (F * w * E * N) * (b * (t : ℝ) / r ^ 2) ^ (α / 2) := by
      exact hbound.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hAM hH.le)
        (Real.rpow_nonneg (div_nonneg hbt.le (sq_nonneg r)) _))
    _ = (H * F * V) * b ^ (α / 2) * (w * w ^ α) * E * N := by rw [hscale]; ring
    _ ≤ (H * F * V) * b ^ (α / 2) * (w * w) * E * N := by gcongr
    _ ≤ C * b ^ (α / 2) * w ^ C * E * N := by
      rw [← sq]
      gcongr

end EinsteinFull.Blueprint
