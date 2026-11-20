import EinsteinFull.Regeneration.StationaryTimeTest

/-!
# Spatial tests for stationary energy functions

Spatial slices of parabolic tests retain their compact support and first
spatial derivatives.
-/

open MeasureTheory Set
open scoped ENNReal

namespace EinsteinFull.Regeneration

/-- A spatial slice of a compact parabolic test is a compact `C¹` test. -/
theorem parabolic_test_spatial_slice {d : ℕ} {U : Set (PDE.Vec d)} {I : Set ℝ}
    (φ : PDE.ParTestFunction U I) (t : ℝ) :
    ContDiff ℝ 1 (fun x => φ.toFun (x, t)) ∧
      HasCompactSupport (fun x => φ.toFun (x, t)) ∧
      tsupport (fun x => φ.toFun (x, t)) ⊆ U := by
  let K : Set (PDE.Vec d) := Prod.fst '' tsupport φ.toFun
  have hK : IsCompact K := φ.hasCompactSupport.isCompact.image continuous_fst
  have hKU : K ⊆ U := by
    rintro x ⟨z, hz, rfl⟩
    exact (φ.tsupport_subset hz).1
  have hs : Function.support (fun x => φ.toFun (x, t)) ⊆ K := by
    intro x hx
    exact ⟨(x, t), subset_tsupport φ.toFun hx, rfl⟩
  have hts : tsupport (fun x => φ.toFun (x, t)) ⊆ K :=
    closure_minimal hs hK.isClosed
  refine ⟨φ.contDiff.comp (contDiff_id.prodMk contDiff_const), ?_, hts.trans hKU⟩
  exact HasCompactSupport.of_support_subset_isCompact hK hs

/-- The spatial derivative of a parabolic test is the derivative of its slice. -/
theorem parSpaceGrad_eq_spaceGradC1_slice {d : ℕ} (φ : PDE.Vec d × ℝ → ℝ)
    (hφ : ContDiff ℝ 1 φ) (x : PDE.Vec d) (t : ℝ) :
    PDE.parSpaceGrad φ (x, t) = PDE.spaceGradC1 (fun y => φ (y, t)) x := by
  ext i
  have h1 : HasFDerivAt φ (fderiv ℝ φ (x, t)) (x, t) :=
    (hφ.differentiable (by norm_num) (x, t)).hasFDerivAt
  have h2 : HasFDerivAt (fun y : PDE.Vec d => ((y, t) : PDE.Vec d × ℝ))
      ((ContinuousLinearMap.id ℝ (PDE.Vec d)).prod 0) x :=
    (hasFDerivAt_id x).prodMk (hasFDerivAt_const t x)
  have h3 : fderiv ℝ (fun y : PDE.Vec d => φ (y, t)) x =
      (fderiv ℝ φ (x, t)).comp ((ContinuousLinearMap.id ℝ (PDE.Vec d)).prod 0) :=
    (h1.comp x h2).fderiv
  unfold PDE.parSpaceGrad PDE.spaceGradC1
  rw [h3]
  simp

/-- A divergence-free spatial `L²` flux pairs to zero with every parabolic test. -/
theorem stationary_space_test_eq_zero {d : ℕ} (U : Set (PDE.Vec d)) (I : Set ℝ)
    [IsFiniteMeasure (volume.restrict I : Measure ℝ)] (F : PDE.Vec d → PDE.Vec d)
    (hF : ∀ i, MemLp (fun x => F x i) 2 (volume.restrict U))
    (hweak : ∀ ψ : PDE.Vec d → ℝ, ContDiff ℝ 1 ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U →
      IntegrableOn (fun x => PDE.vecDot (F x) (PDE.spaceGradC1 ψ x)) U ∧
        (∫ x in U, PDE.vecDot (F x) (PDE.spaceGradC1 ψ x)) = 0)
    (φ : PDE.ParTestFunction U (interior I)) :
    Integrable (fun z : PDE.Vec d × ℝ => PDE.vecDot (F z.1) (PDE.parSpaceGrad φ.toFun z))
      (volume.restrict (U ×ˢ I)) ∧
    (∫ z in U ×ˢ I, PDE.vecDot (F z.1) (PDE.parSpaceGrad φ.toFun z)) = 0 := by
  have hG (i : Fin d) : MemLp (fun z : PDE.Vec d × ℝ => F z.1 i) 2
      (volume.restrict (U ×ˢ I)) := by
    rw [PDE.Parabolic.Energy.volume_restrict_prod]
    exact (hF i).comp_fst (volume.restrict I)
  have hD (i : Fin d) : MemLp (fun z => PDE.parSpaceGrad φ.toFun z i) 2
      (volume.restrict (U ×ˢ I)) := by
    have hc : Continuous (fun z => PDE.parSpaceGrad φ.toFun z i) := by
      unfold PDE.parSpaceGrad
      exact (φ.contDiff.continuous_fderiv_apply (by norm_num)).comp
        (continuous_id.prodMk continuous_const)
    have hk : HasCompactSupport (fun z => PDE.parSpaceGrad φ.toFun z i) :=
      φ.hasCompactSupport.fderiv_apply ℝ (PDE.basisVec i, 0)
    exact (hc.memLp_of_hasCompactSupport hk).mono_measure Measure.restrict_le_self
  have hint : Integrable (fun z : PDE.Vec d × ℝ =>
      PDE.vecDot (F z.1) (PDE.parSpaceGrad φ.toFun z)) (volume.restrict (U ×ˢ I)) := by
    change Integrable (fun z => ∑ i : Fin d, F z.1 i * PDE.parSpaceGrad φ.toFun z i) _
    exact integrable_finsetSum Finset.univ (fun i _ => (hG i).integrable_mul (hD i))
  refine ⟨hint, ?_⟩
  rw [PDE.Parabolic.Energy.volume_restrict_prod] at hint ⊢
  rw [integral_prod_symm _ hint]
  apply integral_eq_zero_of_ae
  filter_upwards [] with t
  obtain ⟨hsmooth, hcompact, hsupport⟩ := parabolic_test_spatial_slice φ t
  obtain ⟨_, heq⟩ := hweak (fun x => φ.toFun (x, t)) hsmooth hcompact hsupport
  simp_rw [parSpaceGrad_eq_spaceGradC1_slice φ.toFun φ.contDiff] 
  simpa only [Pi.zero_apply] using heq

/-- An elliptic weak solution for compact `C¹` tests lifts to a stationary parabolic solution. -/
theorem stationary_isParabolicWeakSolution {d : ℕ} (U : Set (PDE.Vec d)) (I : Set ℝ)
    [IsFiniteMeasure (volume.restrict I : Measure ℝ)] (v : PDE.Vec d → ℝ)
    (g : PDE.Vec d → PDE.Vec d) (a : PDE.Vec d → PDE.Mat d)
    (hv : MemLp v 2 (volume.restrict U))
    (hg : ∀ i, MemLp (fun x => g x i) 2 (volume.restrict U))
    (hgrad : PDE.HasWeakGradientOn U v g)
    (hflux : ∀ i, MemLp (fun x => PDE.matVecMul (a x) (g x) i) 2 (volume.restrict U))
    (hweak : ∀ ψ : PDE.Vec d → ℝ, ContDiff ℝ 1 ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U →
      IntegrableOn (fun x => PDE.vecDot (PDE.matVecMul (a x) (g x)) (PDE.spaceGradC1 ψ x)) U ∧
        (∫ x in U, PDE.vecDot (PDE.matVecMul (a x) (g x)) (PDE.spaceGradC1 ψ x)) = 0) :
    PDE.IsParabolicWeakSolution (fun z => a z.1) U I (stationaryParH1 U I v g hv hg hgrad) := by
  intro φ
  obtain ⟨ht, hteq⟩ := stationary_time_test_eq_zero U I v hv φ
  obtain ⟨hs, hseq⟩ := stationary_space_test_eq_zero U I
    (fun x => PDE.matVecMul (a x) (g x)) hflux hweak φ
  change Integrable (fun z : PDE.Vec d × ℝ =>
    -(v z.1 * PDE.parTimeDeriv φ.toFun z) +
      PDE.vecDot (PDE.matVecMul (a z.1) (g z.1)) (PDE.parSpaceGrad φ.toFun z))
      (volume.restrict (U ×ˢ I)) ∧ _
  refine ⟨ht.neg.add hs, ?_⟩
  change (∫ z in U ×ˢ I, -(v z.1 * PDE.parTimeDeriv φ.toFun z) +
    PDE.vecDot (PDE.matVecMul (a z.1) (g z.1)) (PDE.parSpaceGrad φ.toFun z)) = 0
  have hsum := integral_add ht.neg hs
  simp only [Pi.neg_apply] at hsum
  rw [hsum, integral_neg, hteq, hseq]
  ring

end EinsteinFull.Regeneration
