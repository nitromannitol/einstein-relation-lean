import EinsteinFull.External.Source.GMPDirichletKernel
import EinsteinFull.Calculus.FellerRegularSet
import Mathlib.Topology.MetricSpace.Thickening
import EinsteinFull.Calculus.C13TubeWeakGradientChain
import PDEFoundation.Sobolev.Ch4.Compact
import EinsteinFull.Calculus.C9TubeWeightedZeroPast
import EinsteinFull.Calculus.C13TubeSpatialTranslation

open EinsteinRelation EinsteinFull.External.Source.GMP MeasureTheory Filter
open scoped Topology

namespace EinsteinFull.Calculus

/-- A compactly supported function inside the cylinder has a uniform
neighborhood still contained in the cylinder. -/
theorem c17_cylinder_support_thickening {d : ℕ} {a b R : ℝ}
    (ψ : ℝ × Vec d → ℝ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ Set.Ioo a b ×ˢ sourceBall 0 R) :
    ∃ ε : ℝ, 0 < ε ∧ Metric.cthickening ε (tsupport ψ) ⊆
      Set.Ioo a b ×ˢ sourceBall 0 R := by
  have ho : IsOpen (sourceBall (0 : Vec d) R) := by
    unfold sourceBall
    exact isOpen_lt ((Feller.continuous_euclideanNorm d).comp
      (continuous_id.sub continuous_const)) continuous_const
  exact hc.exists_cthickening_subset_open (isOpen_Ioo.prod ho) hs

/-- The zero extension of a spatial Sobolev function with compact support
inside an open set retains its actual weak gradient. -/
theorem c17_spatial_weak_gradient_zero_extension {d : ℕ}
    {U K : Set (Vec d)} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (f : Vec d → ℝ) (G : Vec d → Vec d)
    (hf : MemLp f 2 (volume.restrict U))
    (hG : MemLp (fun x => euclideanNorm (G x)) 2 (volume.restrict U))
    (hw : HasWeakGradient U f G)
    (hf0 : ∀ x ∈ U, x ∉ K → f x = 0) :
    HasWeakGradient Set.univ (U.indicator f) (U.indicator G) := by
  have hcoord (i : Fin d) : MemLp (fun x => G x i) 2 (volume.restrict U) := by
    apply hG.mono' (hw i).2.1.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun x => by
      simpa only [TimeChange.euclideanNorm_eq_norm_toLp] using
        (PiLp.norm_apply_le (WithLp.toLp 2 (G x)) i)
  have hpde : PDE.HasWeakGradientOn U f G := by
    intro i φ hφ hc hs
    simpa only [coordinateDerivative, PDE.basisVec, unitVector] using
      (hw i).2.2 φ ⟨hφ, hc, hs⟩
  let w : PDE.H1Function U := ⟨f, G, hf, hcoord, hpde⟩
  have hfi : MemLp (U.indicator f) 2 volume :=
    (memLp_indicator_iff_restrict hU.measurableSet).2 hf
  intro i
  have hgi : MemLp (U.indicator (fun x => G x i)) 2 volume :=
    (memLp_indicator_iff_restrict hU.measurableSet).2 (hcoord i)
  have hder := PDE.Ch4Infra.hasWeakPartialDerivOn_univ_zeroExtend hU w hKU hK hf0 i
  have heq : (fun x => (U.indicator G x) i) = U.indicator (fun x => G x i) := by
    funext x
    by_cases hx : x ∈ U <;> simp [Set.indicator, hx]
  refine ⟨?_, ?_, ?_⟩
  · simpa only [locallyIntegrableOn_univ] using hfi.locallyIntegrable (by norm_num)
  · rw [heq]
    simpa only [locallyIntegrableOn_univ] using hgi.locallyIntegrable (by norm_num)
  · intro φ hφ
    have heq' (x : Vec d) : (U.indicator G x) i = U.indicator (fun x => G x i) x :=
      congrFun heq x
    simpa only [w, coordinateDerivative, PDE.basisVec, unitVector, heq'] using
      hder φ hφ.1 hφ.2.1 hφ.2.2

/-- Almost every spatial slice of a compactly supported space-time Sobolev
function has the zero-extended weak gradient on the whole space. -/
theorem c17_spacetime_slice_weak_gradient_zero_extension {d : ℕ}
    {I : Set ℝ} {U : Set (Vec d)} (hU : IsOpen U)
    (f : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hf : MemLp f 2 (volume.restrict (I ×ˢ U)))
    (hG : MemLp (fun z => euclideanNorm (G z)) 2 (volume.restrict (I ×ˢ U)))
    (hw : ∀ᵐ t ∂volume.restrict I,
      HasWeakGradient U (fun x => f (t, x)) (fun x => G (t, x)))
    (hc : HasCompactSupport f) (hs : tsupport f ⊆ I ×ˢ U) :
    ∀ᵐ t ∂volume.restrict I,
      HasWeakGradient Set.univ (U.indicator (fun x => f (t, x)))
        (U.indicator (fun x => G (t, x))) := by
  let K : Set (Vec d) := Prod.snd '' tsupport f
  have hK : IsCompact K := hc.image continuous_snd
  have hKU : K ⊆ U := by
    rintro x ⟨z, hz, rfl⟩
    exact (hs hz).2
  have hf' : MemLp f 2 ((volume.restrict I).prod (volume.restrict U)) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact hf
  have hG' : MemLp (fun z => euclideanNorm (G z)) 2
      ((volume.restrict I).prod (volume.restrict U)) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact hG
  filter_upwards [c9_memLp_prod_right_ae _ _ _ hf',
    c9_memLp_prod_right_ae _ _ _ hG', hw] with t hft hGt hwt
  apply c17_spatial_weak_gradient_zero_extension hU hK hKU _ _ hft hGt hwt
  intro x hx hxK
  apply image_eq_zero_of_notMem_tsupport
  intro htx
  exact hxK ⟨(t, x), htx, rfl⟩

/-- Zero extension in time and space gives a whole-time family of spatial
weak gradients and preserves the two square-integrability estimates. -/
theorem c17_spacetime_zero_extension {d : ℕ}
    {I : Set ℝ} {U : Set (Vec d)} (hI : MeasurableSet I) (hU : IsOpen U)
    (f : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hf : MemLp f 2 (volume.restrict (I ×ˢ U)))
    (hG : MemLp (fun z => euclideanNorm (G z)) 2 (volume.restrict (I ×ˢ U)))
    (hw : ∀ᵐ t ∂volume.restrict I,
      HasWeakGradient U (fun x => f (t, x)) (fun x => G (t, x)))
    (hc : HasCompactSupport f) (hs : tsupport f ⊆ I ×ˢ U) :
    MemLp ((I ×ˢ U).indicator f) 2 volume ∧
    MemLp (fun z => euclideanNorm ((I ×ˢ U).indicator G z)) 2 volume ∧
    ∀ᵐ t ∂volume, HasWeakGradient Set.univ
      (fun x => (I ×ˢ U).indicator f (t, x))
      (fun x => (I ×ˢ U).indicator G (t, x)) := by
  have hS : MeasurableSet (I ×ˢ U) := hI.prod hU.measurableSet
  have hfi := (memLp_indicator_iff_restrict hS).2 hf
  have hGi := (memLp_indicator_iff_restrict hS).2 hG
  have heq : (fun z => euclideanNorm ((I ×ˢ U).indicator G z)) =
      (I ×ˢ U).indicator (fun z => euclideanNorm (G z)) := by
    funext z
    by_cases hz : z ∈ I ×ˢ U
    · simp only [Set.indicator_of_mem hz]
    · simp only [Set.indicator_of_notMem hz, TimeChange.euclideanNorm_eq_norm_toLp,
        WithLp.toLp_zero, norm_zero]
  refine ⟨hfi, heq ▸ hGi, ?_⟩
  have hslices := c17_spacetime_slice_weak_gradient_zero_extension hU f G hf hG hw hc hs
  filter_upwards [(ae_restrict_iff' hI).1 hslices] with t ht
  by_cases hti : t ∈ I
  · have ef : (fun x => (I ×ˢ U).indicator f (t, x)) =
        U.indicator (fun x => f (t, x)) := by
      funext x
      by_cases hx : x ∈ U
      · rw [Set.indicator_of_mem (show (t, x) ∈ I ×ˢ U from ⟨hti, hx⟩), Set.indicator_of_mem hx]
      · rw [Set.indicator_of_notMem (fun h => hx h.2), Set.indicator_of_notMem hx]
    have eg : (fun x => (I ×ˢ U).indicator G (t, x)) =
        U.indicator (fun x => G (t, x)) := by
      funext x
      by_cases hx : x ∈ U
      · rw [Set.indicator_of_mem (show (t, x) ∈ I ×ˢ U from ⟨hti, hx⟩), Set.indicator_of_mem hx]
      · rw [Set.indicator_of_notMem (fun h => hx h.2), Set.indicator_of_notMem hx]
    rw [ef, eg]
    exact ht hti
  · simpa [Set.indicator, Set.mem_prod, hti] using c9_zero_weak_gradient (d := d) Set.univ

/-- The compactly supported value is already its own zero extension; each
coordinate of the zero-extended spatial gradient is square-integrable. -/
theorem c17_spacetime_zero_extension_coordinates {d : ℕ}
    {I : Set ℝ} {U : Set (Vec d)} (hI : MeasurableSet I) (hU : IsOpen U)
    (f : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hf : MemLp f 2 (volume.restrict (I ×ˢ U)))
    (hGm : AEStronglyMeasurable G (volume.restrict (I ×ˢ U)))
    (hG : MemLp (fun z => euclideanNorm (G z)) 2 (volume.restrict (I ×ˢ U)))
    (hw : ∀ᵐ t ∂volume.restrict I,
      HasWeakGradient U (fun x => f (t, x)) (fun x => G (t, x)))
    (hc : HasCompactSupport f) (hs : tsupport f ⊆ I ×ˢ U) :
    MemLp f 2 volume ∧
    (∀ i, MemLp (fun z => ((I ×ˢ U).indicator G z) i) 2 volume) ∧
    ∀ᵐ t ∂volume, HasWeakGradient Set.univ (fun x => f (t, x))
      (fun x => (I ×ˢ U).indicator G (t, x)) := by
  have hfext : (I ×ˢ U).indicator f = f := by
    apply Set.indicator_eq_self.mpr
    exact (show Function.support f ⊆ tsupport f from subset_closure).trans hs
  obtain ⟨hfi, _, hweak⟩ := c17_spacetime_zero_extension hI hU f G hf hG hw hc hs
  refine ⟨hfext ▸ hfi, ?_, ?_⟩
  · intro i
    have hcoord : MemLp (fun z => G z i) 2 (volume.restrict (I ×ˢ U)) := by
      apply hG.mono' ((continuous_apply i).comp_aestronglyMeasurable hGm)
      exact Filter.Eventually.of_forall fun z => by
        simpa only [TimeChange.euclideanNorm_eq_norm_toLp] using
          (PiLp.norm_apply_le (WithLp.toLp 2 (G z)) i)
    have hi := (memLp_indicator_iff_restrict (hI.prod hU.measurableSet)).2 hcoord
    have heq : (fun z => ((I ×ˢ U).indicator G z) i) =
        (I ×ˢ U).indicator (fun z => G z i) := by
      funext z
      by_cases hz : z ∈ I ×ˢ U <;> simp [Set.indicator, hz]
    rw [heq]
    exact hi
  · simpa only [hfext] using hweak

/-- A smooth compact space-time test restricts to a smooth compact spatial
 test, and its spatial coordinate derivative is the joint derivative. -/
theorem c17_spacetime_test_slice {d : ℕ} (φ : ℝ × Vec d → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) (t : ℝ) :
    IsSpatialTest Set.univ (fun x => φ (t, x)) ∧
    ∀ (i : Fin d) (x : Vec d), coordinateDerivative i (fun y => φ (t, y)) x =
      fderiv ℝ φ (t, x) (0, unitVector i) := by
  have hs : ContDiff ℝ (⊤ : ℕ∞) (fun x => φ (t, x)) :=
    hφ.comp (contDiff_prodMk_right t)
  have hk : HasCompactSupport (fun x => φ (t, x)) := by
    apply HasCompactSupport.of_support_subset_isCompact (hc.image continuous_snd)
    intro x hx
    refine ⟨(t, x), ?_, rfl⟩
    exact subset_closure hx
  refine ⟨⟨hs, hk, Set.subset_univ _⟩, ?_⟩
  intro i x
  have hd : HasFDerivAt (fun y : Vec d => (t, y))
      (ContinuousLinearMap.inr ℝ ℝ (Vec d)) x := hasFDerivAt_prodMk_right t x
  unfold coordinateDerivative
  change fderiv ℝ (φ ∘ (fun y : Vec d => (t, y))) x (unitVector i) = _
  rw [fderiv_comp x (hφ.differentiable (by simp) (t, x)) hd.differentiableAt, hd.fderiv]
  rfl

/-- Slice weak gradients give the spatial integration-by-parts identity for
almost every time against any fixed smooth compact space-time test. -/
theorem c17_spacetime_weak_gradient_test_slices {d : ℕ}
    (f : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hw : ∀ᵐ t ∂volume, HasWeakGradient Set.univ
      (fun x => f (t, x)) (fun x => G (t, x)))
    (φ : ℝ × Vec d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hc : HasCompactSupport φ) (i : Fin d) :
    ∀ᵐ t ∂volume,
      (∫ x, f (t, x) * fderiv ℝ φ (t, x) (0, unitVector i)) =
        -(∫ x, G (t, x) i * φ (t, x)) := by
  filter_upwards [hw] with t ht
  obtain ⟨htest, hder⟩ := c17_spacetime_test_slice φ hφ hc t
  have heq := (ht i).2.2 (fun x => φ (t, x)) htest
  simpa only [Measure.restrict_univ, hder] using heq

/-- Integrating the slice identities yields the joint distributional spatial
 derivative identity for every smooth compactly supported space-time test. -/
theorem c17_spacetime_weak_gradient_test {d : ℕ}
    (f : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hf : MemLp f 2 volume) (hG : ∀ i, MemLp (fun z => G z i) 2 volume)
    (hw : ∀ᵐ t ∂volume, HasWeakGradient Set.univ
      (fun x => f (t, x)) (fun x => G (t, x)))
    (φ : ℝ × Vec d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hc : HasCompactSupport φ) (i : Fin d) :
    (∫ z, f z * fderiv ℝ φ z (0, unitVector i)) =
      -(∫ z, G z i * φ z) := by
  have hφ2 : MemLp φ 2 volume := hφ.continuous.memLp_of_hasCompactSupport hc
  have hD2 : MemLp (fun z => fderiv ℝ φ z (0, unitVector i)) 2 volume :=
    ((hφ.continuous_fderiv_apply (by simp)).comp
      (continuous_id.prodMk continuous_const)).memLp_of_hasCompactSupport
        (hc.fderiv_apply ℝ (0, unitVector i))
  have hfD := hf.integrable_mul hD2
  have hGφ := (hG i).integrable_mul hφ2
  calc
    (∫ z, f z * fderiv ℝ φ z (0, unitVector i)) =
        ∫ t, ∫ x, f (t, x) * fderiv ℝ φ (t, x) (0, unitVector i) := by
      exact integral_prod _ hfD
    _ = ∫ t, -(∫ x, G (t, x) i * φ (t, x)) :=
      integral_congr_ae (c17_spacetime_weak_gradient_test_slices f G hw φ hφ hc i)
    _ = -(∫ t, ∫ x, G (t, x) i * φ (t, x)) := integral_neg _
    _ = -(∫ z, G z i * φ z) := by
      congr 1
      exact (integral_prod _ hGφ).symm

/-- The first coordinate is time and the remaining coordinates are space. -/
def c17SpaceTimeEquiv (d : ℕ) : (ℝ × Vec d) ≃L[ℝ] Vec (d + 1) :=
  Fin.consEquivL ℝ (fun _ : Fin (d + 1) => ℝ)

/-- The space-time coordinate change preserves product Lebesgue measure. -/
theorem c17_spaceTimeEquiv_symm_measurePreserving (d : ℕ) :
    MeasurePreserving (c17SpaceTimeEquiv d).symm volume volume := by
  convert (volume_preserving_piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0) using 1
  rfl

/-- The inverse coordinate change also preserves Lebesgue measure. -/
theorem c17_spaceTimeEquiv_measurePreserving (d : ℕ) :
    MeasurePreserving (c17SpaceTimeEquiv d) volume volume := by
  convert ((volume_preserving_piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0).symm _) using 1
  funext z
  change Fin.cons z.1 z.2 = @Fin.insertNth d (fun _ : Fin (d + 1) => ℝ) 0 z.1 z.2
  exact (Fin.insertNth_zero' z.1 z.2).symm

/-- Transport a square-integrable space-time field to the coordinate space. -/
theorem c17_spaceTimeEquiv_memLp {d : ℕ} (f : ℝ × Vec d → ℝ)
    (hf : MemLp f 2 volume) :
    MemLp (fun z : Vec (d + 1) => f ((c17SpaceTimeEquiv d).symm z)) 2 volume :=
  hf.comp_measurePreserving (c17_spaceTimeEquiv_symm_measurePreserving d)

/-- A spatial unit vector becomes the corresponding successor coordinate. -/
theorem c17_spaceTimeEquiv_spatial_basis {d : ℕ} (i : Fin d) :
    c17SpaceTimeEquiv d (0, unitVector i) = PDE.basisVec i.succ := by
  ext j
  refine Fin.cases ?_ (fun k => ?_) j
  · simp [c17SpaceTimeEquiv, Fin.consEquivL, Fin.consLinearEquiv, PDE.basisVec]
  · simp [c17SpaceTimeEquiv, Fin.consEquivL, Fin.consLinearEquiv,
      PDE.basisVec, unitVector, Pi.single_apply]

/-- Derivatives of transported tests in spatial directions use successor coordinates. -/
theorem c17_spaceTimeEquiv_spatial_deriv {d : ℕ}
    (φ : Vec (d + 1) → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (z : ℝ × Vec d) (i : Fin d) :
    fderiv ℝ (φ ∘ c17SpaceTimeEquiv d) z (0, unitVector i) =
      fderiv ℝ φ (c17SpaceTimeEquiv d z) (PDE.basisVec i.succ) := by
  rw [fderiv_comp z (hφ.differentiable (by simp) _) (c17SpaceTimeEquiv d).differentiableAt,
    (c17SpaceTimeEquiv d).fderiv]
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe] using
    congrArg (fderiv ℝ φ (c17SpaceTimeEquiv d z)) (c17_spaceTimeEquiv_spatial_basis i)

/-- Spatial weak derivatives are preserved by the space-time coordinate change. -/
theorem c17_spaceTimeEquiv_weakPartialDeriv {d : ℕ}
    (f : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hf : MemLp f 2 volume) (hG : ∀ i, MemLp (fun z => G z i) 2 volume)
    (hw : ∀ᵐ t ∂volume, HasWeakGradient Set.univ
      (fun x => f (t, x)) (fun x => G (t, x))) (i : Fin d) :
    PDE.HasWeakPartialDerivOn Set.univ i.succ
      (fun z => f ((c17SpaceTimeEquiv d).symm z))
      (fun z => G ((c17SpaceTimeEquiv d).symm z) i) := by
  intro φ hφ hc _
  have h := c17_spacetime_weak_gradient_test f G hf hG hw
    (φ ∘ c17SpaceTimeEquiv d) (hφ.comp (c17SpaceTimeEquiv d).contDiff)
    (hc.comp_homeomorph (c17SpaceTimeEquiv d).toHomeomorph) i
  simp_rw [c17_spaceTimeEquiv_spatial_deriv φ hφ] at h
  simp only [Measure.restrict_univ]
  rw [← (c17_spaceTimeEquiv_measurePreserving d).integral_comp
      (c17SpaceTimeEquiv d).toHomeomorph.measurableEmbedding,
    ← (c17_spaceTimeEquiv_measurePreserving d).integral_comp
      (c17SpaceTimeEquiv d).toHomeomorph.measurableEmbedding]
  simpa only [ContinuousLinearEquiv.symm_apply_apply, Function.comp_apply] using h

/-- Mollification controls a chosen weak coordinate derivative without any
assumption on the other coordinate derivatives. -/
theorem c17_mollify_partial_derivative {d : ℕ} (f g : Vec d → ℝ)
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume)
    (hc : HasCompactSupport f) (i : Fin d)
    (hw : PDE.HasWeakPartialDerivOn Set.univ i f g)
    (a : ℕ → ℝ) (ha : ∀ n, 0 < a n) (ha1 : ∀ n, a n ≤ 1)
    (ha0 : Filter.Tendsto a Filter.atTop (nhds 0)) :
    (∀ n, ContDiff ℝ (⊤ : ℕ∞) (PDE.wholeSpaceMollify (a n) f) ∧
      HasCompactSupport (PDE.wholeSpaceMollify (a n) f) ∧
      tsupport (PDE.wholeSpaceMollify (a n) f) ⊆ Metric.cthickening (a n) (tsupport f)) ∧
    (∀ n, PDE.euclideanCoordDeriv i (PDE.wholeSpaceMollify (a n) f) =
      PDE.wholeSpaceMollify (a n) g) ∧
    Filter.Tendsto (fun n => eLpNorm (PDE.wholeSpaceMollify (a n) f - f) 2 volume)
      Filter.atTop (nhds 0) ∧
    Filter.Tendsto (fun n => eLpNorm (PDE.wholeSpaceMollify (a n) g - g) 2 volume)
      Filter.atTop (nhds 0) := by
  have hρ := PDE.isConvexApproxKernel_unitConvexApproxKernel (d := d)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n
    have hs := PDE.Ch4Infra.support_wholeSpaceMollify_subset_cthickening (h := f) (ha n)
    exact ⟨(PDE.contDiff_memLp_convolution_scaledConvexApproxKernel hρ (ha n)
      (by norm_num) (by norm_num) hf).1,
      HasCompactSupport.of_support_subset_isCompact (hc.isCompact.cthickening) hs,
      closure_minimal hs Metric.isClosed_cthickening⟩
  · intro n
    exact PDE.euclideanCoordDeriv_convolution_eq_of_hasWeakPartialDerivOn
      (PDE.hasCompactSupport_scaledConvexApproxKernel hρ.compactSupport (ha n))
      (PDE.contDiff_scaledConvexApproxKernel hρ _) (hf.locallyIntegrable (by norm_num)) hw
  · exact PDE.tendsto_eLpNorm_wholeSpaceMollify_sub (by norm_num) (by norm_num) hf ha ha1 ha0
  · exact PDE.tendsto_eLpNorm_wholeSpaceMollify_sub (by norm_num) (by norm_num) hg ha ha1 ha0

/-- The joint mollification is smooth and compactly supported; every spatial
 derivative is the corresponding mollification of the weak gradient. -/
theorem c17_spacetime_mollification {d : ℕ}
    (f : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hf : MemLp f 2 volume) (hG : ∀ i, MemLp (fun z => G z i) 2 volume)
    (hw : ∀ᵐ t ∂volume, HasWeakGradient Set.univ
      (fun x => f (t, x)) (fun x => G (t, x)))
    (hc : HasCompactSupport f) (a : ℕ → ℝ)
    (ha : ∀ n, 0 < a n) (ha1 : ∀ n, a n ≤ 1)
    (ha0 : Filter.Tendsto a Filter.atTop (nhds 0)) :
    ∀ n, ContDiff ℝ (⊤ : ℕ∞)
        (PDE.wholeSpaceMollify (a n) (f ∘ (c17SpaceTimeEquiv d).symm) ∘ c17SpaceTimeEquiv d) ∧
      HasCompactSupport
        (PDE.wholeSpaceMollify (a n) (f ∘ (c17SpaceTimeEquiv d).symm) ∘ c17SpaceTimeEquiv d) ∧
      ∀ (i : Fin d) (z : ℝ × Vec d),
        fderiv ℝ (PDE.wholeSpaceMollify (a n) (f ∘ (c17SpaceTimeEquiv d).symm) ∘
          c17SpaceTimeEquiv d) z (0, unitVector i) =
          PDE.wholeSpaceMollify (a n) ((fun z => G z i) ∘ (c17SpaceTimeEquiv d).symm)
            (c17SpaceTimeEquiv d z) := by
  let F := f ∘ (c17SpaceTimeEquiv d).symm
  have hF : MemLp F 2 volume := c17_spaceTimeEquiv_memLp f hf
  have hcF : HasCompactSupport F := hc.comp_homeomorph (c17SpaceTimeEquiv d).symm.toHomeomorph
  have hρ := PDE.isConvexApproxKernel_unitConvexApproxKernel (d := d + 1)
  intro n
  have hs : ContDiff ℝ (⊤ : ℕ∞) (PDE.wholeSpaceMollify (a n) F) :=
    (PDE.contDiff_memLp_convolution_scaledConvexApproxKernel hρ (ha n)
      (by norm_num) (by norm_num) hF).1
  have hk : HasCompactSupport (PDE.wholeSpaceMollify (a n) F) :=
    HasCompactSupport.of_support_subset_isCompact (hcF.isCompact.cthickening)
      (PDE.Ch4Infra.support_wholeSpaceMollify_subset_cthickening (ha n))
  refine ⟨hs.comp (c17SpaceTimeEquiv d).contDiff,
    hk.comp_homeomorph (c17SpaceTimeEquiv d).toHomeomorph, ?_⟩
  intro i z
  have hg := c17_spaceTimeEquiv_memLp (fun z => G z i) (hG i)
  have hweak := c17_spaceTimeEquiv_weakPartialDeriv f G hf hG hw i
  have hder := (c17_mollify_partial_derivative F _ hF hg hcF i.succ hweak a ha ha1 ha0).2.1 n
  rw [c17_spaceTimeEquiv_spatial_deriv _ hs]
  exact congrFun hder _

/-- A sufficiently small joint mollification stays inside any open set
containing the original compact support. -/
theorem c17_spacetime_mollification_support {d : ℕ}
    (f : ℝ × Vec d → ℝ) (hc : HasCompactSupport f)
    {U : Set (ℝ × Vec d)} (hU : IsOpen U) (hs : tsupport f ⊆ U) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r : ℝ, 0 < r → r ≤ δ →
      tsupport (PDE.wholeSpaceMollify r (f ∘ (c17SpaceTimeEquiv d).symm) ∘
        c17SpaceTimeEquiv d) ⊆ U := by
  let E := c17SpaceTimeEquiv d
  let F := f ∘ E.symm
  have hcF : HasCompactSupport F := hc.comp_homeomorph E.symm.toHomeomorph
  have hsF : tsupport F ⊆ E.symm ⁻¹' U := by
    change tsupport (f ∘ E.symm.toHomeomorph) ⊆ E.symm ⁻¹' U
    rw [tsupport_comp_eq_preimage f E.symm.toHomeomorph]
    exact Set.preimage_mono hs
  obtain ⟨δ, hδ, hδU⟩ := hcF.exists_cthickening_subset_open
    (hU.preimage E.symm.continuous) hsF
  refine ⟨δ, hδ, ?_⟩
  intro r hr hrδ z hz
  have hM : tsupport (PDE.wholeSpaceMollify r F) ⊆ Metric.cthickening r (tsupport F) :=
    closure_minimal (PDE.Ch4Infra.support_wholeSpaceMollify_subset_cthickening hr)
      Metric.isClosed_cthickening
  have hz' : E z ∈ tsupport (PDE.wholeSpaceMollify r F) := by
    change z ∈ tsupport (PDE.wholeSpaceMollify r F ∘ E.toHomeomorph) at hz
    rwa [tsupport_comp_eq_preimage] at hz
  have := hδU ((Metric.cthickening_mono hrδ (tsupport F)) (hM hz'))
  simpa only [Set.mem_preimage, ContinuousLinearEquiv.symm_apply_apply] using this

/-- Joint mollification converges in space-time L² under the coordinate change. -/
theorem c17_spacetime_mollification_tendsto {d : ℕ}
    (f : ℝ × Vec d → ℝ) (hf : MemLp f 2 volume)
    (a : ℕ → ℝ) (ha : ∀ n, 0 < a n) (ha1 : ∀ n, a n ≤ 1)
    (ha0 : Filter.Tendsto a Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => eLpNorm
      (fun z => PDE.wholeSpaceMollify (a n) (f ∘ (c17SpaceTimeEquiv d).symm)
        (c17SpaceTimeEquiv d z) - f z) 2 volume) Filter.atTop (nhds 0) := by
  let E := c17SpaceTimeEquiv d
  let F := f ∘ E.symm
  have hF : MemLp F 2 volume := c17_spaceTimeEquiv_memLp f hf
  have hρ := PDE.isConvexApproxKernel_unitConvexApproxKernel (d := d + 1)
  have hm (n : ℕ) : MemLp (PDE.wholeSpaceMollify (a n) F) 2 volume :=
    (PDE.contDiff_memLp_convolution_scaledConvexApproxKernel hρ (ha n)
      (by norm_num) (by norm_num) hF).2.1
  have he (n : ℕ) : eLpNorm
      (fun z => PDE.wholeSpaceMollify (a n) F (E z) - f z) 2 volume =
      eLpNorm (PDE.wholeSpaceMollify (a n) F - F) 2 volume := by
    have h := eLpNorm_comp_measurePreserving (p := 2) ((hm n).sub hF).aestronglyMeasurable
      (c17_spaceTimeEquiv_measurePreserving d)
    simpa only [Function.comp_def, Pi.sub_apply, F, E, ContinuousLinearEquiv.symm_apply_apply] using h
  simpa only [← he] using
    (PDE.tendsto_eLpNorm_wholeSpaceMollify_sub (p := 2) (by norm_num)
      (by norm_num) hF ha ha1 ha0)


/-- The Euclidean length is bounded by the sum of the coordinate magnitudes. -/
theorem c17_euclideanNorm_le_sum_abs {d : ℕ} (y : Vec d) :
    euclideanNorm y ≤ ∑ i, |y i| := by
  unfold euclideanNorm
  rw [Real.sqrt_le_left (Finset.sum_nonneg fun i _ => abs_nonneg _)]
  unfold euclideanSq dot
  calc ∑ i, y i * y i = ∑ i, |y i| * |y i| :=
        Finset.sum_congr rfl fun i _ => (abs_mul_abs_self _).symm
    _ ≤ ∑ i, |y i| * ∑ j, |y j| :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
          (Finset.single_le_sum (f := fun j => |y j|) (fun j _ => abs_nonneg _)
            (Finset.mem_univ i)) (abs_nonneg _)
    _ = (∑ i, |y i|) ^ 2 := by rw [← Finset.sum_mul, sq]

/-- Coordinatewise L² convergence implies convergence of Euclidean lengths. -/
theorem c17_euclideanNorm_tendsto_of_coordinates {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {d : ℕ} (V : ℕ → α → Vec d)
    (hm : ∀ n i, MemLp (fun x => V n x i) 2 μ)
    (ht : ∀ i, Filter.Tendsto (fun n => eLpNorm (fun x => V n x i) 2 μ)
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => eLpNorm (fun x => euclideanNorm (V n x)) 2 μ)
      Filter.atTop (nhds 0) := by
  have hbound (n : ℕ) : eLpNorm (fun x => euclideanNorm (V n x)) 2 μ ≤
      ∑ i : Fin d, eLpNorm (fun x => V n x i) 2 μ := by
    have hv : AEStronglyMeasurable (V n) μ :=
      (aemeasurable_pi_iff.mpr (fun i => (hm n i).aestronglyMeasurable.aemeasurable)).aestronglyMeasurable
    have hn := (Feller.continuous_euclideanNorm d).comp_aestronglyMeasurable hv
    calc
      _ ≤ eLpNorm (∑ i : Fin d, fun x => |V n x i|) 2 μ := by
        apply eLpNorm_mono_real hn
        intro x
        simpa only [Real.norm_eq_abs,
          abs_of_nonneg (show 0 ≤ euclideanNorm (V n x) from Real.sqrt_nonneg _),
          Finset.sum_apply] using c17_euclideanNorm_le_sum_abs (V n x)
      _ ≤ ∑ i : Fin d, eLpNorm (fun x => |V n x i|) 2 μ :=
        eLpNorm_sum_le (by norm_num)
      _ = ∑ i : Fin d, eLpNorm (fun x => V n x i) 2 μ := by
        apply Finset.sum_congr rfl
        intro i _
        simpa only [Real.norm_eq_abs] using
          eLpNorm_norm (fun x => V n x i) (hm n i).aestronglyMeasurable
  have hs : Filter.Tendsto (fun n => ∑ i : Fin d, eLpNorm (fun x => V n x i) 2 μ)
      Filter.atTop (nhds 0) := by
    simpa using tendsto_finsetSum Finset.univ (fun i _ => ht i)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hs
    (fun _ => bot_le) hbound


/-- Jointly smooth tests approximate a compactly supported spatial Sobolev field. -/
theorem c17_spacetime_spatial_sobolev_test_density
    {d : ℕ} {a b R : ℝ}
    (ψ : ℝ × Vec d → ℝ) (H : ℝ × Vec d → Vec d)
    (hψ : MemLp ψ 2 (volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R)))
    (hHm : AEStronglyMeasurable H (volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R)))
    (hH : MemLp (fun z => euclideanNorm (H z)) 2
      (volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R)))
    (hgrad : ∀ᵐ t ∂volume.restrict (Set.Ioo a b),
      HasWeakGradient (sourceBall 0 R) (fun x => ψ (t,x)) (fun x => H (t,x)))
    (hcompact : HasCompactSupport ψ)
    (hsupp : tsupport ψ ⊆ Set.Ioo a b ×ˢ sourceBall 0 R) :
    ∃ v : ℕ → (ℝ × Vec d → ℝ),
      (∀ n, ContDiff ℝ (⊤ : ℕ∞) (v n) ∧ HasCompactSupport (v n) ∧
        tsupport (v n) ⊆ Set.Ioo a b ×ˢ sourceBall 0 R) ∧
      Tendsto (fun n => eLpNorm (fun z => v n z - ψ z) 2
        (volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R))) atTop (𝓝 0) ∧
      Tendsto (fun n => eLpNorm (fun z => euclideanNorm
        ((fun j => fderiv ℝ (v n) z (0,unitVector j)) - H z)) 2
        (volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R))) atTop (𝓝 0) := by
  let U := Set.Ioo a b ×ˢ sourceBall (0 : Vec d) R
  have hball : IsOpen (sourceBall (0 : Vec d) R) := by
    unfold sourceBall
    exact isOpen_lt ((Feller.continuous_euclideanNorm d).comp
      (continuous_id.sub continuous_const)) continuous_const
  have hU : IsOpen U := isOpen_Ioo.prod hball
  let G := U.indicator H
  obtain ⟨hψall, hGall, hw⟩ := c17_spacetime_zero_extension_coordinates
    measurableSet_Ioo hball ψ H hψ hHm hH hgrad hcompact hsupp
  obtain ⟨δ, hδ, hδsupp⟩ := c17_spacetime_mollification_support ψ hcompact hU hsupp
  let c := min δ 1
  have hc : 0 < c := lt_min hδ (by norm_num)
  let r : ℕ → ℝ := fun n => c / (n + 1)
  have hr (n : ℕ) : 0 < r n := div_pos hc (by positivity)
  have hrc (n : ℕ) : r n ≤ c := by
    dsimp [r]
    exact div_le_self hc.le (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero n))
  have hr1 (n : ℕ) : r n ≤ 1 := (hrc n).trans (min_le_right _ _)
  have hrδ (n : ℕ) : r n ≤ δ := (hrc n).trans (min_le_left _ _)
  have hr0 : Tendsto r atTop (𝓝 0) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul c
    simpa only [r, div_eq_mul_inv, one_div, one_mul, mul_zero] using h
  let E := c17SpaceTimeEquiv d
  let v : ℕ → ℝ × Vec d → ℝ := fun n =>
    PDE.wholeSpaceMollify (r n) (ψ ∘ E.symm) ∘ E
  have hv := c17_spacetime_mollification ψ G hψall hGall hw hcompact r hr hr1 hr0
  have hval := c17_spacetime_mollification_tendsto ψ hψall r hr hr1 hr0
  let V : ℕ → ℝ × Vec d → Vec d := fun n z =>
    (fun i => PDE.wholeSpaceMollify (r n) ((fun z => G z i) ∘ E.symm) (E z)) - G z
  have hm (n : ℕ) (i : Fin d) : MemLp (fun z => V n z i) 2 volume := by
    have hi := c17_spaceTimeEquiv_memLp (fun z => G z i) (hGall i)
    have hρ := PDE.isConvexApproxKernel_unitConvexApproxKernel (d := d + 1)
    have hmoll := (PDE.contDiff_memLp_convolution_scaledConvexApproxKernel hρ (hr n)
      (by norm_num) (by norm_num) hi).2.1
    exact (hmoll.comp_measurePreserving (c17_spaceTimeEquiv_measurePreserving d)).sub (hGall i)
  have ht (i : Fin d) : Tendsto (fun n => eLpNorm (fun z => V n z i) 2 volume)
      atTop (𝓝 0) := c17_spacetime_mollification_tendsto (fun z => G z i) (hGall i)
        r hr hr1 hr0
  have hg := c17_euclideanNorm_tendsto_of_coordinates V hm ht
  refine ⟨v, ?_, ?_, ?_⟩
  · intro n
    exact ⟨(hv n).1, (hv n).2.1, hδsupp (r n) (hr n) (hrδ n)⟩
  · apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hval
      (fun _ => bot_le)
    intro n
    exact eLpNorm_mono_measure _ Measure.restrict_le_self
  · apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hg
      (fun _ => bot_le)
    intro n
    calc
      _ = eLpNorm (fun z => euclideanNorm (V n z)) 2 (volume.restrict U) := by
        apply eLpNorm_congr_ae
        filter_upwards [ae_restrict_mem hU.measurableSet] with z hz
        congr 1
        ext i
        change fderiv ℝ (v n) z (0, unitVector i) - H z i =
          PDE.wholeSpaceMollify (r n) ((fun z => G z i) ∘ E.symm) (E z) - G z i
        rw [show fderiv ℝ (v n) z (0, unitVector i) =
          PDE.wholeSpaceMollify (r n) ((fun z => G z i) ∘ E.symm) (E z) from
            (hv n).2.2 i z]
        rw [show G z = H z from Set.indicator_of_mem hz H]
      _ ≤ _ := eLpNorm_mono_measure _ Measure.restrict_le_self

/-- Spatial Sobolev density on a cylinder with arbitrary center. -/
theorem c17_spacetime_spatial_sobolev_test_density_at_center
    {d : ℕ} {y : Vec d} {a b R : ℝ}
    (ψ : ℝ × Vec d → ℝ) (H : ℝ × Vec d → Vec d)
    (hψ : MemLp ψ 2 (volume.restrict (Set.Ioo a b ×ˢ sourceBall y R)))
    (hHm : AEStronglyMeasurable H (volume.restrict (Set.Ioo a b ×ˢ sourceBall y R)))
    (hH : MemLp (fun z => euclideanNorm (H z)) 2
      (volume.restrict (Set.Ioo a b ×ˢ sourceBall y R)))
    (hgrad : ∀ᵐ t ∂volume.restrict (Set.Ioo a b),
      HasWeakGradient (sourceBall y R) (fun x => ψ (t,x)) (fun x => H (t,x)))
    (hcompact : HasCompactSupport ψ)
    (hsupp : tsupport ψ ⊆ Set.Ioo a b ×ˢ sourceBall y R) :
    ∃ v : ℕ → (ℝ × Vec d → ℝ),
      (∀ n, ContDiff ℝ (⊤ : ℕ∞) (v n) ∧ HasCompactSupport (v n) ∧
        tsupport (v n) ⊆ Set.Ioo a b ×ˢ sourceBall y R) ∧
      Tendsto (fun n => eLpNorm (fun z => v n z - ψ z) 2
        (volume.restrict (Set.Ioo a b ×ˢ sourceBall y R))) atTop (𝓝 0) ∧
      Tendsto (fun n => eLpNorm (fun z => euclideanNorm
        ((fun j => fderiv ℝ (v n) z (0,unitVector j)) - H z)) 2
        (volume.restrict (Set.Ioo a b ×ˢ sourceBall y R))) atTop (𝓝 0) := by
  let A : ℝ × Vec d := (0, y)
  let B : ℝ × Vec d := (0, -y)
  let T : ℝ × Vec d → ℝ × Vec d := fun z => z + A
  let S : ℝ × Vec d → ℝ × Vec d := fun z => z + B
  have hTS (z : ℝ × Vec d) : T (S z) = z := by
    rcases z with ⟨t, x⟩
    simp [T, S, A, B, add_assoc]
  have hm : MeasurePreserving T
      (volume.restrict (Set.Ioo a b ×ˢ sourceBall (0 : Vec d) R))
      (volume.restrict (Set.Ioo a b ×ˢ sourceBall y R)) := by
    convert c13_cylinder_translation_measurePreserving y R (Set.Ioo a b) using 1
    funext z
    rcases z with ⟨t, x⟩
    simp [T, A]
  have hm' : MeasurePreserving S
      (volume.restrict (Set.Ioo a b ×ˢ sourceBall y R))
      (volume.restrict (Set.Ioo a b ×ˢ sourceBall (0 : Vec d) R)) := by
    have h := MeasurePreserving.symm (Homeomorph.addRight A).toMeasurableEquiv hm
    convert h using 1
    funext z
    apply (Homeomorph.addRight A).injective
    simp [S, A, B, add_assoc]
  have hts : tsupport (ψ ∘ T) ⊆ Set.Ioo a b ×ˢ sourceBall (0 : Vec d) R := by
    intro z hz
    have hh := hsupp (tsupport_comp_subset_preimage ψ (continuous_id.add continuous_const) hz)
    exact ⟨by simpa [T, A] using hh.1, (c13_sourceBall_translate y z.2 R).1 (by simpa [T, A] using hh.2)⟩
  have hw : ∀ᵐ t ∂volume.restrict (Set.Ioo a b),
      HasWeakGradient (sourceBall 0 R) (fun x => ψ (T (t,x))) (fun x => H (T (t,x))) := by
    filter_upwards [hgrad] with t hh
    intro i
    have h := EinsteinFull.Blueprint.covariance_hasWeakPartialDerivative_translate (hh i) (-y)
    simpa [T, A, sourceBall, EinsteinRelation.External.AKM.ball] using h
  obtain ⟨v, hv, hv0, hv1⟩ := c17_spacetime_spatial_sobolev_test_density
    (ψ ∘ T) (H ∘ T) (hψ.comp_measurePreserving hm)
    (hHm.comp_measurePreserving hm) (hH.comp_measurePreserving hm) hw
    (hcompact.comp_homeomorph (Homeomorph.addRight A)) hts
  have hd (f : ℝ × Vec d → ℝ) (z : ℝ × Vec d) :
      fderiv ℝ (f ∘ S) z = fderiv ℝ f (S z) := by
    simpa [S, Function.comp_def] using fderiv_comp_add_right (𝕜 := ℝ) (f := f) B (x := z)
  refine ⟨fun n => v n ∘ S, ?_, ?_, ?_⟩
  · intro n
    refine ⟨(hv n).1.comp (contDiff_id.add contDiff_const),
      (hv n).2.1.comp_homeomorph (Homeomorph.addRight B), ?_⟩
    intro z hz
    have hh := (hv n).2.2 (tsupport_comp_subset_preimage (v n) (continuous_id.add continuous_const) hz)
    refine ⟨by simpa [S, B] using hh.1, ?_⟩
    have hx := (c13_sourceBall_translate y (z.2 + -y) R).2 (by simpa [S, B] using hh.2)
    simpa using hx
  · have he (n : ℕ) : (fun z => v n (S z) - ψ z) =
        (fun z => v n z - (ψ ∘ T) z) ∘ S := by
      funext z
      simp [hTS]
    have hmeas (n : ℕ) : AEStronglyMeasurable
        (fun z => v n z - (ψ ∘ T) z)
        (volume.restrict (Set.Ioo a b ×ˢ sourceBall (0 : Vec d) R)) :=
      (hv n).1.continuous.aestronglyMeasurable.sub (hψ.comp_measurePreserving hm).aestronglyMeasurable
    have hn (n : ℕ) : eLpNorm (fun z => (v n ∘ S) z - ψ z) 2
        (volume.restrict (Set.Ioo a b ×ˢ sourceBall y R)) =
        eLpNorm (fun z => v n z - (ψ ∘ T) z) 2
          (volume.restrict (Set.Ioo a b ×ˢ sourceBall (0 : Vec d) R)) := by
      change eLpNorm (fun z => v n (S z) - ψ z) 2 _ = _
      rw [he n, eLpNorm_comp_measurePreserving (hmeas n) hm']
    simpa only [hn] using hv0
  · have he (n : ℕ) : (fun z => euclideanNorm
        ((fun j => fderiv ℝ (v n ∘ S) z (0,unitVector j)) - H z)) =
        (fun z => euclideanNorm
          ((fun j => fderiv ℝ (v n) z (0,unitVector j)) - (H ∘ T) z)) ∘ S := by
      funext z
      simp only [Function.comp_apply, hd, hTS]
    have hmeas (n : ℕ) : AEStronglyMeasurable
        (fun z => euclideanNorm
          ((fun j => fderiv ℝ (v n) z (0,unitVector j)) - (H ∘ T) z))
        (volume.restrict (Set.Ioo a b ×ˢ sourceBall (0 : Vec d) R)) := by
      apply (Feller.continuous_euclideanNorm d).comp_aestronglyMeasurable
      apply AEStronglyMeasurable.sub
      · exact (continuous_pi fun j =>
          ((contDiff_infty_iff_fderiv.mp (hv n).1).2.clm_apply contDiff_const).continuous).aestronglyMeasurable
      · exact hHm.comp_measurePreserving hm
    have hn (n : ℕ) := eLpNorm_comp_measurePreserving (p := 2) (hmeas n) hm'
    have hn' (n : ℕ) := (he n).symm ▸ hn n
    simpa only [hn'] using hv1

end EinsteinFull.Calculus
