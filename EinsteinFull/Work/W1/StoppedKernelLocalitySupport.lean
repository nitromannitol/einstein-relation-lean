import EinsteinRelation.Diffusion.StoppedPathLocality
import EinsteinRelation.Diffusion.GMPFamily
import EinsteinRelation.Diffusion.PhysicalH1Representatives
import EinsteinRelation.Calculus.WeightedH1HilbertSupport
import EinsteinRelation.SpatialDirichlet.PhysicalFormBoundednessSupport
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.InnerProductSpace.LaxMilgram
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Exit stopping and local generators on the actual diffusion carriers

These ingredients concern the stopped-law locality used in Appendix A, Step 2.
The exit time and stopped continuous path are the literal blueprint objects.
Their measurability is proved without a locality or uniqueness premise. Agreement
of both physical fields on an open set implies agreement of the actual physical
and reduced generators there, for every signed force. Equality of the stopped
path laws still requires an analytic localization/uniqueness theorem. The
physical reversible measures and full weak-gradient forms are also compared
locally. The zero-boundary domain is constructed by closing the actual smooth
interior tests in the full weighted H¹ Hilbert graph, and its exterior support
properties give equality of the full forms on that domain. Positive-rate variational
resolvents are constructed there from physical L² data and compared under local
agreement of both physical fields. Their identification with killed GMP laws remains open.
-/

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace EinsteinFull

open EinsteinRelation EinsteinRelation.Diffusion

-- v4.35 port: `NormedSpace.exp` lemmas now ask for `NormedAlgebra ℚ 𝔸`; supply it from the real
-- normed algebra structure (low priority, file-local).
/-- Restrict a real normed algebra to rational scalars. -/
noncomputable local instance (priority := low) normedAlgebraRatOfRealAlgebra {A : Type*} [NormedRing A]
    [NormedAlgebra ℝ A] : NormedAlgebra ℚ A :=
  NormedAlgebra.restrictScalars ℚ ℝ A

/-- Before exit, the entire closed finite segment lies in the open domain. -/
theorem lt_localityExitTime_iff {d : ℕ} (U : Set (Vec d)) (hU : IsOpen U)
    (γ : Path d) (T : ℝ≥0) :
    (T : ℝ≥0∞) < localityExitTime U γ ↔ ∀ t : ℝ≥0, t ≤ T → γ t ∈ U := by
  constructor
  · intro h t ht
    by_contra hout
    have he : localityExitTime U γ ≤ (t : ℝ≥0∞) :=
      iInf_le_of_le t (iInf_le _ hout)
    exact (not_le_of_gt h) (he.trans (ENNReal.coe_le_coe.mpr ht))
  · exact lt_localityExitTime_of_stays U hU γ T

/-- Exit from an open set is a measurable extended time. No finiteness is assumed. -/
theorem measurable_localityExitTime {d : ℕ} (U : Set (Vec d)) (hU : IsOpen U) :
    Measurable (localityExitTime U) := by
  apply measurable_of_Ioi
  intro a
  by_cases ha : a = ⊤
  · simp only [ha, Set.Ioi_top, Set.preimage_empty]
    exact MeasurableSet.empty
  · have hopen := ContinuousMap.isOpen_setOf_mapsTo (X := ℝ≥0) (Y := Vec d)
      (K := Set.Icc (0 : ℝ≥0) a.toNNReal) isCompact_Icc hU
    have hset : localityExitTime U ⁻¹' Set.Ioi a =
        {γ : Path d | Set.MapsTo γ (Set.Icc 0 a.toNNReal) U} := by
      ext γ
      rw [Set.mem_preimage, Set.mem_Ioi, ← ENNReal.coe_toNNReal ha,
        lt_localityExitTime_iff U hU]
      simp only [Set.mem_setOf_eq, Set.MapsTo, Set.mem_Icc, zero_le, true_and, ENNReal.toNNReal_coe]
    rw [hset]
    exact hopen.measurableSet

/-- The raw stopped coordinate function in the GMP locality interface is measurable. -/
theorem measurable_rawLocalityStoppedPath {d : ℕ} (U : Set (Vec d)) (hU : IsOpen U) :
    Measurable (fun γ : Path d => fun t : ℝ≥0 =>
      γ ((min (t : ℝ≥0∞) (localityExitTime U γ)).toNNReal)) := by
  apply Measurable.of_eval
  intro t
  have htime : Measurable (fun γ : Path d =>
      (min (t : ℝ≥0∞) (localityExitTime U γ)).toNNReal) :=
    ENNReal.measurable_toNNReal.comp
      (measurable_const.min (measurable_localityExitTime U hU))
  have heval : Continuous (fun p : Path d × ℝ≥0 => p.1 p.2) :=
    continuous_fst.eval continuous_snd
  exact heval.measurable.comp (measurable_id.prodMk htime)

/-- The complete exit-stopped path is measurable in the continuous-path Borel space. -/
theorem measurable_localityStoppedPath {d : ℕ} (U : Set (Vec d)) (hU : IsOpen U) :
    Measurable (localityStoppedPath U) := by
  obtain ⟨D, hD, hdecode⟩ :=
    Probability.exists_measurable_continuousMap_decoder (X := ℝ≥0) (E := Vec d)
  have hraw : Measurable (fun γ : Path d => fun t => localityStoppedPath U γ t) := by
    simpa only [localityStoppedPath_apply] using measurable_rawLocalityStoppedPath U hU
  have hcomp : D ∘ (fun γ : Path d => fun t => localityStoppedPath U γ t) =
      localityStoppedPath U := funext fun γ => hdecode (localityStoppedPath U γ)
  rw [← hcomp]
  exact hD.comp hraw

/-- Every raw stopping map characterized by the GMP formula is measurable. -/
theorem measurable_stoppingMap_of_exit_formula {d : ℕ} (U : Set (Vec d))
    (hU : IsOpen U) (stop : Path d → ℝ≥0 → Vec d)
    (hstop : ∀ (γ : Path d) (t : ℝ≥0), stop γ t =
      γ ((min (t : ℝ≥0∞) (⨅ (s : ℝ≥0) (_ : γ s ∉ U), (s : ℝ≥0∞))).toNNReal)) :
    Measurable stop := by
  have heq : stop = fun γ t =>
      γ ((min (t : ℝ≥0∞) (localityExitTime U γ)).toNNReal) :=
    funext fun γ => funext fun t => hstop γ t
  rw [heq]
  exact measurable_rawLocalityStoppedPath U hU

/-- Stopping retains the displayed initial position, including immediate exit. -/
theorem localityStoppedPath_zero {d : ℕ} (U : Set (Vec d)) (γ : Path d) :
    localityStoppedPath U γ 0 = γ 0 := by
  rw [localityStoppedPath_apply]
  simp only [ENNReal.coe_zero, min_eq_left zero_le, ENNReal.toNNReal_zero]

/-- Pushing forward a probability law under exit stopping is a probability law. -/
theorem isProbabilityMeasure_map_localityStoppedPath {d : ℕ} (U : Set (Vec d))
    (P : Measure (Path d)) [IsProbabilityMeasure P] :
    IsProbabilityMeasure (P.map (localityStoppedPath U)) :=
  inferInstance

/-- The full stopped law retains an arbitrary deterministic starting point. -/
theorem map_localityStoppedPath_starts_at {d : ℕ} (U : Set (Vec d))
    (hU : IsOpen U) (P : Measure (Path d)) (x : Vec d)
    (hstart : ∀ᵐ γ ∂P, γ 0 = x) :
    ∀ᵐ γ ∂P.map (localityStoppedPath U), γ 0 = x := by
  have hm : MeasurableSet {γ : Path d | γ 0 = x} :=
    (measurableSet_singleton x).preimage (measurable_pathPosition 0)
  rw [ae_map_iff (measurable_localityStoppedPath U hU).aemeasurable hm]
  simpa only [localityStoppedPath_zero] using hstart

/-- Both components of the actual reduced pair agree wherever the physical pairs agree. -/
theorem reduce_eqOn_of_physical_eqOn {d : ℕ} (U : Set (Vec d)) (ω ω' : FieldPair d)
    (heq : ∀ y ∈ U, ω.1 y = ω'.1 y ∧ ω.2 y = ω'.2 y) :
    ∀ y ∈ U, (reduce ω).1 y = (reduce ω').1 y ∧
      (reduce ω).2 y = (reduce ω').2 y := by
  intro y hy
  obtain ⟨ha, hV⟩ := heq y hy
  change reducedCoefficient ω y = reducedCoefficient ω' y ∧ clockDensity ω y = clockDensity ω' y
  simp only [reducedCoefficient, clockDensity, ha, hV, and_self]

/-- The actual zero-potential pair used by the reduced GMP laws agrees on the same set. -/
theorem zeroPotentialReducedPair_eqOn_of_physical_eqOn {d : ℕ}
    (U : Set (Vec d)) (ω ω' : FieldPair d)
    (heq : ∀ y ∈ U, ω.1 y = ω'.1 y ∧ ω.2 y = ω'.2 y) :
    ∀ y ∈ U, (zeroPotentialReducedPair ω).1 y = (zeroPotentialReducedPair ω').1 y ∧
      (zeroPotentialReducedPair ω).2 y = (zeroPotentialReducedPair ω').2 y := by
  intro y hy
  exact ⟨(reduce_eqOn_of_physical_eqOn U ω ω' heq y hy).1, rfl⟩

private theorem local_flux_divergence_eq {d : ℕ} (U : Set (Vec d)) (hU : IsOpen U)
    (ω ω' : FieldPair d) (heq : ∀ y ∈ U, ω.1 y = ω'.1 y ∧ ω.2 y = ω'.2 y)
    (f : Vec d → ℝ) (x : Vec d) (hx : x ∈ U) :
    divergence (fun y => (reducedCoefficient ω y).mulVec (gradient f y)) x =
      divergence (fun y => (reducedCoefficient ω' y).mulVec (gradient f y)) x := by
  unfold divergence
  apply Finset.sum_congr rfl
  intro j _
  unfold coordinateDerivative
  have hlocal : (fun y => ((reducedCoefficient ω y).mulVec (gradient f y)) j) =ᶠ[𝓝 x]
      (fun y => ((reducedCoefficient ω' y).mulVec (gradient f y)) j) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    rw [show reducedCoefficient ω y = reducedCoefficient ω' y from
      (reduce_eqOn_of_physical_eqOn U ω ω' heq y hy).1]
  rw [hlocal.fderiv_eq]

/-- The physical local generators coincide for every test and every signed force. -/
theorem physicalGenerator_eqOn_of_physical_eqOn {d : ℕ} (U : Set (Vec d))
    (hU : IsOpen U) (ω ω' : FieldPair d)
    (heq : ∀ y ∈ U, ω.1 y = ω'.1 y ∧ ω.2 y = ω'.2 y)
    (i : Fin d) (lam : ℝ) (f : Vec d → ℝ) :
    Set.EqOn (physicalGenerator i ω lam f) (physicalGenerator i ω' lam f) U := by
  intro x hx
  obtain ⟨ha, hV⟩ := heq x hx
  simp only [physicalGenerator, ha, hV, local_flux_divergence_eq U hU ω ω' heq f x hx]

/-- The reduced local generators coincide for every test and every signed force. -/
theorem reducedGenerator_eqOn_of_physical_eqOn {d : ℕ} (U : Set (Vec d))
    (hU : IsOpen U) (ω ω' : FieldPair d)
    (heq : ∀ y ∈ U, ω.1 y = ω'.1 y ∧ ω.2 y = ω'.2 y)
    (i : Fin d) (lam : ℝ) (f : Vec d → ℝ) :
    Set.EqOn (reducedGenerator i ω lam f) (reducedGenerator i ω' lam f) U := by
  intro x hx
  have ha : reducedCoefficient ω x = reducedCoefficient ω' x :=
    (reduce_eqOn_of_physical_eqOn U ω ω' heq x hx).1
  simp only [reducedGenerator, ha, local_flux_divergence_eq U hU ω ω' heq f x hx]

private theorem compensatedTest_eq_of_eqOn_of_le_exit {d : ℕ}
    (U : Set (Vec d)) (hU : IsOpen U)
    (L L' : (Vec d → ℝ) → Vec d → ℝ) (f : Vec d → ℝ)
    (heq : Set.EqOn (L f) (L' f) U) (γ : Path d) (T : ℝ≥0)
    (hT : (T : ℝ≥0∞) ≤ localityExitTime U γ) :
    compensatedTest L f T γ = compensatedTest L' f T γ := by
  have hi : (∫ u in (0 : ℝ)..(T : ℝ), L f (γ u.toNNReal)) =
      ∫ u in (0 : ℝ)..(T : ℝ), L' f (γ u.toNNReal) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [volume.ae_ne (T : ℝ)] with u hu huI
    rw [Set.uIoc_of_le (show (0 : ℝ) ≤ (T : ℝ) from T.prop)] at huI
    have huT : u < (T : ℝ) := lt_of_le_of_ne huI.2 hu
    have huNN : u.toNNReal < T := by
      exact_mod_cast (show (u.toNNReal : ℝ) < (T : ℝ) by
        rw [Real.coe_toNNReal u huI.1.le]
        exact huT)
    have hbefore : (u.toNNReal : ℝ≥0∞) < localityExitTime U γ :=
      (ENNReal.coe_lt_coe.mpr huNN).trans_le hT
    exact heq ((lt_localityExitTime_iff U hU γ u.toNNReal).mp hbefore _ le_rfl)
  simp only [compensatedTest, hi]

/-- The physical compensated test agrees through exit, including a finite exit endpoint.
The endpoint contributes no Lebesgue time mass; no path-law equality is assumed. -/
theorem physicalCompensatedTest_eq_of_le_exit {d : ℕ} (U : Set (Vec d))
    (hU : IsOpen U) (ω ω' : FieldPair d)
    (heq : ∀ y ∈ U, ω.1 y = ω'.1 y ∧ ω.2 y = ω'.2 y)
    (i : Fin d) (lam : ℝ) (f : Vec d → ℝ) (γ : Path d) (T : ℝ≥0)
    (hT : (T : ℝ≥0∞) ≤ localityExitTime U γ) :
    compensatedTest (physicalGenerator i ω lam) f T γ =
      compensatedTest (physicalGenerator i ω' lam) f T γ :=
  compensatedTest_eq_of_eqOn_of_le_exit U hU _ _ f
    (physicalGenerator_eqOn_of_physical_eqOn U hU ω ω' heq i lam f) γ T hT

/-- The reduced compensated test agrees through exit, for the actual joint physical fields
and any signed force. Neither a solution law nor a uniqueness premise is used. -/
theorem reducedCompensatedTest_eq_of_le_exit {d : ℕ} (U : Set (Vec d))
    (hU : IsOpen U) (ω ω' : FieldPair d)
    (heq : ∀ y ∈ U, ω.1 y = ω'.1 y ∧ ω.2 y = ω'.2 y)
    (i : Fin d) (lam : ℝ) (f : Vec d → ℝ) (γ : Path d) (T : ℝ≥0)
    (hT : (T : ℝ≥0∞) ≤ localityExitTime U γ) :
    compensatedTest (reducedGenerator i ω lam) f T γ =
      compensatedTest (reducedGenerator i ω' lam) f T γ :=
  compensatedTest_eq_of_eqOn_of_le_exit U hU _ _ f
    (reducedGenerator_eqOn_of_physical_eqOn U hU ω ω' heq i lam f) γ T hT

/-- The literal reduced martingale-problem compensators stopped at `t ∧ τ_U`
coincide, for all paths and finite horizons, including infinite exit times. -/
theorem reducedCompensatedTest_eq_at_exit_stop {d : ℕ} (U : Set (Vec d))
    (hU : IsOpen U) (ω ω' : FieldPair d)
    (heq : ∀ y ∈ U, ω.1 y = ω'.1 y ∧ ω.2 y = ω'.2 y)
    (i : Fin d) (lam : ℝ) (f : Vec d → ℝ) (γ : Path d) (t : ℝ≥0) :
    compensatedTest (reducedGenerator i ω lam) f
        (min (t : ℝ≥0∞) (localityExitTime U γ)).toNNReal γ =
      compensatedTest (reducedGenerator i ω' lam) f
        (min (t : ℝ≥0∞) (localityExitTime U γ)).toNNReal γ := by
  apply reducedCompensatedTest_eq_of_le_exit U hU ω ω' heq i lam f γ
  rw [ENNReal.coe_toNNReal (ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_left _ _))]
  exact min_le_right _ _

open EinsteinRelation.External.GantertSection7Support
open EinsteinRelation.SpatialDirichlet

noncomputable section

/-- The actual reversible densities agree on the region of physical field agreement. -/
theorem physicalReversibleDensity_eqOn_of_physical_eqOn {d : ℕ}
    (U : Set (Vec d)) (ω ω' : FieldPair d)
    (heq : ∀ y ∈ U, ω.1 y = ω'.1 y ∧ ω.2 y = ω'.2 y)
    (hd : 2 ≤ d) (lam : ℝ) :
    Set.EqOn (physicalReversibleDensity ω hd lam)
      (physicalReversibleDensity ω' hd lam) U := by
  intro x hx
  simp only [physicalReversibleDensity, clockDensity, (heq x hx).2]

/-- The speed measures restricted to a measurable region agree, including their normalization.
This uses the actual potentials, with the common signed force left arbitrary. -/
theorem physicalReversibleMeasure_restrict_eq_of_physical_eqOn {d : ℕ}
    (U : Set (Vec d)) (hU : MeasurableSet U) (ω ω' : FieldPair d)
    (heq : ∀ y ∈ U, ω.1 y = ω'.1 y ∧ ω.2 y = ω'.2 y)
    (hd : 2 ≤ d) (lam : ℝ) :
    (physicalReversibleMeasure ω hd lam).restrict U =
      (physicalReversibleMeasure ω' hd lam).restrict U := by
  unfold physicalReversibleMeasure
  rw [restrict_withDensity hU, restrict_withDensity hU]
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem hU] with x hx
  rw [physicalReversibleDensity_eqOn_of_physical_eqOn U ω ω' heq hd lam hx]

/-- The full source Sobolev domain has a representative in the common force-weighted
weak-gradient graph, with equality tested under Lebesgue measure. -/
theorem physicalH1Member_iff_exists_graph_volume {d : ℕ}
    (ω : FieldPair d) (hd : 2 ≤ d) (lam : ℝ) (f : Vec d → ℝ) :
    physicalH1Member ω hd lam f ↔
      ∃ u : WeightedSobolevGraph (physicalForceMeasure hd lam), u.value =ᵐ[volume] f := by
  rw [physicalH1Member_iff_exists_graph]
  apply exists_congr
  intro u
  exact ae_withDensity_iff_volume_of_continuous_pos
    (physicalReversibleDensity ω hd lam) (physicalReversibleDensity_continuous ω hd lam)
    (physicalReversibleDensity_pos ω hd lam) _

/-- At fixed force, the full source weighted H¹ domain is independent of the environment.
No local coefficient equality or boundary-domain assumption is needed for this domain fact. -/
theorem physicalH1Member_environment_iff {d : ℕ}
    (ω ω' : FieldPair d) (hd : 2 ≤ d) (lam : ℝ) (f : Vec d → ℝ) :
    physicalH1Member ω hd lam f ↔ physicalH1Member ω' hd lam f := by
  rw [physicalH1Member_iff_exists_graph_volume, physicalH1Member_iff_exists_graph_volume]

/-- The literal local bilinear form agrees on every pair of full weak-gradient representatives.
The coefficient, potential, Euclidean pairing and factor `1/2` are unchanged. -/
theorem physicalWeightedForm_setIntegral_eq_of_physical_eqOn {d : ℕ}
    (U : Set (Vec d)) (hU : MeasurableSet U) (ω ω' : FieldPair d)
    (heq : ∀ y ∈ U, ω.1 y = ω'.1 y ∧ ω.2 y = ω'.2 y)
    (hd : 2 ≤ d) (lam : ℝ)
    (u v : WeightedSobolevGraph (physicalForceMeasure hd lam)) :
    (∫ x in U, weightedFormIntegrand ω.1 u v x ∂physicalReversibleMeasure ω hd lam) =
      ∫ x in U, weightedFormIntegrand ω'.1 u v x
        ∂physicalReversibleMeasure ω' hd lam := by
  rw [physicalReversibleMeasure_restrict_eq_of_physical_eqOn U hU ω ω' heq hd lam]
  apply setIntegral_congr_fun hU
  intro x hx
  simp only [weightedFormIntegrand, (heq x hx).1]

/-- In particular, the local form of the zero-potential GMP reduced environment agrees.
The graph and reversible measure here are those for `(a,0)`, not for `(a,μ)`. -/
theorem zeroPotentialReducedForm_setIntegral_eq_of_physical_eqOn {d : ℕ}
    (U : Set (Vec d)) (hU : MeasurableSet U) (ω ω' : FieldPair d)
    (heq : ∀ y ∈ U, ω.1 y = ω'.1 y ∧ ω.2 y = ω'.2 y)
    (hd : 2 ≤ d) (lam : ℝ)
    (u v : WeightedSobolevGraph (physicalForceMeasure hd lam)) :
    (∫ x in U, weightedFormIntegrand (zeroPotentialReducedPair ω).1 u v x
      ∂physicalReversibleMeasure (zeroPotentialReducedPair ω) hd lam) =
      ∫ x in U, weightedFormIntegrand (zeroPotentialReducedPair ω').1 u v x
        ∂physicalReversibleMeasure (zeroPotentialReducedPair ω') hd lam :=
  physicalWeightedForm_setIntegral_eq_of_physical_eqOn U hU _ _
    (zeroPotentialReducedPair_eqOn_of_physical_eqOn U ω ω' heq) hd lam u v

private theorem physicalH1FormEnergy_eq_setIntegral_of_gradient_zero_off {d : ℕ}
    (U : Set (Vec d)) (ω : FieldPair d) (hd : 2 ≤ d) (lam : ℝ)
    (u : WeightedSobolevGraph (physicalForceMeasure hd lam))
    (hu : ∀ᵐ x ∂(volume : Measure (Vec d)), x ∉ U → u.weakGradient x = 0) :
    physicalH1FormEnergy ω hd lam u =
      ∫ x in U, weightedFormIntegrand ω.1 u u x ∂physicalReversibleMeasure ω hd lam := by
  symm
  apply setIntegral_eq_integral_of_ae_compl_eq_zero
  have hu' : ∀ᵐ x ∂physicalReversibleMeasure ω hd lam,
      x ∉ U → u.weakGradient x = 0 :=
    (withDensity_absolutelyContinuous _ _).ae_le hu
  filter_upwards [hu'] with x hx hxU
  simp [weightedFormIntegrand, hx hxU, dot]

/-- Full energies agree for a weak-gradient representative whose gradient is zero off the
region of agreement. This does not identify that support condition with an H¹₀ domain. -/
theorem physicalH1FormEnergy_eq_of_gradient_zero_off {d : ℕ}
    (U : Set (Vec d)) (hU : MeasurableSet U) (ω ω' : FieldPair d)
    (heq : ∀ y ∈ U, ω.1 y = ω'.1 y ∧ ω.2 y = ω'.2 y)
    (hd : 2 ≤ d) (lam : ℝ)
    (u : WeightedSobolevGraph (physicalForceMeasure hd lam))
    (hu : ∀ᵐ x ∂(volume : Measure (Vec d)), x ∉ U → u.weakGradient x = 0) :
    physicalH1FormEnergy ω hd lam u = physicalH1FormEnergy ω' hd lam u := by
  rw [physicalH1FormEnergy_eq_setIntegral_of_gradient_zero_off U ω hd lam u hu,
    physicalH1FormEnergy_eq_setIntegral_of_gradient_zero_off U ω' hd lam u hu]
  exact physicalWeightedForm_setIntegral_eq_of_physical_eqOn U hU ω ω' heq hd lam u u

/-- Vanishing off a region is preserved by convergence of the actual weighted L² gradients.
This supplies the support step for completing compactly supported graph approximations;
it does not assume an identification of a killed law or of a boundary Sobolev domain. -/
theorem weakGradient_zero_off_of_tendsto {d : ℕ} (U : Set (Vec d))
    (hd : 2 ≤ d) (lam : ℝ)
    (u : ℕ → WeightedSobolevGraph (physicalForceMeasure hd lam))
    (v : WeightedSobolevGraph (physicalForceMeasure hd lam))
    (hu : ∀ n, ∀ᵐ x ∂(volume : Measure (Vec d)), x ∉ U → (u n).weakGradient x = 0)
    (hlim : Tendsto (fun n => (u n).gradient_memLp.toLp (u n).weakGradient) atTop
      (𝓝 (v.gradient_memLp.toLp v.weakGradient))) :
    ∀ᵐ x ∂(volume : Measure (Vec d)), x ∉ U → v.weakGradient x = 0 := by
  have hzero : ∀ᵐ x ∂physicalForceMeasure hd lam,
      ∀ n, x ∉ U → (u n).weakGradient x = 0 := by
    apply ae_all_iff.mpr
    intro n
    exact (ae_withDensity_iff_volume_of_continuous_pos
      (physicalForceWeight hd lam) (physicalForceWeight_continuous hd lam)
      (physicalForceWeight_pos hd lam) _).mpr (hu n)
  have hrep : ∀ᵐ x ∂physicalForceMeasure hd lam,
      ∀ n, (u n).gradient_memLp.toLp (u n).weakGradient x = (u n).weakGradient x :=
    ae_all_iff.mpr (fun n => (u n).gradient_memLp.coeFn_toLp)
  obtain ⟨ns, _, hns⟩ := (tendstoInMeasure_of_tendsto_Lp hlim).exists_seq_tendsto_ae
  apply (ae_withDensity_iff_volume_of_continuous_pos
    (physicalForceWeight hd lam) (physicalForceWeight_continuous hd lam)
    (physicalForceWeight_pos hd lam) _).mp
  filter_upwards [hzero, hrep, hns, v.gradient_memLp.coeFn_toLp] with x hx hr ht hv hxU
  have ht0 : Tendsto
      (fun n => (u (ns n)).gradient_memLp.toLp (u (ns n)).weakGradient x)
      atTop (𝓝 (0 : EuclideanSpace ℝ (Fin d))) := by
    have heq : (fun n => (u (ns n)).gradient_memLp.toLp (u (ns n)).weakGradient x) =
        fun _ : ℕ => (0 : EuclideanSpace ℝ (Fin d)) := by
      funext n
      rw [hr (ns n), hx (ns n) hxU]
    rw [heq]
    exact tendsto_const_nhds
  rw [← hv]
  exact tendsto_nhds_unique ht ht0


open EinsteinRelation.SpatialDirichlet

/-- The actual force-weighted H¹ graph with its L² value/Euclidean-gradient Hilbert norm. -/
abbrev PhysicalH1Space {d : ℕ} (hd : 2 ≤ d) (lam : ℝ) :=
  densityWeightedH1Submodule (physicalForceWeight hd lam)
    (physicalForceWeight_continuous hd lam) (physicalForceWeight_pos hd lam)

-- Keep the inherited structures shared throughout the concrete graph API.
@[reducible] private noncomputable instance physicalH1NormedAddCommGroup {d : ℕ}
    (hd : 2 ≤ d) (lam : ℝ) : NormedAddCommGroup (PhysicalH1Space hd lam) :=
  Submodule.normedAddCommGroup _

@[reducible] private noncomputable instance physicalH1InnerProductSpace {d : ℕ}
    (hd : 2 ≤ d) (lam : ℝ) : InnerProductSpace ℝ (PhysicalH1Space hd lam) :=
  Submodule.innerProductSpace _

-- The next construction adapts the private smooth-graph argument in the pinned
-- `SpatialDirichlet.PhysicalH1DensitySupport`; it uses integration by parts, not a new input.
private theorem locallyFinite_finiteOnCompacts {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] {m : Measure X} [IsLocallyFiniteMeasure m] :
    IsFiniteMeasureOnCompacts m := by
  refine ⟨?_⟩
  intro K hK
  let U : K → Set X := fun x => Classical.choose (m.exists_isOpen_measure_lt_top x.1)
  have hU : ∀ x : K, (x : X) ∈ U x ∧ IsOpen (U x) ∧ m (U x) < ∞ :=
    fun x => Classical.choose_spec (m.exists_isOpen_measure_lt_top x.1)
  have hcover : K ⊆ ⋃ x : K, U x := fun x hx =>
    Set.mem_iUnion.2 ⟨⟨x, hx⟩, (hU ⟨x, hx⟩).1⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover U (fun x => (hU x).2.1) hcover
  calc
    m K ≤ m (⋃ x ∈ t, U x) := measure_mono ht
    _ ≤ ∑ x ∈ t, m (U x) := measure_biUnion_finset_le t U
    _ < ∞ := ENNReal.sum_lt_top.mpr (fun x _ => (hU x).2.2)

private def euclideanSmoothGradient {d : ℕ} (φ : Vec d → ℝ) (x : Vec d) :
    EuclideanSpace ℝ (Fin d) :=
  (EuclideanSpace.equiv (Fin d) ℝ).symm (gradient φ x)

private theorem continuous_euclideanSmoothGradient {d : ℕ} {φ : Vec d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) : Continuous (euclideanSmoothGradient φ) := by
  apply (EuclideanSpace.equiv (Fin d) ℝ).symm.continuous.comp
  apply continuous_pi
  intro i
  change Continuous (fun x => fderiv ℝ φ x (unitVector i))
  exact (hφ.continuous_fderiv_apply (by simp)).comp
    (continuous_id.prodMk continuous_const)

private theorem hasCompactSupport_euclideanSmoothGradient {d : ℕ} {φ : Vec d → ℝ}
    (hφ : HasCompactSupport φ) : HasCompactSupport (euclideanSmoothGradient φ) := by
  apply (HasCompactSupport.fderiv (𝕜 := ℝ) hφ).mono'
  intro x hx
  by_contra hnot
  have hzero : fderiv ℝ φ x = 0 := image_eq_zero_of_notMem_tsupport hnot
  have hcoord : gradient φ x = 0 := by
    funext i
    simp [gradient, coordinateDerivative, hzero]
  exact hx (by simp [euclideanSmoothGradient, hcoord])

private theorem continuous_coordinateDerivative {d : ℕ} {φ : Vec d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (i : Fin d) :
    Continuous (fun x => coordinateDerivative i φ x) := by
  change Continuous (fun x => fderiv ℝ φ x (unitVector i))
  exact (hφ.continuous_fderiv_apply (by simp)).comp
    (continuous_id.prodMk continuous_const)

private noncomputable def smoothPhysicalSobolevGraph {d : ℕ} (hd : 2 ≤ d) (lam : ℝ)
    (φ : Vec d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ) :
    WeightedSobolevGraph (physicalForceMeasure hd lam) := by
  let ρ := physicalForceWeight hd lam
  letI : IsLocallyFiniteMeasure (densityWeightedMeasure ρ) :=
    densityWeightedMeasure_locallyFinite ρ (physicalForceWeight_continuous hd lam)
  letI : IsFiniteMeasureOnCompacts (densityWeightedMeasure ρ) := locallyFinite_finiteOnCompacts
  have hφMem : MemLp φ 2 (densityWeightedMeasure ρ) :=
    hφ.continuous.memLp_of_hasCompactSupport hφc
  have hgradMem : MemLp (euclideanSmoothGradient φ) 2 (densityWeightedMeasure ρ) :=
    (continuous_euclideanSmoothGradient hφ).memLp_of_hasCompactSupport
      (hasCompactSupport_euclideanSmoothGradient hφc)
  have hidentity : ∀ i : Fin d, ∀ ψ : Vec d → ℝ,
      IsSpatialTest Set.univ ψ →
      (∫ x in Set.univ, φ x * coordinateDerivative i ψ x) =
        -(∫ x in Set.univ, (WithLp.ofLp (euclideanSmoothGradient φ x)) i * ψ x) := by
    intro i ψ hψ
    have hfirst : Integrable (fun x => coordinateDerivative i φ x * ψ x) :=
      ((continuous_coordinateDerivative hφ i).mul hψ.1.continuous).integrable_of_hasCompactSupport
        hψ.2.1.mul_left
    have hsecond : Integrable (fun x => φ x * coordinateDerivative i ψ x) :=
      (hφ.continuous.mul (continuous_coordinateDerivative hψ.1 i)).integrable_of_hasCompactSupport
        hφc.mul_right
    have hproduct : Integrable (fun x => φ x * ψ x) :=
      (hφ.continuous.mul hψ.1.continuous).integrable_of_hasCompactSupport hφc.mul_right
    have hparts := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      (μ := volume) hfirst hsecond hproduct
      (fun x _ => (hφ.differentiable (by simp)) x)
      (fun x _ => (hψ.1.differentiable (by simp)) x)
    simpa [setIntegral_univ, euclideanSmoothGradient, gradient, coordinateDerivative] using hparts
  exact weightedSobolevGraph_mk_of_density_distributionalData ρ
    (physicalForceWeight_continuous hd lam) (physicalForceWeight_pos hd lam)
    φ (euclideanSmoothGradient φ) hφMem hgradMem hidentity

/-- Embed every smooth compactly supported scalar test into the actual weighted H¹ graph. -/
noncomputable def physicalH1SmoothTest {d : ℕ} (hd : 2 ≤ d) (lam : ℝ)
    (φ : Vec d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ) :
    PhysicalH1Space hd lam := by
  let g := smoothPhysicalSobolevGraph hd lam φ hφ hφc
  refine ⟨(WithLp.prodContinuousLinearEquiv 2 ℝ _ _).symm
    (densityWeightedGraphPair (physicalForceWeight hd lam) g), ?_⟩
  exact densityWeightedGraphPair_mem_weakGraphSet _
    (physicalForceWeight_continuous hd lam) (physicalForceWeight_pos hd lam) g

/-- The test embedding preserves the scalar function under the actual force measure. -/
theorem physicalH1SmoothTest_value {d : ℕ} (hd : 2 ≤ d) (lam : ℝ)
    (φ : Vec d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ) :
    densityWeightedH1SpaceValue (physicalH1SmoothTest hd lam φ hφ hφc)
      =ᵐ[physicalForceMeasure hd lam] φ := by
  exact (smoothPhysicalSobolevGraph hd lam φ hφ hφc).value_memLp.coeFn_toLp

/-- The test embedding preserves the classical Euclidean gradient. -/
theorem physicalH1SmoothTest_gradient {d : ℕ} (hd : 2 ≤ d) (lam : ℝ)
    (φ : Vec d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ) :
    densityWeightedH1SpaceGradient (physicalH1SmoothTest hd lam φ hφ hφc)
      =ᵐ[physicalForceMeasure hd lam]
        fun x => (EuclideanSpace.equiv (Fin d) ℝ).symm (gradient φ x) := by
  exact (smoothPhysicalSobolevGraph hd lam φ hφ hφc).gradient_memLp.coeFn_toLp

/-- The linear core generated by the literal smooth tests compactly supported inside `U`. -/
noncomputable def physicalH1SmoothCore {d : ℕ} (U : Set (Vec d)) (hd : 2 ≤ d) (lam : ℝ) :
    Submodule ℝ (PhysicalH1Space hd lam) :=
  Submodule.span ℝ {u | ∃ (φ : Vec d → ℝ) (hφ : IsSpatialTest U φ),
    u = physicalH1SmoothTest hd lam φ hφ.1 hφ.2.1}

/-- The zero-boundary domain is the closure of the smooth interior core in the full
force-weighted H¹ graph norm. No identification with a killed process is assumed. -/
noncomputable def physicalH1ZeroBoundary {d : ℕ} (U : Set (Vec d)) (hd : 2 ≤ d) (lam : ℝ) :
    Submodule ℝ (PhysicalH1Space hd lam) :=
  (physicalH1SmoothCore U hd lam).topologicalClosure

@[reducible] private noncomputable instance zeroBoundaryNormedAddCommGroup {d : ℕ}
    (U : Set (Vec d)) (hd : 2 ≤ d) (lam : ℝ) :
    NormedAddCommGroup (physicalH1ZeroBoundary U hd lam) := Submodule.normedAddCommGroup _

@[reducible] private noncomputable instance zeroBoundaryInnerProductSpace {d : ℕ}
    (U : Set (Vec d)) (hd : 2 ≤ d) (lam : ℝ) :
    InnerProductSpace ℝ (physicalH1ZeroBoundary U hd lam) := Submodule.innerProductSpace _

/-- The zero-boundary domain is a closed subspace of the actual full H¹ graph. -/
theorem physicalH1ZeroBoundary_isClosed {d : ℕ} (U : Set (Vec d)) (hd : 2 ≤ d) (lam : ℝ) :
    IsClosed (physicalH1ZeroBoundary U hd lam : Set (PhysicalH1Space hd lam)) :=
  Submodule.isClosed_topologicalClosure _

noncomputable instance physicalH1ZeroBoundary_completeSpace {d : ℕ}
    (U : Set (Vec d)) (hd : 2 ≤ d) (lam : ℝ) :
    CompleteSpace (physicalH1ZeroBoundary U hd lam) :=
  (physicalH1ZeroBoundary_isClosed U hd lam).completeSpace_coe

/-- Every spatial test in the region belongs to its completed zero-boundary domain. -/
theorem physicalH1SmoothTest_mem_zeroBoundary {d : ℕ} (U : Set (Vec d)) (hd : 2 ≤ d)
    (lam : ℝ) (φ : Vec d → ℝ) (hφ : IsSpatialTest U φ) :
    physicalH1SmoothTest hd lam φ hφ.1 hφ.2.1 ∈ physicalH1ZeroBoundary U hd lam :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨φ, hφ, rfl⟩)

/-- Enlarging the region enlarges the zero-boundary graph domain. -/
theorem physicalH1ZeroBoundary_mono {d : ℕ} {U V : Set (Vec d)}
    (hUV : U ⊆ V) (hd : 2 ≤ d) (lam : ℝ) :
    physicalH1ZeroBoundary U hd lam ≤ physicalH1ZeroBoundary V hd lam := by
  apply Submodule.topologicalClosure_mono
  apply Submodule.span_mono
  rintro u ⟨φ, hφ, rfl⟩
  exact ⟨φ, ⟨hφ.1, hφ.2.1, hφ.2.2.trans hUV⟩, rfl⟩


private def lpZeroOffSubmodule {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (U : Set X) (m : Measure X) :
    Submodule ℝ (Lp E 2 m) where
  carrier := {f | ∀ᵐ x ∂m, x ∉ U → f x = 0}
  zero_mem' := by
    filter_upwards [Lp.coeFn_zero E 2 m] with x hx _
    exact hx
  add_mem' := by
    intro f g hf hg
    filter_upwards [hf, hg, Lp.coeFn_add f g] with x hx hy hrep hxU
    exact hrep.trans (by simp only [Pi.add_apply, hx hxU, hy hxU, add_zero])
  smul_mem' := by
    intro c f hf
    filter_upwards [hf, Lp.coeFn_smul c f] with x hx hrep hxU
    simp [hrep, hx hxU]

private theorem lpZeroOffSubmodule_isClosed {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (U : Set X) (m : Measure X) :
    IsClosed (lpZeroOffSubmodule (E := E) U m : Set (Lp E 2 m)) := by
  apply isClosed_of_closure_subset
  intro f hf
  obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.mp hf
  have hzero : ∀ᵐ x ∂m, ∀ n, x ∉ U → u n x = 0 := ae_all_iff.mpr hu
  obtain ⟨ns, _, hns⟩ := (tendstoInMeasure_of_tendsto_Lp hlim).exists_seq_tendsto_ae
  filter_upwards [hzero, hns] with x hx ht hxU
  have ht0 : Tendsto (fun n => u (ns n) x) atTop (𝓝 (0 : E)) := by
    have heq : (fun n => u (ns n) x) = fun _ : ℕ => (0 : E) :=
      funext (fun n => hx (ns n) hxU)
    rw [heq]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique ht ht0

private def physicalH1ValueMap {d : ℕ} (hd : 2 ≤ d) (lam : ℝ) :
    PhysicalH1Space hd lam →L[ℝ] Lp ℝ 2 (physicalForceMeasure hd lam) :=
  (ContinuousLinearMap.fst ℝ _ _).comp
    ((WithLp.prodContinuousLinearEquiv 2 ℝ _ _).toContinuousLinearMap.comp
      (densityWeightedH1Submodule (physicalForceWeight hd lam)
        (physicalForceWeight_continuous hd lam) (physicalForceWeight_pos hd lam)).subtypeL)

private def physicalH1GradientMap {d : ℕ} (hd : 2 ≤ d) (lam : ℝ) :
    PhysicalH1Space hd lam →L[ℝ]
      Lp (EuclideanSpace ℝ (Fin d)) 2 (physicalForceMeasure hd lam) :=
  (ContinuousLinearMap.snd ℝ _ _).comp
    ((WithLp.prodContinuousLinearEquiv 2 ℝ _ _).toContinuousLinearMap.comp
      (densityWeightedH1Submodule (physicalForceWeight hd lam)
        (physicalForceWeight_continuous hd lam) (physicalForceWeight_pos hd lam)).subtypeL)

private theorem physicalH1ZeroBoundary_le_supported {d : ℕ}
    (U : Set (Vec d)) (hd : 2 ≤ d) (lam : ℝ) :
    physicalH1ZeroBoundary U hd lam ≤
      (lpZeroOffSubmodule U (physicalForceMeasure hd lam)).comap
        (physicalH1ValueMap hd lam).toLinearMap ⊓
      (lpZeroOffSubmodule U (physicalForceMeasure hd lam)).comap
        (physicalH1GradientMap hd lam).toLinearMap := by
  apply Submodule.topologicalClosure_minimal
  · apply Submodule.span_le.mpr
    rintro u ⟨φ, hφ, rfl⟩
    constructor
    · change ∀ᵐ x ∂physicalForceMeasure hd lam, x ∉ U →
        densityWeightedH1SpaceValue (physicalH1SmoothTest hd lam φ hφ.1 hφ.2.1) x = 0
      filter_upwards [physicalH1SmoothTest_value hd lam φ hφ.1 hφ.2.1] with x hx hxU
      rw [hx]
      exact image_eq_zero_of_notMem_tsupport (fun ht => hxU (hφ.2.2 ht))
    · change ∀ᵐ x ∂physicalForceMeasure hd lam, x ∉ U →
        densityWeightedH1SpaceGradient (physicalH1SmoothTest hd lam φ hφ.1 hφ.2.1) x = 0
      filter_upwards [physicalH1SmoothTest_gradient hd lam φ hφ.1 hφ.2.1] with x hx hxU
      have hzero : gradient φ x = 0 := by
        funext i
        simp only [gradient, coordinateDerivative,
          fderiv_of_notMem_tsupport ℝ (fun ht => hxU (hφ.2.2 ht))]
        simp
      simp [hx, hzero]
  · exact ((lpZeroOffSubmodule_isClosed U (physicalForceMeasure hd lam)).preimage
      (physicalH1ValueMap hd lam).continuous).inter
        ((lpZeroOffSubmodule_isClosed U (physicalForceMeasure hd lam)).preimage
          (physicalH1GradientMap hd lam).continuous)

/-- The scalar representative of a zero-boundary graph vanishes Lebesgue-a.e. off `U`. -/
theorem physicalH1ZeroBoundary_value_zero_off {d : ℕ} (U : Set (Vec d)) (hd : 2 ≤ d)
    (lam : ℝ) (u : PhysicalH1Space hd lam) (hu : u ∈ physicalH1ZeroBoundary U hd lam) :
    ∀ᵐ x ∂(volume : Measure (Vec d)), x ∉ U → densityWeightedH1SpaceValue u x = 0 := by
  apply (ae_withDensity_iff_volume_of_continuous_pos
    (physicalForceWeight hd lam) (physicalForceWeight_continuous hd lam)
    (physicalForceWeight_pos hd lam) _).mp
  exact (physicalH1ZeroBoundary_le_supported U hd lam hu).1

/-- The Euclidean weak gradient of a zero-boundary graph vanishes Lebesgue-a.e. off `U`. -/
theorem physicalH1ZeroBoundary_gradient_zero_off {d : ℕ} (U : Set (Vec d)) (hd : 2 ≤ d)
    (lam : ℝ) (u : PhysicalH1Space hd lam) (hu : u ∈ physicalH1ZeroBoundary U hd lam) :
    ∀ᵐ x ∂(volume : Measure (Vec d)), x ∉ U → densityWeightedH1SpaceGradient u x = 0 := by
  apply (ae_withDensity_iff_volume_of_continuous_pos
    (physicalForceWeight hd lam) (physicalForceWeight_continuous hd lam)
    (physicalForceWeight_pos hd lam) _).mp
  exact (physicalH1ZeroBoundary_le_supported U hd lam hu).2

/-- Reconstruct the actual distributional weak-gradient representative of a Hilbert graph. -/
def physicalH1SpaceRepresentative {d : ℕ} (hd : 2 ≤ d) (lam : ℝ)
    (u : PhysicalH1Space hd lam) : WeightedSobolevGraph (physicalForceMeasure hd lam) :=
  densityWeightedH1SpaceRepresentative (physicalForceWeight hd lam)
    (physicalForceWeight_continuous hd lam) (physicalForceWeight_pos hd lam) u

/-- Reconstruction preserves both of the weighted L² coordinates. -/
theorem physicalH1SpaceRepresentative_pair {d : ℕ} (hd : 2 ≤ d) (lam : ℝ)
    (u : PhysicalH1Space hd lam) :
    densityWeightedGraphPair (physicalForceWeight hd lam) (physicalH1SpaceRepresentative hd lam u) =
      (densityWeightedH1SpaceValue u, densityWeightedH1SpaceGradient u) :=
  densityWeightedH1SpaceRepresentative_pair u

/-- The full bilinear form agrees when its first graph belongs to the completed interior
core; the second graph may be any member of the full force-weighted H¹ domain. -/
theorem physicalWeightedForm_eq_on_zeroBoundary {d : ℕ}
    (U : Set (Vec d)) (hU : MeasurableSet U) (ω ω' : FieldPair d)
    (heq : ∀ y ∈ U, ω.1 y = ω'.1 y ∧ ω.2 y = ω'.2 y)
    (hd : 2 ≤ d) (lam : ℝ) (u v : PhysicalH1Space hd lam)
    (hu : u ∈ physicalH1ZeroBoundary U hd lam) :
    (∫ x, weightedFormIntegrand ω.1 (physicalH1SpaceRepresentative hd lam u)
      (physicalH1SpaceRepresentative hd lam v) x ∂physicalReversibleMeasure ω hd lam) =
      ∫ x, weightedFormIntegrand ω'.1 (physicalH1SpaceRepresentative hd lam u)
        (physicalH1SpaceRepresentative hd lam v) x ∂physicalReversibleMeasure ω' hd lam := by
  have hzero := physicalH1ZeroBoundary_gradient_zero_off U hd lam u hu
  have hlocal (η : FieldPair d) :
      (∫ x, weightedFormIntegrand η.1 (physicalH1SpaceRepresentative hd lam u)
        (physicalH1SpaceRepresentative hd lam v) x ∂physicalReversibleMeasure η hd lam) =
      ∫ x in U, weightedFormIntegrand η.1 (physicalH1SpaceRepresentative hd lam u)
        (physicalH1SpaceRepresentative hd lam v) x ∂physicalReversibleMeasure η hd lam := by
    symm
    apply setIntegral_eq_integral_of_ae_compl_eq_zero
    have hzero' : ∀ᵐ x ∂physicalReversibleMeasure η hd lam,
        x ∉ U → densityWeightedH1SpaceGradient u x = 0 :=
      (withDensity_absolutelyContinuous _ _).ae_le hzero
    filter_upwards [hzero'] with x hx hxU
    have hx' : (physicalH1SpaceRepresentative hd lam u).weakGradient x = 0 := hx hxU
    simp [weightedFormIntegrand, hx', dot]
  rw [hlocal ω, hlocal ω']
  exact physicalWeightedForm_setIntegral_eq_of_physical_eqOn U hU ω ω' heq hd lam _ _

/-- Agreement of the actual physical fields on the region gives equality of full energies
on its completed smooth-interior domain. The exterior support condition is proved from closure. -/
theorem physicalH1FormEnergy_eq_on_zeroBoundary {d : ℕ}
    (U : Set (Vec d)) (hU : MeasurableSet U) (ω ω' : FieldPair d)
    (heq : ∀ y ∈ U, ω.1 y = ω'.1 y ∧ ω.2 y = ω'.2 y)
    (hd : 2 ≤ d) (lam : ℝ) (u : PhysicalH1Space hd lam)
    (hu : u ∈ physicalH1ZeroBoundary U hd lam) :
    physicalH1FormEnergy ω hd lam (physicalH1SpaceRepresentative hd lam u) =
      physicalH1FormEnergy ω' hd lam (physicalH1SpaceRepresentative hd lam u) := by
  apply physicalH1FormEnergy_eq_of_gradient_zero_off U hU ω ω' heq hd lam
  exact physicalH1ZeroBoundary_gradient_zero_off U hd lam u hu

-- The next private constructions adapt the proved bilinear/value-map implementation in
-- the pinned `SpatialDirichlet.PhysicalResolventExistenceSupport`. Its public theorem tests
-- against the full graph; here the same actual form is restricted to the closed interior domain.
open scoped InnerProductSpace

private theorem sourceDot_add_left {d : ℕ} (u v w : Vec d) :
    dot (u + v) w = dot u w + dot v w := by
  simp only [dot, Pi.add_apply, add_mul, Finset.sum_add_distrib]

private theorem sourceDot_add_right {d : ℕ} (u v w : Vec d) :
    dot u (v + w) = dot u v + dot u w := by
  simp only [dot, Pi.add_apply, mul_add, Finset.sum_add_distrib]

private theorem sourceDot_smul_left {d : ℕ} (c : ℝ) (u v : Vec d) :
    dot (c • u) v = c * dot u v := by
  simp only [dot, Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]

private theorem sourceDot_smul_right {d : ℕ} (c : ℝ) (u v : Vec d) :
    dot u (c • v) = c * dot u v := by
  simp only [dot, Pi.smul_apply, smul_eq_mul]
  calc
    (∑ i, u i * (c * v i)) = ∑ i, c * (u i * v i) :=
      Finset.sum_congr rfl (fun i _ => by ring)
    _ = c * ∑ i, u i * v i := by rw [Finset.mul_sum]

private theorem densityWeightedH1SpaceGradient_add {d : ℕ} {ρ : Vec d → ℝ}
    {hρ : Continuous ρ} {hρpos : ∀ x, 0 < ρ x}
    (u v : densityWeightedH1Submodule ρ hρ hρpos) :
    densityWeightedH1SpaceGradient (u + v) =
      densityWeightedH1SpaceGradient u + densityWeightedH1SpaceGradient v := by
  let E := WithLp.prodContinuousLinearEquiv 2 ℝ
    (Lp ℝ 2 (densityWeightedMeasure ρ))
    (Lp (EuclideanSpace ℝ (Fin d)) 2 (densityWeightedMeasure ρ))
  change (E (u.1 + v.1)).2 = (E u.1).2 + (E v.1).2
  exact congrArg Prod.snd (E.map_add u.1 v.1)

private theorem densityWeightedH1SpaceGradient_smul {d : ℕ} {ρ : Vec d → ℝ}
    {hρ : Continuous ρ} {hρpos : ∀ x, 0 < ρ x}
    (c : ℝ) (u : densityWeightedH1Submodule ρ hρ hρpos) :
    densityWeightedH1SpaceGradient (c • u) = c • densityWeightedH1SpaceGradient u := by
  let E := WithLp.prodContinuousLinearEquiv 2 ℝ
    (Lp ℝ 2 (densityWeightedMeasure ρ))
    (Lp (EuclideanSpace ℝ (Fin d)) 2 (densityWeightedMeasure ρ))
  change (E (c • u.1)).2 = c • (E u.1).2
  exact congrArg Prod.snd (E.map_smul c u.1)

private theorem densityWeightedH1SpaceValue_add {d : ℕ} {ρ : Vec d → ℝ}
    {hρ : Continuous ρ} {hρpos : ∀ x, 0 < ρ x}
    (u v : densityWeightedH1Submodule ρ hρ hρpos) :
    densityWeightedH1SpaceValue (u + v) =
      densityWeightedH1SpaceValue u + densityWeightedH1SpaceValue v := by
  let E := WithLp.prodContinuousLinearEquiv 2 ℝ
    (Lp ℝ 2 (densityWeightedMeasure ρ))
    (Lp (EuclideanSpace ℝ (Fin d)) 2 (densityWeightedMeasure ρ))
  change (E (u.1 + v.1)).1 = (E u.1).1 + (E v.1).1
  exact congrArg Prod.fst (E.map_add u.1 v.1)

private theorem densityWeightedH1SpaceValue_smul {d : ℕ} {ρ : Vec d → ℝ}
    {hρ : Continuous ρ} {hρpos : ∀ x, 0 < ρ x}
    (c : ℝ) (u : densityWeightedH1Submodule ρ hρ hρpos) :
    densityWeightedH1SpaceValue (c • u) = c • densityWeightedH1SpaceValue u := by
  let E := WithLp.prodContinuousLinearEquiv 2 ℝ
    (Lp ℝ 2 (densityWeightedMeasure ρ))
    (Lp (EuclideanSpace ℝ (Fin d)) 2 (densityWeightedMeasure ρ))
  change (E (c • u.1)).1 = c • (E u.1).1
  exact congrArg Prod.fst (E.map_smul c u.1)

private theorem densityWeightedH1Representative_gradient_add {d : ℕ} (ρ : Vec d → ℝ)
    (hρ : Continuous ρ) (hρpos : ∀ x, 0 < ρ x) (σ : Vec d → ℝ) (K : ℝ)
    (hMeasure : densityWeightedMeasure σ ≤
      ENNReal.ofReal K • densityWeightedMeasure ρ)
    (u v : densityWeightedH1Submodule ρ hρ hρpos) :
    (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure (u + v)).weakGradient =ᵐ[
      densityWeightedMeasure σ] fun x =>
        (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure u).weakGradient x +
          (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure v).weakGradient x := by
  change (densityWeightedH1SpaceGradient (u + v) : Vec d → _) =ᵐ[densityWeightedMeasure σ]
    fun x => densityWeightedH1SpaceGradient u x + densityWeightedH1SpaceGradient v x
  rw [densityWeightedH1SpaceGradient_add]
  exact (Measure.absolutelyContinuous_of_le_smul hMeasure).ae_eq (Lp.coeFn_add _ _)

private theorem densityWeightedH1Representative_gradient_smul {d : ℕ} (ρ : Vec d → ℝ)
    (hρ : Continuous ρ) (hρpos : ∀ x, 0 < ρ x) (σ : Vec d → ℝ) (K : ℝ)
    (hMeasure : densityWeightedMeasure σ ≤
      ENNReal.ofReal K • densityWeightedMeasure ρ)
    (c : ℝ) (u : densityWeightedH1Submodule ρ hρ hρpos) :
    (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure (c • u)).weakGradient =ᵐ[
      densityWeightedMeasure σ] fun x => c •
        (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure u).weakGradient x := by
  change (densityWeightedH1SpaceGradient (c • u) : Vec d → _) =ᵐ[densityWeightedMeasure σ]
    fun x => c • densityWeightedH1SpaceGradient u x
  rw [densityWeightedH1SpaceGradient_smul]
  exact (Measure.absolutelyContinuous_of_le_smul hMeasure).ae_eq (Lp.coeFn_smul _ _)

private theorem densityWeightedH1Representative_value_add {d : ℕ} (ρ : Vec d → ℝ)
    (hρ : Continuous ρ) (hρpos : ∀ x, 0 < ρ x) (σ : Vec d → ℝ) (K : ℝ)
    (hMeasure : densityWeightedMeasure σ ≤
      ENNReal.ofReal K • densityWeightedMeasure ρ)
    (u v : densityWeightedH1Submodule ρ hρ hρpos) :
    (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure (u + v)).value =ᵐ[
      densityWeightedMeasure σ] fun x =>
        (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure u).value x +
          (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure v).value x := by
  change (densityWeightedH1SpaceValue (u + v) : Vec d → _) =ᵐ[densityWeightedMeasure σ]
    fun x => densityWeightedH1SpaceValue u x + densityWeightedH1SpaceValue v x
  rw [densityWeightedH1SpaceValue_add]
  exact (Measure.absolutelyContinuous_of_le_smul hMeasure).ae_eq (Lp.coeFn_add _ _)

private theorem densityWeightedH1Representative_value_smul {d : ℕ} (ρ : Vec d → ℝ)
    (hρ : Continuous ρ) (hρpos : ∀ x, 0 < ρ x) (σ : Vec d → ℝ) (K : ℝ)
    (hMeasure : densityWeightedMeasure σ ≤
      ENNReal.ofReal K • densityWeightedMeasure ρ)
    (c : ℝ) (u : densityWeightedH1Submodule ρ hρ hρpos) :
    (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure (c • u)).value =ᵐ[
      densityWeightedMeasure σ] fun x => c *
        (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure u).value x := by
  change (densityWeightedH1SpaceValue (c • u) : Vec d → _) =ᵐ[densityWeightedMeasure σ]
    fun x => c • densityWeightedH1SpaceValue u x
  rw [densityWeightedH1SpaceValue_smul]
  exact (Measure.absolutelyContinuous_of_le_smul hMeasure).ae_eq (Lp.coeFn_smul _ _)

private theorem sourcePhysicalValue_add {d : ℕ} (ρ : Vec d → ℝ)
    (hρ : Continuous ρ) (hρpos : ∀ x, 0 < ρ x) (σ : Vec d → ℝ) (K : ℝ)
    (hMeasure : densityWeightedMeasure σ ≤
      ENNReal.ofReal K • densityWeightedMeasure ρ)
    (u v : densityWeightedH1Submodule ρ hρ hρpos) :
    sourcePhysicalValue ρ hρ hρpos σ K hMeasure (u + v) =
      sourcePhysicalValue ρ hρ hρpos σ K hMeasure u +
        sourcePhysicalValue ρ hρ hρpos σ K hMeasure v := by
  unfold sourcePhysicalValue
  apply Lp.ext
  filter_upwards [densityWeightedH1Representative_value_add ρ hρ hρpos σ K hMeasure u v,
    (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure (u + v)).value_memLp.coeFn_toLp,
    (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure u).value_memLp.coeFn_toLp,
    (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure v).value_memLp.coeFn_toLp,
    Lp.coeFn_add
      ((sourcePhysicalGraph ρ hρ hρpos σ K hMeasure u).value_memLp.toLp
        (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure u).value)
      ((sourcePhysicalGraph ρ hρ hρpos σ K hMeasure v).value_memLp.toLp
        (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure v).value)]
    with x hadd hsum hu hv haddLp
  calc
    _ = (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure (u + v)).value x := hsum
    _ = (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure u).value x +
      (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure v).value x := hadd
    _ = ((sourcePhysicalGraph ρ hρ hρpos σ K hMeasure u).value_memLp.toLp
        (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure u).value) x +
      ((sourcePhysicalGraph ρ hρ hρpos σ K hMeasure v).value_memLp.toLp
        (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure v).value) x := by rw [← hu, ← hv]
    _ = _ := haddLp.symm

private theorem sourcePhysicalValue_smul {d : ℕ} (ρ : Vec d → ℝ)
    (hρ : Continuous ρ) (hρpos : ∀ x, 0 < ρ x) (σ : Vec d → ℝ) (K : ℝ)
    (hMeasure : densityWeightedMeasure σ ≤
      ENNReal.ofReal K • densityWeightedMeasure ρ)
    (c : ℝ) (u : densityWeightedH1Submodule ρ hρ hρpos) :
    sourcePhysicalValue ρ hρ hρpos σ K hMeasure (c • u) =
      c • sourcePhysicalValue ρ hρ hρpos σ K hMeasure u := by
  unfold sourcePhysicalValue
  apply Lp.ext
  filter_upwards [densityWeightedH1Representative_value_smul ρ hρ hρpos σ K hMeasure c u,
    (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure (c • u)).value_memLp.coeFn_toLp,
    (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure u).value_memLp.coeFn_toLp,
    Lp.coeFn_smul c ((sourcePhysicalGraph ρ hρ hρpos σ K hMeasure u).value_memLp.toLp
      (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure u).value)]
    with x hsmul hsum hu hsmulLp
  calc
    _ = (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure (c • u)).value x := hsum
    _ = c * (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure u).value x := hsmul
    _ = c * ((sourcePhysicalGraph ρ hρ hρpos σ K hMeasure u).value_memLp.toLp
        (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure u).value) x := by rw [← hu]
    _ = _ := hsmulLp.symm

private theorem sourcePhysicalForm_add_left {d : ℕ} (ρ : Vec d → ℝ)
    (hρ : Continuous ρ) (hρpos : ∀ x, 0 < ρ x) (σ : Vec d → ℝ) (K L : ℝ)
    (hL : 1 ≤ L)
    (hMeasure : densityWeightedMeasure σ ≤
      ENNReal.ofReal K • densityWeightedMeasure ρ) (ω : FieldPair d)
    (hω : IsRegular L ω) (u₁ u₂ v : densityWeightedH1Submodule ρ hρ hρpos) :
    sourcePhysicalDirichletForm ρ hρ hρpos σ K hMeasure ω.1 (u₁ + u₂) v =
      sourcePhysicalDirichletForm ρ hρ hρpos σ K hMeasure ω.1 u₁ v +
        sourcePhysicalDirichletForm ρ hρ hρpos σ K hMeasure ω.1 u₂ v := by
  unfold sourcePhysicalDirichletForm weightedSpatialForm
  have hfun : weightedFormIntegrand ω.1
      (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure (u₁ + u₂))
      (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure v) =ᵐ[densityWeightedMeasure σ]
      weightedFormIntegrand ω.1
          (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure u₁)
          (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure v) +
        weightedFormIntegrand ω.1
          (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure u₂)
          (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure v) := by
    filter_upwards [densityWeightedH1Representative_gradient_add ρ hρ hρpos σ K
      hMeasure u₁ u₂] with x hx
    change (1 / 2 : ℝ) * dot
        (WithLp.ofLp ((sourcePhysicalGraph ρ hρ hρpos σ K hMeasure (u₁ + u₂)).weakGradient x))
        ((ω.1 x).mulVec (WithLp.ofLp
          ((sourcePhysicalGraph ρ hρ hρpos σ K hMeasure v).weakGradient x))) =
      (1 / 2 : ℝ) * dot
        (WithLp.ofLp ((sourcePhysicalGraph ρ hρ hρpos σ K hMeasure u₁).weakGradient x))
        ((ω.1 x).mulVec (WithLp.ofLp
          ((sourcePhysicalGraph ρ hρ hρpos σ K hMeasure v).weakGradient x))) +
      (1 / 2 : ℝ) * dot
        (WithLp.ofLp ((sourcePhysicalGraph ρ hρ hρpos σ K hMeasure u₂).weakGradient x))
        ((ω.1 x).mulVec (WithLp.ofLp
          ((sourcePhysicalGraph ρ hρ hρpos σ K hMeasure v).weakGradient x)))
    rw [hx, WithLp.ofLp_add, sourceDot_add_left]
    ring
  calc
    _ = ∫ x, (weightedFormIntegrand ω.1
        (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure u₁)
        (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure v) +
      weightedFormIntegrand ω.1
        (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure u₂)
        (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure v)) x ∂densityWeightedMeasure σ :=
      integral_congr_ae hfun
    _ = _ := integral_add
      (physicalWeightedFormIntegrand_integrable_of_regular ω L hL hω _ _)
      (physicalWeightedFormIntegrand_integrable_of_regular ω L hL hω _ _)

private theorem sourcePhysicalForm_smul_left {d : ℕ} (ρ : Vec d → ℝ)
    (hρ : Continuous ρ) (hρpos : ∀ x, 0 < ρ x) (σ : Vec d → ℝ) (K : ℝ)
    (hMeasure : densityWeightedMeasure σ ≤
      ENNReal.ofReal K • densityWeightedMeasure ρ) (ω : FieldPair d)
    (c : ℝ) (u v : densityWeightedH1Submodule ρ hρ hρpos) :
    sourcePhysicalDirichletForm ρ hρ hρpos σ K hMeasure ω.1 (c • u) v =
      c * sourcePhysicalDirichletForm ρ hρ hρpos σ K hMeasure ω.1 u v := by
  unfold sourcePhysicalDirichletForm weightedSpatialForm
  have hfun : weightedFormIntegrand ω.1
      (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure (c • u))
      (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure v) =ᵐ[densityWeightedMeasure σ]
      fun x => c * weightedFormIntegrand ω.1
        (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure u)
        (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure v) x := by
    filter_upwards [densityWeightedH1Representative_gradient_smul ρ hρ hρpos σ K
      hMeasure c u] with x hx
    change (1 / 2 : ℝ) * dot
        (WithLp.ofLp ((sourcePhysicalGraph ρ hρ hρpos σ K hMeasure (c • u)).weakGradient x))
        ((ω.1 x).mulVec (WithLp.ofLp
          ((sourcePhysicalGraph ρ hρ hρpos σ K hMeasure v).weakGradient x))) =
      c * ((1 / 2 : ℝ) * dot
        (WithLp.ofLp ((sourcePhysicalGraph ρ hρ hρpos σ K hMeasure u).weakGradient x))
        ((ω.1 x).mulVec (WithLp.ofLp
          ((sourcePhysicalGraph ρ hρ hρpos σ K hMeasure v).weakGradient x))))
    rw [hx, WithLp.ofLp_smul, sourceDot_smul_left]
    ring
  calc
    _ = ∫ x, (fun y => c * weightedFormIntegrand ω.1
        (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure u)
        (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure v) y) x ∂densityWeightedMeasure σ :=
      integral_congr_ae hfun
    _ = c * _ := integral_const_mul _ _

private theorem sourcePhysicalForm_add_right {d : ℕ} (ρ : Vec d → ℝ)
    (hρ : Continuous ρ) (hρpos : ∀ x, 0 < ρ x) (σ : Vec d → ℝ) (K L : ℝ)
    (hL : 1 ≤ L)
    (hMeasure : densityWeightedMeasure σ ≤
      ENNReal.ofReal K • densityWeightedMeasure ρ) (ω : FieldPair d)
    (hω : IsRegular L ω) (u v₁ v₂ : densityWeightedH1Submodule ρ hρ hρpos) :
    sourcePhysicalDirichletForm ρ hρ hρpos σ K hMeasure ω.1 u (v₁ + v₂) =
      sourcePhysicalDirichletForm ρ hρ hρpos σ K hMeasure ω.1 u v₁ +
        sourcePhysicalDirichletForm ρ hρ hρpos σ K hMeasure ω.1 u v₂ := by
  unfold sourcePhysicalDirichletForm weightedSpatialForm
  have hfun : weightedFormIntegrand ω.1
      (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure u)
      (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure (v₁ + v₂)) =ᵐ[
        densityWeightedMeasure σ]
      weightedFormIntegrand ω.1
          (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure u)
          (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure v₁) +
        weightedFormIntegrand ω.1
          (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure u)
          (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure v₂) := by
    filter_upwards [densityWeightedH1Representative_gradient_add ρ hρ hρpos σ K
      hMeasure v₁ v₂] with x hx
    change (1 / 2 : ℝ) * dot
        (WithLp.ofLp ((sourcePhysicalGraph ρ hρ hρpos σ K hMeasure u).weakGradient x))
        ((ω.1 x).mulVec (WithLp.ofLp
          ((sourcePhysicalGraph ρ hρ hρpos σ K hMeasure (v₁ + v₂)).weakGradient x))) =
      (1 / 2 : ℝ) * dot
        (WithLp.ofLp ((sourcePhysicalGraph ρ hρ hρpos σ K hMeasure u).weakGradient x))
        ((ω.1 x).mulVec (WithLp.ofLp
          ((sourcePhysicalGraph ρ hρ hρpos σ K hMeasure v₁).weakGradient x))) +
      (1 / 2 : ℝ) * dot
        (WithLp.ofLp ((sourcePhysicalGraph ρ hρ hρpos σ K hMeasure u).weakGradient x))
        ((ω.1 x).mulVec (WithLp.ofLp
          ((sourcePhysicalGraph ρ hρ hρpos σ K hMeasure v₂).weakGradient x)))
    rw [hx, WithLp.ofLp_add, Matrix.mulVec_add, sourceDot_add_right]
    ring
  calc
    _ = ∫ x, (weightedFormIntegrand ω.1
        (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure u)
        (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure v₁) +
      weightedFormIntegrand ω.1
        (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure u)
        (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure v₂)) x ∂densityWeightedMeasure σ :=
      integral_congr_ae hfun
    _ = _ := integral_add
      (physicalWeightedFormIntegrand_integrable_of_regular ω L hL hω _ _)
      (physicalWeightedFormIntegrand_integrable_of_regular ω L hL hω _ _)

private theorem sourcePhysicalForm_smul_right {d : ℕ} (ρ : Vec d → ℝ)
    (hρ : Continuous ρ) (hρpos : ∀ x, 0 < ρ x) (σ : Vec d → ℝ) (K : ℝ)
    (hMeasure : densityWeightedMeasure σ ≤
      ENNReal.ofReal K • densityWeightedMeasure ρ) (ω : FieldPair d)
    (c : ℝ) (u v : densityWeightedH1Submodule ρ hρ hρpos) :
    sourcePhysicalDirichletForm ρ hρ hρpos σ K hMeasure ω.1 u (c • v) =
      c * sourcePhysicalDirichletForm ρ hρ hρpos σ K hMeasure ω.1 u v := by
  unfold sourcePhysicalDirichletForm weightedSpatialForm
  have hfun : weightedFormIntegrand ω.1
      (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure u)
      (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure (c • v)) =ᵐ[
        densityWeightedMeasure σ]
      fun x => c * weightedFormIntegrand ω.1
        (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure u)
        (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure v) x := by
    filter_upwards [densityWeightedH1Representative_gradient_smul ρ hρ hρpos σ K
      hMeasure c v] with x hx
    change (1 / 2 : ℝ) * dot
        (WithLp.ofLp ((sourcePhysicalGraph ρ hρ hρpos σ K hMeasure u).weakGradient x))
        ((ω.1 x).mulVec (WithLp.ofLp
          ((sourcePhysicalGraph ρ hρ hρpos σ K hMeasure (c • v)).weakGradient x))) =
      c * ((1 / 2 : ℝ) * dot
        (WithLp.ofLp ((sourcePhysicalGraph ρ hρ hρpos σ K hMeasure u).weakGradient x))
        ((ω.1 x).mulVec (WithLp.ofLp
          ((sourcePhysicalGraph ρ hρ hρpos σ K hMeasure v).weakGradient x))))
    rw [hx, WithLp.ofLp_smul, Matrix.mulVec_smul, sourceDot_smul_right]
    ring
  calc
    _ = ∫ x, (fun y => c * weightedFormIntegrand ω.1
        (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure u)
        (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure v) y) x ∂densityWeightedMeasure σ :=
      integral_congr_ae hfun
    _ = c * _ := integral_const_mul _ _

private theorem sourcePhysicalValue_norm_le {d : ℕ} (ρ : Vec d → ℝ)
    (hρ : Continuous ρ) (hρpos : ∀ x, 0 < ρ x) (σ : Vec d → ℝ) (L : ℝ)
    (hMeasure : densityWeightedMeasure σ ≤
      ENNReal.ofReal (Real.exp (2 * L)) • densityWeightedMeasure ρ)
    (u : densityWeightedH1Submodule ρ hρ hρpos) :
    ‖sourcePhysicalValue ρ hρ hρpos σ (Real.exp (2 * L)) hMeasure u‖ ≤
      Real.exp L * ‖u‖ := by
  let μρ := densityWeightedMeasure ρ
  let μσ := densityWeightedMeasure σ
  let K := Real.exp (2 * L)
  let g := densityWeightedH1SpaceRepresentative ρ hρ hρpos u
  let p := sourcePhysicalGraph ρ hρ hρpos σ K hMeasure u
  have hK : 0 ≤ K := (Real.exp_pos _).le
  have hExpSquared : Real.exp L * Real.exp L = K := by
    dsimp [K]
    rw [← Real.exp_add]
    congr 1
    ring
  have hredValue : ∫ x, ‖g.value x‖ ^ 2 ∂μρ ≤ ‖u‖ ^ 2 := by
    have hgradNonneg : 0 ≤ᵐ[μρ] fun x => ‖g.weakGradient x‖ ^ 2 := by
      filter_upwards [] with x
      positivity
    calc
      _ ≤ (∫ x, ‖g.value x‖ ^ 2 ∂μρ) +
          ∫ x, ‖g.weakGradient x‖ ^ 2 ∂μρ :=
        le_add_of_nonneg_right (integral_nonneg_of_ae hgradNonneg)
      _ = ‖u‖ ^ 2 := by
        simpa [g, μρ, Real.norm_eq_abs, sq_abs] using
          (densityWeightedH1Space_norm_sq_integral u).symm
  have hphysicalSq :
      ‖sourcePhysicalValue ρ hρ hρpos σ K hMeasure u‖ ^ 2 ≤ K * ‖u‖ ^ 2 := by
    calc
      _ = ∫ x, ‖p.value_memLp.toLp p.value x‖ ^ 2 ∂μσ :=
        l2_norm_sq_eq_integral_norm_sq _
      _ = ∫ x, ‖p.value x‖ ^ 2 ∂μσ := by
        apply integral_congr_ae
        filter_upwards [p.value_memLp.coeFn_toLp] with x hx
        rw [hx]
      _ ≤ K * ∫ x, ‖g.value x‖ ^ 2 ∂μρ :=
        integral_le_const_mul_of_measure_le μσ μρ K hK hMeasure
          (fun x => ‖g.value x‖ ^ 2) (by
            filter_upwards [] with x
            positivity) (g.value_memLp.integrable_norm_pow (by norm_num))
      _ ≤ K * ‖u‖ ^ 2 := mul_le_mul_of_nonneg_left hredValue hK
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.exp_nonneg _) (norm_nonneg _))).mp
  rw [pow_two]
  calc
    ‖sourcePhysicalValue ρ hρ hρpos σ K hMeasure u‖ *
        ‖sourcePhysicalValue ρ hρ hρpos σ K hMeasure u‖ =
      ‖sourcePhysicalValue ρ hρ hρpos σ K hMeasure u‖ ^ 2 := by rw [pow_two]
    _ ≤ K * ‖u‖ ^ 2 := hphysicalSq
    _ = (Real.exp L * ‖u‖) ^ 2 := by
      rw [pow_two, ← hExpSquared]
      ring

private noncomputable def sourcePhysicalValueLinearMap {d : ℕ} (ρ : Vec d → ℝ)
    (hρ : Continuous ρ) (hρpos : ∀ x, 0 < ρ x) (σ : Vec d → ℝ) (L : ℝ)
    (hMeasure : densityWeightedMeasure σ ≤
      ENNReal.ofReal (Real.exp (2 * L)) • densityWeightedMeasure ρ) :
    densityWeightedH1Submodule ρ hρ hρpos →ₗ[ℝ]
      Lp ℝ 2 (densityWeightedMeasure σ) where
  toFun := sourcePhysicalValue ρ hρ hρpos σ (Real.exp (2 * L)) hMeasure
  map_add' := sourcePhysicalValue_add ρ hρ hρpos σ (Real.exp (2 * L)) hMeasure
  map_smul' := sourcePhysicalValue_smul ρ hρ hρpos σ (Real.exp (2 * L)) hMeasure

private noncomputable def sourcePhysicalValueContinuousLinearMap {d : ℕ}
    (ρ : Vec d → ℝ) (hρ : Continuous ρ) (hρpos : ∀ x, 0 < ρ x)
    (σ : Vec d → ℝ) (L : ℝ)
    (hMeasure : densityWeightedMeasure σ ≤
      ENNReal.ofReal (Real.exp (2 * L)) • densityWeightedMeasure ρ) :
    densityWeightedH1Submodule ρ hρ hρpos →L[ℝ]
      Lp ℝ 2 (densityWeightedMeasure σ) :=
  (sourcePhysicalValueLinearMap ρ hρ hρpos σ L hMeasure).mkContinuous (Real.exp L)
    (by
      intro u
      exact sourcePhysicalValue_norm_le ρ hρ hρpos σ L hMeasure u)

private noncomputable def sourcePhysicalResolventBilinear {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam L α : ℝ) (hL : 1 ≤ L) (hω : IsRegular L ω)
    (hα : 0 < α) :
    densityWeightedH1Submodule (physicalForceWeight hd lam)
      (physicalForceWeight_continuous hd lam) (physicalForceWeight_pos hd lam) →L[ℝ]
    densityWeightedH1Submodule (physicalForceWeight hd lam)
      (physicalForceWeight_continuous hd lam) (physicalForceWeight_pos hd lam) →L[ℝ] ℝ := by
  let ρ := physicalForceWeight hd lam
  let hρ := physicalForceWeight_continuous hd lam
  let hρpos := physicalForceWeight_pos hd lam
  let σ := physicalReversibleDensity ω hd lam
  let K := Real.exp (2 * L)
  let hMeasure : densityWeightedMeasure σ ≤
      ENNReal.ofReal K • densityWeightedMeasure ρ :=
    sourcePhysicalMeasure_le_reduced ω hd lam L hω
  let V := densityWeightedH1Submodule ρ hρ hρpos
  let B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ (fun u v => α * inner ℝ
      (sourcePhysicalValue ρ hρ hρpos σ K hMeasure u)
      (sourcePhysicalValue ρ hρ hρpos σ K hMeasure v) +
      sourcePhysicalDirichletForm ρ hρ hρpos σ K hMeasure ω.1 u v)
      (by
        intro u₁ u₂ v
        rw [sourcePhysicalValue_add, inner_add_left,
          sourcePhysicalForm_add_left ρ hρ hρpos σ K L hL hMeasure ω hω u₁ u₂ v]
        ring)
      (by
        intro c u v
        rw [sourcePhysicalValue_smul, inner_smul_left, sourcePhysicalForm_smul_left]
        simp only [smul_eq_mul, starRingEnd_apply, star_trivial]
        ring)
      (by
        intro u v₁ v₂
        rw [sourcePhysicalValue_add, inner_add_right,
          sourcePhysicalForm_add_right ρ hρ hρpos σ K L hL hMeasure ω hω u v₁ v₂]
        ring)
      (by
        intro c u v
        rw [sourcePhysicalValue_smul, inner_smul_right, sourcePhysicalForm_smul_right]
        simp only [smul_eq_mul]
        ring)
  exact B.mkContinuous₂ (Real.exp (2 * L) * (α + L / 2)) (by
    intro u v
    rw [Real.norm_eq_abs]
    exact sourcePhysicalResolventForm_bounded hd ω lam L α hL hω hα u v)

private theorem sourcePhysicalResolventBilinear_apply {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam L α : ℝ) (hL : 1 ≤ L) (hω : IsRegular L ω) (hα : 0 < α)
    (u v : PhysicalH1Space hd lam) :
    sourcePhysicalResolventBilinear hd ω lam L α hL hω hα u v =
      α * inner ℝ (sourcePhysicalValue (physicalForceWeight hd lam)
        (physicalForceWeight_continuous hd lam) (physicalForceWeight_pos hd lam)
        (physicalReversibleDensity ω hd lam) (Real.exp (2 * L))
        (sourcePhysicalMeasure_le_reduced ω hd lam L hω) u)
        (sourcePhysicalValue (physicalForceWeight hd lam)
        (physicalForceWeight_continuous hd lam) (physicalForceWeight_pos hd lam)
        (physicalReversibleDensity ω hd lam) (Real.exp (2 * L))
        (sourcePhysicalMeasure_le_reduced ω hd lam L hω) v) +
      sourcePhysicalDirichletForm (physicalForceWeight hd lam)
        (physicalForceWeight_continuous hd lam) (physicalForceWeight_pos hd lam)
        (physicalReversibleDensity ω hd lam) (Real.exp (2 * L))
        (sourcePhysicalMeasure_le_reduced ω hd lam L hω) ω.1 u v := rfl

private theorem sourcePhysicalResolventBilinear_isCoercive {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam L α : ℝ) (hL : 1 ≤ L) (hω : IsRegular L ω)
    (hα : 0 < α) :
    IsCoercive (sourcePhysicalResolventBilinear hd ω lam L α hL hω hα) := by
  let C := Real.exp (-2 * L) * min α ((1 / 2 : ℝ) * L⁻¹)
  have hC : 0 < C := by
    dsimp [C]
    exact sourcePhysicalResolvent_coercivity_constant_pos L α hL hα
  refine ⟨C, hC, ?_⟩
  intro u
  calc
    C * ‖u‖ * ‖u‖ = C * ‖u‖ ^ 2 := by rw [pow_two]; ring
    _ ≤ α * inner ℝ
        (sourcePhysicalValue (physicalForceWeight hd lam)
          (physicalForceWeight_continuous hd lam) (physicalForceWeight_pos hd lam)
          (physicalReversibleDensity ω hd lam) (Real.exp (2 * L))
          (sourcePhysicalMeasure_le_reduced ω hd lam L hω) u)
        (sourcePhysicalValue (physicalForceWeight hd lam)
          (physicalForceWeight_continuous hd lam) (physicalForceWeight_pos hd lam)
          (physicalReversibleDensity ω hd lam) (Real.exp (2 * L))
          (sourcePhysicalMeasure_le_reduced ω hd lam L hω) u) +
      sourcePhysicalDirichletForm (physicalForceWeight hd lam)
        (physicalForceWeight_continuous hd lam) (physicalForceWeight_pos hd lam)
        (physicalReversibleDensity ω hd lam) (Real.exp (2 * L))
        (sourcePhysicalMeasure_le_reduced ω hd lam L hω) ω.1 u u := by
      exact sourcePhysicalResolvent_coercive hd ω lam L α hL hω hα u

private noncomputable def sourcePhysicalResolventForcingForm {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam L : ℝ) (hω : IsRegular L ω)
    (f : Lp ℝ 2 (densityWeightedMeasure (physicalReversibleDensity ω hd lam))) :
    densityWeightedH1Submodule (physicalForceWeight hd lam)
      (physicalForceWeight_continuous hd lam) (physicalForceWeight_pos hd lam) →L[ℝ] ℝ :=
  (innerSL ℝ f).comp
    (sourcePhysicalValueContinuousLinearMap (physicalForceWeight hd lam)
      (physicalForceWeight_continuous hd lam) (physicalForceWeight_pos hd lam)
      (physicalReversibleDensity ω hd lam) L (sourcePhysicalMeasure_le_reduced ω hd lam L hω))

/-- The physical resolvent equation tested on the completed smooth-interior domain.
All pairings use the actual speed measure and the original weak-gradient representatives. -/
def HasPhysicalZeroBoundaryResolvent {d : ℕ} (U : Set (Vec d)) (ω : FieldPair d)
    (hd : 2 ≤ d) (lam α : ℝ) (f : Vec d → ℝ)
    (u : physicalH1ZeroBoundary U hd lam) : Prop :=
  0 < α ∧ ∀ v : physicalH1ZeroBoundary U hd lam,
    α * (∫ x, densityWeightedH1SpaceValue u.1 x * densityWeightedH1SpaceValue v.1 x
      ∂physicalReversibleMeasure ω hd lam) +
      (∫ x, weightedFormIntegrand ω.1 (physicalH1SpaceRepresentative hd lam u.1)
        (physicalH1SpaceRepresentative hd lam v.1) x ∂physicalReversibleMeasure ω hd lam) =
      ∫ x, f x * densityWeightedH1SpaceValue v.1 x ∂physicalReversibleMeasure ω hd lam

private theorem physicalValue_inner_eq_integral {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam L : ℝ) (hω : IsRegular L ω) (u v : PhysicalH1Space hd lam) :
    inner ℝ (sourcePhysicalValue (physicalForceWeight hd lam)
      (physicalForceWeight_continuous hd lam) (physicalForceWeight_pos hd lam)
      (physicalReversibleDensity ω hd lam) (Real.exp (2 * L))
      (sourcePhysicalMeasure_le_reduced ω hd lam L hω) u)
      (sourcePhysicalValue (physicalForceWeight hd lam)
      (physicalForceWeight_continuous hd lam) (physicalForceWeight_pos hd lam)
      (physicalReversibleDensity ω hd lam) (Real.exp (2 * L))
      (sourcePhysicalMeasure_le_reduced ω hd lam L hω) v) =
    ∫ x, densityWeightedH1SpaceValue u x * densityWeightedH1SpaceValue v x
      ∂physicalReversibleMeasure ω hd lam := by
  rw [L2.inner_def]
  apply integral_congr_ae
  let p := sourcePhysicalGraph (physicalForceWeight hd lam)
    (physicalForceWeight_continuous hd lam) (physicalForceWeight_pos hd lam)
    (physicalReversibleDensity ω hd lam) (Real.exp (2 * L))
    (sourcePhysicalMeasure_le_reduced ω hd lam L hω)
  filter_upwards [(p u).value_memLp.coeFn_toLp, (p v).value_memLp.coeFn_toLp] with x hu hv
  change inner ℝ (((p u).value_memLp.toLp (p u).value) x)
    (((p v).value_memLp.toLp (p v).value) x) = _
  rw [hu, hv]
  simp only [RCLike.inner_apply', conj_trivial]
  rfl

private theorem physicalForcing_inner_eq_integral {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam L : ℝ) (hω : IsRegular L ω)
    (f : Vec d → ℝ) (hf : MemLp f 2 (physicalReversibleMeasure ω hd lam))
    (v : PhysicalH1Space hd lam) :
    inner ℝ (hf.toLp f) (sourcePhysicalValue (physicalForceWeight hd lam)
      (physicalForceWeight_continuous hd lam) (physicalForceWeight_pos hd lam)
      (physicalReversibleDensity ω hd lam) (Real.exp (2 * L))
      (sourcePhysicalMeasure_le_reduced ω hd lam L hω) v) =
    ∫ x, f x * densityWeightedH1SpaceValue v x ∂physicalReversibleMeasure ω hd lam := by
  refine (L2.inner_def _ _).trans ?_
  apply integral_congr_ae
  let p := sourcePhysicalGraph (physicalForceWeight hd lam)
    (physicalForceWeight_continuous hd lam) (physicalForceWeight_pos hd lam)
    (physicalReversibleDensity ω hd lam) (Real.exp (2 * L))
    (sourcePhysicalMeasure_le_reduced ω hd lam L hω) v
  filter_upwards [hf.coeFn_toLp, p.value_memLp.coeFn_toLp] with x hf' hv
  change inner ℝ ((hf.toLp f) x) ((p.value_memLp.toLp p.value) x) = _
  rw [hf', hv]
  simp only [RCLike.inner_apply', conj_trivial]
  rfl

private def restrictBilinear {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (B : V →L[ℝ] V →L[ℝ] ℝ) (S : Submodule ℝ V) :
    S →L[ℝ] S →L[ℝ] ℝ :=
  B.bilinearComp S.subtypeL S.subtypeL

private theorem restrictBilinear_isCoercive {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (B : V →L[ℝ] V →L[ℝ] ℝ) (S : Submodule ℝ V)
    (hB : IsCoercive B) : IsCoercive (restrictBilinear B S) := by
  obtain ⟨C, hC, hbound⟩ := hB
  exact ⟨C, hC, fun u => hbound u.1⟩

private def physicalZeroBoundaryBilinear {d : ℕ} (U : Set (Vec d)) (hd : 2 ≤ d)
    (ω : FieldPair d) (lam L α : ℝ) (hL : 1 ≤ L) (hω : IsRegular L ω) (hα : 0 < α) :
    physicalH1ZeroBoundary U hd lam →L[ℝ] physicalH1ZeroBoundary U hd lam →L[ℝ] ℝ :=
  restrictBilinear (sourcePhysicalResolventBilinear hd ω lam L α hL hω hα)
    (physicalH1ZeroBoundary U hd lam)

private theorem physicalZeroBoundaryBilinear_apply_coe {d : ℕ} (U : Set (Vec d))
    (hd : 2 ≤ d) (ω : FieldPair d) (lam L α : ℝ) (hL : 1 ≤ L)
    (hω : IsRegular L ω) (hα : 0 < α) (u v : physicalH1ZeroBoundary U hd lam) :
    physicalZeroBoundaryBilinear U hd ω lam L α hL hω hα u v =
      sourcePhysicalResolventBilinear hd ω lam L α hL hω hα u.1 v.1 := rfl

private theorem sourcePhysicalGraph_weakGradient {d : ℕ} (ρ : Vec d → ℝ)
    (hρ : Continuous ρ) (hρpos : ∀ x, 0 < ρ x) (σ : Vec d → ℝ) (K : ℝ)
    (hMeasure : densityWeightedMeasure σ ≤ ENNReal.ofReal K • densityWeightedMeasure ρ)
    (u : densityWeightedH1Submodule ρ hρ hρpos) :
    (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure u).weakGradient =
      (densityWeightedH1SpaceRepresentative ρ hρ hρpos u).weakGradient := rfl

private theorem sourcePhysicalDirichletForm_eq_physical_integral {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam L : ℝ) (hω : IsRegular L ω) (u v : PhysicalH1Space hd lam) :
    sourcePhysicalDirichletForm (physicalForceWeight hd lam)
      (physicalForceWeight_continuous hd lam) (physicalForceWeight_pos hd lam)
      (physicalReversibleDensity ω hd lam) (Real.exp (2 * L))
      (sourcePhysicalMeasure_le_reduced ω hd lam L hω) ω.1 u v =
      ∫ x, weightedFormIntegrand ω.1 (physicalH1SpaceRepresentative hd lam u)
        (physicalH1SpaceRepresentative hd lam v) x ∂physicalReversibleMeasure ω hd lam := by
  unfold sourcePhysicalDirichletForm weightedSpatialForm
  apply integral_congr_ae
  filter_upwards [] with x
  have hu := sourcePhysicalGraph_weakGradient (physicalForceWeight hd lam)
    (physicalForceWeight_continuous hd lam) (physicalForceWeight_pos hd lam)
    (physicalReversibleDensity ω hd lam) (Real.exp (2 * L))
    (sourcePhysicalMeasure_le_reduced ω hd lam L hω) u
  have hv := sourcePhysicalGraph_weakGradient (physicalForceWeight hd lam)
    (physicalForceWeight_continuous hd lam) (physicalForceWeight_pos hd lam)
    (physicalReversibleDensity ω hd lam) (Real.exp (2 * L))
    (sourcePhysicalMeasure_le_reduced ω hd lam L hω) v
  simp only [weightedFormIntegrand, physicalH1SpaceRepresentative, hu, hv]

private theorem physicalZeroBoundaryBilinear_apply {d : ℕ} (U : Set (Vec d)) (hd : 2 ≤ d)
    (ω : FieldPair d) (lam L α : ℝ) (hL : 1 ≤ L) (hω : IsRegular L ω) (hα : 0 < α)
    (u v : physicalH1ZeroBoundary U hd lam) :
    physicalZeroBoundaryBilinear U hd ω lam L α hL hω hα u v =
      α * (∫ x, densityWeightedH1SpaceValue u.1 x * densityWeightedH1SpaceValue v.1 x
        ∂physicalReversibleMeasure ω hd lam) +
      ∫ x, weightedFormIntegrand ω.1 (physicalH1SpaceRepresentative hd lam u.1)
        (physicalH1SpaceRepresentative hd lam v.1) x ∂physicalReversibleMeasure ω hd lam := by
  have hmass := physicalValue_inner_eq_integral hd ω lam L hω u.1 v.1
  have hform := sourcePhysicalDirichletForm_eq_physical_integral hd ω lam L hω u.1 v.1
  exact (physicalZeroBoundaryBilinear_apply_coe U hd ω lam L α hL hω hα u v).trans
    ((sourcePhysicalResolventBilinear_apply hd ω lam L α hL hω hα u.1 v.1).trans
      (congrArg₂ (· + ·) (congrArg (α * ·) hmass) hform))

private theorem physicalZeroBoundaryBilinear_isCoercive {d : ℕ} (U : Set (Vec d))
    (hd : 2 ≤ d) (ω : FieldPair d) (lam L α : ℝ) (hL : 1 ≤ L)
    (hω : IsRegular L ω) (hα : 0 < α) :
    @IsCoercive (physicalH1ZeroBoundary U hd lam)
      (inferInstance : NormedAddCommGroup (physicalH1ZeroBoundary U hd lam)).toSeminormedAddCommGroup
      inferInstance
      (physicalZeroBoundaryBilinear U hd ω lam L α hL hω hα) := by
  exact restrictBilinear_isCoercive _ _
    (sourcePhysicalResolventBilinear_isCoercive hd ω lam L α hL hω hα)

private theorem coerciveBilinear_existsUnique {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [CompleteSpace V] (B : V →L[ℝ] V →L[ℝ] ℝ)
    (hB : IsCoercive B) (F : V →L[ℝ] ℝ) : ∃! u : V, ∀ v, B u v = F v := by
  let E := hB.continuousLinearEquivOfBilin
  let g := (InnerProductSpace.toDual ℝ V).symm F
  let u := E.symm g
  have hu (v : V) : B u v = F v := by
    rw [← hB.continuousLinearEquivOfBilin_apply]
    rw [show E u = g from E.apply_symm_apply g]
    exact InnerProductSpace.toDual_symm_apply
  refine ⟨u, hu, fun v hv => E.injective ?_⟩
  apply hB.unique_continuousLinearEquivOfBilin (v := u) (f := E v)
  intro w
  rw [hB.continuousLinearEquivOfBilin_apply]
  exact (hv w).trans (hu w).symm

private def physicalZeroBoundaryForcing {d : ℕ} (U : Set (Vec d)) (hd : 2 ≤ d)
    (ω : FieldPair d) (lam L : ℝ) (hω : IsRegular L ω)
    (f : Vec d → ℝ) (hf : MemLp f 2 (physicalReversibleMeasure ω hd lam)) :
    physicalH1ZeroBoundary U hd lam →L[ℝ] ℝ :=
  (sourcePhysicalResolventForcingForm hd ω lam L hω (hf.toLp f)).comp
    (physicalH1ZeroBoundary U hd lam).subtypeL

private theorem physicalZeroBoundaryForcing_apply {d : ℕ} (U : Set (Vec d)) (hd : 2 ≤ d)
    (ω : FieldPair d) (lam L : ℝ) (hω : IsRegular L ω)
    (f : Vec d → ℝ) (hf : MemLp f 2 (physicalReversibleMeasure ω hd lam))
    (v : physicalH1ZeroBoundary U hd lam) :
    physicalZeroBoundaryForcing U hd ω lam L hω f hf v =
      ∫ x, f x * densityWeightedH1SpaceValue v.1 x ∂physicalReversibleMeasure ω hd lam :=
  physicalForcing_inner_eq_integral hd ω lam L hω f hf v.1

private theorem hasPhysicalZeroBoundaryResolvent_iff_bilinear {d : ℕ}
    (U : Set (Vec d)) (hd : 2 ≤ d) (ω : FieldPair d) (lam L α : ℝ)
    (hL : 1 ≤ L) (hω : IsRegular L ω) (hα : 0 < α)
    (f : Vec d → ℝ) (hf : MemLp f 2 (physicalReversibleMeasure ω hd lam))
    (u : physicalH1ZeroBoundary U hd lam) :
    HasPhysicalZeroBoundaryResolvent U ω hd lam α f u ↔
      ∀ v, physicalZeroBoundaryBilinear U hd ω lam L α hL hω hα u v =
        physicalZeroBoundaryForcing U hd ω lam L hω f hf v := by
  constructor
  · intro hu v
    exact (physicalZeroBoundaryBilinear_apply U hd ω lam L α hL hω hα u v).trans
      ((hu.2 v).trans (physicalZeroBoundaryForcing_apply U hd ω lam L hω f hf v).symm)
  · intro hu
    refine ⟨hα, fun v => ?_⟩
    exact (physicalZeroBoundaryBilinear_apply U hd ω lam L α hL hω hα u v).symm.trans
      ((hu v).trans (physicalZeroBoundaryForcing_apply U hd ω lam L hω f hf v))

/-- A genuine variational resolvent exists uniquely on the closed zero-boundary graph for
any physical L² datum and positive rate, including arbitrary signed force. -/
theorem physicalZeroBoundaryResolvent_existsUnique {d : ℕ} (U : Set (Vec d)) (hd : 2 ≤ d)
    (ω : FieldPair d) (lam L α : ℝ) (hL : 1 ≤ L) (hω : IsRegular L ω) (hα : 0 < α)
    (f : Vec d → ℝ) (hf : MemLp f 2 (physicalReversibleMeasure ω hd lam)) :
    ∃! u : physicalH1ZeroBoundary U hd lam,
      HasPhysicalZeroBoundaryResolvent U ω hd lam α f u := by
  obtain ⟨u, hu, huniq⟩ := coerciveBilinear_existsUnique
    (V := physicalH1ZeroBoundary U hd lam)
    (physicalZeroBoundaryBilinear U hd ω lam L α hL hω hα)
    (physicalZeroBoundaryBilinear_isCoercive U hd ω lam L α hL hω hα)
    (physicalZeroBoundaryForcing U hd ω lam L hω f hf)
  have hspec := hasPhysicalZeroBoundaryResolvent_iff_bilinear U hd ω lam L α hL hω hα f hf
  exact ⟨u, (hspec u).mpr hu, fun w hw => huniq w ((hspec w).mp hw)⟩

/-- A zero-boundary value localizes its physical pairing to the region, so agreement of
both physical fields there gives equality for every literal first factor. -/
theorem physicalZeroBoundaryValuePairing_eq_of_physical_eqOn {d : ℕ}
    (U : Set (Vec d)) (hU : MeasurableSet U) (ω ω' : FieldPair d)
    (heq : ∀ y ∈ U, ω.1 y = ω'.1 y ∧ ω.2 y = ω'.2 y)
    (hd : 2 ≤ d) (lam : ℝ) (f : Vec d → ℝ) (v : physicalH1ZeroBoundary U hd lam) :
    (∫ x, f x * densityWeightedH1SpaceValue v.1 x ∂physicalReversibleMeasure ω hd lam) =
      ∫ x, f x * densityWeightedH1SpaceValue v.1 x ∂physicalReversibleMeasure ω' hd lam := by
  have hzero := physicalH1ZeroBoundary_value_zero_off U hd lam v.1 v.2
  have hlocal (η : FieldPair d) :
      (∫ x, f x * densityWeightedH1SpaceValue v.1 x ∂physicalReversibleMeasure η hd lam) =
      ∫ x in U, f x * densityWeightedH1SpaceValue v.1 x
        ∂physicalReversibleMeasure η hd lam := by
    symm
    apply setIntegral_eq_integral_of_ae_compl_eq_zero
    have hzero' : ∀ᵐ x ∂physicalReversibleMeasure η hd lam,
        x ∉ U → densityWeightedH1SpaceValue v.1 x = 0 :=
      (withDensity_absolutelyContinuous _ _).ae_le hzero
    filter_upwards [hzero'] with x hx hxU
    simp only [hx hxU, mul_zero]
  rw [hlocal ω, hlocal ω',
    physicalReversibleMeasure_restrict_eq_of_physical_eqOn U hU ω ω' heq hd lam]

/-- The actual variational equations on the completed interior domain are identical
under agreement of both coefficient fields on that region. -/
theorem hasPhysicalZeroBoundaryResolvent_iff_of_physical_eqOn {d : ℕ}
    (U : Set (Vec d)) (hU : MeasurableSet U) (ω ω' : FieldPair d)
    (heq : ∀ y ∈ U, ω.1 y = ω'.1 y ∧ ω.2 y = ω'.2 y)
    (hd : 2 ≤ d) (lam α : ℝ) (f : Vec d → ℝ) (u : physicalH1ZeroBoundary U hd lam) :
    HasPhysicalZeroBoundaryResolvent U ω hd lam α f u ↔
      HasPhysicalZeroBoundaryResolvent U ω' hd lam α f u := by
  have hidentity (v : physicalH1ZeroBoundary U hd lam) :
      (α * (∫ x, densityWeightedH1SpaceValue u.1 x * densityWeightedH1SpaceValue v.1 x
        ∂physicalReversibleMeasure ω hd lam) +
      ∫ x, weightedFormIntegrand ω.1 (physicalH1SpaceRepresentative hd lam u.1)
        (physicalH1SpaceRepresentative hd lam v.1) x ∂physicalReversibleMeasure ω hd lam) =
      α * (∫ x, densityWeightedH1SpaceValue u.1 x * densityWeightedH1SpaceValue v.1 x
        ∂physicalReversibleMeasure ω' hd lam) +
      ∫ x, weightedFormIntegrand ω'.1 (physicalH1SpaceRepresentative hd lam u.1)
        (physicalH1SpaceRepresentative hd lam v.1) x ∂physicalReversibleMeasure ω' hd lam := by
    rw [physicalZeroBoundaryValuePairing_eq_of_physical_eqOn U hU ω ω' heq hd lam
      (densityWeightedH1SpaceValue u.1) v,
      physicalWeightedForm_eq_on_zeroBoundary U hU ω ω' heq hd lam u.1 v.1 u.2]
  constructor
  · rintro ⟨hα, hu⟩
    refine ⟨hα, fun v => ?_⟩
    rw [← hidentity v, ← physicalZeroBoundaryValuePairing_eq_of_physical_eqOn
      U hU ω ω' heq hd lam f v]
    exact hu v
  · rintro ⟨hα, hu⟩
    refine ⟨hα, fun v => ?_⟩
    rw [hidentity v, physicalZeroBoundaryValuePairing_eq_of_physical_eqOn
      U hU ω ω' heq hd lam f v]
    exact hu v

/-- The uniquely constructed physical variational resolvent on the completed interior domain. -/
def physicalZeroBoundaryResolvent {d : ℕ} (U : Set (Vec d)) (hd : 2 ≤ d)
    (ω : FieldPair d) (lam L α : ℝ) (hL : 1 ≤ L) (hω : IsRegular L ω) (hα : 0 < α)
    (f : Vec d → ℝ) (hf : MemLp f 2 (physicalReversibleMeasure ω hd lam)) :
    physicalH1ZeroBoundary U hd lam :=
  Classical.choose (physicalZeroBoundaryResolvent_existsUnique U hd ω lam L α hL hω hα f hf)

/-- The constructed resolvent satisfies its actual physical integral equation. -/
theorem physicalZeroBoundaryResolvent_spec {d : ℕ} (U : Set (Vec d)) (hd : 2 ≤ d)
    (ω : FieldPair d) (lam L α : ℝ) (hL : 1 ≤ L) (hω : IsRegular L ω) (hα : 0 < α)
    (f : Vec d → ℝ) (hf : MemLp f 2 (physicalReversibleMeasure ω hd lam)) :
    HasPhysicalZeroBoundaryResolvent U ω hd lam α f
      (physicalZeroBoundaryResolvent U hd ω lam L α hL hω hα f hf) :=
  (Classical.choose_spec (physicalZeroBoundaryResolvent_existsUnique
    U hd ω lam L α hL hω hα f hf)).1

/-- Local agreement of the physical fields forces equality of the constructed interior
resolvents, for the same literal datum in both physical L² spaces. -/
theorem physicalZeroBoundaryResolvent_eq_of_physical_eqOn {d : ℕ}
    (U : Set (Vec d)) (hU : MeasurableSet U) (hd : 2 ≤ d) (ω ω' : FieldPair d)
    (heq : ∀ y ∈ U, ω.1 y = ω'.1 y ∧ ω.2 y = ω'.2 y)
    (lam L L' α : ℝ) (hL : 1 ≤ L) (hL' : 1 ≤ L')
    (hω : IsRegular L ω) (hω' : IsRegular L' ω') (hα : 0 < α) (f : Vec d → ℝ)
    (hf : MemLp f 2 (physicalReversibleMeasure ω hd lam))
    (hf' : MemLp f 2 (physicalReversibleMeasure ω' hd lam)) :
    physicalZeroBoundaryResolvent U hd ω lam L α hL hω hα f hf =
      physicalZeroBoundaryResolvent U hd ω' lam L' α hL' hω' hα f hf' := by
  apply (physicalZeroBoundaryResolvent_existsUnique U hd ω' lam L' α hL' hω' hα f hf').unique
  · exact (hasPhysicalZeroBoundaryResolvent_iff_of_physical_eqOn
      U hU ω ω' heq hd lam α f _).mp
      (physicalZeroBoundaryResolvent_spec U hd ω lam L α hL hω hα f hf)
  · exact physicalZeroBoundaryResolvent_spec U hd ω' lam L' α hL' hω' hα f hf'

/-- The value of a zero-boundary graph in the actual physical L² space. -/
def physicalZeroBoundaryValue {d : ℕ} (U : Set (Vec d)) (hd : 2 ≤ d)
    (ω : FieldPair d) (lam L : ℝ) (hω : IsRegular L ω) :
    physicalH1ZeroBoundary U hd lam →L[ℝ] Lp ℝ 2 (physicalReversibleMeasure ω hd lam) :=
  (sourcePhysicalValueContinuousLinearMap (physicalForceWeight hd lam)
    (physicalForceWeight_continuous hd lam) (physicalForceWeight_pos hd lam)
    (physicalReversibleDensity ω hd lam) L
    (sourcePhysicalMeasure_le_reduced ω hd lam L hω)).comp
      (physicalH1ZeroBoundary U hd lam).subtypeL

/-- The physical L² value has the original weak graph's value as representative. -/
theorem physicalZeroBoundaryValue_ae_eq {d : ℕ} (U : Set (Vec d)) (hd : 2 ≤ d)
    (ω : FieldPair d) (lam L : ℝ) (hω : IsRegular L ω)
    (u : physicalH1ZeroBoundary U hd lam) :
    physicalZeroBoundaryValue U hd ω lam L hω u =ᵐ[physicalReversibleMeasure ω hd lam]
      densityWeightedH1SpaceValue u.1 := by
  exact (sourcePhysicalGraph (physicalForceWeight hd lam)
    (physicalForceWeight_continuous hd lam) (physicalForceWeight_pos hd lam)
    (physicalReversibleDensity ω hd lam) (Real.exp (2 * L))
    (sourcePhysicalMeasure_le_reduced ω hd lam L hω) u.1).value_memLp.coeFn_toLp

private def variationalResolventGraph {V H : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [CompleteSpace V] [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (B : V →L[ℝ] V →L[ℝ] ℝ)
    (hB : IsCoercive B) (J : V →L[ℝ] H) : H →L[ℝ] V :=
  hB.continuousLinearEquivOfBilin.symm.toContinuousLinearMap.comp J.adjoint

private theorem variationalResolventGraph_spec {V H : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [CompleteSpace V] [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (B : V →L[ℝ] V →L[ℝ] ℝ)
    (hB : IsCoercive B) (J : V →L[ℝ] H) (f : H) (v : V) :
    B (variationalResolventGraph B hB J f) v = inner ℝ f (J v) := by
  rw [← hB.continuousLinearEquivOfBilin_apply]
  change inner ℝ (hB.continuousLinearEquivOfBilin
    (hB.continuousLinearEquivOfBilin.symm (J.adjoint f))) v = _
  rw [hB.continuousLinearEquivOfBilin.apply_symm_apply]
  exact J.adjoint_inner_left v f

/-- The zero-boundary variational solution depends continuously and linearly on the
physical L² equivalence class of the datum. -/
def physicalZeroBoundaryResolventGraph {d : ℕ} (U : Set (Vec d)) (hd : 2 ≤ d)
    (ω : FieldPair d) (lam L α : ℝ) (hL : 1 ≤ L) (hω : IsRegular L ω) (hα : 0 < α) :
    Lp ℝ 2 (physicalReversibleMeasure ω hd lam) →L[ℝ] physicalH1ZeroBoundary U hd lam :=
  variationalResolventGraph
    (V := physicalH1ZeroBoundary U hd lam)
    (H := Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (physicalZeroBoundaryBilinear U hd ω lam L α hL hω hα)
    (physicalZeroBoundaryBilinear_isCoercive U hd ω lam L α hL hω hα)
    (physicalZeroBoundaryValue U hd ω lam L hω)

private theorem physicalZeroBoundaryResolventGraph_bilinear {d : ℕ}
    (U : Set (Vec d)) (hd : 2 ≤ d) (ω : FieldPair d) (lam L α : ℝ)
    (hL : 1 ≤ L) (hω : IsRegular L ω) (hα : 0 < α)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) (v : physicalH1ZeroBoundary U hd lam) :
    physicalZeroBoundaryBilinear U hd ω lam L α hL hω hα
      (physicalZeroBoundaryResolventGraph U hd ω lam L α hL hω hα f) v =
      inner ℝ f (physicalZeroBoundaryValue U hd ω lam L hω v) :=
  variationalResolventGraph_spec
    (V := physicalH1ZeroBoundary U hd lam)
    (H := Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (physicalZeroBoundaryBilinear U hd ω lam L α hL hω hα)
    (physicalZeroBoundaryBilinear_isCoercive U hd ω lam L α hL hω hα)
    (physicalZeroBoundaryValue U hd ω lam L hω) f v

/-- The L² graph operator satisfies the literal physical weak equation. -/
theorem physicalZeroBoundaryResolventGraph_spec {d : ℕ} (U : Set (Vec d)) (hd : 2 ≤ d)
    (ω : FieldPair d) (lam L α : ℝ) (hL : 1 ≤ L) (hω : IsRegular L ω) (hα : 0 < α)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    HasPhysicalZeroBoundaryResolvent U ω hd lam α f
      (physicalZeroBoundaryResolventGraph U hd ω lam L α hL hω hα f) := by
  apply (hasPhysicalZeroBoundaryResolvent_iff_bilinear U hd ω lam L α hL hω hα
    f (Lp.memLp f) _).mpr
  intro v
  have hf : (Lp.memLp f).toLp f = f := by
    apply Lp.ext
    exact (Lp.memLp f).coeFn_toLp
  change _ = inner ℝ ((Lp.memLp f).toLp f) (physicalZeroBoundaryValue U hd ω lam L hω v)
  exact (physicalZeroBoundaryResolventGraph_bilinear U hd ω lam L α hL hω hα f v).trans
    (congrArg (fun q => inner ℝ q (physicalZeroBoundaryValue U hd ω lam L hω v)) hf.symm)

/-- Constructing from a literal L² datum or its equivalence class gives the same graph. -/
theorem physicalZeroBoundaryResolventGraph_toLp {d : ℕ} (U : Set (Vec d)) (hd : 2 ≤ d)
    (ω : FieldPair d) (lam L α : ℝ) (hL : 1 ≤ L) (hω : IsRegular L ω) (hα : 0 < α)
    (f : Vec d → ℝ) (hf : MemLp f 2 (physicalReversibleMeasure ω hd lam)) :
    physicalZeroBoundaryResolventGraph U hd ω lam L α hL hω hα (hf.toLp f) =
      physicalZeroBoundaryResolvent U hd ω lam L α hL hω hα f hf := by
  apply (physicalZeroBoundaryResolvent_existsUnique U hd ω lam L α hL hω hα f hf).unique
  · apply (hasPhysicalZeroBoundaryResolvent_iff_bilinear U hd ω lam L α hL hω hα f hf _).mpr
    exact physicalZeroBoundaryResolventGraph_bilinear U hd ω lam L α hL hω hα (hf.toLp f)
  · exact physicalZeroBoundaryResolvent_spec U hd ω lam L α hL hω hα f hf

/-- Changing the datum on a physical null set leaves the constructed solution unchanged. -/
theorem physicalZeroBoundaryResolvent_congr_ae {d : ℕ} (U : Set (Vec d)) (hd : 2 ≤ d)
    (ω : FieldPair d) (lam L α : ℝ) (hL : 1 ≤ L) (hω : IsRegular L ω) (hα : 0 < α)
    (f g : Vec d → ℝ) (hf : MemLp f 2 (physicalReversibleMeasure ω hd lam))
    (hg : MemLp g 2 (physicalReversibleMeasure ω hd lam))
    (hfg : f =ᵐ[physicalReversibleMeasure ω hd lam] g) :
    physicalZeroBoundaryResolvent U hd ω lam L α hL hω hα f hf =
      physicalZeroBoundaryResolvent U hd ω lam L α hL hω hα g hg := by
  rw [← physicalZeroBoundaryResolventGraph_toLp U hd ω lam L α hL hω hα f hf,
    ← physicalZeroBoundaryResolventGraph_toLp U hd ω lam L α hL hω hα g hg]
  congr 1
  apply Lp.ext
  exact hf.coeFn_toLp.trans (hfg.trans hg.coeFn_toLp.symm)

/-- The actual physical L² zero-boundary resolvent, obtained by taking the value of the
unique solution graph. This definition does not identify a killed stochastic process. -/
def physicalZeroBoundaryResolventL2 {d : ℕ} (U : Set (Vec d)) (hd : 2 ≤ d)
    (ω : FieldPair d) (lam L α : ℝ) (hL : 1 ≤ L) (hω : IsRegular L ω) (hα : 0 < α) :
    Lp ℝ 2 (physicalReversibleMeasure ω hd lam) →L[ℝ]
      Lp ℝ 2 (physicalReversibleMeasure ω hd lam) :=
  (physicalZeroBoundaryValue U hd ω lam L hω).comp
    (physicalZeroBoundaryResolventGraph U hd ω lam L α hL hω hα)

/-- The L² resolvent retains the representative of its constructed weak solution. -/
theorem physicalZeroBoundaryResolventL2_ae_eq {d : ℕ} (U : Set (Vec d)) (hd : 2 ≤ d)
    (ω : FieldPair d) (lam L α : ℝ) (hL : 1 ≤ L) (hω : IsRegular L ω) (hα : 0 < α)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    physicalZeroBoundaryResolventL2 U hd ω lam L α hL hω hα f
      =ᵐ[physicalReversibleMeasure ω hd lam]
      densityWeightedH1SpaceValue
        (physicalZeroBoundaryResolventGraph U hd ω lam L α hL hω hα f).1 :=
  physicalZeroBoundaryValue_ae_eq U hd ω lam L hω _

private theorem physicalFormIntegral_nonneg {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam L : ℝ) (hL : 1 ≤ L) (hω : IsRegular L ω)
    (u : PhysicalH1Space hd lam) :
    0 ≤ ∫ x, weightedFormIntegrand ω.1 (physicalH1SpaceRepresentative hd lam u)
      (physicalH1SpaceRepresentative hd lam u) x ∂physicalReversibleMeasure ω hd lam := by
  apply integral_nonneg
  intro x
  apply mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hsq : 0 ≤ euclideanSq (WithLp.ofLp
      ((physicalH1SpaceRepresentative hd lam u).weakGradient x)) := by
    unfold euclideanSq dot
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  exact (mul_nonneg (inv_nonneg.mpr (zero_le_one.trans hL)) hsq).trans
    ((hω.1 x).2 _).1

private theorem physicalFormIntegral_symm {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam L : ℝ) (hω : IsRegular L ω) (u v : PhysicalH1Space hd lam) :
    (∫ x, weightedFormIntegrand ω.1 (physicalH1SpaceRepresentative hd lam u)
      (physicalH1SpaceRepresentative hd lam v) x ∂physicalReversibleMeasure ω hd lam) =
      ∫ x, weightedFormIntegrand ω.1 (physicalH1SpaceRepresentative hd lam v)
        (physicalH1SpaceRepresentative hd lam u) x ∂physicalReversibleMeasure ω hd lam := by
  apply integral_congr_ae
  filter_upwards [] with x
  apply congrArg ((1 / 2 : ℝ) * ·)
  change dotProduct _ ((ω.1 x).mulVec _) = dotProduct _ ((ω.1 x).mulVec _)
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, (hω.1 x).1, dotProduct_comm]

private theorem physicalZeroBoundaryBilinear_eq_inner {d : ℕ}
    (U : Set (Vec d)) (hd : 2 ≤ d) (ω : FieldPair d) (lam L α : ℝ)
    (hL : 1 ≤ L) (hω : IsRegular L ω) (hα : 0 < α)
    (u v : physicalH1ZeroBoundary U hd lam) :
    physicalZeroBoundaryBilinear U hd ω lam L α hL hω hα u v =
      α * inner ℝ (physicalZeroBoundaryValue U hd ω lam L hω u)
        (physicalZeroBoundaryValue U hd ω lam L hω v) +
      ∫ x, weightedFormIntegrand ω.1 (physicalH1SpaceRepresentative hd lam u.1)
        (physicalH1SpaceRepresentative hd lam v.1) x ∂physicalReversibleMeasure ω hd lam := by
  exact (physicalZeroBoundaryBilinear_apply_coe U hd ω lam L α hL hω hα u v).trans
    ((sourcePhysicalResolventBilinear_apply hd ω lam L α hL hω hα u.1 v.1).trans
      (congrArg (_ + ·)
        (sourcePhysicalDirichletForm_eq_physical_integral hd ω lam L hω u.1 v.1)))

private theorem physicalZeroBoundaryBilinear_symm {d : ℕ}
    (U : Set (Vec d)) (hd : 2 ≤ d) (ω : FieldPair d) (lam L α : ℝ)
    (hL : 1 ≤ L) (hω : IsRegular L ω) (hα : 0 < α)
    (u v : physicalH1ZeroBoundary U hd lam) :
    physicalZeroBoundaryBilinear U hd ω lam L α hL hω hα u v =
      physicalZeroBoundaryBilinear U hd ω lam L α hL hω hα v u := by
  exact (physicalZeroBoundaryBilinear_eq_inner U hd ω lam L α hL hω hα u v).trans
    ((congrArg₂ (· + ·) (congrArg (α * ·) (real_inner_comm _ _))
      (physicalFormIntegral_symm hd ω lam L hω u.1 v.1)).trans
        (physicalZeroBoundaryBilinear_eq_inner U hd ω lam L α hL hω hα v u).symm)

private theorem physicalZeroBoundaryBilinear_mass_le {d : ℕ}
    (U : Set (Vec d)) (hd : 2 ≤ d) (ω : FieldPair d) (lam L α : ℝ)
    (hL : 1 ≤ L) (hω : IsRegular L ω) (hα : 0 < α)
    (u : physicalH1ZeroBoundary U hd lam) :
    α * ‖physicalZeroBoundaryValue U hd ω lam L hω u‖ ^ 2 ≤
      physicalZeroBoundaryBilinear U hd ω lam L α hL hω hα u u := by
  have hmass := congrArg (α * ·)
    (real_inner_self_eq_norm_sq (physicalZeroBoundaryValue U hd ω lam L hω u)).symm
  exact hmass.le.trans
    ((le_add_of_nonneg_right (physicalFormIntegral_nonneg hd ω lam L hL hω u.1)).trans
      (physicalZeroBoundaryBilinear_eq_inner U hd ω lam L α hL hω hα u u).symm.le)

private theorem norm_le_inv_mul_of_mass_bound {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (α : ℝ) (hα : 0 < α) (f u : H)
    (h : α * ‖u‖ ^ 2 ≤ inner ℝ f u) : ‖u‖ ≤ α⁻¹ * ‖f‖ := by
  by_cases hu : ‖u‖ = 0
  · rw [hu]
    exact mul_nonneg (inv_nonneg.mpr hα.le) (norm_nonneg _)
  have hu0 : 0 < ‖u‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hu)
  have hm : (α * ‖u‖) * ‖u‖ ≤ ‖f‖ * ‖u‖ := by
    simpa only [pow_two, mul_assoc] using h.trans (real_inner_le_norm f u)
  have hbound : α * ‖u‖ ≤ ‖f‖ := (mul_le_mul_iff_left₀ hu0).mp hm
  rw [← div_eq_inv_mul]
  exact (le_div_iff₀ hα).mpr (by simpa only [mul_comm] using hbound)

/-- The resolvent has the exact physical L² bound α⁻¹, independent of the domain,
the regularity constant and the signed force. -/
theorem physicalZeroBoundaryResolventL2_norm_le {d : ℕ} (U : Set (Vec d)) (hd : 2 ≤ d)
    (ω : FieldPair d) (lam L α : ℝ) (hL : 1 ≤ L) (hω : IsRegular L ω) (hα : 0 < α)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    ‖physicalZeroBoundaryResolventL2 U hd ω lam L α hL hω hα f‖ ≤ α⁻¹ * ‖f‖ := by
  apply norm_le_inv_mul_of_mass_bound α hα f
  exact (physicalZeroBoundaryBilinear_mass_le U hd ω lam L α hL hω hα _).trans
    (le_of_eq (physicalZeroBoundaryResolventGraph_bilinear U hd ω lam L α hL hω hα f _))

/-- Operator-norm form of the physical L² contraction bound. -/
theorem physicalZeroBoundaryResolventL2_opNorm_le {d : ℕ}
    (U : Set (Vec d)) (hd : 2 ≤ d) (ω : FieldPair d) (lam L α : ℝ)
    (hL : 1 ≤ L) (hω : IsRegular L ω) (hα : 0 < α) :
    ‖physicalZeroBoundaryResolventL2 U hd ω lam L α hL hω hα‖ ≤ α⁻¹ := by
  exact (physicalZeroBoundaryResolventL2 U hd ω lam L α hL hω hα).opNorm_le_bound
    (inv_nonneg.mpr hα.le)
    (physicalZeroBoundaryResolventL2_norm_le U hd ω lam L α hL hω hα)

/-- Symmetry of the physical coefficient gives symmetry of the actual L² resolvent. -/
theorem physicalZeroBoundaryResolventL2_inner_symm {d : ℕ}
    (U : Set (Vec d)) (hd : 2 ≤ d) (ω : FieldPair d) (lam L α : ℝ)
    (hL : 1 ≤ L) (hω : IsRegular L ω) (hα : 0 < α)
    (f g : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    inner ℝ (physicalZeroBoundaryResolventL2 U hd ω lam L α hL hω hα f) g =
      inner ℝ f (physicalZeroBoundaryResolventL2 U hd ω lam L α hL hω hα g) := by
  let S := physicalZeroBoundaryResolventGraph U hd ω lam L α hL hω hα
  let J := physicalZeroBoundaryValue U hd ω lam L hω
  change inner ℝ (J (S f)) g = inner ℝ f (J (S g))
  exact (real_inner_comm _ _).trans
    ((physicalZeroBoundaryResolventGraph_bilinear U hd ω lam L α hL hω hα g (S f)).symm.trans
      ((physicalZeroBoundaryBilinear_symm U hd ω lam L α hL hω hα (S g) (S f)).trans
        (physicalZeroBoundaryResolventGraph_bilinear U hd ω lam L α hL hω hα f (S g))))

/-- The physical L² resolvent is self-adjoint. -/
theorem physicalZeroBoundaryResolventL2_isSelfAdjoint {d : ℕ}
    (U : Set (Vec d)) (hd : 2 ≤ d) (ω : FieldPair d) (lam L α : ℝ)
    (hL : 1 ≤ L) (hω : IsRegular L ω) (hα : 0 < α) :
    IsSelfAdjoint (physicalZeroBoundaryResolventL2 U hd ω lam L α hL hω hα) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  exact physicalZeroBoundaryResolventL2_inner_symm U hd ω lam L α hL hω hα

/-- The physical L² output vanishes almost everywhere outside the region. -/
theorem physicalZeroBoundaryResolventL2_zero_off {d : ℕ}
    (U : Set (Vec d)) (hd : 2 ≤ d) (ω : FieldPair d) (lam L α : ℝ)
    (hL : 1 ≤ L) (hω : IsRegular L ω) (hα : 0 < α)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    ∀ᵐ x ∂physicalReversibleMeasure ω hd lam,
      x ∉ U → physicalZeroBoundaryResolventL2 U hd ω lam L α hL hω hα f x = 0 := by
  let u := physicalZeroBoundaryResolventGraph U hd ω lam L α hL hω hα f
  have hzero : ∀ᵐ x ∂physicalReversibleMeasure ω hd lam,
      x ∉ U → densityWeightedH1SpaceValue u.1 x = 0 :=
    (withDensity_absolutelyContinuous _ _).ae_le
      (physicalH1ZeroBoundary_value_zero_off U hd lam u.1 u.2)
  filter_upwards [physicalZeroBoundaryResolventL2_ae_eq U hd ω lam L α hL hω hα f,
    hzero] with x hx hz hxU
  exact hx.trans (hz hxU)

/-- The resolvent is nonnegative as a quadratic form on the actual physical L² space. -/
theorem physicalZeroBoundaryResolventL2_inner_nonneg {d : ℕ}
    (U : Set (Vec d)) (hd : 2 ≤ d) (ω : FieldPair d) (lam L α : ℝ)
    (hL : 1 ≤ L) (hω : IsRegular L ω) (hα : 0 < α)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    0 ≤ inner ℝ f (physicalZeroBoundaryResolventL2 U hd ω lam L α hL hω hα f) := by
  have hmass := physicalZeroBoundaryBilinear_mass_le U hd ω lam L α hL hω hα
    (physicalZeroBoundaryResolventGraph U hd ω lam L α hL hω hα f)
  exact (mul_nonneg hα.le (sq_nonneg _)).trans
    (hmass.trans (physicalZeroBoundaryResolventGraph_bilinear
      U hd ω lam L α hL hω hα f _).le)

private theorem variationalResolventGraph_unique {V H : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [CompleteSpace V] [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (B : V →L[ℝ] V →L[ℝ] ℝ)
    (hB : IsCoercive B) (J : V →L[ℝ] H) (f : H) (u : V)
    (hu : ∀ v, B u v = inner ℝ f (J v)) : u = variationalResolventGraph B hB J f := by
  apply hB.continuousLinearEquivOfBilin.injective
  apply ext_inner_right ℝ
  intro v
  exact (hB.continuousLinearEquivOfBilin_apply u v).trans
    ((hu v).trans ((variationalResolventGraph_spec B hB J f v).symm.trans
      (hB.continuousLinearEquivOfBilin_apply _ v).symm))

private theorem variationalResolventGraph_identity {V H : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [CompleteSpace V] [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (B C : V →L[ℝ] V →L[ℝ] ℝ)
    (hB : IsCoercive B) (hC : IsCoercive C) (J : V →L[ℝ] H) (a : ℝ)
    (hBC : ∀ u v, B u v = C u v - a * inner ℝ (J u) (J v)) (f : H) :
    variationalResolventGraph B hB J f - variationalResolventGraph C hC J f =
      a • variationalResolventGraph B hB J (J (variationalResolventGraph C hC J f)) := by
  let u := variationalResolventGraph C hC J f
  let w := variationalResolventGraph B hB J (J u)
  have hsolve : ∀ v, B (u + a • w) v = inner ℝ f (J v) := by
    intro v
    rw [map_add, map_smul]
    change B u v + a * B w v = _
    rw [hBC u v, variationalResolventGraph_spec C hC J f v,
      variationalResolventGraph_spec B hB J (J u) v]
    ring
  have heq := variationalResolventGraph_unique B hB J f (u + a • w) hsolve
  change _ - u = a • w
  exact sub_eq_iff_eq_add.mpr (heq.symm.trans (add_comm _ _))

private theorem scalarResolvent_mass_shift (α β m e : ℝ) :
    α * m + e = β * m + e - (β - α) * m := by ring

private theorem physicalZeroBoundaryBilinear_mass_shift {d : ℕ}
    (U : Set (Vec d)) (hd : 2 ≤ d) (ω : FieldPair d) (lam L α β : ℝ)
    (hL : 1 ≤ L) (hω : IsRegular L ω) (hα : 0 < α) (hβ : 0 < β)
    (u v : physicalH1ZeroBoundary U hd lam) :
    physicalZeroBoundaryBilinear U hd ω lam L α hL hω hα u v =
      physicalZeroBoundaryBilinear U hd ω lam L β hL hω hβ u v -
        (β - α) * inner ℝ (physicalZeroBoundaryValue U hd ω lam L hω u)
          (physicalZeroBoundaryValue U hd ω lam L hω v) := by
  exact (physicalZeroBoundaryBilinear_eq_inner U hd ω lam L α hL hω hα u v).trans
    ((scalarResolvent_mass_shift α β _ _).trans
      (congrArg (· - _) (physicalZeroBoundaryBilinear_eq_inner
        U hd ω lam L β hL hω hβ u v).symm))

/-- The constructed physical L² operators satisfy the resolvent identity for every
pair of positive rates on the same actual zero-boundary domain. -/
theorem physicalZeroBoundaryResolventL2_identity {d : ℕ}
    (U : Set (Vec d)) (hd : 2 ≤ d) (ω : FieldPair d) (lam L α β : ℝ)
    (hL : 1 ≤ L) (hω : IsRegular L ω) (hα : 0 < α) (hβ : 0 < β)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    physicalZeroBoundaryResolventL2 U hd ω lam L α hL hω hα f -
        physicalZeroBoundaryResolventL2 U hd ω lam L β hL hω hβ f =
      (β - α) • physicalZeroBoundaryResolventL2 U hd ω lam L α hL hω hα
        (physicalZeroBoundaryResolventL2 U hd ω lam L β hL hω hβ f) := by
  let J := physicalZeroBoundaryValue U hd ω lam L hω
  have hgraph := variationalResolventGraph_identity
    (V := physicalH1ZeroBoundary U hd lam)
    (H := Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (physicalZeroBoundaryBilinear U hd ω lam L α hL hω hα)
    (physicalZeroBoundaryBilinear U hd ω lam L β hL hω hβ)
    (physicalZeroBoundaryBilinear_isCoercive U hd ω lam L α hL hω hα)
    (physicalZeroBoundaryBilinear_isCoercive U hd ω lam L β hL hω hβ) J (β - α)
    (physicalZeroBoundaryBilinear_mass_shift U hd ω lam L α β hL hω hα hβ) f
  exact (J.map_sub _ _).symm.trans
    ((congrArg J hgraph).trans (J.map_smul (β - α) _))

/-- Local coefficient agreement gives equality of the two physical L² resolvent values
as Lebesgue-a.e. functions, even though their physical L² carriers use different measures. -/
theorem physicalZeroBoundaryResolventL2_eq_of_physical_eqOn {d : ℕ}
    (U : Set (Vec d)) (hU : MeasurableSet U) (hd : 2 ≤ d) (ω ω' : FieldPair d)
    (heq : ∀ y ∈ U, ω.1 y = ω'.1 y ∧ ω.2 y = ω'.2 y)
    (lam L L' α : ℝ) (hL : 1 ≤ L) (hL' : 1 ≤ L')
    (hω : IsRegular L ω) (hω' : IsRegular L' ω') (hα : 0 < α) (f : Vec d → ℝ)
    (hf : MemLp f 2 (physicalReversibleMeasure ω hd lam))
    (hf' : MemLp f 2 (physicalReversibleMeasure ω' hd lam)) :
    physicalZeroBoundaryResolventL2 U hd ω lam L α hL hω hα (hf.toLp f)
      =ᵐ[(volume : Measure (Vec d))]
      physicalZeroBoundaryResolventL2 U hd ω' lam L' α hL' hω' hα (hf'.toLp f) := by
  have hgraph := (physicalZeroBoundaryResolventGraph_toLp U hd ω lam L α hL hω hα f hf).trans
    ((physicalZeroBoundaryResolvent_eq_of_physical_eqOn
      U hU hd ω ω' heq lam L L' α hL hL' hω hω' hα f hf hf').trans
        (physicalZeroBoundaryResolventGraph_toLp U hd ω' lam L' α hL' hω' hα f hf').symm)
  have hleft := (ae_withDensity_iff_volume_of_continuous_pos
    (physicalReversibleDensity ω hd lam) (physicalReversibleDensity_continuous ω hd lam)
    (physicalReversibleDensity_pos ω hd lam) _).mp
      (physicalZeroBoundaryResolventL2_ae_eq U hd ω lam L α hL hω hα (hf.toLp f))
  have hright := (ae_withDensity_iff_volume_of_continuous_pos
    (physicalReversibleDensity ω' hd lam) (physicalReversibleDensity_continuous ω' hd lam)
    (physicalReversibleDensity_pos ω' hd lam) _).mp
      (physicalZeroBoundaryResolventL2_ae_eq U hd ω' lam L' α hL' hω' hα (hf'.toLp f))
  filter_upwards [hleft, hright] with x hx hy
  exact hx.trans ((congrArg (fun u : physicalH1ZeroBoundary U hd lam =>
    densityWeightedH1SpaceValue u.1 x) hgraph).trans hy.symm)

private theorem variationalResolvent_closure_range {V H : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [CompleteSpace V] [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (B : V →L[ℝ] V →L[ℝ] ℝ)
    (hB : IsCoercive B) (J : V →L[ℝ] H) :
    (LinearMap.range (J.comp (variationalResolventGraph B hB J)).toLinearMap).topologicalClosure =
      (LinearMap.range J.toLinearMap).topologicalClosure := by
  let S := variationalResolventGraph B hB J
  have horth : (LinearMap.range (J.comp S).toLinearMap)ᗮ = (LinearMap.range J.toLinearMap)ᗮ := by
    ext f
    constructor
    · intro hf
      have hzero : B (S f) (S f) = 0 :=
        (variationalResolventGraph_spec B hB J f (S f)).trans
          ((real_inner_comm _ _).trans
            ((LinearMap.range (J.comp S).toLinearMap).mem_orthogonal f |>.mp hf
              (J (S f)) ⟨f, rfl⟩))
      have hsolve := variationalResolventGraph_spec B hB J f
      obtain ⟨C, hC, hc⟩ := hB
      have hnorm : ‖S f‖ = 0 := by
        have hb : C * (‖S f‖ * ‖S f‖) ≤ 0 := by
          simpa only [← mul_assoc, hzero] using hc (S f)
        have hsq : ‖S f‖ * ‖S f‖ ≤ 0 := (mul_le_mul_iff_right₀ hC).mp
          (by simpa only [mul_zero] using hb : C * (‖S f‖ * ‖S f‖) ≤ C * 0)
        nlinarith only [hsq, norm_nonneg (S f)]
      have hSf : S f = 0 := norm_eq_zero.mp hnorm
      apply (LinearMap.range J.toLinearMap).mem_orthogonal' f |>.mpr
      rintro _ ⟨v, rfl⟩
      have hs := hsolve v
      change B (S f) v = _ at hs
      have h0 := hs.symm
      simp only [hSf, map_zero, ContinuousLinearMap.zero_apply] at h0
      exact h0
    · intro hf
      apply (LinearMap.range (J.comp S).toLinearMap).mem_orthogonal f |>.mpr
      rintro _ ⟨g, rfl⟩
      exact (LinearMap.range J.toLinearMap).mem_orthogonal f |>.mp hf (J (S g)) ⟨S g, rfl⟩
  rw [← Submodule.orthogonal_orthogonal_eq_closure,
    ← Submodule.orthogonal_orthogonal_eq_closure, horth]

/-- The physical interior value space is the L² closure of values of the actual
zero-boundary H¹ domain. No identification with all exterior-zero L² data is assumed. -/
def physicalZeroBoundaryL2 {d : ℕ} (U : Set (Vec d)) (hd : 2 ≤ d)
    (ω : FieldPair d) (lam L : ℝ) (hω : IsRegular L ω) :
    Submodule ℝ (Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :=
  (LinearMap.range (physicalZeroBoundaryValue U hd ω lam L hω).toLinearMap).topologicalClosure

/-- The physical interior value space is closed. -/
theorem physicalZeroBoundaryL2_isClosed {d : ℕ} (U : Set (Vec d)) (hd : 2 ≤ d)
    (ω : FieldPair d) (lam L : ℝ) (hω : IsRegular L ω) :
    IsClosed (physicalZeroBoundaryL2 U hd ω lam L hω :
      Set (Lp ℝ 2 (physicalReversibleMeasure ω hd lam))) :=
  Submodule.isClosed_topologicalClosure _

/-- Actual zero-boundary graph values belong to the constructed interior value space. -/
theorem physicalZeroBoundaryValue_mem_L2 {d : ℕ} (U : Set (Vec d)) (hd : 2 ≤ d)
    (ω : FieldPair d) (lam L : ℝ) (hω : IsRegular L ω)
    (u : physicalH1ZeroBoundary U hd lam) :
    physicalZeroBoundaryValue U hd ω lam L hω u ∈ physicalZeroBoundaryL2 U hd ω lam L hω :=
  Submodule.le_topologicalClosure _ ⟨u, rfl⟩

/-- Every physical resolvent value lies in the interior value space. -/
theorem physicalZeroBoundaryResolventL2_mem {d : ℕ} (U : Set (Vec d)) (hd : 2 ≤ d)
    (ω : FieldPair d) (lam L α : ℝ) (hL : 1 ≤ L) (hω : IsRegular L ω) (hα : 0 < α)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    physicalZeroBoundaryResolventL2 U hd ω lam L α hL hω hα f ∈
      physicalZeroBoundaryL2 U hd ω lam L hω :=
  physicalZeroBoundaryValue_mem_L2 U hd ω lam L hω _

/-- At each positive rate, the actual resolvent range is dense in the constructed
interior value space. This follows from coercivity of the actual form. -/
theorem physicalZeroBoundaryResolventL2_closure_range {d : ℕ}
    (U : Set (Vec d)) (hd : 2 ≤ d) (ω : FieldPair d) (lam L α : ℝ)
    (hL : 1 ≤ L) (hω : IsRegular L ω) (hα : 0 < α) :
    (LinearMap.range
      (physicalZeroBoundaryResolventL2 U hd ω lam L α hL hω hα).toLinearMap).topologicalClosure =
      physicalZeroBoundaryL2 U hd ω lam L hω := by
  unfold physicalZeroBoundaryResolventL2 physicalZeroBoundaryL2 physicalZeroBoundaryResolventGraph
  exact variationalResolvent_closure_range
    (V := physicalH1ZeroBoundary U hd lam)
    (H := Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (physicalZeroBoundaryBilinear U hd ω lam L α hL hω hα)
    (physicalZeroBoundaryBilinear_isCoercive U hd ω lam L α hL hω hα)
    (physicalZeroBoundaryValue U hd ω lam L hω)

/-- Scaling a positive-rate physical resolvent by its rate gives a contraction. -/
theorem physicalZeroBoundaryResolventL2_smul_norm_le {d : ℕ}
    (U : Set (Vec d)) (hd : 2 ≤ d) (ω : FieldPair d) (lam L α : ℝ)
    (hL : 1 ≤ L) (hω : IsRegular L ω) (hα : 0 < α)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    ‖α • physicalZeroBoundaryResolventL2 U hd ω lam L α hL hω hα f‖ ≤ ‖f‖ := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hα]
  exact (mul_le_mul_of_nonneg_left
    (physicalZeroBoundaryResolventL2_norm_le U hd ω lam L α hL hω hα f) hα.le).trans
      (by rw [← mul_assoc, mul_inv_cancel₀ hα.ne', one_mul])

/-- Normalized physical zero-boundary resolvents at the positive integer rates. -/
def physicalZeroBoundaryResolventApproximation {d : ℕ}
    (U : Set (Vec d)) (hd : 2 ≤ d) (ω : FieldPair d) (lam L : ℝ)
    (hL : 1 ≤ L) (hω : IsRegular L ω) (n : ℕ) :
    Lp ℝ 2 (physicalReversibleMeasure ω hd lam) →L[ℝ]
      Lp ℝ 2 (physicalReversibleMeasure ω hd lam) :=
  ((n : ℝ) + 1) • physicalZeroBoundaryResolventL2 U hd ω lam L ((n : ℝ) + 1)
    hL hω (by positivity)

/-- Every normalized physical resolvent in the approximation sequence is a contraction. -/
theorem physicalZeroBoundaryResolventApproximation_norm_le {d : ℕ}
    (U : Set (Vec d)) (hd : 2 ≤ d) (ω : FieldPair d) (lam L : ℝ)
    (hL : 1 ≤ L) (hω : IsRegular L ω) (n : ℕ)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    ‖physicalZeroBoundaryResolventApproximation U hd ω lam L hL hω n f‖ ≤ ‖f‖ :=
  physicalZeroBoundaryResolventL2_smul_norm_le U hd ω lam L _ hL hω (by positivity) f

private theorem resolvent_error_on_range {H : Type*} [NormedAddCommGroup H]
    [NormedSpace ℝ H] (R S : H →L[ℝ] H) (α : ℝ) (f : H)
    (h : R f - S f = (1 - α) • R (S f)) :
    α • R (S f) - S f = R (S f - f) := by
  rw [map_sub, sub_eq_iff_eq_add.mp h]
  simp only [sub_smul, one_smul]
  abel

private theorem tendsto_physicalZeroBoundaryResolventApproximation_on_range {d : ℕ}
    (U : Set (Vec d)) (hd : 2 ≤ d) (ω : FieldPair d) (lam L : ℝ)
    (hL : 1 ≤ L) (hω : IsRegular L ω)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    Tendsto (fun n => physicalZeroBoundaryResolventApproximation U hd ω lam L hL hω n
      (physicalZeroBoundaryResolventL2 U hd ω lam L 1 hL hω zero_lt_one f)) atTop
      (𝓝 (physicalZeroBoundaryResolventL2 U hd ω lam L 1 hL hω zero_lt_one f)) := by
  let S := physicalZeroBoundaryResolventL2 U hd ω lam L 1 hL hω zero_lt_one
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hb (n : ℕ) :
      ‖physicalZeroBoundaryResolventApproximation U hd ω lam L hL hω n (S f) - S f‖ ≤
        ((n : ℝ) + 1)⁻¹ * ‖S f - f‖ := by
    have he := resolvent_error_on_range
      (physicalZeroBoundaryResolventL2 U hd ω lam L ((n : ℝ) + 1) hL hω (by positivity))
      S ((n : ℝ) + 1) f
      (physicalZeroBoundaryResolventL2_identity U hd ω lam L ((n : ℝ) + 1) 1 hL hω
        (by positivity) zero_lt_one f)
    exact (congrArg norm he).le.trans
      (physicalZeroBoundaryResolventL2_norm_le U hd ω lam L _ hL hω (by positivity) _)
  have hz : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹ * ‖S f - f‖) atTop (𝓝 0) := by
    simpa only [one_div, zero_mul] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const ‖S f - f‖
  exact squeeze_zero (fun _ => norm_nonneg _) hb hz

/-- The normalized physical resolvents converge strongly to the identity on the
constructed interior value space, without a density hypothesis or a process-identification premise. -/
theorem tendsto_physicalZeroBoundaryResolventApproximation {d : ℕ}
    (U : Set (Vec d)) (hd : 2 ≤ d) (ω : FieldPair d) (lam L : ℝ)
    (hL : 1 ≤ L) (hω : IsRegular L ω)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (hf : f ∈ physicalZeroBoundaryL2 U hd ω lam L hω) :
    Tendsto (fun n => physicalZeroBoundaryResolventApproximation U hd ω lam L hL hω n f)
      atTop (𝓝 f) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hclosure : f ∈ closure (LinearMap.range
      (physicalZeroBoundaryResolventL2 U hd ω lam L 1 hL hω zero_lt_one).toLinearMap :
        Set (Lp ℝ 2 (physicalReversibleMeasure ω hd lam))) := by
    change f ∈ (LinearMap.range
      (physicalZeroBoundaryResolventL2 U hd ω lam L 1 hL hω zero_lt_one).toLinearMap).topologicalClosure
    rw [physicalZeroBoundaryResolventL2_closure_range]
    exact hf
  obtain ⟨u, ⟨g, rfl⟩, hfu⟩ := Metric.mem_closure_iff.mp hclosure (ε / 3) (by positivity)
  let u := physicalZeroBoundaryResolventL2 U hd ω lam L 1 hL hω zero_lt_one g
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp
    (tendsto_physicalZeroBoundaryResolventApproximation_on_range U hd ω lam L hL hω g)
      (ε / 3) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have hc : dist (physicalZeroBoundaryResolventApproximation U hd ω lam L hL hω n f)
      (physicalZeroBoundaryResolventApproximation U hd ω lam L hL hω n u) ≤ dist f u := by
    rw [dist_eq_norm, dist_eq_norm, ← map_sub]
    exact physicalZeroBoundaryResolventApproximation_norm_le U hd ω lam L hL hω n (f - u)
  calc
    dist (physicalZeroBoundaryResolventApproximation U hd ω lam L hL hω n f) f ≤
        dist (physicalZeroBoundaryResolventApproximation U hd ω lam L hL hω n f)
          (physicalZeroBoundaryResolventApproximation U hd ω lam L hL hω n u) +
          dist (physicalZeroBoundaryResolventApproximation U hd ω lam L hL hω n u) f :=
      dist_triangle _ _ _
    _ ≤ dist f u + (dist (physicalZeroBoundaryResolventApproximation U hd ω lam L hL hω n u) u +
        dist u f) := add_le_add hc (dist_triangle _ _ _)
    _ < ε := by
      have hnu : dist (physicalZeroBoundaryResolventApproximation U hd ω lam L hL hω n u) u <
          ε / 3 := hN n hn
      have hfu' : dist f u < ε / 3 := hfu
      rw [dist_comm u f]
      linarith only [hfu', hnu]

/-- Actual physical resolvents at any two positive rates commute. -/
theorem physicalZeroBoundaryResolventL2_commute {d : ℕ}
    (U : Set (Vec d)) (hd : 2 ≤ d) (ω : FieldPair d) (lam L α β : ℝ)
    (hL : 1 ≤ L) (hω : IsRegular L ω) (hα : 0 < α) (hβ : 0 < β) :
    Commute (physicalZeroBoundaryResolventL2 U hd ω lam L α hL hω hα)
      (physicalZeroBoundaryResolventL2 U hd ω lam L β hL hω hβ) := by
  by_cases he : α = β
  · subst β
    exact Commute.refl _
  · apply ContinuousLinearMap.ext
    intro f
    have hαβ := physicalZeroBoundaryResolventL2_identity U hd ω lam L α β hL hω hα hβ f
    have hβα := physicalZeroBoundaryResolventL2_identity U hd ω lam L β α hL hω hβ hα f
    apply smul_right_injective (Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
      (sub_ne_zero.mpr (Ne.symm he))
    change (β - α) • physicalZeroBoundaryResolventL2 U hd ω lam L α hL hω hα
      (physicalZeroBoundaryResolventL2 U hd ω lam L β hL hω hβ f) =
      (β - α) • physicalZeroBoundaryResolventL2 U hd ω lam L β hL hω hβ
        (physicalZeroBoundaryResolventL2 U hd ω lam L α hL hω hα f)
    rw [← hαβ]
    have hneg : β - α = -(α - β) := by ring
    rw [hneg, neg_smul, ← hβα, neg_sub]

/-- The bounded Yosida operator formed from the actual normalized physical resolvent. -/
def physicalZeroBoundaryYosida {d : ℕ} (U : Set (Vec d)) (hd : 2 ≤ d)
    (ω : FieldPair d) (lam L : ℝ) (hL : 1 ≤ L) (hω : IsRegular L ω) (n : ℕ) :
    Lp ℝ 2 (physicalReversibleMeasure ω hd lam) →L[ℝ]
      Lp ℝ 2 (physicalReversibleMeasure ω hd lam) :=
  ((n : ℝ) + 1) • (physicalZeroBoundaryResolventApproximation U hd ω lam L hL hω n -
    ContinuousLinearMap.id ℝ _)

/-- Each bounded physical Yosida operator is dissipative on the actual physical L² space. -/
theorem physicalZeroBoundaryYosida_inner_nonpos {d : ℕ}
    (U : Set (Vec d)) (hd : 2 ≤ d) (ω : FieldPair d) (lam L : ℝ)
    (hL : 1 ≤ L) (hω : IsRegular L ω) (n : ℕ)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    inner ℝ f (physicalZeroBoundaryYosida U hd ω lam L hL hω n f) ≤ 0 := by
  have hc := physicalZeroBoundaryResolventApproximation_norm_le U hd ω lam L hL hω n f
  have hh : inner ℝ f (physicalZeroBoundaryResolventApproximation U hd ω lam L hL hω n f) ≤
      ‖f‖ ^ 2 := by
    calc
      _ ≤ ‖f‖ * ‖physicalZeroBoundaryResolventApproximation U hd ω lam L hL hω n f‖ :=
        real_inner_le_norm _ _
      _ ≤ ‖f‖ * ‖f‖ := mul_le_mul_of_nonneg_left hc (norm_nonneg f)
      _ = ‖f‖ ^ 2 := (pow_two _).symm
  change inner ℝ f (((n : ℝ) + 1) •
    (physicalZeroBoundaryResolventApproximation U hd ω lam L hL hω n f - f)) ≤ 0
  rw [real_inner_smul_right, inner_sub_right, real_inner_self_eq_norm_sq]
  exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (sub_nonpos.mpr hh)

/-- The actual bounded Yosida operators preserve the constructed interior value space. -/
theorem physicalZeroBoundaryYosida_mem {d : ℕ}
    (U : Set (Vec d)) (hd : 2 ≤ d) (ω : FieldPair d) (lam L : ℝ)
    (hL : 1 ≤ L) (hω : IsRegular L ω) (n : ℕ)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (hf : f ∈ physicalZeroBoundaryL2 U hd ω lam L hω) :
    physicalZeroBoundaryYosida U hd ω lam L hL hω n f ∈
      physicalZeroBoundaryL2 U hd ω lam L hω := by
  let H := physicalZeroBoundaryL2 U hd ω lam L hω
  exact H.smul_mem _ (H.sub_mem (H.smul_mem _
    (physicalZeroBoundaryResolventL2_mem U hd ω lam L _ hL hω (by positivity) f)) hf)

private theorem commute_yosida_of_commute {A : Type*} [Ring A] [Algebra ℝ A]
    (a b : A) (hab : Commute a b) (r s : ℝ) :
    Commute (r • (r • a - 1)) (s • (s • b - 1)) := by
  have hA := (hab.smul_left r).smul_right s
  have hB := (hA.sub_right (Commute.one_right _)).sub_left
    ((Commute.one_left _).sub_right (Commute.refl 1))
  exact (hB.smul_left r).smul_right s

/-- The physical bounded Yosida generators commute at every two indices. -/
theorem physicalZeroBoundaryYosida_commute {d : ℕ}
    (U : Set (Vec d)) (hd : 2 ≤ d) (ω : FieldPair d) (lam L : ℝ)
    (hL : 1 ≤ L) (hω : IsRegular L ω) (n m : ℕ) :
    Commute (physicalZeroBoundaryYosida U hd ω lam L hL hω n)
      (physicalZeroBoundaryYosida U hd ω lam L hL hω m) := by
  have hR := physicalZeroBoundaryResolventL2_commute U hd ω lam L
    ((n : ℝ) + 1) ((m : ℝ) + 1) hL hω (by positivity) (by positivity)
  exact commute_yosida_of_commute _ _ hR ((n : ℝ) + 1) ((m : ℝ) + 1)

/-- On the positive unit-rate resolvent range, a Yosida value is the normalized
resolvent of the actual candidate generator value. -/
theorem physicalZeroBoundaryYosida_on_resolvent {d : ℕ}
    (U : Set (Vec d)) (hd : 2 ≤ d) (ω : FieldPair d) (lam L : ℝ)
    (hL : 1 ≤ L) (hω : IsRegular L ω) (n : ℕ)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    physicalZeroBoundaryYosida U hd ω lam L hL hω n
      (physicalZeroBoundaryResolventL2 U hd ω lam L 1 hL hω zero_lt_one f) =
      physicalZeroBoundaryResolventApproximation U hd ω lam L hL hω n
        (physicalZeroBoundaryResolventL2 U hd ω lam L 1 hL hω zero_lt_one f - f) := by
  have he := resolvent_error_on_range
    (physicalZeroBoundaryResolventL2 U hd ω lam L ((n : ℝ) + 1) hL hω (by positivity))
    (physicalZeroBoundaryResolventL2 U hd ω lam L 1 hL hω zero_lt_one) ((n : ℝ) + 1) f
    (physicalZeroBoundaryResolventL2_identity U hd ω lam L ((n : ℝ) + 1) 1 hL hω
      (by positivity) zero_lt_one f)
  exact congrArg (((n : ℝ) + 1) • ·) he

/-- The actual bounded Yosida values converge strongly on unit-rate resolvent
values whose data lie in the interior space. -/
theorem tendsto_physicalZeroBoundaryYosida_on_resolvent {d : ℕ}
    (U : Set (Vec d)) (hd : 2 ≤ d) (ω : FieldPair d) (lam L : ℝ)
    (hL : 1 ≤ L) (hω : IsRegular L ω)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (hf : f ∈ physicalZeroBoundaryL2 U hd ω lam L hω) :
    Tendsto (fun n => physicalZeroBoundaryYosida U hd ω lam L hL hω n
      (physicalZeroBoundaryResolventL2 U hd ω lam L 1 hL hω zero_lt_one f)) atTop
      (𝓝 (physicalZeroBoundaryResolventL2 U hd ω lam L 1 hL hω zero_lt_one f - f)) := by
  simp_rw [physicalZeroBoundaryYosida_on_resolvent]
  exact tendsto_physicalZeroBoundaryResolventApproximation U hd ω lam L hL hω _
    ((physicalZeroBoundaryL2 U hd ω lam L hω).sub_mem
      (physicalZeroBoundaryResolventL2_mem U hd ω lam L 1 hL hω zero_lt_one f) hf)

/-- The constructed interior value space is itself a complete physical L² space. -/
instance physicalZeroBoundaryL2_completeSpace {d : ℕ} (U : Set (Vec d)) (hd : 2 ≤ d)
    (ω : FieldPair d) (lam L : ℝ) (hω : IsRegular L ω) :
    CompleteSpace (physicalZeroBoundaryL2 U hd ω lam L hω) :=
  (physicalZeroBoundaryL2_isClosed U hd ω lam L hω).completeSpace_coe

private theorem variationalResolvent_zero_of_forcing_zero {V H : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B) (J : V →L[ℝ] H)
    (f : H) (hf : ∀ v, inner ℝ f (J v) = 0) :
    J (variationalResolventGraph B hB J f) = 0 := by
  have hz : (0 : V) = variationalResolventGraph B hB J f :=
    variationalResolventGraph_unique B hB J f 0 (fun v => by
      simpa only [map_zero, ContinuousLinearMap.zero_apply] using (hf v).symm)
  exact (congrArg J hz.symm).trans J.map_zero

/-- Physical resolvents annihilate the orthogonal complement of the interior value space. -/
theorem physicalZeroBoundaryResolventL2_eq_zero_of_orthogonal {d : ℕ}
    (U : Set (Vec d)) (hd : 2 ≤ d) (ω : FieldPair d) (lam L α : ℝ)
    (hL : 1 ≤ L) (hω : IsRegular L ω) (hα : 0 < α)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (hf : f ∈ (physicalZeroBoundaryL2 U hd ω lam L hω)ᗮ) :
    physicalZeroBoundaryResolventL2 U hd ω lam L α hL hω hα f = 0 := by
  apply variationalResolvent_zero_of_forcing_zero
    (physicalZeroBoundaryBilinear U hd ω lam L α hL hω hα)
    (physicalZeroBoundaryBilinear_isCoercive U hd ω lam L α hL hω hα)
    (physicalZeroBoundaryValue U hd ω lam L hω) f
  intro v
  exact (physicalZeroBoundaryL2 U hd ω lam L hω).mem_orthogonal' f |>.mp hf
    _ (physicalZeroBoundaryValue_mem_L2 U hd ω lam L hω v)

/-- Orthogonal projection onto the actual closed interior value space. -/
def physicalZeroBoundaryProjection {d : ℕ} (U : Set (Vec d)) (hd : 2 ≤ d)
    (ω : FieldPair d) (lam L : ℝ) (hω : IsRegular L ω) :
    Lp ℝ 2 (physicalReversibleMeasure ω hd lam) →L[ℝ]
      Lp ℝ 2 (physicalReversibleMeasure ω hd lam) :=
  (physicalZeroBoundaryL2 U hd ω lam L hω).starProjection

/-- The projection takes values in the constructed interior value space. -/
theorem physicalZeroBoundaryProjection_mem {d : ℕ} (U : Set (Vec d)) (hd : 2 ≤ d)
    (ω : FieldPair d) (lam L : ℝ) (hω : IsRegular L ω)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    physicalZeroBoundaryProjection U hd ω lam L hω f ∈ physicalZeroBoundaryL2 U hd ω lam L hω :=
  Submodule.starProjection_apply_mem _ _

/-- A physical resolvent depends only on the interior orthogonal projection of its datum. -/
theorem physicalZeroBoundaryResolventL2_projection {d : ℕ}
    (U : Set (Vec d)) (hd : 2 ≤ d) (ω : FieldPair d) (lam L α : ℝ)
    (hL : 1 ≤ L) (hω : IsRegular L ω) (hα : 0 < α)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    physicalZeroBoundaryResolventL2 U hd ω lam L α hL hω hα
      (physicalZeroBoundaryProjection U hd ω lam L hω f) =
      physicalZeroBoundaryResolventL2 U hd ω lam L α hL hω hα f := by
  have hz := physicalZeroBoundaryResolventL2_eq_zero_of_orthogonal U hd ω lam L α hL hω hα
    (f - physicalZeroBoundaryProjection U hd ω lam L hω f)
    ((physicalZeroBoundaryL2 U hd ω lam L hω).sub_starProjection_mem_orthogonal f)
  rw [map_sub, sub_eq_zero] at hz
  exact hz.symm

/-- On all ambient physical L² data the normalized resolvents converge strongly to
orthogonal projection onto the interior value space. -/
theorem tendsto_physicalZeroBoundaryResolventApproximation_projection {d : ℕ}
    (U : Set (Vec d)) (hd : 2 ≤ d) (ω : FieldPair d) (lam L : ℝ)
    (hL : 1 ≤ L) (hω : IsRegular L ω)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    Tendsto (fun n => physicalZeroBoundaryResolventApproximation U hd ω lam L hL hω n f)
      atTop (𝓝 (physicalZeroBoundaryProjection U hd ω lam L hω f)) := by
  have he (n : ℕ) : physicalZeroBoundaryResolventApproximation U hd ω lam L hL hω n f =
      physicalZeroBoundaryResolventApproximation U hd ω lam L hL hω n
        (physicalZeroBoundaryProjection U hd ω lam L hω f) :=
    congrArg (((n : ℝ) + 1) • ·)
      (physicalZeroBoundaryResolventL2_projection U hd ω lam L _ hL hω (by positivity) f).symm
  simp_rw [he]
  exact tendsto_physicalZeroBoundaryResolventApproximation U hd ω lam L hL hω _
    (physicalZeroBoundaryProjection_mem U hd ω lam L hω f)

/-- For arbitrary ambient data, the Yosida values on a unit-rate resolvent converge
to the resolvent value minus the interior projection of the datum. -/
theorem tendsto_physicalZeroBoundaryYosida_on_resolvent_projection {d : ℕ}
    (U : Set (Vec d)) (hd : 2 ≤ d) (ω : FieldPair d) (lam L : ℝ)
    (hL : 1 ≤ L) (hω : IsRegular L ω)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    Tendsto (fun n => physicalZeroBoundaryYosida U hd ω lam L hL hω n
      (physicalZeroBoundaryResolventL2 U hd ω lam L 1 hL hω zero_lt_one f)) atTop
      (𝓝 (physicalZeroBoundaryResolventL2 U hd ω lam L 1 hL hω zero_lt_one f -
        physicalZeroBoundaryProjection U hd ω lam L hω f)) := by
  have h := tendsto_physicalZeroBoundaryYosida_on_resolvent U hd ω lam L hL hω
    (physicalZeroBoundaryProjection U hd ω lam L hω f)
    (physicalZeroBoundaryProjection_mem U hd ω lam L hω f)
  simpa only [physicalZeroBoundaryResolventL2_projection] using h


-- (v4.35 port: the former private cache instances for the interior value space are removed,
-- as above.)

private theorem commute_real_smul {A : Type*} [Ring A] [Algebra ℝ A]
    {a b : A} (h : Commute a b) (r s : ℝ) : Commute (r • a) (s • b) :=
  (h.smul_left r).smul_right s

private theorem commute_real_smul_right {A : Type*} [Ring A] [Algebra ℝ A]
    {a b : A} (h : Commute a b) (s : ℝ) : Commute a (s • b) := h.smul_right s

/-- The actual physical Yosida operator restricted to the constructed interior L² space. -/
def physicalZeroBoundaryPartYosida {d : ℕ} (U : Set (Vec d)) (hd : 2 ≤ d)
    (ω : FieldPair d) (lam L : ℝ) (hL : 1 ≤ L) (hω : IsRegular L ω) (n : ℕ) :
    physicalZeroBoundaryL2 U hd ω lam L hω →L[ℝ] physicalZeroBoundaryL2 U hd ω lam L hω :=
  ((physicalZeroBoundaryYosida U hd ω lam L hL hω n).comp
    (physicalZeroBoundaryL2 U hd ω lam L hω).subtypeL).codRestrict _
      (fun f => physicalZeroBoundaryYosida_mem U hd ω lam L hL hω n f f.property)

/-- Restricting the actual Yosida generator preserves its literal ambient value. -/
theorem physicalZeroBoundaryPartYosida_coe {d : ℕ} (U : Set (Vec d)) (hd : 2 ≤ d)
    (ω : FieldPair d) (lam L : ℝ) (hL : 1 ≤ L) (hω : IsRegular L ω) (n : ℕ)
    (f : physicalZeroBoundaryL2 U hd ω lam L hω) :
    (physicalZeroBoundaryPartYosida U hd ω lam L hL hω n f :
      Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) =
      physicalZeroBoundaryYosida U hd ω lam L hL hω n f := rfl

/-- The actual interior Yosida operators are dissipative in the inherited physical norm. -/
theorem physicalZeroBoundaryPartYosida_inner_nonpos {d : ℕ}
    (U : Set (Vec d)) (hd : 2 ≤ d) (ω : FieldPair d) (lam L : ℝ)
    (hL : 1 ≤ L) (hω : IsRegular L ω) (n : ℕ)
    (f : physicalZeroBoundaryL2 U hd ω lam L hω) :
    inner ℝ f (physicalZeroBoundaryPartYosida U hd ω lam L hL hω n f) ≤ 0 :=
  physicalZeroBoundaryYosida_inner_nonpos U hd ω lam L hL hω n f

private theorem commute_restricted_operators {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H] (P : Submodule ℝ H)
    (A B : H →L[ℝ] H) (hA : ∀ f : P, A f ∈ P) (hB : ∀ f : P, B f ∈ P)
    (h : Commute A B) :
    Commute ((A.comp P.subtypeL).codRestrict P hA)
      ((B.comp P.subtypeL).codRestrict P hB) := by
  apply ContinuousLinearMap.ext
  intro f
  apply Subtype.ext
  exact congrArg (fun T : H →L[ℝ] H => T f) h.eq

/-- Restriction preserves commutation of every two actual physical Yosida generators. -/
theorem physicalZeroBoundaryPartYosida_commute {d : ℕ}
    (U : Set (Vec d)) (hd : 2 ≤ d) (ω : FieldPair d) (lam L : ℝ)
    (hL : 1 ≤ L) (hω : IsRegular L ω) (n m : ℕ) :
    Commute (physicalZeroBoundaryPartYosida U hd ω lam L hL hω n)
      (physicalZeroBoundaryPartYosida U hd ω lam L hL hω m) :=
  commute_restricted_operators _ _ _ _ _
    (physicalZeroBoundaryYosida_commute U hd ω lam L hL hω n m)

private theorem hasDerivAt_operator_exp_apply {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    (A : H →L[ℝ] H) (f : H) (t : ℝ) :
    HasDerivAt (fun s => NormedSpace.exp (s • A) f)
      (A (NormedSpace.exp (t • A) f)) t :=
  (ContinuousLinearMap.apply ℝ H f).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_exp_smul_const' (𝕂 := ℝ) A t)

private theorem norm_operator_exp_apply_le {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : H →L[ℝ] H) (hA : ∀ f, inner ℝ f (A f) ≤ 0)
    (f : H) (t : ℝ) (ht : 0 ≤ t) : ‖NormedSpace.exp (t • A) f‖ ≤ ‖f‖ := by
  have hd (s : ℝ) := (hasDerivAt_operator_exp_apply A f s).norm_sq
  have hm := antitone_of_hasDerivAt_nonpos hd (fun s =>
    mul_nonpos_of_nonneg_of_nonpos (by norm_num) (hA _))
  have hb := hm ht
  change ‖NormedSpace.exp (t • A) f‖ ^ 2 ≤
    ‖NormedSpace.exp (0 • A) f‖ ^ 2 at hb
  simp only [zero_smul, NormedSpace.exp_zero, ContinuousLinearMap.one_apply] at hb
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hb

private theorem norm_operator_exp_sub_le {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : H →L[ℝ] H) (hA : ∀ f, inner ℝ f (A f) ≤ 0)
    (f : H) (t : ℝ) (ht : 0 ≤ t) :
    ‖NormedSpace.exp (t • A) f - f‖ ≤ t * ‖A f‖ := by
  have hd (s : ℝ) : HasDerivAt (fun r => NormedSpace.exp (r • A) f)
      (NormedSpace.exp (s • A) (A f)) s :=
    (ContinuousLinearMap.apply ℝ H f).hasFDerivAt.comp_hasDerivAt s
      (hasDerivAt_exp_smul_const (𝕂 := ℝ) A s)
  have hc : Continuous (fun s => NormedSpace.exp (s • A) (A f)) :=
    continuous_iff_continuousAt.mpr fun s =>
      (hasDerivAt_operator_exp_apply A (A f) s).continuousAt
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0 : ℝ)) (b := t)
    (fun s _ => hd s) (hc.intervalIntegrable 0 t)
  simp only [zero_smul, NormedSpace.exp_zero, ContinuousLinearMap.one_apply] at hi
  rw [← hi]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := t)
    (fun s hs => norm_operator_exp_apply_le A hA (A f) s
      (by rw [Set.uIoc_of_le ht] at hs; exact hs.1.le))
  simpa only [sub_zero, abs_of_nonneg ht, mul_comm] using hb

private theorem norm_operator_exp_sub_exp_le {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A B : H →L[ℝ] H) (hA : ∀ f, inner ℝ f (A f) ≤ 0)
    (hB : ∀ f, inner ℝ f (B f) ≤ 0) (hAB : Commute A B)
    (f : H) (t : ℝ) (ht : 0 ≤ t) :
    ‖NormedSpace.exp (t • A) f - NormedSpace.exp (t • B) f‖ ≤
      t * ‖A f - B f‖ := by
  let T := fun r : ℝ => NormedSpace.exp (r • A)
  let S := fun r : ℝ => NormedSpace.exp (r • B)
  have hd (s : ℝ) : HasDerivAt (fun r => T (t-r) (S r f))
      (T (t-s) (S s (B f - A f))) s := by
    have ha : HasDerivAt (fun r => T (t-r)) (-(T (t-s) * A)) s := by
      have h := (hasDerivAt_exp_smul_const (𝕂 := ℝ) A (t-s)).scomp s
        ((hasDerivAt_const s t).sub (hasDerivAt_id s))
      simp only [zero_sub, neg_smul, one_smul] at h
      exact h
    have hb : HasDerivAt S (S s * B) s := hasDerivAt_exp_smul_const (𝕂 := ℝ) B s
    have hc : A * S s = S s * A := ((commute_real_smul_right hAB s).exp_right).eq
    have h : HasDerivAt (fun r => T (t-r) * S r) (T (t-s) * S s * (B-A)) s := by
      convert ha.mul hb using 1
      rw [neg_mul, mul_assoc (T (t-s)) A (S s), hc]
      noncomm_ring
    exact (ContinuousLinearMap.apply ℝ H f).hasFDerivAt.comp_hasDerivAt s h
  have hb (s : ℝ) (hs : s ∈ Set.Ico 0 t) :
      ‖T (t-s) (S s (B f - A f))‖ ≤ ‖B f - A f‖ :=
    (norm_operator_exp_apply_le A hA _ (t-s) (sub_nonneg.mpr hs.2.le)).trans
      (norm_operator_exp_apply_le B hB _ s hs.1)
  have h := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun s (_hs : s ∈ Set.Icc 0 t) => (hd s).hasDerivWithinAt) hb t ⟨ht, le_rfl⟩
  simpa only [T, S, sub_self, sub_zero, zero_smul, NormedSpace.exp_zero,
    ContinuousLinearMap.one_apply, norm_sub_rev, mul_comm] using h

private def operatorEvolution {H : Type*} [NormedAddCommGroup H]
    [NormedSpace ℝ H] (A : H →L[ℝ] H) (t : ℝ) : H →L[ℝ] H :=
  NormedSpace.exp (t • A)

private theorem operatorEvolution_commute {H : Type*} [NormedAddCommGroup H]
    [NormedSpace ℝ H] {A B : H →L[ℝ] H}
    (h : Commute A B) (t : ℝ) : Commute (operatorEvolution A t) B :=
  (h.smul_left t).exp_left

/-- Operator exponential evolution on the actual interior physical L² space. -/
def physicalZeroBoundaryYosidaEvolution {d : ℕ} (U : Set (Vec d)) (hd : 2 ≤ d)
    (ω : FieldPair d) (lam L : ℝ) (hL : 1 ≤ L) (hω : IsRegular L ω) (n : ℕ) (t : ℝ) :
    physicalZeroBoundaryL2 U hd ω lam L hω →L[ℝ] physicalZeroBoundaryL2 U hd ω lam L hω :=
  operatorEvolution (physicalZeroBoundaryPartYosida U hd ω lam L hL hω n) t

/-- The actual bounded interior evolutions start at the identity. -/
theorem physicalZeroBoundaryYosidaEvolution_zero {d : ℕ}
    (U : Set (Vec d)) (hd : 2 ≤ d) (ω : FieldPair d) (lam L : ℝ)
    (hL : 1 ≤ L) (hω : IsRegular L ω) (n : ℕ) :
    physicalZeroBoundaryYosidaEvolution U hd ω lam L hL hω n 0 =
      ContinuousLinearMap.id ℝ _ := by
  simp only [physicalZeroBoundaryYosidaEvolution, operatorEvolution, zero_smul, NormedSpace.exp_zero,
    ContinuousLinearMap.one_def]

private theorem operator_exp_add {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    (A : H →L[ℝ] H) (s t : ℝ) :
    NormedSpace.exp ((s+t) • A) =
      (NormedSpace.exp (s • A)).comp (NormedSpace.exp (t • A)) := by
  rw [add_smul, NormedSpace.exp_add_of_commute
    (commute_real_smul (Commute.refl A) s t)]
  rfl

/-- The actual bounded interior evolutions satisfy the semigroup law. -/
theorem physicalZeroBoundaryYosidaEvolution_add {d : ℕ}
    (U : Set (Vec d)) (hd : 2 ≤ d) (ω : FieldPair d) (lam L : ℝ)
    (hL : 1 ≤ L) (hω : IsRegular L ω) (n : ℕ) (s t : ℝ) :
    physicalZeroBoundaryYosidaEvolution U hd ω lam L hL hω n (s+t) =
      (physicalZeroBoundaryYosidaEvolution U hd ω lam L hL hω n s).comp
        (physicalZeroBoundaryYosidaEvolution U hd ω lam L hL hω n t) :=
  operator_exp_add _ s t

/-- Its strong derivative is the same actual restricted Yosida generator. -/
theorem hasDerivAt_physicalZeroBoundaryYosidaEvolution {d : ℕ}
    (U : Set (Vec d)) (hd : 2 ≤ d) (ω : FieldPair d) (lam L : ℝ)
    (hL : 1 ≤ L) (hω : IsRegular L ω) (n : ℕ)
    (f : physicalZeroBoundaryL2 U hd ω lam L hω) (t : ℝ) :
    HasDerivAt (fun s => physicalZeroBoundaryYosidaEvolution U hd ω lam L hL hω n s f)
      (physicalZeroBoundaryPartYosida U hd ω lam L hL hω n
        (physicalZeroBoundaryYosidaEvolution U hd ω lam L hL hω n t f)) t :=
  hasDerivAt_operator_exp_apply _ f t

/-- Every bounded interior evolution is strongly continuous. -/
theorem continuous_physicalZeroBoundaryYosidaEvolution_apply {d : ℕ}
    (U : Set (Vec d)) (hd : 2 ≤ d) (ω : FieldPair d) (lam L : ℝ)
    (hL : 1 ≤ L) (hω : IsRegular L ω) (n : ℕ)
    (f : physicalZeroBoundaryL2 U hd ω lam L hω) :
    Continuous (fun t => physicalZeroBoundaryYosidaEvolution U hd ω lam L hL hω n t f) :=
  continuous_iff_continuousAt.mpr fun t =>
    (hasDerivAt_physicalZeroBoundaryYosidaEvolution U hd ω lam L hL hω n f t).continuousAt

/-- Dissipativity gives contraction at every nonnegative time on the actual interior space. -/
theorem norm_physicalZeroBoundaryYosidaEvolution_apply_le {d : ℕ}
    (U : Set (Vec d)) (hd : 2 ≤ d) (ω : FieldPair d) (lam L : ℝ)
    (hL : 1 ≤ L) (hω : IsRegular L ω) (n : ℕ)
    (f : physicalZeroBoundaryL2 U hd ω lam L hω) (t : ℝ) (ht : 0 ≤ t) :
    ‖physicalZeroBoundaryYosidaEvolution U hd ω lam L hL hω n t f‖ ≤ ‖f‖ :=
  norm_operator_exp_apply_le _
    (physicalZeroBoundaryPartYosida_inner_nonpos U hd ω lam L hL hω n) f t ht

/-- The orbit increment is bounded by time times the actual restricted generator value. -/
theorem norm_physicalZeroBoundaryYosidaEvolution_sub_le {d : ℕ}
    (U : Set (Vec d)) (hd : 2 ≤ d) (ω : FieldPair d) (lam L : ℝ)
    (hL : 1 ≤ L) (hω : IsRegular L ω) (n : ℕ)
    (f : physicalZeroBoundaryL2 U hd ω lam L hω) (t : ℝ) (ht : 0 ≤ t) :
    ‖physicalZeroBoundaryYosidaEvolution U hd ω lam L hL hω n t f - f‖ ≤
      t * ‖physicalZeroBoundaryPartYosida U hd ω lam L hL hω n f‖ :=
  norm_operator_exp_sub_le _
    (physicalZeroBoundaryPartYosida_inner_nonpos U hd ω lam L hL hω n) f t ht

/-- The time-splitting comparison uses the actual two restricted Yosida values. -/
theorem norm_physicalZeroBoundaryYosidaEvolution_sub_evolution_le {d : ℕ}
    (U : Set (Vec d)) (hd : 2 ≤ d) (ω : FieldPair d) (lam L : ℝ)
    (hL : 1 ≤ L) (hω : IsRegular L ω) (n m : ℕ)
    (f : physicalZeroBoundaryL2 U hd ω lam L hω) (t : ℝ) (ht : 0 ≤ t) :
    ‖physicalZeroBoundaryYosidaEvolution U hd ω lam L hL hω n t f -
      physicalZeroBoundaryYosidaEvolution U hd ω lam L hL hω m t f‖ ≤
      t * ‖physicalZeroBoundaryPartYosida U hd ω lam L hL hω n f -
        physicalZeroBoundaryPartYosida U hd ω lam L hL hω m f‖ :=
  norm_operator_exp_sub_exp_le _ _
    (physicalZeroBoundaryPartYosida_inner_nonpos U hd ω lam L hL hω n)
    (physicalZeroBoundaryPartYosida_inner_nonpos U hd ω lam L hL hω m)
    (physicalZeroBoundaryPartYosida_commute U hd ω lam L hL hω n m) f t ht


/-- The constructed physical resolvent, now with its proved interior codomain. -/
def physicalZeroBoundaryInteriorResolvent {d : ℕ} (U : Set (Vec d)) (hd : 2 ≤ d)
    (ω : FieldPair d) (lam L α : ℝ) (hL : 1 ≤ L) (hω : IsRegular L ω) (hα : 0 < α) :
    Lp ℝ 2 (physicalReversibleMeasure ω hd lam) →L[ℝ]
      physicalZeroBoundaryL2 U hd ω lam L hω :=
  (physicalZeroBoundaryResolventL2 U hd ω lam L α hL hω hα).codRestrict _
    (physicalZeroBoundaryResolventL2_mem U hd ω lam L α hL hω hα)

/-- The interior resolvent is the identical actual physical L² value, with no representative change. -/
theorem physicalZeroBoundaryInteriorResolvent_coe {d : ℕ}
    (U : Set (Vec d)) (hd : 2 ≤ d) (ω : FieldPair d) (lam L α : ℝ)
    (hL : 1 ≤ L) (hω : IsRegular L ω) (hα : 0 < α)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    (physicalZeroBoundaryInteriorResolvent U hd ω lam L α hL hω hα f :
      Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) =
      physicalZeroBoundaryResolventL2 U hd ω lam L α hL hω hα f := rfl

/-- Every positive-rate resolvent has dense range in the constructed interior space. -/
theorem denseRange_physicalZeroBoundaryInteriorResolvent {d : ℕ}
    (U : Set (Vec d)) (hd : 2 ≤ d) (ω : FieldPair d) (lam L α : ℝ)
    (hL : 1 ≤ L) (hω : IsRegular L ω) (hα : 0 < α) :
    DenseRange (physicalZeroBoundaryInteriorResolvent U hd ω lam L α hL hω hα) := by
  intro f
  rw [closure_subtype]
  have he : Subtype.val '' Set.range
      (physicalZeroBoundaryInteriorResolvent U hd ω lam L α hL hω hα) =
      Set.range (physicalZeroBoundaryResolventL2 U hd ω lam L α hL hω hα) := by
    ext y
    constructor
    · rintro ⟨v, ⟨g, rfl⟩, rfl⟩
      exact ⟨g, rfl⟩
    · rintro ⟨g, rfl⟩
      exact ⟨physicalZeroBoundaryInteriorResolvent U hd ω lam L α hL hω hα g,
        ⟨g, rfl⟩, rfl⟩
  rw [he]
  change f.val ∈ (LinearMap.range
    (physicalZeroBoundaryResolventL2 U hd ω lam L α hL hω hα).toLinearMap).topologicalClosure
  rw [physicalZeroBoundaryResolventL2_closure_range]
  exact f.property

private theorem cauchySeq_physicalZeroBoundaryYosidaEvolution_on_resolvent {d : ℕ}
    (U : Set (Vec d)) (hd : 2 ≤ d) (ω : FieldPair d) (lam L : ℝ)
    (hL : 1 ≤ L) (hω : IsRegular L ω)
    (g : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) (t : ℝ) (ht : 0 ≤ t) :
    CauchySeq (fun n => physicalZeroBoundaryYosidaEvolution U hd ω lam L hL hω n t
      (physicalZeroBoundaryInteriorResolvent U hd ω lam L 1 hL hω zero_lt_one g)) := by
  have hc := (tendsto_physicalZeroBoundaryYosida_on_resolvent_projection
    U hd ω lam L hL hω g).cauchySeq
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  have hpos : 0 < t + 1 := by linarith only [ht]
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hc (ε/(t+1)) (div_pos hε hpos)
  refine ⟨N, fun n hn m hm => ?_⟩
  have hgap := hN n hn m hm
  rw [dist_eq_norm] at hgap ⊢
  calc
    _ ≤ t * ‖physicalZeroBoundaryPartYosida U hd ω lam L hL hω n
        (physicalZeroBoundaryInteriorResolvent U hd ω lam L 1 hL hω zero_lt_one g) -
      physicalZeroBoundaryPartYosida U hd ω lam L hL hω m
        (physicalZeroBoundaryInteriorResolvent U hd ω lam L 1 hL hω zero_lt_one g)‖ :=
      norm_physicalZeroBoundaryYosidaEvolution_sub_evolution_le U hd ω lam L hL hω n m _ t ht
    _ ≤ (t+1) * ‖physicalZeroBoundaryYosida U hd ω lam L hL hω n
        (physicalZeroBoundaryResolventL2 U hd ω lam L 1 hL hω zero_lt_one g) -
      physicalZeroBoundaryYosida U hd ω lam L hL hω m
        (physicalZeroBoundaryResolventL2 U hd ω lam L 1 hL hω zero_lt_one g)‖ :=
      mul_le_mul_of_nonneg_right (by linarith only [ht]) (norm_nonneg _)
    _ < ε := (lt_div_iff₀' hpos).mp hgap

/-- Contractivity and the proved dense resolvent range give Cauchy evolutions for every interior datum. -/
theorem cauchySeq_physicalZeroBoundaryYosidaEvolution {d : ℕ}
    (U : Set (Vec d)) (hd : 2 ≤ d) (ω : FieldPair d) (lam L : ℝ)
    (hL : 1 ≤ L) (hω : IsRegular L ω)
    (f : physicalZeroBoundaryL2 U hd ω lam L hω) (t : ℝ) (ht : 0 ≤ t) :
    CauchySeq (fun n => physicalZeroBoundaryYosidaEvolution U hd ω lam L hL hω n t f) := by
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  obtain ⟨g, hfu⟩ := (denseRange_physicalZeroBoundaryInteriorResolvent
    U hd ω lam L 1 hL hω zero_lt_one).exists_dist_lt f (by positivity : 0 < ε/3)
  let u := physicalZeroBoundaryInteriorResolvent U hd ω lam L 1 hL hω zero_lt_one g
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp
    (cauchySeq_physicalZeroBoundaryYosidaEvolution_on_resolvent U hd ω lam L hL hω g t ht)
      (ε/3) (by positivity)
  have hb (n : ℕ) :
      dist (physicalZeroBoundaryYosidaEvolution U hd ω lam L hL hω n t f)
        (physicalZeroBoundaryYosidaEvolution U hd ω lam L hL hω n t u) ≤ dist f u := by
    rw [dist_eq_norm, dist_eq_norm, ← map_sub]
    exact norm_physicalZeroBoundaryYosidaEvolution_apply_le U hd ω lam L hL hω n (f-u) t ht
  refine ⟨N, fun n hn m hm => ?_⟩
  calc
    _ ≤ dist (physicalZeroBoundaryYosidaEvolution U hd ω lam L hL hω n t f)
          (physicalZeroBoundaryYosidaEvolution U hd ω lam L hL hω n t u) +
        (dist (physicalZeroBoundaryYosidaEvolution U hd ω lam L hL hω n t u)
          (physicalZeroBoundaryYosidaEvolution U hd ω lam L hL hω m t u) +
        dist (physicalZeroBoundaryYosidaEvolution U hd ω lam L hL hω m t u)
          (physicalZeroBoundaryYosidaEvolution U hd ω lam L hL hω m t f)) := by
      rw [← add_assoc]
      exact dist_triangle4 _ _ _ _
    _ ≤ dist f u +
        (dist (physicalZeroBoundaryYosidaEvolution U hd ω lam L hL hω n t u)
          (physicalZeroBoundaryYosidaEvolution U hd ω lam L hL hω m t u) + dist f u) :=
      add_le_add (hb n) (add_le_add le_rfl (by simpa only [dist_comm] using hb m))
    _ < ε := by linarith only [hfu, hN n hn m hm]

private def physicalInteriorEvolutionLimit {d : ℕ} (U : Set (Vec d)) (hd : 2 ≤ d)
    (ω : FieldPair d) (lam L : ℝ) (hL : 1 ≤ L) (hω : IsRegular L ω) (t : ℝ≥0)
    (f : physicalZeroBoundaryL2 U hd ω lam L hω) : physicalZeroBoundaryL2 U hd ω lam L hω :=
  limUnder atTop (fun n => physicalZeroBoundaryYosidaEvolution U hd ω lam L hL hω n t f)

private theorem tendsto_physicalInteriorEvolutionLimit {d : ℕ}
    (U : Set (Vec d)) (hd : 2 ≤ d) (ω : FieldPair d) (lam L : ℝ)
    (hL : 1 ≤ L) (hω : IsRegular L ω) (t : ℝ≥0)
    (f : physicalZeroBoundaryL2 U hd ω lam L hω) :
    Tendsto (fun n => physicalZeroBoundaryYosidaEvolution U hd ω lam L hL hω n t f) atTop
      (𝓝 (physicalInteriorEvolutionLimit U hd ω lam L hL hω t f)) :=
  (cauchySeq_physicalZeroBoundaryYosidaEvolution U hd ω lam L hL hω f t t.property).tendsto_limUnder

private theorem norm_physicalInteriorEvolutionLimit_le {d : ℕ}
    (U : Set (Vec d)) (hd : 2 ≤ d) (ω : FieldPair d) (lam L : ℝ)
    (hL : 1 ≤ L) (hω : IsRegular L ω) (t : ℝ≥0)
    (f : physicalZeroBoundaryL2 U hd ω lam L hω) :
    ‖physicalInteriorEvolutionLimit U hd ω lam L hL hω t f‖ ≤ ‖f‖ :=
  le_of_tendsto (tendsto_physicalInteriorEvolutionLimit U hd ω lam L hL hω t f).norm
    (Eventually.of_forall fun n =>
      norm_physicalZeroBoundaryYosidaEvolution_apply_le U hd ω lam L hL hω n f t t.property)

/-- The strong-limit evolution constructed from the actual physical interior resolvents. -/
def physicalZeroBoundaryEvolution {d : ℕ} (U : Set (Vec d)) (hd : 2 ≤ d)
    (ω : FieldPair d) (lam L : ℝ) (hL : 1 ≤ L) (hω : IsRegular L ω) (t : ℝ≥0) :
    physicalZeroBoundaryL2 U hd ω lam L hω →L[ℝ] physicalZeroBoundaryL2 U hd ω lam L hω :=
  (linearMapOfTendsto (physicalInteriorEvolutionLimit U hd ω lam L hL hω t)
    (fun n => (physicalZeroBoundaryYosidaEvolution U hd ω lam L hL hω n t).toLinearMap)
    (tendsto_pi_nhds.mpr (fun f =>
      tendsto_physicalInteriorEvolutionLimit U hd ω lam L hL hω t f))).mkContinuous 1
        (fun f => by
          rw [one_mul]
          exact norm_physicalInteriorEvolutionLimit_le U hd ω lam L hL hω t f)

/-- The bounded physical interior evolutions converge strongly on every interior L² datum. -/
theorem tendsto_physicalZeroBoundaryYosidaEvolution {d : ℕ}
    (U : Set (Vec d)) (hd : 2 ≤ d) (ω : FieldPair d) (lam L : ℝ)
    (hL : 1 ≤ L) (hω : IsRegular L ω) (t : ℝ≥0)
    (f : physicalZeroBoundaryL2 U hd ω lam L hω) :
    Tendsto (fun n => physicalZeroBoundaryYosidaEvolution U hd ω lam L hL hω n t f) atTop
      (𝓝 (physicalZeroBoundaryEvolution U hd ω lam L hL hω t f)) :=
  tendsto_physicalInteriorEvolutionLimit U hd ω lam L hL hω t f

/-- The constructed limit is contractive for every datum and nonnegative time. -/
theorem norm_physicalZeroBoundaryEvolution_apply_le {d : ℕ}
    (U : Set (Vec d)) (hd : 2 ≤ d) (ω : FieldPair d) (lam L : ℝ)
    (hL : 1 ≤ L) (hω : IsRegular L ω) (t : ℝ≥0)
    (f : physicalZeroBoundaryL2 U hd ω lam L hω) :
    ‖physicalZeroBoundaryEvolution U hd ω lam L hL hω t f‖ ≤ ‖f‖ :=
  norm_physicalInteriorEvolutionLimit_le U hd ω lam L hL hω t f

/-- The constructed evolution has operator norm at most one. -/
theorem norm_physicalZeroBoundaryEvolution_le {d : ℕ}
    (U : Set (Vec d)) (hd : 2 ≤ d) (ω : FieldPair d) (lam L : ℝ)
    (hL : 1 ≤ L) (hω : IsRegular L ω) (t : ℝ≥0) :
    ‖physicalZeroBoundaryEvolution U hd ω lam L hL hω t‖ ≤ 1 := by
  apply (physicalZeroBoundaryEvolution U hd ω lam L hL hω t).opNorm_le_bound zero_le_one
  intro f
  simpa only [one_mul] using
    norm_physicalZeroBoundaryEvolution_apply_le U hd ω lam L hL hω t f

/-- Strong convergence of the bounded interior evolutions also permits varying initial data. -/
theorem tendsto_physicalZeroBoundaryYosidaEvolution_apply {d : ℕ}
    (U : Set (Vec d)) (hd : 2 ≤ d) (ω : FieldPair d) (lam L : ℝ)
    (hL : 1 ≤ L) (hω : IsRegular L ω) (t : ℝ≥0)
    {u : ℕ → physicalZeroBoundaryL2 U hd ω lam L hω}
    {f : physicalZeroBoundaryL2 U hd ω lam L hω} (hu : Tendsto u atTop (𝓝 f)) :
    Tendsto (fun n => physicalZeroBoundaryYosidaEvolution U hd ω lam L hL hω n t (u n)) atTop
      (𝓝 (physicalZeroBoundaryEvolution U hd ω lam L hL hω t f)) := by
  have hz : Tendsto (fun n => physicalZeroBoundaryYosidaEvolution U hd ω lam L hL hω n t (u n) -
      physicalZeroBoundaryYosidaEvolution U hd ω lam L hL hω n t f) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
      (tendsto_iff_norm_sub_tendsto_zero.mp hu)
    rw [← map_sub]
    exact norm_physicalZeroBoundaryYosidaEvolution_apply_le U hd ω lam L hL hω n (u n-f) t t.property
  simpa only [sub_add_cancel, zero_add] using
    hz.add (tendsto_physicalZeroBoundaryYosidaEvolution U hd ω lam L hL hω t f)

/-- The actual interior strong limit starts at the identity. -/
theorem physicalZeroBoundaryEvolution_zero {d : ℕ}
    (U : Set (Vec d)) (hd : 2 ≤ d) (ω : FieldPair d) (lam L : ℝ)
    (hL : 1 ≤ L) (hω : IsRegular L ω) :
    physicalZeroBoundaryEvolution U hd ω lam L hL hω 0 = ContinuousLinearMap.id ℝ _ := by
  apply ContinuousLinearMap.ext
  intro f
  have h := tendsto_physicalZeroBoundaryYosidaEvolution U hd ω lam L hL hω 0 f
  simp only [NNReal.coe_zero, physicalZeroBoundaryYosidaEvolution_zero,
    ContinuousLinearMap.id_apply] at h
  exact tendsto_nhds_unique h tendsto_const_nhds

/-- The actual interior strong limit satisfies the nonnegative-time semigroup law. -/
theorem physicalZeroBoundaryEvolution_add {d : ℕ}
    (U : Set (Vec d)) (hd : 2 ≤ d) (ω : FieldPair d) (lam L : ℝ)
    (hL : 1 ≤ L) (hω : IsRegular L ω) (s t : ℝ≥0) :
    physicalZeroBoundaryEvolution U hd ω lam L hL hω (s+t) =
      (physicalZeroBoundaryEvolution U hd ω lam L hL hω s).comp
        (physicalZeroBoundaryEvolution U hd ω lam L hL hω t) := by
  apply ContinuousLinearMap.ext
  intro f
  have h := tendsto_physicalZeroBoundaryYosidaEvolution_apply U hd ω lam L hL hω s
    (tendsto_physicalZeroBoundaryYosidaEvolution U hd ω lam L hL hω t f)
  simp only [← ContinuousLinearMap.comp_apply, ← physicalZeroBoundaryYosidaEvolution_add] at h
  exact tendsto_nhds_unique
    (tendsto_physicalZeroBoundaryYosidaEvolution U hd ω lam L hL hω (s+t) f) h

private theorem norm_physicalZeroBoundaryPartYosida_on_resolvent_le {d : ℕ}
    (U : Set (Vec d)) (hd : 2 ≤ d) (ω : FieldPair d) (lam L : ℝ)
    (hL : 1 ≤ L) (hω : IsRegular L ω) (n : ℕ)
    (g : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    ‖physicalZeroBoundaryPartYosida U hd ω lam L hL hω n
      (physicalZeroBoundaryInteriorResolvent U hd ω lam L 1 hL hω zero_lt_one g)‖ ≤
      ‖physicalZeroBoundaryResolventL2 U hd ω lam L 1 hL hω zero_lt_one g - g‖ := by
  change ‖physicalZeroBoundaryYosida U hd ω lam L hL hω n
    (physicalZeroBoundaryResolventL2 U hd ω lam L 1 hL hω zero_lt_one g)‖ ≤ _
  rw [physicalZeroBoundaryYosida_on_resolvent]
  exact physicalZeroBoundaryResolventApproximation_norm_le U hd ω lam L hL hω n _

/-- Resolvent-range data inherit an orbit-increment bound from the actual variational resolvent. -/
theorem norm_physicalZeroBoundaryEvolution_resolvent_sub_le {d : ℕ}
    (U : Set (Vec d)) (hd : 2 ≤ d) (ω : FieldPair d) (lam L : ℝ)
    (hL : 1 ≤ L) (hω : IsRegular L ω)
    (g : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) (t : ℝ≥0) :
    ‖physicalZeroBoundaryEvolution U hd ω lam L hL hω t
      (physicalZeroBoundaryInteriorResolvent U hd ω lam L 1 hL hω zero_lt_one g) -
      physicalZeroBoundaryInteriorResolvent U hd ω lam L 1 hL hω zero_lt_one g‖ ≤
      (t : ℝ) * ‖physicalZeroBoundaryResolventL2 U hd ω lam L 1 hL hω zero_lt_one g - g‖ := by
  apply le_of_tendsto ((tendsto_physicalZeroBoundaryYosidaEvolution
    U hd ω lam L hL hω t _).sub_const _).norm
  exact Eventually.of_forall fun n =>
    (norm_physicalZeroBoundaryYosidaEvolution_sub_le U hd ω lam L hL hω n _ t t.property).trans
      (mul_le_mul_of_nonneg_left
        (norm_physicalZeroBoundaryPartYosida_on_resolvent_le U hd ω lam L hL hω n g) t.property)

private theorem physicalInteriorEvolution_sub_evolution_le_of_le {d : ℕ}
    (U : Set (Vec d)) (hd : 2 ≤ d) (ω : FieldPair d) (lam L : ℝ)
    (hL : 1 ≤ L) (hω : IsRegular L ω)
    (g : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) (s t : ℝ≥0) (hst : s ≤ t) :
    ‖physicalZeroBoundaryEvolution U hd ω lam L hL hω t
        (physicalZeroBoundaryInteriorResolvent U hd ω lam L 1 hL hω zero_lt_one g) -
      physicalZeroBoundaryEvolution U hd ω lam L hL hω s
        (physicalZeroBoundaryInteriorResolvent U hd ω lam L 1 hL hω zero_lt_one g)‖ ≤
      ((t : ℝ)-(s : ℝ)) *
        ‖physicalZeroBoundaryResolventL2 U hd ω lam L 1 hL hω zero_lt_one g - g‖ := by
  let f := physicalZeroBoundaryInteriorResolvent U hd ω lam L 1 hL hω zero_lt_one g
  have he : physicalZeroBoundaryEvolution U hd ω lam L hL hω t f -
      physicalZeroBoundaryEvolution U hd ω lam L hL hω s f =
      physicalZeroBoundaryEvolution U hd ω lam L hL hω s
        (physicalZeroBoundaryEvolution U hd ω lam L hL hω (t-s) f - f) := by
    rw [map_sub, ← ContinuousLinearMap.comp_apply
      (physicalZeroBoundaryEvolution U hd ω lam L hL hω s)
      (physicalZeroBoundaryEvolution U hd ω lam L hL hω (t-s)) f,
      ← physicalZeroBoundaryEvolution_add, add_tsub_cancel_of_le hst]
  rw [he]
  have h := (norm_physicalZeroBoundaryEvolution_apply_le U hd ω lam L hL hω s _).trans
    (norm_physicalZeroBoundaryEvolution_resolvent_sub_le U hd ω lam L hL hω g (t-s))
  simpa only [NNReal.coe_sub hst] using h

/-- Orbits of the actual resolvent range are Lipschitz, with no generator-domain premise. -/
theorem lipschitzWith_physicalZeroBoundaryEvolution_resolvent {d : ℕ}
    (U : Set (Vec d)) (hd : 2 ≤ d) (ω : FieldPair d) (lam L : ℝ)
    (hL : 1 ≤ L) (hω : IsRegular L ω)
    (g : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    LipschitzWith ⟨‖physicalZeroBoundaryResolventL2 U hd ω lam L 1 hL hω zero_lt_one g - g‖,
      norm_nonneg _⟩ (fun t => physicalZeroBoundaryEvolution U hd ω lam L hL hω t
        (physicalZeroBoundaryInteriorResolvent U hd ω lam L 1 hL hω zero_lt_one g)) := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  rw [dist_eq_norm]
  change ‖physicalZeroBoundaryEvolution U hd ω lam L hL hω s
      (physicalZeroBoundaryInteriorResolvent U hd ω lam L 1 hL hω zero_lt_one g) -
    physicalZeroBoundaryEvolution U hd ω lam L hL hω t
      (physicalZeroBoundaryInteriorResolvent U hd ω lam L 1 hL hω zero_lt_one g)‖ ≤
    ‖physicalZeroBoundaryResolventL2 U hd ω lam L 1 hL hω zero_lt_one g - g‖ * |(s : ℝ)-(t : ℝ)|
  rcases le_total s t with hst | hts
  · rw [norm_sub_rev, abs_of_nonpos (sub_nonpos.mpr (show (s : ℝ) ≤ (t : ℝ) from hst)),
      neg_sub, mul_comm]
    exact physicalInteriorEvolution_sub_evolution_le_of_le U hd ω lam L hL hω g s t hst
  · rw [abs_of_nonneg (sub_nonneg.mpr (show (t : ℝ) ≤ (s : ℝ) from hts)), mul_comm]
    exact physicalInteriorEvolution_sub_evolution_le_of_le U hd ω lam L hL hω g t s hts

/-- The constructed physical interior contraction semigroup is strongly continuous at every time. -/
theorem continuous_physicalZeroBoundaryEvolution_apply {d : ℕ}
    (U : Set (Vec d)) (hd : 2 ≤ d) (ω : FieldPair d) (lam L : ℝ)
    (hL : 1 ≤ L) (hω : IsRegular L ω)
    (f : physicalZeroBoundaryL2 U hd ω lam L hω) :
    Continuous (fun t => physicalZeroBoundaryEvolution U hd ω lam L hL hω t f) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  obtain ⟨g, hfu⟩ := (denseRange_physicalZeroBoundaryInteriorResolvent
    U hd ω lam L 1 hL hω zero_lt_one).exists_dist_lt f (by positivity : 0 < ε/3)
  let u := physicalZeroBoundaryInteriorResolvent U hd ω lam L 1 hL hω zero_lt_one g
  obtain ⟨δ, hδ, huδ⟩ := Metric.continuousAt_iff.mp
    (lipschitzWith_physicalZeroBoundaryEvolution_resolvent U hd ω lam L hL hω g).continuous.continuousAt
      (ε/3) (by positivity)
  refine ⟨δ, hδ, fun s hs => ?_⟩
  have hb (r : ℝ≥0) : dist (physicalZeroBoundaryEvolution U hd ω lam L hL hω r f)
      (physicalZeroBoundaryEvolution U hd ω lam L hL hω r u) ≤ dist f u := by
    rw [dist_eq_norm, dist_eq_norm, ← map_sub]
    exact norm_physicalZeroBoundaryEvolution_apply_le U hd ω lam L hL hω r (f-u)
  calc
    _ ≤ dist (physicalZeroBoundaryEvolution U hd ω lam L hL hω s f)
          (physicalZeroBoundaryEvolution U hd ω lam L hL hω s u) +
        (dist (physicalZeroBoundaryEvolution U hd ω lam L hL hω s u)
          (physicalZeroBoundaryEvolution U hd ω lam L hL hω t u) +
        dist (physicalZeroBoundaryEvolution U hd ω lam L hL hω t u)
          (physicalZeroBoundaryEvolution U hd ω lam L hL hω t f)) := by
      rw [← add_assoc]
      exact dist_triangle4 _ _ _ _
    _ ≤ dist f u +
        (dist (physicalZeroBoundaryEvolution U hd ω lam L hL hω s u)
          (physicalZeroBoundaryEvolution U hd ω lam L hL hω t u) + dist f u) :=
      add_le_add (hb s) (add_le_add le_rfl (by simpa only [dist_comm] using hb t))
    _ < ε := by linarith only [hfu, huδ hs]


/-- The actual restricted Yosida generators converge on unit-rate resolvents of interior data. -/
theorem tendsto_physicalZeroBoundaryPartYosida_resolvent {d : ℕ}
    (U : Set (Vec d)) (hd : 2 ≤ d) (ω : FieldPair d) (lam L : ℝ)
    (hL : 1 ≤ L) (hω : IsRegular L ω)
    (f : physicalZeroBoundaryL2 U hd ω lam L hω) :
    Tendsto (fun n => physicalZeroBoundaryPartYosida U hd ω lam L hL hω n
      (physicalZeroBoundaryInteriorResolvent U hd ω lam L 1 hL hω zero_lt_one f)) atTop
      (𝓝 (physicalZeroBoundaryInteriorResolvent U hd ω lam L 1 hL hω zero_lt_one f - f)) :=
  tendsto_subtype_rng.mpr
    (tendsto_physicalZeroBoundaryYosida_on_resolvent U hd ω lam L hL hω f f.property)

private theorem tendsto_interior_yosida_slope {d : ℕ}
    (U : Set (Vec d)) (hd : 2 ≤ d) (ω : FieldPair d) (lam L : ℝ)
    (hL : 1 ≤ L) (hω : IsRegular L ω) (n : ℕ)
    (f : physicalZeroBoundaryL2 U hd ω lam L hω) :
    Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ •
      (physicalZeroBoundaryYosidaEvolution U hd ω lam L hL hω n t f - f))
      (𝓝[>] (0 : ℝ≥0)) (𝓝 (physicalZeroBoundaryPartYosida U hd ω lam L hL hω n f)) := by
  have ht : Tendsto (fun t : ℝ≥0 => (t : ℝ)) (𝓝[>] (0 : ℝ≥0)) (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨(NNReal.continuous_coe.tendsto 0).mono_left nhdsWithin_le_nhds,
      eventually_mem_nhdsWithin⟩
  have h := ((hasDerivAt_physicalZeroBoundaryYosidaEvolution U hd ω lam L hL hω n f 0).tendsto_slope_zero_right).comp ht
  simp only [Function.comp_def, zero_add, physicalZeroBoundaryYosidaEvolution_zero,
    ContinuousLinearMap.id_apply] at h
  exact h

private theorem physicalInteriorEvolution_resolvent_sub_yosida_le {d : ℕ}
    (U : Set (Vec d)) (hd : 2 ≤ d) (ω : FieldPair d) (lam L : ℝ)
    (hL : 1 ≤ L) (hω : IsRegular L ω)
    (f : physicalZeroBoundaryL2 U hd ω lam L hω) (n : ℕ) (t : ℝ≥0) :
    ‖physicalZeroBoundaryEvolution U hd ω lam L hL hω t
        (physicalZeroBoundaryInteriorResolvent U hd ω lam L 1 hL hω zero_lt_one f) -
      physicalZeroBoundaryYosidaEvolution U hd ω lam L hL hω n t
        (physicalZeroBoundaryInteriorResolvent U hd ω lam L 1 hL hω zero_lt_one f)‖ ≤
      (t : ℝ) * ‖physicalZeroBoundaryInteriorResolvent U hd ω lam L 1 hL hω zero_lt_one f - f -
        physicalZeroBoundaryPartYosida U hd ω lam L hL hω n
          (physicalZeroBoundaryInteriorResolvent U hd ω lam L 1 hL hω zero_lt_one f)‖ :=
  le_of_tendsto_of_tendsto
    ((tendsto_physicalZeroBoundaryYosidaEvolution U hd ω lam L hL hω t _).sub_const _).norm
    (tendsto_const_nhds.mul
      ((tendsto_physicalZeroBoundaryPartYosida_resolvent U hd ω lam L hL hω f).sub_const _).norm)
    (Eventually.of_forall fun m =>
      norm_physicalZeroBoundaryYosidaEvolution_sub_evolution_le U hd ω lam L hL hω m n _ t t.property)

private theorem dist_smul_sub_sub {H : Type*} [NormedAddCommGroup H]
    [NormedSpace ℝ H] (r : ℝ) (a b u : H) :
    dist (r • (a - u)) (r • (b - u)) = |r| * ‖a - b‖ := by
  rw [dist_eq_norm, ← smul_sub, sub_sub_sub_cancel_right, norm_smul, Real.norm_eq_abs]

/-- At the actual unit-rate resolvent values the interior evolution has right derivative
`R₁ f - f`, as determined by the physical variational resolvent equation. -/
theorem tendsto_physicalZeroBoundaryEvolution_slope_resolvent {d : ℕ}
    (U : Set (Vec d)) (hd : 2 ≤ d) (ω : FieldPair d) (lam L : ℝ)
    (hL : 1 ≤ L) (hω : IsRegular L ω)
    (f : physicalZeroBoundaryL2 U hd ω lam L hω) :
    Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ •
      (physicalZeroBoundaryEvolution U hd ω lam L hL hω t
          (physicalZeroBoundaryInteriorResolvent U hd ω lam L 1 hL hω zero_lt_one f) -
        physicalZeroBoundaryInteriorResolvent U hd ω lam L 1 hL hω zero_lt_one f))
      (𝓝[>] (0 : ℝ≥0))
      (𝓝 (physicalZeroBoundaryInteriorResolvent U hd ω lam L 1 hL hω zero_lt_one f - f)) := by
  let u := physicalZeroBoundaryInteriorResolvent U hd ω lam L 1 hL hω zero_lt_one f
  let g := u - f
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨n, hn⟩ := Metric.tendsto_atTop.mp
    (tendsto_physicalZeroBoundaryPartYosida_resolvent U hd ω lam L hL hω f)
      (ε/3) (by positivity)
  have hng := hn n le_rfl
  have hy := Metric.tendsto_nhds.mp
    (tendsto_interior_yosida_slope U hd ω lam L hL hω n u) (ε/3) (by positivity)
  filter_upwards [hy, eventually_mem_nhdsWithin] with t ht hpos
  have htpos : 0 < (t : ℝ) := hpos
  have hb : dist ((t : ℝ)⁻¹ • (physicalZeroBoundaryEvolution U hd ω lam L hL hω t u - u))
      ((t : ℝ)⁻¹ • (physicalZeroBoundaryYosidaEvolution U hd ω lam L hL hω n t u - u)) ≤
        ‖g - physicalZeroBoundaryPartYosida U hd ω lam L hL hω n u‖ := by
    rw [dist_smul_sub_sub, abs_inv, abs_of_pos htpos]
    calc
      _ ≤ (t : ℝ)⁻¹ * ((t : ℝ) *
          ‖g - physicalZeroBoundaryPartYosida U hd ω lam L hL hω n u‖) :=
        mul_le_mul_of_nonneg_left
          (physicalInteriorEvolution_resolvent_sub_yosida_le U hd ω lam L hL hω f n t)
          (inv_nonneg.mpr t.property)
      _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ htpos.ne', one_mul]
  have htri := dist_triangle4
    ((t : ℝ)⁻¹ • (physicalZeroBoundaryEvolution U hd ω lam L hL hω t u - u))
    ((t : ℝ)⁻¹ • (physicalZeroBoundaryYosidaEvolution U hd ω lam L hL hω n t u - u))
    (physicalZeroBoundaryPartYosida U hd ω lam L hL hω n u) g
  have hnrev : ‖g - physicalZeroBoundaryPartYosida U hd ω lam L hL hω n u‖ < ε/3 := by
    simpa only [dist_eq_norm, norm_sub_rev] using hng
  linarith only [htri, hb, ht, hnrev, hng]


/-- The full physical part-generator graph: an actual zero-boundary weak-gradient
representative and its literal physical Dirichlet-form identity against every interior H¹ test. -/
def IsPhysicalZeroBoundaryGeneratorPair {d : ℕ} (U : Set (Vec d)) (hd : 2 ≤ d)
    (ω : FieldPair d) (lam L : ℝ) (hω : IsRegular L ω)
    (f g : physicalZeroBoundaryL2 U hd ω lam L hω) : Prop :=
  ∃ u : physicalH1ZeroBoundary U hd lam,
    physicalZeroBoundaryValue U hd ω lam L hω u = f.val ∧
    ∀ v : physicalH1ZeroBoundary U hd lam,
      (∫ x, weightedFormIntegrand ω.1 (physicalH1SpaceRepresentative hd lam u.1)
        (physicalH1SpaceRepresentative hd lam v.1) x ∂physicalReversibleMeasure ω hd lam) =
        -inner ℝ g.val (physicalZeroBoundaryValue U hd ω lam L hω v)

private theorem variationalGenerator_iff_resolvent {V H : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B) (J : V →L[ℝ] H)
    (E : V → V → ℝ) (hE : ∀ u v, B u v = inner ℝ (J u) (J v) + E u v)
    (f g : H) :
    (∃ u, J u = f ∧ ∀ v, E u v = -inner ℝ g (J v)) ↔
      J (variationalResolventGraph B hB J (f-g)) = f := by
  constructor
  · rintro ⟨u, hu, hv⟩
    have hs : u = variationalResolventGraph B hB J (f-g) := by
      apply variationalResolventGraph_unique B hB J (f-g) u
      intro v
      rw [hE, hu, hv, inner_sub_left, sub_eq_add_neg]
    rw [← hs]
    exact hu
  · intro hu
    refine ⟨variationalResolventGraph B hB J (f-g), hu, fun v => ?_⟩
    have hb := variationalResolventGraph_spec B hB J (f-g) v
    rw [hE, hu, inner_sub_left] at hb
    linarith only [hb]

/-- The complete physical weak part graph is characterized by its constructed unit resolvent. -/
theorem isPhysicalZeroBoundaryGeneratorPair_iff_resolvent {d : ℕ}
    (U : Set (Vec d)) (hd : 2 ≤ d) (ω : FieldPair d) (lam L : ℝ)
    (hL : 1 ≤ L) (hω : IsRegular L ω)
    (f g : physicalZeroBoundaryL2 U hd ω lam L hω) :
    IsPhysicalZeroBoundaryGeneratorPair U hd ω lam L hω f g ↔
      physicalZeroBoundaryInteriorResolvent U hd ω lam L 1 hL hω zero_lt_one
        (f-g : physicalZeroBoundaryL2 U hd ω lam L hω) = f := by
  rw [Subtype.ext_iff]
  exact variationalGenerator_iff_resolvent
    (physicalZeroBoundaryBilinear U hd ω lam L 1 hL hω zero_lt_one)
    (physicalZeroBoundaryBilinear_isCoercive U hd ω lam L 1 hL hω zero_lt_one)
    (physicalZeroBoundaryValue U hd ω lam L hω)
    (fun (u v : physicalH1ZeroBoundary U hd lam) => ∫ x, weightedFormIntegrand ω.1
      (physicalH1SpaceRepresentative hd lam u.1) (physicalH1SpaceRepresentative hd lam v.1) x
      ∂physicalReversibleMeasure ω hd lam)
    (fun u v => by simpa only [one_mul] using
      physicalZeroBoundaryBilinear_eq_inner U hd ω lam L 1 hL hω zero_lt_one u v) f.val g.val

private def physicalInteriorResolventEnd {d : ℕ} (U : Set (Vec d)) (hd : 2 ≤ d)
    (ω : FieldPair d) (lam L α : ℝ) (hL : 1 ≤ L) (hω : IsRegular L ω) (hα : 0 < α) :
    physicalZeroBoundaryL2 U hd ω lam L hω →L[ℝ] physicalZeroBoundaryL2 U hd ω lam L hω :=
  (physicalZeroBoundaryInteriorResolvent U hd ω lam L α hL hω hα).comp
    (physicalZeroBoundaryL2 U hd ω lam L hω).subtypeL

private theorem commute_yosida_resolvent {A : Type*} [Ring A] [Algebra ℝ A]
    {a b : A} (hab : Commute a b) (r : ℝ) : Commute (r • (r • a - 1)) b :=
  ((hab.smul_left r).sub_left (Commute.one_left b)).smul_left r

private theorem physicalInteriorYosida_commute_resolvent {d : ℕ}
    (U : Set (Vec d)) (hd : 2 ≤ d) (ω : FieldPair d) (lam L α : ℝ)
    (hL : 1 ≤ L) (hω : IsRegular L ω) (hα : 0 < α) (n : ℕ) :
    Commute (physicalZeroBoundaryPartYosida U hd ω lam L hL hω n)
      (physicalInteriorResolventEnd U hd ω lam L α hL hω hα) := by
  have hR := physicalZeroBoundaryResolventL2_commute U hd ω lam L
    ((n : ℝ)+1) α hL hω (by positivity) hα
  have hY : Commute (physicalZeroBoundaryYosida U hd ω lam L hL hω n)
      (physicalZeroBoundaryResolventL2 U hd ω lam L α hL hω hα) :=
    commute_yosida_resolvent hR ((n : ℝ)+1)
  exact commute_restricted_operators _ _ _ _ _ hY

private theorem physicalInteriorYosidaEvolution_commute_resolvent {d : ℕ}
    (U : Set (Vec d)) (hd : 2 ≤ d) (ω : FieldPair d) (lam L α : ℝ)
    (hL : 1 ≤ L) (hω : IsRegular L ω) (hα : 0 < α) (n : ℕ) (t : ℝ) :
    Commute (physicalZeroBoundaryYosidaEvolution U hd ω lam L hL hω n t)
      (physicalInteriorResolventEnd U hd ω lam L α hL hω hα) :=
  operatorEvolution_commute
    (physicalInteriorYosida_commute_resolvent U hd ω lam L α hL hω hα n) t

/-- The constructed part evolution commutes with every positive actual interior resolvent. -/
theorem physicalZeroBoundaryEvolution_resolvent_comm {d : ℕ}
    (U : Set (Vec d)) (hd : 2 ≤ d) (ω : FieldPair d) (lam L α : ℝ)
    (hL : 1 ≤ L) (hω : IsRegular L ω) (hα : 0 < α) (t : ℝ≥0)
    (f : physicalZeroBoundaryL2 U hd ω lam L hω) :
    physicalZeroBoundaryEvolution U hd ω lam L hL hω t
        (physicalZeroBoundaryInteriorResolvent U hd ω lam L α hL hω hα f) =
      physicalZeroBoundaryInteriorResolvent U hd ω lam L α hL hω hα
        (physicalZeroBoundaryEvolution U hd ω lam L hL hω t f) := by
  let R := physicalInteriorResolventEnd U hd ω lam L α hL hω hα
  have he (n : ℕ) : physicalZeroBoundaryYosidaEvolution U hd ω lam L hL hω n t (R f) =
      R (physicalZeroBoundaryYosidaEvolution U hd ω lam L hL hω n t f) :=
    congrArg (fun A => A f)
      (physicalInteriorYosidaEvolution_commute_resolvent U hd ω lam L α hL hω hα n t).eq
  have h := (R.continuous.tendsto
    (physicalZeroBoundaryEvolution U hd ω lam L hL hω t f)).comp
      (tendsto_physicalZeroBoundaryYosidaEvolution U hd ω lam L hL hω t f)
  simp only [Function.comp_def] at h
  simp_rw [← he] at h
  exact tendsto_nhds_unique
    (tendsto_physicalZeroBoundaryYosidaEvolution U hd ω lam L hL hω t (R f)) h

/-- Every actual physical weak part-generator pair is a right derivative pair of the constructed evolution. -/
theorem IsPhysicalZeroBoundaryGeneratorPair.tendsto_evolution_slope {d : ℕ}
    {U : Set (Vec d)} {hd : 2 ≤ d} {ω : FieldPair d} {lam L : ℝ}
    {hω : IsRegular L ω} {f g : physicalZeroBoundaryL2 U hd ω lam L hω}
    (hfg : IsPhysicalZeroBoundaryGeneratorPair U hd ω lam L hω f g) (hL : 1 ≤ L) :
    Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ •
      (physicalZeroBoundaryEvolution U hd ω lam L hL hω t f - f))
      (𝓝[>] (0 : ℝ≥0)) (𝓝 g) := by
  have he := (isPhysicalZeroBoundaryGeneratorPair_iff_resolvent U hd ω lam L hL hω f g).mp hfg
  have h := tendsto_physicalZeroBoundaryEvolution_slope_resolvent U hd ω lam L hL hω (f-g)
  simpa only [he, sub_sub_cancel] using h

/-- The full infinitesimal generator of the constructed physical part evolution is
exactly the literal zero-boundary physical weak-form graph. -/
theorem tendsto_physicalZeroBoundaryEvolution_slope_iff {d : ℕ}
    (U : Set (Vec d)) (hd : 2 ≤ d) (ω : FieldPair d) (lam L : ℝ)
    (hL : 1 ≤ L) (hω : IsRegular L ω)
    (f g : physicalZeroBoundaryL2 U hd ω lam L hω) :
    Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ •
      (physicalZeroBoundaryEvolution U hd ω lam L hL hω t f - f))
      (𝓝[>] (0 : ℝ≥0)) (𝓝 g) ↔
      IsPhysicalZeroBoundaryGeneratorPair U hd ω lam L hω f g := by
  constructor
  · intro hfg
    let R := physicalInteriorResolventEnd U hd ω lam L 1 hL hω zero_lt_one
    have he (t : ℝ≥0) : R (physicalZeroBoundaryEvolution U hd ω lam L hL hω t f) =
        physicalZeroBoundaryEvolution U hd ω lam L hL hω t (R f) :=
      (physicalZeroBoundaryEvolution_resolvent_comm U hd ω lam L 1 hL hω zero_lt_one t f).symm
    have hR := (R.continuous.tendsto g).comp hfg
    simp only [Function.comp_def] at hR
    simp_rw [map_smul, map_sub, he] at hR
    have hr := tendsto_physicalZeroBoundaryEvolution_slope_resolvent U hd ω lam L hL hω f
    have hid : R g = R f - f := tendsto_nhds_unique hR hr
    apply (isPhysicalZeroBoundaryGeneratorPair_iff_resolvent U hd ω lam L hL hω f g).mpr
    change R (f-g) = f
    rw [map_sub, hid, sub_sub_cancel]
  · intro hfg
    exact hfg.tendsto_evolution_slope hL

/-- The original zero-boundary graph value, with codomain its actual physical L² closure. -/
def physicalZeroBoundaryInteriorValue {d : ℕ} (U : Set (Vec d)) (hd : 2 ≤ d)
    (ω : FieldPair d) (lam L : ℝ) (hω : IsRegular L ω) :
    physicalH1ZeroBoundary U hd lam →L[ℝ] physicalZeroBoundaryL2 U hd ω lam L hω :=
  (physicalZeroBoundaryValue U hd ω lam L hω).codRestrict _
    (physicalZeroBoundaryValue_mem_L2 U hd ω lam L hω)

/-- The graph values are dense by the literal definition of the physical interior space. -/
theorem denseRange_physicalZeroBoundaryInteriorValue {d : ℕ}
    (U : Set (Vec d)) (hd : 2 ≤ d) (ω : FieldPair d) (lam L : ℝ)
    (hω : IsRegular L ω) : DenseRange (physicalZeroBoundaryInteriorValue U hd ω lam L hω) := by
  intro f
  rw [closure_subtype]
  have he : Subtype.val '' Set.range (physicalZeroBoundaryInteriorValue U hd ω lam L hω) =
      Set.range (physicalZeroBoundaryValue U hd ω lam L hω) := by
    ext y
    constructor
    · rintro ⟨v, ⟨u, rfl⟩, rfl⟩
      exact ⟨u, rfl⟩
    · rintro ⟨u, rfl⟩
      exact ⟨physicalZeroBoundaryInteriorValue U hd ω lam L hω u, ⟨u, rfl⟩, rfl⟩
  rw [he]
  exact f.property

/-- Both locally equal physical fields give the same physical pairing of interior graph values. -/
theorem physicalZeroBoundaryInteriorValue_inner_eq_of_physical_eqOn {d : ℕ}
    (U : Set (Vec d)) (hU : MeasurableSet U) (hd : 2 ≤ d) (ω ω' : FieldPair d)
    (heq : ∀ x ∈ U, ω.1 x = ω'.1 x ∧ ω.2 x = ω'.2 x) (lam L L' : ℝ)
    (hω : IsRegular L ω) (hω' : IsRegular L' ω') (u v : physicalH1ZeroBoundary U hd lam) :
    inner ℝ (physicalZeroBoundaryInteriorValue U hd ω lam L hω u)
      (physicalZeroBoundaryInteriorValue U hd ω lam L hω v) =
    inner ℝ (physicalZeroBoundaryInteriorValue U hd ω' lam L' hω' u)
      (physicalZeroBoundaryInteriorValue U hd ω' lam L' hω' v) := by
  change inner ℝ (physicalZeroBoundaryValue U hd ω lam L hω u)
      (physicalZeroBoundaryValue U hd ω lam L hω v) =
    inner ℝ (physicalZeroBoundaryValue U hd ω' lam L' hω' u)
      (physicalZeroBoundaryValue U hd ω' lam L' hω' v)
  exact (physicalValue_inner_eq_integral hd ω lam L hω u.1 v.1).trans
    ((physicalZeroBoundaryValuePairing_eq_of_physical_eqOn U hU ω ω' heq hd lam
      (densityWeightedH1SpaceValue u.1) v).trans
      (physicalValue_inner_eq_integral hd ω' lam L' hω' u.1 v.1).symm)

private theorem physicalInteriorValue_norm_eq {d : ℕ}
    (U : Set (Vec d)) (hU : MeasurableSet U) (hd : 2 ≤ d) (ω ω' : FieldPair d)
    (heq : ∀ x ∈ U, ω.1 x = ω'.1 x ∧ ω.2 x = ω'.2 x) (lam L L' : ℝ)
    (hω : IsRegular L ω) (hω' : IsRegular L' ω') (u : physicalH1ZeroBoundary U hd lam) :
    ‖physicalZeroBoundaryInteriorValue U hd ω' lam L' hω' u‖ =
      ‖physicalZeroBoundaryInteriorValue U hd ω lam L hω u‖ := by
  have hi := physicalZeroBoundaryInteriorValue_inner_eq_of_physical_eqOn
    U hU hd ω ω' heq lam L L' hω hω' u u
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hi
  nlinarith only [hi, norm_nonneg (physicalZeroBoundaryInteriorValue U hd ω lam L hω u),
    norm_nonneg (physicalZeroBoundaryInteriorValue U hd ω' lam L' hω' u)]

/-- The canonical physical interior L² identification extends the SAME actual graph values.
It is an isometry because both speed measures agree on the domain. -/
def physicalZeroBoundaryLocalIsometry {d : ℕ}
    (U : Set (Vec d)) (hU : MeasurableSet U) (hd : 2 ≤ d) (ω ω' : FieldPair d)
    (heq : ∀ x ∈ U, ω.1 x = ω'.1 x ∧ ω.2 x = ω'.2 x) (lam L L' : ℝ)
    (hω : IsRegular L ω) (hω' : IsRegular L' ω') :
    physicalZeroBoundaryL2 U hd ω lam L hω ≃ₗᵢ[ℝ]
      physicalZeroBoundaryL2 U hd ω' lam L' hω' :=
  (LinearEquiv.refl ℝ (physicalH1ZeroBoundary U hd lam)).extendOfIsometry
    (physicalZeroBoundaryInteriorValue U hd ω lam L hω).toLinearMap
    (physicalZeroBoundaryInteriorValue U hd ω' lam L' hω').toLinearMap
    (denseRange_physicalZeroBoundaryInteriorValue U hd ω lam L hω)
    (denseRange_physicalZeroBoundaryInteriorValue U hd ω' lam L' hω')
    (physicalInteriorValue_norm_eq U hU hd ω ω' heq lam L L' hω hω')

/-- The canonical comparison sends each graph value to the value of that very same graph. -/
theorem physicalZeroBoundaryLocalIsometry_value {d : ℕ}
    (U : Set (Vec d)) (hU : MeasurableSet U) (hd : 2 ≤ d) (ω ω' : FieldPair d)
    (heq : ∀ x ∈ U, ω.1 x = ω'.1 x ∧ ω.2 x = ω'.2 x) (lam L L' : ℝ)
    (hω : IsRegular L ω) (hω' : IsRegular L' ω') (u : physicalH1ZeroBoundary U hd lam) :
    physicalZeroBoundaryLocalIsometry U hU hd ω ω' heq lam L L' hω hω'
      (physicalZeroBoundaryInteriorValue U hd ω lam L hω u) =
        physicalZeroBoundaryInteriorValue U hd ω' lam L' hω' u :=
  LinearEquiv.extendOfIsometry_eq _ _ _ _ _ _ u

private theorem physicalInteriorPairing_local {d : ℕ}
    (U : Set (Vec d)) (hU : MeasurableSet U) (hd : 2 ≤ d) (ω ω' : FieldPair d)
    (heq : ∀ x ∈ U, ω.1 x = ω'.1 x ∧ ω.2 x = ω'.2 x) (lam L L' : ℝ)
    (hω : IsRegular L ω) (hω' : IsRegular L' ω')
    (f : physicalZeroBoundaryL2 U hd ω lam L hω) (v : physicalH1ZeroBoundary U hd lam) :
    inner ℝ (physicalZeroBoundaryLocalIsometry U hU hd ω ω' heq lam L L' hω hω' f).val
      (physicalZeroBoundaryValue U hd ω' lam L' hω' v) =
        inner ℝ f.val (physicalZeroBoundaryValue U hd ω lam L hω v) := by
  let T := physicalZeroBoundaryLocalIsometry U hU hd ω ω' heq lam L L' hω hω'
  have hv := physicalZeroBoundaryLocalIsometry_value U hU hd ω ω' heq lam L L' hω hω' v
  change inner ℝ (T f) (physicalZeroBoundaryInteriorValue U hd ω' lam L' hω' v) =
    inner ℝ f (physicalZeroBoundaryInteriorValue U hd ω lam L hω v)
  rw [← hv]
  exact T.inner_map_map _ _

private theorem physicalZeroBoundaryBilinear_local {d : ℕ}
    (U : Set (Vec d)) (hU : MeasurableSet U) (hd : 2 ≤ d) (ω ω' : FieldPair d)
    (heq : ∀ x ∈ U, ω.1 x = ω'.1 x ∧ ω.2 x = ω'.2 x) (lam L L' α : ℝ)
    (hL : 1 ≤ L) (hL' : 1 ≤ L') (hω : IsRegular L ω) (hω' : IsRegular L' ω')
    (hα : 0 < α) (u v : physicalH1ZeroBoundary U hd lam) :
    physicalZeroBoundaryBilinear U hd ω lam L α hL hω hα u v =
      physicalZeroBoundaryBilinear U hd ω' lam L' α hL' hω' hα u v := by
  exact (physicalZeroBoundaryBilinear_eq_inner U hd ω lam L α hL hω hα u v).trans
    ((congrArg₂ (· + ·)
      (congrArg (α * ·) (physicalZeroBoundaryInteriorValue_inner_eq_of_physical_eqOn
        U hU hd ω ω' heq lam L L' hω hω' u v))
      (physicalWeightedForm_eq_on_zeroBoundary U hU ω ω' heq hd lam u.1 v.1 u.property)).trans
      (physicalZeroBoundaryBilinear_eq_inner U hd ω' lam L' α hL' hω' hα u v).symm)

/-- The actual variational solutions agree under the canonical comparison of physical L² data. -/
theorem physicalZeroBoundaryResolventGraph_localIsometry {d : ℕ}
    (U : Set (Vec d)) (hU : MeasurableSet U) (hd : 2 ≤ d) (ω ω' : FieldPair d)
    (heq : ∀ x ∈ U, ω.1 x = ω'.1 x ∧ ω.2 x = ω'.2 x) (lam L L' α : ℝ)
    (hL : 1 ≤ L) (hL' : 1 ≤ L') (hω : IsRegular L ω) (hω' : IsRegular L' ω')
    (hα : 0 < α) (f : physicalZeroBoundaryL2 U hd ω lam L hω) :
    physicalZeroBoundaryResolventGraph U hd ω' lam L' α hL' hω' hα
      (physicalZeroBoundaryLocalIsometry U hU hd ω ω' heq lam L L' hω hω' f).val =
        physicalZeroBoundaryResolventGraph U hd ω lam L α hL hω hα f.val := by
  symm
  apply variationalResolventGraph_unique
    (physicalZeroBoundaryBilinear U hd ω' lam L' α hL' hω' hα)
    (physicalZeroBoundaryBilinear_isCoercive U hd ω' lam L' α hL' hω' hα)
    (physicalZeroBoundaryValue U hd ω' lam L' hω') _ _
  intro v
  exact (physicalZeroBoundaryBilinear_local U hU hd ω ω' heq lam L L' α hL hL' hω hω' hα
    (physicalZeroBoundaryResolventGraph U hd ω lam L α hL hω hα f.val) v).symm.trans
    ((physicalZeroBoundaryResolventGraph_bilinear U hd ω lam L α hL hω hα f.val v).trans
      (physicalInteriorPairing_local U hU hd ω ω' heq lam L L' hω hω' f v).symm)

/-- Every positive actual interior resolvent intertwines the canonical physical comparison. -/
theorem physicalZeroBoundaryInteriorResolvent_localIsometry {d : ℕ}
    (U : Set (Vec d)) (hU : MeasurableSet U) (hd : 2 ≤ d) (ω ω' : FieldPair d)
    (heq : ∀ x ∈ U, ω.1 x = ω'.1 x ∧ ω.2 x = ω'.2 x) (lam L L' α : ℝ)
    (hL : 1 ≤ L) (hL' : 1 ≤ L') (hω : IsRegular L ω) (hω' : IsRegular L' ω')
    (hα : 0 < α) (f : physicalZeroBoundaryL2 U hd ω lam L hω) :
    physicalZeroBoundaryLocalIsometry U hU hd ω ω' heq lam L L' hω hω'
      (physicalZeroBoundaryInteriorResolvent U hd ω lam L α hL hω hα f.val) =
    physicalZeroBoundaryInteriorResolvent U hd ω' lam L' α hL' hω' hα
      (physicalZeroBoundaryLocalIsometry U hU hd ω ω' heq lam L L' hω hω' f).val := by
  change physicalZeroBoundaryLocalIsometry U hU hd ω ω' heq lam L L' hω hω'
    (physicalZeroBoundaryInteriorValue U hd ω lam L hω
      (physicalZeroBoundaryResolventGraph U hd ω lam L α hL hω hα f.val)) =
    physicalZeroBoundaryInteriorValue U hd ω' lam L' hω'
      (physicalZeroBoundaryResolventGraph U hd ω' lam L' α hL' hω' hα _)
  rw [physicalZeroBoundaryLocalIsometry_value,
    physicalZeroBoundaryResolventGraph_localIsometry U hU hd ω ω' heq lam L L' α hL hL' hω hω' hα f]

/-- The restricted physical Yosida generator has the literal interior resolvent formula. -/
theorem physicalZeroBoundaryPartYosida_apply {d : ℕ}
    (U : Set (Vec d)) (hd : 2 ≤ d) (ω : FieldPair d) (lam L : ℝ)
    (hL : 1 ≤ L) (hω : IsRegular L ω) (n : ℕ)
    (f : physicalZeroBoundaryL2 U hd ω lam L hω) :
    physicalZeroBoundaryPartYosida U hd ω lam L hL hω n f =
      ((n : ℝ)+1) • (((n : ℝ)+1) •
        physicalZeroBoundaryInteriorResolvent U hd ω lam L ((n : ℝ)+1) hL hω (by positivity) f.val - f) := by
  apply Subtype.ext
  rfl

/-- Locally equal physical fields intertwine all actual restricted Yosida generators. -/
theorem physicalZeroBoundaryPartYosida_localIsometry {d : ℕ}
    (U : Set (Vec d)) (hU : MeasurableSet U) (hd : 2 ≤ d) (ω ω' : FieldPair d)
    (heq : ∀ x ∈ U, ω.1 x = ω'.1 x ∧ ω.2 x = ω'.2 x) (lam L L' : ℝ)
    (hL : 1 ≤ L) (hL' : 1 ≤ L') (hω : IsRegular L ω) (hω' : IsRegular L' ω')
    (n : ℕ) (f : physicalZeroBoundaryL2 U hd ω lam L hω) :
    physicalZeroBoundaryLocalIsometry U hU hd ω ω' heq lam L L' hω hω'
      (physicalZeroBoundaryPartYosida U hd ω lam L hL hω n f) =
    physicalZeroBoundaryPartYosida U hd ω' lam L' hL' hω' n
      (physicalZeroBoundaryLocalIsometry U hU hd ω ω' heq lam L L' hω hω' f) := by
  rw [physicalZeroBoundaryPartYosida_apply, map_smul, map_sub, map_smul,
    physicalZeroBoundaryInteriorResolvent_localIsometry U hU hd ω ω' heq lam L L'
      ((n : ℝ)+1) hL hL' hω hω' (by positivity) f,
    physicalZeroBoundaryPartYosida_apply]

private theorem isometry_intertwines_exp {H K : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup K] [NormedSpace ℝ K]
    (e : H ≃ₗᵢ[ℝ] K) (A : H →L[ℝ] H) (B : K →L[ℝ] K)
    (h : ∀ f, e (A f) = B (e f)) (t : ℝ) (f : H) :
    e (NormedSpace.exp (t • A) f) = NormedSpace.exp (t • B) (e f) := by
  let Φ : (H →L[ℝ] H) →+* (K →L[ℝ] K) :=
    { toFun := fun C => e.toContinuousLinearEquiv.toContinuousLinearMap.comp
        (C.comp e.symm.toContinuousLinearEquiv.toContinuousLinearMap)
      map_zero' := by ext x; simp
      map_one' := by ext x; simp
      map_add' := by intro C D; ext x; simp
      map_mul' := by intro C D; ext x; simp }
  have hcont : Continuous Φ := by
    change Continuous (fun C : H →L[ℝ] H =>
      e.toContinuousLinearEquiv.toContinuousLinearMap.comp
        (C.comp e.symm.toContinuousLinearEquiv.toContinuousLinearMap))
    fun_prop
  have hΦ : Φ (t • A) = t • B := by
    ext x
    change e (t • A (e.symm x)) = t • B x
    rw [map_smul, h, e.apply_symm_apply]
  have hx := congrArg (fun C : K →L[ℝ] K => C (e f))
    (NormedSpace.map_exp Φ hcont (t • A))
  rw [hΦ] at hx
  simpa only [Φ, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, e.symm_apply_apply] using hx

/-- Locally equal physical fields intertwine their actual Yosida evolutions at every real time. -/
theorem physicalZeroBoundaryYosidaEvolution_localIsometry {d : ℕ}
    (U : Set (Vec d)) (hU : MeasurableSet U) (hd : 2 ≤ d) (ω ω' : FieldPair d)
    (heq : ∀ x ∈ U, ω.1 x = ω'.1 x ∧ ω.2 x = ω'.2 x) (lam L L' : ℝ)
    (hL : 1 ≤ L) (hL' : 1 ≤ L') (hω : IsRegular L ω) (hω' : IsRegular L' ω')
    (n : ℕ) (t : ℝ) (f : physicalZeroBoundaryL2 U hd ω lam L hω) :
    physicalZeroBoundaryLocalIsometry U hU hd ω ω' heq lam L L' hω hω'
      (physicalZeroBoundaryYosidaEvolution U hd ω lam L hL hω n t f) =
    physicalZeroBoundaryYosidaEvolution U hd ω' lam L' hL' hω' n t
      (physicalZeroBoundaryLocalIsometry U hU hd ω ω' heq lam L L' hω hω' f) :=
  isometry_intertwines_exp
    (physicalZeroBoundaryLocalIsometry U hU hd ω ω' heq lam L L' hω hω')
    (physicalZeroBoundaryPartYosida U hd ω lam L hL hω n)
    (physicalZeroBoundaryPartYosida U hd ω' lam L' hL' hω' n)
    (physicalZeroBoundaryPartYosida_localIsometry U hU hd ω ω' heq lam L L' hL hL' hω hω' n) t f

/-- The constructed physical interior C0 evolutions depend only on both fields inside the domain,
under the canonical isometry extending their identical zero-boundary graph values. -/
theorem physicalZeroBoundaryEvolution_localIsometry {d : ℕ}
    (U : Set (Vec d)) (hU : MeasurableSet U) (hd : 2 ≤ d) (ω ω' : FieldPair d)
    (heq : ∀ x ∈ U, ω.1 x = ω'.1 x ∧ ω.2 x = ω'.2 x) (lam L L' : ℝ)
    (hL : 1 ≤ L) (hL' : 1 ≤ L') (hω : IsRegular L ω) (hω' : IsRegular L' ω')
    (t : ℝ≥0) (f : physicalZeroBoundaryL2 U hd ω lam L hω) :
    physicalZeroBoundaryLocalIsometry U hU hd ω ω' heq lam L L' hω hω'
      (physicalZeroBoundaryEvolution U hd ω lam L hL hω t f) =
    physicalZeroBoundaryEvolution U hd ω' lam L' hL' hω' t
      (physicalZeroBoundaryLocalIsometry U hU hd ω ω' heq lam L L' hω hω' f) := by
  let T := physicalZeroBoundaryLocalIsometry U hU hd ω ω' heq lam L L' hω hω'
  have h := (T.continuous.tendsto
    (physicalZeroBoundaryEvolution U hd ω lam L hL hω t f)).comp
      (tendsto_physicalZeroBoundaryYosidaEvolution U hd ω lam L hL hω t f)
  simp only [Function.comp_def, T] at h
  simp_rw [physicalZeroBoundaryYosidaEvolution_localIsometry
    U hU hd ω ω' heq lam L L' hL hL' hω hω'] at h
  exact tendsto_nhds_unique h
    (tendsto_physicalZeroBoundaryYosidaEvolution U hd ω' lam L' hL' hω' t (T f))

/-- The canonical local comparison preserves and reflects the ENTIRE actual physical weak generator. -/
theorem isPhysicalZeroBoundaryGeneratorPair_localIsometry_iff {d : ℕ}
    (U : Set (Vec d)) (hU : MeasurableSet U) (hd : 2 ≤ d) (ω ω' : FieldPair d)
    (heq : ∀ x ∈ U, ω.1 x = ω'.1 x ∧ ω.2 x = ω'.2 x) (lam L L' : ℝ)
    (hL : 1 ≤ L) (hL' : 1 ≤ L') (hω : IsRegular L ω) (hω' : IsRegular L' ω')
    (f g : physicalZeroBoundaryL2 U hd ω lam L hω) :
    IsPhysicalZeroBoundaryGeneratorPair U hd ω' lam L' hω'
      (physicalZeroBoundaryLocalIsometry U hU hd ω ω' heq lam L L' hω hω' f)
      (physicalZeroBoundaryLocalIsometry U hU hd ω ω' heq lam L L' hω hω' g) ↔
    IsPhysicalZeroBoundaryGeneratorPair U hd ω lam L hω f g := by
  let T := physicalZeroBoundaryLocalIsometry U hU hd ω ω' heq lam L L' hω hω'
  rw [isPhysicalZeroBoundaryGeneratorPair_iff_resolvent U hd ω' lam L' hL' hω',
    isPhysicalZeroBoundaryGeneratorPair_iff_resolvent U hd ω lam L hL hω]
  have he := physicalZeroBoundaryInteriorResolvent_localIsometry
    U hU hd ω ω' heq lam L L' 1 hL hL' hω hω' zero_lt_one (f-g)
  rw [map_sub] at he
  change physicalZeroBoundaryInteriorResolvent U hd ω' lam L' 1 hL' hω' zero_lt_one
    (T f - T g : physicalZeroBoundaryL2 U hd ω' lam L' hω') = T f ↔ _
  rw [← he]
  exact T.injective.eq_iff

end

end EinsteinFull
