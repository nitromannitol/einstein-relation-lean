import EinsteinRelation.Calculus.WeightedH1QuotientSupport
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Order.Filter.Tendsto
import Mathlib.Topology.Sequences

open MeasureTheory
open Filter
open scoped ENNReal InnerProductSpace Topology

namespace EinsteinRelation.SpatialDirichlet

noncomputable section

def densityWeightedMeasure {d : ℕ} (ρ : Vec d → ℝ) : Measure (Vec d) :=
  volume.withDensity (fun x => ENNReal.ofReal (ρ x))

/-- Local finiteness implies finite mass on compact sets by a finite cover. -/
private theorem finiteOnCompacts_of_locallyFinite {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X]
    {m : Measure X} [IsLocallyFiniteMeasure m] : IsFiniteMeasureOnCompacts m := by
  refine ⟨?_⟩
  intro K hK
  let U : K → Set X := fun x => Classical.choose (m.exists_isOpen_measure_lt_top x.1)
  have hU : ∀ x : K, (x : X) ∈ U x ∧ IsOpen (U x) ∧ m (U x) < ∞ := by
    intro x
    exact Classical.choose_spec (m.exists_isOpen_measure_lt_top x.1)
  have hcover : K ⊆ ⋃ x : K, U x := by
    intro x hx
    exact Set.mem_iUnion.2 ⟨⟨x, hx⟩, (hU ⟨x, hx⟩).1⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover U (fun x => (hU x).2.1) hcover
  calc
    m K ≤ m (⋃ x ∈ t, U x) := measure_mono ht
    _ ≤ ∑ x ∈ t, m (U x) := measure_biUnion_finset_le t U
    _ < ∞ := ENNReal.sum_lt_top.mpr (fun x hx => (hU x).2.2)

theorem densityWeightedMeasure_locallyFinite {d : ℕ} (ρ : Vec d → ℝ)
    (hρ : Continuous ρ) : IsLocallyFiniteMeasure (densityWeightedMeasure ρ) := by
  letI : IsLocallyFiniteMeasure (volume : Measure (Vec d)) := inferInstance
  exact IsLocallyFiniteMeasure.withDensity_ofReal hρ

private theorem densityWeightedMeasure_finiteOnCompacts {d : ℕ} (ρ : Vec d → ℝ)
    (hρ : Continuous ρ) : IsFiniteMeasureOnCompacts (densityWeightedMeasure ρ) := by
  letI := densityWeightedMeasure_locallyFinite ρ hρ
  exact finiteOnCompacts_of_locallyFinite

/-- A positive continuous density turns a smooth compact test into a weighted `L²` test
after division by the density. -/
private theorem weightedTest_memLp {d : ℕ} (ρ : Vec d → ℝ)
    (hρ : Continuous ρ) (hρpos : ∀ x, 0 < ρ x)
    {φ : Vec d → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ) :
    MemLp (fun x => φ x / ρ x) 2 (densityWeightedMeasure ρ) := by
  letI := densityWeightedMeasure_finiteOnCompacts ρ hρ
  have hq : Continuous (fun x => φ x / ρ x) :=
    hφ.mul (hρ.inv₀ fun x => ne_of_gt (hρpos x))
  have hqc : HasCompactSupport (fun x => φ x / ρ x) := by
    apply hφc.mono'
    intro x hx
    by_contra hnot
    have hzero : φ x = 0 := image_eq_zero_of_notMem_tsupport hnot
    change φ x / ρ x ≠ 0 at hx
    simp [hzero] at hx
  exact hq.memLp_of_hasCompactSupport hqc

private def weightedScalarTest {d : ℕ} (ρ : Vec d → ℝ)
    (hρ : Continuous ρ) (hρpos : ∀ x, 0 < ρ x)
    (φ : Vec d → ℝ) (hφ : Continuous φ) (hφc : HasCompactSupport φ) :
    Lp ℝ 2 (densityWeightedMeasure ρ) :=
  (weightedTest_memLp ρ hρ hρpos hφ hφc).toLp (fun x => φ x / ρ x)

private theorem weightedScalarTest_pairing {d : ℕ} (ρ : Vec d → ℝ)
    (hρ : Continuous ρ) (hρpos : ∀ x, 0 < ρ x)
    {φ : Vec d → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (u : Lp ℝ 2 (densityWeightedMeasure ρ)) :
    inner ℝ u (weightedScalarTest ρ hρ hρpos φ hφ hφc) =
      ∫ x, u x * φ x ∂volume := by
  rw [L2.inner_def]
  change (∫ x, inner ℝ (u x)
      (weightedScalarTest ρ hρ hρpos φ hφ hφc x) ∂
        volume.withDensity (ENNReal.ofReal ∘ ρ)) = _
  have hfinite : ∀ᵐ x ∂volume, ENNReal.ofReal (ρ x) < ∞ := by
    filter_upwards [] with x
    simp
  rw [integral_withDensity_eq_integral_toReal_smul
    (ENNReal.measurable_ofReal.comp hρ.measurable) hfinite]
  · apply integral_congr_ae
    have hq := (weightedTest_memLp ρ hρ hρpos hφ hφc).coeFn_toLp
    have hqVol : weightedScalarTest ρ hρ hρpos φ hφ hφc =ᵐ[volume]
        fun x => φ x / ρ x := by
      exact (ae_withDensity_iff_volume_of_continuous_pos ρ hρ hρpos _).mp hq
    filter_upwards [hqVol] with x hx
    simp only [Function.comp_apply, ENNReal.toReal_ofReal (hρpos x).le,
      smul_eq_mul, RCLike.inner_apply]
    rw [hx]
    field_simp [ne_of_gt (hρpos x)]
    simp

private theorem weightedCoordinateTest_memLp {d : ℕ} (ρ : Vec d → ℝ)
    (hρ : Continuous ρ) (hρpos : ∀ x, 0 < ρ x)
    (i : Fin d) (φ : Vec d → ℝ) (hφ : Continuous φ) (hφc : HasCompactSupport φ) :
    MemLp (fun x => (φ x / ρ x) • (EuclideanSpace.single i (1 : ℝ))) 2
      (densityWeightedMeasure ρ) := by
  have hqcont : Continuous (fun x => φ x / ρ x) :=
    hφ.mul (hρ.inv₀ fun x => ne_of_gt (hρpos x))
  have hqcompact : HasCompactSupport (fun x => φ x / ρ x) := by
    apply hφc.mono'
    intro x hx
    by_contra hnot
    have hzero : φ x = 0 := image_eq_zero_of_notMem_tsupport hnot
    change φ x / ρ x ≠ 0 at hx
    simp [hzero] at hx
  have hfcont : Continuous (fun x => (φ x / ρ x) • (EuclideanSpace.single i (1 : ℝ))) :=
    hqcont.smul continuous_const
  have hfcompact : HasCompactSupport
      (fun x => (φ x / ρ x) • (EuclideanSpace.single i (1 : ℝ))) :=
    hqcompact.smul_right
  letI := densityWeightedMeasure_finiteOnCompacts ρ hρ
  exact hfcont.memLp_of_hasCompactSupport hfcompact

/-- The vector-valued weighted test selecting one Euclidean gradient coordinate. -/
private def weightedCoordinateTest {d : ℕ} (ρ : Vec d → ℝ)
    (hρ : Continuous ρ) (hρpos : ∀ x, 0 < ρ x)
    (i : Fin d) (φ : Vec d → ℝ) (hφ : Continuous φ) (hφc : HasCompactSupport φ) :
    Lp (EuclideanSpace ℝ (Fin d)) 2 (densityWeightedMeasure ρ) :=
  (weightedCoordinateTest_memLp ρ hρ hρpos i φ hφ hφc).toLp
    (fun x => (φ x / ρ x) • EuclideanSpace.single i (1 : ℝ))

private theorem weightedCoordinateTest_pairing {d : ℕ} (ρ : Vec d → ℝ)
    (hρ : Continuous ρ) (hρpos : ∀ x, 0 < ρ x)
    {i : Fin d} {φ : Vec d → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (u : Lp (EuclideanSpace ℝ (Fin d)) 2 (densityWeightedMeasure ρ)) :
    inner ℝ u (weightedCoordinateTest ρ hρ hρpos i φ hφ hφc) =
      ∫ x, (WithLp.ofLp (u x)) i * φ x ∂volume := by
  rw [L2.inner_def]
  change (∫ x, inner ℝ (u x)
      (weightedCoordinateTest ρ hρ hρpos i φ hφ hφc x) ∂
        volume.withDensity (ENNReal.ofReal ∘ ρ)) = _
  have hfinite : ∀ᵐ x ∂volume, ENNReal.ofReal (ρ x) < ∞ := by
    filter_upwards [] with x
    simp
  rw [integral_withDensity_eq_integral_toReal_smul
    (ENNReal.measurable_ofReal.comp hρ.measurable) hfinite]
  apply integral_congr_ae
  have hq := (weightedCoordinateTest_memLp ρ hρ hρpos i φ hφ hφc).coeFn_toLp
  have hqVol : weightedCoordinateTest ρ hρ hρpos i φ hφ hφc =ᵐ[volume]
      fun x => (φ x / ρ x) • EuclideanSpace.single i (1 : ℝ) := by
    exact (ae_withDensity_iff_volume_of_continuous_pos ρ hρ hρpos _).mp hq
  filter_upwards [hqVol] with x hx
  simp only [Function.comp_apply, ENNReal.toReal_ofReal (hρpos x).le,
    smul_eq_mul]
  rw [hx]
  simp only [inner_smul_right, EuclideanSpace.inner_single_right]
  field_simp [ne_of_gt (hρpos x)]
  simp

/-- The scalar weak-gradient residual on one compact test, represented as continuous `L²`
pairings in the weighted reference measure. -/
private def weightedWeakTestResidual {d : ℕ} (ρ : Vec d → ℝ)
    (hρ : Continuous ρ) (hρpos : ∀ x, 0 < ρ x)
    (i : Fin d) (φ : Vec d → ℝ) (hφ : IsSpatialTest Set.univ φ)
    (p : Lp ℝ 2 (densityWeightedMeasure ρ) ×
      Lp (EuclideanSpace ℝ (Fin d)) 2 (densityWeightedMeasure ρ)) : ℝ := by
  let hderivCont : Continuous (fun x => coordinateDerivative i φ x) := by
    change Continuous (fun x => fderiv ℝ φ x (unitVector i))
    exact (hφ.1.continuous_fderiv_apply (by simp)).comp
      (continuous_id.prodMk continuous_const)
  let hderivCompact : HasCompactSupport (fun x => coordinateDerivative i φ x) := by
    simpa only [coordinateDerivative] using
      HasCompactSupport.fderiv_apply (𝕜 := ℝ) (f := φ) hφ.2.1 (unitVector i)
  exact inner ℝ p.1
      (weightedScalarTest ρ hρ hρpos (coordinateDerivative i φ) hderivCont hderivCompact) +
    inner ℝ p.2 (weightedCoordinateTest ρ hρ hρpos i φ hφ.1.continuous hφ.2.1)

private theorem weightedWeakTestResidual_as_integrals {d : ℕ} (ρ : Vec d → ℝ)
    (hρ : Continuous ρ) (hρpos : ∀ x, 0 < ρ x)
    (i : Fin d) (φ : Vec d → ℝ) (hφ : IsSpatialTest Set.univ φ)
    (p : Lp ℝ 2 (densityWeightedMeasure ρ) ×
      Lp (EuclideanSpace ℝ (Fin d)) 2 (densityWeightedMeasure ρ)) :
    weightedWeakTestResidual ρ hρ hρpos i φ hφ p =
      (∫ x, p.1 x * coordinateDerivative i φ x ∂volume) +
      (∫ x, (WithLp.ofLp (p.2 x)) i * φ x ∂volume) := by
  let hderivCont : Continuous (fun x => coordinateDerivative i φ x) := by
    change Continuous (fun x => fderiv ℝ φ x (unitVector i))
    exact (hφ.1.continuous_fderiv_apply (by simp)).comp
      (continuous_id.prodMk continuous_const)
  let hderivCompact : HasCompactSupport (fun x => coordinateDerivative i φ x) := by
    simpa only [coordinateDerivative] using
      HasCompactSupport.fderiv_apply (𝕜 := ℝ) (f := φ) hφ.2.1 (unitVector i)
  change inner ℝ p.1
      (weightedScalarTest ρ hρ hρpos (coordinateDerivative i φ) hderivCont hderivCompact) +
    inner ℝ p.2 (weightedCoordinateTest ρ hρ hρpos i φ hφ.1.continuous hφ.2.1) = _
  rw [weightedScalarTest_pairing ρ hρ hρpos hderivCont hderivCompact p.1,
    weightedCoordinateTest_pairing ρ hρ hρpos hφ.1.continuous hφ.2.1 p.2]

private theorem weightedWeakTestResidual_add {d : ℕ} (ρ : Vec d → ℝ)
    (hρ : Continuous ρ) (hρpos : ∀ x, 0 < ρ x)
    (i : Fin d) (φ : Vec d → ℝ) (hφ : IsSpatialTest Set.univ φ)
    (p q : Lp ℝ 2 (densityWeightedMeasure ρ) ×
      Lp (EuclideanSpace ℝ (Fin d)) 2 (densityWeightedMeasure ρ)) :
    weightedWeakTestResidual ρ hρ hρpos i φ hφ (p + q) =
      weightedWeakTestResidual ρ hρ hρpos i φ hφ p +
        weightedWeakTestResidual ρ hρ hρpos i φ hφ q := by
  simp [weightedWeakTestResidual, inner_add_left]
  ring

private theorem weightedWeakTestResidual_smul {d : ℕ} (ρ : Vec d → ℝ)
    (hρ : Continuous ρ) (hρpos : ∀ x, 0 < ρ x)
    (i : Fin d) (φ : Vec d → ℝ) (hφ : IsSpatialTest Set.univ φ)
    (c : ℝ) (p : Lp ℝ 2 (densityWeightedMeasure ρ) ×
      Lp (EuclideanSpace ℝ (Fin d)) 2 (densityWeightedMeasure ρ)) :
    weightedWeakTestResidual ρ hρ hρpos i φ hφ (c • p) =
      c * weightedWeakTestResidual ρ hρ hρpos i φ hφ p := by
  simp [weightedWeakTestResidual, inner_smul_left]
  ring

private theorem continuous_weightedWeakTestResidual {d : ℕ} (ρ : Vec d → ℝ)
    (hρ : Continuous ρ) (hρpos : ∀ x, 0 < ρ x)
    (i : Fin d) (φ : Vec d → ℝ) (hφ : IsSpatialTest Set.univ φ) :
    Continuous (weightedWeakTestResidual ρ hρ hρpos i φ hφ) := by
  let hderivCont : Continuous (fun x => coordinateDerivative i φ x) := by
    change Continuous (fun x => fderiv ℝ φ x (unitVector i))
    exact (hφ.1.continuous_fderiv_apply (by simp)).comp
      (continuous_id.prodMk continuous_const)
  let hderivCompact : HasCompactSupport (fun x => coordinateDerivative i φ x) := by
    simpa only [coordinateDerivative] using
      HasCompactSupport.fderiv_apply (𝕜 := ℝ) (f := φ) hφ.2.1 (unitVector i)
  change Continuous (fun p : Lp ℝ 2 (densityWeightedMeasure ρ) ×
      Lp (EuclideanSpace ℝ (Fin d)) 2 (densityWeightedMeasure ρ) =>
    inner ℝ p.1 (weightedScalarTest ρ hρ hρpos (coordinateDerivative i φ)
      hderivCont hderivCompact) +
      inner ℝ p.2 (weightedCoordinateTest ρ hρ hρpos i φ hφ.1.continuous hφ.2.1))
  exact (continuous_fst.inner continuous_const).add (continuous_snd.inner continuous_const)

/-- The exact distributional test constraints in weighted `L² × L²(ℝᵈ)`. -/
def densityWeightedWeakGraphSet {d : ℕ} (ρ : Vec d → ℝ)
    (hρ : Continuous ρ) (hρpos : ∀ x, 0 < ρ x) :
    Set (Lp ℝ 2 (densityWeightedMeasure ρ) ×
      Lp (EuclideanSpace ℝ (Fin d)) 2 (densityWeightedMeasure ρ)) :=
  {p | ∀ i : Fin d, ∀ φ : Vec d → ℝ, ∀ hφ : IsSpatialTest Set.univ φ,
    weightedWeakTestResidual ρ hρ hρpos i φ hφ p = 0}

/-- The concrete value-gradient pair represented by the existing weighted graph carrier. -/
def densityWeightedGraphPair {d : ℕ} (ρ : Vec d → ℝ)
    (u : WeightedSobolevGraph (densityWeightedMeasure ρ)) :
    Lp ℝ 2 (densityWeightedMeasure ρ) ×
      Lp (EuclideanSpace ℝ (Fin d)) 2 (densityWeightedMeasure ρ) :=
  (u.value_memLp.toLp u.value, u.gradient_memLp.toLp u.weakGradient)

private theorem densityWeighted_toLp_coe_ae_volume {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (ρ : Vec d → ℝ)
    (hρ : Continuous ρ) (hρpos : ∀ x, 0 < ρ x) {f : Vec d → E}
    (hf : MemLp f 2 (densityWeightedMeasure ρ)) : hf.toLp f =ᵐ[volume] f :=
  (ae_withDensity_iff_volume_of_continuous_pos ρ hρ hρpos _).mp hf.coeFn_toLp

theorem densityWeightedGraphPair_mem_weakGraphSet {d : ℕ} (ρ : Vec d → ℝ)
    (hρ : Continuous ρ) (hρpos : ∀ x, 0 < ρ x)
    (u : WeightedSobolevGraph (densityWeightedMeasure ρ)) :
    densityWeightedGraphPair ρ u ∈ densityWeightedWeakGraphSet ρ hρ hρpos := by
  intro i φ hφ
  have hderivCont : Continuous (fun x => coordinateDerivative i φ x) := by
    change Continuous (fun x => fderiv ℝ φ x (unitVector i))
    exact (hφ.1.continuous_fderiv_apply (by simp)).comp
      (continuous_id.prodMk continuous_const)
  have hderivCompact : HasCompactSupport (fun x => coordinateDerivative i φ x) := by
    simpa only [coordinateDerivative] using
      HasCompactSupport.fderiv_apply (𝕜 := ℝ) (f := φ) hφ.2.1 (unitVector i)
  have hpv : (densityWeightedGraphPair ρ u).1 =ᵐ[volume] u.value :=
    densityWeighted_toLp_coe_ae_volume ρ hρ hρpos u.value_memLp
  have hpg : (densityWeightedGraphPair ρ u).2 =ᵐ[volume] u.weakGradient :=
    densityWeighted_toLp_coe_ae_volume ρ hρ hρpos u.gradient_memLp
  have hvalueIntegral :
      (∫ x, (densityWeightedGraphPair ρ u).1 x * coordinateDerivative i φ x ∂volume) =
        ∫ x, u.value x * coordinateDerivative i φ x ∂volume := by
    apply integral_congr_ae
    filter_upwards [hpv] with x hx
    rw [hx]
  have hgradientIntegral :
      (∫ x, (WithLp.ofLp ((densityWeightedGraphPair ρ u).2 x)) i * φ x ∂volume) =
        ∫ x, (WithLp.ofLp (u.weakGradient x)) i * φ x ∂volume := by
    apply integral_congr_ae
    filter_upwards [hpg] with x hx
    rw [hx]
  rw [weightedWeakTestResidual_as_integrals ρ hρ hρpos i φ hφ,
    hvalueIntegral, hgradientIntegral]
  have hweak := (u.distributionalGradient i).2.2 φ hφ
  have hweak' :
      (∫ x, u.value x * coordinateDerivative i φ x ∂volume) =
        -(∫ x, (WithLp.ofLp (u.weakGradient x)) i * φ x ∂volume) := by
    simpa only [setIntegral_univ] using hweak
  linarith

/-- A pair satisfying all continuous compact-test constraints is an actual weak-gradient graph.
The local integrability required by the weak derivative is derived from weighted `L²`. -/
def densityWeightedGraphOfPair {d : ℕ} (ρ : Vec d → ℝ)
    (hρ : Continuous ρ) (hρpos : ∀ x, 0 < ρ x)
    (p : Lp ℝ 2 (densityWeightedMeasure ρ) ×
      Lp (EuclideanSpace ℝ (Fin d)) 2 (densityWeightedMeasure ρ))
    (hp : p ∈ densityWeightedWeakGraphSet ρ hρ hρpos) :
    WeightedSobolevGraph (densityWeightedMeasure ρ) := by
  letI : IsLocallyFiniteMeasure (volume : Measure (Vec d)) := inferInstance
  letI : IsLocallyFiniteMeasure (densityWeightedMeasure ρ) :=
    densityWeightedMeasure_locallyFinite ρ hρ
  have hMeasureLocal : IsLocallyFiniteMeasure (densityWeightedMeasure ρ) :=
    densityWeightedMeasure_locallyFinite ρ hρ
  have hValueLocal : LocallyIntegrable p.1 volume :=
    memLp_two_locallyIntegrable_volume_of_density ρ hρ hρpos p.1 hMeasureLocal
      (Lp.memLp p.1)
  have hGradientLocal : LocallyIntegrable p.2 volume :=
    memLp_two_locallyIntegrable_volume_of_density ρ hρ hρpos p.2 hMeasureLocal
      (Lp.memLp p.2)
  have hValueOn : LocallyIntegrableOn p.1 Set.univ volume :=
    locallyIntegrableOn_univ.mpr hValueLocal
  have hGradientAEStrongly : AEStronglyMeasurable p.2 volume :=
    hGradientLocal.aestronglyMeasurable
  refine {
    value := p.1
    weakGradient := p.2
    value_memLp := Lp.memLp p.1
    gradient_memLp := Lp.memLp p.2
    distributionalGradient := ?_
  }
  intro i
  have hCoordinateContinuous :
      Continuous (fun z : EuclideanSpace ℝ (Fin d) => (WithLp.ofLp z) i) :=
    (continuous_apply i).comp (PiLp.continuous_ofLp 2 _)
  have hCoordinateAEStrongly : AEStronglyMeasurable
      (fun x => (WithLp.ofLp (p.2 x)) i) volume :=
    hCoordinateContinuous.comp_aestronglyMeasurable hGradientAEStrongly
  have hCoordinateNorm : ∀ x,
      ‖(WithLp.ofLp (p.2 x)) i‖ ≤ ‖p.2 x‖ := by
    intro x
    simpa using (PiLp.norm_apply_le (p.2 x) i)
  have hCoordinateLocal : LocallyIntegrable
      (fun x => (WithLp.ofLp (p.2 x)) i) volume :=
    hGradientLocal.mono hCoordinateAEStrongly (ae_of_all _ hCoordinateNorm)
  have hCoordinateOn : LocallyIntegrableOn
      (fun x => (WithLp.ofLp (p.2 x)) i) Set.univ volume :=
    locallyIntegrableOn_univ.mpr hCoordinateLocal
  refine ⟨hValueOn, hCoordinateOn, ?_⟩
  intro φ hφ
  have hconstraint := hp i φ hφ
  rw [weightedWeakTestResidual_as_integrals ρ hρ hρpos i φ hφ] at hconstraint
  have hidentity :
      (∫ x, p.1 x * coordinateDerivative i φ x ∂volume) =
        -(∫ x, (WithLp.ofLp (p.2 x)) i * φ x ∂volume) := by
    linarith
  simpa only [setIntegral_univ] using hidentity

theorem densityWeightedGraphPair_graphOfPair {d : ℕ} (ρ : Vec d → ℝ)
    (hρ : Continuous ρ) (hρpos : ∀ x, 0 < ρ x)
    (p : Lp ℝ 2 (densityWeightedMeasure ρ) ×
      Lp (EuclideanSpace ℝ (Fin d)) 2 (densityWeightedMeasure ρ))
    (hp : p ∈ densityWeightedWeakGraphSet ρ hρ hρpos) :
    densityWeightedGraphPair ρ (densityWeightedGraphOfPair ρ hρ hρpos p hp) = p := by
  apply Prod.ext
  · apply Lp.ext
    exact (Lp.memLp p.1).coeFn_toLp
  · apply Lp.ext
    exact (Lp.memLp p.2).coeFn_toLp

theorem densityWeightedGraphPair_range_eq_weakGraphSet {d : ℕ} (ρ : Vec d → ℝ)
    (hρ : Continuous ρ) (hρpos : ∀ x, 0 < ρ x) :
    Set.range (densityWeightedGraphPair ρ) = densityWeightedWeakGraphSet ρ hρ hρpos := by
  ext p
  constructor
  · rintro ⟨u, rfl⟩
    exact densityWeightedGraphPair_mem_weakGraphSet ρ hρ hρpos u
  · intro hp
    exact ⟨densityWeightedGraphOfPair ρ hρ hρpos p hp,
      densityWeightedGraphPair_graphOfPair ρ hρ hρpos p hp⟩

/-- The exact weighted weak-gradient pairs form a linear subspace of weighted `L² × L²`. -/
def densityWeightedWeakGraphSubmodule {d : ℕ} (ρ : Vec d → ℝ)
    (hρ : Continuous ρ) (hρpos : ∀ x, 0 < ρ x) :
    Submodule ℝ (Lp ℝ 2 (densityWeightedMeasure ρ) ×
      Lp (EuclideanSpace ℝ (Fin d)) 2 (densityWeightedMeasure ρ)) where
  carrier := densityWeightedWeakGraphSet ρ hρ hρpos
  zero_mem' := by
    intro i φ hφ
    simp [weightedWeakTestResidual]
  add_mem' := by
    intro p q hp hq i φ hφ
    rw [weightedWeakTestResidual_add ρ hρ hρpos i φ hφ p q,
      hp i φ hφ, hq i φ hφ]
    simp
  smul_mem' := by
    intro c p hp i φ hφ
    rw [weightedWeakTestResidual_smul ρ hρ hρpos i φ hφ c p,
      hp i φ hφ]
    simp

theorem densityWeightedWeakGraphSet_isClosed {d : ℕ} (ρ : Vec d → ℝ)
    (hρ : Continuous ρ) (hρpos : ∀ x, 0 < ρ x) :
    IsClosed (densityWeightedWeakGraphSet ρ hρ hρpos) := by
  rw [← isSeqClosed_iff_isClosed]
  intro seq p hseq hlim i φ hφ
  have hres : Filter.Tendsto (fun n => weightedWeakTestResidual ρ hρ hρpos i φ hφ (seq n))
      atTop (𝓝 (weightedWeakTestResidual ρ hρ hρpos i φ hφ p)) :=
    ((continuous_weightedWeakTestResidual ρ hρ hρpos i φ hφ).tendsto p).comp hlim
  have hzero : Filter.Tendsto
      (fun n => weightedWeakTestResidual ρ hρ hρpos i φ hφ (seq n)) atTop (𝓝 0) := by
    have hconst : (fun n => weightedWeakTestResidual ρ hρ hρpos i φ hφ (seq n)) =
        fun _ => (0 : ℝ) := by
      funext n
      exact hseq n i φ hφ
    rw [hconst]
    exact tendsto_const_nhds
  have heq := tendsto_nhds_unique hres hzero
  exact heq

theorem densityWeightedWeakGraphSet_isComplete {d : ℕ} (ρ : Vec d → ℝ)
    (hρ : Continuous ρ) (hρpos : ∀ x, 0 < ρ x) :
    IsComplete (densityWeightedWeakGraphSet ρ hρ hρpos) := by
  exact (densityWeightedWeakGraphSet_isClosed ρ hρ hρpos).isComplete

theorem densityWeightedWeakGraphSubmodule_isClosed {d : ℕ} (ρ : Vec d → ℝ)
    (hρ : Continuous ρ) (hρpos : ∀ x, 0 < ρ x) :
    IsClosed (densityWeightedWeakGraphSubmodule ρ hρ hρpos : Set
      (Lp ℝ 2 (densityWeightedMeasure ρ) ×
        Lp (EuclideanSpace ℝ (Fin d)) 2 (densityWeightedMeasure ρ))) := by
  exact densityWeightedWeakGraphSet_isClosed ρ hρ hρpos

theorem densityWeightedWeakGraphSubmodule_limit_of_tendsto {d : ℕ}
    (ρ : Vec d → ℝ) (hρ : Continuous ρ) (hρpos : ∀ x, 0 < ρ x)
    {seq : ℕ → Lp ℝ 2 (densityWeightedMeasure ρ) ×
      Lp (EuclideanSpace ℝ (Fin d)) 2 (densityWeightedMeasure ρ)}
    {p : Lp ℝ 2 (densityWeightedMeasure ρ) ×
      Lp (EuclideanSpace ℝ (Fin d)) 2 (densityWeightedMeasure ρ)}
    (hseq : ∀ n, seq n ∈ densityWeightedWeakGraphSubmodule ρ hρ hρpos)
    (hlim : Filter.Tendsto seq atTop (𝓝 p)) :
    p ∈ densityWeightedWeakGraphSubmodule ρ hρ hρpos := by
  have hclosed := densityWeightedWeakGraphSubmodule_isClosed ρ hρ hρpos
  rw [← isSeqClosed_iff_isClosed] at hclosed
  exact hclosed (x := seq) (p := p) hseq hlim

theorem densityWeightedWeakGraphSubmodule_isComplete {d : ℕ} (ρ : Vec d → ℝ)
    (hρ : Continuous ρ) (hρpos : ∀ x, 0 < ρ x) :
    IsComplete (densityWeightedWeakGraphSubmodule ρ hρ hρpos : Set
      (Lp ℝ 2 (densityWeightedMeasure ρ) ×
        Lp (EuclideanSpace ℝ (Fin d)) 2 (densityWeightedMeasure ρ))) := by
  exact (densityWeightedWeakGraphSubmodule_isClosed ρ hρ hρpos).isComplete

theorem densityWeightedGraphPair_range_isClosed {d : ℕ} (ρ : Vec d → ℝ)
    (hρ : Continuous ρ) (hρpos : ∀ x, 0 < ρ x) :
    IsClosed (Set.range (densityWeightedGraphPair ρ)) := by
  rw [densityWeightedGraphPair_range_eq_weakGraphSet ρ hρ hρpos]
  exact densityWeightedWeakGraphSet_isClosed ρ hρ hρpos

theorem densityWeightedGraphPair_range_isComplete {d : ℕ} (ρ : Vec d → ℝ)
    (hρ : Continuous ρ) (hρpos : ∀ x, 0 < ρ x) :
    IsComplete (Set.range (densityWeightedGraphPair ρ)) := by
  rw [densityWeightedGraphPair_range_eq_weakGraphSet ρ hρ hρpos]
  exact densityWeightedWeakGraphSet_isComplete ρ hρ hρpos

/-- The quotient graph map reuses the value and gradient projections of the established
weighted `H¹` quotient. -/
noncomputable def densityWeightedH1GraphPair {d : ℕ} (ρ : Vec d → ℝ)
    (hρ : Continuous ρ) (hρpos : ∀ x, 0 < ρ x) :
    DensityWeightedH1 ρ →
      Lp ℝ 2 (densityWeightedMeasure ρ) ×
        Lp (EuclideanSpace ℝ (Fin d)) 2 (densityWeightedMeasure ρ) :=
  fun q => (densityWeightedH1Value ρ q, densityWeightedH1Gradient ρ hρ hρpos q)

theorem densityWeightedH1GraphPair_quotient_mk {d : ℕ} (ρ : Vec d → ℝ)
    (hρ : Continuous ρ) (hρpos : ∀ x, 0 < ρ x)
    (u : WeightedSobolevGraph (densityWeightedMeasure ρ)) :
    densityWeightedH1GraphPair ρ hρ hρpos
      (Quotient.mk (densityWeightedH1Setoid ρ) u) = densityWeightedGraphPair ρ u := by
  apply Prod.ext
  · rfl
  · rfl

theorem densityWeightedH1GraphPair_range {d : ℕ} (ρ : Vec d → ℝ)
    (hρ : Continuous ρ) (hρpos : ∀ x, 0 < ρ x) :
    Set.range (densityWeightedH1GraphPair ρ hρ hρpos) =
      densityWeightedWeakGraphSet ρ hρ hρpos := by
  rw [← densityWeightedGraphPair_range_eq_weakGraphSet ρ hρ hρpos]
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    refine Quotient.inductionOn q ?_
    intro u
    exact ⟨u, rfl⟩
  · rintro ⟨u, rfl⟩
    exact ⟨Quotient.mk (densityWeightedH1Setoid ρ) u, rfl⟩

theorem densityWeightedH1GraphPair_range_isComplete {d : ℕ} (ρ : Vec d → ℝ)
    (hρ : Continuous ρ) (hρpos : ∀ x, 0 < ρ x) :
    IsComplete (Set.range (densityWeightedH1GraphPair ρ hρ hρpos)) := by
  rw [densityWeightedH1GraphPair_range ρ hρ hρpos]
  exact densityWeightedWeakGraphSet_isComplete ρ hρ hρpos


end

end EinsteinRelation.SpatialDirichlet
