import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.Instances.Matrix
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.Calculus.FDeriv.Basic
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Calculus.Generator
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Calculus.Weak
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Calculus.WeightedFormIntegrabilitySupport
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Environment.Basic
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Environment.Reduction

/-! Vocabulary for `EinsteinRelation.Calculus.WeightedH1QuotientSupport`: the declarations of that library module which the challenge statements use, copied verbatim in their context. -/

open MeasureTheory

open scoped ENNReal InnerProductSpace

namespace EinsteinRelation.SpatialDirichlet

noncomputable section

/-- Weighted `L²` membership for a strictly positive continuous density implies local
integrability against Lebesgue measure. -/
theorem memLp_two_locallyIntegrable_volume_of_density {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (ρ : Vec d → ℝ)
    (hρ : Continuous ρ) (hρpos : ∀ x, 0 < ρ x) (f : Vec d → E)
    (hμlf : IsLocallyFiniteMeasure
      (volume.withDensity (fun x => ENNReal.ofReal (ρ x))))
    (hf : MemLp f 2 (volume.withDensity (fun x => ENNReal.ofReal (ρ x)))) :
    LocallyIntegrable f volume := by
  let w : Vec d → ℝ≥0∞ := fun x => ENNReal.ofReal (ρ x)
  let μ : Measure (Vec d) := volume.withDensity w
  letI : IsLocallyFiniteMeasure μ := hμlf
  have hwmeas : Measurable w := ENNReal.measurable_ofReal.comp hρ.measurable
  intro x
  let K : Set (Vec d) := Metric.closedBall x 1
  have hK : IsCompact K := by simpa [K] using (isCompact_closedBall x (1 : ℝ))
  have hKnonempty : K.Nonempty := ⟨x, by simp [K]⟩
  obtain ⟨z, hzK, hzmin⟩ := hK.exists_isMinOn hKnonempty hρ.continuousOn
  have hzmin' : ∀ y ∈ K, ρ z ≤ ρ y := by
    simpa [IsMinOn, IsMinFilter] using hzmin
  let c : ℝ := ρ z / 2
  have hc : 0 < c := by
    dsimp [c]
    linarith [hρpos z]
  have hcρ : ∀ y ∈ K, c ≤ ρ y := by
    intro y hy
    dsimp [c]
    have hmin := hzmin' y hy
    linarith [hρpos z]
  have hKfin : μ K < ∞ := hK.measure_lt_top
  have hKlp : MemLp f 2 (μ.restrict K) := hf.restrict K
  letI : IsFiniteMeasure (μ.restrict K) := ⟨by simpa using hKfin⟩
  have hKlp1 : MemLp f 1 (μ.restrict K) :=
    hKlp.mono_exponent (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hKint : Integrable f (μ.restrict K) := by
    rw [← memLp_one_iff_integrable]
    exact hKlp1
  have hKmeas : MeasurableSet K := hK.isClosed.measurableSet
  have hKint' : Integrable f ((volume.restrict K).withDensity w) := by
    change Integrable f ((volume.withDensity w).restrict K) at hKint
    rw [restrict_withDensity hKmeas] at hKint
    exact hKint
  have hwfinite : ∀ᵐ y ∂volume.restrict K, w y < ∞ := by
    filter_upwards [] with y
    simp [w]
  have hweighted : Integrable (fun y => (w y).toReal • f y) (volume.restrict K) :=
    (integrable_withDensity_iff_integrable_smul' hwmeas hwfinite).mp hKint'
  have hweightedρ : Integrable (fun y => ρ y • f y) (volume.restrict K) := by
    refine hweighted.congr ?_
    filter_upwards [] with y
    simp [w, ENNReal.toReal_ofReal, (hρpos y).le]
  have hinvCont : Continuous (fun y => (ρ y)⁻¹) :=
    hρ.inv₀ (fun y => ne_of_gt (hρpos y))
  have hinvMeas : AEStronglyMeasurable (fun y => (ρ y)⁻¹) (volume.restrict K) :=
    hinvCont.measurable.aestronglyMeasurable
  have hinvBound : ∀ᵐ y ∂volume.restrict K, ‖(ρ y)⁻¹‖ ≤ c⁻¹ := by
    filter_upwards [ae_restrict_mem hKmeas] with y hy
    have hρy : c ≤ ρ y := hcρ y hy
    calc
      ‖(ρ y)⁻¹‖ = (ρ y)⁻¹ := by
        rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hρpos y))]
      _ ≤ c⁻¹ := by simpa only [one_div] using one_div_le_one_div_of_le hc hρy
  have hKvolumeInt : Integrable f (volume.restrict K) := by
    refine (hweightedρ.bdd_smul c⁻¹ hinvMeas hinvBound).congr ?_
    filter_upwards [] with y
    simp [smul_smul, inv_mul_cancel₀ (ne_of_gt (hρpos y))]
  have hKnhds : K ∈ nhds x := by
    apply Filter.mem_of_superset (Metric.ball_mem_nhds x (by norm_num : (0 : ℝ) < 1))
    intro y hy
    have hy' : dist y x < (1 : ℝ) := by
      simpa [Metric.mem_ball, dist_comm] using hy
    simpa [K, Metric.mem_closedBall, dist_comm] using hy'.le
  exact ⟨K, hKnhds, hKvolumeInt⟩

/-- The existing weak-gradient graph is exactly inhabited by the source data consisting of
weighted `L²` representatives and the compact-test distributional identity. Its local
integrability fields are derived from weighted `L²` and positivity of the density. -/
noncomputable def weightedSobolevGraph_mk_of_density_distributionalData {d : ℕ}
    (ρ : Vec d → ℝ) (hρ : Continuous ρ) (hρpos : ∀ x, 0 < ρ x)
    (u : Vec d → ℝ) (g : Vec d → EuclideanSpace ℝ (Fin d))
    (hu : MemLp u 2 (volume.withDensity (fun x => ENNReal.ofReal (ρ x))))
    (hg : MemLp g 2 (volume.withDensity (fun x => ENNReal.ofReal (ρ x))))
    (hidentity : ∀ i : Fin d, ∀ φ : Vec d → ℝ, IsSpatialTest Set.univ φ →
      (∫ x in Set.univ, u x * coordinateDerivative i φ x) =
        -(∫ x in Set.univ, (WithLp.ofLp (g x)) i * φ x)) :
    WeightedSobolevGraph
      (volume.withDensity (fun x => ENNReal.ofReal (ρ x))) := by
  letI : IsLocallyFiniteMeasure
      (volume.withDensity (fun x => ENNReal.ofReal (ρ x))) :=
    IsLocallyFiniteMeasure.withDensity_ofReal hρ
  have huLocal := memLp_two_locallyIntegrable_volume_of_density ρ hρ hρpos u
    (inferInstance : IsLocallyFiniteMeasure
      (volume.withDensity (fun x => ENNReal.ofReal (ρ x)))) hu
  have hgLocal := memLp_two_locallyIntegrable_volume_of_density ρ hρ hρpos g
    (inferInstance : IsLocallyFiniteMeasure
      (volume.withDensity (fun x => ENNReal.ofReal (ρ x)))) hg
  have huOn : LocallyIntegrableOn u Set.univ volume := locallyIntegrableOn_univ.mpr huLocal
  have hgAestrongly : AEStronglyMeasurable g volume := hgLocal.aestronglyMeasurable
  refine ⟨u, g, hu, hg, ?_⟩
  intro i
  have hcoordinateContinuous : Continuous
      (fun z : EuclideanSpace ℝ (Fin d) => (WithLp.ofLp z) i) :=
    (continuous_apply i).comp (PiLp.continuous_ofLp 2 _)
  have hcoordinateAestrongly : AEStronglyMeasurable
      (fun x => (WithLp.ofLp (g x)) i) volume :=
    hcoordinateContinuous.comp_aestronglyMeasurable hgAestrongly
  have hcoordinateNorm : ∀ x, ‖(WithLp.ofLp (g x)) i‖ ≤ ‖g x‖ := by
    intro x
    simpa using (PiLp.norm_apply_le (g x) i)
  have hcoordinateLocal : LocallyIntegrable
      (fun x => (WithLp.ofLp (g x)) i) volume :=
    hgLocal.mono hcoordinateAestrongly (ae_of_all _ hcoordinateNorm)
  have hcoordinateOn : LocallyIntegrableOn
      (fun x => (WithLp.ofLp (g x)) i) Set.univ volume :=
    locallyIntegrableOn_univ.mpr hcoordinateLocal
  exact ⟨huOn, hcoordinateOn, hidentity i⟩

/-- The weak `H¹` quotient identifies graph representatives with the same weighted `L²` value. -/
def densityWeightedH1Setoid {d : ℕ} (ρ : Vec d → ℝ) :
    Setoid (WeightedSobolevGraph
      (volume.withDensity (fun x => ENNReal.ofReal (ρ x)))) where
  r u v := u.value =ᵐ[volume.withDensity (fun x => ENNReal.ofReal (ρ x))] v.value
  iseqv := {
    refl := fun _ => Filter.EventuallyEq.rfl
    symm := fun {_ _} h => h.symm
    trans := fun {_ _ _} h₁ h₂ => h₁.trans h₂
  }

/-- Equivalence classes of the weighted weak-gradient graph. -/
abbrev DensityWeightedH1 {d : ℕ} (ρ : Vec d → ℝ) :=
  Quotient (densityWeightedH1Setoid ρ)

/-- The weighted `L²` value represented by an equivalence class. -/
noncomputable def densityWeightedH1Value {d : ℕ} (ρ : Vec d → ℝ) :
    DensityWeightedH1 ρ → Lp ℝ 2
      (volume.withDensity (fun x => ENNReal.ofReal (ρ x))) :=
  Quotient.lift (fun u => u.value_memLp.toLp u.value) (by
    intro u v huv
    apply Lp.ext
    have hu := u.value_memLp.coeFn_toLp
    have hv := v.value_memLp.coeFn_toLp
    filter_upwards [hu, huv, hv] with x hu hx hv
    exact hu.trans (hx.trans hv.symm))

end

end EinsteinRelation.SpatialDirichlet
