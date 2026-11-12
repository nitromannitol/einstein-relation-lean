import EinsteinRelation.Environment.Basic
import EinsteinRelation.Environment.Reduction
import EinsteinRelation.Diffusion.Basic
import EinsteinRelation.Calculus.WeightedH1QuotientSupport
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Probability.Kernel.Basic
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Topology.List

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped ENNReal NNReal Topology

noncomputable section

namespace EinsteinRelation.External.GantertSection7Support

instance {d : ℕ} : MeasurableSpace (List (Vec d)) := borel (List (Vec d))
instance {d : ℕ} : BorelSpace (List (Vec d)) := ⟨rfl⟩

/-- The force direction fixed by the manuscript, represented in coordinates. -/
def firstCoordinateIndex {d : ℕ} (hd : 2 ≤ d) : Fin d :=
  ⟨0, Nat.lt_of_lt_of_le (by decide : 0 < 2) hd⟩

/-- The density `ρ_λ² = exp(2 λ x₁)` used in the cited weighted Sobolev space. -/
def physicalForceWeight {d : ℕ} (hd : 2 ≤ d) (lam : ℝ) (x : Vec d) : ℝ :=
  Real.exp (2 * lam * x (firstCoordinateIndex hd))

def physicalForceMeasure {d : ℕ} (hd : 2 ≤ d) (lam : ℝ) : Measure (Vec d) :=
  volume.withDensity (fun x => ENNReal.ofReal (physicalForceWeight hd lam x))

/-- The physical reversible density `exp(2 λ x₁ - 2 V(x))`. -/
def physicalReversibleDensity {d : ℕ} (ω : FieldPair d) (hd : 2 ≤ d)
    (lam : ℝ) (x : Vec d) : ℝ :=
  physicalForceWeight hd lam x * clockDensity ω x

/-- The unnormalized physical reversible measure in the fixed-environment form. -/
def physicalReversibleMeasure {d : ℕ} (ω : FieldPair d) (hd : 2 ≤ d) (lam : ℝ) :
    Measure (Vec d) :=
  volume.withDensity (fun x => ENNReal.ofReal (physicalReversibleDensity ω hd lam x))

theorem physicalForceWeight_continuous {d : ℕ} (hd : 2 ≤ d) (lam : ℝ) :
    Continuous (physicalForceWeight hd lam) := by
  change Continuous (fun x : Vec d => Real.exp (2 * lam * x (firstCoordinateIndex hd)))
  exact Real.continuous_exp.comp
    (continuous_const.mul (continuous_apply (firstCoordinateIndex hd)))

theorem physicalForceWeight_pos {d : ℕ} (hd : 2 ≤ d) (lam : ℝ) (x : Vec d) :
    0 < physicalForceWeight hd lam x :=
  Real.exp_pos _

theorem physicalReversibleDensity_eq_source_formula {d : ℕ} (ω : FieldPair d)
    (hd : 2 ≤ d) (lam : ℝ) (x : Vec d) :
    physicalReversibleDensity ω hd lam x =
      Real.exp (2 * lam * x (firstCoordinateIndex hd) - 2 * ω.2 x) := by
  simp [physicalReversibleDensity, physicalForceWeight, clockDensity, ← Real.exp_add]
  ring

/-- The source Dirichlet energy on an actual representative in the weighted weak-gradient graph.
The integrand includes the source factor `1/2`. -/
noncomputable def physicalH1FormEnergy {d : ℕ} (ω : FieldPair d) (hd : 2 ≤ d)
    (lam : ℝ) (u : SpatialDirichlet.WeightedSobolevGraph
      (physicalForceMeasure hd lam)) : ℝ :=
  ∫ x, SpatialDirichlet.weightedFormIntegrand ω.1 u u x
    ∂physicalReversibleMeasure ω hd lam

/-- The source weighted `H¹(ρ_λ²)` domain, represented by its actual quotient value. -/
def physicalH1Member {d : ℕ} (ω : FieldPair d) (hd : 2 ≤ d)
    (lam : ℝ) (f : Vec d → ℝ) : Prop :=
  ∃ q : SpatialDirichlet.DensityWeightedH1 (physicalForceWeight hd lam),
    SpatialDirichlet.densityWeightedH1Value (physicalForceWeight hd lam) q =ᵐ[
      physicalReversibleMeasure ω hd lam] f

/-- The short-time quadratic form of the transition semigroup in the physical measure. -/
def semigroupFormDifferenceQuotient {d : ℕ} (ω : FieldPair d) (hd : 2 ≤ d)
    (lam : ℝ) (K : ℝ≥0 → Kernel (Vec d) (Vec d)) (t : ℝ≥0) (f : Vec d → ℝ) : ℝ :=
  (1 / (t : ℝ)) * ∫ x,
    (f x - ∫ y, f y ∂K t x) * f x ∂physicalReversibleMeasure ω hd lam

/-- Accumulated times of a finite sequence of nonnegative time increments. -/
def cumulativeTimesFrom (s : ℝ≥0) : List ℝ≥0 → List ℝ≥0
  | [] => []
  | t :: ts => (s + t) :: cumulativeTimesFrom (s + t) ts

def cumulativeTimes (increments : List ℝ≥0) : List ℝ≥0 :=
  cumulativeTimesFrom 0 increments

/-- The ordered coordinate tuple of a continuous path at the accumulated times. -/
def pathPositionsAtTimes {d : ℕ} (times : List ℝ≥0) (γ : Path d) : List (Vec d) :=
  times.map (fun t => pathPosition t γ)

theorem measurable_pathPositionsAtTimes {d : ℕ} (times : List ℝ≥0) :
    Measurable (fun γ : Path d => pathPositionsAtTimes times γ) := by
  induction times with
  | nil => exact measurable_const
  | cons t ts ih =>
      change Measurable (fun γ : Path d =>
        pathPosition t γ :: pathPositionsAtTimes ts γ)
      exact List.continuous_cons.measurable.comp
        ((measurable_pathPosition t).prodMk ih)

/-- The finite-dimensional transition law written as its iterated kernel integral. -/
def iteratedMarkovCylinderIntegral {d : ℕ} (K : ℝ≥0 → Kernel (Vec d) (Vec d)) :
    List ℝ≥0 → (List (Vec d) → ℝ) → Vec d → ℝ
  | [], F, _ => F []
  | t :: ts, F, x =>
      ∫ y, iteratedMarkovCylinderIntegral K ts (fun ys => F (y :: ys)) y ∂K t x

/-- Ergodicity of the induced translation action on the joint field law, modulo null sets. -/
def IsTranslationErgodic {d : ℕ} (Q : Measure (FieldPair d)) : Prop :=
  ∀ A : Set (FieldPair d), MeasurableSet A →
    (∀ z : Vec d, ∀ᵐ ω ∂Q, (translate z ω ∈ A ↔ ω ∈ A)) →
    Q A = 0 ∨ Q A = 1

/-- A fixed-environment realization of the cited Section 7 heat-kernel construction and
Lemma 7.1. Each witness carries the actual path law, transition kernels, heat-kernel density,
and full closed-form identification for this environment and force. -/
structure GantertFixedEnvironmentRealization {d : ℕ} (hd : 2 ≤ d)
    (Λ₀ : ℝ) (hΛ₀ : 1 ≤ Λ₀) (ω : FieldPair d)
    (hω : IsRegular Λ₀ ω) (lam : ℝ) (hlam : 0 ≤ lam) (hlam_le_one : lam ≤ 1) where
  /-- The continuous-path law indexed by every spatial starting point. -/
  pathLaw : Kernel (Vec d) (Path d)
  /-- The transition kernels of the weak-operator semigroup. -/
  transitionKernel : ℝ≥0 → Kernel (Vec d) (Vec d)
  /-- The heat-kernel density `p^{λ,ω}(t,x,y)` at positive time. -/
  heatKernel : ℝ≥0 → Vec d → Vec d → ℝ≥0∞
  pathLaw_isMarkovKernel : IsMarkovKernel pathLaw
  transitionKernel_isMarkovKernel : ∀ t, IsMarkovKernel (transitionKernel t)
  transitionKernel_zero : transitionKernel 0 = Kernel.id
  transitionKernel_add : ∀ s t,
    transitionKernel (s + t) = transitionKernel t ∘ₖ transitionKernel s
  /-- Detailed balance for the source reversible measure. -/
  transitionKernel_reversible : ∀ t (A B : Set (Vec d)), MeasurableSet A →
    MeasurableSet B →
      (∫⁻ x in A, transitionKernel t x B ∂physicalReversibleMeasure ω hd lam) =
        (∫⁻ x in B, transitionKernel t x A ∂physicalReversibleMeasure ω hd lam)
  /-- The process starts at the displayed spatial point. -/
  pathLaw_starts_at : ∀ x, ∀ᵐ γ ∂pathLaw x, pathPosition 0 γ = x
  /-- The heat kernel is measurable in its endpoint variable at positive time. -/
  heatKernel_aeMeasurable : ∀ t, 0 < t → ∀ x,
    AEMeasurable (fun y => heatKernel t x y) (volume : Measure (Vec d))
  /-- The transition kernel has the cited heat-kernel density for every positive time. -/
  transitionKernel_eq_heatKernel : ∀ t, 0 < t → ∀ x,
    transitionKernel t x = volume.withDensity (fun y => heatKernel t x y)
  /-- The actual path law has these transition kernels as all one-time marginals. -/
  pathLaw_endpoint : ∀ t x,
    (pathLaw x).map (pathPosition t) = transitionKernel t x
  /-- Ordered finite-dimensional distributions of the continuous-path law are the
  iterated transition-kernel laws. Increments encode every finite nondecreasing time tuple. -/
  pathLaw_ordered_finite_dimensional : ∀ (increments : List ℝ≥0) (x : Vec d)
      (F : List (Vec d) → ℝ),
    Measurable F → (∃ B : ℝ, ∀ z, |F z| ≤ B) →
      (∫ γ, F (pathPositionsAtTimes (cumulativeTimes increments) γ)
        ∂pathLaw x) =
        iteratedMarkovCylinderIntegral transitionKernel increments F x
  /-- The full semigroup form domain is exactly the source weighted `H¹` domain: boundedness
  of the approximating forms over all positive times is equivalent to membership. -/
  closedForm_domain : ∀ f, MemLp f 2 (physicalReversibleMeasure ω hd lam) →
    ((∃ C : ℝ, ∀ t : ℝ≥0, 0 < t →
      semigroupFormDifferenceQuotient ω hd lam transitionKernel t f ≤ C) ↔
      physicalH1Member ω hd lam f)
  /-- On the entire weighted `H¹` domain, the semigroup form limit equals the source energy. -/
  closedForm_value : ∀ (f : Vec d → ℝ)
      (q : SpatialDirichlet.DensityWeightedH1 (physicalForceWeight hd lam)),
    SpatialDirichlet.densityWeightedH1Value (physicalForceWeight hd lam) q =ᵐ[
      physicalReversibleMeasure ω hd lam] f →
    ∀ u : SpatialDirichlet.WeightedSobolevGraph (physicalForceMeasure hd lam),
      u.value =ᵐ[physicalReversibleMeasure ω hd lam] f →
      Tendsto
        (fun t : ℝ≥0 => semigroupFormDifferenceQuotient ω hd lam
          transitionKernel t f)
        (𝓝[Set.Ioi 0] (0 : ℝ≥0))
        (𝓝 (physicalH1FormEnergy ω hd lam u))

end EinsteinRelation.External.GantertSection7Support
