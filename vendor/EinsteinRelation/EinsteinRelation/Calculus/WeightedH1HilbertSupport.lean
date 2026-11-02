import EinsteinRelation.Calculus.WeightedH1ClosedGraphSupport
import Mathlib.Analysis.InnerProductSpace.ProdL2

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace EinsteinRelation.SpatialDirichlet

noncomputable section

/-- The Hilbert product carrying a weighted value and its Euclidean weak gradient. -/
abbrev DensityWeightedH1Ambient {d : ℕ} (ρ : Vec d → ℝ) :=
  WithLp 2 (Lp ℝ 2 (densityWeightedMeasure ρ) ×
    Lp (EuclideanSpace ℝ (Fin d)) 2 (densityWeightedMeasure ρ))

/-- The full weighted `H¹` graph, equipped with the genuine L² product norm. -/
def densityWeightedH1Submodule {d : ℕ} (ρ : Vec d → ℝ)
    (hρ : Continuous ρ) (hρpos : ∀ x, 0 < ρ x) :
    Submodule ℝ (DensityWeightedH1Ambient ρ) :=
  (densityWeightedWeakGraphSubmodule ρ hρ hρpos).comap
    (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).toLinearEquiv.toLinearMap

theorem densityWeightedH1GraphPair_injective {d : ℕ} (ρ : Vec d → ℝ)
    (hρ : Continuous ρ) (hρpos : ∀ x, 0 < ρ x) :
    Function.Injective (densityWeightedH1GraphPair ρ hρ hρpos) := by
  intro q q' h
  apply densityWeightedH1Value_injective ρ
  exact congrArg Prod.fst h

theorem densityWeightedH1Submodule_isClosed {d : ℕ} (ρ : Vec d → ℝ)
    (hρ : Continuous ρ) (hρpos : ∀ x, 0 < ρ x) :
    IsClosed (densityWeightedH1Submodule ρ hρ hρpos :
      Set (DensityWeightedH1Ambient ρ)) := by
  change IsClosed ((WithLp.prodContinuousLinearEquiv 2 ℝ _ _ :
    DensityWeightedH1Ambient ρ ≃L[ℝ] _).toFun ⁻¹'
      (densityWeightedWeakGraphSubmodule ρ hρ hρpos : Set _))
  exact (densityWeightedWeakGraphSubmodule_isClosed ρ hρ hρpos).preimage
    (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).continuous

instance densityWeightedH1Submodule_completeSpace {d : ℕ} (ρ : Vec d → ℝ)
    (hρ : Continuous ρ) (hρpos : ∀ x, 0 < ρ x) :
    CompleteSpace (densityWeightedH1Submodule ρ hρ hρpos) :=
  (densityWeightedH1Submodule_isClosed ρ hρ hρpos).completeSpace_coe

/-- A quotient class is represented by its unique weighted value-gradient pair. -/
def densityWeightedH1GraphEmbedding {d : ℕ} (ρ : Vec d → ℝ)
    (hρ : Continuous ρ) (hρpos : ∀ x, 0 < ρ x)
    (q : DensityWeightedH1 ρ) : densityWeightedH1Submodule ρ hρ hρpos := by
  refine ⟨(WithLp.prodContinuousLinearEquiv 2 ℝ _ _).symm
    (densityWeightedH1GraphPair ρ hρ hρpos q), ?_⟩
  change densityWeightedH1GraphPair ρ hρ hρpos q ∈
    densityWeightedWeakGraphSet ρ hρ hρpos
  rw [← densityWeightedH1GraphPair_range ρ hρ hρpos]
  exact ⟨q, rfl⟩

theorem densityWeightedH1GraphEmbedding_injective {d : ℕ} (ρ : Vec d → ℝ)
    (hρ : Continuous ρ) (hρpos : ∀ x, 0 < ρ x) :
    Function.Injective (densityWeightedH1GraphEmbedding ρ hρ hρpos) := by
  intro q q' h
  apply densityWeightedH1GraphPair_injective ρ hρ hρpos
  have hp := congrArg (fun u : densityWeightedH1Submodule ρ hρ hρpos =>
    (WithLp.prodContinuousLinearEquiv 2 ℝ _ _ :
      DensityWeightedH1Ambient ρ ≃L[ℝ] _).toFun u) h
  simpa [densityWeightedH1GraphEmbedding] using hp

theorem densityWeightedH1GraphEmbedding_surjective {d : ℕ} (ρ : Vec d → ℝ)
    (hρ : Continuous ρ) (hρpos : ∀ x, 0 < ρ x) :
    Function.Surjective (densityWeightedH1GraphEmbedding ρ hρ hρpos) := by
  intro p
  have hp : (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).toFun p.1 ∈
      densityWeightedWeakGraphSubmodule ρ hρ hρpos := p.2
  change (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).toFun p.1 ∈
    densityWeightedWeakGraphSet ρ hρ hρpos at hp
  rw [← densityWeightedH1GraphPair_range ρ hρ hρpos] at hp
  obtain ⟨q, hq⟩ := hp
  refine ⟨q, ?_⟩
  apply Subtype.ext
  apply (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).injective
  simpa [densityWeightedH1GraphEmbedding] using hq

/-- The quotient and the completed full graph are the same carrier through the injective
value-gradient map. The Hilbert norm is the L² norm of both components together. -/
noncomputable def densityWeightedH1GraphEquiv {d : ℕ} (ρ : Vec d → ℝ)
    (hρ : Continuous ρ) (hρpos : ∀ x, 0 < ρ x) :
    DensityWeightedH1 ρ ≃ densityWeightedH1Submodule ρ hρ hρpos :=
  Equiv.ofBijective (densityWeightedH1GraphEmbedding ρ hρ hρpos)
    ⟨densityWeightedH1GraphEmbedding_injective ρ hρ hρpos,
      densityWeightedH1GraphEmbedding_surjective ρ hρ hρpos⟩

/-- The scalar value in the graph Hilbert space. -/
def densityWeightedH1SpaceValue {d : ℕ} {ρ : Vec d → ℝ}
    {hρ : Continuous ρ} {hρpos : ∀ x, 0 < ρ x}
    (u : densityWeightedH1Submodule ρ hρ hρpos) : Lp ℝ 2 (densityWeightedMeasure ρ) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).toFun u.1 |>.1

/-- The Euclidean weak gradient in the graph Hilbert space. -/
def densityWeightedH1SpaceGradient {d : ℕ} {ρ : Vec d → ℝ}
    {hρ : Continuous ρ} {hρpos : ∀ x, 0 < ρ x}
    (u : densityWeightedH1Submodule ρ hρ hρpos) :
    Lp (EuclideanSpace ℝ (Fin d)) 2 (densityWeightedMeasure ρ) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).toFun u.1 |>.2

/-- The Hilbert norm is precisely the graph norm of the weighted value and Euclidean gradient. -/
theorem densityWeightedH1Space_norm_sq {d : ℕ} {ρ : Vec d → ℝ}
    {hρ : Continuous ρ} {hρpos : ∀ x, 0 < ρ x}
    (u : densityWeightedH1Submodule ρ hρ hρpos) :
    ‖u‖ ^ 2 = ‖densityWeightedH1SpaceValue u‖ ^ 2 +
      ‖densityWeightedH1SpaceGradient u‖ ^ 2 := by
  change ‖u.1‖ ^ 2 = _
  rw [WithLp.prod_norm_sq_eq_of_L2]
  rfl

/-- The graph norm transported from the full Hilbert realization to a quotient class. -/
def densityWeightedH1QuotientGraphNorm {d : ℕ} (ρ : Vec d → ℝ)
    (hρ : Continuous ρ) (hρpos : ∀ x, 0 < ρ x)
    (q : DensityWeightedH1 ρ) : ℝ :=
  ‖densityWeightedH1GraphEmbedding ρ hρ hρpos q‖

/-- The quotient graph norm is exactly the square-sum norm of its actual weighted value and
Euclidean weak gradient in the Hilbert realization. -/
theorem densityWeightedH1QuotientGraphNorm_sq {d : ℕ} (ρ : Vec d → ℝ)
    (hρ : Continuous ρ) (hρpos : ∀ x, 0 < ρ x) (q : DensityWeightedH1 ρ) :
    densityWeightedH1QuotientGraphNorm ρ hρ hρpos q ^ 2 =
      ‖densityWeightedH1Value ρ q‖ ^ 2 +
        ‖densityWeightedH1Gradient ρ hρ hρpos q‖ ^ 2 := by
  rw [densityWeightedH1QuotientGraphNorm, densityWeightedH1Space_norm_sq]
  congr 1


end

end EinsteinRelation.SpatialDirichlet

