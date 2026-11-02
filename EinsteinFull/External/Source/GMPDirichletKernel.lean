import EinsteinRelation.External.AKMLocalCorrectors

open MeasureTheory Filter
open scoped Topology

namespace EinsteinFull.External.Source.GMP
open EinsteinRelation

/-- The Euclidean ball used in GMP Lemma 5.3, printed p.22. The coordinate
carrier's default norm is not used. -/
def sourceBall {d : ℕ} (center : Vec d) (radius : ℝ) : Set (Vec d) :=
  {x | euclideanNorm (x - center) < radius}

/-- The bounded measurable, symmetric coefficients of GMP (5.4). This is a
meaning predicate for the source fields, with no heat-kernel estimate. -/
def IsUniformlyElliptic {d : ℕ} (κ : ℝ) (ρ : Vec d → ℝ)
    (α : Vec d → Mat d) : Prop :=
  Measurable ρ ∧ Measurable α ∧
    ∀ x : Vec d, κ ≤ ρ x ∧ ρ x ≤ κ⁻¹ ∧ (α x).transpose = α x ∧
      ∀ v : Vec d, κ * euclideanSq v ≤ dot v ((α x).mulVec v) ∧
        dot v ((α x).mulVec v) ≤ κ⁻¹ * euclideanSq v

/-- A positive-time weak solution of the weighted equation (5.4). Both time
and space use Lebesgue measure, and the density multiplies only the time
term. Gradients and their Euclidean square integrability are explicit. -/
def IsWeightedCaloric {d : ℕ} (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (I : Set ℝ) (U : Set (Vec d))
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d) : Prop :=
  MemLp u 2 (volume.restrict (I ×ˢ U)) ∧
    AEStronglyMeasurable G (volume.restrict (I ×ˢ U)) ∧
    MemLp (fun z => euclideanNorm (G z)) 2 (volume.restrict (I ×ˢ U)) ∧
    (∀ᵐ t ∂volume.restrict I,
      HasWeakGradient U (fun x => u (t, x)) (fun x => G (t, x))) ∧
    ∀ ψ : ℝ × Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ interior I ×ˢ U →
      (∫ z in I ×ˢ U,
        -(ρ z.2 * u z) * fderiv ℝ ψ z (1, 0) +
          dot ((α z.2).mulVec (G z))
            (fun j => fderiv ℝ ψ z (0, unitVector j))) = 0

/-- The nonnegative Dirichlet fundamental solution in GMP (5.4), with an
actual weak spatial gradient and continuous positive-time representative.
The initial delta is normalized against Lebesgue measure, not rho dx.
The positive-time zero extensions have weak gradients on all space; this
specifies the zero Sobolev trace in addition to the pointwise boundary data.
No lower bound, Gaussian estimate, path law or regeneration claim is assumed. -/
def IsDirichletFundamentalSolution {d : ℕ} (ρ : Vec d → ℝ)
    (α : Vec d → Mat d) (R : ℝ)
    (K : ℝ → Vec d → Vec d → ℝ)
    (G : ℝ → Vec d → Vec d → Vec d) : Prop :=
  let B := sourceBall (0 : Vec d) R
  ∀ y ∈ B,
    ContinuousOn (fun z : ℝ × Vec d => K z.1 z.2 y)
      (Set.Ioi 0 ×ˢ closure B) ∧
    (∀ t : ℝ, 0 < t → ∀ x ∈ B, 0 ≤ K t x y) ∧
    (∀ t : ℝ, 0 < t → ∀ x ∈ frontier B, K t x y = 0) ∧
    (∀ a b : ℝ, 0 < a → a < b →
      IsWeightedCaloric ρ α (Set.Ioo a b) B
        (fun z => K z.1 z.2 y) (fun z => G z.1 z.2 y) ∧
      ∀ᵐ t ∂volume.restrict (Set.Ioo a b),
        HasWeakGradient Set.univ
          (Set.indicator B (fun x => K t x y))
          (Set.indicator B (fun x => G t x y))) ∧
    ∀ ψ : Vec d → ℝ, IsSpatialTest B ψ →
      Tendsto (fun t : ℝ => ∫ x in B, K t x y * ψ x)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (ψ y))

/-- The source's initial normalization, available directly from the meaning
predicate without any literature input. -/
theorem IsDirichletFundamentalSolution.initial_delta
    {d : ℕ} {ρ : Vec d → ℝ} {α : Vec d → Mat d} {R : ℝ}
    {K : ℝ → Vec d → Vec d → ℝ} {G : ℝ → Vec d → Vec d → Vec d}
    (hK : IsDirichletFundamentalSolution ρ α R K G)
    {y : Vec d} (hy : y ∈ sourceBall (0 : Vec d) R)
    {ψ : Vec d → ℝ} (hψ : IsSpatialTest (sourceBall (0 : Vec d) R) ψ) :
    Tendsto (fun t : ℝ => ∫ x in sourceBall (0 : Vec d) R, K t x y * ψ x)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (ψ y)) :=
  (hK y hy).2.2.2.2 ψ hψ

end EinsteinFull.External.Source.GMP
