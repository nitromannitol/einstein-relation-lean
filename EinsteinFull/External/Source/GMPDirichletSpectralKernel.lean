import EinsteinFull.External.Source.GMPDirichletKernel
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.MeasureTheory.Function.L2Space

open MeasureTheory

noncomputable section
namespace EinsteinFull.External.Source.GMP
open EinsteinRelation

/-- The weighted Hilbert space measure of the source Dirichlet operator,
GMP printed p.22. The kernel itself is a density against unweighted dx. -/
def dirichletVolume {d : ℕ} (ρ : Vec d → ℝ) (R : ℝ) : Measure (Vec d) :=
  (volume.restrict (sourceBall (0 : Vec d) R)).withDensity
    (fun x => ENNReal.ofReal (ρ x))

/-- A complete orthonormal resolution of the actual weighted Dirichlet
operator in the auxiliary spectral problem on GMP printed p.22. Each
eigenfunction has its genuine zero-extension weak gradient, and solves the
source eigenvalue equation. No eigenvalue bound, Harnack bound, principal
eigenfunction lower bound or heat-kernel estimate is included. -/
structure DirichletSpectralResolution {d : ℕ} (ρ : Vec d → ℝ)
    (α : Vec d → Mat d) (R : ℝ) where
  /-- The positive Dirichlet eigenvalues. -/
  eigenvalue : ℕ → ℝ
  /-- Continuous representatives of the source real eigenfunctions. -/
  eigenfunction : ℕ → Vec d → ℝ
  /-- Their weak spatial gradients. -/
  gradient : ℕ → Vec d → Vec d
  eigenvalue_pos : ∀ n, 0 < eigenvalue n
  continuous : ∀ n, ContinuousOn (eigenfunction n)
    (closure (sourceBall (0 : Vec d) R))
  boundary_zero : ∀ n, ∀ x ∈ frontier (sourceBall (0 : Vec d) R),
    eigenfunction n x = 0
  square_integrable : ∀ n, MemLp (eigenfunction n) 2 (dirichletVolume ρ R)
  gradient_square_integrable : ∀ n,
    MemLp (fun x => euclideanNorm (gradient n x)) 2
      (volume.restrict (sourceBall (0 : Vec d) R))
  zero_extension_gradient : ∀ n,
    HasWeakGradient Set.univ
      (Set.indicator (sourceBall (0 : Vec d) R) (eigenfunction n))
      (Set.indicator (sourceBall (0 : Vec d) R) (gradient n))
  eigenfunction_equation : ∀ n, ∀ ψ : Vec d → ℝ,
    IsSpatialTest (sourceBall (0 : Vec d) R) ψ →
    (∫ x in sourceBall (0 : Vec d) R,
      dot ((α x).mulVec (gradient n x))
        (fun j => fderiv ℝ ψ x (unitVector j))) =
      eigenvalue n * ∫ x in sourceBall (0 : Vec d) R,
        ρ x * eigenfunction n x * ψ x
  orthonormal : Orthonormal ℝ
    (fun n => (square_integrable n).toLp (eigenfunction n))
  complete : Dense (Submodule.span ℝ (Set.range
    (fun n => (square_integrable n).toLp (eigenfunction n))) :
      Set (Lp ℝ 2 (dirichletVolume ρ R)))

/-- The source Dirichlet heat kernel is selected by its actual complete
weighted Dirichlet spectral resolution. The factor rho(y) converts the
weighted spectral kernel to the Lebesgue-density convention of (5.4).
This excludes the initial boundary entrance sources admitted by V1's local
distributional initial tests. The series is genuinely summable for every
positive time and both interior arguments. No quantitative bound is assumed. -/
def IsSpectralDirichletFundamentalSolution {d : ℕ} (ρ : Vec d → ℝ)
    (α : Vec d → Mat d) (R : ℝ) (K : ℝ → Vec d → Vec d → ℝ)
    (G : ℝ → Vec d → Vec d → Vec d) : Prop :=
  IsDirichletFundamentalSolution ρ α R K G ∧
    ∃ spectrum : DirichletSpectralResolution ρ α R,
      ∀ t : ℝ, 0 < t → ∀ x ∈ sourceBall (0 : Vec d) R,
        ∀ y ∈ sourceBall (0 : Vec d) R,
          Summable (fun n => Real.exp (-spectrum.eigenvalue n * t) *
            spectrum.eigenfunction n x * spectrum.eigenfunction n y) ∧
          K t x y = ρ y * ∑' n, Real.exp (-spectrum.eigenvalue n * t) *
            spectrum.eigenfunction n x * spectrum.eigenfunction n y

/-- The corrected carrier implies the exact weighted symmetry used in the
source proof. In particular the asymmetric boundary entrance counterexample
from the V1 review cannot satisfy it. -/
theorem IsSpectralDirichletFundamentalSolution.weighted_symmetry
    {d : ℕ} {ρ : Vec d → ℝ} {α : Vec d → Mat d} {R : ℝ}
    {K : ℝ → Vec d → Vec d → ℝ} {G : ℝ → Vec d → Vec d → Vec d}
    (hK : IsSpectralDirichletFundamentalSolution ρ α R K G)
    {t : ℝ} (ht : 0 < t) {x y : Vec d}
    (hx : x ∈ sourceBall (0 : Vec d) R) (hy : y ∈ sourceBall (0 : Vec d) R) :
    ρ x * K t x y = ρ y * K t y x := by
  obtain ⟨spectrum, hspec⟩ := hK.2
  rw [(hspec t ht x hx y hy).2, (hspec t ht y hy x hx).2]
  have hswap : (∑' n, Real.exp (-spectrum.eigenvalue n * t) *
      spectrum.eigenfunction n x * spectrum.eigenfunction n y) =
      ∑' n, Real.exp (-spectrum.eigenvalue n * t) *
        spectrum.eigenfunction n y * spectrum.eigenfunction n x :=
    tsum_congr (fun _ => by ring)
  rw [hswap]
  ring

end EinsteinFull.External.Source.GMP
