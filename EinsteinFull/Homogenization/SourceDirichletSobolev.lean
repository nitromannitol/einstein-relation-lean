import EinsteinFull.Homogenization.SourceSobolevApproximation

/-!
# Dirichlet energy and zero-boundary Sobolev functions

The Dirichlet variational quantity in Armstrong, Kuusi and Mourrat,
*Quantitative Stochastic Homogenization and Large-Scale Regularity*, (1.7),
can be expressed using CoarseGraining's zero-boundary Sobolev functions.
-/

open MeasureTheory

namespace EinsteinFull.Homogenization

open EinsteinRelation EinsteinRelation.Environment.AKMTestIntegralSupport

/-- On an open domain the source Dirichlet energy is the infimum over exactly
the gradients of CoarseGraining zero-boundary Sobolev functions. -/
theorem sourceDirichletEnergy_eq_sInf_h10 {d : ℕ} {K : ℝ}
    (a : Coefficient d K) {U : Set (Vec d)} (hU : IsOpen U) (e : Vec d) :
    External.AKM.sourceDirichletEnergy a U e =
      sInf {E : ℝ | ∃ w : _root_.Homogenization.H10Function U,
        E = ⨍ x in U, (1 / 2 : ℝ) * dot (e + w.toH1Function.grad x)
          ((a x).mulVec (e + w.toH1Function.grad x)) ∂volume} := by
  unfold External.AKM.sourceDirichletEnergy
  congr 1
  ext E
  constructor
  · rintro ⟨u, g, hg, rfl⟩
    obtain ⟨w, _, hw⟩ := sourceH01_exists_h10 hU hg
    exact ⟨w, by rw [hw]⟩
  · rintro ⟨w, rfl⟩
    exact ⟨w.toH1Function.toFun, w.toH1Function.grad, h10_sourceH01 hU w, rfl⟩

end EinsteinFull.Homogenization
