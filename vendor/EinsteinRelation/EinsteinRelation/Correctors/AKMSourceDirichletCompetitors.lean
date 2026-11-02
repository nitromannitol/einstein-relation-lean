import EinsteinRelation.Correctors.AKMSourceDirichletBounds

/-!
# Testing the source Dirichlet infimum

Source: `paper/main.tex:693-698,727-729`; AKM (1.7), printed p. 5,
and the affine-competitor argument for (1.14), printed p. 8.
The set in the defining infimum is nonempty and bounded below for every
coefficient, domain and direction, independently of minimizer existence.
-/

open MeasureTheory
namespace EinsteinRelation.External.AKM
open Environment.AKMTestIntegralSupport

/-- Every admissible variation bounds the literal source infimum from above. -/
theorem sourceDirichletEnergy_le_admissible {d : ℕ} {K : ℝ}
    (a : Coefficient d K) (U : Set (Vec d)) (e : Vec d)
    (u : Vec d → ℝ) (g : Vec d → Vec d) (hu : SourceH01 U u g) :
    sourceDirichletEnergy a U e ≤
      ⨍ x in U, (1 / 2 : ℝ) * dot (e + g x) ((a x).mulVec (e + g x)) ∂volume := by
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro E ⟨v, h, hv, rfl⟩
    unfold average
    apply integral_nonneg
    intro x
    have hs : 0 ≤ euclideanSq (e + h x) := by
      unfold euclideanSq dot
      exact Finset.sum_nonneg fun i _ => mul_self_nonneg ((e + h x) i)
    exact mul_nonneg (by norm_num) (hs.trans (a.elliptic x _).1)
  · exact ⟨u, g, hu, rfl⟩

/-- The affine function itself is an admissible Dirichlet competitor. -/
theorem sourceDirichletEnergy_le_affine {d : ℕ} {K : ℝ}
    (a : Coefficient d K) (U : Set (Vec d)) (e : Vec d) :
    sourceDirichletEnergy a U e ≤
      ⨍ x in U, (1 / 2 : ℝ) * dot e ((a x).mulVec e) ∂volume := by
  simpa only [add_zero] using
    sourceDirichletEnergy_le_admissible a U e (fun _ => 0) (fun _ => 0) (sourceH01_zero U)

/-- The Dirichlet value is the infimum of an actual nonempty set of energies. -/
theorem sourceDirichletEnergy_admissible_nonempty {d : ℕ} {K : ℝ}
    (a : Coefficient d K) (U : Set (Vec d)) (e : Vec d) :
    Set.Nonempty {E : ℝ | ∃ (u : Vec d → ℝ) (g : Vec d → Vec d), SourceH01 U u g ∧
      E = ⨍ x in U, (1 / 2 : ℝ) * dot (e + g x) ((a x).mulVec (e + g x)) ∂volume} := by
  exact ⟨_, fun _ => 0, fun _ => 0, sourceH01_zero U, rfl⟩

end EinsteinRelation.External.AKM
