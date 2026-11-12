import EinsteinRelation.Correctors.ParabolicFluxSolution

namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- Symmetry cancels the interior terms in forward/backward energy testing.
Source: `paper/main.tex:787–792,850`; AKM Proposition E.1 proof. -/
theorem parabolic_duality_symmetric_cancellation {d : ℕ} {K : ℝ}
    (A : Coefficient d K) (x : Vec d) (u v r c : ℝ) (G H D : Vec d) :
    dot ((A x).mulVec G)
        (fun j => (r*c)^2 * H j + 2*(r*c)*v*(r*D j)) +
      dot (-((A x).mulVec H))
        (fun j => (r*c)^2 * G j + 2*(r*c)*u*(r*D j)) =
      2*r^2*c * dot (fun j => v*((A x).mulVec G) j-u*((A x).mulVec H) j) D := by
  have hs : dot ((A x).mulVec G) H = dot ((A x).mulVec H) G := by
    calc
      _ = dot H ((A x).mulVec G) := dotProduct_comm _ _
      _ = dot G ((A x).mulVec H) := dot_mulVec_swap (A x) (A.symmetric x) H G
      _ = _ := dotProduct_comm _ _
  calc
    _ = (r*c)^2 * (dot ((A x).mulVec G) H-dot ((A x).mulVec H) G) +
        2*r^2*c * dot (fun j => v*((A x).mulVec G) j-u*((A x).mulVec H) j) D := by
      dsimp only [dot]
      simp_rw [mul_sub, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      dsimp
      ring
    _ = _ := by rw [hs]; ring

end EinsteinRelation.Correctors
