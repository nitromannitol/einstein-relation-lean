import EinsteinFull.Frozen.JointObservationIndex
import EinsteinRelation.Environment.Basic
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

namespace EinsteinFull

open EinsteinRelation

/-- The finite weighted partial-derivative norm N(F) used in Proposition 5.1.
All coordinate derivative words of order at most N are included. For Schwartz
functions this nonempty set is bounded, so its supremum has its literal meaning. -/
noncomputable def schwartzTestNorm {d : ℕ} (N : ℕ)
    (F : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d))) : ℝ :=
  sSup {q : ℝ | ∃ k : Fin (N + 1), ∃ dirs : Fin k.val → Fin d, ∃ x : Vec d,
    q = (1 + euclideanNorm x) ^ N *
      ‖iteratedFDeriv ℝ k.val (fun y => F y) x (fun j => unitVector (dirs j))‖}

end EinsteinFull
