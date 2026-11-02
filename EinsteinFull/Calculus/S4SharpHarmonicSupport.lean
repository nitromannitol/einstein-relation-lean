import EinsteinFull.Calculus.S4SharpDetSupport

/-!
# `app:sharp-harmonic`: the deterministic pointwise conjuncts

For the constructed physical pair and every noise sample and point: the rank-one Jacobian
identities, the constant harmonic flux `ã(e₁ + ∇ψ) = e₁`, and the constant signed generator of the
harmonic coordinate `x₁ + ψ`.
-/

open MeasureTheory

namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinRelation.Sharpness

theorem sharpHarmonic_pointwise {d : ℕ} (i : Fin d) (W : NoiseSample d) (x : Vec d) :
    (jacobian i (gradient (EinsteinFull.Work.W8.corrector W) x)).mulVec (unitVector i) =
        (jacobian i (gradient (EinsteinFull.Work.W8.corrector W) x)).det • unitVector i ∧
      (jacobian i (gradient (EinsteinFull.Work.W8.corrector W) x)).transpose.mulVec
          (unitVector i) = unitVector i + gradient (EinsteinFull.Work.W8.corrector W) x ∧
      (reducedCoefficient (EinsteinFull.Work.W8.physicalPair i W) x).mulVec
          (unitVector i + gradient (EinsteinFull.Work.W8.corrector W) x) = unitVector i ∧
      ∀ lam : ℝ, reducedGenerator i (EinsteinFull.Work.W8.physicalPair i W) lam
          (fun y => y i + EinsteinFull.Work.W8.corrector W y) x = lam :=
  ⟨sharpJacobian_mulVec_unitVector _ _, sharpJacobian_transpose_mulVec_unitVector _ _,
    EinsteinFull.Work.W8.physicalPair_harmonic i W x,
    fun lam => EinsteinFull.Work.W8.physicalPair_harmonicCoordinate_generator i W lam x⟩

end EinsteinFull.Blueprint
