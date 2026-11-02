import EinsteinFull.Work.W8.SharpnessConstructionSupport
import EinsteinFull.Calculus.S4ReducedCoefficientSupport
import EinsteinRelation.Entropy.FisherCauchySchwarz

/-!
# Deterministic clock identities of the sharp example (`app:sharp-clock`, first conjunct)

For the constructed physical pair, the scalar product of the harmonic identity
`ã(e₁ + ∇ψ) = e₁` with `∇ψ` and the generator identity for the corrector.
No path law is involved.
-/

namespace EinsteinFull
open EinsteinRelation EinsteinRelation.Sharpness

/-- `ã e₁ · ∇ψ = 1 - ã₁₁` for the constructed pair, from symmetry of `ã` and `ã(e₁ + ∇ψ) = e₁`. -/
theorem physicalPair_dot_forcing_gradient {d : ℕ} (i : Fin d) (W : NoiseSample d) (x : Vec d) :
    dot ((reducedCoefficient (EinsteinFull.Work.W8.physicalPair i W) x).mulVec (unitVector i))
        (gradient (EinsteinFull.Work.W8.corrector W) x) =
      1 - reducedCoefficient (EinsteinFull.Work.W8.physicalPair i W) x i i := by
  obtain ⟨Λ, -, hreg⟩ := EinsteinFull.Work.W8.exists_physicalPair_regularity i
  set R := reducedCoefficient (EinsteinFull.Work.W8.physicalPair i W) x with hR
  set g := gradient (EinsteinFull.Work.W8.corrector W) x with hg
  have hsym : R.transpose = R := reducedCoefficient_symm (hreg W) x
  have h : R.mulVec (unitVector i + g) = unitVector i :=
    EinsteinFull.Work.W8.physicalPair_harmonic i W x
  rw [Matrix.mulVec_add] at h
  have hRg : R.mulVec g = unitVector i - R.mulVec (unitVector i) := eq_sub_of_add_eq' h
  have hone : unitVector i i = 1 := Pi.single_eq_same i 1
  have hzero : ∀ j, j ≠ i → unitVector i j = 0 := fun j hj => Pi.single_eq_of_ne hj 1
  have hu : ∀ v : Vec d, dot (unitVector i) v = v i := by
    intro v
    unfold dot
    rw [Finset.sum_eq_single i (fun j _ hj => by rw [hzero j hj, zero_mul]) (by simp), hone,
      one_mul]
  have hdiag : R.mulVec (unitVector i) i = R i i := by
    show ∑ j, R i j * unitVector i j = R i i
    rw [Finset.sum_eq_single i (fun j _ hj => by rw [hzero j hj, mul_zero]) (by simp), hone,
      mul_one]
  calc dot (R.mulVec (unitVector i)) g = dot g (R.mulVec (unitVector i)) :=
        dotProduct_comm _ _
    _ = dot (unitVector i) (R.mulVec g) := dot_mulVec_swap R hsym g (unitVector i)
    _ = 1 - R i i := by
        rw [hRg, hu, Pi.sub_apply, hone, hdiag]

/-- Both identities of the first conjunct of `app:sharp-clock`. -/
theorem sharpClock_identities {d : ℕ} (i : Fin d) (W : NoiseSample d) (x : Vec d) (lam : ℝ) :
    dot ((reducedCoefficient (EinsteinFull.Work.W8.physicalPair i W) x).mulVec (unitVector i))
        (gradient (EinsteinFull.Work.W8.corrector W) x) =
      1 - reducedCoefficient (EinsteinFull.Work.W8.physicalPair i W) x i i ∧
    reducedGenerator i (EinsteinFull.Work.W8.physicalPair i W) lam
        (EinsteinFull.Work.W8.corrector W) x =
      (1 - clockDensity (EinsteinFull.Work.W8.physicalPair i W) x) /
          EinsteinFull.Work.W8.clockParameter i +
        lam * (1 - reducedCoefficient (EinsteinFull.Work.W8.physicalPair i W) x i i) :=
  ⟨physicalPair_dot_forcing_gradient i W x,
    EinsteinFull.Work.W8.physicalPair_generator i W lam x⟩

end EinsteinFull
