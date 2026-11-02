import EinsteinRelation.Probability.ReductionInverseLocality
import EinsteinRelation.Probability.ReducedLocalFactor
import EinsteinRelation.Regeneration.HalfSpaces

/-! # Future-halfspace locality of ball-local observables

Source: `paper/main.tex:479–483`. A real function measurable for the physical joint σ-algebra of
the open Euclidean ball of radius `R` factors through the literal reduced observations on that
ball (`EinsteinRelation.Probability.exists_measurable_reduced_local_factor`). The observation of
`translate y ω` at `x` is the observation of `reduce ω` at `y + x`, and for `x` in the ball the
point `y + x` lies in the future half-space `{z | -2R ≤ z i}` whenever `-R ≤ y i`
(`EinsteinRelation.Regeneration.future_ball_in_halfSpace`). So equal reduced observations on the
future half-space force equal ball-local values after translation by `y`.

No positivity of `R` and no dimension premise is needed: the ball is the open Euclidean ball, and
the half-space bound follows from the strict inequality alone.
-/

open EinsteinRelation MeasureTheory

namespace EinsteinRelation.Occupation

theorem local_observable_translate_eq_of_future_observations {d : ℕ}
    (i : Fin d) (R : ℝ) (G : FieldPair d → ℝ)
    (hG : @Measurable (FieldPair d) ℝ
      (localSigma {x : Vec d | euclideanNorm x < R}) inferInstance G)
    (ω ω' : FieldPair d) (y : Vec d) (hy : -R ≤ y i)
    (hobs : ∀ x : Vec d, -2 * R ≤ x i →
      ((reduce ω).1 x, (reduce ω).2 x) = ((reduce ω').1 x, (reduce ω').2 x)) :
    G (translate y ω) = G (translate y ω') := by
  obtain ⟨H, -, hGH⟩ :=
    EinsteinRelation.Probability.exists_measurable_reduced_local_factor
      {x : Vec d | euclideanNorm x < R} G hG
  have hobs_ball : (fun x : {x : Vec d | euclideanNorm x < R} =>
      ((reduce (translate y ω)).1 x, (reduce (translate y ω)).2 x)) =
      (fun x : {x : Vec d | euclideanNorm x < R} =>
      ((reduce (translate y ω')).1 x, (reduce (translate y ω')).2 x)) := by
    funext x
    have hx : euclideanNorm (x : Vec d) < R := x.2
    have hsub : euclideanNorm (y + (x : Vec d) - y) < R := by
      rw [add_sub_cancel_left]
      exact hx
    have hhalf : -2 * R ≤ (y + (x : Vec d)) i :=
      EinsteinRelation.Regeneration.future_ball_in_halfSpace i (y + (x : Vec d)) y R hy hsub
    rw [reduce_translate ω y, reduce_translate ω' y]
    exact hobs (y + (x : Vec d)) hhalf
  calc G (translate y ω)
      = H (fun x : {x : Vec d | euclideanNorm x < R} =>
          ((reduce (translate y ω)).1 x, (reduce (translate y ω)).2 x)) :=
          hGH (translate y ω)
    _ = H (fun x : {x : Vec d | euclideanNorm x < R} =>
          ((reduce (translate y ω')).1 x, (reduce (translate y ω')).2 x)) :=
          congrArg H hobs_ball
    _ = G (translate y ω') := (hGH (translate y ω')).symm

end EinsteinRelation.Occupation
