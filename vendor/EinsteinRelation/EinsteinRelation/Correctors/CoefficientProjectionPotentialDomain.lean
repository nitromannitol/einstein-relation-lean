import EinsteinRelation.Correctors.CoefficientProjectionCoordinates

open MeasureTheory
namespace EinsteinRelation.Correctors

/-- The coefficient projection preserves the closed potential domain once its
scalar H¹ commutation is established; source `paper/main.tex:240-248,693-698`. -/
theorem coefficientProjection_mem_potentialDomain_of_h1 {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    (hH1 : ∀ f : horizontalH1 Q hQ, ∃ g : horizontalH1 Q hQ,
      ∀ i, horizontalH1Gradient Q hQ g i =
        coefficientProjection Q ℝ (horizontalH1Gradient Q hQ f i))
    (G : Lp (EuclideanSpace ℝ (Fin d)) 2 Q)
    (hG : G ∈ stationaryPotentialGradientSubmodule Q hQ) :
    coefficientProjection Q (EuclideanSpace ℝ (Fin d)) G ∈
      stationaryPotentialGradientSubmodule Q hQ := by
  let P := coefficientProjection Q (EuclideanSpace ℝ (Fin d))
  let S := stationaryPotentialGradientSubmodule Q hQ
  have hrange : LinearMap.range (horizontalEuclideanGradientMap Q hQ) ≤
      S.comap P.toLinearMap := by
    rintro _ ⟨f, rfl⟩
    obtain ⟨g, hg⟩ := hH1 f
    have heq : P (horizontalEuclideanGradient Q hQ f) =
        horizontalEuclideanGradient Q hQ g := by
      apply Lp.ext
      have hcoord : ∀ i : Fin d, ∀ᵐ ω ∂Q,
          P (horizontalEuclideanGradient Q hQ f) ω i =
            horizontalEuclideanGradient Q hQ g ω i := by
        intro i
        have hi : (EuclideanSpace.proj (𝕜 := ℝ) i).compLpL 2 Q
            (P (horizontalEuclideanGradient Q hQ f)) =
            horizontalH1Gradient Q hQ g i := by
          change (EuclideanSpace.proj (𝕜 := ℝ) i).compLpL 2 Q
            (coefficientProjection Q (EuclideanSpace ℝ (Fin d))
              (horizontalEuclideanGradient Q hQ f)) = _
          rw [coefficientProjection_coordinateLp, horizontalEuclideanGradient_coordinateLp, hg]
        filter_upwards [(EuclideanSpace.proj (𝕜 := ℝ) i).coeFn_compLpL
            (P (horizontalEuclideanGradient Q hQ f)),
          horizontalEuclideanGradient_coordinates Q hQ g i] with ω hp hgg
        exact hp.symm.trans ((congrArg (fun u : Lp ℝ 2 Q => u ω) hi).trans hgg.symm)
      filter_upwards [ae_all_iff.mpr hcoord] with ω hω
      ext i
      exact hω i
    change P (horizontalEuclideanGradient Q hQ f) ∈ S
    rw [heq]
    exact horizontalEuclideanGradient_mem_stationaryPotentialGradients Q hQ g
  have hclosed : IsClosed (S.comap P.toLinearMap).carrier := by
    change IsClosed (P ⁻¹' (stationaryPotentialGradients Q hQ))
    exact (isClosed_stationaryPotentialGradients Q hQ).preimage P.continuous
  exact (LinearMap.range (horizontalEuclideanGradientMap Q hQ)).topologicalClosure_minimal
    hrange hclosed hG

end EinsteinRelation.Correctors
