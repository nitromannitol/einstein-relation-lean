import EinsteinRelation.Calculus.Weak

/-! # Changing spatial weak representatives

Source: `paper/main.tex:903–928`. Conditional and center averages agree
only almost everywhere. Spatial weak equations are invariant under these
changes of representative, with local integrability retained on the domain.
-/

open MeasureTheory

namespace EinsteinRelation.Correctors

/-- An almost-everywhere equality on an open domain preserves local
integrability there. Source: `paper/main.tex:903–928`. -/
theorem locallyIntegrableOn_congr_ae {d : ℕ} {U : Set (Vec d)} (hU : IsOpen U)
    {f g : Vec d → ℝ} (hf : LocallyIntegrableOn f U volume)
    (hfg : f =ᵐ[volume.restrict U] g) : LocallyIntegrableOn g U volume := by
  rw [locallyIntegrableOn_iff hU.isLocallyClosed]
  intro K hKU hK
  exact (hf.integrableOn_compact_subset hKU hK).congr
    (hfg.filter_mono (ae_mono (Measure.restrict_mono hKU le_rfl)))

/-- Both representatives in a weak partial derivative may be replaced
on a spatial null set. Source: `paper/main.tex:903–928`. -/
theorem hasWeakPartialDerivative_congr_ae {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpen U) {j : Fin d} {f g f' g' : Vec d → ℝ}
    (h : HasWeakPartialDerivative U j f g)
    (hf : f =ᵐ[volume.restrict U] f') (hg : g =ᵐ[volume.restrict U] g') :
    HasWeakPartialDerivative U j f' g' := by
  refine ⟨locallyIntegrableOn_congr_ae hU h.1 hf,
    locallyIntegrableOn_congr_ae hU h.2.1 hg, ?_⟩
  intro ψ hψ
  calc
    (∫ x in U, f' x * coordinateDerivative j ψ x) =
        ∫ x in U, f x * coordinateDerivative j ψ x := by
      apply integral_congr_ae
      filter_upwards [hf] with x hx
      rw [hx]
    _ = -(∫ x in U, g x * ψ x) := h.2.2 ψ hψ
    _ = -(∫ x in U, g' x * ψ x) := by
      congr 1
      apply integral_congr_ae
      filter_upwards [hg] with x hx
      rw [hx]

/-- A weak gradient uses one spatial almost-everywhere vector equality.
Source: `paper/main.tex:903–928`. -/
theorem hasWeakGradient_congr_ae {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpen U) {f f' : Vec d → ℝ} {G G' : Vec d → Vec d}
    (h : HasWeakGradient U f G)
    (hf : f =ᵐ[volume.restrict U] f') (hG : G =ᵐ[volume.restrict U] G') :
    HasWeakGradient U f' G' := by
  intro j
  exact hasWeakPartialDerivative_congr_ae hU (h j) hf
    (hG.mono fun _ hx => congrFun hx j)

/-- Both fields in a divergence equation may be replaced almost
everywhere. Source: `paper/main.tex:903–928`. -/
theorem hasWeakDivergence_congr_ae {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpen U) {F F' : Vec d → Vec d} {h h' : Vec d → ℝ}
    (hF : HasWeakDivergence U F h)
    (hFF' : F =ᵐ[volume.restrict U] F') (hh' : h =ᵐ[volume.restrict U] h') :
    HasWeakDivergence U F' h' := by
  refine ⟨fun j => locallyIntegrableOn_congr_ae hU (hF.1 j)
      (hFF'.mono fun _ hx => congrFun hx j),
    locallyIntegrableOn_congr_ae hU hF.2.1 hh', ?_⟩
  intro ψ hψ
  rw [integral_congr_ae (hFF'.symm.mono fun _ hx => congrArg
      (fun v => dot v (gradient ψ _)) hx), hF.2.2 ψ hψ]
  exact congrArg Neg.neg (integral_congr_ae (hh'.mul (Filter.EventuallyEq.rfl)))

/-- Matrix-valued weak row divergence is independent of spatial
representatives. Source: `paper/main.tex:903–928`. -/
theorem hasWeakRowDivergence_congr_ae {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpen U) {S S' : Vec d → Mat d} {g g' : Vec d → Vec d}
    (hS : HasWeakRowDivergence U S g)
    (hSS' : S =ᵐ[volume.restrict U] S') (hgg' : g =ᵐ[volume.restrict U] g') :
    HasWeakRowDivergence U S' g' := by
  intro j
  exact hasWeakDivergence_congr_ae hU (hS j)
    (hSS'.mono fun _ hx => congrFun hx j)
    (hgg'.mono fun _ hx => congrFun hx j)

end EinsteinRelation.Correctors
