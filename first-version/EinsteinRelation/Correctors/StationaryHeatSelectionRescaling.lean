import EinsteinRelation.Correctors.StationaryHeatCutoffErrors
import EinsteinRelation.Correctors.HeatSelectionCutoffRescaling
import EinsteinRelation.Correctors.SpatialBallLocalL2Support
import EinsteinRelation.Correctors.HeatSelectedPositiveWindow

/-! Source: `paper/main.tex:722,756`. Almost sure transport of the
independent heat cutoff selection under a fixed positive time dilation. -/
open MeasureTheory Filter Topology
open scoped ENNReal
namespace EinsteinRelation.Correctors
open External.AKM HeatSelectedSkewMeaning

/-- A stationary `C/t` moment bound preserves every existing selected
gradient under the literal time dilation. The common full-measure set is
chosen before the selected gradient; no measurability of that choice or
factorization through a smaller environment carrier is assumed. -/
theorem ae_heat_selection_rescaled_local_L2 {d : ℕ}
    (Q : Measure (FieldPair d)) [SFinite Q] (hQ : IsStationary Q)
    (F : FieldPair d → Vec d) (hF : Measurable F)
    (C c : ℝ) (hC : 0 < C) (hc : 0 < c)
    (hbound : ∀ (j k l : Fin d) (t : ℝ), 0 < t → eLpNorm
      (fun ω => akmHeatGradientSpaceIntegral (fun y => F (translate y ω)) t j k l 0)
        2 Q ≤ ENNReal.ofReal (C / t)) :
    ∀ᵐ ω ∂Q, ∀ G : Fin d → Fin d → Vec d → Vec d,
      IsHeatSelectedFluxGradient (fun y => F (translate y ω)) G →
      ∀ (j k l : Fin d) (R : ℕ),
        (∀ m n, MemLp
          (rescaledAKMHeatGradientTruncation (fun y => F (translate y ω)) c m n j k l)
            2 (volume.restrict (ball 0 ((R : ℝ) + 1)))) ∧
        Tendsto (fun mn : ℕ × ℕ => eLpNorm
          (fun x => rescaledAKMHeatGradientTruncation (fun y => F (translate y ω))
            c mn.1 mn.2 j k l x - G j k x l)
            2 (volume.restrict (ball 0 ((R : ℝ) + 1)))) atTop (𝓝 0) := by
  have herr (j k l : Fin d) (R : ℕ) := by
    letI := isFiniteMeasure_restrict_euclideanBall (0 : Vec d) ((R : ℝ) + 1)
      (by positivity)
    exact ae_heat_cutoff_endpoint_errors_local_L2 Q hQ
      (volume.restrict (ball 0 ((R : ℝ) + 1))) F hF j k l C c hC hc
        (hbound j k l)
  filter_upwards [ae_all_iff.mpr (fun j => ae_all_iff.mpr (fun k =>
    ae_all_iff.mpr (fun l => ae_all_iff.mpr (fun R => herr j k l R))))]
      with ω hω
  intro G hselect j k l R
  exact heat_selection_rescaled_local_L2_of_endpoint_errors
    (fun y => F (translate y ω)) G hselect c hc j k l R
      (hω j k l R).1 (hω j k l R).2

/-- Genuine spatial and time integrability holds on the same literal
rescaled windows, directly by restriction from source selection. -/
theorem heat_selection_rescaled_integrable {d : ℕ}
    {g : Vec d → Vec d} {G : Fin d → Fin d → Vec d → Vec d}
    (hselect : IsHeatSelectedFluxGradient g G) (c : ℝ) (hc : 0 < c)
    (j k l : Fin d) (R m n : ℕ) :
    ∀ᵐ x ∂(volume.restrict (ball 0 ((R : ℝ) + 1))),
      (∀ᵐ t ∂(volume.restrict
        (Set.Icc (c / ((m : ℝ) + 1)) (c * ((n : ℝ) + 1)))),
        Integrable (fun y => akmHeatGradientDensity g t j k l x y) volume) ∧
      Integrable (fun t => akmHeatGradientSpaceIntegral g t j k l x)
        (volume.restrict (Set.Icc (c / ((m : ℝ) + 1)) (c * ((n : ℝ) + 1)))) :=
  heat_selected_integrable_positive_window hselect j k l R _ _
    (div_pos hc (by positivity))

end EinsteinRelation.Correctors
