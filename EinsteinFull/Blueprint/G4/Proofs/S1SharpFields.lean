import EinsteinFull.Blueprint.G4.node_app_u3A_sharp_u2D_fields
import EinsteinFull.Blueprint.G4.node_sharp_u2E_example_u23_smooth_u2D_seed
import EinsteinFull.Calculus.S1SharpSmoothSet
import EinsteinRelation.Sharpness.SharpEnvironmentMeans
import EinsteinRelation.Sharpness.SharpPhysicalLaw

/-! Reduction of graph node `app:sharp-fields`, `paper/main.tex:1534–1541`, to its dependency
`sharp.example#smooth-seed`. The deterministic identities are those of the constructed fields; the
structural data, the all-order derivative bounds and the smooth environment law are produced from
the uniform derivative bounds of `EinsteinFull.Calculus.S1`. -/

open MeasureTheory

namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinRelation.Sharpness
open EinsteinFull.Calculus.S1

private theorem isElliptic_mono_of_le {d : ℕ} {a : Vec d → Mat d} {Λ Λ' : ℝ} (hΛ : 0 < Λ)
    (h : Λ ≤ Λ') (ha : IsElliptic Λ a) : IsElliptic Λ' a := by
  intro x
  obtain ⟨hs, hξ⟩ := ha x
  refine ⟨hs, fun ξ => ⟨?_, ?_⟩⟩
  · have hsq : 0 ≤ euclideanSq ξ := by
      unfold euclideanSq dot
      exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
    calc Λ'⁻¹ * euclideanSq ξ ≤ Λ⁻¹ * euclideanSq ξ :=
          mul_le_mul_of_nonneg_right (inv_anti₀ hΛ h) hsq
      _ ≤ _ := (hξ ξ).1
  · have hsq : 0 ≤ euclideanSq ξ := by
      unfold euclideanSq dot
      exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
    exact (hξ ξ).2.trans (mul_le_mul_of_nonneg_right h hsq)

theorem node_app_u3A_sharp_u2D_fields_of_deps
    (_hseed : node_sharp_u2E_example_u23_smooth_u2D_seedStmt) :
    node_app_u3A_sharp_u2D_fieldsStmt := by
  intro d hd first
  refine ⟨EinsteinFull.Work.W8.clockParameter_pos first, ?_, ?_⟩
  · intro W x
    dsimp only
    have hfun : (fun y => (reducedCoefficient (EinsteinFull.Work.W8.physicalPair first W) y).mulVec
          (unitVector first)) =
        fun y => (coefficientField first (EinsteinFull.Work.W8.corrector W) y).mulVec
          (unitVector first) :=
      funext fun y => by rw [EinsteinFull.Work.W8.physicalPair_reducedCoefficient]
    refine ⟨EinsteinFull.Work.W8.reducedCoefficient_inverse_formula first W x, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hfun, EinsteinFull.Work.W8.physicalPair_clockDensity]
      rfl
    · rw [EinsteinFull.Work.W8.physicalPair_clockDensity]
      exact (EinsteinFull.Work.W8.density_bounds first W x).1
    · rw [EinsteinFull.Work.W8.physicalPair_clockDensity]
      exact (EinsteinFull.Work.W8.density_bounds first W x).2
    · rw [EinsteinFull.Work.W8.physicalPair_clockDensity,
        EinsteinFull.Work.W8.physicalPair_reducedCoefficient]
      exact (EinsteinFull.Work.W8.physicalPair_apply first W x).1
    · rw [EinsteinFull.Work.W8.physicalPair_clockDensity]
      exact (EinsteinFull.Work.W8.physicalPair_apply first W x).2
  · obtain ⟨D, S, hD4, hD, hreg, hSm, hSmem, hSb⟩ := exists_sharpData first
    have hF := EinsteinFull.Work.W8.measurable_physicalPair first
    refine ⟨D, fun W => hSb _ (hSmem W), fun W => ?_, ?_, ?_⟩
    · exact isElliptic_mono_of_le (by norm_num) (by linarith)
        (EinsteinFull.Work.W8.reducedCoefficient_isElliptic first W)
    · intro k
      have hdens := (physicalPair_unifBdd first).1
      have hred := (physicalPair_unifBdd first).2.1
      obtain ⟨C0, h0⟩ := hdens.coordinate k
      choose Cr hCr using fun i j : Fin d => (hred i j).coordinate k
      refine ⟨|C0| + ∑ i, ∑ j, |Cr i j|, ?_, fun W x => ⟨?_, fun i j => ?_⟩⟩
      · positivity
      · have hnn : 0 ≤ ∑ i : Fin d, ∑ j : Fin d, |Cr i j| :=
          Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
        exact (h0 W x).trans ((le_abs_self _).trans (by linarith))
      · have h1 : |Cr i j| ≤ ∑ j', |Cr i j'| :=
          Finset.single_le_sum (f := fun j' => |Cr i j'|) (fun _ _ => abs_nonneg _)
            (Finset.mem_univ j)
        have h2 : ∑ j', |Cr i j'| ≤ ∑ i', ∑ j', |Cr i' j'| :=
          Finset.single_le_sum (f := fun i' => ∑ j', |Cr i' j'|)
            (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)
        exact (hCr i j W x).trans ((le_abs_self _).trans (by linarith [abs_nonneg C0]))
    · intro P hP
      haveI : IsProbabilityMeasure P := hP.1
      let Q : EnvironmentLaw d D.ellipticity D.dependenceRange :=
        { measure := P.map (EinsteinFull.Work.W8.physicalPair first)
          probability := inferInstance
          ellipticity_parameter := D.one_le_ellipticity
          range_parameter := D.one_le_dependenceRange
          regular := (ae_map_iff hF.aemeasurable
            (measurableSet_isRegular_fieldPair D.ellipticity)).mpr (ae_of_all P hreg)
          stationary := sharpPhysicalPair_isStationary first
            (EinsteinFull.Work.W8.clockParameter first) (EinsteinFull.Work.W8.seedScale d)
            EinsteinFull.Work.W8.corrector_gradient_bound
            (EinsteinFull.Work.W8.density_bounds first) hP
          finiteRange := by
            rw [hD4]
            exact sharpPhysicalPair_hasFiniteRange first
              (EinsteinFull.Work.W8.clockParameter first) (EinsteinFull.Work.W8.seedScale d)
              EinsteinFull.Work.W8.corrector_gradient_bound
              (EinsteinFull.Work.W8.density_bounds first) hP }
      refine ⟨Q, rfl, ?_, ?_⟩
      · exact ((ae_map_iff hF.aemeasurable hSm).mpr (ae_of_all P hSmem)).mono
          fun ω hω => hSb ω hω
      · exact sharp_meanMu_eq_one first (EinsteinFull.Work.W8.clockParameter first)
          (EinsteinFull.Work.W8.seedScale d) (EinsteinFull.Work.W8.seedScale_pos d)
          EinsteinFull.Work.W8.corrector_gradient_bound
          (EinsteinFull.Work.W8.density_bounds first) P Q.measure rfl Q.stationary

end EinsteinFull.Blueprint
