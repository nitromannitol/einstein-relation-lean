import EinsteinFull.Blueprint.G4.node_sharp_u2E_example_u23_smooth_u2D_seed
import EinsteinFull.Blueprint.G4.node_sharp_u2E_example_u23_seed_u2D_ergodicity
import EinsteinFull.Calculus.S2SeedErgodicitySupport
import EinsteinRelation.Sharpness.SeedFieldStationarity

/-! Reduction of graph node `sharp.example#seed-ergodicity` (`paper/main.tex:1572`) to
`sharp.example#smooth-seed`: the stationary, finite-range seed law is translation ergodic by the
finite-range zero-one argument (`EinsteinFull.seedLaw_zero_one`). -/

open MeasureTheory Filter
open scoped Topology

namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinRelation.Sharpness

theorem node_sharp_u2E_example_u23_seed_u2D_ergodicity_of_deps
    (hseed : node_sharp_u2E_example_u23_smooth_u2D_seedStmt) :
    node_sharp_u2E_example_u23_seed_u2D_ergodicityStmt := by
  intro d hd P hP shift
  letI : MeasurableSpace C(Vec d, ℝ) := borel C(Vec d, ℝ)
  haveI : BorelSpace C(Vec d, ℝ) := ⟨rfl⟩
  haveI : IsProbabilityMeasure (seedFieldLaw P) := isProbabilityMeasure_seedFieldLaw hP
  obtain ⟨-, -, hstat, hindep, -⟩ := hseed d hd P hP
  have hd0 : 0 < d := by omega
  have hindL : ∀ (S T : Type) (xs : S → Vec d) (ys : T → Vec d),
      (∀ s t, 4 < euclideanNorm (xs s - ys t)) →
      ProbabilityTheory.IndepFun (fun H : C(Vec d, ℝ) => fun s => H (xs s))
        (fun H : C(Vec d, ℝ) => fun t => H (ys t)) (seedFieldLaw P) := by
    intro S T xs ys hsep
    have hX : Measurable (fun H : C(Vec d, ℝ) => fun s : S => H (xs s)) :=
      measurable_pi_iff.mpr fun s => (continuous_eval_const (xs s)).measurable
    have hY : Measurable (fun H : C(Vec d, ℝ) => fun t : T => H (ys t)) :=
      measurable_pi_iff.mpr fun t => (continuous_eval_const (ys t)).measurable
    have e : ∀ A : Set C(Vec d, ℝ), MeasurableSet A →
        seedFieldLaw P A = P (seedContinuousField d ⁻¹' A) := by
      intro A hA
      unfold seedFieldLaw
      exact Measure.map_apply (measurable_seedContinuousField d) hA
    refine ProbabilityTheory.indepFun_iff_measure_inter_preimage_eq_mul.2 ?_
    intro u v hu hv
    have h := (hindep S T xs ys hsep).measure_inter_preimage_eq_mul u v hu hv
    rw [e _ ((hX hu).inter (hY hv)), e _ (hX hu), e _ (hY hv)]
    exact h
  refine ⟨fun E hE hinv => ?_, fun F hF hinv => ?_⟩
  · exact EinsteinFull.seedLaw_zero_one hd0 (seedFieldLaw P) (fun x => hstat x) hindL hE
      (fun x => hinv x)
  · obtain ⟨c, hc⟩ := EinsteinFull.exists_ae_eq_const_of_zero_one (seedFieldLaw P) F hF
      fun q => EinsteinFull.seedLaw_zero_one hd0 (seedFieldLaw P) (fun x => hstat x) hindL
        (measurableSet_le hF measurable_const) fun x => by
          filter_upwards [hinv x] with H hH
          show F (shift x H) ≤ q ↔ F H ≤ q
          rw [hH]
    exact ⟨c, hc⟩

end EinsteinFull.Blueprint
