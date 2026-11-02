import EinsteinRelation.Probability.ReductionInverseLocality
import Mathlib.MeasureTheory.Function.FactorsThrough

/-! # Factorization of local functionals through the reduced observations

A real function measurable for the physical joint σ-algebra `localSigma U` is a measurable
function of the literal observations of the reduced pair `reduce ω` on `U`. The observation map
takes values in the product `U → Mat d × ℝ`, which is not assumed standard Borel. Doob–Dynkin
(`Measurable.exists_eq_measurable_comp`) is applied only to the real target, which is standard
Borel. No assumption on `U` is used.

Source: `paper/main.tex:377–403` and `paper/main.tex:479–483`, where local functionals of the
environment are measured against the reduced environment.
-/

open EinsteinRelation MeasureTheory

namespace EinsteinRelation.Probability

/-- The reduced observations on `U`, pulled back along the observation itself, generate the
physical joint σ-algebra `localSigma U`. The coordinate σ-algebra of `U → Mat d × ℝ` is the
supremum of its coordinate comaps, and each coordinate of the reduced observation is the
evaluation of the reduced pair, so `localSigma_reduce_comap_eq` closes the chain. -/
private theorem comap_reducedObservation_eq {d : ℕ} (U : Set (Vec d)) :
    MeasurableSpace.comap (fun ω : FieldPair d => fun x : U => ((reduce ω).1 x, (reduce ω).2 x))
      (inferInstance : MeasurableSpace (U → Mat d × ℝ)) = localSigma U := by
  refine Eq.trans ?_ (localSigma_reduce_comap_eq U)
  have hpi : (inferInstance : MeasurableSpace (U → Mat d × ℝ)) =
      ⨆ x : U, MeasurableSpace.comap (fun y : U → Mat d × ℝ => y x) inferInstance := rfl
  rw [hpi, MeasurableSpace.comap_iSup]
  unfold localSigma
  rw [MeasurableSpace.comap_iSup]
  refine iSup_congr fun x => ?_
  rw [MeasurableSpace.comap_comp, MeasurableSpace.comap_comp]
  rfl

/-- A real function measurable for the physical joint σ-algebra on `U` factors through the
literal observations of the reduced pair on `U`, with a measurable factor. -/
theorem exists_measurable_reduced_local_factor {d : ℕ} (U : Set (Vec d))
    (G : FieldPair d → ℝ)
    (hG : @Measurable (FieldPair d) ℝ (localSigma U) inferInstance G) :
    ∃ H : (U → Mat d × ℝ) → ℝ, Measurable H ∧
      ∀ ω, G ω = H (fun x : U => ((reduce ω).1 x, (reduce ω).2 x)) := by
  have hcomap := comap_reducedObservation_eq U
  have hG' : @Measurable (FieldPair d) ℝ
      (MeasurableSpace.comap (fun ω : FieldPair d => fun x : U => ((reduce ω).1 x, (reduce ω).2 x))
        (inferInstance : MeasurableSpace (U → Mat d × ℝ))) inferInstance G :=
    hG.mono hcomap.symm.le le_rfl
  obtain ⟨H, hH, hGH⟩ := hG'.exists_eq_measurable_comp
  exact ⟨H, hH, fun ω => congrFun hGH ω⟩

/-- The bounded version: the measurable factor is clipped to `[-C, C]`. The clipped map is
measurable, is bounded everywhere, and still equals `G` on every reduced observation, because
`|G ω| ≤ C` pointwise. -/
theorem exists_bounded_measurable_reduced_local_factor {d : ℕ} (U : Set (Vec d))
    (G : FieldPair d → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hG : @Measurable (FieldPair d) ℝ (localSigma U) inferInstance G)
    (hb : ∀ ω, |G ω| ≤ C) :
    ∃ H : (U → Mat d × ℝ) → ℝ, Measurable H ∧
      (∀ y, |H y| ≤ C) ∧
      ∀ ω, G ω = H (fun x : U => ((reduce ω).1 x, (reduce ω).2 x)) := by
  obtain ⟨H, hH, hGH⟩ := exists_measurable_reduced_local_factor U G hG
  refine ⟨fun y => max (-C) (min (H y) C), measurable_const.max (hH.min measurable_const), ?_, ?_⟩
  · intro y
    rw [abs_le]
    exact ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩
  · intro ω
    obtain ⟨hlo, hhi⟩ := abs_le.mp (hb ω)
    have hmem : -C ≤ H (fun x : U => ((reduce ω).1 x, (reduce ω).2 x)) ∧
        H (fun x : U => ((reduce ω).1 x, (reduce ω).2 x)) ≤ C := by
      rw [← hGH ω]
      exact ⟨hlo, hhi⟩
    show G ω = max (-C) (min (H (fun x : U => ((reduce ω).1 x, (reduce ω).2 x))) C)
    rw [hGH ω, min_eq_left hmem.2, max_eq_right hmem.1]

end EinsteinRelation.Probability
