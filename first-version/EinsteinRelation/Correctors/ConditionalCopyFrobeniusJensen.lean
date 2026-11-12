import EinsteinRelation.Correctors.ConditionalCopyEuclideanJensen
import EinsteinRelation.Environment.MatrixNorm
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace EinsteinRelation.Correctors

/-- Source: paper/main.tex:878–886. Conditional-copy Jensen with the literal
entrywise conditional expectation and Frobenius norm. Flatten the matrix
into EuclideanSpace indexed by Fin d × Fin d, then use the Euclidean copy
theorem and continuous linear coordinate projections. -/
theorem eLpNorm_conditional_error_frobenius_le_copy_difference
    {d : ℕ} {A B : Type} [MeasurableSpace A] [StandardBorelSpace A]
    [Nonempty A] [MeasurableSpace B] (Q : Measure A) [IsProbabilityMeasure Q]
    (X : A → B) (hX : Measurable X) {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞)
    {f : A → Mat d} (hfm : Measurable f)
    (hf : ∀ i j, Integrable (fun ω => f ω i j) Q) :
    eLpNorm (fun ω => frobeniusNorm (Matrix.of (fun i j => f ω i j -
      condExp ((inferInstance : MeasurableSpace B).comap X) Q
        (fun ω' => f ω' i j) ω))) p Q ≤
    eLpNorm (fun z : B × (A × A) => frobeniusNorm (f z.2.1 - f z.2.2)) p
      ((Q.map X) ⊗ₘ (condDistrib (id : A → A) X Q ×ₖ
        condDistrib (id : A → A) X Q)) := by
  let φ : Mat d → EuclideanSpace ℝ (Fin d × Fin d) :=
    fun M => WithLp.toLp 2 (fun ij => M ij.1 ij.2)
  have hnorm (M : Mat d) : frobeniusNorm M = ‖φ M‖ := by
    rw [frobeniusNorm, EuclideanSpace.norm_eq]
    congr 1
    change (∑ i : Fin d, ∑ j : Fin d, M i j * M i j) =
      ∑ ij : Fin d × Fin d, ‖M ij.1 ij.2‖ ^ 2
    simp_rw [Real.norm_eq_abs, sq_abs, ← pow_two]
    rw [← Finset.sum_product', Finset.univ_product_univ]
  let g : A → EuclideanSpace ℝ (Fin d × Fin d) := fun ω => φ (f ω)
  have hgm : Measurable g := by
    apply (PiLp.continuous_toLp 2 (fun _ : Fin d × Fin d => ℝ)).measurable.comp
    apply measurable_pi_lambda
    intro ij
    have he : Continuous (fun M : Mat d => M ij.1 ij.2) :=
      (continuous_apply ij.2).comp (continuous_apply ij.1)
    exact he.measurable.comp hfm
  have hgi : Integrable g Q := Integrable.of_eval_piLp (fun ij => hf ij.1 ij.2)
  let ambientSpace : MeasurableSpace A := inferInstance
  let m : MeasurableSpace A := (inferInstance : MeasurableSpace B).comap X
  letI : MeasurableSpace A := ambientSpace
  have hc (ij : Fin d × Fin d) : (fun ω => (condExp m Q g ω) ij) =ᵐ[Q]
      condExp m Q (fun ω => f ω ij.1 ij.2) :=
    (PiLp.proj 2 (fun _ : Fin d × Fin d => ℝ) ij).comp_condExp_comm hgi
  have hleft : eLpNorm (fun ω => frobeniusNorm (Matrix.of (fun i j => f ω i j -
      condExp m Q (fun ω' => f ω' i j) ω))) p Q =
      eLpNorm (g - condExp m Q g) p Q := by
    rw [← eLpNorm_norm (g - condExp m Q g)]
    apply eLpNorm_congr_ae
    filter_upwards [ae_all_iff.mpr hc] with ω hω
    rw [hnorm]
    congr 1
    ext ij
    change f ω ij.1 ij.2 - condExp m Q (fun ω' => f ω' ij.1 ij.2) ω =
      f ω ij.1 ij.2 - (condExp m Q g ω) ij
    rw [hω ij]
  rw [hleft]
  refine (eLpNorm_conditional_error_piL2_le_copy_difference
    (Fin d × Fin d) Q X hX hp hpt hgm hgi).trans_eq ?_
  rw [← eLpNorm_norm]
  apply eLpNorm_congr_ae
  filter_upwards [] with z
  rw [hnorm]
  rfl

end EinsteinRelation.Correctors
