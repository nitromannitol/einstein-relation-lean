import EinsteinRelation.Correctors.SpatialMomentAverage

/-! # Scalar root-mean-square moments

Source: `paper/main.tex:798–806,844–855`. A scalar spatial or space-time
root-mean-square inherits uniform pointwise probability moments. The proof
uses the already checked Euclidean average estimate in dimension one.
-/

open MeasureTheory

namespace EinsteinRelation.Correctors

/-- Uniform scalar moments control the genuine root-mean-square of any
probability average. Source: `paper/main.tex:798–806,844–855`. -/
theorem scalarL2_average_moment_le {Ω X : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (ν : Measure X) [IsProbabilityMeasure ν] {p C : ℝ} (hp : 2 ≤ p) (hC : 0 ≤ C)
    (f : Ω × X → ℝ) (hf : Measurable f)
    (hmom : ∀ x, MemLp (fun ω => f (ω, x)) (ENNReal.ofReal p) Q ∧
      eLpNorm (fun ω => f (ω, x)) (ENNReal.ofReal p) Q ≤ ENNReal.ofReal C) :
    (∀ᵐ ω ∂Q, MemLp (fun x => f (ω, x)) 2 ν) ∧
      MemLp (fun ω => Real.sqrt (∫ x, f (ω, x) ^ 2 ∂ν)) (ENNReal.ofReal p) Q ∧
      eLpNorm (fun ω => Real.sqrt (∫ x, f (ω, x) ^ 2 ∂ν)) (ENNReal.ofReal p) Q ≤
        ENNReal.ofReal C := by
  let g : Ω × X → EuclideanSpace ℝ (Fin 1) :=
    fun z => WithLp.toLp 2 (fun _ => f z)
  have hg : Measurable g :=
    (WithLp.measurable_toLp 2 _).comp (measurable_pi_lambda _ fun _ => hf)
  have hn (z : Ω × X) : ‖g z‖ = ‖f z‖ := by
    rw [EuclideanSpace.norm_eq]
    simp [g, Real.sqrt_sq_eq_abs]
  have hgmom (x : X) : MemLp (fun ω => g (ω, x)) (ENNReal.ofReal p) Q ∧
      eLpNorm (fun ω => g (ω, x)) (ENNReal.ofReal p) Q ≤ ENNReal.ofReal C := by
    have he := eLpNorm_congr_norm_ae (μ := Q) (p := ENNReal.ofReal p)
      (Filter.Eventually.of_forall fun ω => hn (ω, x))
    exact ⟨⟨(hg.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable,
      he.trans_lt (hmom x).1.2⟩, he.trans_le (hmom x).2⟩
  have h := spatialL2_average_moment_le Q ν hp hC g hg hgmom
  refine ⟨h.1.mono fun ω hω => ?_, ?_⟩
  · apply (memLp_norm_iff
      (hf.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable).mp
    simpa only [hn] using hω.norm
  · simpa only [hn, Real.norm_eq_abs, sq_abs] using h.2

end EinsteinRelation.Correctors
