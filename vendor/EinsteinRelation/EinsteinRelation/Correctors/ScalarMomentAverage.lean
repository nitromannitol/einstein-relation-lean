import EinsteinRelation.Correctors.SpatialMomentAverage

/-! # Scalar root-mean-square moments

Source: `paper/main.tex:788–796,834–845`. A scalar spatial or space-time
root-mean-square inherits uniform pointwise probability moments. The proof
uses the already checked Euclidean average estimate in dimension one.
-/

open MeasureTheory

namespace EinsteinRelation.Correctors

/-- Uniform scalar moments control the genuine root-mean-square of any
probability average. Source: `paper/main.tex:788–796,834–845`. -/
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
    (WithLp.measurable_toLp 2 _).comp (Measurable.of_eval fun _ => hf)
  have hn (z : Ω × X) : ‖g z‖ = ‖f z‖ := by
    rw [EuclideanSpace.norm_eq]
    simp [g, Real.sqrt_sq_eq_abs]
  have hgmom (x : X) : MemLp (fun ω => g (ω, x)) (ENNReal.ofReal p) Q ∧
      eLpNorm (fun ω => g (ω, x)) (ENNReal.ofReal p) Q ≤ ENNReal.ofReal C := by
    have hgx : AEStronglyMeasurable (fun ω => g (ω, x)) Q :=
      (hg.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
    have hfx : AEStronglyMeasurable (fun ω => f (ω, x)) Q :=
      (hf.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
    have he := eLpNorm_congr_norm_ae (μ := Q) (p := ENNReal.ofReal p) hgx hfx
      (Filter.Eventually.of_forall fun ω => hn (ω, x))
    exact ⟨memLp_iff.mpr (he.trans_lt (memLp_iff.mp (hmom x).1)), he.trans_le (hmom x).2⟩
  have h := spatialL2_average_moment_le Q ν hp hC g hg hgmom
  refine ⟨h.1.mono fun ω hω => ?_, ?_⟩
  · have hfx : AEStronglyMeasurable (fun x => f (ω, x)) ν :=
      (hf.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    have h1 : MemLp (fun x => ‖g (ω, x)‖) 2 ν := hω.norm
    have h2 : (fun x => ‖g (ω, x)‖) = fun x => ‖f (ω, x)‖ := funext fun x => hn (ω, x)
    rw [h2] at h1
    exact (memLp_norm_iff hfx).mp h1
  · have e : (fun ω => Real.sqrt (∫ x, ‖g (ω, x)‖ ^ 2 ∂ν)) =
        fun ω => Real.sqrt (∫ x, f (ω, x) ^ 2 ∂ν) := by
      funext ω
      simp only [hn, Real.norm_eq_abs, sq_abs]
    have h2 := h.2
    rw [e] at h2
    exact h2

end EinsteinRelation.Correctors
