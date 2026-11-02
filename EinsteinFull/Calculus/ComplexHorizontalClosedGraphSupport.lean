import EinsteinFull.Calculus.ComplexTranslationSupport
import EinsteinFull.Frozen.ComplexHorizontalGradient
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Closedness of the actual complex horizontal derivative graph

Strong coordinate derivatives are characterized by the integrated orbit of the
actual translation group. The fundamental theorem of calculus and continuity
of the orbit integral give closedness on the full L2 domain.
-/

open MeasureTheory Filter
open scoped Topology

noncomputable section

namespace EinsteinFull

open EinsteinRelation

private theorem continuous_coordinate_orbit {d : ℕ} (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (hQ : IsStationary Q) (i : Fin d) (f : Lp ℂ 2 Q) :
    Continuous (fun t : ℝ => complexTranslation Q hQ (t • unitVector i) f) :=
  (continuous_complexTranslation Q hQ).comp
    ((continuous_id.smul continuous_const).prodMk continuous_const)

/-- A strong horizontal derivative differentiates the full actual translation orbit. -/
theorem HasComplexHorizontalDerivative.hasDerivAt_orbit {d : ℕ}
    {Q : Measure (FieldPair d)} {hQ : IsStationary Q} {i : Fin d}
    {f g : Lp ℂ 2 Q} (hf : HasComplexHorizontalDerivative Q hQ i f g) (t : ℝ) :
    HasDerivAt (fun s : ℝ => complexTranslation Q hQ (s • unitVector i) f)
      (complexTranslation Q hQ (t • unitVector i) g) t := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  have h := ((complexTranslation Q hQ (t • unitVector i)).continuous.tendsto g).comp hf
  change Tendsto (fun s : ℝ => complexTranslation Q hQ (t • unitVector i)
    ((s : ℂ)⁻¹ • (complexTranslation Q hQ (s • unitVector i) f - f)))
    (𝓝[≠] (0 : ℝ)) (𝓝 (complexTranslation Q hQ (t • unitVector i) g)) at h
  simp only [map_smul, map_sub] at h
  simp only [← complexTranslation_add, ← add_smul,
    ← Complex.ofReal_inv, Complex.coe_smul] at h
  exact h

/-- Integrating the actual translated derivative recovers each orbit increment. -/
theorem HasComplexHorizontalDerivative.integral_orbit {d : ℕ}
    {Q : Measure (FieldPair d)} [IsProbabilityMeasure Q] {hQ : IsStationary Q}
    {i : Fin d} {f g : Lp ℂ 2 Q} (hf : HasComplexHorizontalDerivative Q hQ i f g)
    (t : ℝ) :
    (∫ s in (0 : ℝ)..t, complexTranslation Q hQ (s • unitVector i) g) =
      complexTranslation Q hQ (t • unitVector i) f - f := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := t) (fun s _ => hf.hasDerivAt_orbit s)
    ((continuous_coordinate_orbit Q hQ i g).intervalIntegrable 0 t)
  simpa only [zero_smul, complexTranslation_zero] using h

/-- The integrated orbit identity characterizes the entire strong derivative domain. -/
theorem hasComplexHorizontalDerivative_iff_integral_orbit {d : ℕ}
    {Q : Measure (FieldPair d)} [IsProbabilityMeasure Q] {hQ : IsStationary Q}
    {i : Fin d} {f g : Lp ℂ 2 Q} :
    HasComplexHorizontalDerivative Q hQ i f g ↔
      ∀ t : ℝ, (∫ s in (0 : ℝ)..t, complexTranslation Q hQ (s • unitVector i) g) =
        complexTranslation Q hQ (t • unitVector i) f - f := by
  constructor
  · exact fun hf t => hf.integral_orbit t
  · intro h
    have hd := ((continuous_coordinate_orbit Q hQ i g).integral_hasStrictDerivAt 0 0).hasDerivAt
    simp only [zero_smul, complexTranslation_zero] at hd
    have he : (fun t : ℝ => ∫ s in (0 : ℝ)..t,
        complexTranslation Q hQ (s • unitVector i) g) =
        fun t => complexTranslation Q hQ (t • unitVector i) f - f := funext h
    rw [he, hasDerivAt_iff_tendsto_slope_zero] at hd
    unfold HasComplexHorizontalDerivative
    simp only [← Complex.ofReal_inv, Complex.coe_smul]
    simp only [zero_add, zero_smul, complexTranslation_zero, sub_self, sub_zero] at hd
    exact hd

private def coordinateOrbitIntegral {d : ℕ} (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (hQ : IsStationary Q) (i : Fin d) (t : ℝ) :
    Lp ℂ 2 Q →L[ℂ] Lp ℂ 2 Q :=
  let L : Lp ℂ 2 Q →ₗ[ℂ] Lp ℂ 2 Q :=
    { toFun := fun g => ∫ s in (0 : ℝ)..t, complexTranslation Q hQ (s • unitVector i) g
      map_add' := fun g h => by
        simp only [map_add]
        exact intervalIntegral.integral_add
          ((continuous_coordinate_orbit Q hQ i g).intervalIntegrable 0 t)
          ((continuous_coordinate_orbit Q hQ i h).intervalIntegrable 0 t)
      map_smul' := fun c g => by
        simp only [map_smul, RingHom.id_apply, intervalIntegral.integral_smul] }
  L.mkContinuous |t| (fun g => by
    change ‖∫ s in (0 : ℝ)..t, complexTranslation Q hQ (s • unitVector i) g‖ ≤ |t| * ‖g‖
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := t)
      (fun s _ => le_of_eq (norm_complexTranslation Q hQ (s • unitVector i) g))
    simpa only [sub_zero, mul_comm] using hb)

/-- The full actual strong horizontal derivative has a closed graph in complex L2. -/
theorem isClosed_complexHorizontalDerivative_graph {d : ℕ} (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (hQ : IsStationary Q) (i : Fin d) :
    IsClosed {p : Lp ℂ 2 Q × Lp ℂ 2 Q |
      HasComplexHorizontalDerivative Q hQ i p.1 p.2} := by
  have hs : {p : Lp ℂ 2 Q × Lp ℂ 2 Q |
      HasComplexHorizontalDerivative Q hQ i p.1 p.2} =
      ⋂ t : ℝ, {p : Lp ℂ 2 Q × Lp ℂ 2 Q |
        coordinateOrbitIntegral Q hQ i t p.2 =
          complexTranslation Q hQ (t • unitVector i) p.1 - p.1} := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_iInter,
      hasComplexHorizontalDerivative_iff_integral_orbit]
    rfl
  rw [hs]
  exact isClosed_iInter fun t => isClosed_eq
    ((coordinateOrbitIntegral Q hQ i t).continuous.comp continuous_snd)
    (((complexTranslation Q hQ (t • unitVector i)).continuous.comp continuous_fst).sub
      continuous_fst)

/-- The full actual horizontal H1 gradient graph is closed, with all coordinates together. -/
theorem isClosed_complexHorizontalGradient_graph {d : ℕ} (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (hQ : IsStationary Q) :
    IsClosed {p : Lp ℂ 2 Q × (Fin d → Lp ℂ 2 Q) |
      HasComplexHorizontalGradient Q hQ p.1 p.2} := by
  have hs : {p : Lp ℂ 2 Q × (Fin d → Lp ℂ 2 Q) |
      HasComplexHorizontalGradient Q hQ p.1 p.2} =
      ⋂ i : Fin d, {p : Lp ℂ 2 Q × (Fin d → Lp ℂ 2 Q) |
        HasComplexHorizontalDerivative Q hQ i p.1 (p.2 i)} := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_iInter, HasComplexHorizontalGradient]
  rw [hs]
  refine isClosed_iInter fun i => ?_
  have hc : Continuous (fun p : Lp ℂ 2 Q × (Fin d → Lp ℂ 2 Q) => (p.1, p.2 i)) :=
    continuous_fst.prodMk ((continuous_apply i).comp continuous_snd)
  exact IsClosed.preimage hc (isClosed_complexHorizontalDerivative_graph Q hQ i)

/-- Strong L2 limits preserve the entire actual horizontal H1 gradient relation. -/
theorem complexHorizontalGradient_of_tendsto {d : ℕ} {ι : Type*}
    {Q : Measure (FieldPair d)} [IsProbabilityMeasure Q] {hQ : IsStationary Q}
    {l : Filter ι} [NeBot l]
    {p : ι → Lp ℂ 2 Q × (Fin d → Lp ℂ 2 Q)}
    {q : Lp ℂ 2 Q × (Fin d → Lp ℂ 2 Q)}
    (hp : ∀ᶠ n in l, HasComplexHorizontalGradient Q hQ (p n).1 (p n).2)
    (hlim : Tendsto p l (𝓝 q)) :
    HasComplexHorizontalGradient Q hQ q.1 q.2 :=
  (isClosed_complexHorizontalGradient_graph Q hQ).mem_of_tendsto hlim hp

end EinsteinFull
