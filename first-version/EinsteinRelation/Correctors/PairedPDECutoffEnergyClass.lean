import EinsteinRelation.Correctors.PairedPDETesting
import EinsteinRelation.Correctors.SpatialWeakProduct

/-! # Spatial energy of the actual solution-dependent cutoff

Source: `paper/main.tex:832–840`. The product-rule field is in L² and is
the spatial weak gradient on almost every time slice. No derivative of the
solution in time is assumed.
-/

open MeasureTheory
open scoped ENNReal

namespace EinsteinRelation.Correctors

open External.AKM Environment.AKMTestIntegralSupport

/-- Euclidean energy controls every coordinate of the weak gradient.
Source: `paper/main.tex:832–840`. -/
theorem parabolicSolution_gradient_coordinate_memLp {d : ℕ} {K : ℝ}
    {A : Coefficient d K} {I : Set ℝ} {U : Set (Vec d)}
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hsol : IsParabolicSolution A I U u G) (j : Fin d) :
    MemLp (fun z => G z j) 2 (volume.restrict (I ×ˢ U)) := by
  apply hsol.2.2.1.of_le ((continuous_apply j).comp_aestronglyMeasurable hsol.2.1)
  exact Filter.Eventually.of_forall fun z => by
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (show 0 ≤ euclideanNorm (G z) from Real.sqrt_nonneg _)]
    apply Real.abs_le_sqrt
    change G z j ^ 2 ≤ ∑ k : Fin d, G z k * G z k
    rw [sq]
    exact Finset.single_le_sum (fun k _ => mul_self_nonneg (G z k))
      (Finset.mem_univ j)

/-- Multiplication by a smooth compact cutoff preserves the actual spatial
energy class. Source: `paper/main.tex:832–840`. -/
theorem parabolicSolution_cutoff_energy_class {d : ℕ} {K : ℝ}
    {A : Coefficient d K} {I : Set ℝ} {U : Set (Vec d)} (hU : IsOpen U)
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hsol : IsParabolicSolution A I U u G)
    {ζ : ℝ × Vec d → ℝ} (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hζc : HasCompactSupport ζ) :
    MemLp (fun z => ζ z * u z) 2 (volume.restrict (I ×ˢ U)) ∧
      (∀ j : Fin d, MemLp
        (fun z => ζ z * G z j + u z * fderiv ℝ ζ z (0, unitVector j)) 2
        (volume.restrict (I ×ˢ U))) ∧
      ∀ᵐ t ∂volume.restrict I,
        HasWeakGradient U (fun x => ζ (t, x) * u (t, x))
          (fun x j => ζ (t, x) * G (t, x) j +
            u (t, x) * fderiv ℝ ζ (t, x) (0, unitVector j)) := by
  have hζm : MemLp ζ ∞ (volume.restrict (I ×ˢ U)) :=
    hζ.continuous.memLp_top_of_hasCompactSupport hζc _
  refine ⟨hsol.1.mul' hζm, ?_, ?_⟩
  · intro j
    have hdc : Continuous (fun z => fderiv ℝ ζ z (0, unitVector j)) :=
      ((contDiff_infty_iff_fderiv.mp hζ).2.clm_apply contDiff_const).continuous
    have hd : MemLp (fun z => fderiv ℝ ζ z (0, unitVector j)) ∞
        (volume.restrict (I ×ˢ U)) :=
      hdc.memLp_top_of_hasCompactSupport (hζc.fderiv_apply ℝ (0, unitVector j)) _
    exact ((parabolicSolution_gradient_coordinate_memLp hsol j).mul' hζm).add
      (hd.mul' hsol.1)
  · filter_upwards [hsol.2.2.2.1] with t ht
    have hs : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec d => ζ (t, x)) :=
      hζ.comp (contDiff_const.prodMk contDiff_id)
    have hg := hasWeakGradient_mul_smooth hU ht hs
    convert hg using 1
    ext x j
    congr 2
    change _ = fderiv ℝ (ζ ∘ fun y : Vec d => (t, y)) x (unitVector j)
    have hpair := hasFDerivAt_prodMk_right (𝕜 := ℝ) t x
    rw [fderiv_comp x (hζ.differentiable (by simp) (t, x)) hpair.differentiableAt,
      hpair.fderiv]
    rfl

end EinsteinRelation.Correctors
