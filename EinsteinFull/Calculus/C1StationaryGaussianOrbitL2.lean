import EinsteinFull.Work.W6.HorizontalPhysicalRealizationProof
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinRelation.External.AKM
/-- Stationary complex L² representatives have Gaussian-weighted spatial L²
orbits on one event for every positive Gaussian width. -/
theorem ae_stationary_spatial_orbit_gaussian_memLp
    (d : ℕ) (hd : 2 ≤ d) (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (hQ : IsStationary Q) (f : Lp ℂ 2 Q) :
    ∀ᵐ ω ∂Q, ∀ r : ℝ, 0 < r →
      MemLp (fun x : Vec d => (Real.exp (-euclideanSq x/r) : ℂ) *
        f (translate x ω)) 2 volume := by
  have hdpos : 0 < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
  have hs : Continuous (euclideanSq : Vec d → ℝ) := by
    unfold euclideanSq dot
    fun_prop
  have hf : Measurable f := (Lp.stronglyMeasurable f).measurable
  have hsq : Integrable (fun ω => ‖f ω‖ ^ 2) Q :=
    (memLp_two_iff_integrable_sq_norm (Lp.memLp f).aestronglyMeasurable).mp (Lp.memLp f)
  have hmeas (r : ℝ) (ω : FieldPair d) : AEStronglyMeasurable
      (fun x : Vec d => (Real.exp (-euclideanSq x/r) : ℂ) * f (translate x ω)) volume := by
    apply Measurable.aestronglyMeasurable
    exact (Complex.measurable_ofReal.comp
      (Real.continuous_exp.comp (hs.neg.div_const r)).measurable).mul
      (hf.comp (Probability.continuous_translate.measurable.comp
        (measurable_id.prodMk measurable_const)))
  have hnorm (r : ℝ) (ω : FieldPair d) (x : Vec d) :
      ‖(Real.exp (-euclideanSq x/r) : ℂ) * f (translate x ω)‖ ^ 2 =
        Real.exp (-(2/r) * euclideanSq x) * ‖f (translate x ω)‖ ^ 2 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_pow]
    rw [← Real.exp_nat_mul]
    congr 2
    push_cast
    ring
  have hn (n : ℕ) : ∀ᵐ ω ∂Q,
      MemLp (fun x : Vec d => (Real.exp (-euclideanSq x/((n:ℝ)+d)) : ℂ) *
        f (translate x ω)) 2 volume := by
    let κ : ℝ := 2 / ((n : ℝ)+d)
    have hκ : 0 < κ := by dsimp only [κ]; positivity
    have hg : Integrable (fun x : Vec d => Real.exp (-κ * euclideanSq x)) := by
      have hp : Integrable (fun x : Vec d => ∏ j : Fin d, Real.exp (-κ * x j ^ 2))
          (Measure.pi fun _ : Fin d => (volume : Measure ℝ)) :=
        Integrable.fintype_prod (fun _ => integrable_exp_neg_mul_sq hκ)
      convert hp using 1
      funext x
      rw [← Real.exp_sum]
      congr 1
      simp only [euclideanSq, dot, ← Finset.mul_sum, sq]
    let g : Vec d × FieldPair d → ℝ := fun p =>
      Real.exp (-κ * euclideanSq p.1) * ‖f (translate p.1 p.2)‖ ^ 2
    have hgm : Measurable g :=
      (Real.continuous_exp.comp ((hs.comp continuous_fst).const_mul (-κ))).measurable.mul
        ((hf.comp Probability.continuous_translate.measurable).norm.pow_const 2)
    have hgi : Integrable g (volume.prod Q) := by
      apply (integrable_prod_iff hgm.aestronglyMeasurable).mpr
      constructor
      · exact ae_of_all _ fun x =>
          ((measurePreserving_translate Q hQ x).integrable_comp_of_integrable hsq).const_mul
            (Real.exp (-κ * euclideanSq x))
      · have heq (x : Vec d) : (∫ ω, ‖g (x, ω)‖ ∂Q) =
            Real.exp (-κ * euclideanSq x) * ∫ ω, ‖f ω‖ ^ 2 ∂Q := by
          have hm := measurePreserving_translate Q hQ x
          simp only [g, norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
            abs_pow, abs_norm, integral_const_mul]
          congr 1
          exact (integral_map hm.measurable.aemeasurable
            (hf.norm.pow_const 2).aestronglyMeasurable).symm.trans
            (congrArg (fun μ : Measure (FieldPair d) => ∫ ω, ‖f ω‖ ^ 2 ∂μ) hm.map_eq)
        simpa only [heq] using hg.mul_const (∫ ω, ‖f ω‖ ^ 2 ∂Q)
    filter_upwards [hgi.prod_left_ae] with ω hω
    apply (memLp_two_iff_integrable_sq_norm (hmeas _ ω)).mpr
    simpa only [hnorm, κ, g] using hω
  filter_upwards [ae_all_iff.mpr hn] with ω hω
  intro r hr
  obtain ⟨n, hn⟩ := exists_nat_gt r
  apply (hω n).mono (hmeas r ω)
  apply ae_of_all
  intro x
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply Real.exp_le_exp.mpr
  have hx : 0 ≤ euclideanSq x := by
    unfold euclideanSq dot
    exact Finset.sum_nonneg fun j _ => mul_self_nonneg (x j)
  have hh : euclideanSq x / ((n:ℝ)+d) ≤ euclideanSq x / r :=
    div_le_div_of_nonneg_left hx hr (by linarith)
  simpa only [neg_div] using neg_le_neg hh
end EinsteinFull.Blueprint
