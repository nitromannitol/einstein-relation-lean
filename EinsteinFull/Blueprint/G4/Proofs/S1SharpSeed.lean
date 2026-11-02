import EinsteinFull.Blueprint.G4.node_sharp_u2E_example_u23_smooth_u2D_seed
import EinsteinFull.Blueprint.G4.node_sharp_u2E_example_u23_seed_u2D_nonconstancy
import EinsteinRelation.Sharpness.SeedFieldStationarity
import EinsteinRelation.Sharpness.SeedFieldFiniteRange
import EinsteinRelation.Sharpness.SeedFieldMean
import EinsteinRelation.Sharpness.SeedFieldDerivatives
import EinsteinRelation.Sharpness.SeedLawNondegeneracy

/-! Reductions of graph nodes `sharp.example#smooth-seed` (`paper/main.tex:1528–1533`) and
`sharp.example#seed-nonconstancy` (`paper/main.tex:1529`). Both are instances of the proved
canonical-seed API of the sharpness construction, for the supplied white-noise law. -/

open MeasureTheory Filter
open scoped Topology

namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinRelation.Sharpness

theorem node_sharp_u2E_example_u23_smooth_u2D_seed_of_deps :
    node_sharp_u2E_example_u23_smooth_u2D_seedStmt := by
  intro d _hd P hP shift
  exact ⟨contDiff_seedField d, fun x => integrable_and_integral_seedField_eq_zero hP x,
    fun x => map_seedFieldLaw_translate d hP x,
    fun S T xs ys hsep => indepFun_seedField_processes_of_separated hP S T xs ys hsep,
    fun k => exists_uniform_seedField_derivative_bound d k,
    EinsteinFull.Work.W8.seedScale_pos d,
    fun W x => EinsteinFull.Work.W8.corrector_gradient_bound W x⟩

private theorem abs_coord_le_euclideanNorm_sharp {d : ℕ} (v : Vec d) (i : Fin d) :
    |v i| ≤ euclideanNorm v := by
  unfold euclideanNorm
  apply Real.abs_le_sqrt
  rw [sq]
  exact Finset.single_le_sum (f := fun j => v j * v j) (fun j _ => mul_self_nonneg _)
    (Finset.mem_univ i)

theorem node_sharp_u2E_example_u23_seed_u2D_nonconstancy_of_deps :
    node_sharp_u2E_example_u23_seed_u2D_nonconstancyStmt := by
  intro d hd P hP
  haveI : IsProbabilityMeasure P := hP.1
  have h0 : ∀ c : ℝ, ¬ ((fun W => seedField d W 0) =ᵐ[P] fun _ => c) :=
    fun c => seedField_zero_not_ae_eq_const hP c
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨c, hc⟩
    exact h0 c hc
  · intro h
    let i : Fin d := ⟨0, by omega⟩
    let z : Vec d := Pi.single i (5 : ℝ)
    have hz : (4 : ℝ) < euclideanNorm ((0 : Vec d) - z) := by
      have h1 := abs_coord_le_euclideanNorm_sharp ((0 : Vec d) - z) i
      have h2 : |((0 : Vec d) - z) i| = 5 := by simp [z]
      linarith
    have hind := indepFun_seedField_processes_of_separated hP Unit Unit
      (fun _ => (0 : Vec d)) (fun _ => z) (fun _ _ => hz)
    have hS : MeasurableSet {v : Unit → ℝ | 0 < v ()} :=
      measurableSet_lt measurable_const (measurable_pi_apply ())
    have hT : MeasurableSet {v : Unit → ℝ | v () < 0} :=
      measurableSet_lt (measurable_pi_apply ()) measurable_const
    have hfac := hind.measure_inter_preimage_eq_mul _ _ hS hT
    obtain ⟨hp, hn⟩ := positive_probability_seedField_signs hP
    have hB : P ((fun W : NoiseSample d => fun _ : Unit => seedField d W z) ⁻¹'
        {v : Unit → ℝ | v () < 0}) = P {W | seedField d W 0 < 0} := by
      refine measure_congr ?_
      filter_upwards [h] with W hW
      exact propext (by simp only [Set.mem_preimage, Set.mem_setOf_eq, hW z])
    have hA : P ((fun W : NoiseSample d => fun _ : Unit => seedField d W 0) ⁻¹'
        {v : Unit → ℝ | 0 < v ()}) = P {W | 0 < seedField d W 0} := rfl
    have hint : P ((fun W : NoiseSample d => fun _ : Unit => seedField d W 0) ⁻¹'
        {v : Unit → ℝ | 0 < v ()} ∩ (fun W : NoiseSample d => fun _ : Unit => seedField d W z) ⁻¹'
        {v : Unit → ℝ | v () < 0}) = 0 := by
      rw [measure_eq_zero_iff_ae_notMem]
      filter_upwards [h] with W hW
      rintro ⟨h1, h2⟩
      simp only [Set.mem_preimage, Set.mem_setOf_eq, hW z] at h1 h2
      linarith
    rw [hint, hA, hB] at hfac
    exact ((ENNReal.mul_pos hp.ne' hn.ne').ne hfac).elim
  · simp only [(integrable_and_integral_seedField_eq_zero hP 0).2, sub_zero]
    have hint : Integrable (fun W : NoiseSample d => seedField d W 0 ^ 2) P := by
      refine Integrable.of_bound (C := 1)
        ((measurable_seedField d 0).pow_const 2).aestronglyMeasurable ?_
      refine Filter.Eventually.of_forall fun W => ?_
      have h1 := abs_seedField_le_one d W 0
      rw [Real.norm_eq_abs, abs_pow]
      calc |seedField d W 0| ^ 2 ≤ 1 ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
        _ = 1 := one_pow 2
    refine lt_of_le_of_ne (integral_nonneg fun W => sq_nonneg _) ?_
    intro heq
    have hae := (integral_eq_zero_iff_of_nonneg (fun W => sq_nonneg (seedField d W 0)) hint).1
      heq.symm
    refine h0 0 ?_
    filter_upwards [hae] with W hW
    exact pow_eq_zero_iff (two_ne_zero) |>.1 hW

end EinsteinFull.Blueprint
