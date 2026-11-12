import EinsteinRelation.Correctors.PoissonLiftLocalL2
import Mathlib.MeasureTheory.Integral.Prod

/-! Source: `paper/main.tex:735-739`. Fubini transfers a bound on the
explicit higher dimensional potential to the original potential. -/
open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM

/-- A lifted almost-everywhere bound controls the original potential on
an interior ball. The height is selected from a positive-measure interval. -/
theorem ae_abs_le_of_poissonLift_bound {d : ℕ} (u : Vec d → ℝ)
    (_hu : AEStronglyMeasurable u (volume : Measure (Vec d))) (M B : ℝ)
    (hB : ∀ᵐ x ∂(volume.restrict (ball (0 : Vec (d + 1)) (1 / 2))),
      |poissonLiftPotential u M x| ≤ B) :
    ∀ᵐ x ∂(volume.restrict (ball (0 : Vec d) (1 / 4))), |u x| ≤ B + |M| := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0
  have he := volume_preserving_piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0
  have heinv (p : ℝ × Vec d) : e.symm p = Fin.cons p.1 p.2 := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;>
      simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
  have hball : MeasurableSet (ball (0 : Vec (d + 1)) (1 / 2)) := by
    unfold ball euclideanNorm euclideanSq dot
    exact (isOpen_lt (by fun_prop) continuous_const).measurableSet
  have hall := (ae_restrict_iff' hball).mp hB
  have hp := (MeasurePreserving.symm e he).quasiMeasurePreserving.ae hall
  have hs := Measure.ae_ae_of_ae_prod hp
  obtain ⟨t, ht, htgood⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (by norm_num : (volume : Measure ℝ) (Set.Ioo (-(1 / 4)) (1 / 4)) ≠ 0)
    (ae_restrict_of_ae hs)
  have hsmall : MeasurableSet (ball (0 : Vec d) (1 / 4)) := by
    unfold ball euclideanNorm euclideanSq dot
    exact (isOpen_lt (by fun_prop) continuous_const).measurableSet
  filter_upwards [ae_restrict_of_ae htgood, ae_restrict_mem hsmall] with x hx hxball
  have hxnorm : euclideanNorm x < 1 / 4 := by
    simpa only [ball, sub_zero] using hxball
  have hxnonneg : 0 ≤ euclideanSq x := by
    change 0 ≤ ∑ i, x i * x i
    exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (x i))
  have hxsq : euclideanSq x < (1 / 4 : ℝ) ^ 2 := by
    have h := Real.sq_sqrt hxnonneg
    change (Real.sqrt (euclideanSq x)) ^ 2 = euclideanSq x at h
    change Real.sqrt (euclideanSq x) < 1 / 4 at hxnorm
    nlinarith [Real.sqrt_nonneg (euclideanSq x)]
  have hlift : Fin.cons t x ∈ ball (0 : Vec (d + 1)) (1 / 2) := by
    change Real.sqrt (euclideanSq (Fin.cons t x - 0)) < 1 / 2
    rw [sub_zero]
    apply (Real.sqrt_lt' (by norm_num)).mpr
    simp only [euclideanSq, dot, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
    change t * t + euclideanSq x < (1 / 2 : ℝ) ^ 2
    have htsq := sq_lt_sq' ht.1 ht.2
    nlinarith
  have hvalue : |u x + M * t| ≤ B := by
    rw [heinv] at hx
    simpa [poissonLiftPotential, poissonLiftBase] using hx hlift
  have htone : |t| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [ht.1, ht.2]
  have htriangle := abs_add_le (u x + M * t) (-(M * t))
  simp only [add_neg_cancel_right, abs_neg, abs_mul] at htriangle
  exact htriangle.trans (add_le_add hvalue
    (by simpa using mul_le_mul_of_nonneg_left htone (abs_nonneg M)))

end EinsteinRelation.Correctors
