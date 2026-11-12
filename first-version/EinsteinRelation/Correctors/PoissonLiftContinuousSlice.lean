import EinsteinRelation.Correctors.PoissonLiftSliceBound

/-! Source: `paper/main.tex:735-743`. A continuous version of the lifted
potential restricts on a Fubini-selected height to a continuous version of
the original potential. -/
open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM

/-- A small product cylinder lies inside the lifted half ball. -/
theorem poissonLift_cons_mem_half_ball {d : ℕ} {t : ℝ} {x : Vec d}
    (ht : t ∈ Set.Ioo (-(1 / 4 : ℝ)) (1 / 4)) (hx : x ∈ ball 0 (1 / 4)) :
    Fin.cons t x ∈ ball (0 : Vec (d + 1)) (1 / 2) := by
  have hxnorm : euclideanNorm x < 1 / 4 := by simpa only [ball, sub_zero] using hx
  have hxn : 0 ≤ euclideanSq x := by
    change 0 ≤ ∑ i, x i * x i
    exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (x i))
  have hxsq : euclideanSq x < (1 / 4 : ℝ) ^ 2 := by
    have h := Real.sq_sqrt hxn
    change (Real.sqrt (euclideanSq x)) ^ 2 = euclideanSq x at h
    change Real.sqrt (euclideanSq x) < 1 / 4 at hxnorm
    nlinarith [Real.sqrt_nonneg (euclideanSq x)]
  change Real.sqrt (euclideanSq (Fin.cons t x - 0)) < 1 / 2
  rw [sub_zero]
  apply (Real.sqrt_lt' (by norm_num)).mpr
  simp only [euclideanSq, dot, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
  change t * t + euclideanSq x < (1 / 2 : ℝ) ^ 2
  nlinarith [sq_lt_sq' ht.1 ht.2]

/-- Fubini selects a height on which the continuous lifted potential has
its prescribed spatial volume class. -/
theorem exists_continuousOn_of_poissonLift_representative {d : ℕ}
    (u : Vec d → ℝ) (M : ℝ) (v : Vec (d + 1) → ℝ)
    (hv : ContinuousOn v (ball 0 (1 / 2)))
    (heq : v =ᵐ[volume.restrict (ball 0 (1 / 2))] poissonLiftPotential u M) :
    ∃ w : Vec d → ℝ, ContinuousOn w (ball 0 (1 / 4)) ∧
      u =ᵐ[volume.restrict (ball 0 (1 / 4))] w := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0
  have he := volume_preserving_piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0
  have heinv (p : ℝ × Vec d) : e.symm p = Fin.cons p.1 p.2 := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;>
      simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
  have hball : MeasurableSet (ball (0 : Vec (d + 1)) (1 / 2)) := by
    unfold ball euclideanNorm euclideanSq dot
    exact (isOpen_lt (by fun_prop) continuous_const).measurableSet
  have hp := (MeasurePreserving.symm e he).quasiMeasurePreserving.ae
    ((ae_restrict_iff' hball).mp heq)
  have hs := Measure.ae_ae_of_ae_prod hp
  obtain ⟨t, ht, htgood⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (by norm_num : (volume : Measure ℝ) (Set.Ioo (-(1 / 4)) (1 / 4)) ≠ 0)
    (ae_restrict_of_ae hs)
  refine ⟨fun x => v (Fin.cons t x) - M * t, ?_, ?_⟩
  · have hcons : Continuous (fun x : Vec d => (Fin.cons t x : Vec (d + 1))) := by
      apply continuous_pi
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa only [Fin.cons_zero] using
          (continuous_const : Continuous (fun _ : Vec d => t))
      · simpa only [Fin.cons_succ] using
          (continuous_apply j : Continuous (fun x : Vec d => x j))
    exact (hv.comp hcons.continuousOn
      (fun x hx => poissonLift_cons_mem_half_ball ht hx)).sub continuousOn_const
  · have hsmall : MeasurableSet (ball (0 : Vec d) (1 / 4)) := by
      unfold ball euclideanNorm euclideanSq dot
      exact (isOpen_lt (by fun_prop) continuous_const).measurableSet
    filter_upwards [ae_restrict_of_ae htgood, ae_restrict_mem hsmall] with x hx hxball
    rw [heinv] at hx
    have hx' : v (Fin.cons t x) = u x + M * t := by
      simpa [poissonLiftPotential] using hx (poissonLift_cons_mem_half_ball ht hxball)
    rw [hx']
    ring

end EinsteinRelation.Correctors
