import EinsteinRelation.Correctors.ParabolicCylinderEnergy

/-! # Unweighted cylinder gradient moments for the selected AKM flow

Source: `paper/main.tex:798–806`. The scalar estimate of AKM Theorem 9.1
and the proved weak energy estimate apply to one measurable coefficient-column
flow. The inverse-radius gain is derived from the constructed cutoff.
-/

open MeasureTheory
open scoped ENNReal

namespace EinsteinRelation.Correctors
open External.AKM External.GilbargTrudinger Environment.AKMTestIntegralSupport

/-- The actual source-selected coefficient-column flow has unweighted
space-time gradient moments. The same flow works for every radius and
moment; the constant precedes the environment law.
Source: `paper/main.tex:798–806`. -/
theorem parabolicSemigroupDecay_actual_column_cylinder_gradient_moments
    (hAKM : ParabolicSemigroupDecay) (d : ℕ) (hd : 2 ≤ d)
    (K s : ℝ) (hK : 1 < K) (hs : 0 < s) (hs2 : s < 2) :
    ∃ C : ℝ → ℝ, (∀ m : ℝ, 0 < m → 0 < C m) ∧
      ∀ P : Measure (Coefficient d K), IsAdmissibleLaw P → ∀ i : Fin d,
        ∃ (u : Coefficient d K → ℝ × Vec d → ℝ)
          (G : Coefficient d K → ℝ × Vec d → Vec d),
          Measurable (fun z : Coefficient d K × (ℝ × Vec d) => u z.1 z.2) ∧
          Measurable (fun z : Coefficient d K × (ℝ × Vec d) => G z.1 z.2) ∧
          (∀ᵐ A ∂P, IsSemigroupSolution A
            (fun x => (A x).mulVec (unitVector i)) (u A) (G A)) ∧
          (∀ m : ℝ, 0 < m → ∀ t : ℝ, 1 ≤ t → ∀ x : Vec d,
            MemLp (fun A => u A (t,x)) (ENNReal.ofReal m) P ∧
            eLpNorm (fun A => u A (t,x)) (ENNReal.ofReal m) P ≤
              ENNReal.ofReal (C m * t^(-(1 : ℝ)/2 - (d : ℝ)/4))) ∧
          ∀ m : ℝ, 2 ≤ m → ∀ r : ℝ, 1 ≤ r →
            MemLp (fun A => vectorRms volume
              (Set.Ioo (2*r^2) (3*r^2) ×ˢ originBall d r) (G A)) (ENNReal.ofReal m) P ∧
            eLpNorm (fun A => vectorRms volume
              (Set.Ioo (2*r^2) (3*r^2) ×ˢ originBall d r) (G A)) (ENNReal.ofReal m) P ≤
                ENNReal.ofReal (C m / r * (r^2)^(-(1 : ℝ)/2 - (d : ℝ)/4)) := by
  obtain ⟨D, hD, henergy⟩ := parabolicSolution_cylinder_rms_le d K (zero_lt_one.trans hK)
  obtain ⟨C, hC, hflow⟩ := parabolicSemigroupDecay_actual_column hAKM d hd K s hK hs hs2
  refine ⟨fun m => max D 1 * C m,
    fun m hm => mul_pos (zero_lt_one.trans_le (le_max_right _ _)) (hC m hm), ?_⟩
  intro P hP i
  letI : IsProbabilityMeasure P := hP.1
  obtain ⟨u, G, hum, hGm, hsol, hval⟩ := hflow P hP i
  refine ⟨u, G, hum, hGm, hsol, ?_, ?_⟩
  · intro m hm t ht x
    obtain ⟨hmem, hb⟩ := hval m hm t ht x
    refine ⟨hmem, hb.trans (ENNReal.ofReal_le_ofReal ?_)⟩
    have hc : C m ≤ max D 1 * C m := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (le_max_right D 1) (hC m hm).le
    exact mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg (zero_le_one.trans ht) _)
  intro m hm r hr
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have hr2 : 0 < r^2 := sq_pos_of_pos hr0
  have hr21 : 1 ≤ r^2 := by nlinarith
  have hm0 : 0 < m := zero_lt_two.trans_le hm
  let V := Set.Ioo (2*r^2) (3*r^2) ×ˢ originBall d r
  let U := Set.Ioo (r^2) (4*r^2) ×ˢ originBall d (2*r)
  let E := fun A => vectorRms volume V (G A)
  let S := fun A => scalarRms volume U (u A)
  have hUmeas : MeasurableSet U := by
    have heq : originBall d (2*r) = ball (0 : Vec d) (2*r) := by
      ext x; simp only [originBall, ball, sub_zero]
    exact measurableSet_Ioo.prod (by rw [heq]; exact (paired_isOpen_ball _ _).measurableSet)
  have hvol := positiveTimeCylinder_volume_pos_finite (d := d)
    (by nlinarith : r^2 < 4*r^2) (by positivity : 0 < 2*r)
  have hscalar := scalarL2_setAverage_moment_le P volume hUmeas hvol.1 hvol.2 hm
    (mul_nonneg (hC m hm0).le (Real.rpow_nonneg hr2.le _))
    (fun z => u z.1 z.2) hum (fun z hz => by
      have hzv := hval m hm0 z.1 (hr21.trans hz.1.1.le) z.2
      refine ⟨hzv.1, hzv.2.trans (ENNReal.ofReal_le_ofReal ?_)⟩
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos hr2 hz.1.1.le (by
          have hd0 : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
          linarith only [hd0])) (hC m hm0).le)
  have hEm : Measurable E := by
    have hgm : Measurable (fun z : Coefficient d K × (ℝ × Vec d) =>
        euclideanSq (G z.1 z.2)) := by
      unfold euclideanSq dot
      exact Finset.measurable_sum _ fun j _ =>
        ((measurable_pi_apply j).comp hGm).mul ((measurable_pi_apply j).comp hGm)
    have hi := (hgm.stronglyMeasurable.integral_prod_right'
      (ν := volume.restrict V)).measurable
    simpa only [E, vectorRms, average_eq, measureReal_restrict_apply_univ, smul_eq_mul] using
      (measurable_const.mul hi).sqrt
  have hdom : ∀ᵐ A ∂P, ‖E A‖ ≤ D/r * ‖S A‖ := by
    filter_upwards [hsol] with A hA
    have h := henergy r hr0 A (u A) (G A)
      (hA.2.1 (r^2) (4*r^2) (2*r) hr2 (by nlinarith) (by positivity))
    simpa only [E, S, vectorRms, scalarRms, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)] using h
  refine ⟨hscalar.1.of_le_mul hEm.aestronglyMeasurable hdom, ?_⟩
  calc
    eLpNorm E (ENNReal.ofReal m) P ≤
        ENNReal.ofReal (D/r) * eLpNorm S (ENNReal.ofReal m) P :=
      eLpNorm_le_mul_eLpNorm_of_ae_le_mul hdom _
    _ ≤ ENNReal.ofReal (D/r) *
        ENNReal.ofReal (C m * (r^2)^(-(1 : ℝ)/2 - (d : ℝ)/4)) :=
      mul_le_mul_right hscalar.2 _
    _ = ENNReal.ofReal (D * C m / r * (r^2)^(-(1 : ℝ)/2 - (d : ℝ)/4)) := by
      rw [← ENNReal.ofReal_mul (div_nonneg hD.le hr0.le)]
      apply congrArg ENNReal.ofReal
      ring
    _ ≤ _ := ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_left D 1) (hC m hm0).le) hr0.le)
        (Real.rpow_nonneg hr2.le _))

end EinsteinRelation.Correctors
