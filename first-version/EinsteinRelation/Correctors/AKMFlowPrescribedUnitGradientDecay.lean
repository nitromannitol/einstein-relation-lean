import EinsteinRelation.Correctors.PrescribedGradientGoodRadius
import EinsteinRelation.Correctors.AKMFlowBadRadiusPrescribedMoments
import EinsteinRelation.Correctors.SemigroupPrescribedGradientRecovery

/-! # Prescribed-time unit-ball gradient decay for one selected column flow

Source: `paper/main.tex:798–806`. The good- and bad-radius contributions
control the weak gradient of the same scalar flow at the prescribed time.
The positive-time endpoint argument is internal; no time-slice estimate
is added as a hypothesis.
-/

open MeasureTheory
open scoped ENNReal

namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- One measurable actual coefficient-column flow has the sharp prescribed-time
unit-ball gradient moment decay at `3*r²` for all `r ≥ 2` simultaneously. Constants precede the environment law.
Source: `paper/main.tex:798–806`. -/
theorem parabolicSemigroupDecay_actual_column_prescribed_unit_gradient_decay
    (hflow : ParabolicSemigroupDecay) (hreg : ParabolicLargeScale)
    (d : ℕ) (hd : 2 ≤ d) (K s : ℝ) (hK : 1 < K)
    (hs : 0 < s) (hs2 : s < 2) :
    ∃ F : ℝ → ℝ, (∀ m : ℝ, 0 < m → 0 < F m) ∧
      ∃ C : ℝ → ℝ, (∀ m : ℝ, 2 ≤ m → 0 < C m) ∧
      ∀ P : Measure (Coefficient d K), IsAdmissibleLaw P → ∀ i : Fin d,
        ∃ (u : Coefficient d K → ℝ × Vec d → ℝ)
          (G H : Coefficient d K → ℝ × Vec d → Vec d),
          Measurable (fun z : Coefficient d K × (ℝ × Vec d) => u z.1 z.2) ∧
          Measurable (fun z : Coefficient d K × (ℝ × Vec d) => G z.1 z.2) ∧
          Measurable (fun z : Coefficient d K × (ℝ × Vec d) => H z.1 z.2) ∧
          (∀ᵐ A ∂P, IsSemigroupSolution A
            (fun x => (A x).mulVec (unitVector i)) (u A) (G A)) ∧
          (∀ᵐ A ∂P, ∀ t : ℝ, 0 < t → HasWeakGradient Set.univ
            (fun x => u A (t,x)) (fun x => H A (t,x))) ∧
          (∀ m : ℝ, 0 < m → ∀ t : ℝ, 1 ≤ t → ∀ x : Vec d,
            MemLp (fun A => u A (t,x)) (ENNReal.ofReal m) P ∧
            eLpNorm (fun A => u A (t,x)) (ENNReal.ofReal m) P ≤
              ENNReal.ofReal (F m * t^(-(1 : ℝ)/2-(d : ℝ)/4))) ∧
          ∀ m : ℝ, 2 ≤ m → ∀ r : ℝ, 2 ≤ r →
            MemLp (fun A => vectorRms volume (originBall d 1) (fun x => H A (3*r^2,x))) (ENNReal.ofReal m) P ∧
            eLpNorm (fun A => vectorRms volume (originBall d 1) (fun x => H A (3*r^2,x))) (ENNReal.ofReal m) P ≤
                ENNReal.ofReal (C m/r * (r^2)^(-(1 : ℝ)/2-(d : ℝ)/4)) := by
  obtain ⟨L,hL,F,hF,C,hC,hflows⟩ :=
    parabolicSemigroupDecay_random_radius_cylinder_moments hflow hreg d hd K s hK hs hs2
  obtain ⟨χ,Lχ,hLχ,hχ,hχb,hχV,hχD⟩ := exists_prescribed_spatial_ball_cutoff d 1 zero_lt_one
  have hχ' : IsSpatialTest (originBall d 2) χ := by simpa only [mul_one] using hχ
  obtain ⟨D,hD,hbad⟩ := semigroupFlow_bad_radius_prescribed_unit_moment_le
    d K (zero_lt_one.trans hK) hχ' hχb hχV hLχ hχD
  let B : ℝ → ℝ := fun m =>
    4 * ((2*((2*m)/s)^((2*m)/s))^(1/(2*m))*L) * D * F (2*m)
  refine ⟨F,hF,fun m => Real.sqrt d*L*C m+B m,?_,?_⟩
  · intro m hm
    have hB : 0 ≤ B m := by
      dsimp only [B]
      exact mul_nonneg (mul_nonneg
        (mul_nonneg (by norm_num) (mul_nonneg (Real.rpow_nonneg (by positivity) _) hL.le))
        hD.le) (hF _ (by linarith only [hm])).le
    exact add_pos_of_pos_of_nonneg (mul_pos (mul_pos (Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < d))) hL) (hC m hm)) hB
  · intro P hP i
    obtain ⟨X,u,G,hXm,hX,htail,hum,hGm,hsol,hval,hcomp,hmom⟩ := hflows P hP i
    obtain ⟨H,hHm,hHw⟩ := exists_measurable_positive_time_gradient
      (zero_lt_one.trans hK) P id (fun A x => (A x).mulVec (unitVector i)) u G hum hsol
    refine ⟨u,G,H,hum,hGm,hHm,hsol,hHw,hval,?_⟩
    intro m hm r hr
    have hm2 : 0 < 2*m := by linarith only [hm]
    have hCm : 0 < C m := hC m hm
    have hF2m : 0 < F (2*m) := hF _ hm2
    have hBm : 0 ≤ B m := by dsimp only [B]; positivity
    have hr1 : 1 ≤ r := by linarith only [hr]
    let E := fun A => vectorRms volume (originBall d 1) (fun x => H A (3*r^2,x))
    let Q := fun A => (X A)^((d : ℝ)/2) * vectorRms volume
      (Set.Ioo (2*r^2) (3*r^2) ×ˢ originBall d r) (G A)
    let S : Set (Coefficient d K) := {A | 4*X A ≤ r}
    let T : Set (Coefficient d K) := {A | r < 4*X A}
    have hSm : MeasurableSet S := measurableSet_le (measurable_const.mul hXm) measurable_const
    have hEm : Measurable E := by
      have hrep : Measurable (fun z : Coefficient d K × Vec d => H z.1 (3*r^2,z.2)) :=
        hHm.comp (measurable_fst.prodMk (measurable_const.prodMk measurable_snd))
      have he : Measurable (fun z : Coefficient d K × Vec d =>
          euclideanSq (H z.1 (3*r^2,z.2))) := by
        unfold euclideanSq dot
        exact Finset.measurable_sum _ fun j _ =>
          ((measurable_pi_apply j).comp hrep).mul ((measurable_pi_apply j).comp hrep)
      have hi := (he.stronglyMeasurable.integral_prod_right'
        (ν := volume.restrict (originBall d 1))).measurable
      simpa only [E,vectorRms,average_eq,measureReal_restrict_apply_univ,smul_eq_mul] using
        (measurable_const.mul hi).sqrt
    have hdom : ∀ᵐ A ∂P, ‖S.indicator E A‖ ≤ (Real.sqrt d*L) * ‖Q A‖ := by
      filter_upwards [hsol,hcomp,hHw] with A hA hc hHA
      by_cases hg : 4*X A ≤ r
      · have hmem : A ∈ S := hg
        rw [Set.indicator_of_mem hmem]
        have he := semigroupSolution_good_radius_prescribed_unit_le hA hr1 (hX A) hL.le hg
          (hc r hg) (hHA (3*r^2) (by nlinarith only [hr]))
        simpa only [E,Q,vectorRms,Real.norm_eq_abs,abs_mul,
          abs_of_nonneg (Real.sqrt_nonneg _),
          abs_of_nonneg (Real.rpow_nonneg (zero_le_one.trans (hX A)) _),mul_assoc] using he.2
      · have hmem : A ∉ S := hg
        rw [Set.indicator_of_notMem hmem,norm_zero]
        exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hL.le) (norm_nonneg _)
    have hQ := hmom m hm r hr1
    have hgood : MemLp (S.indicator E) (ENNReal.ofReal m) P :=
      hQ.1.of_le_mul (hEm.aestronglyMeasurable.indicator hSm) hdom
    have hgoodnorm : eLpNorm (S.indicator E) (ENNReal.ofReal m) P ≤
        ENNReal.ofReal (Real.sqrt d*L*C m/r * (r^2)^(-(1 : ℝ)/2-(d : ℝ)/4)) := by
      calc
        _ ≤ ENNReal.ofReal (Real.sqrt d*L) * eLpNorm Q (ENNReal.ofReal m) P :=
          eLpNorm_le_mul_eLpNorm_of_ae_le_mul hdom _
        _ ≤ ENNReal.ofReal (Real.sqrt d*L) * ENNReal.ofReal
            (C m/r * (r^2)^(-(1 : ℝ)/2-(d : ℝ)/4)) := mul_le_mul_right hQ.2 _
        _ = _ := by rw [← ENNReal.ofReal_mul (mul_nonneg (Real.sqrt_nonneg _) hL.le)]; congr 1; ring
    have hbadE := hbad P hP.1 (fun A x => (A x).mulVec (unitVector i))
      u G H hum hGm hHm hsol hHw X hXm (fun A => zero_le_one.trans (hX A)) s L hs hL htail
      m hm r hr (F (2*m)) (hF _ hm2).le (fun t ht x =>
        hval (2*m) hm2 t ((by nlinarith only [hr] : (1 : ℝ) ≤ r^2).trans ht) x)
    have hsplit : E = S.indicator E + T.indicator E := by
      funext A
      by_cases hg : 4*X A ≤ r
      · have hmem : A ∈ S := hg
        have hnmem : A ∉ T := not_lt.mpr hg
        simp only [Pi.add_apply,Set.indicator_of_mem hmem,Set.indicator_of_notMem hnmem,add_zero]
      · have hmem : A ∉ S := hg
        have hlt : A ∈ T := lt_of_not_ge hg
        simp only [Pi.add_apply,Set.indicator_of_notMem hmem,Set.indicator_of_mem hlt,zero_add]
    refine ⟨by
      change MemLp E (ENNReal.ofReal m) P
      rw [hsplit]
      exact hgood.add hbadE.1,?_⟩
    calc
      eLpNorm E (ENNReal.ofReal m) P =
          eLpNorm (S.indicator E + T.indicator E) (ENNReal.ofReal m) P :=
        congrArg (fun f : Coefficient d K → ℝ => eLpNorm f (ENNReal.ofReal m) P) hsplit
      _ ≤ eLpNorm (S.indicator E) (ENNReal.ofReal m) P +
          eLpNorm (T.indicator E) (ENNReal.ofReal m) P :=
        eLpNorm_add_le hgood.1 hbadE.1.1 (by
          simpa only [ENNReal.ofReal_one] using
            ENNReal.ofReal_le_ofReal (by linarith only [hm] : (1 : ℝ) ≤ m))
      _ ≤ ENNReal.ofReal (Real.sqrt d*L*C m/r * (r^2)^(-(1 : ℝ)/2-(d : ℝ)/4)) +
          ENNReal.ofReal (B m/r * (r^2)^(-(1 : ℝ)/2-(d : ℝ)/4)) :=
        add_le_add hgoodnorm hbadE.2
      _ = _ := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

end EinsteinRelation.Correctors
