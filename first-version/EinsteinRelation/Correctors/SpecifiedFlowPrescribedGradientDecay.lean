import EinsteinRelation.Correctors.AKMFlowPrescribedUnitGradientDecay
import EinsteinRelation.Correctors.SpecifiedFlowCylinderMoments

/-! # Prescribed-time decay for a specified semigroup

Source: `paper/main.tex:798–806`. The gradient estimate applies to the
supplied scalar flow, so a later canonical-flow construction can retain its
representation. No solution selection is hidden in this analytic implication.
-/

open MeasureTheory
open scoped ENNReal
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- Sharp prescribed-time unit-ball gradient decay for a supplied flow.
The constant precedes the law and all supplied flows and scalar bounds.
Source: `paper/main.tex:798–806`. -/
theorem specifiedSemigroupFlow_prescribed_unit_gradient_decay
    (hreg : ParabolicLargeScale) (d : ℕ) (hd : 2 ≤ d)
    (K s : ℝ) (hK : 1 < K) (hs : 0 < s) (hs2 : s < 2) :
    ∃ J : ℝ → ℝ, (∀ m : ℝ, 2 ≤ m → 0 < J m) ∧
      ∀ P : Measure (Coefficient d K), IsAdmissibleLaw P →
      ∀ (g : Coefficient d K → Vec d → Vec d)
        (u : Coefficient d K → ℝ × Vec d → ℝ)
        (G H : Coefficient d K → ℝ × Vec d → Vec d),
      Measurable (fun z : Coefficient d K × (ℝ × Vec d) => u z.1 z.2) →
      Measurable (fun z : Coefficient d K × (ℝ × Vec d) => G z.1 z.2) →
      Measurable (fun z : Coefficient d K × (ℝ × Vec d) => H z.1 z.2) →
      (∀ᵐ A ∂P, IsSemigroupSolution A (g A) (u A) (G A)) →
      (∀ᵐ A ∂P, ∀ t : ℝ, 0 < t → HasWeakGradient Set.univ
        (fun x => u A (t,x)) (fun x => H A (t,x))) →
      ∀ F : ℝ → ℝ, (∀ m : ℝ, 0 < m → 0 < F m) →
      (∀ m : ℝ, 0 < m → ∀ t : ℝ, 1 ≤ t → ∀ x : Vec d,
        MemLp (fun A => u A (t,x)) (ENNReal.ofReal m) P ∧
        eLpNorm (fun A => u A (t,x)) (ENNReal.ofReal m) P ≤
          ENNReal.ofReal (F m*t^(-(1 : ℝ)/2-(d : ℝ)/4))) →
      ∀ m : ℝ, 2 ≤ m → ∀ r : ℝ, 2 ≤ r →
        MemLp (fun A => vectorRms volume (originBall d 1) (fun x => H A (3*r^2,x)))
          (ENNReal.ofReal m) P ∧
        eLpNorm (fun A => vectorRms volume (originBall d 1) (fun x => H A (3*r^2,x)))
          (ENNReal.ofReal m) P ≤
            ENNReal.ofReal (J m*F (2*m)/r*(r^2)^(-(1 : ℝ)/2-(d : ℝ)/4)) := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have ha : 0 < (d : ℝ)/2 := by linarith only [hdR]
  have hsD : s < d := hs2.trans_le hdR
  obtain ⟨L,hL,hlarge⟩ := parabolicLargeScale_semigroup_unit_gradient
    hreg d hd K s hK hs hsD
  obtain ⟨Dcy,hDcy,hcyl⟩ := semigroupFlow_diffusive_cylinder_moment_le_probability
    d K (zero_lt_one.trans hK)
  obtain ⟨χ,Lχ,hLχ,hχ,hχb,hχV,hχD⟩ := exists_prescribed_spatial_ball_cutoff d 1 zero_lt_one
  have hχ' : IsSpatialTest (originBall d 2) χ := by simpa only [mul_one] using hχ
  obtain ⟨D,hD,hbad⟩ := semigroupFlow_bad_radius_prescribed_unit_moment_le
    d K (zero_lt_one.trans hK) hχ' hχb hχV hLχ hχD
  let Bg : ℝ → ℝ := fun m =>
    (2*((2*m)/(s/((d : ℝ)/2)))^((2*m)/(s/((d : ℝ)/2))))^(1/(2*m))*L^((d : ℝ)/2)
  let Bb : ℝ → ℝ := fun m => 4*((2*((2*m)/s)^((2*m)/s))^(1/(2*m))*L)*D
  refine ⟨fun m => Real.sqrt d*L*(Bg m*Dcy)+Bb m,?_,?_⟩
  · intro m hm
    have hm2 : 0 < 2*m := by linarith only [hm]
    have hBg : 0 < Bg m := by
      dsimp only [Bg]
      exact mul_pos (Real.rpow_pos_of_pos (mul_pos two_pos
        (Real.rpow_pos_of_pos (div_pos hm2 (div_pos hs ha)) _)) _)
        (Real.rpow_pos_of_pos hL _)
    have hBb : 0 ≤ Bb m := by dsimp only [Bb]; positivity
    have hdp : 0 < (d : ℝ) := by linarith only [hdR]
    exact add_pos_of_pos_of_nonneg
      (mul_pos (mul_pos (Real.sqrt_pos.mpr hdp) hL) (mul_pos hBg hDcy)) hBb
  intro P hP g u G H hum hGm hHm hsol hHw F hF hval
  obtain ⟨X,hXm,hX,htail,hcompare⟩ := hlarge P hP
  let C : ℝ → ℝ := fun m => Bg m*Dcy*F (2*m)
  let B : ℝ → ℝ := fun m => Bb m*F (2*m)
  have hC (m : ℝ) (hm : 2 ≤ m) : 0 < C m := by
    have hm2 : 0 < 2*m := by linarith only [hm]
    have hBg : 0 < Bg m := by
      dsimp only [Bg]
      exact mul_pos (Real.rpow_pos_of_pos (mul_pos two_pos
        (Real.rpow_pos_of_pos (div_pos hm2 (div_pos hs ha)) _)) _)
        (Real.rpow_pos_of_pos hL _)
    exact mul_pos (mul_pos hBg hDcy) (hF _ hm2)
  have hcomp : ∀ᵐ A ∂P, ∀ r : ℝ, 4*X A ≤ r →
      ∀ᵐ τ ∂volume.restrict (Set.Ioo (-((2*X A)^2)/4) 0),
        vectorRms volume (originBall d 1) (fun x => G A (τ+3*r^2,x)) ≤
          L*(X A)^((d : ℝ)/2)*vectorRms volume
            (Set.Ioo (2*r^2) (3*r^2) ×ˢ originBall d r) (G A) := by
    filter_upwards [hcompare,hsol] with A hA hsolA
    intro r hr
    have hr0 : 0 < r := by linarith only [hr,hX A]
    have hb := hA _ _ _ hsolA r hr (3*r^2) (by nlinarith [sq_pos_of_pos hr0])
    simpa only [vectorRms_diffusive_backward_shift] using hb
  have hmom (m : ℝ) (hm : 2 ≤ m) (r : ℝ) (hr : 1 ≤ r) :
      MemLp (fun A => (X A)^((d : ℝ)/2)*vectorRms volume
        (Set.Ioo (2*r^2) (3*r^2) ×ˢ originBall d r) (G A)) (ENNReal.ofReal m) P ∧
      eLpNorm (fun A => (X A)^((d : ℝ)/2)*vectorRms volume
        (Set.Ioo (2*r^2) (3*r^2) ×ˢ originBall d r) (G A)) (ENNReal.ofReal m) P ≤
          ENNReal.ofReal (C m/r*(r^2)^(-(1 : ℝ)/2-(d : ℝ)/4)) := by
    have hm0 : 0 < m := by linarith only [hm]
    have hm2 : 0 < 2*m := by linarith only [hm]
    have hXmoms := radius_rpow_moments_of_stretchedExponential P hXm
      (fun A => zero_le_one.trans (hX A)) hs hL ha hm2 htail
    have hEmoms := hcyl P hP.1 g u G hum hGm hsol (2*m) (by linarith only [hm])
      r hr (F (2*m)) (hF _ hm2).le (fun t ht x =>
        hval (2*m) hm2 t ((by nlinarith only [hr] : (1 : ℝ) ≤ r^2).trans ht) x)
    haveI := holderTriple_double_ofReal hm0
    refine ⟨hEmoms.1.mul' hXmoms.1,?_⟩
    have he := eLpNorm_smul_le_mul_eLpNorm (𝕜 := ℝ) (E := ℝ) (μ := P)
      (p := ENNReal.ofReal (2*m)) (q := ENNReal.ofReal (2*m)) (r := ENNReal.ofReal m)
      (f := fun A => vectorRms volume (Set.Ioo (2*r^2) (3*r^2) ×ˢ originBall d r) (G A))
      (φ := fun A => (X A)^((d : ℝ)/2)) hEmoms.1.1 hXmoms.1.1
    apply he.trans
    apply (mul_le_mul' hXmoms.2 hEmoms.2).trans_eq
    rw [← ENNReal.ofReal_mul (by dsimp only [Bg]; positivity : 0 ≤ Bg m)]
    congr 1
    dsimp only [C]
    ring
  intro m hm r hr
  have hm2 : 0 < 2*m := by linarith only [hm]
  have hCm : 0 < C m := hC m hm
  have hF2m : 0 < F (2*m) := hF _ hm2
  have hBm : 0 ≤ B m := by dsimp only [B,Bb]; positivity
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
  have hbadE := hbad P hP.1 g
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
      dsimp only [C,B]
      ring
end EinsteinRelation.Correctors
