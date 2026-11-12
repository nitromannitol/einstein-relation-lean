import EinsteinRelation.Correctors.ShiftedMollifierMoments
import EinsteinRelation.Correctors.LocalMollifierSpatialTest
import EinsteinRelation.Regeneration.HalfSpaces

/-! # Shifted means from coordinate mollifier bounds

Source: `paper/main.tex:948–955`. Uniform coordinate estimates `C/R` for
the mollified weak gradient give the shifted mean bound `dC` on `B_R`.
All measurability and moment-domain conditions in the segment argument
follow from the joint gradient representative and the coordinate bounds.
-/

open MeasureTheory
open scoped Convolution

namespace EinsteinRelation.Correctors

/-- A jointly measurable random field has measurable smooth convolution
at every fixed spatial point. Source: `paper/main.tex:948–955`. -/
theorem measurable_random_convolution {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (f : Ω → Vec d → ℝ) (hf : Measurable (Function.uncurry f))
    {ζ : Vec d → ℝ} (hζ : Continuous ζ) (x : Vec d) :
    Measurable (fun ω => (f ω ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ζ) x) := by
  have hm : Measurable (fun z : Ω × Vec d => f z.1 z.2 * ζ (x - z.2)) :=
    hf.mul (hζ.measurable.comp (measurable_const.sub measurable_snd))
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

/-- Coordinate `C/R` estimates for the literal mollifier control the
translation of a smooth average without a regularity assumption on its
weakly differentiable source. Source: `paper/main.tex:948–955`. -/
theorem convolution_shift_moment_le_of_coordinate_bounds
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (Q : Measure Ω) [IsProbabilityMeasure Q] {p C R : ℝ}
    (hp : 1 ≤ p) (hC : 0 ≤ C) (hR : 0 < R)
    (f : Ω → Vec d → ℝ) (G : Ω → Vec d → Vec d)
    (hGm : Measurable (fun z : Ω × Vec d => G z.1 z.2))
    (hloc : ∀ᵐ ω ∂Q, LocallyIntegrable (f ω) volume)
    (hweak : ∀ᵐ ω ∂Q, HasWeakGradient Set.univ (f ω) (G ω))
    (hbound : ∀ x : Vec d, euclideanNorm x ≤ R → ∀ j : Fin d,
      eLpNorm (fun ω => ((fun z => G ω z j)
        ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          Calculus.unitMassScaledMollifier d R) x) (ENNReal.ofReal p) Q ≤
        ENNReal.ofReal (C * R⁻¹))
    (y : Vec d) (hy : euclideanNorm y ≤ R) :
    MemLp (fun ω => (f ω ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        Calculus.unitMassScaledMollifier d R) y -
      (f ω ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        Calculus.unitMassScaledMollifier d R) 0) (ENNReal.ofReal p) Q ∧
      eLpNorm (fun ω => (f ω ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          Calculus.unitMassScaledMollifier d R) y -
        (f ω ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          Calculus.unitMassScaledMollifier d R) 0) (ENNReal.ofReal p) Q ≤
        ENNReal.ofReal ((d : ℝ) * C) := by
  apply convolution_shift_moment_le Q hp (by positivity) f G hGm hloc hweak
    (Entropy.contDiff_unitMassScaledMollifier R)
    (Entropy.hasCompactSupport_unitMassScaledMollifier hR) y
  intro t ht
  have hty : euclideanNorm (t • y) ≤ R := by
    rw [TimeChange.euclideanNorm_smul, abs_of_nonneg ht.1]
    exact (mul_le_mul_of_nonneg_right ht.2 (Real.sqrt_nonneg _)).trans
      (by simpa only [one_mul] using hy)
  let X : Fin d → Ω → ℝ := fun j ω =>
    ((fun z => G ω z j) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      Calculus.unitMassScaledMollifier d R) (t • y)
  have hXm (j : Fin d) : Measurable (X j) :=
    measurable_random_convolution (fun ω z => G ω z j)
      ((measurable_pi_apply j).comp hGm)
      (Entropy.contDiff_unitMassScaledMollifier R).continuous (t • y)
  have hXi (j : Fin d) : MemLp (X j) (ENNReal.ofReal p) Q :=
    ⟨(hXm j).aestronglyMeasurable, (hbound (t • y) hty j).trans_lt ENNReal.ofReal_lt_top⟩
  have hterm (j : Fin d) : eLpNorm (fun ω => y j * X j ω) (ENNReal.ofReal p) Q ≤
      ENNReal.ofReal C := by
    change eLpNorm (y j • X j) _ Q ≤ _
    rw [eLpNorm_const_smul]
    have hyj : ‖y j‖ₑ ≤ ENNReal.ofReal R := by
      simpa only [Real.enorm_eq_ofReal_abs] using ENNReal.ofReal_le_ofReal
        ((Regeneration.coordinate_abs_le_euclideanNorm y j).trans hy)
    calc
      _ ≤ ENNReal.ofReal R * ENNReal.ofReal (C * R⁻¹) :=
        mul_le_mul hyj (hbound (t • y) hty j) (zero_le _) (zero_le _)
      _ = ENNReal.ofReal C := by
        rw [← ENNReal.ofReal_mul hR.le]
        congr 1
        field_simp
  refine ⟨memLp_finset_sum Finset.univ (fun j _ => (hXi j).const_mul (y j)), ?_⟩
  calc
    _ ≤ ∑ j : Fin d, eLpNorm (fun ω => y j * X j ω) (ENNReal.ofReal p) Q :=
      by
        have heq : (fun ω => ∑ j : Fin d, y j * X j ω) =
            ∑ j : Fin d, fun ω => y j * X j ω := by
          funext ω
          simp
        change eLpNorm (fun ω => ∑ j : Fin d, y j * X j ω) _ Q ≤ _
        rw [heq]
        exact
          (eLpNorm_sum_le (f := fun j ω => y j * X j ω) (s := Finset.univ)
            (fun j _ => ((hXi j).const_mul (y j)).aestronglyMeasurable)
            (ENNReal.one_le_ofReal.mpr hp))
    _ ≤ ∑ _ : Fin d, ENNReal.ofReal C := Finset.sum_le_sum (fun j _ => hterm j)
    _ = ENNReal.ofReal ((d : ℝ) * C) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg d)]
      simp

end EinsteinRelation.Correctors
