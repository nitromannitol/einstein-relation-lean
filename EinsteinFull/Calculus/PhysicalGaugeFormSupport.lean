import EinsteinFull.Calculus.PhysicalGaugeDomainSupport
import EinsteinFull.Calculus.PhysicalH1ClosedGraphSupport
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Gauge transport of the actual physical bilinear form.

The weak gradient representatives are obtained from the proved full-domain
transport and uniqueness. No ellipticity or additional analytic input is used.
-/

open MeasureTheory
open scoped ENNReal
noncomputable section
namespace EinsteinFull
open EinsteinRelation

/-- The physical reference integral has the literal exponential density. -/
theorem integral_physicalForceMeasure {d : ℕ} (i : Fin d) (lam : ℝ)
    (f : Vec d → ℂ) :
    (∫ x, f x ∂physicalForceMeasure i lam) =
      ∫ x, (Real.exp (2 * lam * x i) : ℂ) * f x := by
  unfold physicalForceMeasure
  rw [integral_withDensity_eq_integral_toReal_smul
    (show Measurable (fun x : Vec d => ENNReal.ofReal (Real.exp (2 * lam * x i))) from
      (ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp
        (continuous_const.mul (continuous_apply i)))).measurable)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (Real.exp_pos _).le, Complex.real_smul]

private theorem gaugeWeight_sq {d : ℕ} (i : Fin d) (lam : ℝ) (x : Vec d) :
    (Real.exp (2 * lam * x i) : ℂ) =
      (Real.exp (lam * x i) : ℂ) * (Real.exp (lam * x i) : ℂ) := by
  rw [← Complex.ofReal_mul, ← Real.exp_add]
  congr 2
  ring

/-- The unitary transports the actual bilinear mass pairing, without conjugation. -/
theorem integral_physicalGaugeUnitary_mul {d : ℕ} (i : Fin d) (lam : ℝ)
    (f g : Lp ℂ 2 (physicalForceMeasure i lam)) :
    (∫ x, f x * g x ∂physicalForceMeasure i lam) =
      ∫ x, physicalGaugeUnitary i lam f x * physicalGaugeUnitary i lam g x := by
  rw [integral_physicalForceMeasure]
  apply integral_congr_ae
  filter_upwards [physicalGaugeUnitary_coe i lam f, physicalGaugeUnitary_coe i lam g]
    with x hf hg
  rw [hf, hg, gaugeWeight_sq]
  simp only [physicalGaugeMultiplier]
  ring

/-- Any weak gradient of the gauged value has the explicit transported representative. -/
theorem physicalH1Graph_gauge_gradient_coe {d : ℕ} (i : Fin d) (lam : ℝ)
    (f : Lp ℂ 2 (physicalForceMeasure i lam))
    (G : Fin d → Lp ℂ 2 (physicalForceMeasure i lam))
    (G' : Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (hG : IsPhysicalH1Graph (physicalForceMeasure i lam) (Or.inr ⟨i, lam, rfl⟩) f G)
    (hG' : IsPhysicalH1Graph volume (Or.inl rfl) (physicalGaugeUnitary i lam f) G') :
    ∀ j : Fin d, (G' j : Vec d → ℂ) =ᵐ[volume] fun x =>
      (Real.exp (lam * x i) : ℂ) *
        (G j x + (lam : ℂ) * (unitVector i j : ℂ) * f x) := by
  obtain ⟨H, hH, hrep⟩ := physicalH1Graph_gauge_forward i lam f G hG
  have heq := physicalH1Graph_gradient_unique volume (Or.inl rfl)
    (physicalGaugeUnitary i lam f) G' H hG' hH
  rw [heq]
  exact hrep

/-- The real-force gauge transports the full physical bilinear form. -/
theorem physicalBilinearForm_gauge {d : ℕ} (i : Fin d) (lam s : ℝ)
    (a : Vec d → Mat d)
    (ha : ∀ j k : Fin d, MemLp (fun x => (a x j k : ℂ)) ∞ (physicalForceMeasure i lam))
    (ha' : ∀ j k : Fin d, MemLp (fun x => (a x j k : ℂ)) ∞ (volume : Measure (Vec d)))
    (f g : Lp ℂ 2 (physicalForceMeasure i lam))
    (G H : Fin d → Lp ℂ 2 (physicalForceMeasure i lam))
    (G' H' : Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (hG : IsPhysicalH1Graph (physicalForceMeasure i lam) (Or.inr ⟨i, lam, rfl⟩) f G)
    (hH : IsPhysicalH1Graph (physicalForceMeasure i lam) (Or.inr ⟨i, lam, rfl⟩) g H)
    (hG' : IsPhysicalH1Graph volume (Or.inl rfl) (physicalGaugeUnitary i lam f) G')
    (hH' : IsPhysicalH1Graph volume (Or.inl rfl) (physicalGaugeUnitary i lam g) H') :
    physicalBilinearForm (physicalForceMeasure i lam) a ha i s 0 f G g H =
      physicalBilinearForm volume a ha' i s (lam : ℂ)
        (physicalGaugeUnitary i lam f) G' (physicalGaugeUnitary i lam g) H' := by
  have hGr := ae_all_iff.mpr (physicalH1Graph_gauge_gradient_coe i lam f G G' hG hG')
  have hHr := ae_all_iff.mpr (physicalH1Graph_gauge_gradient_coe i lam g H H' hH hH')
  have henergy :
      (∫ x, ∑ j : Fin d, ∑ k : Fin d, G j x * (a x j k : ℂ) * H k x
        ∂physicalForceMeasure i lam) =
      ∫ x, ∑ j : Fin d, ∑ k : Fin d,
        (G' j x - (lam : ℂ) * (unitVector i j : ℂ) * physicalGaugeUnitary i lam f x) *
        (a x j k : ℂ) *
        (H' k x - (lam : ℂ) * (unitVector i k : ℂ) * physicalGaugeUnitary i lam g x) := by
    rw [integral_physicalForceMeasure]
    apply integral_congr_ae
    filter_upwards [hGr, hHr, physicalGaugeUnitary_coe i lam f,
      physicalGaugeUnitary_coe i lam g] with x hGx hHx hfx hgx
    rw [gaugeWeight_sq]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    rw [hGx j, hHx k, hfx, hgx]
    simp only [physicalGaugeMultiplier]
    ring
  unfold physicalBilinearForm
  simp only [zero_mul, sub_zero]
  rw [integral_physicalGaugeUnitary_mul, henergy]

end EinsteinFull
